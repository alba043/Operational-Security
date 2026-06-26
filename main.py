import asyncio
import difflib
import hashlib
import hmac
import json
import os
import re
import sys
from collections import defaultdict
from datetime import datetime, timezone
from pathlib import Path

import discord
from discord import app_commands
from discord.ext import commands
from dotenv import load_dotenv


BASE_DIR = Path(__file__).resolve().parent
DATA_FILE = BASE_DIR / "security_data.json"
TEMP_DATA_FILE = BASE_DIR / "security_data.json.tmp"

load_dotenv(BASE_DIR / ".env")

intents = discord.Intents.default()
intents.guilds = True
intents.members = True
intents.message_content = True

bot = commands.Bot(command_prefix="!", intents=intents)
_ready_once = False
PLACEHOLDER_ENV_VALUES = {
    "replace-with-your-discord-bot-token",
    "replace-with-at-least-32-random-characters",
    "changeme-set-DATA_SECRET-in-env",
}


def utcnow() -> datetime:
    return datetime.now(timezone.utc)


def require_env(name: str, min_length: int = 1) -> str:
    value = os.getenv(name, "").strip()
    if len(value) < min_length or value in PLACEHOLDER_ENV_VALUES or value.lower().startswith("replace-with"):
        sys.exit(f"FATAL: {name} is not set to a real value.")
    return value


def strip_message_content(text: str) -> str:
    return re.sub(
        r"<@[!&]?\d+>|<#\d+>|<a?:\w+:\d+>|https?://\S+",
        "",
        text.lower(),
    ).strip()


def parse_snowflake(raw: str) -> int | None:
    digits = re.sub(r"[^0-9]", "", raw)
    if not digits:
        return None
    try:
        return int(digits)
    except ValueError:
        return None


def serialise_overwrites(overwrites: dict) -> dict:
    data = {}
    for target, overwrite in overwrites.items():
        if isinstance(target, discord.Role):
            key = f"role:{target.id}"
        elif isinstance(target, discord.Member):
            key = f"member:{target.id}"
        else:
            continue
        allow, deny = overwrite.pair()
        data[key] = {"allow": allow.value, "deny": deny.value}
    return data


async def deserialise_overwrites(guild: discord.Guild, raw: dict) -> dict:
    overwrites = {}
    for key, value in raw.items():
        try:
            kind, snowflake = key.split(":", 1)
            target_id = int(snowflake)
            if kind == "role":
                target = guild.get_role(target_id)
            else:
                target = guild.get_member(target_id)
                if target is None:
                    try:
                        target = await guild.fetch_member(target_id)
                    except Exception:
                        target = None
            if target is None:
                continue
            allow = discord.Permissions(int(value["allow"]))
            deny = discord.Permissions(int(value["deny"]))
            overwrites[target] = discord.PermissionOverwrite.from_pair(allow, deny)
        except Exception as exc:
            print(f"Skipping invalid permission overwrite backup {key}: {exc}")
    return overwrites


class SecurityData:
    def __init__(self):
        self.ban_tracker = defaultdict(lambda: defaultdict(list))
        self.kick_tracker = defaultdict(lambda: defaultdict(list))
        self.mention_tracker = defaultdict(lambda: defaultdict(list))
        self.bot_add_tracker = defaultdict(lambda: defaultdict(list))
        self.channel_delete_tracker = defaultdict(lambda: defaultdict(list))
        self.channel_create_tracker = defaultdict(lambda: defaultdict(list))
        self.role_delete_tracker = defaultdict(lambda: defaultdict(list))
        self.role_create_tracker = defaultdict(lambda: defaultdict(list))
        self.webhook_create_tracker = defaultdict(lambda: defaultdict(list))

        self.whitelisted_users = defaultdict(set)
        self.whitelisted_roles = defaultdict(set)
        self.protection_enabled = defaultdict(lambda: True)
        self.log_channels = {}
        self.recovery_snapshots = {}

        self.role_backups = defaultdict(dict)
        self.channel_overwrite_backups = defaultdict(dict)
        self.locked_channels = defaultdict(set)
        self.raid_lockdown = defaultdict(bool)
        self.raid_users = defaultdict(set)
        self.raid_messages = defaultdict(list)

        self.attacker_created_channels = defaultdict(lambda: defaultdict(dict))
        self.attacker_created_roles = defaultdict(lambda: defaultdict(dict))

        self.BAN_LIMIT = 3
        self.KICK_LIMIT = 3
        self.MENTION_LIMIT = 3
        self.BOT_ADD_LIMIT = 2
        self.CHANNEL_DELETE_LIMIT = 3
        self.CHANNEL_CREATE_LIMIT = 3
        self.ROLE_DELETE_LIMIT = 3
        self.ROLE_CREATE_LIMIT = 3
        self.WEBHOOK_CREATE_LIMIT = 2
        self.TIME_WINDOW = 600

        self.RAID_MESSAGE_THRESHOLD = 10
        self.RAID_SIMILARITY_THRESHOLD = 0.75
        self.RAID_TIME_WINDOW = 30

        self.protected_permissions = [
            "administrator",
            "ban_members",
            "kick_members",
            "manage_guild",
            "manage_roles",
            "manage_channels",
            "manage_webhooks",
            "manage_messages",
            "mention_everyone",
            "manage_nicknames",
            "manage_emojis",
            "manage_events",
            "moderate_members",
            "move_members",
            "mute_members",
            "deafen_members",
            "priority_speaker",
            "manage_threads",
        ]

    def compute_hmac(self, data_str: str) -> str:
        secret = require_env("DATA_SECRET", min_length=32)
        return hmac.new(secret.encode("utf-8"), data_str.encode("utf-8"), hashlib.sha256).hexdigest()

    def load_data(self):
        if not DATA_FILE.exists():
            return
        try:
            raw = DATA_FILE.read_text(encoding="utf-8")
            wrapper = json.loads(raw)
            if "sig" in wrapper and "data" in wrapper:
                payload_str = wrapper["data"]
                expected_sig = self.compute_hmac(payload_str)
                if not hmac.compare_digest(str(wrapper["sig"]), expected_sig):
                    sys.exit("FATAL: security_data.json integrity check failed. Refusing to run.")
                data = json.loads(payload_str)
            else:
                print("WARNING: loading legacy unsigned security_data.json; re-saving signed copy.")
                data = wrapper
        except json.JSONDecodeError as exc:
            sys.exit(f"FATAL: security_data.json is not valid JSON: {exc}")
        except SystemExit:
            raise
        except Exception as exc:
            sys.exit(f"FATAL: failed to load security_data.json: {exc}")

        self.whitelisted_users = defaultdict(
            set,
            {guild_id: {int(user_id) for user_id in users} for guild_id, users in data.get("whitelisted_users", {}).items()},
        )
        self.whitelisted_roles = defaultdict(
            set,
            {guild_id: {int(role_id) for role_id in roles} for guild_id, roles in data.get("whitelisted_roles", {}).items()},
        )
        self.log_channels = {guild_id: str(channel_id) for guild_id, channel_id in data.get("log_channels", {}).items()}
        self.protection_enabled = defaultdict(lambda: True, data.get("protection_enabled", {}))
        self.recovery_snapshots = data.get("recovery_snapshots", {})
        self.raid_lockdown = defaultdict(bool, data.get("raid_lockdown", {}))
        self.locked_channels = defaultdict(
            set,
            {guild_id: {int(channel_id) for channel_id in channels} for guild_id, channels in data.get("locked_channels", {}).items()},
        )
        self.raid_users = defaultdict(
            set,
            {guild_id: {int(user_id) for user_id in users} for guild_id, users in data.get("raid_users", {}).items()},
        )
        self.role_backups = defaultdict(dict)
        for guild_id, roles in data.get("role_backups", {}).items():
            self.role_backups[guild_id] = {int(role_id): int(perms) for role_id, perms in roles.items()}

        self.channel_overwrite_backups = defaultdict(dict)
        for guild_id, channels in data.get("channel_overwrite_backups", {}).items():
            self.channel_overwrite_backups[guild_id] = {int(channel_id): overwrites for channel_id, overwrites in channels.items()}

        def load_tracker(raw_tracker):
            tracker = defaultdict(lambda: defaultdict(list))
            for guild_id, users in raw_tracker.items():
                for user_id, timestamps in users.items():
                    loaded = []
                    for timestamp in timestamps:
                        try:
                            loaded.append(datetime.fromisoformat(timestamp))
                        except ValueError:
                            continue
                    tracker[guild_id][int(user_id)] = loaded
            return tracker

        for attr in (
            "ban_tracker",
            "kick_tracker",
            "mention_tracker",
            "bot_add_tracker",
            "channel_delete_tracker",
            "channel_create_tracker",
            "role_delete_tracker",
            "role_create_tracker",
            "webhook_create_tracker",
        ):
            setattr(self, attr, load_tracker(data.get(attr, {})))

        self.load_thresholds(data.get("thresholds", {}))

        if "sig" not in wrapper or "data" not in wrapper:
            self.save_data()

    def load_thresholds(self, thresholds: dict):
        int_fields = {
            "BAN_LIMIT",
            "KICK_LIMIT",
            "MENTION_LIMIT",
            "BOT_ADD_LIMIT",
            "CHANNEL_DELETE_LIMIT",
            "CHANNEL_CREATE_LIMIT",
            "ROLE_DELETE_LIMIT",
            "ROLE_CREATE_LIMIT",
            "WEBHOOK_CREATE_LIMIT",
            "TIME_WINDOW",
            "RAID_MESSAGE_THRESHOLD",
            "RAID_TIME_WINDOW",
        }
        for key in int_fields:
            if key in thresholds:
                value = int(thresholds[key])
                if value >= 1:
                    setattr(self, key, value)
        if "RAID_SIMILARITY_THRESHOLD" in thresholds:
            value = float(thresholds["RAID_SIMILARITY_THRESHOLD"])
            if 0 <= value <= 1:
                self.RAID_SIMILARITY_THRESHOLD = value

    def save_data(self):
        def serialise_tracker(tracker):
            return {
                guild_id: {
                    str(user_id): [timestamp.isoformat() for timestamp in timestamps]
                    for user_id, timestamps in users.items()
                }
                for guild_id, users in tracker.items()
            }

        data = {
            "whitelisted_users": {guild_id: sorted(users) for guild_id, users in self.whitelisted_users.items()},
            "whitelisted_roles": {guild_id: sorted(roles) for guild_id, roles in self.whitelisted_roles.items()},
            "log_channels": self.log_channels,
            "protection_enabled": dict(self.protection_enabled),
            "raid_lockdown": dict(self.raid_lockdown),
            "locked_channels": {guild_id: sorted(channels) for guild_id, channels in self.locked_channels.items()},
            "raid_users": {guild_id: sorted(users) for guild_id, users in self.raid_users.items()},
            "role_backups": {
                guild_id: {str(role_id): permissions for role_id, permissions in roles.items()}
                for guild_id, roles in self.role_backups.items()
            },
            "channel_overwrite_backups": {
                guild_id: {str(channel_id): overwrites for channel_id, overwrites in channels.items()}
                for guild_id, channels in self.channel_overwrite_backups.items()
            },
            "recovery_snapshots": self.recovery_snapshots,
            "thresholds": {
                "BAN_LIMIT": self.BAN_LIMIT,
                "KICK_LIMIT": self.KICK_LIMIT,
                "MENTION_LIMIT": self.MENTION_LIMIT,
                "BOT_ADD_LIMIT": self.BOT_ADD_LIMIT,
                "CHANNEL_DELETE_LIMIT": self.CHANNEL_DELETE_LIMIT,
                "CHANNEL_CREATE_LIMIT": self.CHANNEL_CREATE_LIMIT,
                "ROLE_DELETE_LIMIT": self.ROLE_DELETE_LIMIT,
                "ROLE_CREATE_LIMIT": self.ROLE_CREATE_LIMIT,
                "WEBHOOK_CREATE_LIMIT": self.WEBHOOK_CREATE_LIMIT,
                "TIME_WINDOW": self.TIME_WINDOW,
                "RAID_MESSAGE_THRESHOLD": self.RAID_MESSAGE_THRESHOLD,
                "RAID_SIMILARITY_THRESHOLD": self.RAID_SIMILARITY_THRESHOLD,
                "RAID_TIME_WINDOW": self.RAID_TIME_WINDOW,
            },
            "ban_tracker": serialise_tracker(self.ban_tracker),
            "kick_tracker": serialise_tracker(self.kick_tracker),
            "mention_tracker": serialise_tracker(self.mention_tracker),
            "bot_add_tracker": serialise_tracker(self.bot_add_tracker),
            "channel_delete_tracker": serialise_tracker(self.channel_delete_tracker),
            "channel_create_tracker": serialise_tracker(self.channel_create_tracker),
            "role_delete_tracker": serialise_tracker(self.role_delete_tracker),
            "role_create_tracker": serialise_tracker(self.role_create_tracker),
            "webhook_create_tracker": serialise_tracker(self.webhook_create_tracker),
        }
        payload_str = json.dumps(data, indent=2, sort_keys=True)
        wrapper = {"sig": self.compute_hmac(payload_str), "data": payload_str}
        TEMP_DATA_FILE.write_text(json.dumps(wrapper, indent=2, sort_keys=True), encoding="utf-8")
        os.replace(TEMP_DATA_FILE, DATA_FILE)


security = SecurityData()


def is_owner_only():
    async def predicate(interaction: discord.Interaction):
        return interaction.guild is not None and interaction.user.id == interaction.guild.owner_id

    return app_commands.check(predicate)


def is_owner_or_whitelisted():
    async def predicate(interaction: discord.Interaction):
        if interaction.guild is None:
            return False
        if interaction.user.id == interaction.guild.owner_id:
            return True
        guild_id = str(interaction.guild_id)
        if interaction.user.id in security.whitelisted_users[guild_id]:
            return True
        user_role_ids = {role.id for role in getattr(interaction.user, "roles", [])}
        return bool(user_role_ids & security.whitelisted_roles[guild_id])

    return app_commands.check(predicate)


async def check_user_protected(guild: discord.Guild, user_id: int) -> bool:
    if user_id == guild.owner_id:
        return True
    guild_id = str(guild.id)
    if user_id in security.whitelisted_users[guild_id]:
        return True
    member = guild.get_member(user_id)
    if member is None:
        return False
    user_role_ids = {role.id for role in member.roles}
    return bool(user_role_ids & security.whitelisted_roles[guild_id])


def is_self_action(user) -> bool:
    return bot.user is not None and user is not None and user.id == bot.user.id


def calculate_similarity(text1: str, text2: str) -> float:
    return difflib.SequenceMatcher(None, strip_message_content(text1), strip_message_content(text2)).ratio()


def prune_tracker(tracker: dict, user_id: int, current_time: datetime, window_seconds: int) -> int:
    tracker[user_id] = [
        timestamp for timestamp in tracker[user_id] if (current_time - timestamp).total_seconds() < window_seconds
    ]
    return len(tracker[user_id])


def track_action(tracker: dict, user_id: int, current_time: datetime, window_seconds: int) -> int:
    tracker[user_id].append(current_time)
    return prune_tracker(tracker, user_id, current_time, window_seconds)


def prune_created_records(records: dict, current_time: datetime):
    for item_id, created_at in list(records.items()):
        if (current_time - created_at).total_seconds() >= security.TIME_WINDOW:
            del records[item_id]


async def lock_raid_channels(guild: discord.Guild, channel_ids: set[int]):
    guild_id = str(guild.id)
    for channel_id in channel_ids:
        channel = guild.get_channel(channel_id)
        if not isinstance(channel, discord.TextChannel):
            continue
        security.locked_channels[guild_id].add(channel_id)
        if channel_id not in security.channel_overwrite_backups[guild_id]:
            security.channel_overwrite_backups[guild_id][channel_id] = serialise_overwrites(dict(channel.overwrites))

    security.save_data()

    for channel_id in channel_ids:
        channel = guild.get_channel(channel_id)
        if not isinstance(channel, discord.TextChannel):
            continue
        for role in guild.roles:
            if role.is_bot_managed() or role.is_integration():
                continue
            try:
                await channel.set_permissions(role, send_messages=False, reason="Raid lockdown")
            except Exception as exc:
                print(f"Lock permissions failed for role {role.id} in channel {channel.id}: {exc}")


async def check_raid(guild: discord.Guild, message: discord.Message):
    guild_id = str(guild.id)

    if security.raid_lockdown[guild_id]:
        try:
            await message.delete()
        except Exception as exc:
            print(f"Delete during lockdown failed: {exc}")
        return

    text = strip_message_content(message.content)
    if len(text) < 10:
        return

    current_time = utcnow()
    security.raid_messages[guild_id] = [
        entry
        for entry in security.raid_messages[guild_id]
        if (current_time - entry[4]).total_seconds() < security.RAID_TIME_WINDOW
    ]
    security.raid_messages[guild_id].append((message.id, message.author.id, message.channel.id, text, current_time))

    similar_messages = []
    similar_users = {message.author.id}
    affected_channels = {message.channel.id}
    for _msg_id, author_id, channel_id, content, _timestamp in security.raid_messages[guild_id]:
        if author_id == message.author.id:
            continue
        if calculate_similarity(text, content) >= security.RAID_SIMILARITY_THRESHOLD:
            similar_messages.append((_msg_id, author_id, channel_id, content, _timestamp))
            similar_users.add(author_id)
            affected_channels.add(channel_id)

    if len(similar_messages) + 1 < security.RAID_MESSAGE_THRESHOLD or len(similar_users) < 3:
        return

    security.raid_lockdown[guild_id] = True
    security.raid_users[guild_id] = set(similar_users)
    await lock_raid_channels(guild, affected_channels)
    security.save_data()

    raid_users_list = []
    for user_id in sorted(security.raid_users[guild_id]):
        user = guild.get_member(user_id)
        if user is None:
            raid_users_list.append(f"Unknown User (`{user_id}`)")
            continue
        raid_users_list.append(f"{user.mention} (`{user.id}`)")
        if await check_user_protected(guild, user.id):
            continue
        try:
            await guild.ban(user, reason="Raid participant")
        except Exception as exc:
            print(f"Raid ban failed for {user_id}: {exc}")
            try:
                await guild.kick(user, reason="Raid participant")
            except Exception as kick_exc:
                print(f"Raid kick failed for {user_id}: {kick_exc}")

    embed = discord.Embed(
        title="Raid Detected - Channels Locked",
        description=(
            f"Similar messages: {len(similar_messages) + 1}\n"
            f"Time window: {security.RAID_TIME_WINDOW}s\n"
            f"Similarity: {security.RAID_SIMILARITY_THRESHOLD * 100:.0f}%"
        ),
        color=discord.Color.dark_red(),
        timestamp=utcnow(),
    )
    affected_mentions = [f"<#{channel_id}>" for channel_id in sorted(security.locked_channels[guild_id])]
    embed.add_field(name="Affected Channels", value="\n".join(affected_mentions) or "None", inline=False)
    embed.add_field(
        name=f"Users Involved ({len(raid_users_list)})",
        value="\n".join(raid_users_list[:15]) + ("\n..." if len(raid_users_list) > 15 else ""),
        inline=False,
    )
    embed.add_field(name="Lockdown Active", value="Use /unlock to restore channel permissions.", inline=False)
    await log_event(guild, embed)
    security.raid_messages[guild_id].clear()
    security.save_data()


async def neutralize_roles(guild: discord.Guild, reason: str) -> int:
    guild_id = str(guild.id)
    modified_roles = []

    for role in guild.roles:
        if role.is_bot_managed() or role.is_default() or role.is_integration() or role.is_premium_subscriber():
            continue
        if role.id in security.whitelisted_roles[guild_id]:
            continue
        if any(getattr(role.permissions, perm, False) for perm in security.protected_permissions):
            security.role_backups[guild_id].setdefault(role.id, role.permissions.value)

    security.save_data()

    for role in guild.roles:
        if role.is_bot_managed() or role.is_default() or role.is_integration() or role.is_premium_subscriber():
            continue
        if role.id in security.whitelisted_roles[guild_id]:
            continue
        if not any(getattr(role.permissions, perm, False) for perm in security.protected_permissions):
            continue

        new_permissions = discord.Permissions(role.permissions.value)
        for permission in security.protected_permissions:
            setattr(new_permissions, permission, False)
        try:
            await role.edit(permissions=new_permissions, reason=reason)
            modified_roles.append(role)
            await asyncio.sleep(0.5)
        except Exception as exc:
            print(f"Failed to neutralize role {role.name} ({role.id}): {exc}")

    if modified_roles:
        embed = discord.Embed(
            title="Security Protocol Activated",
            description=f"Server: {guild.name}\nReason: {reason}\nRoles secured: {len(modified_roles)}",
            color=discord.Color.dark_red(),
            timestamp=utcnow(),
        )
        await log_event(guild, embed)
    return len(modified_roles)


async def log_event(guild: discord.Guild, embed: discord.Embed):
    guild_id = str(guild.id)
    channel_id = security.log_channels.get(guild_id)
    if not channel_id:
        return
    try:
        channel = guild.get_channel(int(channel_id))
        if channel is not None:
            await channel.send(embed=embed)
    except Exception as exc:
        print(f"Log send failed: {exc}")


async def snapshot_guild(guild: discord.Guild) -> dict:
    guild_id = str(guild.id)
    snapshot = {"roles": {}, "channels": {}, "timestamp": utcnow().isoformat()}
    for role in guild.roles:
        if role.is_default() or role.is_bot_managed():
            continue
        snapshot["roles"][str(role.id)] = {
            "name": role.name,
            "permissions": role.permissions.value,
            "color": role.color.value,
            "hoist": role.hoist,
            "mentionable": role.mentionable,
            "position": role.position,
        }
    for channel in guild.channels:
        snapshot["channels"][str(channel.id)] = {
            "name": channel.name,
            "type": str(channel.type),
            "position": channel.position,
            "category_id": str(channel.category_id) if channel.category_id else None,
            "overwrites": serialise_overwrites(dict(getattr(channel, "overwrites", {}))),
        }
    security.recovery_snapshots[guild_id] = snapshot
    security.save_data()
    return snapshot


async def punish_attacker(guild: discord.Guild, user, reason: str) -> str:
    if is_self_action(user) or await check_user_protected(guild, user.id):
        return "skipped"
    try:
        await guild.ban(user, reason=reason)
        return "banned"
    except Exception as exc:
        print(f"Ban failed for {user} ({user.id}): {exc}")
    try:
        await guild.kick(user, reason=reason)
        return "kicked"
    except Exception as exc:
        print(f"Kick failed for {user} ({user.id}): {exc}")
    try:
        member = guild.get_member(user.id)
        if member is None:
            return "failed"
        mute_role = discord.utils.get(guild.roles, name="Muted")
        if mute_role is None:
            mute_role = await guild.create_role(name="Muted", reason="Security mute role")
            for channel in guild.channels:
                await channel.set_permissions(mute_role, send_messages=False, speak=False)
        await member.add_roles(mute_role, reason=reason)
        return "muted"
    except Exception as exc:
        print(f"Mute failed for {user} ({user.id}): {exc}")
        return "failed"


@bot.event
async def on_ready():
    global _ready_once
    if _ready_once:
        return
    _ready_once = True
    security.load_data()
    await bot.tree.sync()
    print(f"Security bot active - {len(bot.guilds)} servers")


@bot.event
async def on_guild_join(guild):
    await snapshot_guild(guild)


@bot.event
async def on_message(message):
    if not message.guild or message.author.bot:
        await bot.process_commands(message)
        return

    guild_id = str(message.guild.id)
    if not security.protection_enabled[guild_id] or await check_user_protected(message.guild, message.author.id):
        await bot.process_commands(message)
        return

    await check_raid(message.guild, message)
    if security.raid_lockdown[guild_id]:
        await bot.process_commands(message)
        return

    if message.mention_everyone:
        current_time = utcnow()
        tracker = security.mention_tracker[guild_id]
        count = track_action(tracker, message.author.id, current_time, security.TIME_WINDOW)
        if count >= security.MENTION_LIMIT:
            await neutralize_roles(message.guild, f"Mass mention attack by {message.author} ({message.author.id})")
            result = await punish_attacker(message.guild, message.author, "Mass mentioning everyone")
            try:
                await message.delete()
            except Exception as exc:
                print(f"Delete mention message failed: {exc}")
            embed = discord.Embed(
                title="Mention Attack Detected",
                description=f"User: {message.author.mention} (`{message.author.id}`)\nMentions: {count}\nAction: {result}",
                color=discord.Color.dark_red(),
                timestamp=utcnow(),
            )
            await log_event(message.guild, embed)

    await bot.process_commands(message)


@bot.event
async def on_member_ban(guild, user):
    guild_id = str(guild.id)
    if not security.protection_enabled[guild_id]:
        return
    await asyncio.sleep(2)
    try:
        async for entry in guild.audit_logs(limit=5, action=discord.AuditLogAction.ban):
            if entry.target.id != user.id:
                continue
            moderator = entry.user
            if is_self_action(moderator) or await check_user_protected(guild, moderator.id):
                return
            current_time = utcnow()
            tracker = security.ban_tracker[guild_id]
            count = track_action(tracker, moderator.id, current_time, security.TIME_WINDOW)
            if count >= security.BAN_LIMIT:
                await neutralize_roles(guild, f"Mass ban attack by {moderator} ({moderator.id})")
                result = await punish_attacker(guild, moderator, "Mass banning members")
                embed = discord.Embed(
                    title="Ban Attack Detected",
                    description=f"User: {moderator.mention} (`{moderator.id}`)\nBans: {count}\nAction: {result}",
                    color=discord.Color.dark_red(),
                    timestamp=utcnow(),
                )
                await log_event(guild, embed)
            break
    except Exception as exc:
        print(f"on_member_ban failed: {exc}")


@bot.event
async def on_member_remove(member):
    guild_id = str(member.guild.id)
    if not security.protection_enabled[guild_id]:
        return
    await asyncio.sleep(2)
    try:
        async for entry in member.guild.audit_logs(limit=5, action=discord.AuditLogAction.kick):
            if entry.target.id != member.id:
                continue
            moderator = entry.user
            if is_self_action(moderator) or await check_user_protected(member.guild, moderator.id):
                return
            current_time = utcnow()
            tracker = security.kick_tracker[guild_id]
            count = track_action(tracker, moderator.id, current_time, security.TIME_WINDOW)
            if count >= security.KICK_LIMIT:
                await neutralize_roles(member.guild, f"Mass kick attack by {moderator} ({moderator.id})")
                result = await punish_attacker(member.guild, moderator, "Mass kicking members")
                embed = discord.Embed(
                    title="Kick Attack Detected",
                    description=f"User: {moderator.mention} (`{moderator.id}`)\nKicks: {count}\nAction: {result}",
                    color=discord.Color.dark_red(),
                    timestamp=utcnow(),
                )
                await log_event(member.guild, embed)
            break
    except Exception as exc:
        print(f"on_member_remove failed: {exc}")


@bot.event
async def on_member_join(member):
    guild_id = str(member.guild.id)
    if not security.protection_enabled[guild_id] or not member.bot:
        return
    await asyncio.sleep(2)
    try:
        async for entry in member.guild.audit_logs(limit=5, action=discord.AuditLogAction.bot_add):
            if entry.target.id != member.id:
                continue
            inviter = entry.user
            if is_self_action(inviter) or await check_user_protected(member.guild, inviter.id):
                return
            current_time = utcnow()
            tracker = security.bot_add_tracker[guild_id]
            count = track_action(tracker, inviter.id, current_time, security.TIME_WINDOW)
            if count >= security.BOT_ADD_LIMIT:
                try:
                    await member.kick(reason="Unauthorized bot")
                except Exception as exc:
                    print(f"Unauthorized bot kick failed: {exc}")
                await neutralize_roles(member.guild, f"Unauthorized bot addition by {inviter} ({inviter.id})")
                result = await punish_attacker(member.guild, inviter, "Adding unauthorized bots")
                embed = discord.Embed(
                    title="Bot Addition Attack",
                    description=f"User: {inviter.mention} (`{inviter.id}`)\nBot: {member.name}\nAction: {result}",
                    color=discord.Color.dark_red(),
                    timestamp=utcnow(),
                )
                await log_event(member.guild, embed)
            break
    except Exception as exc:
        print(f"on_member_join bot check failed: {exc}")


@bot.event
async def on_guild_channel_delete(channel):
    guild_id = str(channel.guild.id)
    if not security.protection_enabled[guild_id]:
        return
    await asyncio.sleep(1)
    try:
        async for entry in channel.guild.audit_logs(limit=5, action=discord.AuditLogAction.channel_delete):
            if entry.target.id != channel.id:
                continue
            moderator = entry.user
            if is_self_action(moderator) or await check_user_protected(channel.guild, moderator.id):
                return
            current_time = utcnow()
            tracker = security.channel_delete_tracker[guild_id]
            count = track_action(tracker, moderator.id, current_time, security.TIME_WINDOW)
            if count >= security.CHANNEL_DELETE_LIMIT:
                await neutralize_roles(channel.guild, f"Channel deletion attack by {moderator} ({moderator.id})")
                result = await punish_attacker(channel.guild, moderator, "Mass channel deletion")
                embed = discord.Embed(
                    title="Channel Deletion Attack",
                    description=f"User: {moderator.mention} (`{moderator.id}`)\nChannels deleted: {count}\nAction: {result}",
                    color=discord.Color.dark_red(),
                    timestamp=utcnow(),
                )
                await log_event(channel.guild, embed)
            break
    except Exception as exc:
        print(f"on_guild_channel_delete failed: {exc}")


@bot.event
async def on_guild_channel_create(channel):
    guild_id = str(channel.guild.id)
    if not security.protection_enabled[guild_id]:
        return
    await asyncio.sleep(1)
    try:
        async for entry in channel.guild.audit_logs(limit=5, action=discord.AuditLogAction.channel_create):
            if entry.target.id != channel.id:
                continue
            creator = entry.user
            if is_self_action(creator) or await check_user_protected(channel.guild, creator.id):
                return
            current_time = utcnow()
            tracker = security.channel_create_tracker[guild_id]
            count = track_action(tracker, creator.id, current_time, security.TIME_WINDOW)
            created = security.attacker_created_channels[guild_id][creator.id]
            created[channel.id] = current_time
            prune_created_records(created, current_time)
            if count >= security.CHANNEL_CREATE_LIMIT:
                await neutralize_roles(channel.guild, f"Channel spam attack by {creator} ({creator.id})")
                result = await punish_attacker(channel.guild, creator, "Mass channel creation")
                for channel_id in list(created.keys()):
                    created_channel = channel.guild.get_channel(channel_id)
                    if created_channel is None:
                        continue
                    try:
                        await created_channel.delete(reason="Cleaning up channel spam")
                    except Exception as exc:
                        print(f"Spam channel delete failed for {channel_id}: {exc}")
                created.clear()
                embed = discord.Embed(
                    title="Channel Spam Attack",
                    description=f"User: {creator.mention} (`{creator.id}`)\nChannels created: {count}\nAction: {result}",
                    color=discord.Color.dark_red(),
                    timestamp=utcnow(),
                )
                await log_event(channel.guild, embed)
            break
    except Exception as exc:
        print(f"on_guild_channel_create failed: {exc}")


@bot.event
async def on_guild_role_delete(role):
    guild_id = str(role.guild.id)
    if not security.protection_enabled[guild_id]:
        return
    await asyncio.sleep(1)
    try:
        async for entry in role.guild.audit_logs(limit=5, action=discord.AuditLogAction.role_delete):
            if entry.target.id != role.id:
                continue
            moderator = entry.user
            if is_self_action(moderator) or await check_user_protected(role.guild, moderator.id):
                return
            current_time = utcnow()
            tracker = security.role_delete_tracker[guild_id]
            count = track_action(tracker, moderator.id, current_time, security.TIME_WINDOW)
            if count >= security.ROLE_DELETE_LIMIT:
                await neutralize_roles(role.guild, f"Role deletion attack by {moderator} ({moderator.id})")
                result = await punish_attacker(role.guild, moderator, "Mass role deletion")
                embed = discord.Embed(
                    title="Role Deletion Attack",
                    description=f"User: {moderator.mention} (`{moderator.id}`)\nRoles deleted: {count}\nAction: {result}",
                    color=discord.Color.dark_red(),
                    timestamp=utcnow(),
                )
                await log_event(role.guild, embed)
            break
    except Exception as exc:
        print(f"on_guild_role_delete failed: {exc}")


@bot.event
async def on_guild_role_create(role):
    guild_id = str(role.guild.id)
    if not security.protection_enabled[guild_id]:
        return
    await asyncio.sleep(1)
    try:
        async for entry in role.guild.audit_logs(limit=5, action=discord.AuditLogAction.role_create):
            if entry.target.id != role.id:
                continue
            creator = entry.user
            if is_self_action(creator) or await check_user_protected(role.guild, creator.id):
                return
            current_time = utcnow()
            tracker = security.role_create_tracker[guild_id]
            count = track_action(tracker, creator.id, current_time, security.TIME_WINDOW)
            created = security.attacker_created_roles[guild_id][creator.id]
            created[role.id] = current_time
            prune_created_records(created, current_time)
            if count >= security.ROLE_CREATE_LIMIT:
                await neutralize_roles(role.guild, f"Role spam attack by {creator} ({creator.id})")
                result = await punish_attacker(role.guild, creator, "Mass role creation")
                for role_id in list(created.keys()):
                    created_role = role.guild.get_role(role_id)
                    if created_role is None:
                        continue
                    try:
                        await created_role.delete(reason="Cleaning up role spam")
                    except Exception as exc:
                        print(f"Spam role delete failed for {role_id}: {exc}")
                created.clear()
                embed = discord.Embed(
                    title="Role Spam Attack",
                    description=f"User: {creator.mention} (`{creator.id}`)\nRoles created: {count}\nAction: {result}",
                    color=discord.Color.dark_red(),
                    timestamp=utcnow(),
                )
                await log_event(role.guild, embed)
            break
    except Exception as exc:
        print(f"on_guild_role_create failed: {exc}")


@bot.event
async def on_webhooks_update(channel):
    guild_id = str(channel.guild.id)
    if not security.protection_enabled[guild_id]:
        return
    await asyncio.sleep(1)
    try:
        async for entry in channel.guild.audit_logs(limit=5, action=discord.AuditLogAction.webhook_create):
            target_channel_id = getattr(entry.target, "channel_id", None)
            target_channel = getattr(entry.target, "channel", None)
            if target_channel_id is None and target_channel is not None:
                target_channel_id = target_channel.id
            if target_channel_id != channel.id:
                continue
            creator = entry.user
            if is_self_action(creator) or await check_user_protected(channel.guild, creator.id):
                return
            current_time = utcnow()
            tracker = security.webhook_create_tracker[guild_id]
            count = track_action(tracker, creator.id, current_time, security.TIME_WINDOW)
            if count >= security.WEBHOOK_CREATE_LIMIT:
                await neutralize_roles(channel.guild, f"Webhook spam attack by {creator} ({creator.id})")
                result = await punish_attacker(channel.guild, creator, "Creating spam webhooks")
                try:
                    await entry.target.delete(reason="Cleaning up webhook spam")
                except Exception as exc:
                    print(f"Webhook delete failed: {exc}")
                embed = discord.Embed(
                    title="Webhook Attack",
                    description=f"User: {creator.mention} (`{creator.id}`)\nWebhooks: {count}\nAction: {result}",
                    color=discord.Color.dark_red(),
                    timestamp=utcnow(),
                )
                await log_event(channel.guild, embed)
            break
    except Exception as exc:
        print(f"on_webhooks_update failed: {exc}")


@bot.tree.command(name="whitelist", description="Add a user or role to the security whitelist")
@app_commands.describe(target="User or role to whitelist", target_type="Whether target is a user or role")
@app_commands.choices(
    target_type=[
        app_commands.Choice(name="User", value="user"),
        app_commands.Choice(name="Role", value="role"),
    ]
)
@is_owner_only()
async def whitelist(interaction: discord.Interaction, target: str, target_type: str):
    guild_id = str(interaction.guild_id)
    target_id = parse_snowflake(target)
    if target_id is None:
        await interaction.response.send_message("Target must contain a valid Discord ID or mention.", ephemeral=True)
        return
    if target_type == "user":
        user = interaction.guild.get_member(target_id)
        if user is None:
            try:
                user = await bot.fetch_user(target_id)
            except Exception:
                await interaction.response.send_message("User not found.", ephemeral=True)
                return
        security.whitelisted_users[guild_id].add(user.id)
        security.save_data()
        await interaction.response.send_message(f"{user.mention} added to whitelist.", ephemeral=True)
        return
    role = interaction.guild.get_role(target_id)
    if role is None:
        await interaction.response.send_message("Role not found.", ephemeral=True)
        return
    security.whitelisted_roles[guild_id].add(role.id)
    security.save_data()
    await interaction.response.send_message(f"{role.name} added to whitelist.", ephemeral=True)


@bot.tree.command(name="unwhitelist", description="Remove a user or role from the security whitelist")
@app_commands.describe(target="User or role to remove", target_type="Whether target is a user or role")
@app_commands.choices(
    target_type=[
        app_commands.Choice(name="User", value="user"),
        app_commands.Choice(name="Role", value="role"),
    ]
)
@is_owner_only()
async def unwhitelist(interaction: discord.Interaction, target: str, target_type: str):
    guild_id = str(interaction.guild_id)
    target_id = parse_snowflake(target)
    if target_id is None:
        await interaction.response.send_message("Target must contain a valid Discord ID or mention.", ephemeral=True)
        return
    if target_type == "user":
        security.whitelisted_users[guild_id].discard(target_id)
        security.save_data()
        await interaction.response.send_message("User removed from whitelist.", ephemeral=True)
        return
    security.whitelisted_roles[guild_id].discard(target_id)
    security.save_data()
    await interaction.response.send_message("Role removed from whitelist.", ephemeral=True)


@bot.tree.command(name="whitelist_list", description="View whitelisted users and roles")
@is_owner_or_whitelisted()
async def whitelist_list(interaction: discord.Interaction):
    guild_id = str(interaction.guild_id)
    embed = discord.Embed(title="Security Whitelist", color=discord.Color.dark_green())
    users = []
    for user_id in sorted(security.whitelisted_users[guild_id]):
        member = interaction.guild.get_member(user_id)
        users.append(f"{member.mention} (`{user_id}`)" if member else f"Unknown User (`{user_id}`)")
    roles = []
    for role_id in sorted(security.whitelisted_roles[guild_id]):
        role = interaction.guild.get_role(role_id)
        roles.append(f"{role.mention} (`{role_id}`)" if role else f"Unknown Role (`{role_id}`)")
    embed.add_field(name="Whitelisted Users", value="\n".join(users) or "None", inline=False)
    embed.add_field(name="Whitelisted Roles", value="\n".join(roles) or "None", inline=False)
    await interaction.response.send_message(embed=embed, ephemeral=True)


@bot.tree.command(name="protection", description="Enable or disable security protection")
@app_commands.describe(state="Enable or disable protection")
@app_commands.choices(
    state=[
        app_commands.Choice(name="Enable", value="enable"),
        app_commands.Choice(name="Disable", value="disable"),
    ]
)
@is_owner_only()
async def protection(interaction: discord.Interaction, state: str):
    guild_id = str(interaction.guild_id)
    security.protection_enabled[guild_id] = state == "enable"
    security.save_data()
    if state == "enable":
        await snapshot_guild(interaction.guild)
    await interaction.response.send_message(f"Protection {state}d.", ephemeral=True)


@bot.tree.command(name="setlog", description="Set the logging channel for security events")
@app_commands.describe(channel="Channel for security logs")
@is_owner_only()
async def setlog(interaction: discord.Interaction, channel: discord.TextChannel):
    guild_id = str(interaction.guild_id)
    security.log_channels[guild_id] = str(channel.id)
    security.save_data()
    await interaction.response.send_message(f"Log channel set to {channel.mention}.", ephemeral=True)


@bot.tree.command(name="snapshot", description="Create a server snapshot for recovery")
@is_owner_only()
async def snapshot(interaction: discord.Interaction):
    await interaction.response.defer(ephemeral=True)
    snapshot_data = await snapshot_guild(interaction.guild)
    embed = discord.Embed(
        title="Server Snapshot Created",
        description=f"Roles: {len(snapshot_data['roles'])}\nChannels: {len(snapshot_data['channels'])}",
        color=discord.Color.dark_green(),
        timestamp=utcnow(),
    )
    await interaction.followup.send(embed=embed, ephemeral=True)


@bot.tree.command(name="thresholds", description="Configure security thresholds")
@app_commands.describe(
    bans="Max bans before trigger",
    kicks="Max kicks before trigger",
    mentions="Max @everyone mentions before trigger",
    channels="Max channel creates/deletes before trigger",
    roles="Max role creates/deletes before trigger",
)
@is_owner_only()
async def thresholds(
    interaction: discord.Interaction,
    bans: int | None = None,
    kicks: int | None = None,
    mentions: int | None = None,
    channels: int | None = None,
    roles: int | None = None,
):
    values = {"bans": bans, "kicks": kicks, "mentions": mentions, "channels": channels, "roles": roles}
    invalid = [name for name, value in values.items() if value is not None and value < 1]
    if invalid:
        await interaction.response.send_message(f"Thresholds must be at least 1: {', '.join(invalid)}.", ephemeral=True)
        return
    if bans is not None:
        security.BAN_LIMIT = bans
    if kicks is not None:
        security.KICK_LIMIT = kicks
    if mentions is not None:
        security.MENTION_LIMIT = mentions
    if channels is not None:
        security.CHANNEL_CREATE_LIMIT = channels
        security.CHANNEL_DELETE_LIMIT = channels
    if roles is not None:
        security.ROLE_CREATE_LIMIT = roles
        security.ROLE_DELETE_LIMIT = roles
    security.save_data()
    embed = discord.Embed(title="Current Thresholds", color=discord.Color.dark_blue())
    embed.add_field(name="Bans / Kicks", value=f"{security.BAN_LIMIT} / {security.KICK_LIMIT} per 10 min", inline=True)
    embed.add_field(name="Mentions", value=f"{security.MENTION_LIMIT} per 10 min", inline=True)
    embed.add_field(name="Channel Ops", value=f"{security.CHANNEL_CREATE_LIMIT} per 10 min", inline=True)
    embed.add_field(name="Role Ops", value=f"{security.ROLE_CREATE_LIMIT} per 10 min", inline=True)
    await interaction.response.send_message(embed=embed, ephemeral=True)


@bot.tree.command(name="raidconfig", description="Configure anti-raid settings")
@app_commands.describe(
    message_threshold="Number of similar messages to trigger",
    similarity="Similarity percentage from 1 to 100",
    time_window="Time window in seconds",
)
@is_owner_only()
async def raidconfig(
    interaction: discord.Interaction,
    message_threshold: int | None = None,
    similarity: int | None = None,
    time_window: int | None = None,
):
    if message_threshold is not None and message_threshold < 5:
        await interaction.response.send_message("Message threshold must be at least 5.", ephemeral=True)
        return
    if similarity is not None and not 1 <= similarity <= 100:
        await interaction.response.send_message("Similarity must be between 1 and 100.", ephemeral=True)
        return
    if time_window is not None and time_window < 10:
        await interaction.response.send_message("Time window must be at least 10 seconds.", ephemeral=True)
        return
    if message_threshold is not None:
        security.RAID_MESSAGE_THRESHOLD = message_threshold
    if similarity is not None:
        security.RAID_SIMILARITY_THRESHOLD = similarity / 100
    if time_window is not None:
        security.RAID_TIME_WINDOW = time_window
    security.save_data()
    embed = discord.Embed(title="Anti-Raid Configuration", color=discord.Color.dark_blue())
    embed.add_field(name="Message Threshold", value=str(security.RAID_MESSAGE_THRESHOLD), inline=True)
    embed.add_field(name="Similarity", value=f"{security.RAID_SIMILARITY_THRESHOLD * 100:.0f}%", inline=True)
    embed.add_field(name="Time Window", value=f"{security.RAID_TIME_WINDOW}s", inline=True)
    await interaction.response.send_message(embed=embed, ephemeral=True)


@bot.tree.command(name="unlock", description="Restore channel permissions after raid lockdown")
@is_owner_only()
async def unlock(interaction: discord.Interaction):
    guild_id = str(interaction.guild_id)
    if not security.raid_lockdown[guild_id]:
        await interaction.response.send_message("No active lockdown.", ephemeral=True)
        return
    await interaction.response.defer(ephemeral=True)
    restored = 0
    failed = []
    for channel_id in list(security.locked_channels[guild_id]):
        channel = interaction.guild.get_channel(channel_id)
        backup = security.channel_overwrite_backups[guild_id].get(channel_id)
        if not isinstance(channel, discord.TextChannel) or backup is None:
            failed.append(str(channel_id))
            continue
        try:
            overwrites = await deserialise_overwrites(interaction.guild, backup)
            await channel.edit(overwrites=overwrites, reason="Raid lockdown restore")
            restored += 1
            security.channel_overwrite_backups[guild_id].pop(channel_id, None)
            security.locked_channels[guild_id].discard(channel_id)
        except Exception as exc:
            print(f"Unlock failed for channel {channel_id}: {exc}")
            failed.append(str(channel_id))

    security.raid_lockdown[guild_id] = bool(security.locked_channels[guild_id])
    security.raid_messages[guild_id].clear()
    security.raid_users[guild_id].clear()
    security.save_data()

    embed = discord.Embed(
        title="Channels Unlocked",
        description=f"Restored: {restored}\nFailed/skipped: {len(failed)}",
        color=discord.Color.dark_green() if not failed else discord.Color.orange(),
        timestamp=utcnow(),
    )
    if failed:
        embed.add_field(name="Manual Review Needed", value=", ".join(failed[:20]), inline=False)
    await log_event(interaction.guild, embed)
    await interaction.followup.send(embed=embed, ephemeral=True)


@bot.tree.command(name="restore", description="Restore role permissions from security backups")
@is_owner_only()
async def restore(interaction: discord.Interaction):
    guild_id = str(interaction.guild_id)
    if not security.role_backups[guild_id]:
        await interaction.response.send_message("No role backups found.", ephemeral=True)
        return
    await interaction.response.defer(ephemeral=True)
    restored = 0
    failed = []
    for role_id, permissions_value in list(security.role_backups[guild_id].items()):
        role = interaction.guild.get_role(role_id)
        if role is None:
            failed.append(str(role_id))
            continue
        try:
            await role.edit(permissions=discord.Permissions(permissions_value), reason="Role restoration")
            restored += 1
            security.role_backups[guild_id].pop(role_id, None)
            await asyncio.sleep(0.5)
        except Exception as exc:
            print(f"Failed to restore role {role.name} ({role.id}): {exc}")
            failed.append(str(role_id))
    security.save_data()

    embed = discord.Embed(
        title="Role Restore Complete",
        description=f"Restored: {restored}\nFailed/skipped: {len(failed)}",
        color=discord.Color.dark_green() if not failed else discord.Color.orange(),
        timestamp=utcnow(),
    )
    if failed:
        embed.add_field(name="Backups Kept For", value=", ".join(failed[:20]), inline=False)
    await interaction.followup.send(embed=embed, ephemeral=True)


async def send_command_error(interaction: discord.Interaction, message: str):
    if interaction.response.is_done():
        await interaction.followup.send(message, ephemeral=True)
    else:
        await interaction.response.send_message(message, ephemeral=True)


@whitelist.error
@unwhitelist.error
@whitelist_list.error
@protection.error
@setlog.error
@snapshot.error
@thresholds.error
@raidconfig.error
@unlock.error
@restore.error
async def command_error(interaction: discord.Interaction, error):
    if isinstance(error, app_commands.CheckFailure):
        await send_command_error(interaction, "You do not have permission to use this command.")
        return
    print(f"Command error: {error}")
    await send_command_error(interaction, "An error occurred.")


if __name__ == "__main__":
    require_env("DATA_SECRET", min_length=32)
    token = require_env("DISCORD_TOKEN", min_length=20)
    bot.run(token)
