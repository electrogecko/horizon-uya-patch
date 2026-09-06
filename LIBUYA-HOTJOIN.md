# libuya changes made for mid-game hotjoin

Everything the hotjoin work added to `libuya/`, why each entry exists, and what is known
about it. Branch `hotjoin-ig-join`.

Two files are touched:

| File | Change |
| --- | --- |
| `libuya/src/functions.S` | 11 `internal_hj*` address symbols |
| `libuya/src/gamesettings.c` + `.h` | `gameSyncSettings()` |

Nothing else in libuya is modified. No existing symbol was moved or repointed.

> **Caveat on the diff of commit `3ac0fab`.** It shows 1091 changed lines in
> `functions.S`, but 543 of those are pure CRLF line-ending churn from an editor. The
> real content is three added `FUNCTION` lines. Do not read that diff as a rewrite.

---

## 1. `gameSyncSettings()` — `libuya/src/gamesettings.c`

```c
void gameSyncSettings(void)
{
    GameSettings* gs = gameGetSettings();
    if (!gs)
        return;

    u32 netCtx = *(u32*)0x0024d860;      // 0x0024d760 on PAL
    if (!netCtx || !*(u32*)netCtx)
        return;

    internal_netUpdatetNWGameSettings(
        CLIENT_UPDATE_A0, 0,
        gs->PlayerNames[0], gs->PlayerSkins[0], gs->PlayerTeams[0], gs->PlayerStates[0],
        (u32)gs + 0x80);
}
```

**Why.** A late joiner needs the *current* `tNW_GameSettings` in order to appear in a
roster slot at all. Vanilla broadcasts settings during staging and then stops, so an
in-game host never re-sends them and a joiner arriving mid-match has nothing to receive.
This makes the in-game host keep publishing.

**Driven from** `patch/main.c` at ~line 2560, gated `isInGame() && gameAmIHost()`, every
5 frames (~80 ms).

**Follows the file's existing pattern.** `gamesettings.c` already had
`gameSetPlayerState`/`gameSetPlayerTeam` calling the same `internal_netUpdatetNWGameSettings`
with the same `CLIENT_UPDATE_A0` macro; this reuses both. Both PAL and NTSC context
pointers are handled, matching the `#if UYA_PAL` split already in the file.

**Verified**: the joiner receives the settings blob and populates its roster
(`clients=0 1  states=7 0`) on every attempt.

---

## 2. Address symbols — `libuya/src/functions.S`

All inside the existing `#ifndef UYA_PAL` block in the NET section. **NTSC only** — none
of these has a PAL equivalent yet, and every one would need re-deriving for PAL.

### Peer / session layer (base exe, map-independent)

| Symbol | Address | What it is | Confidence |
| --- | --- | --- | --- |
| `internal_hjResolvePlayerCtx` | `0x0016ed00` | Resolves the session context; returns non-zero on failure, writes the object to `*a1` | Confirmed — the NULL return is the `0x199c6c` fault |
| `internal_hjSendPeerConnectReq` | `0x0014ecd8` | Sends a **tracked peer-connect request** (allocates a slot in the 28-byte-stride table at `0x1FA718`, sends internal message id 1) | Confirmed. **Not a disconnect** — an early misreading of this cost us a working retransmit |
| `internal_hjPeerConnectCtor` | `0x00199ba0` | Constructs the missing peer-registration object | Confirmed in use |
| `internal_hjPeerLookup` | `0x0014f8e8` | `peers, idx -> record*`; bounds-checks `idx < 256`, returns NULL when absent | Confirmed |
| `internal_hjPeerClose` | `0x0014cea8` | Fires disconnect callbacks, then `peerReset 0x14c658` = `memset(rec, 0, 40)` | Confirmed by disassembly + runtime |
| `internal_hjNetLeaveGame` | `0x00195900` | Leave-session entry. With flag `0x001A5FC0 == 0` it is **asynchronous**: sends peer msg 42, sets state 9, queues completion `0x196088` | Confirmed by disassembly + runtime |
| `internal_hjIntroducePeer` | `0x00173fc0` | Introduces a peer; issues the connect request 3x for redundancy | Confirmed |
| `internal_hjMarkConnected` | `0x00172898` | Writes the real connected marker (`peer->0x08 = 5`). Called from `0x172668` only when the peer index equals `peers->0x408` | Confirmed. **Do not call directly** — its tail calls `0x171d18` and a peer-connected callback, and doing so cost the host its host status |
| `internal_hjSendPeerMsg` | `0x0014bdb0` | Sends a peer message; `idx == -1` is broadcast. The outgoing **type is read from our own record** (`myRec->0x08`), not passed in | Confirmed by disassembly |

### Remote-player lifecycle (base exe, calls into the level overlay)

| Symbol | Address | What it is |
| --- | --- | --- |
| `internal_hjSpawnRemotePlayer` | `0x001999b8` | Loads the level-registered create callback from `0x002407D0`, calls it, sets `bCallbackCalled` (+0x1a6) |
| `internal_hjDeleteRemotePlayer` | `0x00199a40` | The delete twin. Loads `0x002407D4`, calls it, then `netClientIndex = -1`, `+0x1a0 = 0`, `bSpawned = 0`, `bCallbackCalled = 0` |

Both confirmed against a runtime dump on a Metropolis host: the callback slots held
`0x0052a270` (`playerCreateRemoteForSession_Metropolis`) and `0x0052aba0`
(`playerDeleteRemoteForSession_Metropolis`), matching the decomp exactly.

`0x00199a40` self-guards at `0x00199a80` against wiping our own client entry. Clearing
`cid` to `-1` is what stops `hjHostSpawnRemotes` rebuilding the player next frame, since
it requires `cid >= 0`.

`functions.S` carries an instruction-level annotation for `0x00199a40` — keep it. It is
the evidence for a symbol that cannot be found any other way.

---

## Addresses used by the patch but deliberately NOT symbolised

These are data, tables, or hook sites rather than callable functions, so they live as
`#define`s in `patch/ui.c` instead:

```
0x002412F0  pad table            0x00225900  P1 pad (stride 0x1700)
0x0022F550  tNW_Player array     stride 0xC70, 8 slots
0x001A1CF0  net ctx ptr          +0xE4 last-activity, +0xE8 peers
0x001A1CB8  net clock ptr        +0x50 now
0x001A5E50  leave state machine  +0x120 state, +0x170 leave-now flag
0x001dd970  message-received handler table   (handler 0 = 0x199c40 registerPlayerBit)
0x001dd9b0  message-retired handler table    (handler 0 = 0x199cb8)
0x001d883c  ctx+0x1C = 0x171ee8, the real leave
0x0014f130  sweep comparison — verified INTACT, deliberately not patched
```

---

## PAL status

**Every `internal_hj*` symbol is NTSC-only.** The `#ifndef UYA_PAL` guard means a PAL
build compiles, but every hotjoin entry point compiles to an empty stub in `ui.c`. PAL
support needs all 11 addresses re-derived. `gameSyncSettings()` is the one exception —
it handles both.

## How these addresses were derived

From `/srv/nas2/uya/temp_staging_dump/ntsc.27.Lobby.bin`, a 32 MB EE RAM image where
**file offset == virtual address**:

```
mipsel-linux-gnu-objdump -b binary -m mips -EL -D \
  --start-address=0xSTART --stop-address=0xEND ntsc.27.Lobby.bin
```

**Do not use `iso_extract/NETGUI_NTGUI.ELF`.** Its `.text` is mapped at the same
`0x00100000` and its Ghidra symbol table lists matching `FUN_00xxxxxx` names, but the
bytes disagree with the running image everywhere that matters — it is a different build.
Its decompile is also 4219/4424 `halt_baddata`.

Overlay code (`0x005xxxxx`) comes from
`uya_decomp_local/decomp_exports/level44_overlay_wrench.*` (Metropolis only).

**An overlay address must never be stored anywhere that outlives a level.** Writing
Metropolis's `0x00534568` into a static structure crashed the joiner on Bakisi with
`TLB Miss, pc=0x534568`. Anything per-level needs `VariableAddress_t` treatment.
