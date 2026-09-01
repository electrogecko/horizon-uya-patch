#include <tamtypes.h>
#include <libuya/string.h>
#include <libuya/game.h>
#include <libuya/gamesettings.h>
#include <libuya/pad.h>
#include <libuya/stdio.h>
#include <libuya/uya.h>
#include <libuya/random.h>
#include <libuya/sha1.h>
#include <libuya/time.h>
#include <libuya/ui.h>
#include <libuya/graphics.h>
#include <libuya/utils.h>
#include <libuya/net.h>
#include "messageid.h"
#include "config.h"

#ifdef UYA_PAL
// UI Functions
#define STAGING_BASE_FUNC (0x006c1730)
#define CREATE_GAME_BASE_FUNC (0x0069a630)
#define ADVANCED_OPTIONS_BASE_FUNC (0x0069ce50)
// #define BUDDIES_BASE_FUNC (0x00690de8)
// #define PLAYER_DETAILS_BASE_FUNC (0x006b48c8)
// #define STATS_BASE_FUNC (0x006c5cc8)
#define KEYBOARD_BASE_FUNC (0x6aaa08)

// Needed Staging Functions
#define OPTION_REQUEST_TEAM_CHANGE_BASE_FUNC (0x006c4360)
#define BUDDY_IGNORE_LIST_PTR (*(u32*)0x0024d760)
#define GET_BUDDY_LIST_BASE_FUNC (0x006cd768)
#define GET_IGNORE_LIST_BASE_FUNC (0x006d5d68)
// #define OPTION_ADD_BUDDY_BASE_FUNC (0x006cdc30)
// #define OPTION_REMOVE_BUDDY_BASE_FUNC (0x006cddb0)
#define OPTION_IGNORE_PLAYER_BASE_FUNC (0x006d6210)
#define OPTION_UNIGNORE_PLAYER_BASE_FUNC (0x006d6398)
#else
// UI Functions
#define STAGING_BASE_FUNC (0x006bec18)
#define CREATE_GAME_BASE_FUNC (0x00697e20)
#define ADVANCED_OPTIONS_BASE_FUNC (0x0069a640)
// #define BUDDIES_BASE_FUNC (0x0068e6f8)
// #define PLAYER_DETAILS_BASE_FUNC (0x006b1f60)
// #define STATS_BASE_FUNC (0x006c31b8)
#define KEYBOARD_BASE_FUNC (0x006a80b8)

// Needed Staging Functions
#define OPTION_REQUEST_TEAM_CHANGE_BASE_FUNC (0x006c1848)
#define BUDDY_IGNORE_LIST_PTR (*(u32*)0x0024d860)
#define GET_BUDDY_LIST_BASE_FUNC (0x006cafe0)
#define GET_IGNORE_LIST_BASE_FUNC (0x006d35d8)
// #define OPTION_ADD_BUDDY_BASE_FUNC (0x006cb4a8)
// #define OPTION_REMOVE_BUDDY_BASE_FUNC (0x006cb628)
#define OPTION_IGNORE_PLAYER_BASE_FUNC (0x006d3a80)
#define OPTION_UNIGNORE_PLAYER_BASE_FUNC (0x006d3c08)
#endif

#define MAX_BUDDIES (64)
#define MAX_IGNORED (25)
#define OPTIONS_SCROLL_CHECK ((u32)STAGING_BASE_FUNC + 0xae0)
#define BUDDY_LIST_STACK (*(u32*)(BUDDY_IGNORE_LIST_PTR + 0x34))
#define BUDDY_LIST_COUNT (*(int*)(BUDDY_LIST_STACK + *(int*)(BUDDY_LIST_STACK + 0x4) * 0xc + 0x2c))
#define BUDDY_LIST_START (*(u32*)(BUDDY_LIST_STACK + 0x40) + 0x10)
#define BUDDY_LIST_END (*(u32*)(BUDDY_LIST_STACK + 0x40) + 0x1c)
#define IGNORE_LIST_STACK (*(u32*)(BUDDY_IGNORE_LIST_PTR + 0x40))
#define IGNORE_LIST_COUNT (*(int*)(IGNORE_LIST_STACK + *(int*)(IGNORE_LIST_STACK + 0x4) * 0xc + 0x2c))
#define IGNORE_LIST_START (*(u32*)(IGNORE_LIST_STACK + 0x40) + 0x10)
#define IGNORE_LIST_END (*(u32*)(IGNORE_LIST_STACK + 0x40) + 0x1c)

typedef enum playerOptions {
    PLAYER_OPTION_CANCEL = -1,
    PLAYER_OPTION_TEAMSKIN = 0,
    PLAYER_OPTION_KICK,
    PLAYER_OPTION_ADD_BUDDY,
    PLAYER_OPTION_IGNORE
} PlayerOptions_e;

typedef enum teamOptions {
    TEAM_OPTION_CANCEL = -1,
    TEAM_OPTION_RANDOM = 0,
    TEAM_OPTION_BLUE,
    TEAM_OPTION_RED,
    // TEAM_OPTION_TVB_BVR,
    // TEAM_OPTION_TVB_RVB,
    TEAM_OPTION_FFA
} TeamOptions_e;

typedef struct buddyIgnoreInfo {
/* 0x00 */ int currentWorldId;
/* 0x04 */ short buddyCount;
/* 0x06 */ short ignoredCount;
/* 0x08 */ char client_ids[GAME_MAX_PLAYERS];
/* 0x10 */ char buddies[GAME_MAX_PLAYERS];
/* 0x18 */ char ignored[GAME_MAX_PLAYERS];
} buddyIgnoreInfo_t;

typedef struct buddyListInfo { // 0xd0
/* 0x00 */ char messageID[21];
/* 0x18 */ int statusCode;
/* 0x1c */ int accountID;
/* 0x20 */ char accountName[32];
/* 0x40 */ char onlineState[0x8c];
/* 0xcc */ int EndOfList;
} buddyListInfo_t;

typedef struct ignoreListInfo { // 0x48
/* 0x00 */ char messageID[21];
/* 0x18 */ int statusCode;
/* 0x1c */ int accountID;
/* 0x20 */ char accountName[32];
/* 0x40 */ int onlinetatus;
/* 0x44 */ int EndOfList;
} ignoreListInfo_t;

typedef struct BuddyIgnoreRequest { // 0x2c
/* 0x00 */ char messageID[21];
/* 0x15 */ char sessionKey[17];
/* 0x28 */ int accountID;
} BuddyIgnoreRequest_t;

typedef struct keyboardNew { // 0x4
/* 0x0 */ u8 index;
/* 0x1 */char text[3];
} keyboardNew_t;

typedef int (*uiVTable_Func)(UiMenu_t * ui, int pad);
uiVTable_Func createGameFunc = (uiVTable_Func)CREATE_GAME_BASE_FUNC;
uiVTable_Func advancedOptionsFunc = (uiVTable_Func)ADVANCED_OPTIONS_BASE_FUNC;
uiVTable_Func stagingFunc = (uiVTable_Func)STAGING_BASE_FUNC;
// uiVTable_Func buddiesFunc = (uiVTable_Func)BUDDIES_BASE_FUNC;
// uiVTable_Func playerDetailsFunc = (uiVTable_Func)PLAYER_DETAILS_BASE_FUNC;
// uiVTable_Func statsFunc = (uiVTable_Func)STATS_BASE_FUNC;
uiVTable_Func keyboardFunc = (uiVTable_Func)KEYBOARD_BASE_FUNC;

typedef int (*buddy_Func)(int stack, int account_id);
buddy_Func getBuddyList = (buddy_Func)GET_BUDDY_LIST_BASE_FUNC;
buddy_Func getIgnoreList = (buddy_Func)GET_IGNORE_LIST_BASE_FUNC;
// buddy_Func addBuddy = (buddy_Func)OPTION_ADD_BUDDY_BASE_FUNC;
// buddy_Func removeBuddy = (buddy_Func)OPTION_REMOVE_BUDDY_BASE_FUNC;
buddy_Func ignorePlayer = (buddy_Func)OPTION_IGNORE_PLAYER_BASE_FUNC;
buddy_Func unignorePlayer = (buddy_Func)OPTION_UNIGNORE_PLAYER_BASE_FUNC;

typedef void (*requestTeamChange_Func)(void * ui, int index);
requestTeamChange_Func requestTeamChange = (requestTeamChange_Func)OPTION_REQUEST_TEAM_CHANGE_BASE_FUNC;

extern isConfigMenuActive;
extern mapOverrideResponse;

// --- hot-join instrumentation (temporary) --------------------------------
// printf goes to the PCSX2 EE console. Uses printf directly rather than
// DPRINTF so it does not require -DDEBUG, which would enable every DPRINTF
// in the patch at 60fps. Remove once the in-game join path is understood.
#define HOTJOIN_LOG(fmt, args...)   printf("HJ " fmt, ##args)

// ---------------------------------------------------------------------------
// Hotjoin: guard the per-player registration that faults for a late joiner.
//
// A joiner that reaches staging via the hotjoin path dies with
//   R5900 TLB Miss, addr=0x7c  [load] then [store]
// The faulting pair is at 0x199c98 / 0x199ca0 (PCSX2 reports the recompiled
// block address 0x199c6c, not the instruction). Reconstructed:
//
//   void f(void *a0, void *a1, int playerIndex) {           // 0x199c40
//       if (playerIndex == -2) return;
//       void *out = NULL;
//       if (resolve(&out, a1) != 0) return;
//       void *ctx = out->0x1C;
//       int   idx = ctx->0x54;
//       void *obj = (0x22F550 + idx * 3184)->0x04;          // NULL for a hotjoiner
//       obj->0x7C |= (1 << playerIndex);                    // <-- faults
//   }
//
// The function has no direct callers; it is reached through the vtable slot at
// 0x1DD970, so we replace it there the same way patchStaging replaces the
// staging handler. This is a diagnostic, not a fix: skipping the bit leaves the
// joiner unregistered with whatever subsystem this is. The point is to find out
// whether this is the only broken structure or the first of many, and to log
// idx so we can tell a legitimately-NULL object from a garbage table index.
// ---------------------------------------------------------------------------
#ifndef UYA_PAL
#define HJ_PLAYERBIT_VTABLE_SLOT    (0x001dd970)
#define HJ_PLAYERBIT_TABLE_BASE     (0x0022f550)
#define HJ_PLAYERBIT_TABLE_STRIDE   (3184)
#define HJ_PLAYERBIT_TABLE_MAXIDX   (64)

extern int internal_hjResolvePlayerCtx(void ** out, void * arg);
extern void internal_hjPeerConnectCtor(void * a0, void * a1);

static int hjPlayerBitInstalled = 0;
static int hjPlayerBitSkips = 0;
static int hjPlayerBitSeen = 0;

void hjRegisterPlayerBit(void * a0, void * a1, int playerIndex)
{
    void * out = 0;

    if (playerIndex == -2)
        return;

    if (internal_hjResolvePlayerCtx(&out, a1) != 0)
        return;

    if (!out) {
        HOTJOIN_LOG("playerbit: out=NULL idx? player=%d\n", playerIndex);
        return;
    }

    u32 ctx = *(u32*)((u32)out + 0x1C);
    if (!ctx) {
        HOTJOIN_LOG("playerbit: ctx=NULL player=%d\n", playerIndex);
        return;
    }

    int idx = *(int*)(ctx + 0x54);
    if (idx < 0 || idx >= HJ_PLAYERBIT_TABLE_MAXIDX) {
        HOTJOIN_LOG("playerbit: idx=%d OUT OF RANGE player=%d\n", idx, playerIndex);
        return;
    }

    u32 obj = *(u32*)(HJ_PLAYERBIT_TABLE_BASE + (idx * HJ_PLAYERBIT_TABLE_STRIDE) + 0x04);
    if (!obj) {
        // Construct-on-demand instead of masking. The game's own OnPeerConnect
        // handler at 0x199ba0 is the constructor of this entry: it resolves the
        // same a1, and if entry->0x04 is NULL it initializes the entry, stores
        // the peer pointer into entry->0x04 and zeroes peer->0x7C -- the exact
        // field the code below ORs into. On a hotjoin it never fires because the
        // host's peer record pre-exists by the time host traffic arrives, so the
        // create-on-first-sight path (0x172dc0 -> 0x16f208) is skipped. It is
        // idempotent (checks entry->0x04), touches only local state, and the one
        // hotjoin attempt where it happened to run got noticeably further.
        internal_hjPeerConnectCtor(a0, a1);
        obj = *(u32*)(HJ_PLAYERBIT_TABLE_BASE + (idx * HJ_PLAYERBIT_TABLE_STRIDE) + 0x04);
        HOTJOIN_LOG("playerbit: ctor-on-demand idx=%d id=%d -> obj=%08x\n",
            idx, playerIndex, obj);
    }
    if (!obj) {
        if ((hjPlayerBitSkips % 60) == 0)
            HOTJOIN_LOG("playerbit: SKIP obj=NULL idx=%d id=%d ra=%08x n=%d\n",
                idx, playerIndex, (u32)__builtin_return_address(0), hjPlayerBitSkips);
        ++hjPlayerBitSkips;
        return;
    }

    // Identify what this object is on a join where it exists. The first word of a
    // PS2 C++ object is its vtable pointer, which we can look up in the overlay to
    // name the class -- that tells us exactly which structure a hotjoiner is missing.
    if (!hjPlayerBitSeen) {
        hjPlayerBitSeen = 1;
        HOTJOIN_LOG("playerbit: OK obj=%08x idx=%d id=%d ra=%08x\n",
            obj, idx, playerIndex, (u32)__builtin_return_address(0));
    }

    *(u32*)(obj + 0x7C) |= (1 << playerIndex);
}

// ---------------------------------------------------------------------------
// Hotjoin: find (and optionally delay) the client-side give-up.
//
// A hotjoiner aborts ~250ms after connecting -- it emits 00-12-01 twice and then
// RT_MSG_CLIENT_DISCONNECT -- while a working join needs ~3.1s. Nothing the server
// sends can matter inside that window, so the race has to be closed on the client.
//
// 0x14ecd8 is the disconnect routine: it calls internal_netSendMessage with
// t0 = 1 = RT_MSG_CLIENT_DISCONNECT. It has exactly four call sites in the resident
// copy. Redirect all four through a pass-through that reports which one fired, so
// we can identify the abort path. Unlike every other diagnostic left in this file,
// this one keys off the FAILING case, which is reproducible on demand.
//
// Pure pass-through for now -- it changes no behaviour, it only reports.
// The give-up is a peer-timeout sweep at 0x14f120:
//
//   if (ctx->0xE4 + 3000 < now && ctx->0x430 == 1)
//       for (i = 0; i < ctx->0x43C; ++i)
//           if (peer(i) && i != myIndex && peer->0x1C)
//               disconnect(i);            // <-- 0x14f19c, the site that fired
//
// 3000 is a millisecond deadline, and a working join takes ~3.1s -- so a hotjoiner
// only gets in when it happens to press JOIN early in that free-running window.
// That is the whole race. Widen the deadline instead of trying to win it.
#define HJ_PEER_TIMEOUT_INSN  (0x0014f12c)   // addiu v0,v0,3000
#define HJ_PEER_TIMEOUT_NEW   (0x24427530)   // addiu v0,v0,30000

// The sweep accumulates its own clock (clk->0x50 += delta) and that accumulator
// jumps discontinuously -- 21015 -> 2927161 observed in one step. Refreshing
// ctx->0xE4 every frame keeps "stale" at one frame (~16ms) and STILL loses, because
// any jump larger than the 3000ms window expires us instantly. So stop the comparison
// instead of chasing the timestamp:
//
//   14f130: sltu v0,v0,a1    ->  move v0,zero
//   14f134: beqz v0,0x14f1d0     (now always taken; v0 is dead afterwards)
//
// This disables ONLY the peer-timeout sweep. Fine for a test sandbox; it would need
// gating before it went anywhere near a real build.
#define HJ_SWEEP_CMP_INSN (0x0014f130)
#define HJ_SWEEP_CMP_ORIG (0x0045102b)   // sltu v0,v0,a1
#define HJ_SWEEP_CMP_NEW  (0x0000102d)   // move v0,zero

#define HJ_NET_CTX_PTR    (0x001A1CF0)
#define HJ_NET_CLOCK_PTR  (0x001A1CB8)
#define HJ_CTX_LAST_ACT   (0xE4)
#define HJ_CTX_PEERS      (0xE8)
#define HJ_CLOCK_NOW      (0x50)

#define HJ_DISCONNECT_SITE_A  (0x0014f19c)
#define HJ_DISCONNECT_SITE_B  (0x0017415c)
#define HJ_DISCONNECT_SITE_C  (0x00174164)
#define HJ_DISCONNECT_SITE_D  (0x0017416c)

extern void internal_hjSendPeerConnectReq(int idx);   // 0x14ecd8


void hjPeerConnectReqHook(int idx)
{
    u32 ra = (u32)__builtin_return_address(0);

    // Report only -- this is the outgoing peer-connect request, not a disconnect.
    {
        u32 c = *(u32*)HJ_NET_CTX_PTR;
        HOTJOIN_LOG("peerconnreq: idx=%d ra=%08x ctx=%08x lastRetry=%u menus=%d gs=%p\n",
            idx, ra, c, c ? *(u32*)(c + HJ_CTX_LAST_ACT) : 0,
            isInMenus(), gameGetSettings());
    }

    internal_hjSendPeerConnectReq(idx);
}

// The sweep at 0x14f120 drops every peer when
//
//     ctx->0xE4 + 3000 < now        ctx = *(0x001A1CF0), now = (*(0x001A1CB8))->0x50
//
// ctx->0xE4 is a last-activity stamp that ordinary traffic keeps fresh. A hotjoiner's
// is stale or never set, so the deadline is already blown when it arrives -- which is
// why widening the 3000 constant did nothing, and why the failure looked like a race
// (it depends on where in the free-running window you press JOIN).
//
// Keep the stamp fresh while we are in menus instead of blocking the disconnect. The
// sweep still runs and still reaps genuinely dead peers everywhere else; we just stop
// looking dead ourselves. Every frame rather than once, because a single refresh only
// buys 3s and a normal join needs ~3.1s.

static int hjRefreshes = 0;

void hjRefreshPeerActivity(void)
{
    return;   // superseded by the sweep-comparison patch

    if (!isInMenus())
        return;

    u32 ctx = *(u32*)HJ_NET_CTX_PTR;
    if (!ctx || !*(u32*)(ctx + HJ_CTX_PEERS))
        return;

    u32 clk = *(u32*)HJ_NET_CLOCK_PTR;
    if (!clk)
        return;

    u32 now = *(u32*)(clk + HJ_CLOCK_NOW);
    u32 last = *(u32*)(ctx + HJ_CTX_LAST_ACT);

    // Refresh UNCONDITIONALLY every frame. Making this conditional on
    // "(last + 3000) < now" was wrong: it only fires once the deadline has ALREADY
    // passed, so it races the sweep inside the same frame and loses about half the
    // time. Observed cycle was refresh -> 3s -> sweep fires with exactly the value we
    // had written. A keepalive has to run before expiry, not after it.
    if (hjRefreshes < 4 || (hjRefreshes % 600) == 0)
        HOTJOIN_LOG("peeract: ctx=%08x last=%u now=%u stale=%d n=%d\n",
            ctx, last, now, (int)(now - last), hjRefreshes);
    ++hjRefreshes;

    *(u32*)(ctx + HJ_CTX_LAST_ACT) = now;
}

// ---------------------------------------------------------------------------
// Hotjoin: expose failure mode B (dies before ctx->0xE8 populates).
//
// The world-connect API is at 0x16f770(params, out), reached only through the
// pointer slot 0x1D884C inside the API block at 0x1D8820. It is SYNCHRONOUS:
// it validates, allocates from the RT pool (0x14a4f0 -> 0x14c1e8), assigns the
// peer table into ctx->0xE8, sends the connect, then pumps the net for up to
// 30s waiting for ctx->0x10C (server accept). Distinct error returns:
//   16 = API busy flag (0x1D8908) still set from a previous attempt
//   22 = pool record alloc failed (0x14a4f0 returned NULL)
//   23/38/15/8 = param validation
//   14 (out state 2) = 30s accept timeout, cleanup via 0x171ee8
// Both 16 and 22 are progressive-leak shaped -- prime mode-B suspects. This
// wrapper logs entry/exit so a silent failure becomes a named error, and
// "never called at all" becomes a diagnosis too (failure is then upstream in
// the medius/TCP stage, visible in DME logs).
// ---------------------------------------------------------------------------
#define HJ_CONNECT_SLOT       (0x001d884c)
#define HJ_CONNECT_ORIG       (0x0016f770)
#define HJ_API_BUSY_FLAG      (0x001d8908)
#define HJ_CTX_ACCEPT         (0x10C)

static int hjConnectCalls = 0;

int hjConnectHook(void * params, u32 * out)
{
    int (*orig)(void *, u32 *) = (int (*)(void *, u32 *))HJ_CONNECT_ORIG;
    u32 clk = *(u32*)HJ_NET_CLOCK_PTR;
    u32 t0 = clk ? *(u32*)(clk + HJ_CLOCK_NOW) : 0;
    u32 busy = *(u32*)HJ_API_BUSY_FLAG;
    u32 * p = (u32*)params;
    int n = ++hjConnectCalls;

    HOTJOIN_LOG("connect[%d] IN params=%08x out=%08x busy=%08x ctx=%08x\n",
        n, (u32)params, (u32)out, busy, *(u32*)HJ_NET_CTX_PTR);
    if (p)
        HOTJOIN_LOG("connect[%d] p0=%08x p4=%08x p8=%08x pC=%08x p14=%08x p18=%08x\n",
            n, p[0], p[1], p[2], p[3], p[5], p[6]);

    int ret = orig(params, out);

    u32 ctx = *(u32*)HJ_NET_CTX_PTR;
    u32 t1 = clk ? *(u32*)(clk + HJ_CLOCK_NOW) : 0;
    HOTJOIN_LOG("connect[%d] OUT ret=%d out0=%u out1=%u out2=%u accept=%08x busy=%08x dt=%u\n",
        n, ret, out ? out[0] : 0, out ? out[1] : 0, out ? out[2] : 0,
        ctx ? *(u32*)(ctx + HJ_CTX_ACCEPT) : 0, *(u32*)HJ_API_BUSY_FLAG, t1 - t0);
    return ret;
}

// ---------------------------------------------------------------------------
// Hotjoin: prove whether SERVER_CONNECT_ACCEPT_AUX_UDP (RT type 25) ever
// reaches the game. Server logs show every hotjoin attempt's UDP hello
// arriving and 3x accepts being sent back, yet the client aborts as if the
// accept never landed -- so the question is whether the loss is inbound
// (PCSX2 DEV9) or the accept is processed and some other gate fails.
//
// RT message handlers are registered via 0x151550(type, stack, fn) into a
// table at *(0x001A294C), slot = table + (stack*maxTypes + type)*4; stack 0.
// The table is allocated at net-init, not boot, so installation is deferred:
// call hjInstallAuxAcceptProbe() every frame until it sticks.
// ---------------------------------------------------------------------------
#define HJ_RT_HANDLER_TABLE_PTR   (0x001A294C)
#define HJ_RT_MAXTYPES_PTR        (0x001D2370)   // 0x1D2374 is MAX_STACKS, not maxTypes
#define HJ_RT_TYPE_ACCEPT_AUX_UDP (25)
#define HJ_AUX_ACCEPT_ORIG        (0x0014B500)
#define HJ_RT_MAX_STACKS          (4)

static int hjAuxAcceptInstalled = 0;
static int hjAuxAcceptCount = 0;
static u32 hjAuxAcceptOrig = 0;

int hjAuxAcceptHook(void * a0, void * a1, void * a2, void * a3)
{
    int (*orig)(void *, void *, void *, void *) =
        (int (*)(void *, void *, void *, void *))hjAuxAcceptOrig;
    int n = ++hjAuxAcceptCount;
    if (n <= 8)
        HOTJOIN_LOG("auxaccept[%d]: a0=%08x a1=%08x a2=%08x a3=%08x\n",
            n, (u32)a0, (u32)a1, (u32)a2, (u32)a3);
    return orig(a0, a1, a2, a3);
}

void hjInstallAuxAcceptProbe(void)
{
    if (hjAuxAcceptInstalled)
        return;

    u32 table = *(u32*)HJ_RT_HANDLER_TABLE_PTR;
    u32 maxTypes = *(u32*)HJ_RT_MAXTYPES_PTR;
    if (!table || !maxTypes || maxTypes > 256)
        return;

    // Handlers are registered per protocol stack: 0x151550 passes stack 0, 0x151578
    // passes stack 2, so slot = table + (stack*maxTypes + type)*4. A previous version
    // hooked stack 0 only and stayed silent even on SUCCESSFUL joins, which proved
    // nothing except that the aux-UDP accept is dispatched on a different stack.
    // Hook every stack whose slot 25 holds the expected handler, and report the lot.
    int hooked = 0;
    int stack;
    for (stack = 0; stack < HJ_RT_MAX_STACKS; ++stack) {
        u32 * slot = (u32*)(table + ((stack * maxTypes) + HJ_RT_TYPE_ACCEPT_AUX_UDP) * 4);
        HOTJOIN_LOG("auxaccept: stack%d slot25 @%08x = %08x\n", stack, (u32)slot, *slot);
        if (*slot == HJ_AUX_ACCEPT_ORIG) {
            hjAuxAcceptOrig = *slot;
            *slot = (u32)&hjAuxAcceptHook;
            ++hooked;
        }
    }

    hjAuxAcceptInstalled = 1;
    HOTJOIN_LOG("auxaccept: maxTypes=%d, hooked %d stack(s)\n", (int)maxTypes, hooked);
}

void hjInstallPlayerBitGuard(void)
{
    if (hjPlayerBitInstalled)
        return;

    hjPlayerBitInstalled = 1;
    // VERIFY BEFORE PATCHING. The clean NETGUI_NTGUI.ELF and the RAM dump disagree
    // about what lives at these addresses, so read what is ACTUALLY there at runtime
    // before writing anything. Expected from the dump:
    //   0x0014f19c = 0c053b36 (jal 0x14ecd8)   0x0014f12c = 24420bb8 (addiu v0,v0,3000)
    // Expected from the clean ELF:
    //   0x0014f19c = 8e030004 (lw v1,4(s0))    -- if we see this, the hooks are WRONG
    //                                             and must not be installed.
    HOTJOIN_LOG("verify: 14f19c=%08x 14f12c=%08x 14ecd8=%08x 1dd970=%08x 199c98=%08x\n",
        *(u32*)0x0014f19c, *(u32*)0x0014f12c, *(u32*)0x0014ecd8,
        *(u32*)HJ_PLAYERBIT_VTABLE_SLOT, *(u32*)0x00199c98);

    if (*(u32*)HJ_DISCONNECT_SITE_A != 0x0c053b36 ||
        *(u32*)HJ_SWEEP_CMP_INSN != HJ_SWEEP_CMP_ORIG) {
        HOTJOIN_LOG("verify: MISMATCH -- hooks NOT installed\n");
        return;
    }

    // DO NOT patch HJ_SWEEP_CMP_INSN. An earlier version wrote `move v0,zero` there
    // to "stop the peer-timeout sweep from disconnecting us". That reading was wrong:
    //   0x14ecd8 allocates a slot in the 28-byte-stride table at 0x1FA718 (0x14eb50,
    //   returns 127 when full) and sends internal message id 1 -- it is a TRACKED
    //   PEER-CONNECT REQUEST, not a disconnect. 0x173fc0 issues it three times for
    //   redundancy when introducing a peer, and the loop at 0x14f120 re-issues it to
    //   every not-yet-connected peer, rate-limited to once per 3000 ms by ctx->0xE4,
    //   which 0x14f1c8 stamps with `now` after the loop.
    // So this block is the RETRY for peer connection setup. Disabling it left every
    // join with exactly one chance for its connect request to survive, which is why
    // joins looked like pure packet loss and got worse as DEV9 grew lossier.
    // ctx->0xE4 starting at 0 is correct: it makes the first retry fire immediately.

    POKE_U32(HJ_PLAYERBIT_VTABLE_SLOT, &hjRegisterPlayerBit);

    HOOK_JAL(HJ_DISCONNECT_SITE_A, &hjPeerConnectReqHook);
    HOOK_JAL(HJ_DISCONNECT_SITE_B, &hjPeerConnectReqHook);
    HOOK_JAL(HJ_DISCONNECT_SITE_C, &hjPeerConnectReqHook);
    HOOK_JAL(HJ_DISCONNECT_SITE_D, &hjPeerConnectReqHook);

    if (*(u32*)HJ_CONNECT_SLOT == HJ_CONNECT_ORIG) {
        POKE_U32(HJ_CONNECT_SLOT, &hjConnectHook);
        HOTJOIN_LOG("connect hook installed at slot %08x\n", HJ_CONNECT_SLOT);
    } else {
        HOTJOIN_LOG("connect slot %08x holds %08x, expected %08x -- NOT hooked\n",
            HJ_CONNECT_SLOT, *(u32*)HJ_CONNECT_SLOT, HJ_CONNECT_ORIG);
    }

    HOTJOIN_LOG("guards installed: playerbit %08x, retransmit INTACT, 4 peer-connect-req sites\n",
        HJ_PLAYERBIT_VTABLE_SLOT);
}
#else
void hjInstallPlayerBitGuard(void) { }
void hjInstallAuxAcceptProbe(void) { }
void hjRefreshPeerActivity(void) { }
#endif
#define HOTJOIN_LOG_MAX_FRAMES      (240)

char changeTeamStr[] = "Change Team";
char kickPlayerStr[] = "Kick Player";
char addBuddyStr[] = "Add to Buddies";
char removeBuddyStr[] = "Remove Buddy";
char ignorePlayerStr[] = "Ignore Player";
char unignorePlayeStr[] = "Unignore Player";

char *playerOptions[4];

char *randomTeamOptions[4] = {
    "Random Teams",
    // "Top vs Bottom (BvR)",
    // "Top vs Buttom (RvB)",
    "All Blue",
    "All Red",
    "Free For All"
};

buddyIgnoreInfo_t info = {
    .currentWorldId = -1
};

keyboardNew_t keys[] = {
    {KEY_1, "\x08 D"}, // Default
    {KEY_2, "\x09 B"}, // Blue
    {KEY_3, "\x0aG"}, // Green
    {KEY_4, "\x0bP"}, // Pink
    {KEY_5, "\x0cW"}, // White
    {KEY_6, "\x0dG"}, // Gray
    {KEY_7, "\x0e B"}, // Black
    {KEY_8, "\x0f A"}, // Aqua
    {KEY_Q, "\x10"}, // Cross
    {KEY_W, "\x11"}, // Circle
    {KEY_E, "\x12"}, // Triangle
    {KEY_R, "\x13"}, // Square
    {KEY_T, "\x14"}, // L1
    {KEY_Y, "\x15"}, // R1
    {KEY_U, "\x16"}, // L2
    {KEY_I, "\x17"}, // R2
    {KEY_O, "\x18"}, // L3
    {KEY_P, "\x19"}, // R3
    {KEY_BRACKET_OPEN, "\x1a"} // Select
};

void setTeams(int numTeams)
{
    int i, j;
	u32 seed = timerGetSystemTime();
	char teamByClientId[GAME_MAX_PLAYERS];
	char Pool[GAME_MAX_PLAYERS];
    int PlayerSize;

	memset(teamByClientId, -1, sizeof(teamByClientId));
	// get game settings
	GameSettings* gameSettings = gameGetSettings();
	if (gameSettings) {
        // fill pool with needed teams
        PlayerSize = gameSettings->PlayerCount;
        for (i = 0; i < PlayerSize; ++i)
            Pool[i] = i % 2;

		for (i = 0; i < GAME_MAX_PLAYERS; ++i) {
			int clientId = gameSettings->PlayerClients[i];
			if (clientId >= 0) {
				int teamId = teamByClientId[clientId];
				if (teamId < 0) {
					if (PlayerSize == 0 || numTeams == TEAM_OPTION_BLUE || numTeams == TEAM_OPTION_RED) {
						teamId = numTeams - 1;
                    } else if (numTeams == TEAM_OPTION_FFA) {
                        teamId = i;
					} else if (numTeams == TEAM_OPTION_RANDOM) {
						// psuedo random
						sha1(&seed, 4, &seed, 4);

						// get pool index from rng
						int teamPoolIndex = seed % PlayerSize;

						// set team
						teamId = Pool[teamPoolIndex];

						// printf("\npool info pid: %d\npoolIndex: %d\npoolSize: %d\nteam: %d", i, teamPoolIndex, PlayerSize, teamId);

						// remove element from pool
						if (PlayerSize > 0) {
							for (j = teamPoolIndex+1; j < PlayerSize; ++j)
								Pool[j-1] = Pool[j];
                        
							PlayerSize -= 1;
						}
					}
					// set client id team
					teamByClientId[clientId] = teamId;
				}
				// set team
				// printf("\nsetting pid:%d  team to %d", i, teamId);
				gameSettings->PlayerTeams[i] = teamId;
			}
		}
	}
}

/*
 * This function is needed to return the correct
 * index of where the selected player is at.
 * If people leave/get kicked, it messes up
 * the selectedItem -> needed player order.
*/
int getPlayerIndex(void * ui,int selectedPlayer)
{
    GameSettings * gs = gameGetSettings();
    int uiElement = *(int*)(ui + (selectedPlayer + 0xf) * 4 + 0x110);
    long compareNames;
    int i = 0;
    while (((gs == 0 || (gs->PlayerClients[i] == -1)) || (compareNames = strcmp(uiElement + 0x14, gs->PlayerNames[i]), compareNames != 0))) {
        ++i;
        if (7 < i) return -1;
    }
    return i;
}

void optionChangeTeamSkin(void * ui, GameSettings * gs, int selectedItem, int isBot, int isTeams)
{
    // Get correct player index
    int i =  getPlayerIndex(ui, selectedItem);
    // Get the needed number of teams dependent on gametype.
    int numTeams = (gs->GameType == GAMETYPE_DM) ? 8 : 2;

    if (isBot) {
        // Open Team/Skin Menu
        uiShowChangeTeamSkinDialog(gs->PlayerTeams[i], gs->PlayerSkins[i], numTeams, isTeams, 1, 1);
        // Save chosen Team/Skin
        u32 getUI = uiGetMenu(UI_MENU_CHANGE_SKIN_TEAM);
        gs->PlayerTeams[i] = *(int*)(*(u32*)(getUI + 0x110) + 0x146c);
        gs->PlayerSkins[i] = *(int*)(*(u32*)(getUI + 0x114) + 0x146c);
    } else if (!isBot && isTeams) {
        // Keep this function just in case.
        // requestTeamChange(ui, selectedItem);
        int gsTeam = gs->PlayerTeams[i];
        // Change Teams depending on game type.
        int team = 0;
        if (gs->GameType == GAMETYPE_DM) {
            if (gsTeam >= (numTeams - 1)) {
                team = 0;
            } else {
                team = gsTeam + 1;
            }
        } else {
            team = !gsTeam;
        }
        // Set players team
        gs->PlayerTeams[i] = team;
        // Unready the player.
        gs->PlayerStates[i] = 0;
    }
}

/*
    using the first "removeBuddy" function worked, but
    always gave a network error for some reason.
*/
int addOrRemoveBuddy(int selectedIndex, int account_id)
{
    int i = selectedIndex;
    u32 msg[11];
    msg[0] = 0x001A0031;
    msg[1] = 0x00000000;
    msg[2] = 0x00000007;
    msg[3] = 0x00000000;
    msg[4] = 0x00000000;
    msg[5] = 0x00003500;
    msg[6] = 0x00000000;
    msg[7] = 0x00000000;
    msg[8] = 0x00000000;
    msg[9] = 0x00000000;
    msg[10] = account_id;
    #ifdef UYA_PAL
        u32 removeOrAdd = (info.buddies[i]) ? 0x0017ed28 : 0x0017eca8;
    #else
        u32 removeOrAdd = (info.buddies[i]) ? 0x0017ee18 : 0x0017ed98;
    #endif
    // flip return type.  (True usually equals 0 with medius functions)
    return 0 == ((int (*)(void *, u32, int))removeOrAdd)(msg, 0x00197858, 0);

}

int optionAddRemoveBuddy(int account_id, int selectedIndex)
{
    int i = selectedIndex;
    int ret = 0;
    // if isn't buddy, add to buddies
    if (info.buddies[i] == 0) {
        // if ignored, return 0.
        if (info.ignored[i] == 1) {
            uiShowOkDialog("Error","You must unignore this player before adding them to your buddies.");
            return ret;
        }
        // check if buddy list is full, if so, show ok dialog and return 0.
        if (info.buddyCount > MAX_BUDDIES) {
            uiShowOkDialog("", uiMsgString(0x184d));
            return ret;
        }
        // ret = addBuddy(BUDDY_LIST_STACK, account_id);
        ret = addOrRemoveBuddy(i, account_id);
        if (ret) {
            info.buddies[i] = 1;
            info.buddyCount += 1;
        } else if (!ret) {
            char buff[64];
            snprintf(buff, 64, "n: %d; c: %d; b: %d; i: %d;", i, info.client_ids[i], info.buddies[i], info.ignored[i]);
            uiShowOkDialog("Add Buddy Error", buff);
        }
        return ret;
    } else if (info.buddies[i] == 1) {
        // else Remove Buddy if is buddy
        // ret = removeBuddy(BUDDY_LIST_STACK, account_id);
        ret = addOrRemoveBuddy(i, account_id);
        if (ret) {
            info.buddies[i] = 0;
            info.buddyCount -= 1;
        } else if (!ret) {
            char buff[64];
            snprintf(buff, 64, "n: %d; ret: %d; c: %d; b: %d; i: %d;", i, ret, info.client_ids[i], info.buddies[i], info.ignored[i]);
            uiShowOkDialog("Remove Buddy Error", buff);
        }
        return ret;
    }
    // all else, return 0.
    return ret;
}

int optionIgnorePlayer(int account_id, int selectedIndex)
{
    int i = selectedIndex;
    int ret = 0;
    // if isn't ignored
    if (info.ignored[i] == 0) {
        // if ignored, return 0.
        if (info.buddies[i] == 1) {
            uiShowOkDialog("","You must remove buddy before you can ignore them.");
            return ret;
        }
        // check if ignore list is full, if so, show ok dialog and return 0.
        if (info.ignored[i] > MAX_IGNORED) {
            uiShowOkDialog("", uiMsgString(0x18d3));
            return ret;
        }
        ret = ignorePlayer(IGNORE_LIST_STACK, account_id);
        if (ret) {
            info.ignored[i] = 1;
            info.ignoredCount += 1;
        } else if (!ret) {
            char buff[64];
            snprintf(buff, 64, "n: %d; c: %d; b: %d; i: %d;", i, info.client_ids[i], info.buddies[i], info.ignored[i]);
            uiShowOkDialog("Ignore Player Error", buff);
        }
        return ret;
    } else if (info.ignored[i] == 1){
        // else Unignore
        ret = unignorePlayer(IGNORE_LIST_STACK, account_id);
        if (ret) {
            info.ignored[i] = 0;
            info.ignoredCount -= 1;
        } else if (ret == 0) {
            char buff[64];
            snprintf(buff, 64, "n: %d; ret: %d c: %d; b: %d; i: %d;", i, ret, info.client_ids[i], info.buddies[i], info.ignored[i]);
            uiShowOkDialog("Unignore Player Error", buff);
        }
        return ret;
    }
    // all else, return 0.
    return ret;
}

int loopBuddyList(int account_id, buddyListInfo_t * list, int listCount)
{
    int k;
    int r = 0;
    for (k = 0; k < listCount; ++k) {
        // if account id is found on list, it's a buddy!
        if (list[k].accountID == account_id){
            r = 1;
            break;
        }
    }
    return r;
}

int loopIgnoreList(int account_id, ignoreListInfo_t * list, int listCount)
{
    int k;
    int r = 0;
    for (k = 0; k < listCount; ++k) {
        // if account id is found on list, it's a buddy!
        if (list[k].accountID == account_id){
            r = 1;
            break;
        }
    }
    return r;
}

void updateInfo(GameSettings *gs, int selectedIndex)
{
    int i = selectedIndex;
    int account_id = gs->PlayerAccountIds[i];
    int client_id = gs->PlayerClients[i];
    int isHost = gameAmIHost();
    struct buddyListInfo_t * buddy = (struct buddyListInfo_t *)(*(u32*)BUDDY_LIST_START);
    struct ignoreListInfo_t * ignore = (struct ignoreListInfo_t*)(*(u32*)IGNORE_LIST_START);

    // Check if client is alraedy in info list.
    if (info.client_ids[i] != client_id) {
        // store client id
        info.client_ids[i] = client_id;
        info.buddies[i] = 0;
        info.ignored[i] = 0;

        // Check if uddy
        if (info.buddyCount > 0) {
            int isBuddy = loopBuddyList(account_id, buddy, info.buddyCount);
            info.buddies[i] = isBuddy;
            if (isBuddy)
                info.ignored[i] = 0;
        }
        // Check Ignored: if ignore list isn't zero, and player isn't a buddy
        if (info.ignoredCount > 0 && info.buddies[i] == 0) {
            int isIgnored = loopIgnoreList(account_id, ignore, info.ignoredCount);
            // check if ignored
            info.ignored[i] = isIgnored;
        }
    }

    // update player options
    int offset = 2;
    if (isHost) {
        offset = 0;
        playerOptions[PLAYER_OPTION_TEAMSKIN] = changeTeamStr;
        playerOptions[PLAYER_OPTION_KICK] = kickPlayerStr;
    }
    playerOptions[PLAYER_OPTION_ADD_BUDDY - offset] = info.buddies[i] ? removeBuddyStr : addBuddyStr;
    playerOptions[PLAYER_OPTION_IGNORE - offset] = info.ignored[i] ? unignorePlayeStr : ignorePlayerStr;
}

int openPlayerOptions(void * ui, GameSettings * gs, int itemSelected, int isTeams)
{
    int selectedItem = itemSelected - 0xf;
    int i = getPlayerIndex(ui, selectedItem);
    int account_id = gs->PlayerAccountIds[i];
    int client_id = gs->PlayerClients[i];
    int isBot = (account_id >= 883) && (account_id <= 1880);
    int isHost = gameAmIHost();
    // if selected player isn't first player (host)
    if (selectedItem > -1 && client_id != gameGetMyClientId()) {
        // if not botupdate info struct and player option names.
        if (!isBot)
            updateInfo(gs, i);
        
#ifdef DEBUG
        int a;
        printf("\n========");
        printf("\nbuddies: %d, ignored: %d", info.buddyCount, info.ignoredCount);
        for (a = 0; a < 8; ++a) {
            printf("\nc: %d, b: %d, i: %d", info.client_ids[a], info.buddies[a], info.ignored[a]);
        }
        printf("\n========");
#endif

        char * title = "Player Options";
        int size = sizeof(playerOptions)/sizeof(char*);
        int optionsSize = (isHost) ? size : size - 2;
        // if bot, change title and remove last two options.
        if (isBot) {
            title = "Bot Options";
            optionsSize -= 2;
        }
        int select = uiShowSelectDialog(title, playerOptions, optionsSize, 0);
        int selection = -1;
        if (select > PLAYER_OPTION_CANCEL)
            selection = (isHost) ? select : (select + 2);

        switch (selection) {
            case PLAYER_OPTION_TEAMSKIN: optionChangeTeamSkin(ui, gs, selectedItem, isBot, isTeams); break;
            case PLAYER_OPTION_KICK: {
                char kickingPlayer[32];
                char * kickEm = uiMsgString(0x15ff);
                snprintf(kickingPlayer, 32, kickEm, gs->PlayerNames[i]);
                int kickDialog = uiShowYesNoDialog("", kickingPlayer);
                if (kickDialog == 1) {
                    gs->PlayerStates[i] = 5;
                }
                break;
            }
            case PLAYER_OPTION_ADD_BUDDY: optionAddRemoveBuddy(account_id, i); break;
            case PLAYER_OPTION_IGNORE: optionIgnorePlayer(account_id, i); break;
        }
        return UI_PAD_NONE;
    }
    // return pressing X if nothing else.
    return UI_PAD_CROSS;
}

void openTeamsOptions(GameSettings * gs, int isTeams)
{
    int size = sizeof(randomTeamOptions)/sizeof(char*);
    int optionsSize = (gs->GameType == GAMETYPE_DM) ? size : (size - 1);
    int select = uiShowSelectDialog("Team Options", randomTeamOptions, size, 0);
    if (select > TEAM_OPTION_CANCEL)
        setTeams(select);
}
// extern forceMapOverride;
int patchStaging(UiMenu_t* ui, int pad)
{
    static int init_staging = 0;
    static int hjLogFrames = HOTJOIN_LOG_MAX_FRAMES;
    static int allPlayersReady = -1;
    static int pressedL1 = -1;
    static int holdingL1time = 0; 
    int i;
    int j;
    GameSettings* gs = gameGetSettings();
    int clientId = gameGetMyClientId();
    int isTeams = gameGetOptions()->GameFlags.MultiplayerGameFlags.Teams;
    int itemSelected = *(int*)((u32)ui + 0x290);
    int isLoading = *(u8*)((u32)ui + 0x2b6);
    int isRequstingTeamChange = *(u8*)((u32)ui + 0x2c8);

    // Hot-join instrumentation (temporary): fires on entry, before any early return,
    // so we can tell "staging never entered" apart from "logging not working".
    {
        static int hjEntry = 0;
        if ((hjEntry % 30) == 0) {
            printf("HJ enter e=%d host=%d gs=%p cid=%d lobbyConn=%p\n",
                hjEntry, gameAmIHost(), gs, clientId, netGetLobbyServerConnection());
            if (hjEntry < 900) {
                u8 ebuf[8];
                ebuf[0] = 0xE0;                        /* tag: patchStaging entered */
                ebuf[1] = (u8)(hjEntry / 30);
                ebuf[2] = (u8)(gameAmIHost() & 0xFF);
                ebuf[3] = (u8)(gs ? 1 : 0);
                ebuf[4] = (u8)(clientId & 0xFF);
                ebuf[5] = (u8)(netGetLobbyServerConnection() ? 1 : 0);
                ebuf[6] = 0;
                ebuf[7] = 0;
                netSendCustomAppMessage(netGetLobbyServerConnection(),
                    NET_LOBBY_CLIENT_INDEX, CUSTOM_MSG_ID_HOTJOIN_DEBUG, 8, ebuf);
            }
        }
        ++hjEntry;
    }

    // check for connetion
    if (!netGetLobbyServerConnection())
        return stagingFunc(ui, pad);

    // Change pad buttons for all players
    if (pad == UI_PAD_CROSS) {
        pad = openPlayerOptions(ui, gs, itemSelected, isTeams);
    }
    // Change pad buttons on for host
    if (gameAmIHost()) {
        if (pad == UI_PAD_CIRCLE && allPlayersReady == 1) {
            // Force "Start" to be selected
            ui->selectedIndex = 4;
            allPlayersReady = 2;
            pad = UI_PAD_CROSS;
        } else if (pad == UI_PAD_R1) {
            pad = UI_PAD_NONE;
        } else if (pad == UI_PAD_L2) {
            pad = UI_PAD_NONE;
        } else if (pad == UI_PAD_R2) {
            pad = UI_PAD_NONE;
        }
    }

	// call game function we're replacing
	int result = stagingFunc(ui, pad);

    // Dump the joining client's view of staging each frame, so we can see what it
    // observes in the handful of frames before it gives up and disconnects.
    if (gs && !gameAmIHost() && hjLogFrames < HOTJOIN_LOG_MAX_FRAMES) {
        int hj;
        int mySlot = -1;
        char hjName[17];

        for (hj = 0; hj < GAME_MAX_PLAYERS; ++hj) {
            if (gs->PlayerClients[hj] == clientId) { mySlot = hj; break; }
        }

        HOTJOIN_LOG("f=%d res=%d cid=%d slot=%d hostState=%d load=%d teamReq=%d mapResp=%d\n",
            hjLogFrames, result, clientId, mySlot, gs->PlayerStates[0],
            isLoading, isRequstingTeamChange, mapOverrideResponse);
        HOTJOIN_LOG("f=%d clients=%d %d %d %d %d %d %d %d\n", hjLogFrames,
            gs->PlayerClients[0], gs->PlayerClients[1], gs->PlayerClients[2], gs->PlayerClients[3],
            gs->PlayerClients[4], gs->PlayerClients[5], gs->PlayerClients[6], gs->PlayerClients[7]);
        HOTJOIN_LOG("f=%d states=%d %d %d %d %d %d %d %d\n", hjLogFrames,
            gs->PlayerStates[0], gs->PlayerStates[1], gs->PlayerStates[2], gs->PlayerStates[3],
            gs->PlayerStates[4], gs->PlayerStates[5], gs->PlayerStates[6], gs->PlayerStates[7]);
        if (mySlot >= 0) {
            for (hj = 0; hj < 16; ++hj) hjName[hj] = gs->PlayerNames[mySlot][hj];
            hjName[16] = 0;
            HOTJOIN_LOG("f=%d me slot=%d state=%d team=%d name='%s'\n",
                hjLogFrames, mySlot, gs->PlayerStates[mySlot], gs->PlayerTeams[mySlot], hjName);
        }
        {
            u8 dbuf[28];
            int k;
            dbuf[0] = 0xF1;                            /* tag: staging frame snapshot */
            dbuf[1] = (u8)(hjLogFrames & 0xFF);
            dbuf[2] = (u8)(mySlot & 0xFF);
            dbuf[3] = (u8)(gs->PlayerStates[0] & 0xFF);
            for (k = 0; k < GAME_MAX_PLAYERS; ++k) dbuf[4 + k]  = (u8)(gs->PlayerClients[k] & 0xFF);
            for (k = 0; k < GAME_MAX_PLAYERS; ++k) dbuf[12 + k] = (u8)(gs->PlayerStates[k] & 0xFF);
            dbuf[20] = (u8)(isLoading & 0xFF);
            dbuf[21] = (u8)(isRequstingTeamChange & 0xFF);
            dbuf[22] = (u8)(clientId & 0xFF);
            dbuf[23] = (u8)(mapOverrideResponse & 0xFF);
            dbuf[24] = (u8)(result & 0xFF);
            dbuf[25] = (u8)(mySlot >= 0 ? gs->PlayerTeams[mySlot] : 0xFF);
            dbuf[26] = 0;
            dbuf[27] = 0;
            netSendCustomAppMessage(netGetLobbyServerConnection(),
                NET_LOBBY_CLIENT_INDEX, CUSTOM_MSG_ID_HOTJOIN_DEBUG, 28, dbuf);
        }

        ++hjLogFrames;
    }

    //  init staging if not done already, or equals 2
    if (!init_staging || info.currentWorldId != gameGetWorldId()) {
        getBuddyList(BUDDY_LIST_STACK, 2);
        getIgnoreList(IGNORE_LIST_STACK, 0);
        info.currentWorldId = gameGetWorldId();
        info.buddyCount = BUDDY_LIST_COUNT;
        info.ignoredCount = IGNORE_LIST_COUNT;
        memset(info.client_ids, -1, sizeof(info.client_ids));
        memset(info.buddies, -1, sizeof(info.buddies));
        memset(info.ignored, -1, sizeof(info.ignored));
        init_staging = 1;
        hjLogFrames = 0;
    }

    // if host
    if (gameAmIHost()) {
        // Opem Teams Options Menu
        // if teams and config menu is closed and host hasn't started game
        if (isTeams && !isConfigMenuActive && gs->PlayerStates[0] != 7) {
            // if L1 isn't pressed and no other menu is open
            if (!padGetButton(0, PAD_L1)) {
                // reset pressed l1 if nothing is pressed.
                pressedL1 = -1;
                holdingL1time = gameGetTime() + .75 * TIME_SECOND;
            } else if (padGetButton(0, PAD_L1) && pressedL1 < 1 && (*(u32*)0x01c5c114 == 0)) {
                pressedL1 = 0;
            }
            if (pressedL1 == 0) {
                pressedL1 = 1;
                setTeams(TEAM_OPTION_RANDOM);
            } else if (pressedL1 == 1 && holdingL1time <= gameGetTime() && *(u32*)0x01c5c114 == 0) {
                pressedL1 = 2;
                openTeamsOptions(gs, isTeams);
            }
        }

        // Set host to always ready
        if (gs->PlayerStates[0] != 7)
            gs->PlayerStates[0] = 6;    
        
        // Replace "\x11 UNREADY" with "\x11 STSART"
        int str = uiMsgString(0x16d9);
        if (allPlayersReady)
	        strncpy((char*)str, "\x11 START", 9);
        else
	        strncpy((char*)str, "         ", 9);
        
        // check if all players are ready
        for (i = 0; i < GAME_MAX_PLAYERS; ++i) {
            // if not all players are ready
            if (gs->PlayerClients[i] > -1 && gs->PlayerStates[i] < 6) {
                allPlayersReady = 0;
            } else if (gs->PlayerClients[i] > -1 && gs->PlayerStates[i] == 6) {
                allPlayersReady = 1;
            } else if (allPlayersReady == 2) {
                allPlayersReady = -1;
            }
        }
    } else {
        // Non-Host Stuff
        // Make it so all clients can scroll over users names
        if (*(u32*)OPTIONS_SCROLL_CHECK == 0x24050001)
            *(u32*)OPTIONS_SCROLL_CHECK = 0x24050003;

        // Auto-join when entering staging while host is already in-game.
        // Observed on the wire: an in-game host reports PlayerStates[0] == 8,
        // which is one past GS_PLAYER_STATE_GAME_START (7) and undocumented in
        // eGS_PlayerStates. Accept both so this fires for loading and playing.
        if (gs->PlayerStates[0] >= GS_PLAYER_STATE_GAME_START) {
            for (i = 0; i < GAME_MAX_PLAYERS; ++i) {
                if (gs->PlayerClients[i] == clientId) {
                    // Auto-balance team if unassigned
                    if (isTeams && gs->PlayerTeams[i] < 0) {
                        int blueCount = 0, redCount = 0;
                        int p;
                        for (p = 0; p < GAME_MAX_PLAYERS; ++p) {
                            if (p != i && gs->PlayerClients[p] > -1) {
                                if (gs->PlayerTeams[p] == 0) blueCount++;
                                else if (gs->PlayerTeams[p] == 1) redCount++;
                            }
                        }
                        gs->PlayerTeams[i] = (redCount < blueCount) ? 1 : 0;
                    }
                    // Auto-ready to begin streaming and load active map
                    gs->PlayerStates[i] = 6;
                    break;
                }
            }
        }

        // Unkick (never worked)
        // for (i = 0; i < GAME_MAX_PLAYERS; ++i) {
        //     // if server client id matches local client id.
        //     if (gs->PlayerClients[i] == clientId) {
        //         // Patch Unkick: if leave game pop is up, close it.
        //         u32 popup = uiGetActiveMenu(11, 1);
        //         if (gs->PlayerStates[i] == 5 && popup > 0) {
        //             // Compare popup text and "Leave Game" string.
        //             if (strcmp(*(u32*)(popup + 0x110) + 0x64, uiMsgString(0x1643))) {
        //                 *(u32*)0x01C5C284 = 0x2c;
        //             }
        //         }
        //     }
        // }
    }
	return result;
}

int patchCreateGame(UiMenu_t* ui, long pad)
{
    int time_limit = 120; // in minutes
 
    // check for connetion
    if (!netGetLobbyServerConnection())
        return createGameFunc(ui, pad);

    int result = createGameFunc(ui, pad);

    UiCreateGameElements_t * createGame = &ui->pChildren;
    if (createGame->time->rangeMax != time_limit) {
        // Change Time Limit
        createGame->time->rangeMax = time_limit;
        // Change time limit if frag limit is 0.
        *(u32*)((u32)CREATE_GAME_BASE_FUNC + 0x3f8) = 0x24040000 | time_limit;
    }
    // Let password field always be active.
    if (createGame->usePassword->state == 2) {
        createGame->usePassword->state = 3;
        createGame->password->state = 3;
    }
    // Lock local players to 1
    if (createGame->localPlayers->state == 3) {
        createGame->localPlayers->state = 2;
        createGame->localPlayers->rangeMax = 1;
    }

    return result;
}

int patchAdvancedOptions(UiMenu_t* ui, int pad)
{
    static int savedTeams = 0;
    int frag_limit = 50;
    int ctfCaps_limit = 50;

    // check for connetion
    if (!netGetLobbyServerConnection())
        return advancedOptionsFunc(ui, pad);

    int result = advancedOptionsFunc(ui, pad);
    UiAdvancedOptionsElements_t* ao = &ui->pChildren;
    UiMenu_t* menu = uiGetMenu(UI_MENU_CREATE_GAME);
    UiCreateGameElements_t* createGame = &menu->pChildren;
    int isDeathmatch = createGame->mode->selectedIndex == 2;
    if (isDeathmatch) {
        // set savedteams to last team value.
        savedTeams = ao->teams->selectedIndex;
        if (ao->fragLimit->rangeMax != frag_limit)
            ao->fragLimit->rangeMax = frag_limit;
    } else if (createGame->mode->selectedIndex == 1) {
        if (ao->ctfCaps->rangeMax != ctfCaps_limit)
            ao->ctfCaps->rangeMax = ctfCaps_limit;
    }
    if (isDeathmatch && ao->teams->selectedIndex != savedTeams)
        ao->teams->selectedIndex = savedTeams;
    
    return result;
}

// int patchBuddies(void * ui, long pad)
// {
//     static int pressedSquare = -1;
//     static int holdingSquareTime = 0;
//     u32 * uiElements = (u32*)((u32)ui + 0x110);
//     int itemSelected = *(int*)(ui + 0x290);
//     int isLoading = *(u8*)(ui + 0x2b6);

//     // check for connetion
//     if (!netGetLobbyServerConnection())
//         return buddiesFunc(ui, pad);

//     int result = buddiesFunc(ui, pad);

//     return result;
// }

// int patchPlayerDetails(void * ui, long pad)
// {
//     u32 * uiElements = (u32*)((u32)ui + 0x110);
//     int itemSelected = *(int*)(ui + 0x290);
//     int account_id = *(u32*)(ui + 0x2a8);

//     // check for connetion
//     if (!netGetLobbyServerConnection())
//         return playerDetailsFunc(ui, pad);

//     int result = playerDetailsFunc(ui, pad);

//     return result;
// }

// int patchStats(void * ui, int pad)
// {
//     u32 * uiElements = (u32*)((u32)ui + 0x110);
//     int itemSelected = *(int*)(ui + 0x290);

//     // check for connetion
//     if (!netGetLobbyServerConnection())
//         return statsFunc(ui, pad);

//     int result = statsFunc(ui, pad);

//     return result;
// }

int patchKeyboard(UiMenu_t * ui, int pad)
{
    int i;
    int selectedIndex = ui->selectedIndex;
    // UiElement_t * keyboardEnd = (UiElement_t*)((u32)ui + 0x294);
    // int keyboardSize = *(u32*)(u32)ui + 0x298;
    // UiElement_t * keyboardStart = (UiElement_t*)((u32)ui + 0x2a4);
    int currentPage = ((u32)ui + 0x2b0);
    int pages = ((u32)ui + 0x2b4);
    static int setPages = 0;

    int result = keyboardFunc(ui, pad);

    // if on clan details or cities menu, then update keyboard.
    if (uiGetActiveMenu(UI_MENU_CLAN_DETAILS, 0) > 0 || uiGetActiveMenu(UI_MENU_CITY, 0) > 0) {
        // get children
        // Update number of pages.  We have to account for different number of pages per language.
        if (setPages !=  *(int*)pages) {
            *(int*)pages += 1;
            setPages =  *(int*)pages;
        }
        // Change SHIFT to COLOR if on page 2
        if (*(int*)currentPage ==  *(int*)pages - 2) {
            strncpy(ui->pChildren[KEY_SHIFT]->title, "\x14MISC", 6);
        } else {
            strncpy(ui->pChildren[KEY_SHIFT]->title, "\x14SHIFT", 6); 
        }
        // Update keyboard
        if (*(int*)currentPage ==  *(int*)pages - 1) {
            for (i = 0; i < COUNT_OF(keys); ++i) {
                // don't let the use of buttons in clan tags
                if (uiGetActiveMenu(UI_MENU_CLAN_DETAILS, 0) > 0 && keys[i].index < KEY_1)
                    break;

                strncpy(ui->pChildren[keys[i].index]->title, keys[i].text, 3);
            }
        }
    }

    return result;  
}
