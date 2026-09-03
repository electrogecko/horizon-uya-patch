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
// Armed by patchStaging (we are ENTERING a game), cleared once we are in one.
// This is what lets the pad-table seed run during the menus=0/game=0 load window
// without also running during the identical-looking window on the way OUT of a
// game. Declared outside the NTSC block because patchStaging is common code.
int hjSeedArmed = 0;

#ifndef UYA_PAL
#define HJ_PLAYERBIT_VTABLE_SLOT    (0x001dd970)
#define HJ_PLAYERBIT_TABLE_BASE     (0x0022f550)
#define HJ_PLAYERBIT_TABLE_STRIDE   (3184)
#define HJ_PLAYERBIT_TABLE_MAXIDX   (64)

extern int internal_hjResolvePlayerCtx(void ** out, void * arg);
extern void internal_hjPeerConnectCtor(void * a0, void * a1);
extern void * internal_hjPeerLookup(void * peers, int idx);
extern int internal_hjIntroducePeer(void * ctx, int peerIdx, int a2, int a3);

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

// ---------------------------------------------------------------------------
// Hotjoin: the joiner's Player has no PAD, which is the single root cause of
// every in-game TLB fault we have seen (Metropolis addresses shown; the same
// faults appear at different VAs on other maps because this is per-map code):
//
//   0x4ffb38  lw $2,9524($16)   ; player->pPad          (0x2534 = PAD *pPad)
//   0x4ffb4c  lw $2,452($2)     ; pPad->0x1c4   <-- TLB, pPad == NULL
//   0x525008  lw $3,416($4)     ; pPad->0x1a0   <-- TLB
//   0x487c48  lw $2,1384($4)    ; pad->0x568    <-- TLB, pad passed as a0
//
// It originates in player construction:
//   0x525c80  lw $4,0($5)       ; $5 = padTable + playerIndex*4
//   0x525c84  sw $4,9524($18)   ; player->pPad = padTable[playerIndex]
//   0x525c98  jal 0x487c48      ; immediately used -> faults when NULL
// so the table entry for the joiner's slot is empty; the pads are set up during
// the normal game-start sequence, which a hot-joiner skips.
//
// The engine itself treats a NULL pad as recoverable: the sibling routine at
// 0x487c70 does `bnez $4 ...` and substitutes the global at 0x225900. We do the
// same thing one level earlier -- fill in a missing pPad rather than let every
// consumer fault -- and log what we found, because we still do not know WHICH
// players are missing pads (local vs remote) and that determines the real fix.
// ---------------------------------------------------------------------------
#define HJ_PAD_TABLE        (0x002412F0)   // candidate only -- see note below
#define HJ_PAD_P1           (0x00225900)   // REAL local pad, confirmed at runtime
// The `P1_PAD = 0x225980` label in known_labels_ntsc.tsv is 0x80 past the actual pad.
// Host runtime proves it: its padtable[0] AND its local player's pPad both read
// 0x00225900, and the engine's own NULL-substitute at 0x487c70 uses 0x225900 too.
// Filling the joiner's pPad with 0x225980 pointed every field access 0x80 into the
// struct -- scrambled input, which is the likeliest cause of the "jumbled, hard to
// move" behaviour (a NULL pad instead gives no input at all, which is what session 7
// showed).
#define HJ_PAD_STRIDE       (0x1700)
#define HJ_PAD_SLOTS        (8)
#define HJ_PLAYER_PPAD_OFF  (0x2534)
// PadStream lives at Player + 0x430C; the producer the pad poll calls into.
#define HJ_PS_STREAM            (0x430C)
#define HJ_PADSTREAM_PRODUCER   (0x00534568)
// PadStream fields, relative to the Player (0x430C + the struct's own offsets).
#define HJ_PS_CURFRAME  (HJ_PS_STREAM + 0x1D8)   /* 0x44E4, +1 per producer call */
#define HJ_PS_READY     (HJ_PS_STREAM + 0x1DC)   /* 0x44E8, bit count, else -1   */
#define HJ_PS_SEQ       (HJ_PS_STREAM + 0x1E1)   /* 0x44ED, +1 per packet sent   */
#define HJ_PLAYER_MPIDX_OFF (0x2544)

// 0x2412F0 IS the pad pointer table, and it is what the constructor reads:
//   525c48  lui   $2,0x24
//   525c4c  addiu $2,$2,4848      ; 0x002412F0
//   525c50  lw    $6,112($29)     ; local player index * 4
//   525c60  addu  $5,$6,$2
//   525c80  lw    $4,0($5)        ; pPad = table[idx]
//   525c84  sw    $4,9524($18)    ; player->pPad
// An earlier note here claimed a runtime dump had "proved it wrong" because slots
// 4..7 held floats (1.0f, 1/60). Those slots are simply not part of the table --
// only 0..3 are pointers, one per local pad. The dump was reading past the end.
#define HJ_PAD_PTRS         (4)
static int hjPadTableLogged = 0;
static int hjPadTableSeeded = 0;
static int hjPadFillLogged = 0;
static int hjPlayerMapLogged = 0;

static int hjLooksLikePad(u32 v)
{
    // Was anchored on 0x225980 and therefore rejected the real pad 0x225900, which is
    // why even the HOST -- which has a perfectly good padtable[0] -- reported valid=0.
    // The table was never the problem; the validator was.
    if (v < HJ_PAD_P1) return 0;
    if (v >= HJ_PAD_P1 + (4 * HJ_PAD_STRIDE)) return 0;
    return ((v - HJ_PAD_P1) % HJ_PAD_STRIDE) == 0;
}

void hjFixMissingPads(void)
{
    u32 * table = (u32*)HJ_PAD_TABLE;
    int i, valid = 0, spare = 1;

    // Must be BOTH out of menus and in a live game. Leaving a game passes
    // through menus=0/game=0 for several seconds, and everything below writes
    // into structures the engine is tearing down in exactly that window.
    // Guarding only on isInMenus() let this run during teardown and crashed
    // both consoles on exit -- see the padhook note below.
    if (isInMenus())
        return;

    // menus=0/game=0 covers BOTH the load into a game and the teardown out of
    // one. Only the first is safe, and only the first is useful: the local
    // player constructor runs inside it. hjSeedArmed tells them apart.
    if (!isInGame() && !hjSeedArmed)
        return;

    for (i = 0; i < HJ_PAD_PTRS; ++i)
        if (hjLooksLikePad(table[i]))
            ++valid;

    // THE actual fix, as opposed to the two repairs below it.
    //
    // On a hot-join the table is still all-zero when playerCreateLocalForSlot
    // runs, so it reads pPad = NULL and its two follow-up stores
    //   *(pPad + 0x56C) = producer ;  *(pPad + 0x570) = player + 0x430C
    // fault into low memory and are lost. Seeding the entry BEFORE the
    // constructor runs lets the constructor do its own job: it installs the
    // producer itself, which means we no longer hardcode 0x00534568 -- an
    // address that is per-level overlay and would be wrong on other maps.
    //
    // Only slot 0: a client has exactly one local player, and a healthy load
    // shows table[0] = 0x00225900 with 1..3 zero. Guarded on the entry being
    // zero, so this is a no-op on a normal load and cannot fight the engine.
    if (!table[0]) {
        table[0] = HJ_PAD_P1;
        if (!hjPadTableSeeded) {
            hjPadTableSeeded = 1;
            HOTJOIN_LOG("padseed: table[0] was NULL -> %08x (before ctor)\n", table[0]);
        }
    }

    if (hjPadTableLogged < 3) {
        ++hjPadTableLogged;
        HOTJOIN_LOG("padtable @%08x: %08x %08x %08x %08x %08x %08x %08x %08x (valid=%d)\n",
            (u32)table, table[0], table[1], table[2], table[3],
            table[4], table[5], table[6], table[7], valid);
    }

    // Repair ONLY the local player (slot 0), and only when its pad is NULL.
    //
    // A previous version filled every NULL pPad, cycling P1..P4 with `spare & 3`. That
    // handed P1 to slot 0 AND slot 6, and P2 to slot 1 AND slot 7. Those pad structs are
    // written every frame (the 0x568/0x56c/0x570 stores), so two players were clobbering
    // one input buffer -- which is what produced movement that was "jumbled and hard,
    // button-mashing does some stuff". It also handed a pad to slot 4, which the runtime
    // dump shows is uninitialised (mpIndex=-842150451, pPad=0xcdcdcdcd, i.e. 0xcd fill).
    //
    // Observed layout: players are 0x4500 apart from 0x2f77c0; slot 0 is this console's
    // local player and carries mpIndex=1 (the hot-joiner is player index 1); slot 5
    // already holds a valid pad (0x311820) that we must not touch.
    //
    // Remote players keep a NULL pPad for now. That re-admits their per-frame TLB misses,
    // which are noisy but non-fatal -- and correct input for the local player is worth
    // more than a quiet log until we know where per-player pads are really allocated.
    if (!isInGame())
        return;
    hjSeedArmed = 0;

    {
        Player * p = playerGetFromSlot(0);
        if (p) {
            u32 * ppad = (u32*)((u32)p + HJ_PLAYER_PPAD_OFF);
            int mpIndex = *(int*)((u32)p + HJ_PLAYER_MPIDX_OFF);

            if (hjPlayerMapLogged < 8) {
                // Dump the POINTER table, not the storage array.
                //
                // playerGetAll() returns Player** -- the list the game itself iterates
                // (see playerPadUpdate). playerGetFromSlot(i) returns the i'th STORAGE
                // slot, which is a valid address whether or not anyone occupies it; that
                // is why it always handed back 0x2f77c0 + i*0x4500 and why slot 4 is
                // uninitialised 0xcdcdcdcd. Reading storage told us the host had one
                // player while it was visibly rendering a second one in a vehicle -- a
                // remote player's Player struct need not live in that static array at all.
                // Print both: the pointer table entry, and whether it aims inside the
                // static array or somewhere else entirely.
                Player ** all = playerGetAll();
                int j;
                for (j = 0; j < GAME_MAX_PLAYERS; ++j) {
                    Player * q = all ? all[j] : 0;
                    u32 qa = (u32)q;
                    int inArr = (qa >= 0x2f77c0 && qa < 0x2f77c0 + (8 * 0x4500)
                                 && ((qa - 0x2f77c0) % 0x4500) == 0);
                    if (!q) {
                        HOTJOIN_LOG("plist: [%d] NULL\n", j);
                        continue;
                    }
                    // pNetPlayer (Player+0x2558, per player.h:1231) is the argument the remote-player
                    // constructor takes. Chain found in the Metropolis overlay decomp:
                    //   vaInitNetworkedGameplaySystems -> func_0x001999a8(
                    //       playerCreateRemoteForSession)   ; stores cb at 0x002407D0
                    //   0x001999b8(NWPlayer *p): v0 = *(0x002407D0); jalr v0;
                    //                            p->0x1a6 = 1 (bCallbackCalled)
                    // playerCreateRemoteForSession is what allocates the vanilla host's
                    // heap Player (0x00311e80). If the hot-join host's net layer already
                    // holds an NWPlayer for the joiner, calling 0x1999b8 on it should let
                    // the level's own constructor build the player.
                    HOTJOIN_LOG("plist: [%d] %08x %s mpIndex=%d pMoby=%08x pPad=%08x team=%d veh=%08x pNet=%08x\n",
                        j, qa, inArr ? "static" : "HEAP",
                        *(int*)(qa + HJ_PLAYER_MPIDX_OFF),
                        *(u32*)(qa + 0x2524), *(u32*)(qa + HJ_PLAYER_PPAD_OFF),
                        *(int*)(qa + 0x2548), *(u32*)(qa + 0x2528),
                        *(u32*)(qa + 0x2558));
                }
                hjPlayerMapLogged = 8;
            }

            if (!*ppad) {
                *ppad = HJ_PAD_P1;
                if (hjPadFillLogged < 4) {
                    ++hjPadFillLogged;
                    HOTJOIN_LOG("padfill: FALLBACK FIRED - LOCAL slot=0 mpIndex=%d pPad NULL -> %08x\n",
                        mpIndex, *ppad);
                }
            }

            // The padhook that used to live here is DELETED, not disabled.
            //
            // It wrote 0x00534568 -- Metropolis's producer -- into the pad
            // struct. On Bakisi that address is different code, and the joiner
            // executed it: "TLB Miss, pc=0x534568 addr=0x5053456b", then
            // pc=0x0, then "Syscall: undefined (0)". A fallback that hardcodes
            // a per-overlay address cannot be made safe; the seed above is the
            // only correct fix, because it lets the constructor install its own
            // overlay's producer.
            //
            // padfill above stays: 0x00225900 is static and safe to point at.
            // If it fires, the seed landed too late -- that is a diagnostic,
            // and the joiner will move badly rather than crash.
        }
    }
}


// ---------------------------------------------------------------------------
// Hotjoin probe: locate the DELETE invoker.
//
// vaInitNetworkedGameplaySystems registers a matched pair:
//     func_0x001999a8(playerCreateRemoteForSession)
//     func_0x001999b0(playerDeleteRemoteForSession)
// and 0x001999b8 is the invoker for the CREATE side: it loads the callback
// from 0x002407D0, jalrs it, and sets nwp->0x1a6 = 1. We already use it
// (internal_hjSpawnRemotePlayer) to admit a hot-joiner.
//
// The DELETE side must have the same shape, but we have no base-exe image on
// disk to read it from, and playerDeleteRemoteForSession itself is an OVERLAY
// address (0x0052aba0 on Metropolis) -- calling that directly is the exact
// mistake that crashed the joiner on Bakisi. So dump the dispatch family and
// the callback slots and decode them offline.
// ---------------------------------------------------------------------------
void hjDumpDispatch(void)
{
    static int done = 0;
    u32 * p;
    int i;

    // The callback slots are only populated by vaInitNetworkedGameplaySystems,
    // which runs at level load -- dumping at boot would read zeros and waste
    // the run. Wait until we are actually in a game.
    if (done || !isInGame() || isInMenus()) return;
    done = 1;

    // The registration/invoke family around 0x001999a8.
    p = (u32*)0x001999a0;
    for (i = 0; i < 32; i += 4) {
        HOTJOIN_LOG("disp %08x: %08x %08x %08x %08x\n",
            (u32)(p + i), p[i], p[i+1], p[i+2], p[i+3]);
    }

    // The callback slots. 0x002407D0 is the create callback; the delete one
    // should sit next to it, and on an in-game host both must be non-zero.
    p = (u32*)0x002407C8;
    for (i = 0; i < 8; i += 4) {
        HOTJOIN_LOG("cbslot %08x: %08x %08x %08x %08x\n",
            (u32)(p + i), p[i], p[i+1], p[i+2], p[i+3]);
    }

    // Find the DELETE invoker. The create invoker reads its callback as
    //   3c020024  lui v0,0x24
    //   8c4207d0  lw  v0,0x07d0(v0)
    // so the delete twin must contain an lw with offset 0x07D4, or the
    // gp-relative form lw rX,-0x796c(gp) = offset 0x8694 (the registration
    // stores use exactly those two encodings). Scan base-exe code for lw
    // (opcode 0x23) with either offset and print the surrounding words, so
    // the invoker is identified from evidence rather than guessed -- calling
    // a wrong address here would be a jump into arbitrary code.
    {
        u32 * scan = (u32*)0x00100000;
        u32 * end  = (u32*)0x00200000;
        int hits = 0;
        while (scan < end && hits < 20) {
            u32 w = *scan;
            if ((w >> 26) == 0x23) {
                u32 off = w & 0xFFFF;
                if (off == 0x07D4 || off == 0x8694) {
                    HOTJOIN_LOG("cbref %08x: %08x %08x %08x %08x %08x\n",
                        (u32)(scan - 1), scan[-1], scan[0], scan[1], scan[2], scan[3]);
                    ++hits;
                }
            }
            ++scan;
        }
        HOTJOIN_LOG("cbref: %d hit(s)\n", hits);
    }

    // The single cbref hit puts the delete callback's load at 0x00199a44.
    // In the create invoker the lui sits at entry+4 (entry 0x001999b8, lui
    // 0x001999bc), so the delete entry should be 0x00199a40 -- but "should
    // be" is not good enough for a jalr target. Dump the whole function so
    // the prologue is confirmed and, just as important, so we can see what
    // it does with bCallbackCalled (nwp+0x1a6). Create SETS that flag; if
    // delete does not CLEAR it, hjHostSpawnRemotes would instantly rebuild
    // the player we just tore down.
    p = (u32*)0x00199a30;
    for (i = 0; i < 32; i += 4) {
        HOTJOIN_LOG("delfn %08x: %08x %08x %08x %08x\n",
            (u32)(p + i), p[i], p[i+1], p[i+2], p[i+3]);
    }
}

// ---------------------------------------------------------------------------
// Hotjoin: why does the host<->joiner peer link never complete?
//
// Both ends retransmit forever -- host logs `peerconnreq idx=1`, joiner logs
// `peerconnreq idx=0`, every ~3 s, indefinitely. A peer is marked CONNECTED by
//   172970:  sw $2,8($3)      ; peer->0x08 = 5
// inside 0x172898, which its caller at 0x172668 only reaches when the peer index
// equals ctx->0x408. Rather than keep deducing the state machine statically (that
// approach has produced two wrong answers today), just print the peer table.
//
// peer = 0x14f8e8(ctx->0xE8, idx); fields seen in use:
//   0x08 = state (2 = connecting, 3 = ?, 5 = CONNECTED)
//   0x18 = sequence assigned by 0x173fc0
//   0x1C = "eligible to receive a connect request" (checked by the retransmit loop)
// ---------------------------------------------------------------------------
static int hjPeerDumps = 0;
static u32 hjLastPeerSig = 0;

// ---------------------------------------------------------------------------
// hjAnnounce -- finish the announce step the joiner's connect path skipped.
//
// 0x16f7d8 (connect) contains:
//   16fa68  bnez v0,0x16fac0   ; if (s6 | peers->0x438) != 0 -> SKIP
//   16fa70  li v0,5
//   16fa78  sw v0,8(s0)        ; myRecord->0x08 = 5
//   16fa80  sw s2,24(s0)       ; myRecord->0x18 = 1
// Runtime shows peers->0x438 == 1 for the whole of connect, clearing only once the
// HOST's type-5 arrives -- after connect has passed the check. Nothing re-runs that
// block, so myRecord->0x08 stays 4 forever, and since the sender at 0x14bdb0 takes the
// outbound type straight out of myRecord->0x08 the joiner can never emit type 5.
//
// Perform the skipped assignment once, when the preconditions the original block would
// have seen are true: our record is at 4 (introduce done) and 0x438 has cleared. Then
// drive the send ourselves -- setting the field is not sufficient, because the 3 and 4
// the host receives are emitted during the connect handshake and nothing sends again
// afterwards. Deliberately NOT calling 0x171d18 as well: that overwrites peers->0x408,
// which on the joiner legitimately points at the host.
//
// This MUST live outside hjDumpPeers. It used to sit after that function's
// `sig == hjLastPeerSig || hjPeerDumps > 60` early-out, which is a log throttle: the
// announce and every resend therefore only ran on frames where some peer's 0x08 happened
// to change, and stopped entirely after 60 such frames. Whether the announce fired at
// all, and how many of the 8 datagrams were actually sent, was decided by unrelated peer
// churn -- which is exactly the "sometimes lands, sometimes hangs" behaviour observed.
// ---------------------------------------------------------------------------
static int hjAnnounceDone = 0;
static int hjAnnounceSends = 0;
static int hjAnnounceTick = 0;

// Cadence, not a burst. The first version sent 12 datagrams over 2.4 s, which the log
// showed were ALL spent while the joiner was still loading the map -- the player did not
// spawn until 54 s later, so by the time the joiner existed in the game the announce had
// been over for nearly a minute and the host had nothing live to match. Announce at 1 Hz
// for as long as the join is in progress instead, so the window spans the load and, more
// importantly, continues after spawn.
#define HJ_ANNOUNCE_MAX_SENDS   (240)  // ~4 min at 1 Hz; a cap, not an expected count
#define HJ_ANNOUNCE_PERIOD      (60)   // frames between resends (~1 s at 60 Hz)

void hjAnnounce(void)
{
    u32 ctx = *(u32*)HJ_NET_CTX_PTR;
    u32 peers, mine;

    if (isInMenus()) {
        // Rearm for the next join attempt, so a retry is a clean run rather than
        // inheriting a spent send budget from the attempt that failed.
        hjAnnounceDone = 0;
        hjAnnounceSends = 0;
        hjAnnounceTick = 0;
        return;
    }

    if (!ctx)
        return;
    peers = *(u32*)(ctx + HJ_CTX_PEERS);
    if (!peers)
        return;
    mine = *(u32*)(peers + 0x400);
    if (!mine)
        return;

    if (*(u32*)(peers + 0x438) == 0 && *(int*)(mine + 0x08) == 4) {
        *(int*)(mine + 0x08) = 5;
        *(int*)(mine + 0x18) = 1;
        hjAnnounceSends = 0;
        hjAnnounceTick = 0;
        if (!hjAnnounceDone) {
            hjAnnounceDone = 1;
            HOTJOIN_LOG("announce: myRecord %08x 0x08 -> 5, 0x18 -> 1 (p438=0), sending\n",
                mine);
        }
    }

    // Retransmit: these are UDP datagrams and this protocol demonstrably depends on
    // repetition (the game's own peer-connect request retries every ~3 s). Space them
    // out rather than firing the whole budget in consecutive frames.
    if (*(int*)(mine + 0x08) == 5 && hjAnnounceSends < HJ_ANNOUNCE_MAX_SENDS) {
        if (--hjAnnounceTick <= 0) {
            hjAnnounceTick = HJ_ANNOUNCE_PERIOD;
            ++hjAnnounceSends;
            internal_hjSendPeerMsg((void*)peers, -1);
            // 1 Hz for minutes would flood the console; log the early ones (the load
            // phase) then sample, so the tail is still visible without drowning the rest.
            if (hjAnnounceSends <= 5 || (hjAnnounceSends % 10) == 0)
                HOTJOIN_LOG("announce: send %d/%d game=%d p408=%d\n",
                    hjAnnounceSends, HJ_ANNOUNCE_MAX_SENDS,
                    isInGame(), *(int*)(peers + 0x408));
        }
    }
}


// ---------------------------------------------------------------------------
// hjDumpRoster -- the GameSettings player roster, on BOTH machines, every frame,
// in menus AND in-game.
//
// Why this is the thing to watch now. A vanilla two-player join (both clients through
// staging) was captured on the same build as a reference, and it killed every lead the
// peer layer had produced: `playerbit ... id=-1`, the joiner's `p408=0`, and the
// `peerconnreq` retry firing every 3 s forever all occur in a join that WORKS. Even the
// announce fix fires in vanilla -- a record sitting at 4 with p438==0 is the game's
// ordinary state at that moment, not a hot-join defect.
//
// The one thing vanilla has that hot-join does not is the staging roster negotiation:
//   f=19  clients=0 1 -1 -1 -1 -1 -1 -1   states=6 6 0 0 0 0 0 0
//   f=86  hostState=7                     states=7 6 ...
// gs->PlayerClients[] is how the host learns a joiner exists AS A PLAYER, and it is
// negotiated on the staging screen. Hot-join skips staging entirely, so the host's PEER
// table gets the joiner (p408=1, type-5 both ways) while its PLAYER roster never does --
// a connected peer with no player entity, which is exactly what is on screen.
//
// The existing f= dump only runs inside the staging UI hook, which a hot-joiner never
// enters; that is why hot-join logs contain no f= lines at all. This one is deliberately
// independent of that hook so we can see the roster on the host while it is in-game.
//
// Logged on change, plus a heartbeat, and the budget refills via hjLogEpochTock -- a
// one-shot cap goes quiet exactly during the long session we care about, which has now
// cost two rounds of measurement (the 40-message type-22 cap, and the peer-dump cap).
// ---------------------------------------------------------------------------
static int hjRosterDumps = 0;
static u32 hjLastRosterSig = 0;
static int hjRosterBeat = 0;


// ---------------------------------------------------------------------------
// hjHostAdoptPeers -- write the roster entry the host's staging loop would have
// written, but never does while it is in-game.
//
// Established chain, both sides logged plus the server's own probe output:
//   1. The joiner broadcasts its staging announce (00-0F, carrying its name). The DME
//      world forwards broadcasts to every client, so THE HOST RECEIVES IT -- the server
//      log shows the name being read out of that very message
//      ("injected roster slot 1 (\"Gtr4\")", 241x).
//   2. In staging, the host's staging loop consumes that announce, writes the roster
//      slot, and answers the joiner's 02-13 poll with 02-12.
//   3. In-game, that loop is not running. The host never writes the slot, and never
//      sends 02-12 (the server already fakes the 02-12 on its behalf).
//   4. Every server-side fix so far points AT THE JOINER: TryInjectHotjoinSlot rewrites
//      the host->joiner settings snapshot in flight (World.cs:416, gated
//      source.DmeId == 0 && targetDmeId > 0). Nothing writes the HOST's own copy, and
//      the host is the producer of those snapshots, not a consumer -- so no amount of
//      server-side work can inform it. It has to do it itself.
//
// Result, captured on both machines at the same moment:
//   HOST:   clients=0 -1 -1 ...  states=8 0 0 ...   n=1
//   JOINER: clients=0  1 -1 ...  states=8 6 0 ...   n=1
// A connected peer (p408=1, type-5 both ways) with no player entity on the host.
//
// Slot == client id == DmeId == peer index: the server injects at slot = targetDmeId,
// and the joiner (cid=1) landed in slot 1, so the host can derive the mapping from the
// peer index alone without parsing the announce.
//
// NOTE: this tests whether the roster is the ONLY thing gating visibility. It may not
// be -- in staging the host runs a real add-player path with downstream effects (spawn,
// pad binding, HUD), and poking fields does not run any of that. "Roster now correct,
// still no player" is a real possible outcome, and would point at the in-game
// waiting-for-players / readiness gate as the place the actual admit-player work lives.
// ---------------------------------------------------------------------------
static int hjAdopted = 0;          // bitmask of slots we have already written

void hjHostAdoptPeers(void)
{
    GameSettings * gs = gameGetSettings();
    u32 ctx, peers;
    int i, count;

    if (isInMenus()) {
        hjAdopted = 0;      // rearm, so a retry is a clean run
        return;
    }
    if (!gs)
        return;

    // Recompute PlayerCount on BOTH machines. It sits at 1 on the host and, more
    // tellingly, at 1 on the joiner as well -- even though the joiner's clients[] has two
    // entries. Vanilla reaches 2. The joiner's roster arrives via our injected snapshot,
    // which only rewrites the arrays inside the first 0x100 bytes and never touches
    // PlayerCount at 0x178, so its roster has been half-built all along.
    count = 0;
    for (i = 0; i < GAME_MAX_PLAYERS; ++i)
        if (gs->PlayerClients[i] >= 0)
            ++count;

    if (!gameAmIHost()) {
        if (count > 0 && gs->PlayerCount != count) {
            HOTJOIN_LOG("adopt: joiner PlayerCount %d -> %d\n", gs->PlayerCount, count);
            gs->PlayerCount = count;
        }
        return;
    }

    ctx = *(u32*)HJ_NET_CTX_PTR;
    if (!ctx)
        return;
    peers = *(u32*)(ctx + HJ_CTX_PEERS);
    if (!peers)
        return;

    for (i = 0; i < GAME_MAX_PLAYERS; ++i) {
        void * p;
        if (i == *(int*)(peers + 0x404))          // skip ourselves
            continue;
        if (hjAdopted & (1 << i))                 // write once per slot, not per frame
            continue;
        if (gs->PlayerClients[i] >= 0)            // already present
            continue;

        p = internal_hjPeerLookup((void*)peers, i);
        if (!p || *(int*)((u32)p + 0x08) != 5)    // only fully-connected peers
            continue;

        gs->PlayerClients[i] = (short)i;
        gs->PlayerStates[i]  = gs->PlayerStates[*(int*)(peers + 0x404)];
        gs->PlayerTeams[i]   = 0;
        gs->PlayerSkins[i]   = 0;
        gs->PlayerTypes[i]   = 0;
        {
            /* placeholder name; the real one is in the 00-0F announce we do not parse yet */
            const char * nm = "Hotjoiner";
            int k;
            for (k = 0; k < 16; ++k)
                gs->PlayerNames[i][k] = (k < 9) ? nm[k] : 0;
        }
        gs->PlayerCount = count + 1;
        hjAdopted |= (1 << i);
        HOTJOIN_LOG("adopt: host wrote roster slot %d (client %d, state %d), n -> %d\n",
            i, i, gs->PlayerStates[i], gs->PlayerCount);
    }
}

// hjDumpNWPlayers -- the tNW_Player array, on BOTH machines.
//
// The array is STATIC, so its addresses are the same on host and joiner:
//   0x199a00:  li a0,3184; lui v0,0x23; lbu v1,1(a1); addiu v0,v0,-2736;
//              mult v1,v1,a0; addu v1,v1,v0      ->  0x0022F550 + idx*0xC70
// Confirmed live: a joiner's plist showed pNet=0022f550 (idx 0) and
// 002301c0 (idx 1), exactly base and base+0xC70.
//
// That matters because it means the argument to 0x001999b8 (the "spawn remote
// player" entry that calls the level's playerCreateRemoteForSession) does not
// have to be handed to us by the net layer -- it is a fixed address. What is
// still unknown is whether the HOST's slot for the joiner is populated or is
// just a zeroed slice of a static array, which is what this prints.
#define HJ_NWPLAYER_BASE   (0x0022F550)
#define HJ_NWPLAYER_STRIDE (0xC70)

static int hjNwDumps = 0;
static u32 hjLastNwSig = 0;

void hjDumpNWPlayers(void)
{
    u32 sig = 0;
    int i;

    for (i = 0; i < 2; ++i) {
        u32 p = HJ_NWPLAYER_BASE + (i * HJ_NWPLAYER_STRIDE);
        sig = (sig * 31) + *(u32*)(p + 0x00) + *(u32*)(p + 0x04)
            + (u32)*(short*)(p + 0x1a2) + (u32)*(short*)(p + 0x1a6)
            + (u32)*(unsigned char*)(p + 0x68)
            + *(u32*)(p + 0xc34) + *(u32*)(p + 0xc38) + *(u32*)(p + 0xc44);
    }
    if (sig == hjLastNwSig || hjNwDumps > 20)
        return;
    hjLastNwSig = sig;
    ++hjNwDumps;

    for (i = 0; i < 2; ++i) {
        u32 p = HJ_NWPLAYER_BASE + (i * HJ_NWPLAYER_STRIDE);
        HOTJOIN_LOG("nwp: [%d] %08x cid=%d pData=%08x flags=%08x bLocal=%d spawned=%d cbCalled=%d\n",
            i, p,
            *(int*)(p + 0x00), *(u32*)(p + 0x04), *(u32*)(p + 0x14),
            (int)*(char*)(p + 0x68),
            (int)*(short*)(p + 0x1a2), (int)*(short*)(p + 0x1a6));
        // The pad-input pipeline. A remote player on the host moves by replaying
        // decoded pad messages; if that stream stalls, the last frame repeats
        // forever, which looks exactly like walking in the facing direction with
        // yaw still tracking (rotation rides on the state message, not the pad).
        HOTJOIN_LOG("nwp: [%d] pad decodePos=%d frame=%d seq=%d buffered=%d rcvFrame=%d thr=%d skips=%d act=%08x tail=%08x\n",
            i,
            (int)*(char*)(p + 0xc30), (int)*(char*)(p + 0xc31),
            *(int*)(p + 0xc34), *(int*)(p + 0xc38), *(int*)(p + 0xc3c),
            (int)*(signed char*)(p + 0xc41), (int)*(char*)(p + 0xc42),
            *(u32*)(p + 0xc44), *(u32*)(p + 0xc48));
    }
}

// hjDumpPadStream -- the local player's outgoing pad cadence.
//
// Chain (Metropolis overlay + base exe):
//   playerCreateLocalForSlot: padCtx = *(0x002412F0 + i);
//                             *(padCtx + 0x56C) = producer 0x00534568
//   padPollControllerAndUpdate (0x488938) calls that hook (jalr at 0x488ca8)
//   producer tail 0x534804:  curFrame++;  if ((curFrame & 3) == 0)
//                                padStreamReady = cur_btn_bit_offset  -> SEND
//                            else padStreamReady = -1                 -> no send
//   playerUpdateLocalFrame (0x523210) sends only when copyPayload != 0,
//   i.e. only when padStreamReady != -1.
//
// So one send per 4 producer calls. Vanilla measures 15.1/s on the wire, which
// is 60/4 -- the producer runs once per frame. A hot-join host receives ~68/s,
// so either the producer runs ~4x per frame, or curFrame does not step by 1.
// The disassembly cannot tell those apart; these two counters can.
//
// PadStream lives at player + 0x430C (Ghidra's Player is 0x2600, so the
// decomp's player[1].field_0x1eed is player + 0x44ED):
//   +0x44E4  curFrame          -- +1 per producer call
//   +0x44E8  padStreamReady    -- bit count when a batch is ready, else -1
//   +0x44ED  send seq byte     -- +1 per packet actually sent
static int hjPsTick = 0;
static int hjPsLastFrame = 0;
static int hjPsLastSeq = -1;

void hjDumpPadStream(void)
{
    Player ** all;
    u32 p;
    int me, curFrame, seq, dFrame, dSeq;

    if (isInMenus() || !isInGame()) { hjPsLastSeq = -1; hjPsTick = 0; return; }
    if (++hjPsTick < 60)            // ~1 s at 60 Hz, so deltas read as per-second
        return;
    hjPsTick = 0;

    all = playerGetAll();
    if (!all)
        return;
    me = gameGetMyClientId();
    if (me < 0 || me >= GAME_MAX_PLAYERS || !all[me])
        return;
    p = (u32)all[me];

    curFrame = *(int*)(p + HJ_PS_CURFRAME);
    seq      = (int)*(unsigned char*)(p + HJ_PS_SEQ);

    if (hjPsLastSeq < 0) { hjPsLastFrame = curFrame; hjPsLastSeq = seq; return; }
    dFrame = curFrame - hjPsLastFrame;
    dSeq   = (seq - hjPsLastSeq) & 0xFF;   // the seq byte wraps
    hjPsLastFrame = curFrame;
    hjPsLastSeq   = seq;

    // Expect vanilla: producer ~60/s, sends ~15/s, ratio 4.
    HOTJOIN_LOG("padstream: curFrame=%d (+%d/s) seq=%d (+%d/s) ready=%d ratio=%d\n",
        curFrame, dFrame, seq, dSeq, *(int*)(p + HJ_PS_READY),
        dSeq ? (dFrame / dSeq) : -1);
}

extern void internal_hjSpawnRemotePlayer(void * nwPlayer);

// hjHostSpawnRemotes -- the missing call.
//
// Established across four captures:
//   - a CLIENT builds every player at level load from the roster (static slots);
//     a HOST builds its own at load and allocates remotes dynamically on join.
//   - in a hot-join the host's tNW_Player for the joiner is fully populated
//     (cid=1, real pNetPlayerData, spawned=1) and stays that way indefinitely --
//     only bCallbackCalled stays 0, i.e. 0x1999b8 was never invoked for it.
//   - on a joiner, bCallbackCalled flips to 1 for the REMOTE and stays 0 for the
//     LOCAL, which is what says the flag tracks playerCreateRemoteForSession.
//
// So the record is ready and nothing consumes it. Call the game's own entry point
// and let the level's constructor build the Player, rather than synthesising one.
//
// Deliberately conservative: host only, in-game only, and only for a slot that
// has a populated NWPlayer, no Player in the pointer table, and bCallbackCalled
// still clear. 0x1999b8 sets that flag itself, so this cannot fire twice for a
// slot -- but keep an explicit mask too, since a constructor of 2352 instructions
// run twice on one record is not something to leave to one flag.
static int hjSpawned = 0;

void hjHostSpawnRemotes(void)
{
    Player ** all;
    int i, me;

    if (isInMenus()) { hjSpawned = 0; return; }
    if (!gameAmIHost() || !isInGame())
        return;

    all = playerGetAll();
    if (!all)
        return;

    me = gameGetMyClientId();
    for (i = 0; i < GAME_MAX_PLAYERS; ++i) {
        u32 nwp = HJ_NWPLAYER_BASE + (i * HJ_NWPLAYER_STRIDE);
        if (i == me)                       continue;   // never the local player
        if (hjSpawned & (1 << i))          continue;
        if (all[i])                        continue;   // already has a Player
        if (*(int*)(nwp + 0x00) < 0)       continue;   // no client in this slot
        if (*(short*)(nwp + 0x1a6) != 0)   continue;   // callback already ran
        if (*(u32*)(nwp + 0x04) == 0)      continue;   // no tNW_PlayerData

        hjSpawned |= (1 << i);
        HOTJOIN_LOG("spawn: calling 0x1999b8 for nwp[%d] %08x cid=%d pData=%08x\n",
            i, nwp, *(int*)(nwp + 0x00), *(u32*)(nwp + 0x04));
        internal_hjSpawnRemotePlayer((void*)nwp);
        // Re-read the table: the constructor is what fills the entry in.
        // (playerGetAll is only implicitly declared in this file, so it has to
        // land in a typed local before it can be subscripted.)
        {
            Player ** now = playerGetAll();
            HOTJOIN_LOG("spawn: returned; cbCalled=%d player=%08x\n",
                (int)*(short*)(nwp + 0x1a6), now ? (u32)now[i] : 0);
        }
    }
}

void hjDumpRoster(void)
{
    GameSettings * gs = gameGetSettings();
    u32 sig = 0;
    int i, beat;

    if (!gs)
        return;

    for (i = 0; i < GAME_MAX_PLAYERS; ++i)
        sig = (sig * 31) + (u32)(gs->PlayerClients[i] & 0xFFFF)
            + (u32)((gs->PlayerStates[i] & 0xFF) << 16);
    sig = (sig * 31) + (u32)gs->PlayerCount;

    beat = (++hjRosterBeat >= 300);       // ~5 s, so steady state is visible too
    if (beat)
        hjRosterBeat = 0;
    if ((sig == hjLastRosterSig && !beat) || hjRosterDumps > 40)
        return;
    hjLastRosterSig = sig;
    ++hjRosterDumps;

    HOTJOIN_LOG("roster: host=%d game=%d menus=%d n=%d cid=%d\n",
        gameAmIHost(), isInGame(), isInMenus(), gs->PlayerCount,
        gameGetMyClientId());
    HOTJOIN_LOG("roster: clients=%d %d %d %d %d %d %d %d\n",
        gs->PlayerClients[0], gs->PlayerClients[1], gs->PlayerClients[2], gs->PlayerClients[3],
        gs->PlayerClients[4], gs->PlayerClients[5], gs->PlayerClients[6], gs->PlayerClients[7]);
    HOTJOIN_LOG("roster: states =%d %d %d %d %d %d %d %d\n",
        gs->PlayerStates[0], gs->PlayerStates[1], gs->PlayerStates[2], gs->PlayerStates[3],
        gs->PlayerStates[4], gs->PlayerStates[5], gs->PlayerStates[6], gs->PlayerStates[7]);
    HOTJOIN_LOG("roster: teams  =%d %d %d %d %d %d %d %d  types=%d %d %d %d %d %d %d %d\n",
        gs->PlayerTeams[0], gs->PlayerTeams[1], gs->PlayerTeams[2], gs->PlayerTeams[3],
        gs->PlayerTeams[4], gs->PlayerTeams[5], gs->PlayerTeams[6], gs->PlayerTeams[7],
        gs->PlayerTypes[0], gs->PlayerTypes[1], gs->PlayerTypes[2], gs->PlayerTypes[3],
        gs->PlayerTypes[4], gs->PlayerTypes[5], gs->PlayerTypes[6], gs->PlayerTypes[7]);
}

void hjDumpPeers(void)
{
    u32 ctx = *(u32*)HJ_NET_CTX_PTR;
    u32 peers, sig = 0;
    int i;

    if (!ctx)
        return;
    peers = *(u32*)(ctx + HJ_CTX_PEERS);
    if (!peers)
        return;

    // Only print when something actually changes, so this stays readable across a
    // multi-minute session instead of flooding at 60 Hz.
    for (i = 0; i < 8; ++i) {
        void * p = internal_hjPeerLookup((void*)peers, i);
        sig = (sig * 31) + (p ? (*(u32*)((u32)p + 0x08) + 1) : 0);
    }
    // Cap per game-entry, not per boot. The first version used a single global cap of
    // 40, which was entirely consumed by ~17 failed connect attempts in the menu -- so
    // the log went silent exactly when the joiner finally got in-game, which is the only
    // moment that matters. Reset the budget on each menus->in-game transition.
    if (isInMenus()) {
        hjPeerDumps = 0;
        hjLastPeerSig = 0;
    }
    if (sig == hjLastPeerSig || hjPeerDumps > 60)
        return;
    hjLastPeerSig = sig;
    ++hjPeerDumps;

    // 0x404 (my index), 0x430 (sweep gate) and 0x43C (peer count) are fields of the
    // PEERS block (ctx->0xE8), not of ctx -- the sweep reads them as 1028(s1)/1072(s1)/
    // 1084(s1) with s1 = ctx->0xE8. An earlier version read them off ctx and printed
    // "me=0 n=0" every time; that was garbage, not a finding.
    // p408 is the field the mark-connected guard compares a peer index against
    // (0x172658: `bne s4,v1` where v1 = peers->0x408). It is initialised to 256 at
    // 0x14f474 and is only ever set by RECEIVING peer message type 5, whose handler
    // branch calls ctx->0x44 = 0x171d18 -> `sw a1,1032(a0)`. A host that never receives
    // type 5 keeps 408 == 256, which matches no peer index, so it can never mark the
    // joiner connected -- and then wipes the half-open record.
    // The outbound peer message type is NOT built from a constant -- the sender at
    // 0x14bdb0 reads it straight out of its own record:
    //   14bde4  lw  s0,1024(s2)   ; s0 = peers->0x400 (my own record)
    //   14be08  lbu v1,8(s0)      ; myRecord->0x08
    //   14be0c  sb  v1,0(sp)      ; payload[0] = that
    // So the joiner sends 3 then 4 because its own 0x08 is 3 then 4, and it never sends
    // 5 because its own 0x08 never becomes 5. The step that would set it is in the
    // connect path:
    //   16fa68  bnez v0,0x16fac0  ; if (s6 | peers->0x438) != 0 -> SKIP
    //   16fa70  li v0,5
    //   16fa78  sw v0,8(s0)       ; myRecord->0x08 = 5
    //   16fa84  jal 0x171d18      ; publish it
    // p438 is therefore the prime suspect for the whole hot-join stall. Print it, plus
    // p400 (my own record pointer) and its 0x08, so we can see the sender's actual input.
    {
        u32 mine = *(u32*)(peers + 0x400);
        HOTJOIN_LOG("peers: me=%d n=%d gate=%d p408=%d p438=%08x mine=%08x mine08=%d ---\n",
            *(int*)(peers + 0x404), *(int*)(peers + 0x43C),
            *(int*)(peers + 0x430), *(int*)(peers + 0x408),
            *(u32*)(peers + 0x438), mine, mine ? *(int*)(mine + 0x08) : -1);
    }
    for (i = 0; i < 8; ++i) {
        void * p = internal_hjPeerLookup((void*)peers, i);
        if (!p)
            continue;
        // +0x08 is NOT reliably a connection state: the type-22 handler at 0x150dd8
        // looks the peer up (0x150e10) and then does `sw a1,8(s2)` at 0x150e48, writing
        // the INCOMING MESSAGE TYPE into it. So the 3->4->0 sequence we chased may be
        // message types arriving, not a teardown. Dump the neighbouring fields so a real
        // state machine can be told apart from that echo.
        HOTJOIN_LOG("peers: [%d] %08x t08=%d f00=%08x f04=%08x f0C=%08x f10=%08x\n",
            i, (u32)p, *(int*)((u32)p + 0x08), *(u32*)((u32)p + 0x00),
            *(u32*)((u32)p + 0x04), *(u32*)((u32)p + 0x0C), *(u32*)((u32)p + 0x10));
        HOTJOIN_LOG("peers: [%d]          f14=%08x f18=%d f1C=%d f20=%08x f24=%08x f28=%08x\n",
            i, *(u32*)((u32)p + 0x14), *(int*)((u32)p + 0x18), *(int*)((u32)p + 0x1C),
            *(u32*)((u32)p + 0x20), *(u32*)((u32)p + 0x24), *(u32*)((u32)p + 0x28));
    }
}

// ---------------------------------------------------------------------------
// Hotjoin: who destroys the joiner's peer record?
//
// Host-side peer dump shows the joiner's record cycling 3 -> 4 -> 0 every ~2.5-3 s,
// i.e. built up to state 4 then wiped (state, f18 and f1C all zeroed) and rebuilt.
// The link is not stalling one step short -- it is being torn down repeatedly.
//
// `0x170118` writes the whole record from stack args (1702b4 sw a1,8(s0) with a zero
// param would produce exactly this) and is reachable via the API block slot 0x1D8834,
// but its arity is unknown and it reads several stack slots, so a C wrapper risks
// corrupting the ABI. `0x173fc0` is the safer target: 4 register args, two real jal
// call sites, and it is the routine that (re)introduces a peer -- the prime suspect
// for resetting an in-flight handshake every retransmit.
//
// Log the call and the peer's state either side of it. If state collapses to 0 across
// this call, this is the teardown and `ra` names which caller did it:
//   ra = 0x172d84 -> the introduce-every-peer loop at 0x172d7c
//   ra = 0x173dc0 -> the inbound-message path at 0x173db8
// ---------------------------------------------------------------------------
// NOT reachable via its jal sites. Hooking 0x172d7c / 0x173db8 produced ZERO hits on
// both machines, while the host kept logging peerconnreq with ra = 0x174164/6c/74 --
// which are the three `jal 0x14ecd8` sites INSIDE 0x173fc0. So the function runs, just
// not through those call sites; it is dispatched through the net API table, slot
// 0x1d88b4, the same way worldConnect is reached via 0x1d884c. Hook the slot instead.
#define HJ_INTRO_SLOT    (0x001d88b4)
#define HJ_INTRO_ORIG    (0x00173fc0)

static int hjIntroLogged = 0;

int hjIntroducePeerHook(void * ctx, int peerIdx, int a2, int a3)
{
    u32 c = *(u32*)HJ_NET_CTX_PTR;
    u32 peers = c ? *(u32*)(c + HJ_CTX_PEERS) : 0;
    int before = -1, after = -1;
    void * pp;
    int ret;

    if (peers && peerIdx >= 0 && peerIdx < 8) {
        pp = internal_hjPeerLookup((void*)peers, peerIdx);
        if (pp) before = *(int*)((u32)pp + 0x08);
    }

    ret = internal_hjIntroducePeer(ctx, peerIdx, a2, a3);

    if (peers && peerIdx >= 0 && peerIdx < 8) {
        pp = internal_hjPeerLookup((void*)peers, peerIdx);
        if (pp) after = *(int*)((u32)pp + 0x08);
    }

    if (hjIntroLogged < 24) {
        ++hjIntroLogged;
        HOTJOIN_LOG("introduce: idx=%d ra=%08x a2=%08x a3=%08x state %d -> %d ret=%d\n",
            peerIdx, (u32)__builtin_return_address(0), (u32)a2, (u32)a3,
            before, after, ret);
    }
    return ret;
}

// ---------------------------------------------------------------------------
// Hotjoin: what messages actually drive the peer record?
//
// 0x150dd8 is the RT handler for message type 22 (registered via `li a0,22` at
// 0x1510a4, and present in the handler table at index 22). It does:
//   150e10  jal 0x14f8e8         ; peer = lookup(peers, payload[1])
//   150e18  move s2,v0           ; s2 IS the peer record
//   150e48  sw a1,8(s2)          ; peer->0x08 = payload[0]  (the MESSAGE TYPE)
//   150e5c  bne a1,5 ...         ; type 5 -> ctx->0x44 (0x171d18)
//   150f98  ...                  ; type 3 -> ctx->0x94 (0x173fc0, introducePeer)
// so the value our dump prints as "state" is overwritten with the inbound message
// type on every one of these. Log the type and the peer it lands on, so the
// 3 -> 4 -> 0 sequence can be read as protocol traffic rather than a teardown.
//
// Four register arguments, dispatched from the handler table, so wrapping is ABI-safe
// (same shape as the aux-accept probe).
// ---------------------------------------------------------------------------
#define HJ_T22_TYPE   (22)
#define HJ_T22_ORIG   (0x00150dd8)

static int hjT22Installed = 0;
static u32 hjT22Orig = 0;

// Log budgets are refilled every HJ_LOG_EPOCH frames rather than spent once for the
// life of the process. Both the peer dump and the type-22 hook previously used one-shot
// caps, which go quiet exactly during a long session -- i.e. during the part we care
// about. A rolling window keeps output bounded while still covering the whole run.
#define HJ_LOG_EPOCH   (1800)   // ~30 s at 60 Hz
static unsigned char hjT22Seen[16][8];
static int hjLogEpochTick = 0;

void hjLogEpochTock(void)
{
    int t, p;
    if (++hjLogEpochTick < HJ_LOG_EPOCH)
        return;
    hjLogEpochTick = 0;
    hjPeerDumps = 0;
    hjLastPeerSig = 0;
    hjRosterDumps = 0;
    hjLastRosterSig = 0;
    hjNwDumps = 0;
    hjLastNwSig = 0;
    // The player-array dump had the same one-shot cap as the others, and it cost us a
    // measurement: on the host it fired ONCE at 217.7s, six seconds BEFORE the roster
    // adopt at 223.98s, so the run that finally produced a matching roster on both
    // machines had no picture of the host's player array afterwards -- exactly the thing
    // that says whether an entity followed the roster write.
    hjPlayerMapLogged = 0;
    for (t = 0; t < 16; ++t)
        for (p = 0; p < 8; ++p)
            hjT22Seen[t][p] = 0;
}

int hjType22Hook(void * a0, void * a1, int a2, u8 * payload)
{
    int (*orig)(void *, void *, int, u8 *) =
        (int (*)(void *, void *, int, u8 *))hjT22Orig;
    int msgType = payload ? payload[0] : -1;
    int peerIdx = payload ? payload[1] : -1;
    int ret;

    ret = orig(a0, a1, a2, payload);

    // Budget per (msgType, peerIdx) pair, refilled by the log epoch below -- NOT one
    // global counter. A single global cap of 40 was silently fatal: the host burned all
    // 40 during one early run and then logged nothing for the next eleven minutes, so
    // "no type=5 in the host dump" meant only "the budget was spent", not "nothing
    // arrived". The host never returns to menus, so it can never reset on that edge.
    if (msgType >= 0 && msgType < 16 && peerIdx >= 0 && peerIdx < 8
        && hjT22Seen[msgType][peerIdx] < 4) {
        ++hjT22Seen[msgType][peerIdx];
        u32 c = *(u32*)HJ_NET_CTX_PTR;
        u32 peers = c ? *(u32*)(c + HJ_CTX_PEERS) : 0;
        void * pp = (peers && peerIdx >= 0 && peerIdx < 8)
                  ? internal_hjPeerLookup((void*)peers, peerIdx) : 0;
        HOTJOIN_LOG("msg22: type=%d peerIdx=%d peer=%08x t08=%d f1C=%d ret=%d\n",
            msgType, peerIdx, (u32)pp,
            pp ? *(int*)((u32)pp + 0x08) : -1,
            pp ? *(int*)((u32)pp + 0x1C) : -1, ret);
    }
    return ret;
}

void hjInstallType22Probe(void)
{
    u32 table, maxTypes;
    u32 * slot;

    if (hjT22Installed)
        return;

    table = *(u32*)HJ_RT_HANDLER_TABLE_PTR;
    maxTypes = *(u32*)HJ_RT_MAXTYPES_PTR;
    if (!table || !maxTypes || maxTypes > 256)
        return;

    slot = (u32*)(table + (HJ_T22_TYPE * 4));
    if (*slot != HJ_T22_ORIG) {
        HOTJOIN_LOG("msg22: slot22 @%08x holds %08x, expected %08x -- NOT hooked\n",
            (u32)slot, *slot, HJ_T22_ORIG);
        hjT22Installed = 1;
        return;
    }

    hjT22Orig = *slot;
    *slot = (u32)&hjType22Hook;
    hjT22Installed = 1;
    HOTJOIN_LOG("msg22: probe installed, slot22 @%08x\n", (u32)slot);
}

// ---------------------------------------------------------------------------
// Hotjoin: does the mark-connected path ever run, and does type 5 ever get sent?
//
// 0x172898 writes the real connected marker (0x172970: peer->0x08 = 5) and is called
// from 0x172668 only when the peer index equals peers->0x408. That field starts at 256
// (0x14f474) and is set solely by receiving message type 5 (dispatcher branch at
// 0x150e5c -> ctx->0x44 = 0x171d18 -> `sw a1,1032(a0)`).
//
// Observed: the joiner RECEIVES type 5 (so its p408 should become 0) but the host never
// does. If this hook fires on the joiner and the host still sees no type 5, the joiner
// completes locally without telling the host -- which is the whole bug.
//
// 0x172668 is a genuine `jal` (verified: the only entries into 0x172898 are that call
// site), and the callee takes three register arguments, so HOOK_JAL is safe here.
// ---------------------------------------------------------------------------
#define HJ_MARKCONN_SITE (0x00172668)

extern int internal_hjMarkConnected(void * peers, int peerIdx, void * out);
extern int internal_hjSendPeerMsg(void * peers, int targetIdx);
static int hjMarkLogged = 0;

int hjMarkConnectedHook(void * peers, int peerIdx, void * out)
{
    int before = -1, after = -1;
    void * pp;
    int ret;

    if (peers && peerIdx >= 0 && peerIdx < 8) {
        pp = internal_hjPeerLookup(peers, peerIdx);
        if (pp) before = *(int*)((u32)pp + 0x08);
    }

    ret = internal_hjMarkConnected(peers, peerIdx, out);

    if (peers && peerIdx >= 0 && peerIdx < 8) {
        pp = internal_hjPeerLookup(peers, peerIdx);
        if (pp) after = *(int*)((u32)pp + 0x08);
    }

    if (hjMarkLogged < 16) {
        ++hjMarkLogged;
        HOTJOIN_LOG("markconn: idx=%d p408=%d t08 %d -> %d ret=%d\n",
            peerIdx, peers ? *(int*)((u32)peers + 0x408) : -1, before, after, ret);
    }
    return ret;
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
    HOOK_JAL(HJ_MARKCONN_SITE, &hjMarkConnectedHook);

    if (*(u32*)HJ_INTRO_SLOT == HJ_INTRO_ORIG) {
        POKE_U32(HJ_INTRO_SLOT, &hjIntroducePeerHook);
        HOTJOIN_LOG("introduce hook installed at slot %08x\n", HJ_INTRO_SLOT);
    } else {
        HOTJOIN_LOG("introduce slot %08x holds %08x, expected %08x -- NOT hooked\n",
            HJ_INTRO_SLOT, *(u32*)HJ_INTRO_SLOT, HJ_INTRO_ORIG);
    }

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
void hjFixMissingPads(void) { }
void hjDumpDispatch(void) { }
void hjAnnounce(void) { }
void hjDumpRoster(void) { }
void hjDumpNWPlayers(void) { }
void hjHostSpawnRemotes(void) { }
void hjDumpPadStream(void) { }
void hjHostAdoptPeers(void) { }
void hjLogEpochTock(void) { }
void hjDumpPeers(void) { }
void hjInstallType22Probe(void) { }
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

        // Reaching staging means we are on our way INTO a game, so the pad
        // table may be seeded during the load window that follows. Cleared
        // again by hjFixMissingPads once we are actually in the game, so the
        // teardown window on the way out stays untouched.
        hjSeedArmed = 1;

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
