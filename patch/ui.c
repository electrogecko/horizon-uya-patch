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
    // Log on the first sighting AND whenever the object for a slot changes. This
    // used to be a hard one-shot, which made a rejoin look like the handler had
    // stopped running when in fact it was only the log that had stopped. Do not
    // read absence of this line as absence of the call.
    {
        static u32 lastObj[HJ_PLAYERBIT_TABLE_MAXIDX];
        if (!hjPlayerBitSeen || lastObj[idx] != obj) {
            hjPlayerBitSeen = 1;
            lastObj[idx] = obj;
            HOTJOIN_LOG("playerbit: OK obj=%08x idx=%d id=%d ra=%08x\n",
                obj, idx, playerIndex, (u32)__builtin_return_address(0));
        }
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


// ---------------------------------------------------------------------------
// Hotjoin: WHO WIPES THE PEER RECORD.
//
// Every failing join shows the same 2 s cycle on the host: three connect requests, an
// introduce, msg22 type=3 (record -> state 3, f18=2), msg22 type=4 twice (record ->
// state 4), and then, 15-170 ms later, the whole record reads back as zeroes with the
// slot pointer unchanged. The successful join in the same log shows that cycle too --
// it just got one cycle where the zeroing did NOT happen, and type=5 arrived 1.1 s
// later. So this is a race that hot-join loses most of the time, not a hot-join-only
// code path.
//
// Traced statically from the RAM image (ntsc.27.Lobby.bin, file offset == vaddr):
//   0x14c658  peerReset(peers, idx): rec = peerLookup(peers, idx); memset(rec, 0, 40)
//             -- 40 bytes is exactly the record size (0x14f960 allocates `li a0,40`),
//                which is why our dump's f28 keeps its stale value: it is past the end.
//   0x14cea8  peerClose(peers, idx): fires the disconnect callbacks, then peerReset.
//             The ONLY caller of 0x14c658.
// peerClose has exactly two call sites:
//   0x14d0e0  inside the callback at 0x14d098 -- taken when its 4th argument is 0.
//             The other branch bumps peers->0x438 and retransmits (0x14c390); our
//             dumps show p438 stuck at 0, so this side never runs and the close side
//             always does.
//   0x150310  inside 0x150230(idx, reason) -- taken when 0 < reason < 3.
// Both are plain `jal`s, so HOOK_JAL is safe and `ra` alone separates them.
//
// Budgeted and refilled per log epoch: this fires about once per 2 s, never per frame.
#define HJ_PEERCLOSE_SITE_A (0x0014d0e0)
#define HJ_PEERCLOSE_SITE_B (0x00150310)
#define HJ_PEERCLOSE_CALL   (0x0c0533aa)   // jal 0x14cea8

extern void internal_hjPeerClose(void * peers, int idx);   // 0x14cea8
int hjCloseLogged = 0;
int hjLeaveCallerLogged = 0;
int hjLeaveSuppressed = 0;
int hjLeavePending = 0;
int hjLeaveConnectSeq = 0;
int hjLeaveSkipDestroy = 0;
int hjDestroyLogged = 0;
int hjDestroySitesHooked = 0;

// ---------------------------------------------------------------------------
// The leave EPILOGUE at 0x001961D4, which runs whether or not we suppress the two
// teardown calls before it:
//
//   1961d4  li   v1,5
//   1961dc  sw   v1,0x120(s0)     state = 5
//   1961f0  li   v0,-1
//   1961f4  sw   v0,0x08(s0)      myClientIndex = -1
//   1961fc  sw   zero,0x130(s0)
//   196200  sw   v0,0x00(s0)
//   196204  sw   zero,0x04(s0)    session pointer = NULL
//   19620c  sw   zero,0x12c(s0)
//
// s0 is 0x001A5E50, and GAME_NET_INFO is 0x001A5E40 -- so +0x08 here IS
// tNW_Info.myClientIndex (0x1A5E40 + 0x18). That is the `cid=-1` in our roster dump.
//
// Measured with both calls suppressed: peers survived (both records at 5), gs survived,
// nwp[0] was rebuilt, the roster read n=2 states=8 8 -- and the joiner still sat in
// menus forever, because the epilogue had wiped its client id and session pointer. The
// objects were fine; the bookkeeping that names them was gone.
//
// So snapshot the fields the epilogue clobbers at suppression time and put them back on
// the next tick. One frame of bad bookkeeping is survivable -- the client demonstrably
// just sits there -- whereas losing it permanently is what blocks the join.
#define HJ_SM_BASE      (0x001A5E50)
#define HJ_SM_F00       (0x00)
#define HJ_SM_SESSION   (0x04)
#define HJ_SM_CLIENTID  (0x08)
#define HJ_SM_STATE     (0x120)
#define HJ_SM_F12C      (0x12c)
#define HJ_SM_F130      (0x130)
#define HJ_SM_LEAVENOW  (0x001A5FC0)   // +0x170: 1 = leave on THIS pass, no async queue

int hjSmRestorePending = 0;
int hjSmRestoreLogged = 0;
u32 hjSmSaved[6];
int hjLeaveReqState = 7;   // 7 = established session; what leavecall reports every time
int hjSmWatchLast = -1;
int hjSmWatchLogged = 0;
int hjCcLogged = 0;
int hjCcInstalled = 0;
int hjLeaveActLogged = 0;
int hjLeaveActHooked = 0;
int hjBackoutLogged = 0;
int hjBackoutHooked = 0;
int hjCbLogged = 0;
int hjRt12Logged = 0;
int hjRt12Installed = 0;
#define HJ_RT12_DEFER_MAX (240)   // ~4 min of 1 Hz retries; the loop times out long before
int hjRt12Defer = 0;
u32 hjRt12Orig = 0;
int hjEvLogged = 0;
int hjEvDropped = 0;
int hjLatchLogged = 0;
u32 hjLatchSeen[4] = {0,0,0,0};
int hjLatchWatchLogged = 0;

static void hjSnapshotStateMachine(void)
{
    hjSmSaved[0] = *(u32*)(HJ_SM_BASE + HJ_SM_F00);
    hjSmSaved[1] = *(u32*)(HJ_SM_BASE + HJ_SM_SESSION);
    hjSmSaved[2] = *(u32*)(HJ_SM_BASE + HJ_SM_CLIENTID);
    hjSmSaved[3] = *(u32*)(HJ_SM_BASE + HJ_SM_STATE);
    hjSmSaved[4] = *(u32*)(HJ_SM_BASE + HJ_SM_F12C);
    hjSmSaved[5] = *(u32*)(HJ_SM_BASE + HJ_SM_F130);
    hjSmRestorePending = 1;
}

// Every transition of the session manager's state, edge-triggered. This is the thing
// we have been inferring from side effects; now it is just printed. Cheap: one load
// per frame, one log line per transition.
void hjWatchStateMachine(void)
{
    int now = *(int*)(HJ_SM_BASE + HJ_SM_STATE);
    if (now == hjSmWatchLast)
        return;
    if (hjSmWatchLogged < 64) {
        ++hjSmWatchLogged;
        HOTJOIN_LOG("sm: state %d -> %d  cid=%d session=%08x flag=%d menus=%d game=%d gs=%p\n",
            hjSmWatchLast, now,
            *(int*)(HJ_SM_BASE + HJ_SM_CLIENTID),
            *(u32*)(HJ_SM_BASE + HJ_SM_SESSION),
            *(int*)0x001A5FC0,
            isInMenus(), isInGame(), gameGetSettings());
    }
    hjSmWatchLast = now;
}

void hjRestoreStateMachine(void)
{
    u32 nowState, nowSession;

    if (1 || !hjSmRestorePending)   // DISABLED (section 48)
        return;
    hjSmRestorePending = 0;

    nowState   = *(u32*)(HJ_SM_BASE + HJ_SM_STATE);
    nowSession = *(u32*)(HJ_SM_BASE + HJ_SM_SESSION);

    // Only act if the epilogue actually ran. If it did not, the saved values are the
    // live ones and writing them back is a no-op we would rather not perform.
    if (nowSession != 0 || nowState != 5)
        return;

    {
        // The state to unwind to is the one from BEFORE the leave was requested. If that
        // itself reads as a leave-in-progress value (9/10/11), something is off and 7
        // (established) is the only sane target.
        int target = (hjLeaveReqState >= 1 && hjLeaveReqState <= 8) ? hjLeaveReqState : 7;

        *(u32*)(HJ_SM_BASE + HJ_SM_F00)      = hjSmSaved[0];
        *(u32*)(HJ_SM_BASE + HJ_SM_SESSION)  = hjSmSaved[1];
        *(u32*)(HJ_SM_BASE + HJ_SM_CLIENTID) = hjSmSaved[2];
        *(u32*)(HJ_SM_BASE + HJ_SM_STATE)    = (u32)target;
        *(u32*)(HJ_SM_BASE + HJ_SM_F12C)     = hjSmSaved[4];
        *(u32*)(HJ_SM_BASE + HJ_SM_F130)     = hjSmSaved[5];

        if (hjSmRestoreLogged < 8) {
            ++hjSmRestoreLogged;
            HOTJOIN_LOG("smrestore: state 5 -> %d (snapshot had %d, request had %d), cid -1 -> %d, session 0 -> %08x\n",
                target, (int)hjSmSaved[3], hjLeaveReqState, (int)hjSmSaved[2], hjSmSaved[1]);
        }
    }
}
int hjLeaveSitesHooked = 0;
u32 hjLeaveOrig = 0;
int hjLeaveLogged = 0;
int hjCloseSuppressed = 0;
// Declared here, not next to hjSessionEndHook: hjLogEpochTock refills the budget and
// lives earlier in the file.
u32 hjSessEndOrig = 0;
int hjSessEndLogged = 0;

// Cap the protection so a peer that really is gone is eventually released. ~40 closes
// is about 80 s of the 2 s retry cycle -- far longer than any join needs, short enough
// that a dead slot does not survive the whole match. Rearmed in menus by hjAnnounce.
#define HJ_CLOSE_SUPPRESS_MAX (40)

// a2/a3 are still live at the 0x14d0e0 call site: 0x14d098 only copies a0 into t0 and
// branches on a2/a3 before it gets here, so nothing has clobbered them. a3 is 0 by the
// branch condition; a2 is the one unknown worth reading.
void hjPeerCloseHook(void * peers, int idx, int a2, int a3)
{
    u32 ra = (u32)__builtin_return_address(0);
    void * pp = (peers && idx >= 0 && idx < 8)
              ? internal_hjPeerLookup(peers, idx) : 0;
    int t08 = pp ? *(int*)((u32)pp + 0x08) : -1;

    // The close is what loses us the join. Measured on the host: the joiner's record
    // reaches state 4, and this fires 15-170 ms later and memsets it, while the type-5
    // that would finish the handshake does not arrive until ~1.1 s after state 4. So
    // the record has to survive the handshake window or the join cannot complete.
    //
    // Suppress ONLY mid-handshake (states 1..4), only on the host, only in-game. An
    // ESTABLISHED peer at state 5 still closes normally -- that path is correct and is
    // what feeds the reaper when a player quits (observed: close at t08=5, reap 0.9 s
    // later). This does not explain WHY the close fires; it stops it eating the
    // handshake while that is still open.
    // DISABLED (section 49). This was guarding against the 2 s wipe cycle of section 33,
    // which turned out to be the joiner LEAVING (its own retry loop) and the host closing
    // the departed peer correctly. Suppressing it left the host holding a dead record at
    // state 2, so on the joiner's next attempt the host never re-introduced it and the
    // joiner saw peers[0]=NULL immediately. Log only.
    if (0 && gameAmIHost() && isInGame() && !isInMenus()
        && t08 >= 1 && t08 <= 4
        && hjCloseSuppressed < HJ_CLOSE_SUPPRESS_MAX) {
        ++hjCloseSuppressed;
        if (hjCloseLogged < 24) {
            ++hjCloseLogged;
            HOTJOIN_LOG("peerclose: SUPPRESSED idx=%d ra=%08x t08=%d f18=%d a2=%08x a3=%08x n=%d\n",
                idx, ra, t08,
                pp ? *(int*)((u32)pp + 0x18) : -1,
                (u32)a2, (u32)a3, hjCloseSuppressed);
        }
        return;
    }

    if (hjCloseLogged < 24) {
        ++hjCloseLogged;
        HOTJOIN_LOG("peerclose: idx=%d ra=%08x rec=%08x t08=%d f18=%d f1C=%d p438=%d p408=%d a2=%08x a3=%08x\n",
            idx, ra, (u32)pp, t08,
            pp ? *(int*)((u32)pp + 0x18) : -1,
            pp ? *(int*)((u32)pp + 0x1C) : -1,
            peers ? *(int*)((u32)peers + 0x438) : -1,
            peers ? *(int*)((u32)peers + 0x408) : -1,
            (u32)a2, (u32)a3);
    }

    internal_hjPeerClose(peers, idx);
}

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

    HOTJOIN_LOG("connect[%d] IN params=%08x out=%08x busy=%08x ctx=%08x sm=%d stk=%08x/%08x/%08x/%08x\n",
        n, (u32)params, (u32)out, busy, *(u32*)HJ_NET_CTX_PTR, *(int*)0x001A5F70,
        *(u32*)0x001CF760, *(u32*)0x001CF764, *(u32*)0x001CF768, *(u32*)0x001CF76C);
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
#define HJ_ANNOUNCE_MAX_SENDS   (240)  // a cap, not an expected count
#define HJ_ANNOUNCE_PERIOD      (60)   // frames between resends once the burst is spent
// The host's record for the joiner is closed (memset to 0 by peerClose, see FINDINGS
// s33) 15-170 ms after it reaches state 4. Our type-5 announce is what drives that
// record to 5, and at a flat 1 Hz it lands inside that window roughly one time in six
// -- which is exactly the observed join rate. In the one join that worked, the host's
// record happened to survive a full 1.09 s (one announce period) and the very next
// announce completed it. So burst first, then settle: the burst is what wins the race,
// the 1 Hz tail is what covers a host that is slow to arrive.
#define HJ_ANNOUNCE_BURST_SENDS (20)   // sends issued at the fast rate
#define HJ_ANNOUNCE_BURST_PERIOD (6)   // frames between them (~10 Hz, ~2 s of burst)

static int hjAnnounceWasInMenus = 0;
#define HJ_PROMOTE_STALL (90)   // 1.5 s: the game's own 3 -> 5 lands at ~0.2 s
int hjPromoteStall = 0;
extern int internal_hjPublishMyIndex(void * peers, int idx);   // 0x171d18
// 0x171d30 -- the completion gate. It has NO static callers: its address lives at
// ctx+0x8C (0x001D88AC) and the net layer invokes it when a peer event arrives. So
// satisfying its gates is not enough on a stalled rejoin; nothing re-evaluates them
// until another peer message shows up, and none does. The promote below calls it
// directly, exactly as the net layer would. It takes no arguments and reads only
// globals (ctx->0xE8, netctx->0x10C, peers->0x400/0x404).
extern int internal_hjCheckAllConnected(void);   // 0x171d30

void hjAnnounce(void)
{
    u32 ctx = *(u32*)HJ_NET_CTX_PTR;
    u32 peers, mine;

    {
        int inMenus = isInMenus();

        // Rearm on the EDGE into menus, so a retry is a clean run rather than inheriting
        // a spent budget -- but do NOT return while in menus. Measured: the joiner's own
        // record reached state 4 at client 745.3047 with menus=1, and the old level-
        // triggered gate meant hjAnnounce refused to promote it; the joiner then tore
        // down 0.03 s later having never announced. Staging IS when the announce has to
        // happen for a hot-join.
        if (inMenus && !hjAnnounceWasInMenus) {
            hjAnnounceDone = 0;
            hjAnnounceSends = 0;
            hjAnnounceTick = 0;
            hjCloseSuppressed = 0;
            hjLeaveSuppressed = 0;
        }
        hjAnnounceWasInMenus = inMenus;

        // Only announce from menus when this is actually a hot-join: the server clamps
        // an in-game host to GAME_START (7) in the roster it injects, whereas an ordinary
        // staging join sits at READY (6) until the match starts. Without this a vanilla
        // staging join would start forcing its own record to 5 mid-staging, which is a
        // behaviour change we have no evidence is safe.
    }

    if (!ctx)
        return;
    peers = *(u32*)(ctx + HJ_CTX_PEERS);
    if (!peers)
        return;
    mine = *(u32*)(peers + 0x400);
    if (!mine)
        return;

    // The connect completion at ctx+0xF0 is gated by 0x00171D30, and gate B is
    //     v0 = myRec->0x08 - 4;  if ((unsigned)v0 >= 2) return;
    // i.e. MY OWN record must read 4 or 5 or the completion never fires -- the manager
    // stays at state 9 and the joiner spins forever. Measured across a working join and
    // a stuck rejoin on the same boot:
    //     success  mine08 3 -> 3 -> 5 at +180 ms, completion 70 ms later
    //     stuck    mine08 3 -> 3 -> 3 ... forever, no completion, no gs
    // The game's own 3 -> 5 transition is 0x0016FA78 (`li v0,5; sw v0,8(s0)`, then
    // 0x18 = 1 and 0x171D18 to publish the index), taken only when it has no outstanding
    // type-21 sends AND peers->0x438 == 0. On the rejoin it has an outstanding send, so
    // it never runs -- which is section 35's `0x0016FA68` ordering condition, seen from
    // the other side.
    //
    // So accept 3 as well as 4, but only after the peer layer has had its chance: the
    // manager still at 9 (completion pending), 0x438 clear, and stalled for
    // HJ_PROMOTE_STALL frames. On the fast path the game gets there first and this never
    // fires.
    // Deliberately NOT gated on gs: on a stuck rejoin gs is NULL for the entire stall,
    // because gs only appears once the completion has run. The discriminator is the
    // stall itself -- manager parked at 9 with the completion pending and my own record
    // still at 3 -- which no healthy join of either kind sits in for 1.5 s.
    if (!gameAmIHost() && *(u32*)(peers + 0x438) == 0
        && *(int*)(mine + 0x08) == 3
        && *(int*)(HJ_SM_BASE + HJ_SM_STATE) == 9) {
        if (++hjPromoteStall == HJ_PROMOTE_STALL) {
            void * p0 = internal_hjPeerLookup((void*)peers, 0);
            *(int*)(mine + 0x08) = 5;
            *(int*)(mine + 0x18) = 1;
            internal_hjPublishMyIndex((void*)peers, *(int*)(peers + 0x404));
            {
                u32 nctx = *(u32*)HJ_NET_CTX_PTR;
                int gateA = nctx ? *(int*)(nctx + 0x10C) : -1;
                int r = internal_hjCheckAllConnected();
                HOTJOIN_LOG("promote: myRec %08x 3 -> 5 after %d frames; idx %d; p0 t08=%d f1C=%d p408=%d p43C=%d gateA=%d check=%d sm=%d gs=%p\n",
                    mine, HJ_PROMOTE_STALL, *(int*)(peers + 0x404),
                    p0 ? *(int*)((u32)p0 + 0x08) : -1, p0 ? *(int*)((u32)p0 + 0x1C) : -1,
                    *(int*)(peers + 0x408), *(int*)(peers + 0x43C), gateA, r,
                    *(int*)(HJ_SM_BASE + HJ_SM_STATE), gameGetSettings());
            }
        }
    } else {
        hjPromoteStall = 0;
    }

    // The hot-join gate for the ANNOUNCE only. It cannot cover the promote above: the
    // stall happens before gs exists (`gs=0x0` for the whole stuck rejoin), which is
    // exactly why the first version of the promote never fired -- it sat behind this
    // very return. The server clamps an in-game host to GAME_START (7) in the roster it
    // injects, so a vanilla staging join (host at READY 6) still never announces.
    if (isInMenus()) {
        GameSettings * ags = gameGetSettings();
        if (!ags || ags->PlayerStates[0] < 7)
            return;
    }

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
    // Only the machine that PERFORMED the 4 -> 5 promotion announces. The host's own
    // record already sits at 5 from the moment it opens the game, so without this gate
    // the host also ran the send loop -- 240 unsolicited type-5 broadcasts per game,
    // from a machine that has nothing to announce. That is traffic vanilla never emits.
    if (hjAnnounceDone && *(int*)(mine + 0x08) == 5
        && hjAnnounceSends < HJ_ANNOUNCE_MAX_SENDS) {
        if (--hjAnnounceTick <= 0) {
            hjAnnounceTick = (hjAnnounceSends < HJ_ANNOUNCE_BURST_SENDS)
                           ? HJ_ANNOUNCE_BURST_PERIOD : HJ_ANNOUNCE_PERIOD;
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
// One bit per slot: "we have already called the spawn invoker for this player".
// Cleared on the menus edge -- and, since section 63, by the reaper, because an in-game
// host NEVER returns to menus. A stale bit here silently disables every repair below it.
int hjSpawned = 0;
int hjAdopted = 0;                 // bitmask of slots we have already written

// The tNW_Player array, needed here as well as further down. Identical redefinition
// is legal C; the authoritative comments on these live with hjDumpNWPlayers.
#define HJ_NWPLAYER_BASE   (0x0022F550)
#define HJ_NWPLAYER_STRIDE (0xC70)
#define HJ_NW_SEQ          (0xc34)

// Slots reaped and not yet proven to have come back, plus the tNW_Player sequence
// each held at the moment it was reaped. See hjHostAdoptPeers for why.
int hjReapBlocked = 0;
int hjReapBlockFrames[GAME_MAX_PLAYERS];

// Per-slot: the tNW_Player pad sequence at the moment the slot was reaped, and a
// bit saying we have not yet seen it move. Consumed by hjHostSpawnRemotes.
int hjSpawnBlocked = 0;
int hjSpawnSeq[GAME_MAX_PLAYERS];
#define HJ_REAP_BLOCK_MAX  (900)   // 15 s, then adopt anyway rather than hang

void hjHostAdoptPeers(void)
{
    GameSettings * gs = gameGetSettings();
    u32 ctx, peers;
    int i, count;

    if (isInMenus()) {
        hjAdopted = 0;      // rearm, so a retry is a clean run
        hjReapBlocked = 0;
        hjSpawnBlocked = 0;
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

        // (Re-adoption of a just-reaped slot is gated below, after the peer lookup.)

        if (gs->PlayerClients[i] >= 0)            // already present
            continue;

        p = internal_hjPeerLookup((void*)peers, i);

        // Do not re-adopt a slot we just reaped until the OLD peer record is gone.
        //
        // Without a gate the reaper cleared the adopt bit outright, and because a
        // departing peer lingers at state 5, this loop re-claimed the slot on the
        // next frame and hjHostSpawnRemotes rebuilt the player -- a destroy/recreate
        // cycle against a live player (reap 112.9456 -> adopt 112.9620 -> spawn
        // 112.9637). That is what made the remote's weapon moby alternate with NULL.
        //
        // The first attempt gated on the pad sequence advancing, which DEADLOCKED:
        // the sequence cannot advance until the joiner is in game, and the joiner
        // cannot get in game until the host adopts it. Measured: "blocked until seq
        // moves off 2" with no unblock, ever, and the joiner stuck on "waiting for
        // players". Never gate an admission step on evidence that only exists after
        // admission.
        //
        // The peer record does not have that problem: the stale one is torn down
        // independently of anything we do, and a genuine rejoin brings a fresh one
        // back to state 5. So wait for it to leave 5 (or disappear) once.
        if (hjReapBlocked & (1 << i)) {
            if (!p || *(int*)((u32)p + 0x08) != 5) {
                hjReapBlocked &= ~(1 << i);
                HOTJOIN_LOG("adopt: slot %d unblocked, stale peer cleared (p=%08x)\n",
                    i, (u32)p);
            } else if (++hjReapBlockFrames[i] < HJ_REAP_BLOCK_MAX) {
                continue;                        // still the record we reaped
            } else {
                // Belt and braces. A gate that can never open is worse than the
                // churn it prevents -- this file has now produced one of those.
                hjReapBlocked &= ~(1 << i);
                HOTJOIN_LOG("adopt: slot %d unblocked on timeout after %d frames\n",
                    i, hjReapBlockFrames[i]);
            }
        }

        if (!p || *(int*)((u32)p + 0x08) != 5)    // only fully-connected peers
            continue;

        gs->PlayerClients[i] = (short)i;
        gs->PlayerStates[i]  = gs->PlayerStates[*(int*)(peers + 0x404)];
        gs->PlayerTeams[i]   = 0;
        gs->PlayerSkins[i]   = 0;
        gs->PlayerTypes[i]   = 0;
        // Deliberately DO NOT write a name here. The placeholder that used to live at
        // this line round-tripped: the host wrote "Hotjoiner", its periodic settings
        // broadcast carried that to the joiner (the broadcast is not the single-target
        // path DME injects the real name into), the joiner then registered ITSELF under
        // it, and the host read it straight back out of the registration. Measured: a
        // namescan of the host's tNW_Player found 'Hotjoiner' at nwp[1]+0x1b0 while the
        // host's OWN entry nwp[0] had no name at all -- proof that +0x1b0 is filled from
        // the network, not from our roster, so any placeholder we invent here comes back
        // to us as if it were real. hjHostRefreshNames below copies the name the joiner
        // actually registered under.
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

// ---------------------------------------------------------------------------
// Hotjoin: reap a joiner who has left.
//
// An in-game host never tears down a departed hot-joiner. Measured across a
// full join/leave/rejoin cycle, ~120s after the joiner quit:
//     roster: clients=0 1   states=8 8
//     nwp: [1] cid=1 spawned=1 cbCalled=1
//     nwp: [1] pad seq=149 buffered=0 rcvFrame=1888 act=0 tail=0   (frozen)
//     plist: [1] 00319f80 HEAP pMoby=01b2e380
//     peerconnreq: idx=1 ... every 3s forever
// The host keeps retransmitting connect requests at the dead peer object while
// a returning joiner allocates a fresh one and stalls at t08=3 -- which is why
// rejoining hangs on an infinite spinner. Missed disconnect and failed rejoin
// are the same bug.
//
// This is the exact mirror of hjHostSpawnRemotes: the engine's own teardown
// exists and is registered next to the create callback, but the loop that
// would drive it belongs to a state an in-game host has already left. So call
// the invoker ourselves and let playerDeleteRemoteForSession do the real work
// -- deleting the weapon moby slots and player moby, nulling pNetPlayer,
// clearing the pointer-table slot, migrating abandoned object owners, and
// calling guberMobyHandlePlayerLeft. None of that is worth reimplementing.
//
// Staleness, not a disconnect event: +0xc34 (seq) advances once per received
// pad message, ~15/s. If it has not moved for HJ_REAP_FRAMES while the ring is
// drained, that client is gone.
// ---------------------------------------------------------------------------
#define HJ_NWP_SLOTS      (8)
#define HJ_NW_CID         (0x00)
#define HJ_NW_PDATA       (0x04)
#define HJ_NW_BLOCAL      (0x68)
#define HJ_NW_SPAWNED     (0x1a2)
#define HJ_NW_CBCALLED    (0x1a6)
#define HJ_NW_SEQ         (0xc34)
#define HJ_NW_BUFFERED    (0xc38)

// hjHostRefreshNames -- take the joiner's name from its own registration.
//
// tNW_Player carries the registering client's name at +0x1b0. Established by a
// scan of the host's entries: slot 1 held the name the joiner registered under
// while slot 0, the host's own, held nothing -- so the field is written from the
// received registration and never from the local roster.
//
// The registration can land before or after hjHostAdoptPeers claims the slot, so
// this runs every frame and copies whenever the roster disagrees, rather than once
// at adopt time. Guarded on a printable, NUL-terminated string so a slot that is
// not yet populated leaves the roster alone instead of writing garbage into it.
#define HJ_NW_NAME  (0x1b0)

void hjHostRefreshNames(void)
{
    GameSettings * gs;
    int i, me;

    if (isInMenus() || !isInGame() || !gameAmIHost())
        return;

    gs = gameGetSettings();
    if (!gs)
        return;
    me = gameGetMyClientId();

    for (i = 0; i < GAME_MAX_PLAYERS; ++i) {
        u32 nm = HJ_NWPLAYER_BASE + (i * HJ_NWPLAYER_STRIDE) + HJ_NW_NAME;
        int k, len = -1, differs = 0;

        if (i == me || gs->PlayerClients[i] < 0)
            continue;

        for (k = 0; k < 16; ++k) {
            unsigned char c = *(unsigned char*)(nm + k);
            if (c == 0) { len = k; break; }
            if (c < 0x20 || c > 0x7e) break;
        }
        if (len <= 0)                     // empty, unterminated, or non-printable
            continue;

        for (k = 0; k < 16; ++k)
            if (gs->PlayerNames[i][k] != *(char*)(nm + k)) { differs = 1; break; }
        if (!differs)
            continue;

        for (k = 0; k < 16; ++k)
            gs->PlayerNames[i][k] = (k < len) ? *(char*)(nm + k) : 0;

        HOTJOIN_LOG("name: roster slot %d -> '%s' (from nwp +0x%x)\n",
            i, gs->PlayerNames[i], HJ_NW_NAME);
    }
}

// Hotjoin: the joiner tells the host its name.
//
// CORRECTION to the previous reading of nwp+0x1b0. A second scan, on a build with
// the "Hotjoiner" placeholder removed, showed:
//
//     namescan: slot 0 ... nwp +0x1b0 'Luka77'      <- the HOST's own name
//     namescan: slot 1 ... no name at all           <- the joiner, roster correct
//
// The first scan had happened to catch slot 0 before its name was set, and that
// one empty reading was the whole basis for concluding the field is written from
// the network. It is not: +0x1b0 mirrors the local roster. It held 'Hotjoiner'
// only because we had put 'Hotjoiner' in the roster ourselves. With the roster
// entry blank it stays blank, so it can never be a SOURCE for a name the host does
// not already have. hjHostRefreshNames is kept -- it is correct and harmless, and
// it is what applies the name once something supplies one -- but it was never
// going to fix this on its own.
//
// The host has no local source for a joiner's name, so the joiner has to send it.
// This uses the existing client-to-client channel over the DME connection (the same
// one ping.c and the flag-pickup request use), not a new protocol.
//
// The joiner's own name is correct in its roster because DME injects it into the
// snapshot (section 67), but the host's blank name can propagate back over the
// host's settings broadcast -- so latch the first non-empty name seen and keep
// sending that, rather than re-reading a field that may have been blanked.
#define CUSTOM_MSG_ID_HOTJOIN_NAME  (32)
#define HJ_NAME_SENDS               (30)   // ~30 s, once a second

typedef struct HjNameMsg {
    int  clientIdx;
    char name[16];
} HjNameMsg_t;

static char hjMyName[16];
static int  hjMyNameValid = 0;
static int  hjNameSends = 0;
static int  hjNameTick = 0;

int hjOnRemoteName(void * connection, void * data)
{
    HjNameMsg_t msg;
    GameSettings * gs;
    int k, len = -1;

    memcpy(&msg, data, sizeof(msg));

    gs = gameGetSettings();
    if (!gs || msg.clientIdx < 0 || msg.clientIdx >= GAME_MAX_PLAYERS)
        return sizeof(HjNameMsg_t);

    // Validate before writing into the roster: printable and NUL-terminated.
    for (k = 0; k < 16; ++k) {
        unsigned char c = (unsigned char)msg.name[k];
        if (c == 0) { len = k; break; }
        if (c < 0x20 || c > 0x7e) break;
    }
    if (len <= 0)
        return sizeof(HjNameMsg_t);

    for (k = 0; k < 16; ++k)
        if (gs->PlayerNames[msg.clientIdx][k] != msg.name[k]) break;
    if (k == 16)
        return sizeof(HjNameMsg_t);      // already correct

    for (k = 0; k < 16; ++k)
        gs->PlayerNames[msg.clientIdx][k] = (k < len) ? msg.name[k] : 0;

    HOTJOIN_LOG("name: slot %d -> '%s' (from client %d)\n",
        msg.clientIdx, gs->PlayerNames[msg.clientIdx], msg.clientIdx);
    return sizeof(HjNameMsg_t);
}

void hjSendMyName(void)
{
    GameSettings * gs;
    void * conn;
    HjNameMsg_t msg;
    int me, k;

    // Latch in MENUS too, and never clear the latched name.
    //
    // The first cut only looked once in game and cleared the latch on every menu
    // transition, which can deadlock: the host starts with a blank name for the
    // joiner, its settings broadcast blanks the joiner's own slot, the joiner then
    // has nothing to latch, so it never tells the host and both stay blank for the
    // whole match. Measured: "name: cannot latch -- me=1 bytes 00 00 00 00" on a run
    // where DME had injected "Gtr4" correctly (server log confirms it for that very
    // join). It worked the other times only because the joiner happened to look
    // before the host's broadcast landed -- a race, not a design.
    //
    // Staging is where the injected snapshot is freshest, so look there as well. An
    // account name does not change within a boot, so once latched it stays.
    gs = gameGetSettings();
    if (!gs)
        return;

    // Resolve our roster slot properly rather than indexing by client id: the two
    // coincide for a hotjoiner today, but patchStaging already searches for it and
    // this should not quietly depend on them staying equal.
    {
        int cid = gameGetMyClientId();
        me = -1;
        for (k = 0; k < GAME_MAX_PLAYERS; ++k)
            if (gs->PlayerClients[k] == cid) { me = k; break; }
    }
    if (me < 0)
        return;

    // Latch the name the first time it reads as something real.
    if (!hjMyNameValid) {
        unsigned char c = (unsigned char)gs->PlayerNames[me][0];
        if (c < 0x20 || c > 0x7e) {
            // Say so, once. The previous build produced no name traffic at all and
            // no log line either, which left three candidate causes (not called,
            // wrong slot, empty name) indistinguishable. Never guess which gate
            // closed when one line can name it.
            static int moaned = 0;
            if (!moaned) {
                moaned = 1;
                HOTJOIN_LOG("name: cannot latch -- me=%d bytes %02x %02x %02x %02x\n",
                    me, (unsigned char)gs->PlayerNames[me][0],
                    (unsigned char)gs->PlayerNames[me][1],
                    (unsigned char)gs->PlayerNames[me][2],
                    (unsigned char)gs->PlayerNames[me][3]);
            }
            return;
        }
        for (k = 0; k < 16; ++k)
            hjMyName[k] = gs->PlayerNames[me][k];
        hjMyNameValid = 1;
        HOTJOIN_LOG("name: latched my own name '%s' (slot %d)\n", hjMyName, me);
    }

    // Rearm the send budget on the way back to menus -- but NOT the latched name,
    // which is the whole point of the change above. Without this a second match in
    // one boot would find the budget spent and never announce.
    if (isInMenus()) {
        hjNameSends = 0;
        hjNameTick = 0;
        return;
    }

    // Sending is still in-game, joiner-only, and budgeted.
    if (!isInGame() || gameAmIHost() || hjNameSends >= HJ_NAME_SENDS)
        return;

    if (++hjNameTick < 60)
        return;
    hjNameTick = 0;

    conn = netGetDmeServerConnection();
    if (!conn)
        return;

    msg.clientIdx = me;
    for (k = 0; k < 16; ++k)
        msg.name[k] = hjMyName[k];

    // Repeat rather than send once: the host may not have adopted the slot yet, and
    // a single lost message would leave the name blank for the whole match.
    netSendCustomAppMessage(conn, gameGetHostId(), CUSTOM_MSG_ID_HOTJOIN_NAME,
        sizeof(msg), &msg);
    ++hjNameSends;
}

void hjInstallNameHandler(void)
{
    // Every frame, NOT once. netInstallCustomMsgHandler also (re)installs the hook
    // into DME_CALLBACK_TABLE and the Medius app-handler jump, and those live in
    // game memory that is rewritten across a level load -- which is why ping.c calls
    // this from its per-frame update too. Installing once at boot registered the
    // handler into a table that was later replaced: the joiner latched and sent its
    // name every second (log: "latched my own name 'Gtr4' (slot 1)") and the host
    // never dispatched a single one.
    netInstallCustomMsgHandler(CUSTOM_MSG_ID_HOTJOIN_NAME, &hjOnRemoteName);
}

// hjFindRemoteName -- where the joiner's account name lives on the host.
//
// The host writes the literal "Hotjoiner" into its roster slot when it adopts a
// peer, because when that code was written nothing on the host was known to carry
// the real name. That placeholder then propagates: the host's periodic settings
// broadcast is NOT the single-target path DME injects into, so the joiner receives
// "Hotjoiner" back and displays it over the correct name the server had already
// injected into its first snapshot.
//
// Fixing it server-side alone cannot work for the host's own screen -- the host
// never receives its own roster back -- so the host has to learn the name. It now
// DOES receive the joiner's tNW_Player registration (server trace: "broadcast to 1
// of 2 00-04 (236 bytes) from 1"), and 236 bytes is roomy enough to carry a name.
// No tNW_Player struct definition exists in the decomp or in libuya, so this finds
// the offset empirically rather than guessing: one scan per slot for printable
// ASCII runs, in the tNW_Player entry and in the tNW_PlayerData it points at. Once
// the offset is known this is replaced by a direct read.
static u32 hjNameScanned = 0;

static void hjScanAscii(const char * what, u32 base, int len)
{
    int i = 0;
    int hits = 0;

    while (i < len && hits < 8) {
        int j = i;
        while (j < len) {
            unsigned char c = *(unsigned char*)(base + j);
            if (c < 0x20 || c > 0x7e) break;
            ++j;
        }
        if (j - i >= 4) {
            char buf[33];
            int k, n = (j - i) > 32 ? 32 : (j - i);
            for (k = 0; k < n; ++k) buf[k] = *(char*)(base + i + k);
            buf[n] = 0;
            HOTJOIN_LOG("namescan: %s +0x%03x '%s'\n", what, i, buf);
            ++hits;
        }
        i = (j > i) ? j : (i + 1);
    }
}

void hjFindRemoteName(void)
{
    int i;

    if (isInMenus()) { hjNameScanned = 0; return; }
    if (!isInGame() || !gameAmIHost())
        return;

    for (i = 0; i < GAME_MAX_PLAYERS; ++i) {
        u32 nwp = HJ_NWPLAYER_BASE + (i * HJ_NWPLAYER_STRIDE);
        u32 pData;

        if (hjNameScanned & (1 << i))            continue;
        if (*(int*)(nwp + HJ_NW_CID) < 0)        continue;
        pData = *(u32*)(nwp + HJ_NW_PDATA);
        if (!pData)                              continue;

        hjNameScanned |= (1 << i);
        HOTJOIN_LOG("namescan: slot %d nwp=%08x pData=%08x\n", i, nwp, pData);
        // The entry is a known 0xC70 stride so scanning it is safe; stop short of the
        // pad ring at 0xC30. pData is a heap object of unknown size -- 0x100 is the
        // same window the settings blob uses, so do not widen it without evidence.
        hjScanAscii("nwp", nwp, 0xC00);
        hjScanAscii("pdata", pData, 0x100);
    }
}

// hjDumpWeaponMask -- is a hot-joined remote stuck on the default loadout?
//
// playerSyncRemoteWeaponInventory (Metropolis 0x005292c0) runs every remote frame
// and applies the inventory from
//
//     *(u16*)( *(u32*)( *(u32*)(player + 0x2558) + 4 ) + 0x80 )
//
// player+0x2558 is pNetPlayer, +4 is pNetPlayerData -- the same pData this file
// already tracks -- so the mask is a u16 at pData+0x80. The function itself is
// obfuscated (vaPlayerObfuscateWeaponAddr), but its INPUT is not, and the input is
// what tells us whether the inventory is wrong or merely applied late.
//
// The theory, which the N60 observation motivates: a remote is constructed with the
// default loadout, and the real inventory only arrives on a weapon-change event the
// joiner was not present for. That predicts the host reads a default-looking mask
// for the joiner (N60 = the default index, so the low bit set and little else)
// while the joiner reads its true mask for itself, and the two converge only when
// the owner switches weapons. Both machines log this, so the two views can be
// compared directly on one timeline.
//
// If instead the mask is correct on both sides all along, the inventory is not the
// problem and the delay is in applying it -- which would send this back to the
// obfuscated consumer.
#define HJ_PDATA_WEAPONMASK  (0x80)

static u32 hjWmLastSig = 0;
static int hjWmSamples = 0;

void hjDumpWeaponMask(void)
{
    u32 sig = 0;
    int i;

    if (isInMenus() || !isInGame()) { hjWmLastSig = 0; hjWmSamples = 0; return; }
    if (hjWmSamples >= 200)
        return;

    for (i = 0; i < GAME_MAX_PLAYERS; ++i) {
        u32 nwp = HJ_NWPLAYER_BASE + (i * HJ_NWPLAYER_STRIDE);
        u32 pd  = *(u32*)(nwp + HJ_NW_PDATA);
        if (*(int*)(nwp + HJ_NW_CID) < 0 || !pd)
            continue;
        sig = (sig * 31) + (u32)*(unsigned short*)(pd + HJ_PDATA_WEAPONMASK)
            + (u32)(i << 24);
    }
    if (sig == hjWmLastSig)          // edge-triggered: a stuck mask prints once
        return;
    hjWmLastSig = sig;
    ++hjWmSamples;

    for (i = 0; i < GAME_MAX_PLAYERS; ++i) {
        u32 nwp = HJ_NWPLAYER_BASE + (i * HJ_NWPLAYER_STRIDE);
        u32 pd  = *(u32*)(nwp + HJ_NW_PDATA);
        int cid = *(int*)(nwp + HJ_NW_CID);
        if (cid < 0 || !pd)
            continue;
        HOTJOIN_LOG("wmask: [%d] cid=%d local=%d pData=%08x mask=%04x\n",
            i, cid, (int)*(char*)(nwp + HJ_NW_BLOCAL), pd,
            (int)*(unsigned short*)(pd + HJ_PDATA_WEAPONMASK));
    }
}

// hjDumpWeaponSlots -- the per-player weapon mobys.
//
// pData+0x80 was NOT the per-player inventory. Measured on both machines with a
// 3-weapon match (blitz, flux, N60): mask=c80e on the host AND the joiner, and
// identical for every player, converging from 0000 within ~0.6 s on the joiner and
// ~3 s on the host on every rejoin, with no progressive widening. That is the
// match weapon SET, not what a player is holding. The read chain in section 74 was
// right and the interpretation was wrong.
//
// The per-player state is one level down. playerDeleteWeaponMobySlots walks SIX
// slots at stride 0x50 in the Player struct, and playerUpdateWeaponMobySlotRemote
// drives a slot from the remote pad buttons:
//
//     if (padCtx->0x1a0 & *(u32*)(&player->field_0x460 + slot*0x50))
//         (&player->field_0x458)[slot*0x50] = 1;
//
// so per slot: +0x450 weapon moby, +0x454 a second moby, +0x458 the active flag,
// +0x460 the button mask that fires it. A remote that cannot shoot but whose pad
// stream is healthy (section 72) and whose weapon set is correct (above) would look
// exactly like a slot whose moby is NULL or whose mask is 0.
//
// The N60 evidence predicts one populated slot and the rest empty until something
// seeds them. 0x450 is inferred from the 0x454/0x458/0x460 cluster and the 0x50
// stride, not confirmed -- if it prints nonsense, that is the field to doubt first.
#define HJ_WS_MOBY    (0x450)
#define HJ_WS_MOBY2   (0x454)
#define HJ_WS_ACTIVE  (0x458)
#define HJ_WS_MASK    (0x460)
#define HJ_WS_STRIDE  (0x50)
#define HJ_WS_SLOTS   (6)

static u32 hjWsLastSig = 0;
static int hjWsSamples = 0;

void hjDumpWeaponSlots(void)
{
    Player ** all;
    u32 sig = 0;
    int i, k;

    if (isInMenus() || !isInGame()) { hjWsLastSig = 0; hjWsSamples = 0; return; }
    if (hjWsSamples >= 200)
        return;

    all = playerGetAll();
    if (!all)
        return;

    for (i = 0; i < GAME_MAX_PLAYERS; ++i) {
        if (!all[i]) continue;
        for (k = 0; k < HJ_WS_SLOTS; ++k) {
            u32 b = (u32)all[i] + (k * HJ_WS_STRIDE);
            sig = (sig * 31) + (*(u32*)(b + HJ_WS_MOBY) ? 1u : 0u)
                + ((u32)*(unsigned char*)(b + HJ_WS_ACTIVE) << 1)
                + (*(u32*)(b + HJ_WS_MASK) ? 4u : 0u);
        }
    }
    if (sig == hjWsLastSig)
        return;
    hjWsLastSig = sig;
    ++hjWsSamples;

    for (i = 0; i < GAME_MAX_PLAYERS; ++i) {
        if (!all[i]) continue;
        HOTJOIN_LOG("wslot: [%d] p=%08x moby=%08x %08x %08x %08x %08x %08x\n",
            i, (u32)all[i],
            *(u32*)((u32)all[i] + 0*HJ_WS_STRIDE + HJ_WS_MOBY),
            *(u32*)((u32)all[i] + 1*HJ_WS_STRIDE + HJ_WS_MOBY),
            *(u32*)((u32)all[i] + 2*HJ_WS_STRIDE + HJ_WS_MOBY),
            *(u32*)((u32)all[i] + 3*HJ_WS_STRIDE + HJ_WS_MOBY),
            *(u32*)((u32)all[i] + 4*HJ_WS_STRIDE + HJ_WS_MOBY),
            *(u32*)((u32)all[i] + 5*HJ_WS_STRIDE + HJ_WS_MOBY));
        HOTJOIN_LOG("wslot: [%d] act=%d%d%d%d%d%d mask=%08x %08x %08x %08x %08x %08x\n",
            i,
            (int)*(unsigned char*)((u32)all[i] + 0*HJ_WS_STRIDE + HJ_WS_ACTIVE),
            (int)*(unsigned char*)((u32)all[i] + 1*HJ_WS_STRIDE + HJ_WS_ACTIVE),
            (int)*(unsigned char*)((u32)all[i] + 2*HJ_WS_STRIDE + HJ_WS_ACTIVE),
            (int)*(unsigned char*)((u32)all[i] + 3*HJ_WS_STRIDE + HJ_WS_ACTIVE),
            (int)*(unsigned char*)((u32)all[i] + 4*HJ_WS_STRIDE + HJ_WS_ACTIVE),
            (int)*(unsigned char*)((u32)all[i] + 5*HJ_WS_STRIDE + HJ_WS_ACTIVE),
            *(u32*)((u32)all[i] + 0*HJ_WS_STRIDE + HJ_WS_MASK),
            *(u32*)((u32)all[i] + 1*HJ_WS_STRIDE + HJ_WS_MASK),
            *(u32*)((u32)all[i] + 2*HJ_WS_STRIDE + HJ_WS_MASK),
            *(u32*)((u32)all[i] + 3*HJ_WS_STRIDE + HJ_WS_MASK),
            *(u32*)((u32)all[i] + 4*HJ_WS_STRIDE + HJ_WS_MASK),
            *(u32*)((u32)all[i] + 5*HJ_WS_STRIDE + HJ_WS_MASK));
    }
}

// hjDumpPadRing -- why a hot-joiner sees the host's actions late.
//
// Remote players replay a jitter-buffered pad stream. Ghidra names the fields on
// tNW_Player, and the base exe's ring advance is 0x0019b5b8, reached only from the
// tail of playerConsumeRemoteStatePacket (overlay 0x005284b8):
//
//   activePadFrame++;  if (activePadFrame == 4) { advance(pNetPlayer); ... }
//
// so one ring entry is retired per 4 remote frames -- 15/s, matching the sender.
// The advance pops one entry, and pops a SECOND when the catch-up flag (+0xc40) is
// set. That flag has hysteresis around jitterThrottleFrames * 0.25:
//
//   set   when buffered > thr*0.25 + 4
//   clear when buffered < thr*0.25 + 3
//
// With thr=2 that is a steady state of 3-4 entries, which is exactly where a settled
// stream sits in the logs. But right after a hot-join the joiner's buffer climbs to
// 15-16 -- about a second of lag at 15/s, which is the reported late-shot symptom --
// and takes the better part of a minute to come down. With catch-up engaged it should
// drain 15 entries/s, i.e. in well under a second, so something is stopping the
// advance from running at all.
//
// The prime suspect is the gate at the TOP of the consumer, which returns before
// activePadFrame is ever incremented:
//
//   if (pActivePadMsg == NULL ||
//       (numConsecutiveSkips != 0 && now - lastPadMsgReceiveTick < jitterThrottleFrames))
//       return;
//
// numConsecutiveSkips is incremented by the enqueue path (0x0019b544) every time two
// pad messages land less than 600 ticks apart, and reset when they do not. A joiner
// coming out of a level load receives its backlog as a burst, which is precisely the
// condition that runs that counter up.
//
// This probe does not fix anything. It samples the whole tuple once a second so the
// next capture says which term is actually stuck -- guessing between "catch-up never
// engages", "the consumer is never called", and "the ring is simply full" would mean
// patching a jitter buffer blind.
#define HJ_PR_DECODEPOS   (0xc30)
#define HJ_PR_ACTIVEFRAME (0xc31)
#define HJ_PR_BUFFERED    (0xc38)
#define HJ_PR_LASTTICK    (0xc3c)
#define HJ_PR_CATCHUP     (0xc40)
#define HJ_PR_THROTTLE    (0xc41)
#define HJ_PR_SKIPS       (0xc42)
#define HJ_PR_ACTIVEMSG   (0xc44)
#define HJ_NET_TICK       (0x002412ac)

static int hjPrTick = 0;
static int hjPrSamples = 0;
static u32 hjPrLastSig = 0;

void hjDumpPadRing(void)
{
    int i;

    if (isInMenus() || !isInGame()) {
        hjPrTick = 0; hjPrSamples = 0; hjPrLastSig = 0;
        return;
    }
    if (++hjPrTick < 60)          // 1 Hz -- per-frame probes perturb join timing
        return;
    hjPrTick = 0;
    if (hjPrSamples >= 120)       // ~2 minutes, then stop logging entirely
        return;

    // Only speak when something moved. A first cut logged two lines a second for
    // the whole join regardless, and the run that produced was a hard failure --
    // the joiner never exchanged a pad packet at all. That failure is not
    // attributable to this probe (it only reads), but log volume during a join has
    // cost us before, so the steady state here is silence.
    {
        u32 sig = 0;
        for (i = 0; i < GAME_MAX_PLAYERS; ++i) {
            u32 n = HJ_NWPLAYER_BASE + (i * HJ_NWPLAYER_STRIDE);
            sig = (sig * 31) + (u32)*(int*)(n + HJ_PR_BUFFERED)
                + (u32)*(unsigned char*)(n + HJ_PR_CATCHUP)
                + (u32)*(unsigned char*)(n + HJ_PR_SKIPS)
                + (u32)*(signed char*)(n + HJ_PR_THROTTLE);
        }
        if (sig == hjPrLastSig)
            return;
        hjPrLastSig = sig;
    }
    ++hjPrSamples;

    for (i = 0; i < GAME_MAX_PLAYERS; ++i) {
        u32 nwp = HJ_NWPLAYER_BASE + (i * HJ_NWPLAYER_STRIDE);
        int cid = *(int*)(nwp + HJ_NW_CID);
        int buffered, thr, skips, catchup, lastTick, now, gate;

        // Only remote slots have a ring; a local one never buffers.
        if (cid < 0 || *(u32*)(nwp + HJ_NW_PDATA) == 0 || *(char*)(nwp + HJ_NW_BLOCAL))
            continue;

        buffered = *(int*)(nwp + HJ_PR_BUFFERED);
        thr      = (int)*(signed char*)(nwp + HJ_PR_THROTTLE);
        skips    = (int)*(unsigned char*)(nwp + HJ_PR_SKIPS);
        catchup  = (int)*(unsigned char*)(nwp + HJ_PR_CATCHUP);
        lastTick = *(int*)(nwp + HJ_PR_LASTTICK);
        now      = *(int*)HJ_NET_TICK;

        // The consumer's own gate, evaluated the way the overlay evaluates it.
        gate = (*(u32*)(nwp + HJ_PR_ACTIVEMSG) != 0)
            && (skips == 0 || (now - lastTick) >= thr);

        HOTJOIN_LOG("padring: [%d] cid=%d buffered=%d frame=%d catchup=%d thr=%d "
            "skips=%d dTick=%d gate=%d msg=%08x\n",
            i, cid, buffered,
            (int)*(unsigned char*)(nwp + HJ_PR_ACTIVEFRAME),
            catchup, thr, skips, now - lastTick, gate,
            *(u32*)(nwp + HJ_PR_ACTIVEMSG));
    }
}

// 8 seconds at 60fps. A pad stream runs at ~15/s, so this is ~120 missed
// messages -- far beyond any lag spike, but still well inside the window
// before a returning player tries to rejoin.
#define HJ_REAP_FRAMES    (480)

extern int hjAdopted;

void hjHostReapRemotes(void)
{
    GameSettings * gs = gameGetSettings();
    static int lastSeq[HJ_NWP_SLOTS];
    static int stallFrames[HJ_NWP_SLOTS];
    static int init = 0;
    int i;

    if (!init) {
        init = 1;
        for (i = 0; i < HJ_NWP_SLOTS; ++i) { lastSeq[i] = 0; stallFrames[i] = 0; }
    }

    // Host only, and only while actually in a game -- the teardown window on
    // the way out looks identical by state and must not be touched.
    if (!gameAmIHost() || !isInGame() || isInMenus())
        return;

    for (i = 0; i < HJ_NWP_SLOTS; ++i) {
        u32 nwp = HJ_NWPLAYER_BASE + (i * HJ_NWPLAYER_STRIDE);
        int cid      = *(int*)(nwp + HJ_NW_CID);
        u32 pData    = *(u32*)(nwp + HJ_NW_PDATA);
        int bLocal   = (int)*(char*)(nwp + HJ_NW_BLOCAL);
        int spawned  = (int)*(short*)(nwp + HJ_NW_SPAWNED);
        int cbCalled = (int)*(short*)(nwp + HJ_NW_CBCALLED);
        int seq      = *(int*)(nwp + HJ_NW_SEQ);
        int buffered = *(int*)(nwp + HJ_NW_BUFFERED);

        // Only a live, remote, fully-admitted player is a candidate. The
        // invoker refuses to wipe our own entry anyway (0x00199a80 compares
        // against our client index), but do not even ask.
        if (cid < 0 || !pData || bLocal || !spawned || !cbCalled
            || cid == gameGetMyClientId()) {
            lastSeq[i] = seq;
            stallFrames[i] = 0;
            continue;
        }

        // seq == 0 means this client has never sent a pad message: it is still
        // arriving, not leaving. Reaping there would kill a joiner mid-join.
        if (seq == 0 || seq != lastSeq[i] || buffered > 0) {
            lastSeq[i] = seq;
            stallFrames[i] = 0;
            continue;
        }

        if (++stallFrames[i] < HJ_REAP_FRAMES)
            continue;

        HOTJOIN_LOG("reap: nwp[%d] %08x cid=%d seq=%d stalled %d frames -> deleting\n",
            i, nwp, cid, seq, stallFrames[i]);

        // Does the vanilla teardown have anything to match on?
        //
        // playerDeleteRemoteForSession (Metropolis 0x0052aba0) is ONE guarded block:
        // it walks the player array for a Player whose pNetPlayer (+0x2558) equals
        // the tNW_Player being deleted, and only inside that match does it queue the
        // "%s has left the game." message AND free the weapon moby slots, delete the
        // player moby, clear the array slot, migrate abandoned object owners and call
        // guberMobyHandlePlayerLeft. No match means none of it runs.
        //
        // The message has never been seen in a non-vanilla join. The per-index byte
        // at 0x001a6625 suppresses only the MESSAGE (not the cleanup) once it reads
        // 2, and this function is the only known writer of it -- so on a fresh boot
        // the first leave should emit. That points at "no match", i.e. the whole
        // teardown being skipped, which would explain weapon state degrading across
        // successive rejoins. But "only known writer" is an assumption, so log the
        // byte as well as the match rather than trusting the deduction.
        {
            Player ** all = playerGetAll();
            int k, matched = -1;

            if (all) {
                for (k = 0; k < GAME_MAX_PLAYERS; ++k) {
                    if (!all[k])
                        continue;
                    if (*(u32*)((u32)all[k] + 0x2558) == nwp)
                        matched = k;
                    HOTJOIN_LOG("reap: player[%d]=%08x pNetPlayer=%08x f1a14=%d msgflag=%d\n",
                        k, (u32)all[k], *(u32*)((u32)all[k] + 0x2558),
                        (int)*(char*)((u32)all[k] + 0x1a14),
                        (int)*(unsigned char*)(0x001a6625 + k));
                }
            }
            HOTJOIN_LOG("reap: nwp=%08x match=%d (-1 means the vanilla teardown will "
                "find nothing and skip every step)\n", nwp, matched);
        }

        internal_hjDeleteRemotePlayer((void*)nwp);
        HOTJOIN_LOG("reap: nwp[%d] after: cid=%d spawned=%d cbCalled=%d\n",
            i, *(int*)(nwp + HJ_NW_CID),
            (int)*(short*)(nwp + HJ_NW_SPAWNED),
            (int)*(short*)(nwp + HJ_NW_CBCALLED));

        // playerDeleteRemoteForSession clears the ENGINE state -- Player, moby,
        // pointer-table slot -- but knows nothing about the Horizon roster slot,
        // because we wrote that ourselves in hjHostAdoptPeers. Measured: after a
        // successful reap the host still reported
        //     roster: clients=0 1  states=8 8  n=2
        //     plist: [1] NULL
        // and a returning joiner's introduce stalled at "state 3 -> 3" forever.
        // The host saw client 1 already present at state 8 (fully joined), so it
        // never ran the admit sequence. Undo the adopt as well, and clear the
        // write-once bit so a rejoin can be adopted again -- hjAdopted is only
        // rearmed in menus, and an in-game host never goes there.
        if (gs && cid >= 0 && cid < GAME_MAX_PLAYERS) {
            int k, n = 0;
            // Release our own per-slot latch too. Without this the slot is reaped and
            // re-adopted correctly but hjHostSpawnRemotes still skips it forever on
            // `hjSpawned & (1 << i)`, so the rejoining player is never reconstructed --
            // measured as reap -> adopt -> nothing, with plist[1] NULL for the rest of
            // the match.
            hjSpawned &= ~(1 << cid);
            gs->PlayerClients[cid] = -1;
            gs->PlayerStates[cid]  = 0;
            gs->PlayerTeams[cid]   = -1;
            gs->PlayerSkins[cid]   = 0;
            gs->PlayerTypes[cid]   = 0;
            for (k = 0; k < 16; ++k)
                gs->PlayerNames[cid][k] = 0;
            for (k = 0; k < GAME_MAX_PLAYERS; ++k)
                if (gs->PlayerClients[k] >= 0)
                    ++n;
            gs->PlayerCount = n;
            hjAdopted &= ~(1 << cid);
            // Rearm, but blocked until this slot sees fresh pad traffic.
            hjReapBlocked |= (1 << cid);
            hjReapBlockFrames[cid] = 0;
            hjSpawnBlocked |= (1 << cid);
            hjSpawnSeq[cid] = seq;

            // Release the slot's stale registration.
            //
            // 0x00199A40 clears netClientIndex but deliberately LEAVES
            // pNetPlayerData. Measured across a rejoin: nwp[1] keeps cid=-1 and the
            // identical pData (01f7b8c0, the first life's pointer) for the whole
            // session, and its pad sequence never advances again -- so nothing ever
            // re-initialises the slot for the returning client, and the only reason
            // earlier builds showed a player at all is that they spawned from that
            // dead pointer (section 79, which froze the host).
            //
            // Leaving the pointer is right for vanilla, where the slot belongs to a
            // session that is going away with it. It is wrong for reuse. Clearing it
            // is what lets the registration path treat a returning client as new.
            // Only the SLOT's reference is cleared -- the object itself is owned by
            // the net layer and is not freed here.
            HOTJOIN_LOG("reap: clearing nwp[%d] pData=%08x seq=%d for re-registration\n",
                cid, *(u32*)(nwp + HJ_NW_PDATA), *(int*)(nwp + HJ_NW_SEQ));
            *(u32*)(nwp + HJ_NW_PDATA) = 0;
            *(int*)(nwp + HJ_NW_SEQ) = 0;
            hjSpawnSeq[cid] = 0;
            HOTJOIN_LOG("reap: roster slot %d cleared, n -> %d, adopt rearmed "
                "(blocked until the stale peer record clears; seq was %d)\n",
                cid, gs->PlayerCount);
        }

        stallFrames[i] = 0;
        lastSeq[i] = 0;
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

void hjHostSpawnRemotes(void)
{
    Player ** all;
    GameSettings * gs;
    int i, me;

    if (isInMenus()) { hjSpawned = 0; return; }
    if (!gameAmIHost() || !isInGame())
        return;

    all = playerGetAll();
    if (!all)
        return;

    gs = gameGetSettings();
    me = gameGetMyClientId();
    for (i = 0; i < GAME_MAX_PLAYERS; ++i) {
        u32 nwp = HJ_NWPLAYER_BASE + (i * HJ_NWPLAYER_STRIDE);
        if (i == me)                       continue;   // never the local player
        if (hjSpawned & (1 << i))          continue;
        if (all[i])                        continue;   // already has a Player

        // REJOIN REPAIR. The delete invoker 0x199A40 clears netClientIndex to -1 but
        // deliberately leaves pNetPlayerData (+0x04) intact, so after a reap the slot
        // reads cid=-1 with pData still populated. On a reconnect the engine does not
        // put the index back -- measured with the joiner re-broadcasting its 00-04 on
        // every connect and the host still showing
        //     nwp[1] cid=-1 pData=01f7c1f0 spawned=0  seq=186 rcvFrame=5532 thr=2
        // i.e. the joiner's pad data arriving and being buffered into a slot whose
        // identity is missing, with plist[1] NULL and the host unable to see the player.
        //
        // The roster is the authority here and it is already correct (clients=0 1,
        // written by hjHostAdoptPeers from a peer at state 5). So when the roster claims
        // this slot and the data pointer is live, put the index back and let the vanilla
        // invoker below do the real work. This is the same shape as the roster adopt,
        // one level down.
        // Same caveat as the spawn gate below: after a reap the pData here is the
        // previous life's, so do not repair the index until the stream proves a new
        // one exists.
        if (*(int*)(nwp + 0x00) < 0 && *(u32*)(nwp + 0x04) != 0
            && !(hjSpawnBlocked & (1 << i))
            && gs && gs->PlayerClients[i] == i) {
            *(int*)(nwp + 0x00) = i;
            // bSpawned too. 0x199A40 clears +0x1a2 on delete and 0x1999B8 sets only
            // +0x1a6 (bCallbackCalled), so a repaired slot would sit at spawned=0
            // forever -- and hjHostReapRemotes skips any slot with !spawned, resetting
            // its stall counter every frame. Measured: the first leave reaped correctly,
            // the second never did, and nwp[1] sat at seq=213 unchanged for 90 s with
            // the departed player still in the world. The reused Player object then
            // appears to teleport when the next joiner takes the slot.
            *(short*)(nwp + HJ_NW_SPAWNED) = 1;
            HOTJOIN_LOG("respawn: nwp[%d] cid -1 -> %d, spawned -> 1 (pData=%08x)\n",
                i, i, *(u32*)(nwp + 0x04));
        }

        if (*(int*)(nwp + 0x00) < 0)       continue;   // no client in this slot
        if (*(short*)(nwp + 0x1a6) != 0)   continue;   // callback already ran
        if (*(u32*)(nwp + 0x04) == 0)      continue;   // no tNW_PlayerData

        // ...but a non-NULL pData is NOT proof of a live registration on a REJOIN.
        // 0x00199A40 deliberately leaves pNetPlayerData intact when it deletes, so
        // after a reap this gate is already satisfied by the previous life's
        // pointer and the spawn fires the instant the slot is re-adopted. Measured:
        //     first join   adopt 74.55 -> spawn 82.99   (8.4 s, pData really arrives)
        //     rejoin       adopt 111.1774 -> spawn 111.1824  (5 ms, stale pData)
        //     and the pad seq read 147 at BOTH reaps -- it never advanced, so the
        //     second life never streamed anything at all.
        // Building a remote player out of that is what froze the host.
        //
        // The honest signal that a new life exists is the pad sequence moving off
        // what it held at reap time. Unlike the adopt gate of section 78 this does
        // NOT deadlock: adoption still happens, the roster still reaches the joiner,
        // and the joiner streams as soon as it is in game -- which is exactly the
        // 8 s the first join takes anyway.
        if (hjSpawnBlocked & (1 << i)) {
            if (*(int*)(nwp + HJ_NW_SEQ) == hjSpawnSeq[i])
                continue;
            hjSpawnBlocked &= ~(1 << i);
            HOTJOIN_LOG("spawn: slot %d unblocked, seq moved %d -> %d\n",
                i, hjSpawnSeq[i], *(int*)(nwp + HJ_NW_SEQ));
        }


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

    // Names, on both machines. Three builds have now argued about who holds which
    // name without either side ever printing what it actually has -- the roster is
    // the thing both the display and the outgoing registration read from, so print
    // it. Copied into a terminated buffer first: PlayerNames entries are a fixed 16
    // bytes and are not guaranteed to contain a NUL.
    {
        char nb[GAME_MAX_PLAYERS][17];
        int k;
        for (i = 0; i < GAME_MAX_PLAYERS; ++i) {
            for (k = 0; k < 16; ++k) {
                unsigned char c = (unsigned char)gs->PlayerNames[i][k];
                nb[i][k] = (c >= 0x20 && c <= 0x7e) ? (char)c : (c ? '?' : 0);
                if (!c) break;
            }
            nb[i][16] = 0;
        }
        HOTJOIN_LOG("roster: names  ='%s' '%s' '%s' '%s'\n", nb[0], nb[1], nb[2], nb[3]);
    }
}

static int hjPeerWasInMenus = 0;

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
    // EDGE-triggered, not level-triggered. Resetting hjLastPeerSig on every menus frame
    // defeated the dedup entirely for the joiner, which spends the whole join in menus:
    // one 13-second client capture came back with 6592 identical peer dumps and no room
    // for anything else. Per probe-perturbs-timing, that is not just noise -- it is a
    // per-frame cost on the machine whose timing we are measuring.
    {
        int inMenus = isInMenus();
        if (inMenus && !hjPeerWasInMenus) {
            hjPeerDumps = 0;
            hjLastPeerSig = 0;
        }
        hjPeerWasInMenus = inMenus;
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
    hjCloseLogged = 0;
    hjSessEndLogged = 0;
    hjLeaveLogged = 0;
    hjLeaveCallerLogged = 0;
    hjDestroyLogged = 0;
    hjSmRestoreLogged = 0;
    hjSmWatchLogged = 0;
    hjCcLogged = 0;
    hjLeaveActLogged = 0;
    hjBackoutLogged = 0;
    hjCbLogged = 0;
    hjRt12Logged = 0;
    hjEvLogged = 0;
    hjLatchLogged = 0;
    hjLatchWatchLogged = 0;
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
    hjInstallRt12Probe();
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

// ---------------------------------------------------------------------------
// Hotjoin: WHO TEARS THE JOINER DOWN.
//
// The joiner now reaches a state where everything looks right -- peers[0] and its own
// record both at 5, roster clients=0 1, states=7 0, nwp[0] created with cid=0 -- and
// then abandons the whole join ~30 ms later (nwp[0] cid 0 -> -1, then gs=0x0).
//
// The teardown runs through a sweep at 0x199d28: for each of the 8 tNW_Player slots
// (0x22F550, stride 0xC70) it checks `slot->0x1a4`, and if set decrements a gp-relative
// counter and calls the delete invoker at 0x199a40. The only thing that sets 0x1a4 is
// the routine at 0x199cb8: it resolves the session context via 0x16ed00, takes ctx->0x1C,
// reads sessionObj->0x54 as the slot index, and marks that slot. 0x199cb8 is not called
// by anything -- it is a callback, and the pointer lives at 0x001dd9b0.
//
// So swapping that pointer gives us the one thing we cannot infer: the return address of
// whatever in the netplay layer decided the host's session had ended. Fires at most once
// per attempt, off the hot path.
#define HJ_SESSEND_SLOT (0x001dd9b0)
#define HJ_SESSEND_ORIG (0x00199cb8)

void hjSessionEndHook(int idx, int msgId)
{
    u32 ra = (u32)__builtin_return_address(0);
    void (*orig)(int, int) = (void (*)(int, int))hjSessEndOrig;
    int i, marked = -1;

    orig(idx, msgId);

    // 0x199cb8 sets slot->0x1a4; the sweep clears it. Read it back before the sweep runs
    // to name the slot that was just condemned.
    for (i = 0; i < HJ_NWP_SLOTS; ++i) {
        u32 nwp = HJ_NWPLAYER_BASE + (i * HJ_NWPLAYER_STRIDE);
        if (*(short*)(nwp + 0x1a4) != 0) { marked = i; break; }
    }

    if (hjSessEndLogged < 8) {
        ++hjSessEndLogged;
        HOTJOIN_LOG("sessend: ra=%08x idx=%d msg=%d marked=%d menus=%d game=%d host=%d\n",
            ra, idx, msgId, marked, isInMenus(), isInGame(), gameAmIHost());
    }
}

// ---------------------------------------------------------------------------
// Hotjoin: WHO LEAVES THE SESSION.
//
// The sessend probe answered the previous question: ra=0016f360, which is the tail of
// 0x16f308 -- a two-argument dispatch through a table at 0x001dd9b0 indexed by a byte
// out of the message descriptor (0x16f020 maps a message id < 4096 to its descriptor).
// So 0x199cb8 is not a standalone callback, it is handler 0 of the MESSAGE-RETIRED
// table, and 0x199c40 (registerPlayerBit) is handler 0 of the parallel MESSAGE-RECEIVED
// table at 0x001dd970. Retiring that message deletes the player it created.
//
// Following it up: 0x16f378(msgId) retires one message and is called from five sites,
// one of which (0x16f734) is a loop over all 4096 message slots -- a bulk flush --
// reached only from 0x171f48. That call sits inside 0x171ee8, which broadcasts internal
// message 18 to every peer, flushes every message, then clears ctx->0xE8 (the peers
// pointer) and ctx->0x108/0x10C. That is LEAVE SESSION, and it explains everything the
// joiner does: its tNW_Players are deleted, gs goes NULL, and hjDumpPeers falls silent
// until the next connect because ctx->0xE8 is zero.
//
// 0x171ee8 lives at ctx+0x1C (0x001d883c), so one pointer swap names the caller that
// decided to leave. Nothing here is per-frame: it fires once per attempt.
#define HJ_LEAVE_SLOT (0x001d883c)
#define HJ_LEAVE_ORIG (0x00171ee8)

// The leave is ASYNCHRONOUS and it lands too late. Measured on the joiner:
//
//   967.8138  leavecall ra=006d0ee8 state=7 flag=0   <- leave REQUESTED (pre-join teardown)
//   967.8167  connect[1]                             <- new session starts 3 ms later
//   968.0353  roster clients=0 1                     <- new session healthy
//   968.0360  nwp[0] cid=0 spawned=1
//   968.0369  leave: ctx->0x1C fires                 <- the leave COMPLETES, 220 ms late
//   968.0468  nwp[0] cid=-1                          <- and takes the new session with it
//
// 0x195900 with flag == 0 does not leave immediately: it sends peer message 42, sets
// state 9, and registers 0x196088 as the completion callback (its address is written to
// sp+0x20 at 0x1959e4 for the 0x14b448 call -- which is why 0x196088 has no static
// callers anywhere in RAM). When that completes it sets state 10, and the next tick of
// 0x196128 runs the real leave. By then the joiner has connected, been given a roster,
// and built the host's tNW_Player. 0x171ee8 clears ctx->0xE8, so the peers block it
// destroys is the NEW one -- which is also why the next attempt finds peers[0] == NULL
// and p438 == 1 and spins forever.
//
// Suppress the leave when a live game object already exists on the joiner. Host-side and
// out-of-menus leaves are untouched, and the budget is rearmed in menus.
#define HJ_LEAVE_SUPPRESS_MAX (4)

int hjLeaveSessionHook(void * peers)
{
    u32 ra = (u32)__builtin_return_address(0);
    int (*orig)(void *) = (int (*)(void *))hjLeaveOrig;
    u32 ctx = *(u32*)HJ_NET_CTX_PTR;
    u32 live = ctx ? *(u32*)(ctx + HJ_CTX_PEERS) : 0;

    // Suppress ONLY a leave that has been overtaken by a new connect. hjNetLeaveGameHook
    // snapshots hjConnectCalls when the leave is REQUESTED; if a connect has happened
    // between the request and this completion, the session being torn down is not the one
    // the request was about, and running it would destroy the new one.
    //
    // The first version of this gated on `peers == ctx->0xE8` and on not being the host,
    // and that broke CREATING a game: the pre-create teardown has no connect after it, is
    // entirely legitimate, and matched the condition anyway -- so the old DME session was
    // never released and the next create bounced straight back out (Medius showed
    // CreateGameResponse MediusSuccess immediately followed by LeftGameWorld). A leave
    // with no intervening connect must always be allowed through.
    GameSettings * lgs = gameGetSettings();
    int stale = hjLeavePending && (hjConnectCalls != hjLeaveConnectSeq);
    hjLeavePending = 0;

    // Belt and braces after the create-a-game regression: also require the hot-join
    // signature -- we are not the host, and the roster we are looking at has its host
    // already at GAME_START (7) or beyond. A game you just created has neither.
    // DISABLED (section 48): the teardown is the probe completing by design. Kept as a
    // log line only; `stale` is still computed so the trace shows the ordering.
    if (0 && stale && !isInGame() && !gameAmIHost()
        && lgs && lgs->PlayerStates[0] >= 7
        && hjLeaveSuppressed < HJ_LEAVE_SUPPRESS_MAX) {
        ++hjLeaveSuppressed;
        // Arm the destructor skip. 0x1961c4 makes TWO calls, and suppressing only the
        // first is worse than suppressing neither -- see hjPeersDestroyHook.
        hjLeaveSkipDestroy = 1;
        hjSnapshotStateMachine();
        if (hjLeaveLogged < 8) {
            ++hjLeaveLogged;
            HOTJOIN_LOG("leave: SUPPRESSED (stale) ra=%08x peers=%08x live=%08x conn %d->%d gs=%p n=%d\n",
                ra, (u32)peers, live, hjLeaveConnectSeq, hjConnectCalls,
                (void*)lgs, hjLeaveSuppressed);
        }
        return 0;
    }

    hjLeaveSkipDestroy = 0;

    if (hjLeaveLogged < 8) {
        ++hjLeaveLogged;
        HOTJOIN_LOG("leave: ra=%08x peers=%08x live=%08x conn %d->%d stale=%d menus=%d game=%d host=%d gs=%p\n",
            ra, (u32)peers, live, hjLeaveConnectSeq, hjConnectCalls, stale,
            isInMenus(), isInGame(), gameAmIHost(), (void*)lgs);
    }

    return orig(peers);
}

// ---------------------------------------------------------------------------
// Hotjoin: WHICH menu path asks to leave.
//
// Traced from the leave downward, all in the base exe:
//   0x171ee8  ctx+0x1C   broadcast internal msg 18, flush all messages, ctx->0xE8 = 0
//   0x14b1b8             the locked wrapper around it; sole caller 0x1961c4
//   0x1961c4             inside a state machine on the struct at 0x001A5E50:
//                        state (+0x120, i.e. 0x001A5F70) == 10 -> leave, then state 5
//   0x195900             the entry point: if state >= 10 return; else if +0x170
//                        (0x001A5FC0) == 1 -> state 10 (leave NOW); else send peer
//                        message 42 via (*(0x1a1ce8))->0x28 = 0x1746e8, which itself
//                        sets +0x170 = 1, and go to state 9 (leave next pass).
//
// 0x195900 has exactly four callers and every one of them is in the MENU/STAGING
// overlay: 0x6aa2dc, 0x6adc54, 0x6d0ee0, 0x6d15b0. Two of them (0x6aa2b0, 0x6adc20)
// pre-set +0x170 = 1 so the leave happens on the first pass -- which matches the ~2
// frames we measured. So the joiner is not being disconnected; the staging screen is
// asking to leave.
//
// These are OVERLAY addresses, so: verify each site still reads `jal 0x195900` before
// writing, install only while in menus (when that module is certainly resident), and
// allow reinstallation if the module is reloaded. If the overlay is replaced our four
// words go with it, which is harmless -- the hook body lives in patch RAM.
#define HJ_LEAVE_CALL     (0x0c065640)   // jal 0x195900
#define HJ_LEAVE_SITE_A   (0x006aa2dc)
#define HJ_LEAVE_SITE_B   (0x006adc54)
#define HJ_LEAVE_SITE_C   (0x006d0ee0)
#define HJ_LEAVE_SITE_D   (0x006d15b0)

extern int internal_hjNetLeaveGame(void);   // 0x195900

int hjNetLeaveGameHook(void)
{
    u32 ra = (u32)__builtin_return_address(0);

    hjLeaveReqState = *(int*)(HJ_SM_BASE + HJ_SM_STATE);

    // NOTE: 0x195900 is the world CONNECT, not a teardown -- section 47 had this right
    // and a later build briefly forgot it. With the flag at 0x001A5FC0 set it jumps
    // straight to state 10 and returns WITHOUT connecting (0x195978 -> 0x195988), so
    // forcing that path here would skip the join entirely. The `leavecall` name is a
    // misnomer inherited from section 39; it is the connect request.
    //
    // Snapshot the connect counter at REQUEST time. 0x195900 with flag == 0 does not
    // leave here -- it queues an async completion that can land hundreds of ms later.
    hjLeavePending = 1;
    hjLeaveConnectSeq = hjConnectCalls;
    // And the state the manager was in BEFORE any of this. This is the value a stale
    // leave must be unwound to. The suppression-time snapshot is too late for that:
    // by then the completion callback has already written 10 ("leave on next tick"),
    // and restoring 10 wedged the manager in exactly the state we were avoiding --
    // measured as `smrestore: state 5 -> 10` followed by a client that sat in menus
    // forever with every object healthy and cid=1.

    if (hjLeaveCallerLogged < 8) {
        ++hjLeaveCallerLogged;
        HOTJOIN_LOG("leavecall: ra=%08x state=%d flag=%d f174=%d menus=%d game=%d\n",
            ra, *(int*)0x001A5F70, *(int*)0x001A5FC0, *(int*)0x001A5FC4,
            isInMenus(), isInGame());
    }

    return internal_hjNetLeaveGame();
}

void hjInstallLeaveCallerProbe(void)
{
    if (!isInMenus())
        return;

    // Re-arm if the overlay was reloaded: the sites read as `jal 0x195900` again only
    // when the original module is back.
    if (hjLeaveSitesHooked
        && *(u32*)HJ_LEAVE_SITE_A != HJ_LEAVE_CALL
        && *(u32*)HJ_LEAVE_SITE_B != HJ_LEAVE_CALL)
        return;

    if (*(u32*)HJ_LEAVE_SITE_A != HJ_LEAVE_CALL ||
        *(u32*)HJ_LEAVE_SITE_B != HJ_LEAVE_CALL ||
        *(u32*)HJ_LEAVE_SITE_C != HJ_LEAVE_CALL ||
        *(u32*)HJ_LEAVE_SITE_D != HJ_LEAVE_CALL) {
        if (!hjLeaveSitesHooked) {
            hjLeaveSitesHooked = 1;   // report once, then stop looking
            HOTJOIN_LOG("leavecall: sites read %08x/%08x/%08x/%08x, expected %08x -- NOT hooked\n",
                *(u32*)HJ_LEAVE_SITE_A, *(u32*)HJ_LEAVE_SITE_B,
                *(u32*)HJ_LEAVE_SITE_C, *(u32*)HJ_LEAVE_SITE_D, HJ_LEAVE_CALL);
        }
        return;
    }

    HOOK_JAL(HJ_LEAVE_SITE_A, &hjNetLeaveGameHook);
    HOOK_JAL(HJ_LEAVE_SITE_B, &hjNetLeaveGameHook);
    HOOK_JAL(HJ_LEAVE_SITE_C, &hjNetLeaveGameHook);
    HOOK_JAL(HJ_LEAVE_SITE_D, &hjNetLeaveGameHook);
    hjLeaveSitesHooked = 1;
    HOTJOIN_LOG("leavecall: hooked 4 menu sites\n");
}

// ---------------------------------------------------------------------------
// Hotjoin: the OTHER half of the teardown.
//
// 0x001961C4 performs a leave with TWO calls, not one:
//
//     0x1961c4  jal 0x14b1b8   -> lock; ctx->0x1C (= 0x171ee8); unlock
//                                 graceful: broadcast msg 18, retire all messages,
//                                 ctx->0xE8 = 0
//     0x1961cc  jal 0x14b218   -> lock; 0x14f2c8; unlock
//                                 DESTRUCTOR: memset all 256 peer records (40 bytes
//                                 each), peers->0x434 = -1, 0x408 = 256, 0x404 = 256,
//                                 0x400 = 0, 0x430 = 0, 0x420..0x42c = 0, 0x438 = 0,
//                                 then 0x14f870 frees the table
//     0x1961d4  state = 5
//
// Suppressing only the first was strictly worse than suppressing neither. Measured:
// the graceful half was skipped, the destructor ran anyway, and the joiner was left
// reading freed memory --
//     peers: me=256 gate=0 p408=256 mine=00000000 mine08=-1
//     peers[0] 0019dc88 t08=32859768 f00=0019dc80 ...   <- heap residue
// -- followed by a dead TCP connection and a network error on screen. GameSettings
// survived (gs stayed non-NULL, which is why the roster was still readable), so the
// graceful suppression itself worked; it was the unmatched destructor that corrupted
// the session.
//
// So: both halves are skipped together or neither is. hjLeaveSkipDestroy is set only by
// hjLeaveSessionHook when it actually suppresses, and cleared whenever it does not, so
// the destructor can never be skipped on its own.
#define HJ_DESTROY_CALL   (0x0c052c86)   // jal 0x14b218
#define HJ_DESTROY_SITE_A (0x001961cc)   // base exe, always resident
#define HJ_DESTROY_SITE_B (0x0095c054)   // second copy of the same sequence

extern int internal_hjDestroyPeers(void * peers);   // 0x14b218

int hjPeersDestroyHook(void * peers)
{
    if (0 && hjLeaveSkipDestroy) {
        hjLeaveSkipDestroy = 0;
        if (hjDestroyLogged < 8) {
            ++hjDestroyLogged;
            HOTJOIN_LOG("destroy: SUPPRESSED peers=%08x (paired with the leave above)\n",
                (u32)peers);
        }
        return 0;
    }

    if (hjDestroyLogged < 8) {
        u32 ra = (u32)__builtin_return_address(0);
        ++hjDestroyLogged;
        // ra names WHICH copy of the leave body ran: 0x001961D0 is the base-exe
        // 0x196128, 0x0095C058 is the overlay twin. Neither leaveact (3 known call
        // sites of 0x196128) nor backout (5 sites of 0x6D1928) logged a single line
        // this run while destroy fired five times, so the teardown is reached through
        // a path not in either list.
        HOTJOIN_LOG("destroy: ra=%08x peers=%08x sm=%d cid=%d menus=%d game=%d gs=%p\n",
            ra, (u32)peers, *(int*)(HJ_SM_BASE + HJ_SM_STATE),
            *(int*)(HJ_SM_BASE + HJ_SM_CLIENTID), isInMenus(), isInGame(), gameGetSettings());
    }

    return internal_hjDestroyPeers(peers);
}

void hjInstallDestroyProbe(void)
{
    if (hjDestroySitesHooked)
        return;

    // Site A is base exe and always present. Site B is only checked, never required.
    if (*(u32*)HJ_DESTROY_SITE_A != HJ_DESTROY_CALL) {
        hjDestroySitesHooked = 1;
        HOTJOIN_LOG("destroy: site A %08x holds %08x, expected %08x -- NOT hooked\n",
            HJ_DESTROY_SITE_A, *(u32*)HJ_DESTROY_SITE_A, HJ_DESTROY_CALL);
        return;
    }

    HOOK_JAL(HJ_DESTROY_SITE_A, &hjPeersDestroyHook);
    if (*(u32*)HJ_DESTROY_SITE_B == HJ_DESTROY_CALL)
        HOOK_JAL(HJ_DESTROY_SITE_B, &hjPeersDestroyHook);
    hjDestroySitesHooked = 1;
    HOTJOIN_LOG("destroy: hooked site A%s\n",
        (*(u32*)HJ_DESTROY_SITE_B == (u32)&hjPeersDestroyHook) ? " and B" : " only");
}

// ---------------------------------------------------------------------------
// Hotjoin: the world-connect COMPLETION callback, hooked at its source.
//
// Everything sections 40-46 built downstream guards for turns out to be one lifecycle:
//
//   0x195620   sync connect            state 6 -> 7, session ptr stored
//   0x195900   0x14b448 -> ctx->0x2C = 0x16f770 = connect[1], the world connect,
//              with a descriptor whose +0x20 is 0x196088          state 9
//   0x196088   ON CONNECT COMPLETE: 0x14af70 -> 0x14c198 copies peers->0x404 (my peer
//              index) into +0x08 = tNW_Info.myClientIndex; records it in the slot
//              arrays at +0x140/+0x6a5; state 10
//   0x1961c4   next tick, state == 10: 0x14b1b8 + 0x14b218 + epilogue   TEARDOWN
//
// That is a PROBE -- connect, learn your client id, disconnect. The hot-join menu site
// (0x6d0ec4/0x6d0ee0) runs it as the join, so the manager tears its own session down
// ~200 ms in. The two vanilla sites (0x6aa2b0, 0x6adc20) pre-set the flag at 0x1A5FC0,
// which makes 0x195900 skip 0x14b448 entirely: no descriptor, no 0x196088, no teardown.
//
// So the callback is registered ONLY on the hot-join path. Hooking it is inherently
// hot-join-only, and vanilla is untouched by construction. If `cc:` lines ever appear
// during a vanilla staging join, that reasoning is wrong and this must come out.
//
// The callback's address is not in a static slot -- 0x195900 materialises it with
// `lui v1,0x19; addiu v1,v1,0x6088` and stores it to sp+0x20 for the 0x14b448 call. So
// those two instructions are repointed at hjConnectCompleteHook, which forwards to the
// original (cid is learned exactly as vanilla does it) and then holds the manager at 7
// (established) instead of leaving it at 10 for the teardown tick. Race-free: we are
// inside the completion, and the tick that acts on 10 has not run yet.
#define HJ_CC_LUI_SITE    (0x001959d8)   // lui   v1,0x19
#define HJ_CC_ADDIU_SITE  (0x001959e4)   // addiu v1,v1,0x6088
#define HJ_CC_LUI_ORIG    (0x3c030019)
#define HJ_CC_ADDIU_ORIG  (0x24636088)
#define HJ_CC_ORIG        (0x00196088)

void hjConnectCompleteHook(void * result)
{
    u32 ra = (u32)__builtin_return_address(0);
    void (*orig)(void *) = (void (*)(void *))HJ_CC_ORIG;
    int before = *(int*)(HJ_SM_BASE + HJ_SM_STATE);
    int after, held = 0;

    orig(result);

    after = *(int*)(HJ_SM_BASE + HJ_SM_STATE);

    // Hold at 7 only when this is a real session on a joiner. 10 with a NULL session is
    // the vanilla no-op reset and must be left alone; 11 is the error path.
    // LOG ONLY. Holding at 7 here broke a vanilla staging join (section 48): the probe
    // must complete and tear down so the menu can issue connect[2], the real join.
    (void)held;

    if (hjCcLogged < 8) {
        ++hjCcLogged;
        HOTJOIN_LOG("cc: ra=%08x result=%08x r0=%d state %d -> %d%s cid=%d session=%08x menus=%d game=%d\n",
            ra, (u32)result, result ? *(int*)result : -1, before, after,
            held ? " HELD at 7" : "",
            *(int*)(HJ_SM_BASE + HJ_SM_CLIENTID),
            *(u32*)(HJ_SM_BASE + HJ_SM_SESSION),
            isInMenus(), isInGame());
    }
}

// The descriptor's other two callbacks, hooked the same way. +0x30 (0x197550) is the
// one that sets 0x1A5E50+0x169, which is exactly what the staging update at 0x6bec84
// backs out on. Naming the event that fires it, with the event struct's first words.
#define HJ_CB28_LUI   (0x001959dc)   // lui   a2,0x19
#define HJ_CB28_ADDIU (0x001959e8)   // addiu a2,a2,0x71e8
#define HJ_CB30_LUI   (0x001959e0)   // lui   a3,0x19
#define HJ_CB30_ADDIU (0x001959ec)   // addiu a3,a3,0x7550
#define HJ_CB28_ORIG  (0x001971e8)
#define HJ_CB30_ORIG  (0x00197550)

static void hjLogCb(const char * which, u32 ra, void * ev)
{
    if (hjCbLogged >= 12) return;
    ++hjCbLogged;
    HOTJOIN_LOG("%s: ra=%08x ev=%08x ev0=%08x ev4=%d ev8=%d  cid=%d sm=%d f168=%d f169=%d menus=%d\n",
        which, ra, (u32)ev,
        ev ? *(u32*)ev : 0, ev ? *(int*)((u32)ev + 4) : -1, ev ? *(int*)((u32)ev + 8) : -1,
        *(int*)(HJ_SM_BASE + HJ_SM_CLIENTID), *(int*)(HJ_SM_BASE + HJ_SM_STATE),
        *(u8*)(HJ_SM_BASE + 0x168), *(u8*)(HJ_SM_BASE + 0x169), isInMenus());
}

int hjCb28Hook(void * ev)
{
    int (*orig)(void *) = (int (*)(void *))HJ_CB28_ORIG;
    hjLogCb("cb28", (u32)__builtin_return_address(0), ev);
    return orig(ev);
}

int hjCb30Hook(void * ev)
{
    int (*orig)(void *) = (int (*)(void *))HJ_CB30_ORIG;
    int r;
    hjLogCb("cb30", (u32)__builtin_return_address(0), ev);
    r = orig(ev);
    if (hjCbLogged < 12) {
        ++hjCbLogged;
        HOTJOIN_LOG("cb30: after -> f168=%d f169=%d f16c=%d ret=%d\n",
            *(u8*)(HJ_SM_BASE + 0x168), *(u8*)(HJ_SM_BASE + 0x169), *(int*)(HJ_SM_BASE + 0x16c), r);
    }
    return r;
}

static void hjRepoint(u32 luiSite, u32 addiuSite, u32 luiOrig, u32 addiuOrig, u32 fn, const char * name)
{
    u32 hi = (fn >> 16) + ((fn & 0x8000) ? 1 : 0), lo = fn & 0xffff;
    if (*(u32*)luiSite != luiOrig || *(u32*)addiuSite != addiuOrig) {
        HOTJOIN_LOG("%s: sites read %08x/%08x, expected %08x/%08x -- NOT hooked\n",
            name, *(u32*)luiSite, *(u32*)addiuSite, luiOrig, addiuOrig);
        return;
    }
    POKE_U32(luiSite,   (luiOrig   & 0xffff0000) | (hi & 0xffff));
    POKE_U32(addiuSite, (addiuOrig & 0xffff0000) | lo);
    HOTJOIN_LOG("%s: repointed -> %08x\n", name, fn);
}

// ---------------------------------------------------------------------------
// Hotjoin: the JOIN RESULT handler.
//
// The join function 0x6d0d50 spins at 0x6d1068 after connecting, pumping the manager
// (0x195500) until 0x1A5E50+0x630 clears. Exactly one thing clears it: the handler at
// 0x19af80 (RT dispatch table slot 0x12), which stores the first payload word into
// +0x634 and zeroes +0x630. The join function then reads +0x634:
//     0 -> proceed (0x6d1e30, s2 = 1, success)
//     1/3/4/5 -> error string 50/51/49/52, back out via 0x6d112c
//     2 -> silent back out via 0x6d1174
// On the wire: a vanilla joiner receives 02-12-00-00-00-00 (word 0); the in-game host
// sends the hot-joiner 02-12-04-00-00-00 (word 4). Same message, different verdict.
//
// This hook logs what arrives, and -- only on a joiner whose roster already shows the
// host at GAME_START, i.e. a hot-join by construction -- rewrites a nonzero verdict to
// 0 before the original stores it. Vanilla's word is already 0, so vanilla is untouched.
#define HJ_RT12_TYPE  (0x12)
#define HJ_RT12_ORIG  (0x0019af80)

int hjRt12Hook(void * a0, void * a1, int a2, u8 * payload)
{
    int (*orig)(void *, void *, int, u8 *) = (int (*)(void *, void *, int, u8 *))hjRt12Orig;
    u32 ra = (u32)__builtin_return_address(0);
    GameSettings * gs = gameGetSettings();
    int word = payload ? *(int*)payload : -1;
    int sm = *(int*)(HJ_SM_BASE + HJ_SM_STATE);
    int joining = isInMenus() && !isInGame() && (sm == 9 || sm == 10);
    int forced = 0;

    // Never let the join wait finish while gs is NULL. 0x19AF80 stores the verdict into
    // +0x634 and CLEARS +0x630, which releases the loop; if the settings have not landed
    // yet, staging is entered with a NULL GameSettings and faults immediately at
    // 0x6BF470. Measured exactly that, twice.
    //
    // Skipping orig() leaves +0x630 set and the loop waiting. The host repeats this
    // message about once a second, so a later one completes the join once gs exists.
    // If it never does, we stop deferring and hand the loop a verdict of 2, which is its
    // own silent back-out -- a clean failure instead of a crash. The join function's own
    // deadline (0x6D5F80) would catch it too; this just makes the outcome explicit.
    // Defer ANY verdict while gs is NULL, not just 0. Measured: on a rejoin the server's
    // verdict-0 message never arrives -- only the host's 4 does -- so a rule that only
    // deferred 0 let the 4 through, and the loop died on error 49 with no settings.
    if (payload && joining && !gs) {
        if (++hjRt12Defer <= HJ_RT12_DEFER_MAX) {
            if (hjRt12Logged < 8) {
                ++hjRt12Logged;
                HOTJOIN_LOG("rt12: DEFER %d/%d (word=%d, gs is NULL) ra=%08x f630=%d sm=%d\n",
                    hjRt12Defer, HJ_RT12_DEFER_MAX, word, ra, *(u8*)(HJ_SM_BASE + 0x630), sm);
            }
            return 0;
        }
        *(int*)payload = 2;   // give up cleanly rather than enter staging with no settings
        word = 2;
    } else if (gs) {
        hjRt12Defer = 0;
    }

    // The host answers a hot-join with verdict 4. Rewrite it only when the settings are
    // in hand and the roster already shows the host in-game.
    if (payload && word != 0 && gs && gs->PlayerStates[0] >= 7) {
        *(int*)payload = 0;
        forced = 1;
    }
    if (hjRt12Logged < 8) {
        ++hjRt12Logged;
        HOTJOIN_LOG("rt12: ra=%08x a2=%d word=%d%s host=%d hostState=%d f630=%d f634=%d sm=%d\n",
            ra, a2, word, forced ? " -> FORCED 0" : "", gameAmIHost(),
            gs ? gs->PlayerStates[0] : -9,
            *(u8*)(HJ_SM_BASE + 0x630), *(int*)(HJ_SM_BASE + 0x634),
            *(int*)(HJ_SM_BASE + HJ_SM_STATE));
    }
    return orig(a0, a1, a2, payload);
}

void hjInstallRt12Probe(void)
{
    u32 table, maxTypes, st, n = 0;
    if (hjRt12Installed) return;
    table = *(u32*)HJ_RT_HANDLER_TABLE_PTR;
    maxTypes = *(u32*)HJ_RT_MAXTYPES_PTR;
    if (!table || !maxTypes || maxTypes > 256) {
        HOTJOIN_LOG("rt12: table %08x maxTypes %d -- NOT hooked\n", table, (int)maxTypes);
        return;
    }
    hjRt12Installed = 1;
    for (st = 0; st < HJ_RT_MAX_STACKS; ++st) {
        u32 * slot = (u32*)(table + (st * maxTypes * 4) + (HJ_RT12_TYPE * 4));
        if (*slot == HJ_RT12_ORIG) {
            if (!hjRt12Orig) hjRt12Orig = *slot;
            *slot = (u32)&hjRt12Hook;
            ++n;
        }
    }
    HOTJOIN_LOG("rt12: hooked slot 0x12 in %d of %d stacks (orig %08x)\n", (int)n, HJ_RT_MAX_STACKS, hjRt12Orig);
}

// ---------------------------------------------------------------------------
// Hotjoin: the EVENT DRAIN.
//
// The per-frame menu network update 0x195ae8 (which the join wait pumps through
// 0x195500) calls 0x14b160 = lock; 0x14f298(buf); unlock. 0x14f298 memcpy's the 40-byte
// pending-event block at 0x001CDAB0 into buf: five 8-byte entries. The caller stores the
// LAST non-zero code into 0x1A5E50+0x2dc, and the join loop at 0x6d10a4 treats any
// non-zero +0x2dc as fatal (error 40, silent back-out at 0x6d1174).
//
// Measured: on every hot-join attempt +0x2dc reads 12 within ~20 ms of the completion,
// before the 02-12 verdict has arrived; on vanilla it stays 0. This hook logs every code
// the drain returns, and -- only on a joiner whose roster already shows the host at
// GAME_START, and only while the join wait flag +0x630 is still set -- removes code-12
// entries from both the copy and the source block, so the wait continues to the verdict.
#define HJ_EV_SITE   (0x0014b188)   // jal 0x14f298 inside 0x14b160
#define HJ_EV_CALL   (0x0c053ca6)
#define HJ_EV_BLOCK  (0x001CDAB0)
#define HJ_EV_DROP_CODE (12)

extern int internal_hjEventCopy(void * buf);   // 0x14f298

int hjEventDrainHook(void * buf)
{
    int r = internal_hjEventCopy(buf);
    u32 * e = (u32*)buf;
    u32 * src = (u32*)HJ_EV_BLOCK;
    GameSettings * gs = gameGetSettings();
    int i, any = 0, dropped = 0;
    // gs is an EXCLUSION here, never a requirement. Gating on `gs != NULL` was wrong
    // three separate times (the ev drop, the promote, the SYNC block): the join stalls
    // BEFORE gs exists -- gs only appears once staging is entered -- so any guard that
    // demands it can never fire in the window it was written for. Measured: every ev
    // line carrying code 12 shows `hot=0 f630=0 gs=0x0`.
    //
    // The window is: in menus, not in game, a connect in flight or just completed
    // (manager 9 or 10), and no settings yet. That is exactly the join wait and nothing
    // else -- staging and in-game keep their real event 12.
    // Event 12 is a TRANSIENT RACE, not a persistent error. hjWatchLatch proved it:
    // 0x1CF760 flickers 0 -> 7 -> 0 within one or two frames, on stacks 1 and 2, at
    // manager states 5/6/9/10, before and during joins. 0x14EE08 memsets that table at
    // the top of every net tick and repopulates it during its walk, so code 12 fires
    // whenever the walk reaches stack i and finds table[i] already set EARLIER IN THE
    // SAME TICK. The "stale latch surviving a session" model of sections 54-55 was wrong.
    //
    // The join loop polls +0x2DC every iteration and treats any non-zero value as fatal,
    // so a long enough wait is near-certain to catch a flicker. Measured: two consecutive
    // attempts died 150 ms after connect with `gs=0x1f7ed20 st=7/0 cl=0/1` -- settings
    // present, roster correct, nothing actually wrong with either join.
    //
    // Dropping this is safe ONLY because hjRt12Hook now refuses to complete a join while
    // gs is NULL. That pairing matters: dropping alone let a join finish with no settings
    // and staging faulted at 0x6BF470 dereferencing the NULL; refusing alone left the
    // transient free to kill healthy joins. Each covers the other's failure mode.
    int sm = *(int*)(HJ_SM_BASE + HJ_SM_STATE);
    int hot = (isInMenus() && !isInGame() && (sm == 9 || sm == 10));
    (void)gs;

    if (!buf) return r;
    for (i = 2; i < 10; ++i) if (e[i]) any = 1;   // e[0] is the block size (0x28), not a code
    if (hot) {
        // entries at +8,+16,+24,+32 (code word), and the 5th code at +36
        for (i = 2; i <= 9; i += 2)
            if (e[i] == HJ_EV_DROP_CODE) { e[i] = 0; src[i] = 0; ++dropped; }
        if (e[9] == HJ_EV_DROP_CODE) { e[9] = 0; src[9] = 0; ++dropped; }
    }
    if (dropped) hjEvDropped += dropped;
    if ((any || dropped) && hjEvLogged < 16) {
        ++hjEvLogged;
        HOTJOIN_LOG("ev: [%08x %08x | %08x %08x | %08x %08x | %08x %08x | %08x %08x]%s hot=%d f630=%d sm=%d stk=%08x/%08x/%08x/%08x\n",
            e[0], e[1], e[2], e[3], e[4], e[5], e[6], e[7], e[8], e[9],
            dropped ? " DROPPED 12" : "", hot, *(u8*)(HJ_SM_BASE + 0x630), sm,
            *(u32*)0x001CF760, *(u32*)0x001CF764, *(u32*)0x001CF768, *(u32*)0x001CF76C);
        // The stack registry. 0x14F780 registers a peers object at 0x1DD648[idx] only
        // when the slot is EMPTY (else it returns 23), and 0x14F8C8 -> 0x14C228 ->
        // 0x1521C0 nulls the slot when the object is destroyed. 0x1CF760[2] holding 7
        // means SOME peers object with ->0x448 == 2 had a send fail. Printing the
        // registry says whether that object is the live one or a leftover the
        // destructor never reached.
        {
            u32 * reg = (u32*)0x001CD648;   /* NOT 0x1DD648: addiu -10680 with lui 0x1d is 0x1D0000-0x29B8 */
            HOTJOIN_LOG("ev: reg=%08x/%08x/%08x/%08x  idx=%d/%d/%d/%d  gate=%d/%d/%d/%d\n",
                reg[0], reg[1], reg[2], reg[3],
                reg[0] ? *(int*)(reg[0] + 0x448) : -1, reg[1] ? *(int*)(reg[1] + 0x448) : -1,
                reg[2] ? *(int*)(reg[2] + 0x448) : -1, reg[3] ? *(int*)(reg[3] + 0x448) : -1,
                reg[0] ? *(int*)(reg[0] + 0x430) : -1, reg[1] ? *(int*)(reg[1] + 0x430) : -1,
                reg[2] ? *(int*)(reg[2] + 0x430) : -1, reg[3] ? *(int*)(reg[3] + 0x430) : -1);
        }
    }
    return r;
}

void hjInstallEventDrainHook(void)
{
    if (*(u32*)HJ_EV_SITE != HJ_EV_CALL) {
        HOTJOIN_LOG("ev: site %08x holds %08x, expected %08x -- NOT hooked\n",
            HJ_EV_SITE, *(u32*)HJ_EV_SITE, HJ_EV_CALL);
        return;
    }
    HOOK_JAL(HJ_EV_SITE, &hjEventDrainHook);
    HOTJOIN_LOG("ev: event drain hooked at %08x\n", HJ_EV_SITE);
}

// ---------------------------------------------------------------------------
// Hotjoin: the ERROR LATCH that becomes event 12.
//
// 0x14ee08 (top of every net tick) raises 12 when 0x1CF760[0] is non-zero after its
// per-stack walk. The only base-exe writer of that table is 0x14ce48, which stores
// 0x152fb8(peers, code) into 0x1CF760[peers->0x448], and 0x14ce48 has exactly one jal
// caller: 0x1503e4, in the peer close-with-reason region. Log-only: names the peers,
// stack, code and caller at the moment the latch is set.
#define HJ_LATCH_SITE (0x001503e4)
#define HJ_LATCH_CALL (0x0c053392)   // jal 0x14ce48

extern int internal_hjSetErrorLatch(void * peers, int code);   // 0x14ce48

int hjErrorLatchHook(void * peers, int code)
{
    u32 ra = (u32)__builtin_return_address(0);
    int r = internal_hjSetErrorLatch(peers, code);
    if (hjLatchLogged < 8) {
        ++hjLatchLogged;
        HOTJOIN_LOG("latch: ra=%08x peers=%08x stack=%d code=%d -> ret=%d table=%08x/%08x/%08x/%08x f630=%d sm=%d host=%d\n",
            ra, (u32)peers, peers ? *(int*)((u32)peers + 0x448) : -1, code, r,
            *(u32*)0x001CF760, *(u32*)0x001CF764, *(u32*)0x001CF768, *(u32*)0x001CF76C,
            *(u8*)(HJ_SM_BASE + 0x630), *(int*)(HJ_SM_BASE + HJ_SM_STATE), gameAmIHost());
    }
    return r;
}

// Called every frame, no latch. 0x1503E4 is base exe so it cannot be swapped out, but
// this probe has never logged a single line while 0x1CF760[2] held 7 on every failing
// tick -- and 0x14CE48 has no other executing caller (the second `jal` at 0x91626C is
// in the duplicate image copy at +0x7C5E88, which also explains 0x95C04C and the high
// callers of 0x196128). Either the hook is not installed or the write arrives another
// way; re-checking every frame and logging on install settles which.
// A POLLING watcher on the latch table, not a hook.
//
// Every probe so far has hooked a call site deduced from static analysis, and that has
// produced a contradiction: 0x1CF760 has exactly one writer in the image (0x14CE48),
// reached from exactly one executing call site (0x1503E4), the hook there is installed,
// and it has never once logged while 0x1CF760[2] held 7 on every failing tick. So the
// write arrives by a path the scan cannot see -- most likely a store whose base register
// is loaded from memory rather than built with `lui`, which the search would miss.
//
// This assumes nothing about the writer. It samples the four entries every frame and
// reports any 0 -> non-zero or non-zero -> 0 transition with the surrounding state, so
// the exact frame is pinned even though the instruction is not. Four loads per frame.
void hjWatchLatch(void)
{
    u32 * t = (u32*)0x001CF760;
    u32 * reg = (u32*)0x001CD648;
    int i;

    for (i = 0; i < 4; ++i) {
        if (t[i] == hjLatchSeen[i])
            continue;
        if (hjLatchWatchLogged < 24) {
            u32 ctx = *(u32*)HJ_NET_CTX_PTR;
            ++hjLatchWatchLogged;
            HOTJOIN_LOG("latchwatch: [%d] %08x -> %08x  sm=%d cid=%d gs=%p live=%08x reg=%08x/%08x/%08x/%08x menus=%d game=%d\n",
                i, hjLatchSeen[i], t[i],
                *(int*)(HJ_SM_BASE + HJ_SM_STATE), *(int*)(HJ_SM_BASE + HJ_SM_CLIENTID),
                gameGetSettings(), ctx ? *(u32*)(ctx + HJ_CTX_PEERS) : 0,
                reg[0], reg[1], reg[2], reg[3], isInMenus(), isInGame());
        }
        hjLatchSeen[i] = t[i];
    }
}

void hjInstallErrorLatchProbe(void)
{
    if (*(u32*)HJ_LATCH_SITE != HJ_LATCH_CALL)
        return;   // already ours, or not the expected instruction
    HOOK_JAL(HJ_LATCH_SITE, &hjErrorLatchHook);
    HOTJOIN_LOG("latch: hooked at %08x (site now %08x)\n",
        HJ_LATCH_SITE, *(u32*)HJ_LATCH_SITE);
}

void hjInstallConnectCompleteHook(void)
{
    u32 fn = (u32)&hjConnectCompleteHook;
    u32 hi = (fn >> 16) + ((fn & 0x8000) ? 1 : 0);   // addiu sign-extends its immediate
    u32 lo = fn & 0xffff;

    if (hjCcInstalled)
        return;
    hjCcInstalled = 1;

    if (*(u32*)HJ_CC_LUI_SITE != HJ_CC_LUI_ORIG || *(u32*)HJ_CC_ADDIU_SITE != HJ_CC_ADDIU_ORIG) {
        HOTJOIN_LOG("cc: sites read %08x/%08x, expected %08x/%08x -- NOT hooked\n",
            *(u32*)HJ_CC_LUI_SITE, *(u32*)HJ_CC_ADDIU_SITE, HJ_CC_LUI_ORIG, HJ_CC_ADDIU_ORIG);
        return;
    }

    POKE_U32(HJ_CC_LUI_SITE,   0x3c030000 | (hi & 0xffff));
    POKE_U32(HJ_CC_ADDIU_SITE, 0x24630000 | lo);
    HOTJOIN_LOG("cc: completion callback repointed 0x196088 -> %08x (lui %04x addiu %04x)\n",
        fn, hi & 0xffff, lo);
    hjInstallEventDrainHook();
    hjInstallErrorLatchProbe();
    hjRepoint(HJ_CB28_LUI, HJ_CB28_ADDIU, 0x3c060019, 0x24c671e8, (u32)&hjCb28Hook, "cb28");
    hjRepoint(HJ_CB30_LUI, HJ_CB30_ADDIU, 0x3c070019, 0x24e77550, (u32)&hjCb30Hook, "cb30");
}

// ---------------------------------------------------------------------------
// Hotjoin: WHO calls the leave ACTION.
//
// 0x196128 is not a tick. The host reaches state 10 and stays there for the entire
// game with its session intact; 0x196128 only runs when a menu decides to leave. On the
// joiner it runs ~200 ms after every connect, which is the join -> LeftGameWorld ->
// JoinedChatWorld -> retry cycle Medius logs every 2 s. That decision is made in the
// overlay, at one of exactly three sites. This names which one, and what the manager,
// roster and peers looked like at that instant.
#define HJ_LEAVEACT_CALL   (0x0c06584a)   // jal 0x196128
#define HJ_LEAVEACT_SITE_A (0x005f9a94)
#define HJ_LEAVEACT_SITE_B (0x006ac684)
#define HJ_LEAVEACT_SITE_C (0x006d1948)

extern int internal_hjLeaveAction(void);   // 0x196128

int hjLeaveActionHook(void)
{
    u32 ra = (u32)__builtin_return_address(0);
    GameSettings * gs = gameGetSettings();
    u32 ctx = *(u32*)HJ_NET_CTX_PTR;
    u32 peers = ctx ? *(u32*)(ctx + HJ_CTX_PEERS) : 0;
    void * p0 = peers ? internal_hjPeerLookup((void*)peers, 0) : 0;
    void * p1 = peers ? internal_hjPeerLookup((void*)peers, 1) : 0;

    if (hjLeaveActLogged < 8) {
        ++hjLeaveActLogged;
        HOTJOIN_LOG("leaveact: ra=%08x sm=%d cid=%d session=%08x gs=%p n=%d roster[0]=%d/%d roster[1]=%d/%d p0=%d p1=%d p438=%d menus=%d game=%d\n",
            ra, *(int*)(HJ_SM_BASE + HJ_SM_STATE), *(int*)(HJ_SM_BASE + HJ_SM_CLIENTID),
            *(u32*)(HJ_SM_BASE + HJ_SM_SESSION), (void*)gs,
            gs ? gs->PlayerCount : -1,
            gs ? gs->PlayerClients[0] : -9, gs ? gs->PlayerStates[0] : -9,
            gs ? gs->PlayerClients[1] : -9, gs ? gs->PlayerStates[1] : -9,
            p0 ? *(int*)((u32)p0 + 0x08) : -1, p1 ? *(int*)((u32)p1 + 0x08) : -1,
            peers ? *(int*)(peers + 0x438) : -1,
            isInMenus(), isInGame());
    }
    return internal_hjLeaveAction();
}

// Re-checked every menus frame, with NO "already hooked" latch.
//
// These are overlay addresses. The previous version latched hjLeaveActHooked on the
// first success and never looked again -- so when the module was swapped (which
// hjInstallLeaveCallerProbe logs as `leavecall: hooked 4 menu sites`, seen mid-session)
// the HOOK_JALs went with it while the latch still claimed they were installed. The
// probe then sat silent through five teardowns and its silence read as "this path was
// not taken", which was wrong.
//
// A site holding the ORIGINAL call is uninstalled and gets hooked; a site holding our
// hook does not match and is skipped. Idempotent, and it survives any number of reloads.
void hjInstallLeaveActionProbe(void)
{
    int n = 0;
    if (!isInMenus())
        return;
    if (*(u32*)HJ_LEAVEACT_SITE_A == HJ_LEAVEACT_CALL) { HOOK_JAL(HJ_LEAVEACT_SITE_A, &hjLeaveActionHook); ++n; }
    if (*(u32*)HJ_LEAVEACT_SITE_B == HJ_LEAVEACT_CALL) { HOOK_JAL(HJ_LEAVEACT_SITE_B, &hjLeaveActionHook); ++n; }
    if (*(u32*)HJ_LEAVEACT_SITE_C == HJ_LEAVEACT_CALL) { HOOK_JAL(HJ_LEAVEACT_SITE_C, &hjLeaveActionHook); ++n; }
    if (n)
        HOTJOIN_LOG("leaveact: hooked %d of 3 sites\n", n);
}

// ---------------------------------------------------------------------------
// Hotjoin: WHICH back-out site.
//
// leaveact resolved the leave to the helper at 0x6d1928 (ra=006d1950), which has ten
// callers. Five are in the join/staging overlay. This names the one that fires, with
// the manager state, the roster, the host-state flag byte at 0x1A7118 and a0 at that
// instant. Same overlay-guarded install as the leavecall probe.
#define HJ_BACKOUT_CALL   (0x0c1b464a)   // jal 0x6d1928
#define HJ_BACKOUT_A (0x006c0cdc)   // in 0x6c0c60: dialog 5699 answered 1, or a2==0
#define HJ_BACKOUT_B (0x006d0f04)   // in 0x6d0d50 (the join fn): 0x195900 failed
#define HJ_BACKOUT_C (0x006d112c)   // in 0x6d0d50: poll loop
#define HJ_BACKOUT_D (0x006d1174)   // in 0x6d0d50: poll loop
#define HJ_BACKOUT_E (0x006d1838)   // in 0x6d12a8

extern int internal_hjBackout(int a0);   // 0x6d1928 (overlay)

int hjBackoutHook(int a0)
{
    u32 ra = (u32)__builtin_return_address(0);
    GameSettings * gs = gameGetSettings();
    if (hjBackoutLogged < 8) {
        ++hjBackoutLogged;
        HOTJOIN_LOG("backout: ra=%08x a0=%08x sm=%d cid=%d f630=%d f634=%d f2dc=%08x f638=%d err=%d f168=%d f169=%d f2ec=%08x flag7118=%d gs=%p n=%d st=%d/%d cl=%d/%d menus=%d\n",
            ra, (u32)a0, *(int*)(HJ_SM_BASE + HJ_SM_STATE), *(int*)(HJ_SM_BASE + HJ_SM_CLIENTID),
            *(u8*)(HJ_SM_BASE + 0x630), *(int*)(HJ_SM_BASE + 0x634), *(u32*)(HJ_SM_BASE + 0x2dc), *(short*)(HJ_SM_BASE + 0x638),
            (*(u32*)0x0024D860) ? *(int*)((*(u32*)0x0024D860) + 0x14) : -1,
            *(u8*)(HJ_SM_BASE + 0x168), *(u8*)(HJ_SM_BASE + 0x169), *(u32*)(HJ_SM_BASE + 0x2ec),
            *(u8*)0x001A7118, (void*)gs, gs ? gs->PlayerCount : -1,
            gs ? gs->PlayerStates[0] : -9, gs ? gs->PlayerStates[1] : -9,
            gs ? gs->PlayerClients[0] : -9, gs ? gs->PlayerClients[1] : -9, isInMenus());
    }
    return internal_hjBackout(a0);
}

void hjInstallBackoutProbe(void)   // same re-arm rule as hjInstallLeaveActionProbe
{
    int n = 0;
    if (!isInMenus()) return;
    if (*(u32*)HJ_BACKOUT_A == HJ_BACKOUT_CALL) { HOOK_JAL(HJ_BACKOUT_A, &hjBackoutHook); ++n; }
    if (*(u32*)HJ_BACKOUT_B == HJ_BACKOUT_CALL) { HOOK_JAL(HJ_BACKOUT_B, &hjBackoutHook); ++n; }
    if (*(u32*)HJ_BACKOUT_C == HJ_BACKOUT_CALL) { HOOK_JAL(HJ_BACKOUT_C, &hjBackoutHook); ++n; }
    if (*(u32*)HJ_BACKOUT_D == HJ_BACKOUT_CALL) { HOOK_JAL(HJ_BACKOUT_D, &hjBackoutHook); ++n; }
    if (*(u32*)HJ_BACKOUT_E == HJ_BACKOUT_CALL) { HOOK_JAL(HJ_BACKOUT_E, &hjBackoutHook); ++n; }
    if (n) HOTJOIN_LOG("backout: hooked %d of 5 sites\n", n);
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

    hjInstallDestroyProbe();
    hjInstallConnectCompleteHook();

    if (*(u32*)HJ_LEAVE_SLOT == HJ_LEAVE_ORIG) {
        hjLeaveOrig = *(u32*)HJ_LEAVE_SLOT;
        POKE_U32(HJ_LEAVE_SLOT, &hjLeaveSessionHook);
        HOTJOIN_LOG("leave: hooked slot %08x\n", HJ_LEAVE_SLOT);
    } else {
        HOTJOIN_LOG("leave: slot %08x holds %08x, expected %08x -- NOT hooked\n",
            HJ_LEAVE_SLOT, *(u32*)HJ_LEAVE_SLOT, HJ_LEAVE_ORIG);
    }

    if (*(u32*)HJ_SESSEND_SLOT == HJ_SESSEND_ORIG) {
        hjSessEndOrig = *(u32*)HJ_SESSEND_SLOT;
        POKE_U32(HJ_SESSEND_SLOT, &hjSessionEndHook);
        HOTJOIN_LOG("sessend: hooked slot %08x\n", HJ_SESSEND_SLOT);
    } else {
        HOTJOIN_LOG("sessend: slot %08x holds %08x, expected %08x -- NOT hooked\n",
            HJ_SESSEND_SLOT, *(u32*)HJ_SESSEND_SLOT, HJ_SESSEND_ORIG);
    }

    if (*(u32*)HJ_PEERCLOSE_SITE_A == HJ_PEERCLOSE_CALL &&
        *(u32*)HJ_PEERCLOSE_SITE_B == HJ_PEERCLOSE_CALL) {
        HOOK_JAL(HJ_PEERCLOSE_SITE_A, &hjPeerCloseHook);
        HOOK_JAL(HJ_PEERCLOSE_SITE_B, &hjPeerCloseHook);
        HOTJOIN_LOG("peerclose: hooked both sites (14d0e0, 150310)\n");
    } else {
        HOTJOIN_LOG("peerclose: sites hold %08x/%08x, expected %08x -- NOT hooked\n",
            *(u32*)HJ_PEERCLOSE_SITE_A, *(u32*)HJ_PEERCLOSE_SITE_B, HJ_PEERCLOSE_CALL);
    }

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
void hjHostReapRemotes(void) { }
void hjDumpPadStream(void) { }
void hjDumpPadRing(void) { }
void hjDumpWeaponMask(void) { }
void hjDumpWeaponSlots(void) { }
void hjFindRemoteName(void) { }
void hjSendMyName(void) { }
void hjInstallNameHandler(void) { }
void hjHostAdoptPeers(void) { }
void hjHostRefreshNames(void) { }
void hjLogEpochTock(void) { }
void hjDumpPeers(void) { }
void hjInstallType22Probe(void) { }
void hjRefreshPeerActivity(void) { }
void hjInstallLeaveCallerProbe(void) { }
void hjInstallLeaveActionProbe(void) { }
void hjInstallBackoutProbe(void) { }
void hjInstallErrorLatchProbe(void) { }
void hjWatchLatch(void) { }
void hjRestoreStateMachine(void) { }
void hjWatchStateMachine(void) { }
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
