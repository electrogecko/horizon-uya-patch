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

// HJ_BUILD_TAG -- the build fingerprint, printed once at hook-install time.
//
// A test round was held up asking the emulator agents to confirm an md5, which they CANNOT
// do: Horizon delivers the patch over the network straight into EE memory, so
// patch-10684.bin never lands on a client's disk and there is nothing there to hash. Both
// agents refused to guess rather than fake a match.
//
// Bump by hand for any build handed to a tester, and identify rounds by this string. An md5
// still identifies a build on the SERVER machine, where the file exists and the bind mount
// can be verified; the tag is the only identifier available on a client.
#define HJ_BUILD_TAG   "20261024a-deleteguard"

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

// s209-G: these two are used by patchGameDetails, which is compiled for BOTH regions, so
// they must live OUTSIDE the #ifndef UYA_PAL block below. Putting them inside it built
// fine for NTSC and failed the PAL link -- and because bin/ is bind-mounted, that failure
// DELETED the served artifact. Region-guarded definitions and unguarded users do not mix.
int hjTeamPromptAsked = 0;       // armed on entry to GAME DETAILS, per join attempt
static const char * hjTeamChoiceOptions[] = { "Auto (balance teams)", "Blue", "Red" };

#ifndef UYA_PAL
#define HJ_PLAYERBIT_VTABLE_SLOT    (0x001dd970)
#define HJ_PLAYERBIT_TABLE_BASE     (0x0022f550)
#define HJ_PLAYERBIT_TABLE_STRIDE   (3184)
#define HJ_PLAYERBIT_TABLE_MAXIDX   (64)

extern int internal_hjResolvePlayerCtx(void ** out, void * arg);
extern void internal_hjPeerConnectCtor(void * a0, void * a1);
extern void * internal_hjPeerLookup(void * peers, int idx);
extern int internal_hjIntroducePeer(void * ctx, int peerIdx, int a2, int a3);
extern int internal_hjType9(void * peers, int a1, int peerIdx, void * msg);
extern void * internal_hjAuxGet(void * ctx, int peerIdx);   // 0x14a490

static int hjPlayerBitInstalled = 0;
static int hjPlayerBitNegIds = 0;
static int hjPlayerBitSkips = 0;
static int hjPlayerBitSeen = 0;

void hjRegisterPlayerBit(void * a0, void * a1, int playerIndex)
{
    void * out = 0;

    // playerIndex < 0 MUST be rejected, not just -2.   (s154, measured 2026-09-28)
    // The final statement of this function is `obj->0x7C |= (1 << playerIndex)`. A
    // negative shift is undefined in C, and on MIPS the shift amount is masked to 5
    // bits, so playerIndex == -1 sets BIT 31 instead of any player's bit. Observed
    // live on the host during a hot-join:
    //     HJ playerbit: OK obj=01f7c1d0 idx=1 id=-1 ra=0016f2f0
    // obj and idx were both correct -- it is only the id that was bogus -- so the
    // registration "succeeded" while setting a garbage bit and leaving player 1's bit
    // clear. That matches the symptom exactly: the host rendered maxTest2's NAMETAG but
    // no character model and no radar blip.
    // Returning early cannot lose a legitimate registration, because bit 31 was never
    // the right bit for anybody. It is deliberately LOUD rather than silent: the -1 is
    // an upstream defect and masking it quietly is how we would lose it.
    if (playerIndex == -2)
        return;
    // REVERTED TO LOG-ONLY on 2026-09-28 (s154-A). I briefly returned early here, on the
    // belief that `1 << -1` was a bug of mine. It is not: vanilla 0x00199c40 does the
    // IDENTICAL shift with the IDENTICAL single `-2` guard (`sllv` masks to 5 bits exactly as
    // C does), so refusing it was a DIVERGENCE from the game, not a fix. Measured across a
    // round: it changed nothing visually -- still nametag-only, one radar blip -- so it bought
    // no benefit either. Observe, do not diverge.
    if (playerIndex < 0) {
        if ((hjPlayerBitNegIds % 60) == 0)
            HOTJOIN_LOG("playerbit: ANOMALY negative id=%d ra=%08x n=%d "
                "-- vanilla shift APPLIED (sets bit 31)\n",
                playerIndex, (u32)__builtin_return_address(0), hjPlayerBitNegIds);
        ++hjPlayerBitNegIds;
        /* fall through: do what vanilla does */
    }

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
// peers+0x404 = my own peer index; peers+0x408 = the index of the machine allowed to
// run introducePeer (0x00173FC0 returns immediately unless the two are equal). Defined
// here rather than beside the type-22 hook because hjIntroducePeerHook, which is
// earlier in the file, reads them too.
#define HJ_PEERS_MYIDX    (0x404)
#define HJ_PEERS_INTRO    (0x408)
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
void hjPeerClosedRemote(int idx, int t08);   // defined with the teardown, ~800 lines down

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

    // AFTER the vanilla close, so its own disconnect callbacks have run and we tear down
    // what they left behind rather than racing them. t08 was read above, before peerReset
    // memsets the record.
    hjPeerClosedRemote(idx, t08);
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

// ---------------------------------------------------------------------------
// s211: hjLogWhere -- say where the client IS, in one line, on change.
//
// This session burned a large fraction of its effort taking screenshots to answer "which
// menu am I on", then driving a press, then screenshotting again. The patch already knew
// the answer: the three active-menu slots at 0x01c5c110/114/118. menuscan logged them,
// but as raw ids behind a 400-line cap, so it documented the dialog hunt rather than
// serving as a navigation oracle.
//
// One named line per transition, uncapped (it is edge-triggered, so it costs nothing when
// nothing moves). A driver can now `grep -a 'HJ where:' emulog.txt | tail -1` instead of
// fetching and decoding a PNG, which is both cheaper and not subject to screenshot lag --
// the stale GAME INFO screenshot that had me telling the user maxTest2 was still in the
// lobby would not have survived this check.
//
// In game the UI slots hold reused memory, so scanning them yields dozens of false
// matches. Report IN_GAME directly there and only scan when actually in menus.
static const char * hjMenuName(int id)
{
    switch (id) {
        case UI_MENU_SELECT_PROFILE:        return "PROFILES";
        case UI_MENU_ONLINE_AGREEMENT:      return "LICENSE_AGREEMENT";
        case UI_MENU_ONLINE_AGREEMENT_2:    return "LICENSE_AGREEMENT_2";
        case UI_MENU_ANNOUNCEMENTS:         return "ANNOUNCEMENTS";
        case UI_MENU_BUDDY_LIST:            return "BUDDIES";
        case UI_MENU_CREATE_GAME:           return "CREATE_GAME";
        case UI_MENU_FIND_GAME:             return "FIND_GAME";
        case UI_MENU_GAME_DETAILS:          return "GAME_DETAILS";
        case UI_MENU_KEYBOARD:              return "KEYBOARD";
        case UI_MENU_ONLINE_LOBBY:          return "ONLINE_LOBBY";
        case UI_MENU_PLAYER_DETAILS:        return "PLAYER_DETAILS";
        case UI_MENU_CITY:                  return "CITY";
        case UI_MENU_STAGING:               return "STAGING";
        case UI_MENU_CHANGE_SKIN_TEAM:      return "CHANGE_SKIN_TEAM";
        case UI_MENU_STATS:                 return "STATS";
        case UI_MENU_CITY_SELECT:           return "CITY_SELECT";
        case UI_MENU_IN_GAME_DETAILS:       return "IN_GAME_DETAILS";
        case UI_MENU_WEAPON_SELECT:         return "WEAPON_SELECT";
        default:                            return "?";
    }
}

// s233-TEST: force gameConfig.grNewPlayerSync on, for the s226 experiment ONLY.
//
// s226 says a late-joining client builds remote players from defaults and an idle or dead
// player never corrects it. playerSyncBroadcastPlayerState sends full state (GadgetId,
// State, Health, position) on a RATE TICKER rather than on change, so with that system
// running an idle player keeps re-broadcasting and a joiner is corrected within one
// interval -- i.e. s226 should not happen at all. But playerSyncTick returns immediately
// unless this flag is set, `case 5: // Siege` sets it to 0 ("Off in case of vehicles"),
// and every s226 observation was in Siege. Live read confirmed 0.
//
// The flag has to be on for BOTH parties -- the sender to broadcast and the receiver to
// handle (playerSyncOnReceivePlayerState returns early when it is clear) -- and the config
// menu's tab navigation could not be driven, so force it here instead of fighting the UI.
// Forcing it in the patch also keeps the diagnostic honest: a read of gameConfig+43 shows
// the value actually in effect.
//
// THIS DEFINE MUST BE 0 IN ANY BUILD THAT IS COMMITTED. It overrides a deliberate
// per-mode setting whose comment warns about vehicles, which Siege has.
#define HJ_TEST_FORCE_PLAYERSYNC   (0)

extern PatchGameConfig_t gameConfig;    // defined in config.c

void hjTestForceSync(void)
{
#if HJ_TEST_FORCE_PLAYERSYNC
    static int said = 0, tick = 0, forced = 0;
    if (!isInGame())
        return;
    // Re-force every frame: if something stomps it back we want to win, and we want to see
    // the fight in the log rather than infer it.
    if (!gameConfig.grNewPlayerSync) {
        gameConfig.grNewPlayerSync = 1;
        ++forced;
    }

    // Report the VALUE AND THE ADDRESS from inside the patch, ~every 5 s. An external read
    // of a symbol address taken from the ELF is an assumption; this is not. If the address
    // printed here differs from the one being read externally, that explains an external
    // read of 0 while the patch believes it has set 1 -- which is exactly the situation
    // this is here to resolve.
    if (!said || ++tick >= 300) {
        tick = 0; said = 1;
        HOTJOIN_LOG("TEST: grNewPlayerSync=%d &gameConfig=%08x forced=%d (s226, not for commit)\n",
            (int)gameConfig.grNewPlayerSync, (u32)&gameConfig, forced);
    }
#endif
}

void hjLogWhere(void)
{
    static int lastTop = -2;
    static int lastIn  = -2;
    int top = -1, w, i, ig = isInGame(), im = isInMenus();

    if (!im) {
        top = -1;                       // in game: the UI slots are reused memory
    } else {
        for (w = 2; w >= 0 && top < 0; --w)      // topmost slot wins
            for (i = 0; i <= 42; ++i)
                if (uiGetActiveMenu(i, w)) { top = i; break; }
    }

    hjTestForceSync();

    if (top == lastTop && ig == lastIn)
        return;
    lastTop = top;
    lastIn  = ig;

    if (!im && ig)
        HOTJOIN_LOG("where: IN_GAME\n");
    else if (top >= 0)
        HOTJOIN_LOG("where: %s (id %d) inGame=%d\n", hjMenuName(top), top, ig);
    else
        HOTJOIN_LOG("where: LOADING/NONE inGame=%d menus=%d\n", ig, im);
}

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
            // s163: 4, not 5. This is the stuck-at-3 safety net, and it must leave us in the
            // state the election can act on. Writing 5 here made us permanently unelectable,
            // which is the same mistake as the announce block above.
            *(int*)(mine + 0x08) = 4;
            *(int*)(mine + 0x18) = 1;
            internal_hjPublishMyIndex((void*)peers, *(int*)(peers + 0x404));
            {
                u32 nctx = *(u32*)HJ_NET_CTX_PTR;
                int gateA = nctx ? *(int*)(nctx + 0x10C) : -1;
                int r = internal_hjCheckAllConnected();
                HOTJOIN_LOG("promote: myRec %08x 3 -> 4 after %d frames; idx %d; p0 t08=%d f1C=%d p408=%d p43C=%d gateA=%d check=%d sm=%d gs=%p\n",
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

    // s163/s163-A: DO NOT write 5 here any more.
    // This block's own gate is `mine08 == 4`, which means the ENGINE has just promoted us
    // 3 -> 4 by itself (observed live: mine08 read 3 at 75573.5156 and this block fired at
    // 75573.7188). Writing 5 here consumed that state immediately -- and the election at
    // 0x00172898 considers ONLY peers with t08 == 4, so it could never elect us. We were
    // destroying the candidate we had just been handed.
    // The value is ALSO the inner message type the sender reads from myRecord->0x08, so it is
    // set to 5 only momentarily around each send below and left at 4 the rest of the time.
    // REGRESSION FIX, s163-B. `!hjAnnounceDone` MUST be in this gate.
    // The old code wrote `mine08 = 5` here, which made this block's own `mine08 == 4` gate
    // false -- so that write was an IMPLICIT LATCH, not just a state change. Removing it in
    // 20260929a left the gate true forever, so the block re-ran EVERY FRAME and reset
    // hjAnnounceSends and hjAnnounceTick each time. Measured consequences: the send counter
    // never advanced past 1/240, the tick reset to 0 made `--tick <= 0` true immediately, and
    // HJ_ANNOUNCE_MAX_SENDS was therefore NEVER reached -- so we broadcast at frame rate
    // indefinitely instead of 240 times. Unbounded traffic, caused by me.
    // Found by the mbp agent from a before/after difference in the counter, which it flagged
    // without being able to place the cause.
    if (!hjAnnounceDone && *(u32*)(peers + 0x438) == 0 && *(int*)(mine + 0x08) == 4) {
        *(int*)(mine + 0x18) = 1;
        hjAnnounceSends = 0;
        hjAnnounceTick = 0;
        hjAnnounceDone = 1;
        HOTJOIN_LOG("announce: myRecord %08x armed at 0x08=4, 0x18 -> 1 (p438=0), sending\n",
            mine);
    }

    // Retransmit: these are UDP datagrams and this protocol demonstrably depends on
    // repetition (the game's own peer-connect request retries every ~3 s). Space them
    // out rather than firing the whole budget in consecutive frames.
    // Only the machine that PERFORMED the 4 -> 5 promotion announces. The host's own
    // record already sits at 5 from the moment it opens the game, so without this gate
    // the host also ran the send loop -- 240 unsolicited type-5 broadcasts per game,
    // from a machine that has nothing to announce. That is traffic vanilla never emits.
    // Gate accepts 4 OR 5: the record now rests at 4 between sends (s163).
    if (hjAnnounceDone
        && (*(int*)(mine + 0x08) == 5 || *(int*)(mine + 0x08) == 4)
        && hjAnnounceSends < HJ_ANNOUNCE_MAX_SENDS) {
        if (--hjAnnounceTick <= 0) {
            hjAnnounceTick = (hjAnnounceSends < HJ_ANNOUNCE_BURST_SENDS)
                           ? HJ_ANNOUNCE_BURST_PERIOD : HJ_ANNOUNCE_PERIOD;
            ++hjAnnounceSends;
            // The sender at 0x14bdb0 reads the outbound inner type straight out of
            // myRecord->0x08 (14be08 `lbu v1,8(s0)` -> payload[0]), so the wire type and the
            // state the election reads are THE SAME FIELD. Hold 5 across the send so the wire
            // is byte-identical to before -- receivers keep getting inner-type-5, which is what
            // sets their p408 and was measured working 112 times -- then drop back to 4 so we
            // remain electable.
            *(int*)(mine + 0x08) = 5;
            internal_hjSendPeerMsg((void*)peers, -1);
            *(int*)(mine + 0x08) = 4;
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
#define HJ_NW_PDATA        (0x04)
#define HJ_NW_NAME         (0x1b0)   // s224: needed by the release path, see below

// Slots reaped and not yet proven to have come back, plus the tNW_Player sequence
// each held at the moment it was reaped. See hjHostAdoptPeers for why.
int hjReapBlocked = 0;
int hjReapBlockFrames[GAME_MAX_PLAYERS];

// Per-slot: the tNW_Player pad sequence at the moment the slot was reaped, and a
// bit saying we have not yet seen it move. Consumed by hjHostSpawnRemotes.
int hjSpawnBlocked = 0;
int hjSpawnSeq[GAME_MAX_PLAYERS];
// HJ_REAP_BLOCK_MAX -- how long the re-adopt block may hold before giving up.
//
// RAISED 900 -> 3600 on 2026-09-26, because 900 caused the exact churn it was meant to
// prevent. Measured on the SIGSTOP vanished-client round:
//
//     8531.82  reap + release slot 1            (block armed)
//     8546.84  "unblocked on timeout after 900 frames"   = 901 frames, 15.02 s
//              -> adopt immediately rewrote roster slot 1, n -> 2, WITH NO PEER THERE
//     8566.67  "unblocked, stale peer cleared"   = 2091 frames, 34.85 s
//              -> roster corrected back to n = 1
//
// 19.8 s of PHANTOM SECOND PLAYER. The escape hatch opened while the departing peer record
// was still sitting at state 5, and the adopt loop's `state == 5` test cannot tell a dying
// record from a fresh one -- so it adopted the corpse. The frozen client had not sent
// anything and did not resume until ~62 s later.
//
// THE TIMEOUT WAS GUARDING AGAINST A DEADLOCK THAT CANNOT HAPPEN HERE, and the comment in
// hjHostAdoptPeers already says why: "the stale one is torn down independently of anything we
// do". A gate waiting on someone else's teardown cannot deadlock on our own inaction -- unlike
// the pad-sequence gate of section 89, which genuinely could. So this hatch was belt-and-braces
// against a risk the same file argues away, and it became the bug.
//
// 3600 frames = 60 s, against a measured teardown of 34.85 s. Kept rather than removed because
// "peerclose always arrives" is observed, not guaranteed, and a slot blocked forever would stop
// that player ever rejoining. But it is now an ANOMALY threshold, not a routine one: if it ever
// fires, the peer record outlived its own teardown by 25 s and that is worth knowing about.
#define HJ_REAP_BLOCK_MAX  (3600)

// Identical redefinitions, same reason as the block above: these are needed here as
// well as beside hjDumpNWPlayers, and the reaper lives 800 lines further down.
#define HJ_NW_CID          (0x00)
#define HJ_NW_SPAWNED      (0x1a2)
#define HJ_NW_CBCALLED     (0x1a6)

extern void internal_hjDeleteRemotePlayer(void * nwp);   // 0x199a40

// ---------------------------------------------------------------------------
// hjReleaseRemoteSlot -- the ONE teardown, shared by both paths that free a slot.
//
// This function exists because the two paths drifted apart and the divergence was the
// bug, twice. The stall-driven reaper (hjHostReapRemotes) had the complete sequence; a
// roster-driven rearm added in hjHostAdoptPeers on 2026-09-11 reimplemented most of it
// by hand, omitted two steps, and produced a hard regression in which only the first
// late join ever spawned. Reverting that rearm then exposed the opposite failure: with
// nothing clearing the latches on a clean leave, the rejoin never got adopted at all.
//
// Measured, agent hosting, 2026-09-12. Clean leave at 325.54 (sessend msg=3,
// peerclose t08=2) with NO reap line anywhere in the run, then the rejoin:
//
//     347.48  introduce  p404=0 p408=0 ret=1040296128     <- the introduce is FIXED
//     no adopt line, no spawn line, for 105+ s
//     nwp[1]  cid=1 pData=01f7b680 (new) bSpawned=1 cbCalled=0 padSeq=-1
//
// So the engine re-registered the slot on its own, and both of OUR latches were still
// set from the first join: hjAdopted made hjHostAdoptPeers skip the roster write (it is
// write-once per slot) and hjSpawned made hjHostSpawnRemotes skip the slot before it
// even reached the sequence gate. padSeq stuck at the -1 sentinel is downstream of
// that, not a separate fault -- with PlayerClients[1] still -1 the host has no reason
// to take the joiner's pad stream. The first join proves the ordering:
// adopt 184.16 -> pads flow -> spawn 194.86.
//
// Both latches, or neither. Clearing hjAdopted alone regresses to "adopt then nothing";
// clearing hjSpawned alone leaves the roster wrong.
//
// The delete invoker is conditional on cbCalled, which is our own marker that 0x1999b8
// ran. With it clear there is no constructed player to destroy, and calling 0x199A40
// anyway risks tearing down a registration that has already come back -- exactly the
// race this path runs into, since it fires within ~50 ms of the session end.
// ---------------------------------------------------------------------------
void hjReleaseRemoteSlot(int cid, GameSettings * gs, const char * why)
{
    u32 nwp;
    int k, n = 0;

    if (cid < 0 || cid >= GAME_MAX_PLAYERS)
        return;
    nwp = HJ_NWPLAYER_BASE + (cid * HJ_NWPLAYER_STRIDE);

    HOTJOIN_LOG("release: slot %d (%s) cid=%d pData=%08x spawned=%d cbCalled=%d seq=%d\n",
        cid, why, *(int*)(nwp + HJ_NW_CID), *(u32*)(nwp + HJ_NW_PDATA),
        (int)*(short*)(nwp + HJ_NW_SPAWNED), (int)*(short*)(nwp + HJ_NW_CBCALLED),
        *(int*)(nwp + HJ_NW_SEQ));

    // s263. GUARD THE DELETE, NOT THE ELIGIBILITY.
    //
    // s258 widened hjPeerClosedRemote's gate so this function finally runs on a departure
    // (pData is already 0 by then, so the old `spawned && pData` test never fired). That
    // fixed the silent split -- and it also means this delete now runs in cases it never
    // ran in before, specifically with pData ALREADY ZERO. The old eligibility test was
    // accidentally doing double duty as a precondition for the delete invoker.
    //
    // Two of three machines then hung on 20261023a-splitfix, both of them hosts, with
    // NULL+small-offset faults (addr=0x17b, 0xc, 0x4) at PCs OUTSIDE our address range.
    // I first read "not our PC" as exculpatory. It is not: a faulting instruction in
    // vanilla code says nothing about who zeroed the pointer it dereferenced, and this
    // function zeroes a great deal -- nwp+pData, nwp+seq, every gs->Player* entry for the
    // slot -- besides invoking 0x199a40. Patch code clearing state that vanilla code still
    // expects produces precisely a NULL-base fault at a vanilla PC. TLB misses are not
    // observed on this title outside the patch, and the previous build did not do this.
    //
    // So require an actual Player object, not merely cbCalled. 0x199a40 exists to tear a
    // constructed player down; handing it a slot whose net record is already gone is
    // asking it to walk pointers nobody has set. cbCalled only says the constructor ran
    // ONCE, which stays true after a teardown -- it is a history bit, not a liveness bit.
    //
    // The latch clearing below still happens unconditionally, which is what actually
    // repairs s254: the rejoin needs hjSpawned/hjAdopted cleared whether or not there was
    // a body to delete.
    //
    // TODO (s263 guard, 2026-10-25): THIS BRANCH HAS NEVER FIRED. Decide to keep or remove
    // once there is evidence either way -- do not assume it is protecting anything.
    //
    // Measured across a full three-client night on 20261024a-deleteguard: `SKIPPING delete`
    // = 0 on every machine across FIVE departure modes -- non-host observer of a peer
    // leaving, surviving non-host when the host leaves, the host's own peer-closed path, a
    // hard client kill (PCSX2 killed outright), and a two-peer host quit. In every one the
    // Player object still existed, so the delete was permitted exactly as the old code did.
    //
    // HOW WE THEORISE IT WOULD BE REACHED, so a future reader can test it rather than guess:
    // the branch needs cbCalled set with all[cid] already NULL. A double release cannot do
    // it -- 0x199A40 clears netClientIndex, bSpawned and bCallbackCalled, which is why a
    // late second peerclose reads `cid=-1 pData=00000000 spawned=0 cbCalled=0` and comes out
    // `elig=0` (measured: mbp's reaper released slot 0, the real peerclose arrived 34.8 s
    // later and declined). So the plausible route is the Player object being freed WITHOUT
    // the delete invoker running -- a level load or engine-side teardown that frees the
    // player array while leaving our nwp record intact, after which cbCalled is a stale
    // history bit (it records that the constructor ran once; it is NOT a liveness bit).
    //
    // To reproduce deliberately: have a remote spawn, then force a level transition or an
    // engine teardown that clears the player array, then trigger a departure for that slot
    // and check for the line. If that cannot be made to happen, the branch is dead code and
    // should be removed along with the playerGetAll() call it costs per release.
    {
        Player ** all = playerGetAll();
        int haveBody = all && all[cid];
        if (*(short*)(nwp + HJ_NW_CBCALLED) && haveBody) {
            internal_hjDeleteRemotePlayer((void*)nwp);
        } else if (*(short*)(nwp + HJ_NW_CBCALLED)) {
            HOTJOIN_LOG("release: slot %d SKIPPING delete -- cbCalled set but no Player "
                "(all=%08x) (s263 guard)\n", cid, (u32)all);
        }
    }

    hjSpawned &= ~(1 << cid);
    hjAdopted &= ~(1 << cid);

    hjReapBlocked |= (1 << cid);
    hjReapBlockFrames[cid] = 0;
    hjSpawnBlocked |= (1 << cid);
    hjSpawnSeq[cid] = 0;

    if (gs) {
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
    }

    *(u32*)(nwp + HJ_NW_PDATA) = 0;
    *(int*)(nwp + HJ_NW_SEQ) = 0;

    // s224. Clearing gs->PlayerNames above is NOT enough. hjHostRefreshNames copies
    // nwp+0x1b0 back into the roster every frame for every occupied non-self slot, so
    // leaving the departed player's name here means the NEXT occupant of this slot
    // inherits it. The joiner's own hjSendMyName does fight back, producing an
    // alternating correct/stale pair in the log, but HJ_NAME_SENDS is finite: the
    // corrections run out and the cycle terminates on the STALE value. Worse, it is not
    // host-local -- a client joining later reads the stale string in its own freshly
    // built nw record, so it propagates through the bootstrap data.
    //
    // Observed 2026-10-16: maxMac3 left, maxTest2 took slot 1, and every client in the
    // match -- including one that joined afterwards and never saw the departure --
    // called maxTest2 'maxMac3' permanently.
    for (k = 0; k < 16; ++k)
        *(char*)(nwp + HJ_NW_NAME + k) = 0;

    HOTJOIN_LOG("release: slot %d done, n -> %d, adopt+spawn latches rearmed\n", cid, n);
}

// ---------------------------------------------------------------------------
// hjPeerClosedRemote -- the OFF-HOST teardown (sections 96, 101-A, 109).
//
// A non-host never destroys a departed remote player. At three players that leaves a ghost:
// a live, frame-ticked moby with a HUD arrow over it. At two players with the HOST leaving
// it strands the survivor -- measured: roster still [0,1], n=2, the host's player still
// spawned with a live pData, and no teardown of any kind for as long as anyone watched.
//
// That is permanent BY CONSTRUCTION. Both existing triggers are unreachable off-host:
//   roster-driven  hjHostAdoptPeers releases when the HOST writes PlayerClients[i] = -1.
//                  When the host is the departing party, nobody is left to write it.
//   stall-driven   hjHostReapRemotes returns immediately on !gameAmIHost().
// peerclose is the one departure signal that does reach a non-host, its hook is already
// installed on both call sites, and that hook is not host-gated. So trigger off it.
//
// EVERY CLAUSE OF THE FIRST VERSION OF THIS GATE WAS WRONG, and shipping it log-only is the
// only reason we know. What the measurements corrected:
//
//   t08 == 5 REQUIRED  ->  REMOVED. Taken from an old note reading "close at t08=5, reap
//     0.9 s later". Measured: a clean leave closes at t08 = 2 on BOTH roles (host ev=1,2;
//     joiner ev=1). Requiring 5 meant this could never fire on the case it was written for.
//     t08 is logged, never tested.
//
//   WHY REMOVING IT IS SAFE, the part that needs care: state 2 is ALSO the initialised
//     state an ARRIVING peer passes through (0x17262c), and firing a teardown at an
//     arriving peer is the section-89 mistake a third time. What separates arrival from
//     departure is not the peer state -- it is whether a player has been CONSTRUCTED. An
//     arriving peer has spawned=0, pData=0; a departing one has spawned=1 and a live pData.
//     `spawned && pData` is the real discriminator and it was already here.
//
//   forceDelete, TO BEAT THE cbCalled GUARD  ->  DROPPED, and its premise was false. The
//     claim was that only the host runs 0x1999b8, so a non-host's cbCalled stays 0 forever
//     and the guard "reduces the teardown to a roster edit -- that IS the ghost". Measured
//     on the joiner: cbCalled=1 while its log contains ZERO spawn, adopt or release lines.
//     The ENGINE writes +0x1A6, not us. The guard passes on its own and needed no override,
//     and the ghost is not caused by it -- it is caused by no trigger existing off-host.
//
// THE HOST EXCLUDES ITSELF WITH NO HOST GATE. Measured ordering on a host:
//     1262.8511  release: slot 1 (roster freed the slot)
//     1262.8855  peerclosed: idx=1 ... spawned=0 pData=00000000      <- 34 ms later
// The roster path wins and has already cleared those fields, so this declines by itself.
// Off-host they are still set and it fires. One rule, correct on both roles -- this file's
// two historical teardown bugs were both caused by having two rules that drifted apart.
//
// STILL UNVERIFIED: this repairs the roster and the moby. It does NOT repair p408, which in
// the host-leaves case still points at a departed peer. Whether the survivor becomes
// joinable again, or merely stops rendering a corpse, is open. Do not report the stranded
// client as fixed until a rejoin against a survivor has actually been observed.
// ---------------------------------------------------------------------------
static int hjPeerCloseReleases = 0;
// s258-B: hjPeerCloseReleases used to be bumped on every peerclose EVENT, eligible or not,
// and then compared against the cap -- so eight close events of any kind disabled the
// teardown for the rest of the session. That never showed up while the eligibility test
// was broken (nothing was being released anyway), but with s258 the path actually fires,
// and one 2026-10-22 session logged ten releases. Capping on events rather than on the
// thing being capped is the same error as the p408 budget that burned 40 on one run and
// then logged nothing for eleven minutes. Count releases for the cap, events for the log.
static int hjPeerCloseEvents = 0;
#define HJ_PEERCLOSE_MAX  (32)

void hjPeerClosedRemote(int idx, int t08)
{
    GameSettings * gs = gameGetSettings();
    u32 ctx   = *(u32*)HJ_NET_CTX_PTR;
    u32 peers = ctx ? *(u32*)(ctx + HJ_CTX_PEERS) : 0;
    u32 nwp;
    int spawned, cbCalled, eligible;
    u32 pData;

    if (idx < 0 || idx >= GAME_MAX_PLAYERS)
        return;

    nwp      = HJ_NWPLAYER_BASE + (idx * HJ_NWPLAYER_STRIDE);
    spawned  = (int)*(short*)(nwp + HJ_NW_SPAWNED);
    pData    = *(u32*)(nwp + HJ_NW_PDATA);
    cbCalled = (int)*(short*)(nwp + HJ_NW_CBCALLED);

    // s258. `spawned && pData` was wrong, and it is the whole silent-split bug.
    //
    // The comment above justifies it as "an arriving peer has spawned=0, pData=0; a
    // departing one has spawned=1 and a live pData". The second half does not hold.
    // MEASURED on a non-host at a clean departure (2026-10-22, round 2):
    //     peerclosed: idx=2 ... pData=00000000 spawned=1 cbCalled=1 seq=171 elig=0
    // pData is ALREADY zero by the time this hook runs, so the test fails on exactly the
    // departure it was written to catch, every time. The non-host teardown therefore
    // never fired, hjSpawned was never cleared, and hjHostSpawnRemotes skipped the slot
    // forever at the rejoin -- the departed player was invisible on that client for the
    // rest of the match, with a correct roster and a correct name. Controlled on one
    // machine in one session: the slot whose latch was clear stranded, a slot whose latch
    // was set recovered 3/3.
    //
    // The discriminator the comment actually wants is "has a player been CONSTRUCTED for
    // this slot on THIS machine", and we hold that directly: hjSpawned is set by
    // hjHostSpawnRemotes, which is deliberately NOT host-gated, so it is set on every
    // machine that built the remote. cbCalled is the engine's own equivalent.
    //
    // Still safe against the arriving-peer teardown that this file has got wrong three
    // times: an arriving peer has hjSpawned clear AND cbCalled 0 AND pData 0, so it is
    // ineligible until something has actually built it.
    eligible = (idx != gameGetMyClientId())
               && spawned
               && (pData || cbCalled || (hjSpawned & (1 << idx)));

    ++hjPeerCloseEvents;
    HOTJOIN_LOG("peerclosed: idx=%d t08=%d host=%d p404=%d myCid=%d "
        "nwp[%d] cid=%d pData=%08x spawned=%d cbCalled=%d seq=%d "
        "roster=[%d,%d,%d,%d] n=%d elig=%d ev=%d\n",
        idx, t08, gameAmIHost(),
        peers ? *(int*)(peers + HJ_PEERS_MYIDX) : -1,
        gameGetMyClientId(),
        idx, *(int*)(nwp + HJ_NW_CID), pData, spawned, cbCalled,
        *(int*)(nwp + HJ_NW_SEQ),
        gs ? gs->PlayerClients[0] : -9, gs ? gs->PlayerClients[1] : -9,
        gs ? gs->PlayerClients[2] : -9, gs ? gs->PlayerClients[3] : -9,
        gs ? gs->PlayerCount : -9,
        eligible, hjPeerCloseEvents);

    if (!eligible)
        return;

    ++hjPeerCloseReleases;

    // Safety valve. An unbounded teardown is how this file once produced a destroy/recreate
    // cycle against a live player. Eight is far more leaves than a test round needs and
    // small enough that a runaway stops being silent.
    if (hjPeerCloseReleases > HJ_PEERCLOSE_MAX) {
        HOTJOIN_LOG("peerclosed: slot %d NOT released, cap %d reached\n",
            idx, HJ_PEERCLOSE_MAX);
        return;
    }

    hjReleaseRemoteSlot(idx, gs, "peer closed");
}

// ---------------------------------------------------------------------------
// s208: deliver the joiner's team choice TO THE HOST, before it adopts.
//
// WHY. s207 let the joiner write its own gs->PlayerTeams[] every frame. That changed the
// byte and nothing else. Measured: the joiner read 0 (Blue) with the log line proving our
// write, while the HOST held 1 (Red) for 30 consecutive samples over 2.5 minutes -- a
// joiner-side write does NOT propagate upward. Worse, the joiner's OWN skin rendered red
// and it spawned at the RED base, so even locally the derived state follows the HOST's
// value, not the byte it had just written.
//
// So teams are host-authoritative in EFFECT. The choice has to reach the host, and it has
// to be there before the player object is built -- which is why s206 auto-assign works:
// it writes at adopt, on the owning machine, before anything derives from it.
//
// This uses the patch's existing client-to-client custom message facility (the same one
// vote-to-end and playersync use), so no server change is needed.
#define HJ_TEAMPREF_NONE   (-1)
extern PatchConfig_t config;      // defined in main.c
extern int hjTeamChoice;          // defined just below, in the s207 block
static int hjPeerTeamPref[GAME_MAX_PLAYERS];
static int hjTeamPrefInit = 0;
static int hjTeamPrefSendTick = 0;
// s209-D: the ONE place the joiner's wanted team is resolved. -1 = Auto.
//
// The pre-join prompt is now the only source. The config option that used to back this
// was scaffolding: it existed so the host-side plumbing could be tested while the dialog
// was broken, and it was wrong as a design -- the team is a per-join decision, so a value
// that persists across joins (or, worse, across boots) is not what anyone wants. Choosing
// "Auto" in the prompt must also MEAN auto, which a config fallback would quietly
// override.
static int hjTeamSelection(void)
{
    return hjTeamChoice;
}

static int hjPrefBlockedLogged = 0;   // s208-D, rearmed on the edge into the game
static int hjPrefSentLogged    = 0;   // s208-D, ditto

static void hjTeamPrefEnsureInit(void)
{
    int i;
    if (hjTeamPrefInit) return;
    for (i = 0; i < GAME_MAX_PLAYERS; ++i)
        hjPeerTeamPref[i] = HJ_TEAMPREF_NONE;
    hjTeamPrefInit = 1;
}

int hjOnTeamPrefMsg(void * connection, void * data)
{
    HjTeamPref_t msg;

    hjTeamPrefEnsureInit();
    memcpy(&msg, data, sizeof(msg));

    {
        // s208-D: log the first receipts UNCONDITIONALLY. The change-gated log below
        // cannot distinguish "nothing arrived" from "arrived with a value we already
        // held" -- and "no teampref line on the host" was the whole finding last run.
        static int rxLogged = 0;
        if (rxLogged < 12) {
            ++rxLogged;
            HOTJOIN_LOG("teampref RX %d: cid=%d team=%d\n",
                rxLogged, msg.ClientId, msg.Team);
        }
    }
    if (msg.ClientId >= 0 && msg.ClientId < GAME_MAX_PLAYERS
        && (msg.Team == 0 || msg.Team == 1)) {
        if (hjPeerTeamPref[msg.ClientId] != msg.Team) {
            hjPeerTeamPref[msg.ClientId] = msg.Team;
            HOTJOIN_LOG("teampref: client %d wants team %d\n", msg.ClientId, msg.Team);
        }
    }
    return sizeof(HjTeamPref_t);
}

// Broadcast our own preference while we are joining and shortly after. Repetition matters:
// the host must have it before hjHostAdoptPeers writes the slot, and we do not know exactly
// when that lands. Cheap enough to send at 1 Hz.
void hjSendTeamPref(void)
{
    HjTeamPref_t msg;
    void * conn;
    int want;

    hjTeamPrefEnsureInit();

    // -1 = Auto, which never announces, so a player who leaves the prompt alone keeps the
    // s206 host-side balance untouched.
    want = hjTeamSelection();
    {
        static int wantLogged = -2;
        if (want != wantLogged) {
            wantLogged = want;
            HOTJOIN_LOG("teampref: want=%d (choice=%d host=%d)\n",
                want, hjTeamChoice, gameAmIHost());
        }
    }
    if (want < 0)
        return;
    if (gameAmIHost())              // the host applies its own pick directly
        return;

    // 15 frames = ~4 Hz. 1 Hz was too slow to be safe: adopt can land within a second of
    // the peer reaching state 5, and if the preference arrives AFTER adopt the host has
    // already written the balanced team. Cheap message, so send it often while joining.
    if (--hjTeamPrefSendTick > 0)
        return;
    hjTeamPrefSendTick = 15;

    conn = netGetDmeServerConnection();
    msg.ClientId = gameGetMyClientId();
    msg.Team     = want;

    // s208-D DIAGNOSTIC. s208-C capped its log at 12 lines and ALL TWELVE were spent in
    // the menus, where conn==0 and cid==-1 -- so the run proved only that the config was
    // read, and said nothing about the window that actually matters (post-adopt, when
    // conn and cid do exist). Three budgets, because a single one is exactly the trap
    // s208-C fell into: the menus phase lasts MINUTES (navigating to the lobby, opening
    // the config menu, finding the game), so any budget shared with the menus is spent
    // long before the join and proves nothing about the join. The in-game budgets are
    // therefore rearmed on the EDGE into the game.
    {
        static int wasInGame = 0;
        int nowInGame = isInGame();
        if (nowInGame && !wasInGame) {
            hjPrefBlockedLogged = 0;
            hjPrefSentLogged    = 0;
            HOTJOIN_LOG("teampref: entered game, diagnostic budgets rearmed\n");
        }
        wasInGame = nowInGame;
    }

    if (!conn || msg.ClientId < 0) {
        static int blockedTick = 0;
        if (--blockedTick <= 0) {
            blockedTick = 8;            // 8 * 15 frames = ~2 s
            if (hjPrefBlockedLogged < 40) {
                ++hjPrefBlockedLogged;
                HOTJOIN_LOG("teampref BLOCKED %d: want=%d cid=%d conn=%08x inGame=%d menus=%d\n",
                    hjPrefBlockedLogged, want, msg.ClientId, (u32)conn,
                    isInGame(), isInMenus());
            }
        }
        return;
    }

    // Send on BOTH paths. netBroadcastCustomAppMessage goes out via
    // netBroadcastMediusAppMessage; the vote-to-end code in main.c uses the OTHER entry
    // point, netSendCustomAppMessage(conn, -1, ...), and that one is known to work in
    // this patch today. Trying only the broadcast is an untested assumption about which
    // path the DME relays for a client that has just hot-joined -- and s200 showed the
    // DME treats a hot-joiner's traffic differently from an ordinary client's. Both are
    // cheap; the two return values say which one, if either, got off the machine.
    {
        int host = gameGetHostId();
        int rcB  = netBroadcastCustomAppMessage(conn, CUSTOM_MSG_ID_HJ_TEAM_PREF,
                                                sizeof(msg), &msg);
        // s208-E: also address the host directly, which is exactly what the name sync
        // (hjSendMyName) does and that one is known to arrive. Keep the broadcast as
        // well: in staging gameGetHostId() may not be resolved yet.
        int rcS  = netSendCustomAppMessage(conn, host, CUSTOM_MSG_ID_HJ_TEAM_PREF,
                                           sizeof(msg), &msg);
        if (hjPrefSentLogged < 12) {
            ++hjPrefSentLogged;
            HOTJOIN_LOG("teampref SENT %d: want=%d cid=%d host=%d conn=%08x rcB=%d rcS=%d inGame=%d menus=%d\n",
                hjPrefSentLogged, want, msg.ClientId, host, (u32)conn, rcB, rcS,
                isInGame(), isInMenus());
        }
    }
}

// s208-B: apply a preference that arrived AFTER adopt.
//
// The joiner cannot guarantee its broadcast reaches us before hjHostAdoptPeers writes the
// slot. But the team is not CONSUMED at adopt -- it is consumed when the player object is
// built, which s206 measured at ~11.3s after adopt (and is why auto-assign gets skin and
// spawn base right). So a preference landing inside that window can still take effect if we
// rewrite the roster entry.
//
// Host-only, and only while the slot is adopted but not yet spawned.
void hjHostApplyLateTeamPref(void)
{
    GameSettings * gs;
    int i;

    if (!gameAmIHost() || !isInGame())
        return;
    hjTeamPrefEnsureInit();

    gs = gameGetSettings();
    if (!gs)
        return;

    for (i = 0; i < GAME_MAX_PLAYERS; ++i) {
        if (gs->PlayerClients[i] < 0)
            continue;
        if (hjPeerTeamPref[i] == HJ_TEAMPREF_NONE)
            continue;
        if (gs->PlayerTeams[i] == (short)hjPeerTeamPref[i])
            continue;

        HOTJOIN_LOG("teampref: LATE apply, slot %d team %d -> %d\n",
            i, (int)gs->PlayerTeams[i], hjPeerTeamPref[i]);
        gs->PlayerTeams[i] = (short)hjPeerTeamPref[i];
    }
}

// ---------------------------------------------------------------------------
// s207: PRE-JOIN TEAM SELECTOR.
//
// Goal: auto-balance stays the default (s206), but a player may override it to Blue or Red
// before joining. A hot-joiner has no staging screen -- that is the whole reason it could
// never pick a team -- so the last UI it owns is the GAME DETAILS screen it is looking at
// when it presses JOIN. We raise the picker there.
//
// The dialog machinery is NOT staging-bound: uiShowSelectDialog renders into the fixed
// UI_DIALOG_A0 object and consults no staging state. openTeamsOptions only happens to be
// CALLED from the staging loop; it is not confined to it.
//
// This records the CHOICE only. Applying it is separate, because the host writes
// gs->PlayerTeams[] at adopt time and a joiner's own copy is rebuilt during the join.
//
// -1 = auto (host balances, s206), 0 = Blue, 1 = Red.
int hjTeamChoice = -1;
static int hjTeamPromptShown = 0;
static int hjTeamPromptDelay = 0;   // s209-E, frames since GAME_DETAILS opened

// s209-D: GAME_DETAILS can occupy any of the three active-menu slots depending on what it
// was opened over. Ask all three.
static int hjGameDetailsOpen(void)
{
    int w;
    for (w = 0; w < 3; ++w)
        if (uiGetActiveMenu(UI_MENU_GAME_DETAILS, w))
            return 1;
    return 0;
}

void hjTeamSelectPrompt(void)
{
    int sel;

    // s209-D: the choice belongs to ONE join. Clear it on the way out of a game, so a
    // player who hot-joins as Red, leaves, and then takes some other route back in (Quick
    // Play, an invite -- anything that does not pass through GAME DETAILS) is not silently
    // still Red. Without this the variable outlives the decision it recorded.
    {
        static int wasInGame = 0;
        int nowInGame = isInGame();
        if (wasInGame && !nowInGame) {
            if (hjTeamChoice >= 0)
                HOTJOIN_LOG("teamsel: left game, choice %d -> auto\n", hjTeamChoice);
            hjTeamChoice = -1;
            hjTeamPromptAsked = 0;
        }
        wasInGame = nowInGame;
    }

    // s207-D DIAGNOSTIC. Two axes, not one.
    //
    // uiGetActiveMenu(UI, whichMenu) reads *(UI_ACTIVE_MENU_1 + whichMenu*4) and compares
    // it against uiGetMenu(UI). There are THREE active-menu slots (0x01c5c110/114/118) and
    // my earlier probes only ever checked slot 0 -- so an all-zero result could have meant
    // "wrong id" OR "right id, wrong slot", and I could not tell which. Scan both axes, and
    // log the raw slot pointers too so that even a total miss is diagnosable.
    {
        static u32 lastP0 = 0xffffffff, lastP1 = 0xffffffff, lastP2 = 0xffffffff;
        u32 p0 = *(u32*)0x01c5c110, p1 = *(u32*)0x01c5c114, p2 = *(u32*)0x01c5c118;
        static int logged = 0;

        if ((p0 != lastP0 || p1 != lastP1 || p2 != lastP2) && logged < 400) {
            int i, w;
            lastP0 = p0; lastP1 = p1; lastP2 = p2;
            ++logged;
            HOTJOIN_LOG("menuscan: slots = %08x %08x %08x\n", p0, p1, p2);
            for (w = 0; w < 3; ++w) {
                for (i = 0; i <= 42; ++i) {
                    if (uiGetActiveMenu(i, w)) {
                        HOTJOIN_LOG("menuscan:   id %d ACTIVE in slot %d\n", i, w);
                        ++logged;
                    }
                }
            }
        }
    }

    // s209-D: check ALL THREE active-menu slots, not slot 0.
    //
    // This one wrong index is why the dialog never fired in any build. The s207-D scan
    // above finally showed why, decoded against the menu enum:
    //     [407.68] slots = 01d86248 01d40578 00000000
    //                id 31 (CITY) ACTIVE in slot 0
    //                id 32 (UNK_2) ACTIVE in slot 0
    //                id 16 (GAME_DETAILS) ACTIVE in slot 1   <-- GAME INFO
    // GAME_DETAILS opens OVER the city screen, so the city keeps slot 0 and the details
    // menu lands in slot 1. Nothing about the gate was conceptually wrong; it was
    // looking at the wrong one of three places.
    if (!hjGameDetailsOpen()) {
        // Rearm whenever we are not on the screen, so re-entering the game list asks
        // again rather than silently reusing a choice made for a different game.
        hjTeamPromptShown = 0;
        hjTeamPromptDelay = 0;
        // s239: AND the latch that actually gates the prompt. This block already said
        // "rearm whenever we are not on the screen" and then rearmed two OTHER flags,
        // leaving hjTeamPromptAsked -- the one patchGameDetails tests -- untouched.
        //
        // This is also why the s232 fix did nothing: that block sits BELOW this early
        // return, so when the player backs out to CITY and hjGameDetailsOpen() goes
        // false, we return here and never reach it. Measured 2026-10-21 on two
        // independent clients: prompt appears on first open, never again on reopen.
        // My fix was correct code placed where it could not run -- the same mistake as
        // s225, where the nwp clear sat in a function the host never calls.
        //
        // Cannot loop (the s210-B failure): while the dialog is up, GAME_DETAILS is
        // still in an active slot, so hjGameDetailsOpen() is true and we never get here.
        hjTeamPromptAsked = 0;
        return;
    }
    // s209-G: the dialog is NOT raised from here any more.
    //
    // Calling uiShowSelectDialog from main() wedges the patch. Measured: with the slot
    // gate fixed the prompt did fire, but the last HJ log line of ANY kind was t=376.03,
    // and 40 s of game time later the EE was still running and rendering while our
    // per-frame hook had never executed again. The call does not return. The first two
    // builds hid this by taking the immediate -1 as an answer and never calling twice.
    //
    // Every working uiShowSelectDialog call site in this patch (openTeamsOptions,
    // openPlayerOptions) runs inside patchStaging(ui, pad) -- a pad handler, where the
    // UI owns the frame. main() is not that context. The prompt now lives in
    // patchStaging; see hjStagingTeamPrompt.
    //
    // What survives here is the rearm bookkeeping: being on GAME DETAILS means the
    // player is picking a game, so the next staging entry must ask again.
    // s210-B: arm on the EDGE into GAME DETAILS, not every frame while it is open.
    //
    // The level-triggered version looped: the dialog blocks, so main() does not run while
    // it is up; the moment it returns, this line saw GAME DETAILS still open, cleared the
    // flag, and patchGameDetails raised the dialog again. Measured -- "raising prompt from
    // GAME DETAILS" at 383.39, answered at 429.17, raised again at 429.57.
    //
    // s232: ARM ON LEAVING THE SCREEN, not on arriving at it. The edge above used
    // hjGameDetailsOpen(), which is true if GAME_DETAILS sits in ANY of the three
    // active-menu slots -- and backing out to CITY leaves it registered in one. So
    // nowOnDetails never went false, there was no rising edge, and the prompt never
    // re-armed. Measured 2026-10-17: three entries into GAME DETAILS produced ONE prompt.
    //
    //     [430.2352] teamsel: raising prompt from GAME DETAILS
    //     [433.2567] teamsel: choice -> -1 (auto)
    //     [494.1320] where: GAME_DETAILS (id 16)      <- no prompt
    //     [612.2334] where: GAME_DETAILS (id 16)      <- no prompt
    //
    // The `where` trace settles the mechanism without a raw slot read: the TOPMOST menu
    // went 16 -> 36 -> 31 -> 16, so a topmost-based edge would have fired. It did not
    // re-arm, and this is the only re-arm on this path, therefore hjGameDetailsOpen()
    // never went false. That matters because the prompt is the ONLY way a hot-joiner
    // picks a team -- they have no staging screen -- so one stray dismissal locked a
    // player to Auto for the rest of the session with no sign anything was wrong.
    //
    // Arming on the topmost menu becoming GAME_DETAILS would reintroduce the s210-B loop,
    // because the blocking dialog is itself the topmost menu while it is up and the
    // screen goes 16 -> 37 -> 16 on every answer. So arm when the player is definitively
    // somewhere ELSE: a city or lobby screen. Selecting the game from the lobby therefore
    // always re-raises the prompt, which is the required behaviour, and answering it
    // cannot re-trigger it.
    {
        int w, i, top = -1;
        if (isInMenus()) {
            for (w = 2; w >= 0 && top < 0; --w)
                for (i = 0; i <= 42; ++i)
                    if (uiGetActiveMenu(i, w)) { top = i; break; }
        }
        if (top == UI_MENU_CITY || top == UI_MENU_CITY_SELECT
            || top == UI_MENU_ONLINE_LOBBY)
            hjTeamPromptAsked = 0;
    }
}

// s207: the joiner IMPOSES its chosen team, every frame, while in game.
//
// The host writes gs->PlayerTeams[] at adopt and re-broadcasts settings periodically, so a
// single write from the joiner could be overwritten. Reasserting per frame is what makes an
// explicit choice stick regardless of what the host decides -- which is the behaviour asked
// for: auto is the default, but a player who picks Blue or Red gets it.
//
// Deliberately does nothing when the choice is "auto" (-1), so the s206 host-side balance
// remains the sole authority in the default case.
void hjApplyTeamChoice(void)
{
    static int logged = -2;
    GameSettings * gs;
    int cid;

    int choice = hjTeamSelection();

    if (choice < 0)                             // auto -- let the host balance
        return;
    if (!isInGame() || isInMenus()) {
        logged = -2;                            // rearm the one-shot log for the next game
        return;
    }
    if (gameAmIHost())                          // host applied it in hjPickTeamForJoiner
        return;

    gs = gameGetSettings();
    if (!gs)
        return;
    cid = gameGetMyClientId();
    if (cid < 0 || cid >= GAME_MAX_PLAYERS)
        return;

    if (gs->PlayerTeams[cid] != (short)choice) {
        gs->PlayerTeams[cid] = (short)choice;
        if (logged != choice) {
            HOTJOIN_LOG("teamsel: joiner imposed team %d on slot %d\n", choice, cid);
            logged = choice;
        }
    }
}

// ---------------------------------------------------------------------------
// s206: pick a team for a late joiner instead of hardcoding Blue.
//
// WHY THIS EXISTS. Every hot-joiner landed on team 0, and the cause was not that staging's
// bulk setTeams() fails to reach late arrivals -- it is that hjHostAdoptPeers below wrote
// `gs->PlayerTeams[i] = 0;` outright at the moment it admitted them. Measured on three
// machines in a live CTF match: teams = 0 0 0, confirmed from the game's own settings
// struct (gs+0xd0) as well as our roster log, with mode_id=1 (CTF). There is NO in-game
// route to a team selector for anyone -- the pause menu is PATCH CONFIG / OPTIONS / QUIT,
// OPTIONS holds only CONTROLS-CAMERA and AUDIO-VISUAL, and the external tooling is gated
// on the staging screen in code -- so a hot-joiner could never correct it either. In a CTF
// match that means late joiners can only ever reinforce one side.
//
// The adopt-time write is known to PROPAGATE: the hardcoded 0 is what every client read,
// which is why all three machines agreed on Blue. So a chosen value written here reaches
// everyone by the same path, with no new plumbing and no protocol change.
//
// Tie goes to team 0, so a joiner entering a game where the host sits alone on team 0 is
// placed on 1 -- the empty side -- which is the behaviour we want.
static int hjPickTeamForJoiner(GameSettings * gs, int newSlot)
{
    int j, n0 = 0, n1 = 0;

    // Non-team modes: leave the vanilla value. setTeams() uses this field differently when
    // teams are off (FFA assigns teamId = slot index), so balancing it would be wrong.
    if (!gameGetOptions()->GameFlags.MultiplayerGameFlags.Teams)
        return 0;

    // s208: honour a preference the joiner announced, if one arrived before adopt. This is
    // the ONLY way an explicit choice can work -- see the comment above hjSendTeamPref.
    hjTeamPrefEnsureInit();
    if (newSlot >= 0 && newSlot < GAME_MAX_PLAYERS
        && hjPeerTeamPref[newSlot] != HJ_TEAMPREF_NONE) {
        HOTJOIN_LOG("teampref: honouring client %d request for team %d\n",
            newSlot, hjPeerTeamPref[newSlot]);
        return hjPeerTeamPref[newSlot];
    }

    // s207 NOTE: deliberately does NOT consult hjTeamChoice. This runs on the HOST, where
    // hjTeamChoice is the HOST's own pick -- if the host had ever opened GAME DETAILS it
    // would stamp its preference onto every joiner that arrived. The joiner imposes its own
    // choice locally in hjApplyTeamChoice instead, which is also what makes the override
    // work without the host needing to know anything about it.
    //
    // So the host ALWAYS balances here, and that is the right default: the host is the only
    // machine that reliably knows the current team sizes.

    for (j = 0; j < GAME_MAX_PLAYERS; ++j) {
        if (j == newSlot || gs->PlayerClients[j] < 0)
            continue;
        if (gs->PlayerTeams[j] == 1)      ++n1;
        else if (gs->PlayerTeams[j] == 0) ++n0;
    }

    return (n1 < n0) ? 1 : 0;
}

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
        // REARM ON A CLEAN LEAVE, via the shared teardown.
        //
        // Third attempt at this, and the history matters because the first two failed in
        // opposite directions:
        //
        //   09-11  a hand-written rearm here cleared hjAdopted but not hjSpawned, so
        //          rejoins were adopted and then skipped forever by hjHostSpawnRemotes
        //          -- "adopt then nothing", only the first join ever spawned
        //   09-12  reverting it removed the only thing that cleared hjAdopted on a clean
        //          leave, so rejoins were never adopted at all -- introduce succeeded,
        //          roster stayed PlayerClients[1] = -1, no pads, no spawn
        //
        // Both were the same underlying defect: two code paths freeing one slot, with
        // only one of them complete. hjReleaseRemoteSlot is now the single definition and
        // both callers use it, so they cannot disagree again.
        //
        // The roster is the authority on whether a slot is free, and it is the right
        // trigger rather than "which teardown won the race": the stall-driven reaper does
        // not fire on a clean leave at all (measured -- sessend msg=3, peerclose t08=2,
        // and no reap line anywhere in a run with three leaves), so keying on our own
        // reaper is keying on the path that does not happen.
        if ((hjAdopted & (1 << i)) && gs->PlayerClients[i] < 0)
            hjReleaseRemoteSlot(i, gs, "roster freed the slot");

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
                HOTJOIN_LOG("adopt: slot %d ANOMALY unblocked on timeout after %d frames "
                    "-- peer record outlived its teardown; a phantom re-adopt may follow\n",
                    i, hjReapBlockFrames[i]);
            }
        }

        if (!p || *(int*)((u32)p + 0x08) != 5)    // only fully-connected peers
            continue;

        gs->PlayerClients[i] = (short)i;
        gs->PlayerStates[i]  = gs->PlayerStates[*(int*)(peers + 0x404)];
        gs->PlayerTeams[i]   = (short)hjPickTeamForJoiner(gs, i);   // s206, was hardcoded 0
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
        // s231: this used to print "(s206 auto-assign)" UNCONDITIONALLY, including when the
        // team came from an honoured preference. That label cost real time: a reader seeing
        // auto-assign fire on an explicitly-chosen join reasonably concluded the pick was
        // being overridden, when in fact hjHostTeamForSlot had already returned the
        // preference. Say which source actually supplied the value.
        HOTJOIN_LOG("adopt: slot %d team -> %d (%s)\n", i, (int)gs->PlayerTeams[i],
            hjPeerTeamPref[i] != HJ_TEAMPREF_NONE ? "client preference" : "s206 auto-assign");
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

    for (i = 0; i < GAME_MAX_PLAYERS; ++i) {
        u32 p = HJ_NWPLAYER_BASE + (i * HJ_NWPLAYER_STRIDE);
        sig = (sig * 31) + *(u32*)(p + 0x00) + *(u32*)(p + 0x04)
            + (u32)*(short*)(p + 0x1a2) + (u32)*(short*)(p + 0x1a6)
            + (u32)*(unsigned char*)(p + 0x68)
            + *(u32*)(p + 0xc34) + *(u32*)(p + 0xc38) + *(u32*)(p + 0xc44);
    }
    // Cap stays at 20. This is NOT a lifetime budget -- hjLogEpochTock rearms
    // hjNwDumps every epoch, so it sets a SUSTAINED line rate. Raising it to 60
    // while also widening the loop from 2 slots to 8 multiplied this probe's
    // output by about twelve, and it measured 31.3 of the host's 39.2 HJ lines
    // per second -- 80% of all log traffic. printf to the EE console is not free,
    // and per-frame instrumentation has already taken this game's join success
    // from 2 tries to 9 once before. Widening the loop was necessary for three
    // players; raising the cap was not, and the two went out in the same build as
    // a behaviour fix, which is exactly the bundling that costs us runs.
    if (sig == hjLastNwSig || hjNwDumps > 20)
        return;
    hjLastNwSig = sig;
    ++hjNwDumps;

    for (i = 0; i < GAME_MAX_PLAYERS; ++i) {
        u32 p = HJ_NWPLAYER_BASE + (i * HJ_NWPLAYER_STRIDE);
        // Occupied slots only. An empty slot prints two lines of zeroes that say
        // nothing; in a 3-player game this is 6 lines per dump instead of 16, and
        // it keeps the cost proportional to the players actually in the match
        // rather than to GAME_MAX_PLAYERS.
        if (*(int*)(p + 0x00) < 0 && *(u32*)(p + 0x04) == 0)
            continue;
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

// s227: slots we have watched become occupied. Cleared when we scrub the slot, so the
// scrub runs exactly once per occupied -> vacant transition and never on a slot that
// was never occupied. See the long note in the loop below for why "every frame while
// the byte is non-zero" was not safe.
static int hjNameSeen = 0;

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

        // s225. Clearing nwp+0x1b0 in hjReleaseRemoteSlot was NOT enough, because on the
        // HOST that function never runs for an ordinary departure. hjPeerClosedRemote
        // computes `eligible = spawned && pData && ...` and the host reaches it with
        // pData already 0, so it returns early (logged as elig=0) and the ENGINE does the
        // whole slot clear by itself -- which is also why PlayerSkins comes back as the
        // engine's -1 sentinel rather than our 0 (correcting the s224 reading). The engine
        // clears gs but leaves nwp+0x1b0 alone, so the stale name sat there and was stomped
        // onto the next occupant from right here.
        //
        // Measured 2026-10-16 on 20261016a-nwname, with the release-path clear in place:
        //     [431.8923] peerclosed: idx=1 ... spawned=1 pData=00000000 ... elig=0
        //                nwp[1]+0x1b0 = 'maxMac3\x00...'        <- never cleared
        //     [492.1325] name: roster slot 1 -> 'maxMac3' (from nwp +0x1b0)
        //
        // So do it HERE instead: this function is host-gated, runs every frame, and already
        // walks every slot.
        //
        // s227 -- HARDENED, and the first version was dangerous. It cleared whenever the
        // byte was non-zero and LOGGED EVERY TIME, inside a per-frame loop. Two faults:
        //
        //   1. If anything rewrites that field for a vacant slot -- and the note above
        //      says +0x1b0 MIRRORS THE LOCAL ROSTER, i.e. the engine writes it -- then we
        //      clear, it rewrites, we clear again, and we emit a console line every frame.
        //      HOTJOIN_LOG is a synchronous console write. At 60 fps that is a freeze.
        //      s228: the host went silent 23 s after a hot-join attached, process alive and
        //      memory coherent but the game loop dead. That is the shape this would make.
        //   2. Slots 3..7 are ALWAYS vacant. Non-zero garbage in any of them meant writing
        //      into tNW_Player entries that were never ours, every frame, forever.
        //
        // Both go away by latching on the OCCUPIED -> VACANT transition. We only ever touch
        // a slot we watched become occupied, exactly once per departure, and a slot that was
        // never occupied is never written at all. Unbounded work in a per-frame hook is how
        // this file has caused trouble before; see the HJ_PEERCLOSE_MAX safety valve.
        if (gs->PlayerClients[i] < 0) {
            if (hjNameSeen & (1 << i)) {
                u32 nmv = HJ_NWPLAYER_BASE + (i * HJ_NWPLAYER_STRIDE) + HJ_NW_NAME;
                hjNameSeen &= ~(1 << i);
                for (k = 0; k < 16; ++k) *(char*)(nmv + k) = 0;
                HOTJOIN_LOG("name: slot %d vacant, cleared stale nwp +0x%x\n",
                    i, HJ_NW_NAME);
            }
            continue;
        }

        hjNameSeen |= (1 << i);

        if (i == me)
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
// s208-E: CUSTOM_MSG_ID_HOTJOIN_NAME now lives in common/messageid.h. It was defined
// here as 32, which silently collided with CUSTOM_MSG_ID_HJ_TEAM_PREF -- see the note
// on the enum.
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
    // s257. Addressing this to gameGetHostId() ALONE sent it to the wrong machine.
    //
    // gameGetHostId() is sessionMasterClientIndex (+0x17c). MEASURED on the wire
    // (2026-10-22, horizon-server trace), a joiner at clientId 2 sending its name:
    //     TCP RECV (clientId:2) RT_MSG_CLIENT_APP_SINGLE TargetOrSource:1
    //         Payload:00-08-...-6D-61-78-54-65-73-74-32      ("maxTest2")
    //     SEND  -> 192.168.1.32   TargetOrSource:2            (the OTHER joiner)
    // The server routed it exactly as addressed. Nothing was dropped and no handler ate
    // it -- the joiner believed client 1 was the host. The real host's whole-log
    // `grep -c "HJ name: slot 2"` found only the vacancy scrub, so its resolution line
    // never fired once, and the user saw a BLANK NAME on a first join.
    //
    // Note this also falsifies the s208-E comment on hjSendTeamPref, which justifies its
    // direct-to-host send as "exactly what the name sync does and that one is known to
    // arrive". It arrives -- somewhere.
    //
    // So broadcast as well, which does not depend on knowing who the host is. Keeping the
    // direct send too: s208-E's reasoning still holds that the DME may relay the two paths
    // differently for a client that has just hot-joined, and the broadcast alone is an
    // untested assumption. hjOnRemoteName is deliberately NOT host-gated and stays that
    // way -- it only writes gs->PlayerNames[idx], validates printability, and is
    // idempotent, so every client ending up with correct names is the better outcome.
    {
        int host = gameGetHostId();
        int rcB  = netBroadcastCustomAppMessage(conn, CUSTOM_MSG_ID_HOTJOIN_NAME,
                                                sizeof(msg), &msg);
        int rcS  = netSendCustomAppMessage(conn, host, CUSTOM_MSG_ID_HOTJOIN_NAME,
                                           sizeof(msg), &msg);
        ++hjNameSends;
        // Log the target: if host != 0 here, s257 is live on this machine, and that is
        // the one number that says so.
        if (hjNameSends <= 4) {
            HOTJOIN_LOG("name SENT %d: me=%d host=%d (smaster) rcB=%d rcS=%d\n",
                hjNameSends, me, host, rcB, rcS);
        }
    }
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
    // 2026-09-25: was 120, which is why this probe went silent at t=920 in round
    // 20260925a and stayed silent for the remaining 342 s of the session. That silence was
    // then read as possible evidence that the joiner's pad ring had frozen and the reaper
    // could not see it -- a bug that does not exist. It emitted exactly its quota and
    // switched off.
    //
    // THIRD TIME AN ABSENCE OF LOG OUTPUT MISLED THIS PROJECT (after an anchored `^HJ`
    // grep reporting zero lines in a log full of them, and a pad_seq snapshot read out of
    // the middle of a reap loop). RULE: absence of a line is almost never evidence about
    // the game -- check the emitter's caps and gates first.
    if (hjPrSamples >= 3600)      // ~a whole match of CHANGED samples
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
                + (u32)*(signed char*)(n + HJ_PR_THROTTLE)
                // seq IS IN THE SIGNATURE DELIBERATELY, added 2026-09-25. Without it this
                // was a liveness probe blind to liveness: a ring in steady state (buffered
                // parked, catchup 0, skips 0, throttle constant) gave an unchanging
                // signature and total silence while seq advanced perfectly normally, so
                // silence could not be told from a frozen stream -- the exact question the
                // probe exists to answer. seq counts messages RECEIVED and is the only
                // field here that measures whether the remote is still talking to us.
                + (u32)*(int*)(n + HJ_NW_SEQ);
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

        // seq IS PRINTED, added 2026-09-25 after a round that could not answer its own
        // question. seq went into the change-detection signature earlier the same day but
        // not into the output, so the ONE number needed -- whether a remote's received
        // count is still advancing -- was still unreadable. A signature is not a report.
        HOTJOIN_LOG("padring: [%d] cid=%d seq=%d buffered=%d frame=%d catchup=%d thr=%d "
            "skips=%d dTick=%d gate=%d msg=%08x\n",
            i, cid, *(int*)(nwp + HJ_NW_SEQ), buffered,
            (int)*(unsigned char*)(nwp + HJ_PR_ACTIVEFRAME),
            catchup, thr, skips, now - lastTick, gate,
            *(u32*)(nwp + HJ_PR_ACTIVEMSG));
    }
}

// 8 seconds at 60fps. A pad stream runs at ~15/s, so this is ~120 missed
// messages -- far beyond any lag spike, but still well inside the window
// before a returning player tries to rejoin.
// REVISED 2026-09-25. 900 frames = 15 s at 60 Hz. Was 480 (8.0 s), which collided with
// the game's own leave latency almost exactly.
//
// What the reaper races is PROPAGATION -- the delay between a client leaving and the host
// learning of it -- and that is a DIFFERENT quantity from how long the leaving client takes
// to tear itself down locally. The two were conflated twice, in opposite directions,
// because on one machine they happen to be nearly equal.
//
//   departure OBSERVED BY HOST   7.48, 7.57, 7.62, 7.73, 7.82, 8.33, 9.33 s
//                                (7 samples, both directions, both hosts)
//   local teardown of the leaver 2.24, 2.55 s (one machine) / ~7.4-7.7 s (the other)
//
// Against 480 frames TWO OF SEVEN propagation samples are over -- roughly a third of
// departures would take the stall path instead of the clean one. 900 clears the observed
// 9.33 s maximum by 5.7 s, which is adequate rather than generous given that nothing is
// known about what governs the excursions.
//
// VALIDATED 2026-09-25 on a real run: a clean leave at 7.62 s propagation was taken by the
// roster-driven path and the stall reaper never fired -- zero reap lines in the session.
//
// COVERAGE GAP: all seven samples are ONE case -- a non-host leaving a match it joined
// mid-game. No first-join departure and no host departure has ever been timed.
//
// A TOPOLOGY OBJECTION WAS RAISED AND IS DISPROVEN: a host on the Horizon server's own
// subnet observed a departure at 8.33 s, INSIDE the band measured from a host one router
// hop away. Co-location bought nothing, so the delay is not a function of host-to-server
// distance.
#define HJ_REAP_FRAMES    (900)

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

    // Host only, and only while actually in a game.
    //
    // CORRECTED 2026-09-25. This comment used to claim the gate protected "the teardown
    // window on the way out, which looks identical by state and must not be touched". It
    // does not, and nothing here does. isInMenus() is a LOBBY predicate --
    //
    //     isInGame()  =  GAME_ACTIVE && GAME_MAP_ID != 0x27 && SCENE_LOADED == 1
    //     isInMenus() = !GAME_ACTIVE && GAME_MAP_ID == 0x27 && SCENE_LOADED == 1
    //
    // -- so the two are MUTUALLY EXCLUSIVE and the isInMenus() term is strictly redundant
    // with !isInGame(). It is kept because it costs nothing and reads as intent. What it
    // emphatically does NOT do is notice an in-game PAUSE menu: pausing clears neither
    // GAME_ACTIVE nor the map id, so isInMenus() is false throughout.
    //
    // The only thing protecting a player who is merely paused is the pad-stall threshold,
    // and whether that suffices depends on a fact not yet measured: if a client's pad seq
    // keeps advancing while its pause menu is open, a paused player can never look stalled.
    // If it freezes at menu-open, a player sitting in the pause menu is reaped -- at 15 s
    // now, at 8 s in every build before today. Do not add an in-game-menu gate on the
    // strength of the guess; measure the seq first.
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

        // seq <= 0 means this client has never sent a pad message: it is still
        // arriving, not leaving. Reaping there would kill a joiner mid-join.
        //
        // BOTH non-positive values mean "nothing has arrived yet", and the test
        // has to cover both or it eats the second one:
        //    0  -- no remote stream expected yet (fresh slot)
        //   -1  -- registered, nothing ever arrived (re-registration sentinel)
        // The -1 is not hypothetical: hjHostSpawnRemotes logs "seq moved 0 -> -1"
        // on every spawn, so a slot sits at -1 from the instant it is admitted
        // until the first pad lands. With only the == 0 exemption, -1 == lastSeq
        // on the next frame, stallFrames climbs, and at HJ_REAP_FRAMES the slot is
        // reaped -- then rearmed, respawned back to -1, and reaped again.
        // Measured 2026-09-23 on a userver/mbpubuntu two-client match: 26 releases
        // and 36 spawns in a ~2 minute loop, cycling every ~10s, ending only when
        // pads finally began arriving. The joiner was invisible to the host for
        // 2m16s of a 6 minute match.
        //
        // This is the same error as the spawn-gate deadlock of section 89, mirrored:
        // that one gated ADMISSION on evidence only available after admission, this
        // one gates EVICTION on evidence that has not had time to appear yet.
        if (seq <= 0 || seq != lastSeq[i] || buffered > 0) {
            // WHY THE RESET REASON IS LOGGED, once per slot per transition.
            //
            // Until 2026-09-25 this function logged ONLY when it fired, so "the stream
            // never stalled" and "the stream stalled but something pinned the counter at
            // zero" produced identical logs -- total silence -- despite opposite meanings.
            //
            // `buffered > 0` is the suspect clause: seq counts messages RECEIVED, while
            // buffered is a CONSUMER-side quantity, so a ring that stops draining pins the
            // counter at zero forever and the slot becomes permanently un-reapable. That
            // would defeat the reaper's only purpose, collecting a client that crashed or
            // vanished.
            //
            // MEASURED 2026-09-25, AND THE CLAUSE STAYS. I had written here that it was
            // "wrong on principle" and planned to drop it, on the theory that a frozen
            // client's ring might never drain and would pin the counter at zero forever.
            // A SIGSTOP test of a genuinely vanished client says otherwise:
            //
            //   frozen/dead client    buffered = 0 from the FIRST stalling line -> reap
            //                         proceeded, fired at exactly 900 frames (14.998 s)
            //   merely-paused player  buffered = 2 steadily -> reap correctly blocked
            //
            // So this clause does the right thing in BOTH cases: it protects a paused player
            // and does not obstruct a dead one. Dropping it would have exposed paused players
            // to deletion while fixing nothing. The distinction the reaper needs -- paused
            // versus gone -- is carried by whether the ring drains, and the ring already
            // reports it.
            //
            // Leave this alone. `reason=BUFFERED-HELD` is kept as a tripwire: if it ever
            // appears on a client that is genuinely gone, the premise above has broken.
            //
            // Logged on TRANSITION only, so a healthy slot is silent and this cannot become
            // per-frame volume -- per-frame probes took joins from 2 tries to 9 once.
            if (stallFrames[i] > 0) {
                HOTJOIN_LOG("reap: nwp[%d] cid=%d stall reset after %d frames "
                    "(seq=%d last=%d buffered=%d) reason=%s\n",
                    i, cid, stallFrames[i], seq, lastSeq[i], buffered,
                    (seq <= 0)          ? "seq-nonpositive"
                  : (seq != lastSeq[i]) ? "seq-advanced"
                  :                       "BUFFERED-HELD");
            }
            lastSeq[i] = seq;
            stallFrames[i] = 0;
            continue;
        }

        // Progress, so a stall in flight is visible rather than inferred from silence.
        // Every 150 frames is 2.5 s at 60 Hz: six lines before a reap at 900, none for a
        // healthy slot.
        if ((stallFrames[i] % 150) == 0)
            HOTJOIN_LOG("reap: nwp[%d] cid=%d stalling %d/%d frames (seq=%d buffered=%d)\n",
                i, cid, stallFrames[i], HJ_REAP_FRAMES, seq, buffered);

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

        // Everything this used to do inline now lives in hjReleaseRemoteSlot, which the
        // roster-driven path in hjHostAdoptPeers calls as well. The two had drifted apart
        // twice and each divergence was a shipped bug; see that function's comment.
        hjReleaseRemoteSlot(cid, gs, "pad stall");

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

    // NOT host-only. Building a remote Player is purely local object management --
    // nothing in the loop below writes the roster or touches peer state, so every
    // machine in the game needs to run it, not just the host.
    //
    // Measured with a third client hot-joining a 2-player match (host LuKa77 slot 0,
    // in-game client maxTest1 slot 1, late joiner Gtr4 slot 2). Read out of the
    // NON-HOST's EE memory:
    //     GameSettings  clients=0 1 2, states=8 8 8, names ok, PlayerCount=3
    //     tNW_Player[2] cid=2 pData=01f7c560 bSpawned=1 cbCalled=0 seq=-1
    //     PlayerStructArray[2] = NULL
    // i.e. the joiner was fully registered on the non-host and the roster was
    // correct, but cbCalled=0 -- the vanilla construction callback never fired,
    // exactly as it never fires on the host. The host got a body only because this
    // function ran there. Slot 0 (the host) on that same machine reads cbCalled=1,
    // because it was built the ordinary way at level load.
    //
    // So the host gate was never a safety property, just an artifact of having only
    // ever tested two players.
    if (!isInGame())
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
            // GATE ON RE-REGISTRATION, NOT ON PAD DATA.  Corrected 2026-09-12.
            //
            // The previous version required a positive sequence and rejected the -1
            // sentinel, to stop a churn cycle seen with a paused emulator:
            //     296.64 reap -> 297.04 unblocked (0 -> -1) -> spawn
            //     305.04 reap -> 305.44 unblocked (0 -> -1) -> spawn   ... forever
            // Its comment asserted "this cannot deadlock: the spawn is not an admission
            // gate, so the joiner is still adopted and still streams". That assumption
            // is false, and it is the whole remaining rejoin bug.
            //
            // Measured with the host clean and the joiner in-game, both sides verified
            // by live EE memory:
            //     joiner   in-game, padstream curFrame +60/s, seq +15/s, sees the host
            //     host     peer1+0x08 = 5 (fully promoted), PlayerClients[1] = 1,
            //              peers+0x404 = peers+0x408 = 0
            //     host     nwp[1] cbCalled=0 padSeq=-1, ring tick FROZEN, act/tail NULL
            // The joiner streams and the host accepts none of it, because the pad
            // consumer has no Player object for the slot -- and the Player object is
            // created by the spawn this gate is blocking. So:
            //
            //     spawn waits for pad data -> pad data needs a Player -> Player needs
            //     the spawn
            //
            // A first join escapes it only because hjSpawnBlocked is never SET without a
            // prior release, so the gate is skipped entirely; every rejoin is caught.
            // That is exactly the error already written down twelve hundred lines up, in
            // the reap-block comment: "Never gate an admission step on evidence that only
            // exists after admission."
            //
            // So accept the sentinel. -1 means "re-registered, nothing received yet",
            // which is precisely the evidence we want: the slot is live and new. Require
            // the registration to be real as well, so this can never spawn from the
            // previous life's dead pointer (section 79, which froze the host).
            //
            // The anti-churn protection does NOT come from here. It belongs to
            // hjReapBlocked, which holds the re-adopt until the OLD peer record has left
            // state 5 or disappeared -- peer identity, not payload, and the correct
            // signal for "this is genuinely a new client". It worked this run, clearing
            // 0.1 ms after the release because the stale record was already gone.
            int seqNow = *(int*)(nwp + HJ_NW_SEQ);
            if (*(int*)(nwp + HJ_NW_CID) != i || *(u32*)(nwp + HJ_NW_PDATA) == 0)
                continue;
            if (seqNow == hjSpawnSeq[i])
                continue;
            hjSpawnBlocked &= ~(1 << i);
            HOTJOIN_LOG("spawn: slot %d unblocked, seq moved %d -> %d\n",
                i, hjSpawnSeq[i], seqNow);
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
static int hjP408Held = 0;

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
        // p408/p404 say whether the introducer gate (0x174038) let us through, and aux
        // says whether the SECOND gate (0x17404c, "this peer already has an aux record")
        // would refuse instead. Until section 84's latch, every rejoin died at the first
        // gate and the second was never reached, so its state is still unmeasured.
        // Both are read after the call, which is what the next attempt will see.
        HOTJOIN_LOG("introduce: idx=%d ra=%08x a2=%08x a3=%08x state %d -> %d ret=%d "
            "p404=%d p408=%d aux=%08x\n",
            peerIdx, (u32)__builtin_return_address(0), (u32)a2, (u32)a3,
            before, after, ret,
            peers ? *(int*)(peers + HJ_PEERS_MYIDX) : -1,
            peers ? *(int*)(peers + HJ_PEERS_INTRO) : -1,
            peers ? (u32)internal_hjAuxGet((void*)peers, peerIdx) : 0);
    }
    return ret;
}

// ---------------------------------------------------------------------------
// Hotjoin section 141: WHAT DRIVES state 3 -> 4?
//
// 0x001508d0 holds the only write of peer state 4 in the net module (at 0x1509dc), and
// it has no jal callers because it is dispatch table[9] -- four entries on from
// table[5] = 0x00173fc0 = introducePeer, the slot we already hook at 0x001d88b4.
// Every failure signature we have (the rejoin-after-reap stall, the section 108 staging
// stall, and section 122's two unexplained failures) is one thing: a peer parked at
// state 3. So state 3 -> 4 is this function, and the question is only whether it runs.
//
// Read off the disassembly, it bails -- WITHOUT writing state 4 -- on five conditions:
//   1. peers == NULL                                      -> -1
//   2. peerIdx >= 256                                      -> -1
//   3. ctx->0x108 != 0                                     -> 8   <-- SILENT
//   4. *(peers+0x404) (my idx) == 256                      -> -1
//   5. ctx->vtable[0x48](peers, myIdx) returned NULL        -> -1
//   6. ctx->0xec == 1  -> diverts to the ctx->0xf0/0xf4 callback and returns 8
//   7. *(peers+0x400) == NULL                              -> -1
// and on success writes 4, broadcasts via 0x14bdb0, calls ctx->vtable[0x44](peers,
// peerIdx) and SETS ctx->0x108 = 1.
//
// Two things in that list are worth the whole probe:
//
// (a) CONDITION 3 IS A ONCE-ONLY LATCH THAT RETURNS THE SUCCESS CODE. The success path
//     sets ctx->0x108 = 1; any later call sees it non-zero and returns 8 having done
//     nothing at all. The caller cannot tell the two apart. It is cleared at 0x171f74,
//     in the same routine that initialises a peer record to state 2 -- so a second peer
//     negotiating before any re-init would be silently swallowed.
//
// (b) THE STATE-4 WRITE DOES NOT GO TO peers[peerIdx]. It goes to *(peers+0x400), a
//     SINGLE "peer under negotiation" pointer sitting just below +0x404 (my idx) and
//     +0x408 (introducer idx). If that slot points at a different peer than the message's
//     peerIdx, the wrong record is promoted and peerIdx stays at 3 for good. A single
//     slot is exactly the assumption hot-join breaks, since we negotiate an arriving peer
//     while others are already established.
//
// So this logs, per call: peerIdx, the state of peers[peerIdx] before and after, the
// 0x400 slot and ITS state, whether the two agree, ctx->0x108 and ctx->0xec as read
// BEFORE the call (after the call 0x108 is always 1 and says nothing), and the return.
// Log-only -- it changes no behaviour, which is the point: we do not yet know which of
// the seven branches we are in.
#define HJ_T9_SLOT           (0x001d88c4)
#define HJ_T9_ORIG           (0x001508d0)
#define HJ_T9_RUNTIME_SLOT   (0x01f4cac4)
#define HJ_CTX_T9LATCH       (0x108)
#define HJ_CTX_T9MODE        (0x0ec)
#define HJ_PEERS_NEGOTIATING (0x400)

static int hjT9Logged = 0;

int hjType9Hook(void * peers, int a1, int peerIdx, void * msg)
{
    u32 p = (u32)peers;
    u32 c = *(u32*)HJ_NET_CTX_PTR;
    int before = -1, after = -1, negState = -1;
    u32 neg = 0, latch = 0, mode = 0;
    void * pp;
    int ret;

    if (p) {
        neg = *(u32*)(p + HJ_PEERS_NEGOTIATING);
        if (neg) negState = *(int*)(neg + 0x08);
        if (peerIdx >= 0 && peerIdx < 256) {
            pp = internal_hjPeerLookup(peers, peerIdx);
            if (pp) before = *(int*)((u32)pp + 0x08);
        }
    }
    if (c) {
        latch = *(u32*)(c + HJ_CTX_T9LATCH);
        mode  = *(u32*)(c + HJ_CTX_T9MODE);
    }

    ret = internal_hjType9(peers, a1, peerIdx, msg);

    if (p && peerIdx >= 0 && peerIdx < 256) {
        pp = internal_hjPeerLookup(peers, peerIdx);
        if (pp) after = *(int*)((u32)pp + 0x08);
    }

    if (hjT9Logged < 48) {
        ++hjT9Logged;
        // `match` is the discriminator for (b): 0 means the state-4 write landed on a
        // peer OTHER than the one this message is about. `latch`/`mode` are the
        // discriminators for (a) and for condition 6. A line with ret=8, latch=1 and
        // state unchanged is the silent swallow, and nothing else looks like that.
        HOTJOIN_LOG("type9: idx=%d state %d -> %d ret=%d latch=%d mode=%d "
            "neg=%08x negState=%d match=%d p404=%d p408=%d ra=%08x\n",
            peerIdx, before, after, ret, (int)latch, (int)mode,
            neg, negState,
            (neg && peerIdx >= 0 && peerIdx < 256 &&
             neg == (u32)internal_hjPeerLookup(peers, peerIdx)) ? 1 : 0,
            p ? *(int*)(p + HJ_PEERS_MYIDX) : -1,
            p ? *(int*)(p + HJ_PEERS_INTRO) : -1,
            (u32)__builtin_return_address(0));
    }
    return ret;
}

// ---------------------------------------------------------------------------
// Hotjoin: hook the ctx-RESIDENT copy of the dispatch table too.
//
// There are TWO copies of this table. `0x001724d0` (the ctx constructor tail) builds a
// second one INSIDE the net ctx from literal lui/addiu immediates rather than copying
// the static `0x001d88a8`. It writes table[16..18] at ctx+0xc0/c4/c8, which puts type 2
// at ctx+0x88 and type 9 at ctx+0xa4 (section 142).
//
// The static slot is only KNOWN to be live because the introduce hook demonstrably
// fires. If dispatch actually reads the ctx copy, a round with only the static hook
// installed draws zero `type9:` lines and tells us nothing except "try the other table
// tomorrow" -- which costs a whole test round with two machines and a human. Hooking
// both removes that outcome from the table entirely. `ra` in the type9 line says which
// copy dispatched.
//
// Deriving the slot from the LIVE ctx pointer, not from the hardcoded 0x01f4cac4 seen
// in one dump: that address is only valid for one particular ctx allocation. The
// derivation also self-checks -- finding exactly 0x001508d0 at ctx+0xa4 CONFIRMS
// section 142's offset arithmetic, and finding something else says it is wrong before
// we have staked a test round on it.
//
// Re-checked periodically rather than poked once at install, because the ctx is built
// after the patch loads and may be rebuilt per game, which would silently restore the
// vanilla pointer mid-session.
//
// SAFETY, because two of my own "defensive" additions have caused the problems they
// were meant to prevent: this writes ONLY when the slot holds exactly the vanilla
// handler, so a freed or re-laid-out ctx cannot produce a blind write; re-hooking is
// idempotent; and hjType9Hook is a transparent wrapper that calls the original and
// returns its value, so even if BOTH copies dispatch, behaviour is unchanged and the
// only cost is duplicate log lines.
#define HJ_CTX_T9SLOT   (0xa4)

static u32 hjT9CtxLast   = 0;
static int hjT9CtxLogged = 0;

// HARDENED 2026-09-27 after the userver crash (s145/s146). This is the ONLY code in the
// file that dereferences the net ctx unconditionally -- main.c calls it every 30 frames
// regardless of game state, so it runs in the lobby and, critically, DURING A LOGIN
// TRANSITION. Every other HJ_NET_CTX_PTR read is reached from an in-game event.
//
// `if (!c)` is not enough. 0x001A1CF0 is game memory, not ours: right after a logout it
// can still hold a pointer to a torn-down context, which is non-NULL and unusable. The
// load below then reads a wild address, and an unguarded load is a TLB miss -- the exact
// fault class that opens the crash cascade in s145.
//
// So validate before dereferencing: 4-byte aligned, and the whole read must land inside
// the 32 MB of EE RAM, above the low region where nothing legitimate lives. The real ctx
// has been observed around 0x01f4ca20, comfortably inside this.
//
// NOT gated on isInGame(): s108's staging stall happens at menus=1 game=0, so a game-state
// gate would blind the probe to the very case it exists to measure.
#define HJ_EE_RAM_END    (0x02000000)
#define HJ_CTX_MIN       (0x00100000)

void hjT9EnsureCtxHook(void)
{
    u32 c = *(u32*)HJ_NET_CTX_PTR;
    u32 slot, held;

    if (!c)
        return;
    if ((c & 3) || c < HJ_CTX_MIN || c > HJ_EE_RAM_END - HJ_CTX_T9SLOT - 4) {
        // Say it once per distinct bogus value rather than every 30 frames.
        if (c != hjT9CtxLast && hjT9CtxLogged < 8) {
            hjT9CtxLast = c;
            ++hjT9CtxLogged;
            HOTJOIN_LOG("type9 ctx-copy SKIPPED, ctx=%08x is not a usable pointer "
                "(aligned=%d, in-range=%d)\n",
                c, (c & 3) == 0,
                (c >= HJ_CTX_MIN && c <= HJ_EE_RAM_END - HJ_CTX_T9SLOT - 4));
        }
        return;
    }

    slot = c + HJ_CTX_T9SLOT;
    held = *(u32*)slot;

    if (held == (u32)&hjType9Hook)
        return;                                 // already ours

    if (held == HJ_T9_ORIG) {
        POKE_U32(slot, &hjType9Hook);
        if (c != hjT9CtxLast && hjT9CtxLogged < 8) {
            hjT9CtxLast = c;
            ++hjT9CtxLogged;
            HOTJOIN_LOG("type9 ctx-copy hooked at %08x (ctx=%08x, static slot %08x) "
                "-- s142 offset CONFIRMED\n", slot, c, HJ_T9_SLOT);
        }
        return;
    }

    // Neither vanilla nor ours: either ctx+0xa4 is not the type-9 entry, or this ctx is
    // laid out differently. Say so once per ctx rather than poking blind.
    if (c != hjT9CtxLast && hjT9CtxLogged < 8) {
        hjT9CtxLast = c;
        ++hjT9CtxLogged;
        HOTJOIN_LOG("type9 ctx-copy at %08x holds %08x, expected %08x -- NOT hooked "
            "(ctx=%08x)\n", slot, held, HJ_T9_ORIG, c);
    }
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
    // FOURTH TIME. hjP408Held was a LIFETIME cap of 8, not an epoch budget, and the
    // first join spent all 8. "ABSENT: HJ p408 on both rejoins" therefore meant "the
    // budget was gone", and I read it as "the joiner never announced" -- while the
    // joiner's own log showed 70 announces and a peer table with both records at
    // state 5. Sections 63, 78 and 80 are the same mistake: a probe's own gating read
    // as a property of the game. Every counter in this file belongs in this function.
    hjP408Held = 0;
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

// ---------------------------------------------------------------------------
// THE REJOIN ROOT CAUSE: our own announce disarms the host's introducer.
//
// 0x00173FC0 introducePeer opens with a gate that is easy to miss because none of its
// exits load a return value -- every failure path falls through with whatever v0 last
// held, so the value our probe prints as `ret` IS the thing that failed the test:
//
//     174000  jal 0x16f1e0        ; sp+16 = peers->0x408   (that function is a
//                                 ;   two-line getter: *out = peers[0x408]; return 0)
//     174030  lw   v0,16(sp)      ; v0 = peers->0x408
//     174034  lw   v1,0x404(s3)   ; v1 = peers->0x404 = MY peer index
//     174038  bnel v1,v0,0x174178 ; if (p404 != p408) return p408, introduce NOTHING
//
// peers->0x408 has exactly ONE runtime writer in the whole image -- 0x00171D20,
// `sw a1,0x408(a0)`, reached only through 0x00171D18, which the type-22 handler
// dispatches as ctx->0x44 for inbound message type 5:
//
//     150e3c  lbu a1,0(s1)        ; a1 = msg[0] = type
//     150e48  sw  a1,8(s2)        ; peer->0x08 = type       (the useful half)
//     150e5c  bne a1,5 -> skip
//     150e68  lbu a1,1(s1)        ; msg[1] = the SENDER's peer index
//     150e74  jalr ctx->0x44      ; peers->0x408 = sender index
//
// hjAnnounce sets our own record to 5 and calls 0x14bdb0 with target -1. That builds a
// header whose msg[0] is the record's 0x08 (= 5) and whose msg[1] is our own index, and
// broadcasts it to EVERY peer. So each announce tells every other machine
// "peers->0x408 = the joiner", and nothing ever puts it back.
//
// Measured on both machines in the same session. Host LuKa77, me=0:
//
//     p408   0 -> 1 at 99.6 s (first joiner announces) -> 2 at 338.3 s (second)
//     introduce  88.6  ret=1040296128   p408=0 == me   <- the gate PASSED, join worked
//     introduce 299.9  ret=1            p408=1
//     introduce 338.1  ret=1            p408=1
//     introduce 570.6 .. 839.2  ret=2   p408=2         <- five rejoins, all refused
//
// ret equals p408 in all eight samples, and the single introduce that did real work is
// the single one taken before any announce landed. Gtr4 shows the same correlation from
// the other side: its introduce at 9490.81 returned 0 while p408 was still 0, p408
// flipped to 2 at 9491.03, and every introduce from 9723 on returned 2.
//
// That is the whole "first hot-join works, every rejoin fails" symptom, and it is
// self-inflicted: the comment on hjAnnounce notes we deliberately do NOT call 0x171d18
// locally "because that overwrites peers->0x408, which on the joiner legitimately points
// at the host" -- correct, but we then broadcast a message whose entire remote effect is
// to make every other machine perform that exact write.
//
// THE GUARD. Once a machine's p408 equals its own p404 it is the introducer, and no
// inbound announce may take that away. Restoring the pre-call value (rather than forcing
// p404) keeps this to a pure undo of the damage:
//
//   host      p408 == p404 == 0, so the latch holds it at 0 and introduce works on
//             every rejoin, not just the first
//   non-host  p408 never equals p404 (it points at the host), the condition is never
//             true, and not a single write is suppressed -- zero behaviour change
//
// The useful half of the type-5 -- `peer->0x08 = 5`, which is the whole reason
// hjAnnounce exists -- happens at 150e48, BEFORE the branch, so it is untouched.
//
// UNVERIFIED: this is reasoned from the disassembly and from two logs that do not share
// a clock. It predicts the host's p408 now stays 0 for the whole session and that
// introduce stops returning a small index. If p408 still drifts, the write has a second
// source this scan did not find and the scan (sw rt,0x408(base) over 0x140000-0x1b0000)
// is the thing to widen.
// ---------------------------------------------------------------------------

int hjType22Hook(void * a0, void * a1, int a2, u8 * payload)
{
    int (*orig)(void *, void *, int, u8 *) =
        (int (*)(void *, void *, int, u8 *))hjT22Orig;
    int msgType = payload ? payload[0] : -1;
    int peerIdx = payload ? payload[1] : -1;
    int ret;
    u32 nc = *(u32*)HJ_NET_CTX_PTR;
    u32 np = nc ? *(u32*)(nc + HJ_CTX_PEERS) : 0;
    int wasIntro = 0, p408Before = 0;

    // Snapshot before the handler runs: only a machine that already owns the introducer
    // role has anything to defend.
    if (np) {
        p408Before = *(int*)(np + HJ_PEERS_INTRO);
        wasIntro = (p408Before == *(int*)(np + HJ_PEERS_MYIDX));
    }

    ret = orig(a0, a1, a2, payload);

    if (wasIntro && np && *(int*)(np + HJ_PEERS_INTRO) != p408Before) {
        int stolenBy = *(int*)(np + HJ_PEERS_INTRO);
        *(int*)(np + HJ_PEERS_INTRO) = p408Before;
        if (hjP408Held < 8) {
            ++hjP408Held;
            HOTJOIN_LOG("p408: held at %d -- type=%d from peer %d tried to take it to %d\n",
                p408Before, msgType, peerIdx, stolenBy);
        }
    }

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
// Hotjoin: WHY mark-connected NEVER RUNS, and WHO WRITES p408.   (s150-s151-A)
//
// Measured on a live hot-join that looked healthy: roster n=2, both peer records t08=5,
// pad data flowing BOTH ways -- and the joiner invisible to the host, absent from the
// radar. `markconn` fired ZERO times on BOTH machines (8288 / 6978 HJ lines as positive
// controls), so 0x172898 never runs and the engine never registers the peer.
//
// CAUTION established in s151: t08 is NOT a trustworthy indicator, because hjAnnounce and
// hjPromote write `mine->0x08 = 5` OURSELVES. Every side reads "promoted" while none of
// the engine bookkeeping happened. Only `markconn` firing is evidence, because that is the
// engine's own action and we merely observe it.
//
// The gate lives in the function at 0x001725c0, which is NOT called by any `jal` -- it is
// a function pointer at 0x001d8828 = ctx+0x08 (ctx is STATIC at 0x001d8820, s149). Its
// prologue gives the signature: s5 = a0 = peers, s4 = a1 = peerIdx.
//
// FIVE bails precede the p408 gate, and our markconn hook cannot distinguish them:
//   1725f8  beqz s5          -> peers == NULL
//   17260c  bnel s5,v1       -> peers != ctx->0xE8
//   172620  beqz v1          -> peerLookup(peers, peerIdx) == NULL
//   172644  beqz s2          -> auxGet(...) == 0
//   172658  bne  s4,v1       -> peerIdx != peers->0x408        <- the known gate
//   172668  jal  0x172898    -> the promoter (what we want to reach)
// So log 1, 2, 3 and 5 directly; if all four pass and markconn still does not fire, the
// answer is 4 by elimination.
#define HJ_PROMOGATE_SLOT (0x001d8828)      /* ctx+0x08 */
#define HJ_PROMOGATE_ORIG (0x001725c0)

extern int internal_hjPromoteGate(void * peers, int peerIdx);

static int hjPromoGateLogged = 0;

int hjPromoteGateHook(void * peers, int peerIdx)
{
    u32 pp = (u32)peers;
    u32 c  = *(u32*)HJ_NET_CTX_PTR;
    u32 ctxPeers = c ? *(u32*)(c + HJ_CTX_PEERS) : 0;
    void * rec;
    int p408 = -1, p404 = -1, before = -1, after = -1;
    int ret;

    if (pp) {
        p408 = *(int*)(pp + 0x408);
        p404 = *(int*)(pp + 0x404);
    }
    rec = (pp && peerIdx >= 0 && peerIdx < 256)
        ? internal_hjPeerLookup(peers, peerIdx) : 0;
    if (rec)
        before = *(int*)((u32)rec + 0x08);

    ret = internal_hjPromoteGate(peers, peerIdx);

    rec = (pp && peerIdx >= 0 && peerIdx < 256)
        ? internal_hjPeerLookup(peers, peerIdx) : 0;
    if (rec)
        after = *(int*)((u32)rec + 0x08);

    // Log every call whose outcome could matter, plus the opening few unconditionally.
    // A promoted peer is rare, so `t08 %d -> %d` changing is the headline.
    if (hjPromoGateLogged < 40 || before != after) {
        ++hjPromoGateLogged;
        HOTJOIN_LOG("promogate: idx=%d peers=%08x ctxPeers=%08x match=%d "
            "rec=%08x p404=%d p408=%d gate=%d t08 %d -> %d ret=%d\n",
            peerIdx, pp, ctxPeers, (pp && pp == ctxPeers) ? 1 : 0,
            (u32)rec, p404, p408, (peerIdx == p408) ? 1 : 0,
            before, after, ret);
    }
    return ret;
}

// p408 is written from THREE places, so a probe on one site proves nothing:
//   0x0016fa84  jal 0x171d18   -- the LOCAL connect-path publish. This is why a host that
//                                opens a game has p408 == 0 (its own index) rather than
//                                the 256 initial value (s151-A).
//   ctx+0x44 = 0x001d8864      -- the indirect call taken by the type-22 receive branch
//                                when msgType == 5; writes payload[1] = SENDER'S index.
//   our own hjPromote          -- internal_hjPublishMyIndex(peers, peers->0x404).
// s151-A narrowed the failure to three candidates and this catches all three at once:
// never set to the joiner's index / set then clobbered back / set correctly but unused.
#define HJ_SETP408_SLOT (0x001d8864)        /* ctx+0x44 */
#define HJ_SETP408_ORIG (0x00171d18)
#define HJ_SETP408_SITE (0x0016fa84)        /* direct jal, local publish */
#define HJ_SETP408_CALL (0x0c05c746)

static int hjP408Logged = 0;

int hjSetP408Hook(void * peers, int value)
{
    u32 ra = (u32)__builtin_return_address(0);
    u32 pp = (u32)peers;
    int before = pp ? *(int*)(pp + 0x408) : -1;
    int ret = internal_hjPublishMyIndex(peers, value);
    int after = pp ? *(int*)(pp + 0x408) : -1;

    // Always log a CHANGE -- a 1 -> 0 rewrite is the whole question -- and sample the rest
    // so a caller firing every few seconds cannot bury it.
    if (before != after || hjP408Logged < 24) {
        ++hjP408Logged;
        HOTJOIN_LOG("setp408: %d -> %d arg=%d ra=%08x me=%d ret=%d\n",
            before, after, value, ra, pp ? *(int*)(pp + 0x404) : -1, ret);
    }
    return ret;
}

// ---------------------------------------------------------------------------
// Hotjoin: THE REAL 3 -> 4 TRANSITION.   (s159, s160)
//
// Four functions in the net module write t08 = 4 (0x001509dc, 0x00154f64, 0x0016bde4,
// 0x0016d864) -- my notes claimed for days that 0x1509dc was the ONLY one, and that single
// false premise is what launched the whole "message type 9" dead end (s156, s158-A).
//
// 0x0016d7c8..0x0016d87c is a message handler `(peer, type, payload, len)` that performs the
// 3 -> 4 promotion, and its three conditions are readable:
//     16d810  bne  s0,64    -> BAIL unless LENGTH == 64
//     16d848  bne  v1,3     -> only if the peer's CURRENT state is 3
//     16d850  jal  0x16c710 -> only if this returns 0
//     16d864  sw   v0,8(s2) -> peer->0x08 = 4
//
// We cannot hook 0x0016d7c8 itself: it has no `jal` callers and its address appears nowhere
// as data, so it is almost certainly a switch-case target reached by a computed `jr`.
// But the GATE is callable -- `0x0016c710` has exactly two call sites, 0x0016bdd0 and
// 0x0016d850, and the latter IS the one in this path. Hooking that `jal` places a probe
// between condition 2 and condition 3, so a line appearing at all proves length==64 AND
// state==3 both passed, and the return value says whether the promotion follows.
//
// 0x0016bdd0 is the other caller and sits beside 0x0016bde4, ANOTHER t08=4 writer -- so there
// are two similar 3 -> 4 paths. Hook both and let the ra distinguish them.
//
// Log-only. No behaviour change. Unlike the type-9 probes this cannot be chasing something
// nonexistent: each site is a literal store of 4 into a peer record.
#define HJ_S34_GATE_A   (0x0016d850)      /* jal 0x16c710 inside the 3->4 handler */
#define HJ_S34_GATE_B   (0x0016bdd0)      /* the other caller, beside 0x0016bde4 */
#define HJ_S34_GATE_CALL (0x0c05b1c4)     /* jal 0x0016c710 */

extern int internal_hjS34Gate(void * peer);

static int hjS34Logged = 0;

int hjS34GateHook(void * peer)
{
    u32 ra = (u32)__builtin_return_address(0);
    u32 pp = (u32)peer;
    int before = pp ? *(int*)(pp + 0x08) : -1;
    int ret = internal_hjS34Gate(peer);
    int after = pp ? *(int*)(pp + 0x08) : -1;

    // Always log a state change; sample the rest. Reaching here at all is the headline,
    // because it means the length and state tests already passed.
    if (before != after || hjS34Logged < 32) {
        ++hjS34Logged;
        HOTJOIN_LOG("s34gate: peer=%08x t08 %d -> %d ret=%d ra=%08x "
            "(ret==0 promotes to 4)\n", pp, before, after, ret, ra);
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

    // Both slots are reported whether or not we hook, because 0x001724d0 builds a
    // SECOND copy of this table inside the net ctx from literal immediates rather than
    // copying 0x001d88a8 -- so if the static poke turns out to draw no type9 lines at
    // all, the runtime copy is where dispatch is really reading from.
    if (*(u32*)HJ_T9_SLOT == HJ_T9_ORIG) {
        POKE_U32(HJ_T9_SLOT, &hjType9Hook);
        HOTJOIN_LOG("type9 hook installed at slot %08x (runtime copy %08x holds %08x)\n",
            HJ_T9_SLOT, HJ_T9_RUNTIME_SLOT, *(u32*)HJ_T9_RUNTIME_SLOT);
    } else {
        HOTJOIN_LOG("type9 slot %08x holds %08x, expected %08x -- NOT hooked\n",
            HJ_T9_SLOT, *(u32*)HJ_T9_SLOT, HJ_T9_ORIG);
    }

    // s150/s151-A: the promoter gate and every p408 writer. These are the probes that
    // matter now -- type 9 never arrives (s149), so table[9] tells us nothing.
    if (*(u32*)HJ_PROMOGATE_SLOT == HJ_PROMOGATE_ORIG) {
        POKE_U32(HJ_PROMOGATE_SLOT, &hjPromoteGateHook);
        HOTJOIN_LOG("promogate hook installed at ctx slot %08x\n", HJ_PROMOGATE_SLOT);
    } else {
        HOTJOIN_LOG("promogate slot %08x holds %08x, expected %08x -- NOT hooked\n",
            HJ_PROMOGATE_SLOT, *(u32*)HJ_PROMOGATE_SLOT, HJ_PROMOGATE_ORIG);
    }

    if (*(u32*)HJ_SETP408_SLOT == HJ_SETP408_ORIG) {
        POKE_U32(HJ_SETP408_SLOT, &hjSetP408Hook);
        HOTJOIN_LOG("setp408 hook installed at ctx slot %08x\n", HJ_SETP408_SLOT);
    } else {
        HOTJOIN_LOG("setp408 slot %08x holds %08x, expected %08x -- NOT hooked\n",
            HJ_SETP408_SLOT, *(u32*)HJ_SETP408_SLOT, HJ_SETP408_ORIG);
    }

    if (*(u32*)HJ_SETP408_SITE == HJ_SETP408_CALL) {
        HOOK_JAL(HJ_SETP408_SITE, &hjSetP408Hook);
        HOTJOIN_LOG("setp408 hook installed at local publish site %08x\n", HJ_SETP408_SITE);
    } else {
        HOTJOIN_LOG("setp408 site %08x holds %08x, expected %08x -- NOT hooked\n",
            HJ_SETP408_SITE, *(u32*)HJ_SETP408_SITE, HJ_SETP408_CALL);
    }

    // s160: the real 3 -> 4 gate. Guarded on the exact `jal` encoding so a wrong address
    // declines instead of corrupting code.
    if (*(u32*)HJ_S34_GATE_A == HJ_S34_GATE_CALL) {
        HOOK_JAL(HJ_S34_GATE_A, &hjS34GateHook);
        HOTJOIN_LOG("s34gate hook installed at %08x\n", HJ_S34_GATE_A);
    } else {
        HOTJOIN_LOG("s34gate site %08x holds %08x, expected %08x -- NOT hooked\n",
            HJ_S34_GATE_A, *(u32*)HJ_S34_GATE_A, HJ_S34_GATE_CALL);
    }
    if (*(u32*)HJ_S34_GATE_B == HJ_S34_GATE_CALL) {
        HOOK_JAL(HJ_S34_GATE_B, &hjS34GateHook);
        HOTJOIN_LOG("s34gate hook installed at %08x\n", HJ_S34_GATE_B);
    } else {
        HOTJOIN_LOG("s34gate site %08x holds %08x, expected %08x -- NOT hooked\n",
            HJ_S34_GATE_B, *(u32*)HJ_S34_GATE_B, HJ_S34_GATE_CALL);
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

    HOTJOIN_LOG("build: " HJ_BUILD_TAG "\n");
}
#else
// s207: PAL stubs. The selector and its apply live in the NTSC block above, so without
// these the PAL link fails on main.c's references -- and because bin/ is bind-mounted, a
// failed build DELETES the served artifact. (It did: patch-10683.bin was removed.)
int hjTeamChoice = -1;
void hjTeamSelectPrompt(void) { }
void hjApplyTeamChoice(void) { }
void hjSendTeamPref(void) { }
void hjHostApplyLateTeamPref(void) { }
int  hjOnTeamPrefMsg(void * connection, void * data) { return sizeof(HjTeamPref_t); }

void hjInstallPlayerBitGuard(void) { }
void hjInstallAuxAcceptProbe(void) { }
void hjFixMissingPads(void) { }
void hjDumpDispatch(void) { }
void hjAnnounce(void) { }
void hjLogWhere(void) { }           // s211
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
void hjT9EnsureCtxHook(void) { }
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
// ---------------------------------------------------------------------------
// s210: raise the team prompt BEFORE the join request, on GAME DETAILS.
//
// s209-G put it on STAGING, which works but is the wrong place: by then the join is
// already in flight -- the joiner is connected to DME, the host is waiting on the peer
// sequence, and a countdown is running. uiShowSelectDialog BLOCKS, so holding staging
// holds all of that (main() does not run either, so hjAnnounce stops sending). It
// survived a 49 s block in testing, but "it happened to be fine" is not a property.
//
// On GAME DETAILS nothing is pending: the player is sitting in a menu, and the choice is
// simply in hand when they press JOIN. Blocking there costs nothing.
//
// The game dispatches each menu through a vtable whose `update` sits at +0x14; main.c
// installs patchStaging by poking that slot at a hardcoded address. There is no such
// constant for GAME DETAILS, so derive the slot at runtime from the menu object
// (UiMenu_t.vTable, +0x60) -- and SELF-CHECK the derivation against the one address we
// do know, staging's. If `stagingVt + 0x14` does not equal the known constant then the
// +0x60 assumption is wrong, and we log and install nothing rather than poke a guess
// into executable dispatch.
static int (*hjOrigGameDetailsUpdate)(UiMenu_t*, int) = 0;

int patchGameDetails(UiMenu_t* ui, int pad)
{
    if (!hjTeamPromptAsked) {
        int sel;
        hjTeamPromptAsked = 1;
        HOTJOIN_LOG("teamsel: raising prompt from GAME DETAILS\n");
        sel = uiShowSelectDialog("Join Team", hjTeamChoiceOptions, 3, 0);
        hjTeamChoice = (sel <= 0) ? -1 : (sel - 1);
        HOTJOIN_LOG("teamsel: choice -> %d (%s), raw sel %d\n", hjTeamChoice,
            (hjTeamChoice < 0) ? "auto" : ((hjTeamChoice == 0) ? "blue" : "red"), sel);
    }

    if (hjOrigGameDetailsUpdate)
        return hjOrigGameDetailsUpdate(ui, pad);
    return 0;
}

// s237: a pointer we are about to dereference must be inside EE RAM and aligned.
// uiGetMenu() returning non-NULL is NOT sufficient -- see the note in the function below.
// Mask off the segment bits first: the EE reaches the same 32 MB through cached
// (0x00......), uncached (0x20......) and uncached-accelerated (0x30......) mirrors,
// and a legitimate object can be handed to us through any of them. Testing the raw
// value would FALSELY REJECT a valid pointer and silently stop installing the hook --
// which would look exactly like a successful fix, since the storm would also stop.
// Mask is 0x0FFFFFFF, not 0x1FFFFFFF: on the EE the mirrors are 0x20...... and
// 0x30......, and 0x1FFFFFFF leaves the 0x10000000 bit of the UCA mirror set, which
// false-rejects it. Caught by a table test before this ever ran. Real rejections all
// survive: 382d8d08 -> 082d8d08, 3c08b50f -> 0c08b50f and
// 6c03bc00 -> 0c03bc00 are all still past the end of RAM.
#define HJ_PLAUSIBLE_EE_PTR(p)  ((((u32)(p)) & 0x0FFFFFFFu) >= 0x00100000u \
                                 && (((u32)(p)) & 0x0FFFFFFFu) < 0x02000000u \
                                 && ((((u32)(p)) & 3u) == 0u))

void hjInstallGameDetailsHook(u32 stagingUpdateSlot)
{
    // s216: this used to latch on a `static int state` and install EXACTLY ONCE per boot.
    // Measured 2026-10-14: the team prompt fired on the first join of a session and never
    // again. Three GAME_DETAILS visits, one `raising prompt` line, one `uihook` line --
    // and `hjTeamPromptAsked` was definitely cleared, because `left game, choice 1 -> auto`
    // fired in between. So the flag was not the problem: patchGameDetails simply stopped
    // being called, i.e. the vtable slot no longer pointed at us.
    //
    // The menu object is rebuilt across a game session, which restores the original update
    // pointer. A once-only install cannot survive that. So verify the slot every frame and
    // re-install whenever it is not ours. Cheap: two pointer loads and a compare.
    //
    // User-visible symptom this fixes: the team choice is supposed to be a PER-JOIN
    // decision, and it was silently unavailable on every join after the first.
    static int disproven = 0;
    static int installs  = 0;
    UiMenu_t * stg;
    UiMenu_t * det;
    u32 svt, dvt, slot, cur;

    if (disproven)
        return;

    // s216-C: the menu objects DO NOT EXIST while a game is running, and uiGetMenu() hands
    // back DANGLING pointers into memory the level has since reused. Reading a vTable
    // through one of those is meaningless.
    //
    // Measured twice, and the second reading is what gave it away:
    //   ee=591.16  staging vt 00000000, details vt 00000000   (mid-teardown)
    //   ee=472.39  staging vt 382d8d08, details vt 382d8d08   (reused memory)
    // Two distinct menu objects cannot share a vTable pointer, so 382d8d08 is not a layout
    // we failed to recognise -- it is whatever the level put there. s216-B only skipped the
    // zero case, so the garbage case still latched `disproven` and killed the prompt.
    //
    // The right condition is not "is this value plausible" but "do these objects exist",
    // and they exist exactly when we are in the menus.
    if (!isInMenus())
        return;

    stg = uiGetMenu(UI_MENU_STAGING);
    det = uiGetMenu(UI_MENU_GAME_DETAILS);
    if (!stg || !det)
        return;                     // menus not built yet; try again next frame

    // s237: NULL IS NOT THE ONLY BAD POINTER. uiGetMenu() can hand back a DANGLING
    // non-NULL pointer -- s216-C already caught it returning 382d8d08 for two distinct
    // menus at once, which is reused level memory, not a menu. The !stg || !det check
    // above passes such a pointer straight through to the two loads below.
    //
    // Measured 2026-10-19, in an ORDINARY game with no testing involved:
    //     TLB Miss, pc=0xe33f8 addr=0x3c08b56f [load]
    //     TLB Miss, pc=0xe33f8 addr=0x6c03bc60 [load]
    // repeating EVERY FRAME. Those are exactly our two loads: 0x3c08b56f - 0x60 and
    // 0x6c03bc60 - 0x60 are the stg and det pointers, both wild, both non-NULL.
    //
    // And it NEVER STOPS, because of the s216-B guard below. A TLB-missed load reads 0,
    // so `if (!svt || !dvt) return;` takes the early return before `disproven` can latch
    // -- and we come back and fault again next frame, forever. (Deductive: if the load
    // returned garbage rather than 0, disproven WOULD latch, we would get one DISPROVEN
    // line and no storm. We observe a storm, therefore it reads 0.) The guard added to
    // survive one failure mode is what makes this one permanent.
    //
    // So validate the POINTER before dereferencing it, not just the value it yields.
    // EE RAM is 32 MB; menu objects live around 0x01c.....; anything outside that, or
    // unaligned, is not an object. This range also rejects the 382d8d08 of s216-C.
    if (!HJ_PLAUSIBLE_EE_PTR((u32)stg) || !HJ_PLAUSIBLE_EE_PTR((u32)det)) {
        // Log once per DISTINCT pair, not once ever. A once-ever line cannot tell
        // "caught one bad pointer during a teardown" from "rejecting every frame so the
        // hook never installs at all" -- and those have opposite meanings while looking
        // identical from outside. Bounded, so it cannot become the storm it replaces.
        static u32 lastS = 1, lastD = 1;
        static int pairs = 0;
        if (((u32)stg != lastS || (u32)det != lastD) && pairs < 8) {
            lastS = (u32)stg; lastD = (u32)det; ++pairs;
            HOTJOIN_LOG("uihook: implausible menu ptr stg=%08x det=%08x -- skipping "
                        "(s237 #%d; would have faulted at +0x60)\n",
                        (u32)stg, (u32)det, pairs);
        }
        return;
    }

    svt = *(u32*)((u32)stg + 0x60);
    dvt = *(u32*)((u32)det + 0x60);

    // s216-B: a menu object can be non-NULL while its vTable field reads 0 -- it exists but
    // is mid-build or mid-teardown. Measured: during the join at ee=591.16 BOTH vtables read
    // 00000000 while the menus were torn down for the level load.
    //
    // The first version of this re-check treated that as a layout disagreement and latched
    // `disproven`, permanently killing the hook on the first join -- worse than the
    // once-only install it replaced. A zero vTable is NOT "the layout is wrong", it is "not
    // ready yet", exactly like the NULL check above. Retry next frame.
    if (!svt || !dvt)
        return;

    // Self-check against a constant we know, before poking dispatch. Permanent stop: if the
    // layout is genuinely DIFFERENT (non-zero and not what we expect), never write.
    if (svt + 0x14 != stagingUpdateSlot) {
        disproven = 1;
        HOTJOIN_LOG("uihook: DISPROVEN -- staging vt %08x +0x14 != known %08x; "
                    "leaving dispatch alone (details vt %08x)\n",
            svt, stagingUpdateSlot, dvt);
        return;
    }

    slot = dvt + 0x14;
    cur  = *(u32*)slot;

    if (cur == (u32)&patchGameDetails)
        return;                     // already ours; the common case, costs a compare

    // Never store our own pointer as "the original" -- that would recurse forever. The
    // check above guarantees cur != patchGameDetails here.
    hjOrigGameDetailsUpdate = (int (*)(UiMenu_t*, int))cur;
    POKE_U32(slot, (u32)&patchGameDetails);
    ++installs;
    HOTJOIN_LOG("uihook: GAME_DETAILS update slot %08x -> patchGameDetails "
                "(orig %08x, verified against staging %08x) install #%d\n",
        slot, cur, stagingUpdateSlot, installs);
}

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
    int isTeams, itemSelected, isLoading, isRequstingTeamChange;

    // s236: do not dereference before checking. This prologue read four pointers
    // unguarded -- gameGetOptions()'s return and three fields of `ui` -- with no NULL
    // test anywhere in the function. s212 already records staging faulting at 0x6BF470
    // on a NULL gs, so the hazard is not hypothetical.
    //
    // Falls through to the original handler rather than returning, so staging keeps
    // working; stagingFunc is already the pass-through at the end of this function.
    //
    // Honesty about scope: this is HARDENING, not a fix for a reproduced fault. The TLB
    // storm s236 was written around turned out to come from hjInstallGameDetailsHook
    // (s237, confirmed on hardware), not from here -- patch symbols move between builds
    // and the pc attribution was off. No patchStaging fault has ever been observed.
    if (!gs || !ui || !gameGetOptions())
        return stagingFunc(ui, pad);

    isTeams = gameGetOptions()->GameFlags.MultiplayerGameFlags.Teams;
    itemSelected = *(int*)((u32)ui + 0x290);
    isLoading = *(u8*)((u32)ui + 0x2b6);
    isRequstingTeamChange = *(u8*)((u32)ui + 0x2c8);

    // s210-C: there is NO staging fallback, and there should not be one.
    //
    // s210 kept the prompt here as a backstop for routes that skip GAME DETAILS. The user
    // established that no such route exists: an invite is impossible from in-game, and
    // Quick Play only brings you to the game listing -- it never joins directly. Every
    // hot-join passes through GAME DETAILS, so the backstop was dead code that could only
    // ever misfire, and misfiring means blocking a staging screen with a live join in
    // flight, which is exactly what s210 moved the prompt away from. Deleted rather than
    // left dormant.

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
