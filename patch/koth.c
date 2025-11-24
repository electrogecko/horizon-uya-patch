#include <tamtypes.h>

#include <libuya/stdio.h>
#include <libuya/string.h>
#include <libuya/player.h>
#include <libuya/utils.h>
#include <libuya/game.h>
#include <libuya/interop.h>
#include <libuya/moby.h>
#include <libuya/graphics.h>
#include <libuya/gamesettings.h>
#include <libuya/spawnpoint.h>
#include <libuya/ui.h>
#include <libuya/time.h>
#include <libuya/net.h>
#include <libuya/team.h>
#include <libuya/math.h>
#include "messageid.h"
#include "include/config.h"

extern PatchGameConfig_t gameConfig;

#define KOTH_MAX_HILLS         (8)
#define KOTH_RING_RADIUS       (10.0f)
#define KOTH_RING_HEIGHT       (1.0f)
#define KOTH_RING_ALPHA_SCALE  (1.0f)
#define KOTH_SCORE_TICK_MS     (TIME_SECOND)
#define KOTH_HILL_ACTIVE_MS    (TIME_SECOND * 60)

// Toggle how the active hill is selected each rotation window
// Define KOTH_RANDOM_ORDER to cycle hills in a deterministic randomized order without replacement.
// Leave undefined to rotate in fixed index order.
#define KOTH_RANDOM_ORDER

typedef struct KothHill {
    VECTOR position;
    Moby *moby;
    Moby *drawMoby;
    float scroll;
#ifdef KOTH_RANDOM_ORDER
    int orderIdx;
#endif
} KothHill_t;

static KothHill_t hills[KOTH_MAX_HILLS];
static int hillCount = 0;
static int initialized = 0;
static int handlerInstalled = 0;
static int nextScoreTickTime = 0;
static int gameOverTriggered = 0;
static int hillCycleStartTime = 0;
#ifdef KOTH_RANDOM_ORDER
static int hillOrder[KOTH_MAX_HILLS];
static int hillOrderCount = 0;
static u32 hillOrderSeed = 0;

// simple LCG for deterministic shuffling
static u32 kothRngNext(u32 *state)
{
    *state = (*state * 1664525u + 1013904223u);
    return *state;
}

static int kothRandRange(u32 *state, int min, int max)
{
    if (max <= min)
        return min;
    u32 r = kothRngNext(state);
    return min + (int)(r % (u32)(max - min));
}
#endif
static int kothScores[GAME_MAX_PLAYERS];
static int lastBroadcastScore[GAME_MAX_PLAYERS];

static float clampf(float value, float min, float max)
{
    if (value < min) return min;
    if (value > max) return max;
    return value;
}

static int kothGetActiveHillIndex(void);

static void vector_rodrigues(VECTOR output, VECTOR v, VECTOR axis, float angle)
{
    VECTOR k, v_cross, term1, term2, term3;
    float cosTheta = cosf(angle);
    float sinTheta = sinf(angle);

    vector_normalize(k, axis);
    vector_scale(term1, v, cosTheta);
    vector_outerproduct(v_cross, k, v);
    vector_scale(term2, v_cross, sinTheta);
    float dot = vector_innerproduct(k, v);
    vector_scale(term3, k, dot * (1.0f - cosTheta));
    vector_add(output, term1, term2);
    vector_add(output, output, term3);
    output[3] = v[3];
}

static void scanHillsOnce(void)
{
    if (initialized)
        return;

    memset(hills, 0, sizeof(hills));
    hillCount = 0;

    Moby* moby = mobyListGetStart();
    Moby* mobyEnd = mobyListGetEnd();
    while (moby < mobyEnd && hillCount < KOTH_MAX_HILLS) {
        if (moby->oClass == MOBY_ID_SIEGE_NODE) {
            vector_copy(hills[hillCount].position, moby->position);
            hills[hillCount].position[3] = 1;
            hills[hillCount].moby = moby;
            hills[hillCount].scroll = 0;
            hills[hillCount].drawMoby = mobySpawn(0x1c0d, 0);
            if (hills[hillCount].drawMoby) {
                vector_copy(hills[hillCount].drawMoby->position, moby->position);
                hills[hillCount].drawMoby->updateDist = -1;
                hills[hillCount].drawMoby->drawn = 1;
                hills[hillCount].drawMoby->opacity = 0;
                hills[hillCount].drawMoby->drawDist = 0x00;
                hills[hillCount].drawMoby->pUpdate = NULL; // set later
            }
            ++hillCount;
        }
        ++moby;
    }

#ifdef KOTH_RANDOM_ORDER
    hillOrderCount = hillCount;
    int i;
    for (i = 0; i < hillCount; ++i)
        hillOrder[i] = i;
    // deterministic Fisher-Yates shuffle
    hillOrderSeed = 0;
    GameData *gd = gameGetData();
    if (gd)
        hillOrderSeed = (u32)gd->timeStart;
    for (i = hillCount - 1; i > 0; --i) {
        int j = kothRandRange(&hillOrderSeed, 0, i + 1);
        int tmp = hillOrder[i];
        hillOrder[i] = hillOrder[j];
        hillOrder[j] = tmp;
    }
#endif

    initialized = 1;
}

static int playerInsideHill(Player *player)
{
    if (!player)
        return 0;

    int activeIdx = kothGetActiveHillIndex();
    if (activeIdx < 0 || activeIdx >= hillCount)
        return 0;

    VECTOR delta;
    vector_subtract(delta, player->playerPosition, hills[activeIdx].position);
    // ignore height to keep circle flat on ground
    delta[2] = 0;
    float sqrDist = vector_sqrmag(delta);
    return sqrDist <= (KOTH_RING_RADIUS * KOTH_RING_RADIUS);
}

static void broadcastScore(int playerIdx)
{
    void *connection = netGetDmeServerConnection();
    if (!connection)
        return;

    KothScoreUpdate_t msg;
    msg.PlayerIdx = (char)playerIdx;
    msg.Score = (short)kothScores[playerIdx];
    msg.Padding = 0;

    netBroadcastCustomAppMessage(connection, CUSTOM_MSG_ID_KOTH_SCORE_UPDATE, sizeof(msg), &msg);
    lastBroadcastScore[playerIdx] = kothScores[playerIdx];
}

static void updateScores(void)
{
    Player **players = playerGetAll();
    int i;
    for (i = 0; i < GAME_MAX_PLAYERS; ++i) {
        Player *p = players[i];
        if (!p || playerIsDead(p))
            continue;

        if (playerInsideHill(p) && p->isLocal) {
            ++kothScores[p->mpIndex];
            if (kothScores[p->mpIndex] != lastBroadcastScore[p->mpIndex])
                broadcastScore(p->mpIndex);
        }
    }
}

static int kothGetScoreLimit(void)
{
    int setting = (int)gameConfig.kothScoreLimit;
    if (setting <= 0)
        return 0;

    return setting * 50;
}

static int kothFindLeader(int *outScore, int *outTie)
{
    GameSettings *gs = gameGetSettings();
    if (!gs)
        return -1;

    Player **players = playerGetAll();
    char seen[GAME_MAX_PLAYERS];
    int leaderIdx = -1;
    int leaderScore = 0;
    int isTie = 0;
    int i;

    memset(seen, 0, sizeof(seen));
    for (i = 0; i < GAME_MAX_PLAYERS; ++i) {
        Player *p = players[i];
        if (!p)
            continue;

        int idx = p->mpIndex;
        if (idx < 0 || idx >= GAME_MAX_PLAYERS)
            continue;
        if (seen[idx])
            continue;
        if (!gs->PlayerNames[idx][0])
            continue;

        seen[idx] = 1;
        int score = kothScores[idx];
        if (leaderIdx < 0 || score > leaderScore) {
            leaderIdx = idx;
            leaderScore = score;
            isTie = 0;
        } else if (score == leaderScore) {
            isTie = 1;
        }
    }

    if (outScore)
        *outScore = leaderScore;
    if (outTie)
        *outTie = isTie;
    return leaderIdx;
}

static int kothSetWinnerFields(int winnerIdx, int reason, int endGame)
{
    GameSettings *gs = gameGetSettings();
    GameOptions *go = gameGetOptions();
    GameData *gd = gameGetData();
    if (!gs || !go || !gd)
        return 0;

    int useTeams = go->GameFlags.MultiplayerGameFlags.Teams;
    int winnerId = useTeams ? gs->PlayerTeams[winnerIdx] : winnerIdx;
    if (winnerId < 0)
        return 0;

    gd->gameEndReason = reason;
    gameSetWinner(winnerId, useTeams);
    if (endGame)
        gameEnd(reason);
    gameOverTriggered = 1;
    return 1;
}

static void kothDeclareWinner(int winnerIdx, int reason)
{
    if (!kothSetWinnerFields(winnerIdx, reason, 1))
        return;
}

static void kothCheckVictory(void)
{
    if (gameOverTriggered)
        return;
    if (!gameAmIHost())
        return;

    GameData *gd = gameGetData();
    if (!gd)
        return;

    int leaderScore = 0;
    int isTie = 0;
    int leaderIdx = kothFindLeader(&leaderScore, &isTie);
    if (leaderIdx < 0)
        return;

    int scoreLimit = kothGetScoreLimit();
    if (scoreLimit > 0 && leaderScore >= scoreLimit && !isTie) {
        kothDeclareWinner(leaderIdx, GAME_END_TEAM_WIN);
        return;
    }

    int timerActive = (gd->timeStart > 0) && (gd->timeEnd > gd->timeStart);
    if (timerActive && gameGetTime() >= gd->timeEnd && !isTie) {
        if (gameHasEnded())
            kothSetWinnerFields(leaderIdx, GAME_END_TIME_UP, 0);
        else
            kothDeclareWinner(leaderIdx, GAME_END_TIME_UP);
    }
}

static void drawHillAt(VECTOR center, u32 color, float *scroll)
{
    const int MAX_SEGMENTS = 64;
    const int MIN_SEGMENTS = 8;
    QuadDef quad[3];
    gfxSetupEffectTex(&quad[0], FX_VISIBOMB_HORIZONTAL_LINES, 0, 0x80);
    gfxSetupEffectTex(&quad[2], FX_CIRLCE_NO_FADED_EDGE, 0, 0x80);

    quad[0].uv[0] = (UV_t){0, 0};
    quad[0].uv[1] = (UV_t){0, 1};
    quad[0].uv[2] = (UV_t){1, 0};
    quad[0].uv[3] = (UV_t){1, 1};
    quad[1] = quad[0];
    quad[2] = quad[0];

    float uvOffset = 0;
    quad[0].uv[0].y += uvOffset;
    quad[0].uv[1].y -= uvOffset;
    quad[0].uv[2].y += uvOffset;
    quad[0].uv[3].y -= uvOffset;
    quad[1] = quad[0];

    int alphaOuterNear = (int)(0x00 * KOTH_RING_ALPHA_SCALE) & 0xFF;
    int alphaOuterFar = (int)(0x30 * KOTH_RING_ALPHA_SCALE);
    if (alphaOuterFar > 0xFF) alphaOuterFar = 0xFF;
    int alphaMidNear = (int)(0x50 * KOTH_RING_ALPHA_SCALE);
    if (alphaMidNear > 0xFF) alphaMidNear = 0xFF;
    int alphaMidFar = (int)(0x20 * KOTH_RING_ALPHA_SCALE);
    if (alphaMidFar > 0xFF) alphaMidFar = 0xFF;
    int alphaCenter = (int)(0x30 * KOTH_RING_ALPHA_SCALE);
    if (alphaCenter > 0xFF) alphaCenter = 0xFF;

    u32 baseRgb = color & 0x00FFFFFF;
    quad[0].rgba[0] = quad[0].rgba[1] = (alphaOuterNear << 24) | baseRgb;
    quad[0].rgba[2] = quad[0].rgba[3] = (alphaOuterFar << 24) | baseRgb;
    quad[1].rgba[0] = quad[1].rgba[1] = (alphaMidNear << 24) | baseRgb;
    quad[1].rgba[2] = quad[1].rgba[3] = (alphaMidFar << 24) | baseRgb;
    quad[2].rgba[0] = quad[2].rgba[1] = quad[2].rgba[2] = quad[2].rgba[3] = (alphaCenter << 24) | baseRgb;

    VECTOR xAxis = {KOTH_RING_RADIUS * 2, 0, 0, 0};
    VECTOR zAxis = {0, KOTH_RING_RADIUS * 2, 0, 0};
    VECTOR yAxis = {0, 0, KOTH_RING_HEIGHT, 0};
    VECTOR tempRight, tempUp, halfX, halfZ, vRadius, tempCenter;
    vector_scale(halfX, xAxis, .5);
    vector_scale(halfZ, zAxis, .5);
    float fRadius = vector_length(halfX);
    int signs[4][2] = {{1, -1}, {-1, -1}, {1, 1}, {-1, 1}};
    vector_normalize(yAxis, yAxis);

    vector_outerproduct(tempRight, yAxis, halfX);
    vector_normalize(tempRight, tempRight);
    vector_scale(tempRight, tempRight, 1);
    vector_scale(tempUp, yAxis, KOTH_RING_HEIGHT * 0.5f);

    float segmentSize = 1;
    int segments = (int)((2 * MATH_PI * fRadius) / segmentSize);
    float thetaStep = 2 * MATH_PI / clampf((float)segments, (float)MIN_SEGMENTS, (float)MAX_SEGMENTS);

    int k, i;
    for (k = 0; k < 2; ++k) {
        vector_copy(vRadius, halfX);
        for (i = 0; i < segments; ++i) {
            vector_add(tempCenter, center, vRadius);
            tempCenter[2] += k * KOTH_RING_HEIGHT;
            int j;
            for (j = 0; j < 4; ++j) {
                quad[k].point[j][0] = tempCenter[0] + signs[j][0] * tempRight[0] + signs[j][1] * tempUp[0];
                quad[k].point[j][1] = tempCenter[1] + signs[j][0] * tempRight[1] + signs[j][1] * tempUp[1];
                quad[k].point[j][2] = tempCenter[2] + signs[j][0] * tempRight[2] + signs[j][1] * tempUp[2];
                quad[k].point[j][3] = 1;
            }

            quad[k].uv[0].x = quad[k].uv[1].x = 0 - *scroll;
            quad[k].uv[2].x = quad[k].uv[3].x = 1 - *scroll;

            gfxDrawQuad(quad[k], NULL);
            vector_rodrigues(vRadius, vRadius, yAxis, thetaStep);
            vector_outerproduct(tempRight, yAxis, vRadius);
            vector_normalize(tempRight, tempRight);
        }
    }
    *scroll += .007f;

    // floor quad
    VECTOR corners[4];
    vector_copy(corners[0], (VECTOR){center[0] - fRadius, center[1] - fRadius, center[2], 0});
    vector_copy(corners[1], (VECTOR){center[0] + fRadius, center[1] - fRadius, center[2], 0});
    vector_copy(corners[2], (VECTOR){center[0] + fRadius, center[1] + fRadius, center[2], 0});
    vector_copy(corners[3], (VECTOR){center[0] - fRadius, center[1] + fRadius, center[2], 0});

    QuadDef floorQuad;
    gfxSetupEffectTex(&floorQuad, FX_CIRLCE_NO_FADED_EDGE, 0, 0x80);
    floorQuad.uv[0] = (UV_t){0, 0};
    floorQuad.uv[1] = (UV_t){0, 1};
    floorQuad.uv[2] = (UV_t){1, 0};
    floorQuad.uv[3] = (UV_t){1, 1};
    floorQuad.rgba[0] = floorQuad.rgba[1] = floorQuad.rgba[2] = floorQuad.rgba[3] = (0x20 << 24) | baseRgb;
    vector_copy(floorQuad.point[0], corners[1]);
    vector_copy(floorQuad.point[1], corners[0]);
    vector_copy(floorQuad.point[2], corners[2]);
    vector_copy(floorQuad.point[3], corners[3]);
    gfxDrawQuad(floorQuad, NULL);
}

static KothHill_t *kothFindHill(Moby *moby)
{
    int i;
    for (i = 0; i < hillCount; ++i) {
        if (hills[i].moby == moby || hills[i].drawMoby == moby)
            return &hills[i];
    }
    return NULL;
}

static void kothEnsureCycleStart(void)
{
    if (hillCycleStartTime == 0 && hillCount > 0) {
        GameData *gd = gameGetData();
        if (gd && gd->timeStart > 0)
            hillCycleStartTime = gd->timeStart;
        else
            hillCycleStartTime = gameGetTime();
    }
}

static int kothGetActiveHillIndex(void)
{
    if (hillCount <= 0)
        return -1;

    kothEnsureCycleStart();

    int duration = KOTH_HILL_ACTIVE_MS;
    if (duration <= 0)
        return 0;

    int elapsed = gameGetTime() - hillCycleStartTime;
    if (elapsed < 0)
        elapsed = 0;

    int idx = (elapsed / duration) % hillCount;
#ifdef KOTH_RANDOM_ORDER
    if (hillOrderCount <= 0 || idx >= hillOrderCount)
        return idx;
    return hillOrder[idx];
#else
    return idx;
#endif
}

static void drawHill(Moby *moby)
{
    u32 baseColor = 0x0080FF00; // green tint for hill marker
    KothHill_t *hill = kothFindHill(moby);
    float *scroll = hill ? &hill->scroll : NULL;
    float fallbackScroll = 0;
    if (!scroll)
        scroll = &fallbackScroll;
    drawHillAt(moby->position, baseColor, scroll);
}

static void hillUpdate(Moby *moby)
{
    gfxRegistserDrawFunction(&drawHill, moby);
}

static void drawHills(void)
{
    int activeIdx = kothGetActiveHillIndex();
    int i;
    for (i = 0; i < hillCount; ++i) {
        if (hills[i].drawMoby) {
            hills[i].drawMoby->pUpdate = (i == activeIdx) ? &hillUpdate : NULL;
        } else if (i == activeIdx) {
            drawHillAt(hills[i].position, 0x0080FF00, &hills[i].scroll);
        }
    }
}

static void drawHud(void)
{
    GameSettings *gs = gameGetSettings();
    if (!gs)
        return;

    // gather entries
    typedef struct {
        int idx;
        int score;
    } Entry;
    Entry entries[GAME_MAX_PLAYERS];
    char seen[GAME_MAX_PLAYERS];
    int count = 0;

    memset(seen, 0, sizeof(seen));
    Player **players = playerGetAll();
    int i;
    for (i = 0; i < GAME_MAX_PLAYERS; ++i) {
        Player *p = players[i];
        if (!p)
            continue;

        int idx = p->mpIndex;
        if (idx < 0 || idx >= GAME_MAX_PLAYERS)
            continue;
        if (seen[idx])
            continue;
        if (!gs->PlayerNames[idx][0])
            continue;

        seen[idx] = 1;
        entries[count].idx = idx;
        entries[count].score = kothScores[idx];
        ++count;
    }

    // sort desc by score (small N)
    int swapped = 1;
    while (swapped) {
        swapped = 0;
        for (i = 0; i < count - 1; ++i) {
            if (entries[i].score < entries[i + 1].score) {
                Entry tmp = entries[i];
                entries[i] = entries[i + 1];
                entries[i + 1] = tmp;
                swapped = 1;
            }
        }
    }

    float startX = 20;
    float startY = SCREEN_HEIGHT * 0.35f;
    float lineH = 16.0f;
    gfxScreenSpaceText(startX, startY - lineH, 1, 1, 0x80FFFFFF, "KOTH", -1, TEXT_ALIGN_TOPLEFT, FONT_BOLD);

    for (i = 0; i < count; ++i) {
        int idx = entries[i].idx;
        char line[64];
        snprintf(line, sizeof(line), "%s: %d", gs->PlayerNames[idx], entries[i].score);
        int team = gs->PlayerTeams[idx];
        u32 color = (0x80 << 24) | ((team >= 0 && team < 8) ? TEAM_COLORS[team] : 0x00FFFFFF);
        gfxScreenSpaceText(startX, startY + (i * lineH), 1, 1, color, line, -1, TEXT_ALIGN_TOPLEFT, FONT_DEFAULT);
    }
}

int kothOnReceiveScore(void *connection, void *data)
{
    KothScoreUpdate_t *msg = (KothScoreUpdate_t*)data;
    int idx = msg->PlayerIdx;
    if (idx < 0 || idx >= GAME_MAX_PLAYERS)
        return sizeof(KothScoreUpdate_t);

    kothScores[idx] = msg->Score;
    return sizeof(KothScoreUpdate_t);
}

void kothReset(void)
{
    initialized = 0;
    handlerInstalled = 0;
    hillCount = 0;
    nextScoreTickTime = 0;
    gameOverTriggered = 0;
    hillCycleStartTime = 0;
#ifdef KOTH_RANDOM_ORDER
    hillOrderCount = 0;
#endif
    memset(hills, 0, sizeof(hills));
    memset(kothScores, 0, sizeof(kothScores));
    memset(lastBroadcastScore, 0, sizeof(lastBroadcastScore));
}

void kothInit(void)
{
    if (!handlerInstalled) {
        netInstallCustomMsgHandler(CUSTOM_MSG_ID_KOTH_SCORE_UPDATE, &kothOnReceiveScore);
        handlerInstalled = 1;
    }
    scanHillsOnce();
}

void kothTick(void)
{
    if (!isInGame())
        return;

    kothInit();
    drawHills();
    drawHud();

    int gameTime = gameGetTime();
    if (nextScoreTickTime == 0)
        nextScoreTickTime = gameTime + KOTH_SCORE_TICK_MS;

    if (gameTime >= nextScoreTickTime) {
        updateScores();
        nextScoreTickTime = gameTime + KOTH_SCORE_TICK_MS;
    }

    kothCheckVictory();
}
