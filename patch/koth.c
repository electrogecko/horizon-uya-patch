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

typedef struct KothHill {
    VECTOR position;
} KothHill_t;

static KothHill_t hills[KOTH_MAX_HILLS];
static int hillCount = 0;
static int initialized = 0;
static int handlerInstalled = 0;
static int nextScoreTickTime = 0;
static int gameOverTriggered = 0;
static int kothScores[GAME_MAX_PLAYERS];
static int lastBroadcastScore[GAME_MAX_PLAYERS];

static float clamp01(float value)
{
    if (value < 0.0f) return 0.0f;
    if (value > 1.0f) return 1.0f;
    return value;
}

static float clampf(float value, float min, float max)
{
    if (value < min) return min;
    if (value > max) return max;
    return value;
}

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
            ++hillCount;
        }
        ++moby;
    }

    initialized = 1;
}

static int playerInsideHill(Player *player)
{
    if (!player)
        return 0;

    int i;
    VECTOR delta;
    for (i = 0; i < hillCount; ++i) {
        vector_subtract(delta, player->playerPosition, hills[i].position);
        // ignore height to keep circle flat on ground
        delta[2] = 0;
        float sqrDist = vector_sqrmag(delta);
        if (sqrDist <= (KOTH_RING_RADIUS * KOTH_RING_RADIUS))
            return 1;
    }

    return 0;
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

static void kothDeclareWinner(int winnerIdx, int reason)
{
    GameSettings *gs = gameGetSettings();
    GameOptions *go = gameGetOptions();
    if (!gs || !go)
        return;

    int useTeams = go->GameFlags.MultiplayerGameFlags.Teams;
    int winnerId = useTeams ? gs->PlayerTeams[winnerIdx] : winnerIdx;
    if (winnerId < 0)
        return;

    gameSetWinner(winnerId, useTeams);
    gameEnd(reason);
    gameOverTriggered = 1;
}

static void kothCheckVictory(void)
{
    if (gameOverTriggered || gameHasEnded())
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

    if (gd->timeEnd > 0 && gameGetTime() >= gd->timeEnd && !isTie) {
        kothDeclareWinner(leaderIdx, GAME_END_TIME_UP);
    }
}

static void drawHill(VECTOR center, u32 color)
{
    const int MAX_SEGMENTS = 64;
    const int MIN_SEGMENTS = 8;
    QuadDef quad[3];
    gfxSetupEffectTex(&quad[0], FX_UNK_2, 0, 0x80);
    gfxSetupEffectTex(&quad[2], FX_CIRLCE_NO_FADED_EDGE, 0, 0x80);

    quad[0].uv[0] = (UV_t){0, 0};
    quad[0].uv[1] = (UV_t){0, 1};
    quad[0].uv[2] = (UV_t){1, 0};
    quad[0].uv[3] = (UV_t){1, 1};
    quad[1] = quad[0];
    quad[2] = quad[0];

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

    VECTOR xAxis = {KOTH_RING_RADIUS, 0, 0, 0};
    VECTOR zAxis = {0, KOTH_RING_RADIUS, 0, 0};
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

            gfxDrawQuad(quad[k], NULL);
            vector_rodrigues(vRadius, vRadius, yAxis, thetaStep);
            vector_outerproduct(tempRight, yAxis, vRadius);
            vector_normalize(tempRight, tempRight);
        }
    }

    // floor quad
    VECTOR offset = {0, 0, -1, 0};
    VECTOR corners[4];
    int j;
    for (j = 0; j < 4; ++j) {
        corners[j][0] = center[0] + signs[j][0] * halfX[0] + signs[j][1] * halfZ[0] + offset[0];
        corners[j][1] = center[1] + signs[j][0] * halfX[1] + signs[j][1] * halfZ[1] + offset[1];
        corners[j][2] = center[2] + signs[j][0] * halfX[2] + signs[j][1] * halfZ[2] + offset[2];
        corners[j][3] = 1;
    }

    QuadDef floorQuad;
    gfxSetupEffectTex(&floorQuad, FX_CIRLCE_NO_FADED_EDGE, 0, 0x80);
    floorQuad.uv[0] = (UV_t){0, 0};
    floorQuad.uv[1] = (UV_t){0, 1};
    floorQuad.uv[2] = (UV_t){1, 0};
    floorQuad.uv[3] = (UV_t){1, 1};
    floorQuad.rgba[0] = floorQuad.rgba[1] = floorQuad.rgba[2] = floorQuad.rgba[3] = (0x20 << 24) | baseRgb;
    for (j = 0; j < 4; ++j) {
        floorQuad.point[j][0] = corners[j][0];
        floorQuad.point[j][1] = corners[j][1];
        floorQuad.point[j][2] = corners[j][2];
        floorQuad.point[j][3] = corners[j][3];
    }
    gfxDrawQuad(floorQuad, NULL);
}

static void drawHills(void)
{
    u32 baseColor = 0x0080FF00; // green tint for hill marker
    int i;
    for (i = 0; i < hillCount; ++i) {
        drawHill(hills[i].position, baseColor);
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
