#include <tamtypes.h>

#include <libuya/stdio.h>
#include <libuya/string.h>
#include <libuya/player.h>
#include <libuya/utils.h>
#include <libuya/game.h>
#include <libuya/pad.h>
#include <libuya/uya.h>
#include <libuya/weapon.h>
#include <libuya/interop.h>
#include <libuya/moby.h>
#include <libuya/graphics.h>
#include <libuya/gamesettings.h>
#include <libuya/spawnpoint.h>
#include <libuya/team.h>
#include <libuya/ui.h>
#include <libuya/time.h>
#include <libuya/camera.h>
#include <libuya/gameplay.h>
#include <libuya/map.h>
#include <libuya/collision.h>
#include <libuya/guber.h>
#include <libuya/sound.h>
#include <libuya/music.h>
#include <libuya/math.h>
#include "config.h"
#include "include/koth.h"

#define HILL_OCLASS (0x3000)
#define MAX_SEGMENTS (64)
#define MIN_SEGMENTS (4)
#define TEXTURE_SCROLL_SPEED (0.007)
#define EDGE_OPACITY (0x40)
#define TEXTURE_EDGE_TRIM_U (0.0f)
#define TEXTURE_EDGE_TRIM_V (0.25f)
#define KOTH_HILL_SCALE_BITS (0xF)
#define KOTH_DEFAULT_HILL_DURATION_SECONDS (60)

int spawned = 0;
/* Prepare arrays for strip vertices */
vec3 positions[2][(MAX_SEGMENTS + 1) * 2];
int colors[2][(MAX_SEGMENTS + 1) * 2];
UV_t uvs[2][(MAX_SEGMENTS + 1) * 2];
int cachedSegments = -1;
int cachedIsCircle = -1;
float scrollQuad = 0;

typedef struct kothInfo {
    int gameState;
    int foundMoby;
    Moby* kothMoby;
} kothInfo_t;
kothInfo_t kothInfo;


typedef struct hillPvar {
    int cuboidIndex[32];
    bool foundMoby;
    bool isCircle;
    short pad;
    Player* playersIn[GAME_MAX_PLAYERS];
    Cuboid* currentCuboid;
    int teamTime[8];
    u32 color;
} hillPvar_t;

static const float KOTH_HILL_SCALE_TABLE[] = { 1.f, 1.5f, 2.f, 2.5f, 3.f, 3.5f, 4.f };
static const int KOTH_HILL_DURATION_TABLE[] = { 60, 120, 180, 240, 300 };
static const int KOTH_SCORE_LIMIT_TABLE[] = { 0, 50, 100, 150, 200, 250, 300, 350, 400, 450, 500, 750, 1000, 2000 };

typedef struct KothRuntimeConfig {
    int scoreLimit;
    int hillDurationMs;
    float hillScale;
} KothRuntimeConfig_t;

static KothRuntimeConfig_t kothConfig = {
    .scoreLimit = 0,
    .hillDurationMs = KOTH_DEFAULT_HILL_DURATION_SECONDS * TIME_SECOND,
    .hillScale = 1.f
};

static const Cuboid HILL_CUBOID_TEMPLATE = {
    .matrix = {
        {20, 0, 0, 0},
        {0, 30, 0, 0},
        {0, 0, 1, 0}
    },
    .pos = {519.58356, 398.7586, 201.38, 1},
    .imatrix = 0,
    .rot = {0, 0, 0, 0}
};

static Cuboid rawr = {
    .matrix = {
        {20, 0, 0, 0},
        {0, 30, 0, 0},
        {0, 0, 1, 0}
    },
    .pos = {519.58356, 398.7586, 201.38, 1},
    .imatrix = 0,
    .rot = {0, 0, 0, 0}
};

static void kothUpdateHillScale(float scale)
{
    rawr = HILL_CUBOID_TEMPLATE;
    rawr.matrix.v0[0] *= scale;
    rawr.matrix.v1[1] *= scale;
    cachedSegments = -1;
    cachedIsCircle = -1;
}

int hillCheckIfInside(Cuboid cube, VECTOR playerPos, char isCircle)
{
    MATRIX rotMatrix;
    matrix_unit(rotMatrix);
    matrix_rotate_x(rotMatrix, rotMatrix, cube.rot[0]);
    matrix_rotate_y(rotMatrix, rotMatrix, cube.rot[1]);
    matrix_rotate_z(rotMatrix, rotMatrix, cube.rot[2]);

    // get imatrix
    MATRIX invMatrix;
    matrix_unit(invMatrix);
    matrix_inverse(invMatrix, rotMatrix);
    memcpy(&cube.imatrix, invMatrix, sizeof(mtx3));

    VECTOR delta;
    vector_subtract(delta, playerPos, (VECTOR) { cube.pos[0], cube.pos[1], cube.pos[2], 0 });
    vector_apply(delta, delta, invMatrix);
    VECTOR xAxis = { cube.matrix.v0[0], cube.matrix.v1[0], cube.matrix.v2[0], 0 };
    VECTOR zAxis = { cube.matrix.v0[1], cube.matrix.v1[1], cube.matrix.v2[1], 0 };
    VECTOR yAxis = { cube.matrix.v0[2], cube.matrix.v1[2], cube.matrix.v2[2], 0 };

    float halfWidth = vector_length(xAxis) * .5;
    float halfDepth = vector_length(zAxis) * .5;
    float yHeight = vector_length(yAxis);

    if (delta[2] < -1.25 || delta[2] > yHeight + 6) {
        return 0;
    }
    if (isCircle) {
        float radius = halfWidth;
        float distSq = delta[0] * delta[0] + delta[1] * delta[1];
        return (distSq <= radius * radius);
    }
    else {
        int x = delta[0] < -halfWidth || delta[0] > halfWidth;
        int z = delta[1] < -halfDepth || delta[1] > halfDepth;
        return (x || z) ? 0 : 1;
    }
}

void hillPlayerUpdates(Moby* this)
{
    hillPvar_t* pvar = (hillPvar_t*)this->pVar;
    GameSettings* gs = gameGetSettings();
    if (!gs)
        return;

    int playerCount = gs->PlayerCount;
    int i;
    for (i = 0; i < playerCount; ++i) {
        Player* player = playerGetFromSlot(i);
        if (!player || playerIsDead(player))
            continue;

        int in = hillCheckIfInside(*pvar->currentCuboid, player->playerPosition, pvar->isCircle);
        printf("\ninside hill: %d", in);
        if (in) {
            pvar->color = TEAM_COLORS[player->mpTeam];
        }
        else {
            pvar->color = 0x00ffffff;
        }

    }
}

void vector_rodrigues(VECTOR output, VECTOR v, VECTOR axis, float angle)
{
    VECTOR k, v_cross, term1, term2, term3;
    float cosTheta = cosf(angle);
    float sinTheta = sinf(angle);

    // normalize axis into k
    vector_normalize(k, axis);

    // term1 = v * cos(theta)
    vector_scale(term1, v, cosTheta);

    // term2 = (k x v) * sin(theta)
    vector_outerproduct(v_cross, k, v);  // cross product
    vector_scale(term2, v_cross, sinTheta);

    // term3 = k * (k . v) * (1 - cos(theta))
    float dot = vector_innerproduct(k, v);
    vector_scale(term3, k, dot * (1.0f - cosTheta));

    // output = term1 + term2 + term3
    vector_add(output, term1, term2);
    vector_add(output, output, term3);

    // preserve homogeneous component
    output[3] = v[3];
}

void circleMeFinal_StripMe(Moby* this, Cuboid cube)
{
    hillPvar_t* pvar = (hillPvar_t*)this->pVar;
    int isCircle = pvar->isCircle;
    u32 baseColor = pvar->color;
    int i, edge, s;

    /* Setup rotation matrix from cube */
    MATRIX rotMatrix;
    matrix_unit(rotMatrix);
    matrix_rotate_x(rotMatrix, rotMatrix, cube.rot[0]);
    matrix_rotate_y(rotMatrix, rotMatrix, cube.rot[1]);
    matrix_rotate_z(rotMatrix, rotMatrix, cube.rot[2]);

    /* Extract axes from cube matrix */
    VECTOR center, xAxis, zAxis, yAxis, halfX, halfZ;
    vector_copy(center, cube.pos);
    vector_copy(xAxis, (VECTOR) { cube.matrix.v0[0], cube.matrix.v1[0], cube.matrix.v2[0], 0 });
    vector_copy(zAxis, (VECTOR) { cube.matrix.v0[1], cube.matrix.v1[1], cube.matrix.v2[1], 0 });
    vector_copy(yAxis, (VECTOR) { cube.matrix.v0[2], cube.matrix.v1[2], cube.matrix.v2[2], 0 });

    /* Apply rotation to axes */
    vector_apply(xAxis, xAxis, rotMatrix);
    vector_apply(zAxis, zAxis, rotMatrix);
    vector_apply(yAxis, yAxis, rotMatrix);

    vector_scale(halfX, xAxis, 0.5f);
    vector_scale(halfZ, zAxis, 0.5f);
    vector_normalize(yAxis, yAxis);

    float fRadius = vector_length(halfX);

    /* ===== Calculate segment count ===== */
    int segmentSize = 2;
    int segments;

    if (isCircle) {
        segments = clamp((2 * MATH_PI * fRadius) / segmentSize, MIN_SEGMENTS, MAX_SEGMENTS);
    }
    else {
        /* For square, calculate total segments around perimeter */
        float sideLenX = vector_length(xAxis);
        float sideLenZ = vector_length(zAxis);
        float perimeter = (sideLenX + sideLenZ) * 2.0f;
        segments = clamp((int)(perimeter / segmentSize), MIN_SEGMENTS, MAX_SEGMENTS);
    }

    /* ===== Setup rendering ===== */
    int floorTex = isCircle ? FX_CIRLCE_NO_FADED_EDGE : FX_SQUARE_FLAT_1;
    int ringTex = FX_TIRE_TRACKS;

    /* UV trimming to remove transparent edges */
    float uMin = TEXTURE_EDGE_TRIM_U;
    float uMax = 1.0f - TEXTURE_EDGE_TRIM_U;
    float vMin = TEXTURE_EDGE_TRIM_V;
    float vMax = 1.0f - TEXTURE_EDGE_TRIM_V;
    float uRange = uMax - uMin;
    float vRange = vMax - vMin;

    /* Initialize strip drawing */
    gfxDrawStripInit();
    gfxAddRegister(8, 0);
    gfxAddRegister(0x14, 0xff9000000260);
    gfxAddRegister(6, gfxGetEffectTex(ringTex));
    gfxAddRegister(0x47, 0x513f1);
    gfxAddRegister(0x42, 0x8000000044);

    /* === Setup shape-specific parameters === */
    VECTOR corners[4], vRadius;
    int segmentsPerEdge[4];
    float thetaStep;

    if (isCircle) {
        thetaStep = (2.0f * MATH_PI) / segments;
    }
    else {
        /* Calculate corners */
        float hx0 = halfX[0], hx1 = halfX[1], hx2 = halfX[2];
        float hz0 = halfZ[0], hz1 = halfZ[1], hz2 = halfZ[2];

        vector_copy(corners[0], (VECTOR) { center[0] - hx0 - hz0, center[1] - hx1 - hz1, center[2] - hx2 - hz2, 0 });
        vector_copy(corners[1], (VECTOR) { center[0] + hx0 - hz0, center[1] + hx1 - hz1, center[2] + hx2 - hz2, 0 });
        vector_copy(corners[2], (VECTOR) { center[0] + hx0 + hz0, center[1] + hx1 + hz1, center[2] + hx2 + hz2, 0 });
        vector_copy(corners[3], (VECTOR) { center[0] - hx0 + hz0, center[1] - hx1 + hz1, center[2] - hx2 + hz2, 0 });

        /* Calculate segments per edge proportionally */
        float sideLenX = vector_length(xAxis);
        float sideLenZ = vector_length(zAxis);
        float perimeter = (sideLenX + sideLenZ) * 2.0f;

        segmentsPerEdge[0] = segmentsPerEdge[2] = (int)((sideLenX / perimeter) * segments);
        segmentsPerEdge[1] = segmentsPerEdge[3] = (int)((sideLenZ / perimeter) * segments);

        /* Ensure we use all segments */
        segmentsPerEdge[0] += segments - (segmentsPerEdge[0] + segmentsPerEdge[1] + segmentsPerEdge[2] + segmentsPerEdge[3]);
    }

    int numSegments = (segments + 1) * 2;
    VECTOR tempRight, tempUp;

    /* === Generate positions once (only if not cached) === */
    if (cachedSegments != segments || cachedIsCircle != isCircle) {
        if (isCircle) vector_copy(vRadius, halfX);

        for (i = 0; i <= segments; i++) {
            VECTOR pos;

            if (isCircle) {
                /* Calculate position on circle */
                vector_add(pos, center, vRadius);

                /* Calculate tangent for quad orientation */
                vector_outerproduct(tempRight, yAxis, vRadius);
                vector_normalize(tempRight, tempRight);
                vector_copy(tempUp, yAxis);

                /* Rotate radius for next segment */
                vector_rodrigues(vRadius, vRadius, yAxis, thetaStep);
            }
            else {
                /* Determine which edge we're on */
                int accumulatedSegs = 0;
                int currentEdge = 0;
                int localS = i;

                for (edge = 0; edge < 4; edge++) {
                    if (i <= accumulatedSegs + segmentsPerEdge[edge]) {
                        currentEdge = edge;
                        localS = i - accumulatedSegs;
                        break;
                    }
                    accumulatedSegs += segmentsPerEdge[edge];
                }

                VECTOR p0, p1, edgeDir;
                vector_copy(p0, corners[currentEdge]);
                vector_copy(p1, corners[(currentEdge + 1) & 3]);

                vector_subtract(edgeDir, p1, p0);
                vector_normalize(edgeDir, edgeDir);

                float t = (float)localS / segmentsPerEdge[currentEdge];
                vector_lerp(pos, p0, p1, t);

                /* For square, vertices are just offset in Z direction */
                vector_copy(tempRight, (VECTOR) { 0, 0, 0, 0 });
                vector_copy(tempUp, (VECTOR) { 0, 0, 0, 0 });
            }

            int idx = i * 2;

            /* === Upper ring positions === */
            positions[0][idx][0] = pos[0] + tempRight[0] - tempUp[0];
            positions[0][idx][1] = pos[1] + tempRight[1] - tempUp[1];
            positions[0][idx][2] = pos[2] + tempRight[2] - tempUp[2] - 1;

            positions[0][idx + 1][0] = pos[0] + tempRight[0] + tempUp[0];
            positions[0][idx + 1][1] = pos[1] + tempRight[1] + tempUp[1];
            positions[0][idx + 1][2] = pos[2] + tempRight[2] + tempUp[2] + 1;

            /* === Lower ring positions === */
            VECTOR offsetPos;
            vector_add(offsetPos, pos, (VECTOR) { 0, 0, 2, 0 });

            positions[1][idx][0] = offsetPos[0] + tempRight[0] + tempUp[0];
            positions[1][idx][1] = offsetPos[1] + tempRight[1] + tempUp[1];
            positions[1][idx][2] = offsetPos[2] + tempRight[2] + tempUp[2] + 1;

            positions[1][idx + 1][0] = offsetPos[0] + tempRight[0] - tempUp[0];
            positions[1][idx + 1][1] = offsetPos[1] + tempRight[1] - tempUp[1];
            positions[1][idx + 1][2] = offsetPos[2] + tempRight[2] - tempUp[2] - 1;
        }

        cachedSegments = segments;
        cachedIsCircle = isCircle;
    }

    /* === Calculate distance-based opacity === */
    Player* player = playerGetFromSlot(0);
    VECTOR delta;
    vector_subtract(delta, center, player->playerPosition);
    float distance = vector_length(delta);

    float opacityFactor = 1.0f;
    // if (distance > 52.0f) {
    //     opacityFactor = 1.0f - clamp((distance - 52.0f) / 12.0f, 0.0f, 1.0f);
    // }

    /* === Update colors and UVs every frame === */
    float trimmedU = uMin + (scrollQuad - floorf(scrollQuad)) * uRange;

    for (i = 0; i <= segments; i++) {
        float trimmedV = vMin + (((float)i / segmentSize) - floorf((float)i / segmentSize)) * vRange;
        int idx = i * 2;

        /*
         === Order of colors:
         - top of upper strip
         - bottom of upper strip
         - top of lower strip
         - bottom oflower strip
        */
        colors[1][idx] = ((0x10 * (int)opacityFactor) << 24) | baseColor;
        colors[1][idx + 1] = ((0x30 * (int)opacityFactor) << 24) | baseColor;
        colors[0][idx + 1] = ((0x50 * (int)opacityFactor) << 24) | baseColor;
        colors[0][idx] = ((0x10 * (int)opacityFactor) << 24) | baseColor;

        uvs[0][idx].x = uvs[1][idx].x = trimmedU;
        uvs[0][idx].y = uvs[0][idx + 1].y = uvs[1][idx].y = uvs[1][idx + 1].y = trimmedV;
        uvs[0][idx + 1].x = trimmedU - 0.3f;
        uvs[1][idx + 1].x = trimmedU + 0.3f;
    }

    /* === Draw both rings === */
    gfxDrawStrip(numSegments, positions[0], colors[0], uvs[0], 1);
    gfxDrawStrip(numSegments, positions[1], colors[1], uvs[1], 1);

    /* Animate texture scroll */
    scrollQuad += TEXTURE_SCROLL_SPEED;
    if (scrollQuad >= 1.0f) scrollQuad -= 1.0f;

    /* ===== Draw floor quad ===== */
    QuadDef floorQuad;
    gfxSetupEffectTex(&floorQuad, floorTex, DRAW_TYPE_NORMAL, 0x30);

    /* Offset floor down slightly */
    VECTOR offset = { 0, 0, -1, 0 };
    VECTOR rotatedOffset;
    vector_apply(rotatedOffset, offset, rotMatrix);

    /* Create floor corners */
    VECTOR floorCorners[4];
    if (isCircle) {
        vector_copy(floorCorners[0], (VECTOR) { center[0] - fRadius, center[1] - fRadius, center[2], 0 });
        vector_copy(floorCorners[1], (VECTOR) { center[0] + fRadius, center[1] - fRadius, center[2], 0 });
        vector_copy(floorCorners[2], (VECTOR) { center[0] + fRadius, center[1] + fRadius, center[2], 0 });
        vector_copy(floorCorners[3], (VECTOR) { center[0] - fRadius, center[1] + fRadius, center[2], 0 });
    }
    else {
        vector_copy(floorCorners[0], (VECTOR) { center[0] - halfX[0] - halfZ[0], center[1] - halfX[1] - halfZ[1], center[2] - halfX[2] - halfZ[2], 0 });
        vector_copy(floorCorners[1], (VECTOR) { center[0] + halfX[0] - halfZ[0], center[1] + halfX[1] - halfZ[1], center[2] + halfX[2] - halfZ[2], 0 });
        vector_copy(floorCorners[2], (VECTOR) { center[0] + halfX[0] + halfZ[0], center[1] + halfX[1] + halfZ[1], center[2] + halfX[2] + halfZ[2], 0 });
        vector_copy(floorCorners[3], (VECTOR) { center[0] - halfX[0] + halfZ[0], center[1] - halfX[1] + halfZ[1], center[2] - halfX[2] + halfZ[2], 0 });
    }

    /* Apply offset to all corners */
    for (i = 0; i < 4; i++) {
        vector_add(floorCorners[i], floorCorners[i], rotatedOffset);
    }

    /* Setup floor quad vertices */
    u32 floorColor = (0x30 << 24) | baseColor;

    vector_copy(floorQuad.point[0], floorCorners[1]);
    vector_copy(floorQuad.point[1], floorCorners[0]);
    vector_copy(floorQuad.point[2], floorCorners[2]);
    vector_copy(floorQuad.point[3], floorCorners[3]);

    floorQuad.point[0][3] = 1.0f;
    floorQuad.point[1][3] = 1.0f;
    floorQuad.point[2][3] = 1.0f;
    floorQuad.point[3][3] = 1.0f;

    floorQuad.rgba[0] = floorColor;
    floorQuad.rgba[1] = floorColor;
    floorQuad.rgba[2] = floorColor;
    floorQuad.rgba[3] = floorColor;

    floorQuad.uv[0] = (UV_t){ 0, 0 };
    floorQuad.uv[1] = (UV_t){ 0, 1 };
    floorQuad.uv[2] = (UV_t){ 1, 0 };
    floorQuad.uv[3] = (UV_t){ 1, 1 };

    gfxDrawQuad(floorQuad, NULL);
}

static void hill_drawShape(Moby* moby, Cuboid cube)
{
    circleMeFinal_StripMe(moby, cube);
}

void hill_postDraw(Moby* moby)
{
    hillPvar_t* pvars = (hillPvar_t*)moby->pVar;
    if (!pvars)
        return;

    if (vector_length(pvars->currentCuboid->matrix.v2) > 1.0001)
        pvars->isCircle = 1;

    hill_drawShape(moby, *pvars->currentCuboid);
}

void hill_update(Moby* moby)
{
    printf("\nhill_update: start");
    hillPvar_t* pvars = (hillPvar_t*)moby->pVar;
    if (!pvars)
        return;

    if (!pvars->currentCuboid) {
        pvars->currentCuboid = &rawr;
    }

    vector_copy(moby->position, pvars->currentCuboid->pos);

    printf("\ncuboid: %08x, pos: %d", pvars->currentCuboid, pvars->currentCuboid->pos[0]);

    gfxRegisterDrawFunction(&hill_postDraw, moby);

    // handle players
    hillPlayerUpdates(moby);

    // handle auto destruct
    // if (pvars->DestroyAtTime && gameGetTime() > pvars->DestroyAtTime) {
    //     scavHuntHBoltDestroy(moby);
    // }
}

void hill_setupMoby(void)
{
    Moby* moby = getHillMoby();
    if (moby == 0) {
        moby = mobySpawn(HILL_OCLASS, sizeof(hillPvar_t));
    }
    if (!moby) return;

    printf("\nmoby: %08x", moby);

    hillPvar_t* pvars = (hillPvar_t*)moby->pVar;
    memset(pvars, 0, sizeof(hillPvar_t));
    pvars->currentCuboid = &rawr;
    pvars->color = 0x00ffffff;

    moby->pUpdate = &hill_update;
    moby->modeBits = 0;
    moby->updateDist = -1;
    moby->drawn = 1;
    moby->opacity = 0;
    moby->drawDist = 0;
    vector_copy(moby->position, rawr.pos);

    soundPlayByOClass(1, 0, moby, MOBY_ID_OMNI_SHIELD);
    kothInfo.kothMoby = moby;
}

Moby* getHillMoby(void)
{
    Moby* moby = mobyListGetStart();
    Moby* mobyEnd = mobyListGetEnd();
    int i = 0;
    while (moby < mobyEnd) {
        if (moby->oClass == 0x3000) {
            return moby;
            break;
        }
        ++moby;
    }
    return 0;
}

static int clampIndex(int idx, int max)
{
    if (max <= 0)
        return 0;
    if (idx < 0)
        return 0;
    if (idx >= max)
        return max - 1;
    return idx;
}

void kothReset(void)
{
    memset(&kothInfo, 0, sizeof(kothInfo));
    spawned = 0;
    scrollQuad = 0;
    cachedSegments = -1;
    cachedIsCircle = -1;
    kothUpdateHillScale(kothConfig.hillScale);
}

void kothSetConfig(PatchGameConfig_t* config)
{
    int scoreIdx = config ? config->grKothScoreLimit : 0;
    int durationIdx = config ? config->grKothHillDuration : 0;
    int sizeIdx = config ? ((config->grSeed >> 28) & KOTH_HILL_SCALE_BITS) : 0;

    scoreIdx = clampIndex(scoreIdx, COUNT_OF(KOTH_SCORE_LIMIT_TABLE));
    durationIdx = clampIndex(durationIdx, COUNT_OF(KOTH_HILL_DURATION_TABLE));
    sizeIdx = clampIndex(sizeIdx, COUNT_OF(KOTH_HILL_SCALE_TABLE));

    kothConfig.scoreLimit = KOTH_SCORE_LIMIT_TABLE[scoreIdx];
    kothConfig.hillDurationMs = KOTH_HILL_DURATION_TABLE[durationIdx] * TIME_SECOND;
    kothConfig.hillScale = KOTH_HILL_SCALE_TABLE[sizeIdx];

    kothUpdateHillScale(kothConfig.hillScale);

    if (kothInfo.kothMoby && kothInfo.kothMoby->pVar) {
        hillPvar_t* pvars = (hillPvar_t*)kothInfo.kothMoby->pVar;
        pvars->currentCuboid = &rawr;
        vector_copy(kothInfo.kothMoby->position, rawr.pos);
    }
}

void kothTick(void)
{
    GameSettings* gs = gameGetSettings();
    GameData* gd = gameGetData();

    // only continue if enabled and in game
    if (!isInGame() || !gs || !gd) {
        return;
    }

    if (!kothInfo.kothMoby) {
        hill_setupMoby();
    }
}
