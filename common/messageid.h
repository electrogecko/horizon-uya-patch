
/***************************************************
 * FILENAME :		messageid.h
 * DESCRIPTION :
 * AUTHOR :			Daniel "Dnawrkshp" Gerendasy
 */

#ifndef _MESSAGEID_H_
#define _MESSAGEID_H_
#include "config.h"

/*
 * NAME :		CustomMessageId
 * DESCRIPTION :
 * 			Contains the different message ids.
 * NOTES :
 * AUTHOR :			Daniel "Dnawrkshp" Gerendasy
 */
enum CustomMessageId
{
    UNUSED = 0,

    /*
     * Sent to the client when the server initiates a data download.
     */
    CUSTOM_MSG_ID_SERVER_DOWNLOAD_DATA_REQUEST = 1,

    /*
     * Sent from the client to the server when the client receives a data request message.
     */
    CUSTOM_MSG_ID_CLIENT_DOWNLOAD_DATA_RESPONSE = 2,

    /*
     * Sent to the server when the client wants the map loader irx modules.
     */
    CUSTOM_MSG_ID_CLIENT_REQUEST_MAP_IRX_MODULES = 3,

    /*
     * Sent after the server has sent all the map loader irx modules.
     */
    CUSTOM_MSG_ID_SERVER_SENT_MAP_IRX_MODULES = 4,

    /*
     * Info on custom map.
     */
    CUSTOM_MSG_ID_SET_MAP_OVERRIDE = 5,

    /*
     * Sent in response to CUSTOM_MSG_ID_SET_MAP_OVERRIDE by the client.
     */
    CUSTOM_MSG_ID_SET_MAP_OVERRIDE_RESPONSE = 6,

    /*
     * Client requests server to sent current map override info.
     */
    CUSTOM_MSG_ID_REQUEST_MAP_OVERRIDE = 7,

    /*
     * Sent from the client to the server when the client has updated their patch config.
     */
    CUSTOM_MSG_ID_CLIENT_USER_CONFIG = 8,

    /*
     * Sent from the client to the server when the client has updated their patch game config.
     */
    CUSTOM_MSG_ID_CLIENT_USER_GAME_CONFIG = 9,

    /*
     * Sent from the server to the client when the host has changed and is propogating the patch game config.
     */
    CUSTOM_MSG_ID_SERVER_SET_GAME_CONFIG = 10,

    /*
     * Sent by the host when a game lobby has started.
     */
    CUSTOM_MSG_ID_GAME_LOBBY_STARTED = 11,

    /*
     * Sent by the host when a game lobby has ended.
     */
    CUSTOM_MSG_ID_GAME_LOBBY_ENDED = 12,

    /*
     * Sent from the client to the server when the client wants to redownload the patch.
     */
    CUSTOM_MSG_ID_CLIENT_REQUEST_PATCH = 13,

    /*
     * Sent from the client to the server with the client's machine id (MAC address).
     */
    CUSTOM_MSG_ID_CLIENT_SET_MACHINE_ID = 14,

    /*
     * Sent from a client to the host when they pick up the flag.
     */
    CUSTOM_MSG_ID_FLAG_REQUEST_PICKUP = 15,

    /*
     * Sent by the client to the server when the client has collected a horizon bolt.
     */
    CUSTOM_MSG_ID_CLIENT_PICKED_UP_HORIZON_BOLT = 16,

    /*
     * Sent by the client to the server when the client requests the current scavenger hunt settings.
     */
    CUSTOM_MSG_ID_CLIENT_REQUEST_SCAVENGER_HUNT_SETTINGS = 17,

    /*
     * Sent by the server to the client containing the current scavenger hunt settings.
     */
    CUSTOM_MSG_ID_SERVER_RESPONSE_SCAVENGER_HUNT_SETTINGS = 18,

    /*
     * Sent by the client to the server when the client requests MONTH and DAY (no year).
     */
    CUSTOM_MSG_ID_CLIENT_REQUEST_DATE_SETTINGS = 19,

    /*
     * Sent by the server to the client containing the current MONTH and DAY (no year).
     */
    CUSTOM_MSG_ID_CLIENT_RESPONSE_DATE_SETTINGS = 20,

    /*
     * Sent to the server when a player votes to end
     */
    CUSTOM_MSG_ID_PLAYER_VOTED_TO_END = 21,

    /*
     * sent to the client to update voes to end state
     */
    CUSTOM_MSG_ID_VOTE_TO_END_STATE_UPDATED = 22,

    /*
     * Sent to the client to invite bots
     */
    CUSTOM_MSG_ID_INVITE_BOT = 23,

    /*
     * Sent from the server to the host when the server wants the host to update all the teams
     */
    CUSTOM_MSG_ID_SERVER_REQUEST_TEAM_CHANGE = 24,

    /*
     * Sent to server for game details/state
     */
    CUSTOM_MSG_ID_CLIENT_SET_GAME_STATE = 25,

    /*
     * Temporary hot-join diagnostics. Sent to the lobby server, which logs it as an
     * unhandled custom message with the payload hex. Used because EE printf is not
     * visible in the current PCSX2 log configuration. Remove once IG join works.
     */
    CUSTOM_MSG_ID_HOTJOIN_DEBUG = 26,

    /*
     * Sent to server for game details/state
     */
    CUSTOM_MSG_PLAYER_SYNC_STATE_UPDATE = 27,
    /*
     * Sent every second to sync KOTH personal score.
     */
    CUSTOM_MSG_ID_KOTH_SCORE_UPDATE = 28,
    /*
     * Sent by host when the active KOTH hill changes to keep clients in sync.
     */
    CUSTOM_MSG_ID_KOTH_HILL_SYNC = 29,
    /*
     * Sent by the client to the server when the client wants a boot elf.
     */
    CUSTOM_MSG_ID_CLIENT_REQUEST_BOOT_ELF = 30,

    /*
     * Sent by the server to the client when the server has finished sending a boot elf.
     */
    CUSTOM_MSG_ID_SERVER_RESPONSE_BOOT_ELF = 31,

    /*
     * Start of custom message ids reserved for custom game modes.
     */
    /*
     * s208: a hot-joiner announces its chosen team to the host, so the host can honour it
     * at adopt time. A joiner-side write to gs->PlayerTeams does NOT propagate upward
     * (measured: host held 1 for 30 samples while the joiner read 0), and skin and spawn
     * base are both derived from the HOST's value, so the choice must reach the host.
     */
    /*
     * s208-E: the hot-join name sync. This used to be a bare `#define
     * CUSTOM_MSG_ID_HOTJOIN_NAME (32)` local to patch/ui.c, invisible from here -- and
     * CUSTOM_MSG_ID_HJ_TEAM_PREF was given the same 32. Both handlers install into
     * callbacks[32]; hjInstallNameHandler() runs LAST in main() and every frame, so the
     * name handler always won. Team-preference messages were dispatched into
     * hjOnRemoteName, which read them as HjNameMsg_t, saw name[0] == 0 and returned at
     * its `len <= 0` guard WITHOUT logging. The message left the joiner, the DME
     * relayed it to the host (server log: RT_MSG_CLIENT_APP_BROADCAST in,
     * RT_MSG_CLIENT_APP_SINGLE TargetOrSource:1 out), and it vanished on arrival.
     * Keep every id in this one enum so a collision is visible.
     */
    CUSTOM_MSG_ID_HOTJOIN_NAME = 32,

    CUSTOM_MSG_ID_HJ_TEAM_PREF = 33,

    CUSTOM_MSG_ID_GAME_MODE_START = 100,
};

typedef struct ServerDownloadDataRequest
{
    int Id;
    int TargetAddress;
    int TotalSize;
    int DataOffset;
    short Chunk;
    short DataSize;
    char Data[2048];
} ServerDownloadDataRequest_t;

typedef struct SetMapOverrideResponse {
  char MapFilename[64];
  int MapVersion;
} SetMapOverrideResponse_t;

typedef struct ClientDownloadDataResponse {
  int Id;
  int BytesReceived;
  int Stop;
} ClientDownloadDataResponse_t;

typedef struct ClientSetGameConfig
{
  PatchGameConfig_t GameConfig;
  CustomMapDef_t CustomMap;
} ClientSetGameConfig_t;

typedef struct ClientRequestPickUpFlag
{
    int GameTime;
    int PlayerId;
    u32 FlagUID;
} ClientRequestPickUpFlag_t;

typedef struct ScavengerHuntSettingsResponse
{
  int Enabled;
  float SpawnFactor;
} ScavengerHuntSettingsResponse_t;

typedef struct DateResponse {
  char Month;
  char Day;
  char Hour;
  char Minute;
  char Second;
} DateResponse_t;

typedef struct KothScoreUpdate {
  char PlayerIdx;
  short Score;
  char Padding;
} KothScoreUpdate_t;

typedef struct KothHillSync {
  char HillIdx;
  char Padding[3];
  int ElapsedMs; // how long current hill has been active on host
} KothHillSync_t;

typedef struct ClientRequestBootElf {
  int BootElfId;
} ClientRequestBootElf_t;

typedef struct ServerResponseBootElf {
  int BootElfId;
  u32 Address;
  u32 Size;
} ServerResponseBootElf_t;

typedef struct HjTeamPref {
  int ClientId;      // who this preference is for
  int Team;          // 0 = Blue, 1 = Red  (Auto never sends)
} HjTeamPref_t;

typedef struct ClientSetClientTypeRequest {
  int ClientType;
  u8 mac[6];
} ClientSetClientTypeRequest_t;

#endif // _MESSAGEID_H_
