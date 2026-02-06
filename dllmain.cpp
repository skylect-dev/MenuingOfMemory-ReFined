#define _CRT_SECURE_NO_WARNINGS
#include <Windows.h>
#include <Psapi.h>
#include <cstdint>
#include <cstring>
#include <vector>
#include <string>
#include <map>
#include <algorithm>

#pragma comment(lib, "user32.lib")
#pragma comment(lib, "psapi.lib")

// === Menuing of Memory (Re:Fined Module) ===
// Toggle modes via LT+RT+DPadUp/Down. Shows info popup like SCDHook.

// Base offsets (KH2FM)
static const uintptr_t kOffsets[] = {
    0x3B1B85, // Magic Cursor Reset
    0x3B1391, // Cursor Set Failsafe (always NOP)
    0x3B1192, // Item Cursor Reset
    0x3B1421  // Main Cursor Reset
};
// Cursor sync addresses (from known pointers)
#define ADDR_ComMenuSwitchState 0x7FF7689711F4
#define ADDR_CursorMain         0x7FF7689706BC
#define ADDR_CursorSecondary    0x7FF7689709BC
#define ADDR_SubMenuState       0x7FF766A1C4FC
static const uint8_t kLengths[] = {
    3, // Magic
    3, // Failsafe
    4, // Item
    3  // Main
};

enum PatchIndex {
    Magic = 0,
    Failsafe = 1,
    Item = 2,
    Main = 3
};

static bool kEnablePatch[4] = { false, true, false, false }; // default: only failsafe
static uint8_t kOrigBytes[4][4] = {};
static bool kOrigSaved = false;
// Mode: 0=Off, 1=Magic Only, 2=All
static int g_mode = 0;
static uint16_t g_prevInput = 0;
static char g_iniPath[MAX_PATH] = {};
static HMODULE g_moduleHandle = nullptr;

// INI helpers (forward decl)
static void BuildIniPath();
static void LoadIni();
static void SaveIni();
static uint32_t g_prevSwitchState = 0;
static uint32_t g_prevSubMenuState = 0;
static int g_forceResetFrames = 0;
static const int kForceResetFrameCount = 12; // about 200ms at 60fps

// Re:Fined exports
static HMODULE MAIN_HANDLE = nullptr;
static uint16_t* g_hardpadInput = nullptr;
static bool* g_isTitle = nullptr;

// Information popup (SCDHook style)
using openInformationWindow_t = void(*)(const char* message);
static openInformationWindow_t g_openInfo = nullptr;
static char g_infoBuffer[256] = {};

// --- Minimal signature scan (from SCDHook SigScan) ---
struct ModuleInfo
{
    const char* startAddr;
    const char* endAddr;
    ModuleInfo()
    {
        HMODULE hModule = GetModuleHandle(NULL);
        startAddr = reinterpret_cast<const char*>(hModule);
        MODULEINFO info = {};
        GetModuleInformation(GetCurrentProcess(), hModule, &info, sizeof(info));
        endAddr = startAddr + info.SizeOfImage;
    }
};
static const ModuleInfo moduleInfo;

template <typename T>
T SignatureScan(const char* pattern, const char* mask)
{
    size_t patLen = std::strlen(mask);
    for (const char* addr = moduleInfo.startAddr; addr < moduleInfo.endAddr - patLen; ++addr)
    {
        size_t i = 0;
        for (; i < patLen; ++i)
        {
            if (mask[i] != '?' && pattern[i] != addr[i]) break;
        }
        if (i == patLen) return reinterpret_cast<T>(const_cast<char*>(addr));
    }
    return nullptr;
}

// KHSCII encoding (minimal copy from SCDHook)
static std::vector<char> EncodeKHSCII(const std::string& Input)
{
    static const std::map<char, uint8_t> _specialDict = {
        { ' ', 0x01 }, { '\n', 0x02 }, { '!', 0x48 }, { '?', 0x49 }, { '%', 0x4A }, { '/', 0x4B },
        { '.', 0x4F }, { ',', 0x50 }, { ';', 0x51 }, { ':', 0x52 }, { '-', 0x54 }, { '~', 0x56 },
        { '\'', 0x57 }, { '(', 0x5A }, { ')', 0x5B }, { '[', 0x62 }, { ']', 0x63 }
    };

    std::vector<char> out;
    size_t i = 0;
    while (i < Input.size())
    {
        char c = Input[i];
        if (c >= 'a' && c <= 'z') { out.push_back(c + 0x39); i++; }
        else if (c >= 'A' && c <= 'Z') { out.push_back(c - 0x13); i++; }
        else if (c >= '0' && c <= '9') { out.push_back(c + 0x60); i++; }
        else {
            auto it = _specialDict.find(c);
            out.push_back(it != _specialDict.end() ? it->second : 0x01);
            i++;
        }
    }
    out.push_back(0x00);
    return out;
}

static void EnsureOrigSaved()
{
    if (kOrigSaved) return;
    const uintptr_t base = reinterpret_cast<uintptr_t>(GetModuleHandleW(nullptr));
    for (size_t i = 0; i < _countof(kOffsets); ++i) {
        std::memcpy(kOrigBytes[i], reinterpret_cast<void*>(base + kOffsets[i]), kLengths[i]);
    }
    kOrigSaved = true;
}

static void WriteNops(uintptr_t addr, uint8_t len)
{
    DWORD oldProtect = 0;
    if (!VirtualProtect(reinterpret_cast<LPVOID>(addr), len, PAGE_EXECUTE_READWRITE, &oldProtect))
        return;

    uint8_t nops[4] = { 0x90, 0x90, 0x90, 0x90 };
    std::memcpy(reinterpret_cast<void*>(addr), nops, len);

    DWORD tmp;
    VirtualProtect(reinterpret_cast<LPVOID>(addr), len, oldProtect, &tmp);
}

static void WriteOrig(uintptr_t addr, uint8_t len, const uint8_t* src)
{
    DWORD oldProtect = 0;
    if (!VirtualProtect(reinterpret_cast<LPVOID>(addr), len, PAGE_EXECUTE_READWRITE, &oldProtect))
        return;

    std::memcpy(reinterpret_cast<void*>(addr), src, len);

    DWORD tmp;
    VirtualProtect(reinterpret_cast<LPVOID>(addr), len, oldProtect, &tmp);
}

static void ApplyPatchState()
{
    const uintptr_t base = reinterpret_cast<uintptr_t>(GetModuleHandleW(nullptr));
    for (size_t i = 0; i < _countof(kOffsets); ++i)
    {
        if (i == Failsafe || kEnablePatch[i]) {
            WriteNops(base + kOffsets[i], kLengths[i]);
        } else {
            WriteOrig(base + kOffsets[i], kLengths[i], kOrigBytes[i]);
        }
    }
}

static void SyncCursors()
{
    uint32_t* pSwitch = (uint32_t*)ADDR_ComMenuSwitchState;
    uint32_t* pMain   = (uint32_t*)ADDR_CursorMain;
    uint32_t* pSec    = (uint32_t*)ADDR_CursorSecondary;
    uint32_t curSwitch = *pSwitch;

    if (g_prevSwitchState != curSwitch) {
        if (g_prevSwitchState == 0 && curSwitch == 6) {
            *pSec = *pMain;
        } else if (g_prevSwitchState == 6 && curSwitch == 0) {
            *pMain = *pSec;
        }
        g_prevSwitchState = curSwitch;
    }
}

static void SetMode(int mode)
{
    g_mode = mode;
    if (g_mode == 0) { // Off
        kEnablePatch[Magic] = false;
        kEnablePatch[Item] = false;
        kEnablePatch[Main] = false;
    } else if (g_mode == 1) { // Magic Only
        kEnablePatch[Magic] = true;
        kEnablePatch[Item] = false;
        kEnablePatch[Main] = false;
    } else { // All
        kEnablePatch[Magic] = true;
        kEnablePatch[Item] = true;
        kEnablePatch[Main] = true;
    }
    ApplyPatchState();
    SaveIni();
}

static void ShowModePopup()
{
    if (!g_openInfo) return;

    const char* modeText = (g_mode == 0) ? "OFF" : (g_mode == 1 ? "MAGIC ONLY" : "ALL");
    std::string msg = std::string("MoM: ") + modeText;
    auto encoded = EncodeKHSCII(msg);
    memset(g_infoBuffer, 0, sizeof(g_infoBuffer));
    memcpy(g_infoBuffer, encoded.data(), std::min<size_t>(encoded.size(), sizeof(g_infoBuffer) - 1));
    g_openInfo(g_infoBuffer);
}

static void BuildIniPath()
{
    if (g_iniPath[0] != 0) return;
    char pathA[MAX_PATH] = {};
    HMODULE mod = g_moduleHandle ? g_moduleHandle : GetModuleHandleA(nullptr);
    GetModuleFileNameA(mod, pathA, MAX_PATH);
    char* lastSlash = strrchr(pathA, '\\');
    if (lastSlash) *(lastSlash + 1) = 0;
    strcat_s(pathA, "MenuingOfMemory.ini");
    strcpy_s(g_iniPath, pathA);
}

static void LoadIni()
{
    BuildIniPath();
    FILE* f = nullptr;
    fopen_s(&f, g_iniPath, "r");
    if (!f) return;
    int mode = -1;
    fscanf_s(f, "Mode=%d", &mode);
    fclose(f);
    if (mode >= 0 && mode <= 2) {
        SetMode(mode);
    }
}

static void SaveIni()
{
    BuildIniPath();
    FILE* f = nullptr;
    fopen_s(&f, g_iniPath, "w");
    if (!f) return;
    fprintf(f, "Mode=%d\n", g_mode);
    fclose(f);
}

static void ResolveRefs()
{
    if (!MAIN_HANDLE) return;

    // HARDPAD input pointer
    g_hardpadInput = *(uint16_t**)GetProcAddress(MAIN_HANDLE, "?Input@HARDPAD@YS@@2PEAGEA");
    // Title flag
    g_isTitle = *(bool**)GetProcAddress(MAIN_HANDLE, "?IsTitle@TITLE@YS@@2PEA_NEA");

    // Information popup signature (same as SCDHook)
    if (!g_openInfo)
        g_openInfo = SignatureScan<openInformationWindow_t>(
            "\x40\x53\x48\x83\xEC\x20\x48\x8B\xD9\x48\x8B\x0D\x00\x00\x00\x00\xE8\x00\x00\x00\x00\x48\x8B\x0D\x00\x00\x00\x00\x48\x8B\xD3",
            "xxxxxxxxxxxx????x????xxx????xxx");
}

extern "C"
{
    __declspec(dllexport) void RF_ModuleInit(const wchar_t* mod_path)
    {
        wchar_t filepath[MAX_PATH];
        wcscpy(filepath, mod_path);
        wcscat(filepath, L"\\dll\\ReFined.KH2.dll");
        MAIN_HANDLE = LoadLibraryW(filepath);

        ResolveRefs();
        EnsureOrigSaved();
        LoadIni();
        if (g_mode < 0 || g_mode > 2) SetMode(0);
        g_prevSwitchState = *(uint32_t*)ADDR_ComMenuSwitchState;
        g_prevSubMenuState = *(uint32_t*)ADDR_SubMenuState;
    }

    __declspec(dllexport) void RF_ModuleExecute()
    {
        if (!g_hardpadInput) return;
        if (g_isTitle && *g_isTitle) return;

        uint16_t input = *g_hardpadInput;
        bool combo = (input & 0x0100) && (input & 0x0200); // L2 + R2
        bool up = (input & 0x0010) != 0;
        bool down = (input & 0x0040) != 0;

        if (combo) {
            bool prevCombo = (g_prevInput & 0x0100) && (g_prevInput & 0x0200);
            bool prevUp = (g_prevInput & 0x0010) != 0;
            bool prevDown = (g_prevInput & 0x0040) != 0;

            if (up && !prevUp) {
                SetMode((g_mode + 1) % 3);
                ShowModePopup();
            } else if (down && !prevDown) {
                SetMode((g_mode + 2) % 3);
                ShowModePopup();
            }
        }

        g_prevInput = input;

        // Cursor sync across main menu views
        SyncCursors();

        // Magic-only fix: reset CursorMain to 0 when submenu closes
        if (g_mode == 1) {
            uint32_t curSub = *(uint32_t*)ADDR_SubMenuState;
            if (g_prevSubMenuState != 0 && curSub == 0) {
                g_forceResetFrames = kForceResetFrameCount;
            }
            g_prevSubMenuState = curSub;
        }

        // Force write CursorMain for a few frames to override game writes
        if (g_forceResetFrames > 0) {
            volatile uint32_t* pMain = (uint32_t*)ADDR_CursorMain;
            *pMain = 0;
            --g_forceResetFrames;
        }
    }
}

BOOL APIENTRY DllMain(HMODULE hModule, DWORD reason, LPVOID)
{
    if (reason == DLL_PROCESS_ATTACH) {
        g_moduleHandle = hModule;
        EnsureOrigSaved();
    }
    return TRUE;
}
