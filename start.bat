@echo off
setlocal EnableDelayedExpansion
title RMKCET Shine Rebuild
color 0B

echo.
echo  ============================================
echo   RMKCET Shine Rebuild
echo   Windows Launcher
echo  ============================================
echo.

cd /d "%~dp0"

where node >nul 2>&1
if errorlevel 1 (
    echo  [ERROR] Node.js is not installed or not in PATH.
    echo  Please install Node.js 20+ and try again.
    pause
    exit /b 1
)

where npm.cmd >nul 2>&1
if errorlevel 1 (
    echo  [ERROR] npm.cmd is not available in PATH.
    pause
    exit /b 1
)

if not exist "node_modules" (
    echo  [INFO] Root dependencies not found. Installing...
    call npm.cmd install
    if errorlevel 1 (
        echo  [ERROR] Failed to install root dependencies.
        pause
        exit /b 1
    )
)

if not exist "client\node_modules" (
    echo  [INFO] Client dependencies not found. Installing...
    call npm.cmd install --prefix client
    if errorlevel 1 (
        echo  [ERROR] Failed to install client dependencies.
        pause
        exit /b 1
    )
)

if not exist "server\node_modules" (
    echo  [INFO] Server dependencies not found. Installing...
    call npm.cmd install --prefix server
    if errorlevel 1 (
        echo  [ERROR] Failed to install server dependencies.
        pause
        exit /b 1
    )
)

if not exist "desktop\node_modules" (
    echo  [INFO] Desktop dependencies not found. Installing...
    call npm.cmd install --prefix desktop
    if errorlevel 1 (
        echo  [ERROR] Failed to install desktop dependencies.
        pause
        exit /b 1
    )
)

echo.
echo  Choose launch mode:
echo    [1] Web app only
echo    [2] Desktop dev-shell
echo    [3] Desktop app mode (desktop only)
echo    [4] Server only
echo    [5] Build/publish desktop update package
echo    [6] Production web + desktop app
echo.
choice /c 123456 /n /m "Enter your choice: "
set "LAUNCH_MODE=%errorlevel%"

set "PORTS_TO_KILL=5001"
set "NPM_SCRIPT=dev:server"
set "OPEN_BROWSER=0"
set "MODE_LABEL=Server only"
set "PACKAGE_BUILD=0"

if "%LAUNCH_MODE%"=="1" (
    set "PORTS_TO_KILL=5000 5001"
    set "NPM_SCRIPT=dev:web"
    set "OPEN_BROWSER=1"
    set "MODE_LABEL=Web app"
)

if "%LAUNCH_MODE%"=="2" (
    set "PORTS_TO_KILL=5000 5001"
    set "NPM_SCRIPT=dev:desktop"
    set "MODE_LABEL=Desktop dev-shell"
)

if "%LAUNCH_MODE%"=="3" (
    set "PORTS_TO_KILL=5001 5123"
    set "NPM_SCRIPT=desktop:app"
    set "MODE_LABEL=Desktop app mode (desktop only)"
)

if "%LAUNCH_MODE%"=="6" (
    set "PORTS_TO_KILL=5000 5001 5123"
    set "NPM_SCRIPT=prod:desktop-web:release-exe"
    set "OPEN_BROWSER=2"
    set "MODE_LABEL=Production web + desktop app + EXE release"
    set "PACKAGE_DEFAULT_ORIGIN=!SHINE_DESKTOP_RELEASE_API_ORIGIN!"
    if not defined PACKAGE_DEFAULT_ORIGIN set "PACKAGE_DEFAULT_ORIGIN=https://shine.athergrid.dev"
    set /p "PACKAGE_API_ORIGIN=Enter hosted Shine server domain [!PACKAGE_DEFAULT_ORIGIN!]: "
    if errorlevel 1 set "PACKAGE_API_ORIGIN=!PACKAGE_DEFAULT_ORIGIN!"
    if "!PACKAGE_API_ORIGIN!"=="" set "PACKAGE_API_ORIGIN=!PACKAGE_DEFAULT_ORIGIN!"
    set "SHINE_DESKTOP_RELEASE_API_ORIGIN=!PACKAGE_API_ORIGIN!"
    set "SHINE_DESKTOP_PUBLIC_BASE_URL=!PACKAGE_API_ORIGIN!"
    set "SHINE_DESKTOP_RELEASE_CHANNEL_URL=!PACKAGE_API_ORIGIN!/api/desktop/installer"
    set /p "PACKAGE_LOCATOR_CSV=Enter public Google Sheet locator CSV URL (optional) [!SHINE_DESKTOP_LOCATOR_CSV_URL!]: "
    if not "!PACKAGE_LOCATOR_CSV!"=="" set "SHINE_DESKTOP_LOCATOR_CSV_URL=!PACKAGE_LOCATOR_CSV!"
    set "SHINE_DESKTOP_SKIP_UNCHANGED=1"
)

if "%LAUNCH_MODE%"=="5" (
    set "MODE_LABEL=Desktop install package"
    set "PACKAGE_BUILD=1"
)

if "%PACKAGE_BUILD%"=="1" (
    echo.
    echo  Choose package type:
    echo    [1] Local MSIX test build
    echo    [2] Hosted MSIX release package
    echo    [3] Local EXE installer build
    echo    [4] Hosted EXE website package
    echo.
    choice /c 1234 /n /m "Enter your choice: "
    set "PACKAGE_MODE=!errorlevel!"

    if "!PACKAGE_MODE!"=="1" (
        set "PACKAGE_DEFAULT_ORIGIN=!SHINE_DESKTOP_RELEASE_API_ORIGIN!"
        if not defined PACKAGE_DEFAULT_ORIGIN set "PACKAGE_DEFAULT_ORIGIN=http://localhost:5001"
        set /p "PACKAGE_API_ORIGIN=Enter local Shine server URL for the packaged app [!PACKAGE_DEFAULT_ORIGIN!]: "
        if errorlevel 1 set "PACKAGE_API_ORIGIN=!PACKAGE_DEFAULT_ORIGIN!"
        if "!PACKAGE_API_ORIGIN!"=="" set "PACKAGE_API_ORIGIN=!PACKAGE_DEFAULT_ORIGIN!"
        set "SHINE_DESKTOP_RELEASE_API_ORIGIN=!PACKAGE_API_ORIGIN!"
        echo.
        echo  ============================================
        echo   Packaging Local Desktop MSIX Test Build...
        echo   Local API URL  : !SHINE_DESKTOP_RELEASE_API_ORIGIN!
        echo   Output MSIX    : desktop\out\msix
        echo   Note           : Keep option [4] Server only running when testing the packaged app.
        echo  ============================================
        echo.
        call npm.cmd run desktop:msix
        if errorlevel 1 (
            echo.
            echo  [ERROR] Desktop local MSIX packaging failed.
            pause
            exit /b 1
        )
        echo.
        echo  [SUCCESS] Local desktop MSIX test artifacts are ready.
        echo  Install from: desktop\out\msix\
        pause
        exit /b 0
    )

    if "!PACKAGE_MODE!"=="3" (
        set "PACKAGE_DEFAULT_ORIGIN=!SHINE_DESKTOP_RELEASE_API_ORIGIN!"
        if not defined PACKAGE_DEFAULT_ORIGIN set "PACKAGE_DEFAULT_ORIGIN=http://localhost:5001"
        set /p "PACKAGE_API_ORIGIN=Enter local Shine server URL for the packaged app [!PACKAGE_DEFAULT_ORIGIN!]: "
        if errorlevel 1 set "PACKAGE_API_ORIGIN=!PACKAGE_DEFAULT_ORIGIN!"
        if "!PACKAGE_API_ORIGIN!"=="" set "PACKAGE_API_ORIGIN=!PACKAGE_DEFAULT_ORIGIN!"
        set "SHINE_DESKTOP_RELEASE_API_ORIGIN=!PACKAGE_API_ORIGIN!"
        echo.
        echo  ============================================
        echo   Packaging Local Desktop EXE Build...
        echo   Local API URL  : !SHINE_DESKTOP_RELEASE_API_ORIGIN!
        echo   Output EXE     : desktop\out\exe
        echo   Note           : Keep option [4] Server only running when testing the installed app.
        echo  ============================================
        echo.
        call npm.cmd run desktop:exe
        if errorlevel 1 (
            echo.
            echo  [ERROR] Desktop local EXE packaging failed.
            pause
            exit /b 1
        )
        echo.
        echo  [SUCCESS] Local desktop EXE artifacts are ready.
        echo  Install from: desktop\out\exe\
        pause
        exit /b 0
    )

    set "PACKAGE_DEFAULT_ORIGIN=!SHINE_DESKTOP_RELEASE_API_ORIGIN!"
    if not defined PACKAGE_DEFAULT_ORIGIN set "PACKAGE_DEFAULT_ORIGIN=https://shine.athergrid.dev"
    set /p "PACKAGE_API_ORIGIN=Enter hosted Shine URL for the packaged app [!PACKAGE_DEFAULT_ORIGIN!]: "
    if errorlevel 1 set "PACKAGE_API_ORIGIN=!PACKAGE_DEFAULT_ORIGIN!"
    if "!PACKAGE_API_ORIGIN!"=="" set "PACKAGE_API_ORIGIN=!PACKAGE_DEFAULT_ORIGIN!"
    set "SHINE_DESKTOP_RELEASE_API_ORIGIN=!PACKAGE_API_ORIGIN!"
    set "SHINE_DESKTOP_PUBLIC_BASE_URL=!PACKAGE_API_ORIGIN!"
    set /p "PACKAGE_LOCATOR_CSV=Enter public locator CSV URL (optional) [!SHINE_DESKTOP_LOCATOR_CSV_URL!]: "
    if not "!PACKAGE_LOCATOR_CSV!"=="" set "SHINE_DESKTOP_LOCATOR_CSV_URL=!PACKAGE_LOCATOR_CSV!"
    set /p "PACKAGE_RELEASE_CHANNEL=Enter release channel URL (optional) [!SHINE_DESKTOP_RELEASE_CHANNEL_URL!]: "
    if not "!PACKAGE_RELEASE_CHANNEL!"=="" set "SHINE_DESKTOP_RELEASE_CHANNEL_URL=!PACKAGE_RELEASE_CHANNEL!"

    if "!PACKAGE_MODE!"=="2" (
        echo.
        echo  ============================================
        echo   Packaging Hosted Desktop Install Build...
        echo   Hosted API/App URL : !SHINE_DESKTOP_RELEASE_API_ORIGIN!
        echo   Output MSIX        : desktop\out\msix
        echo   Published Channel  : data\desktop-installer
        echo  ============================================
        echo.
        call npm.cmd run desktop:release
        if errorlevel 1 (
            echo.
            echo  [ERROR] Desktop packaging failed.
            pause
            exit /b 1
        )
        echo.
        echo  [SUCCESS] Desktop installer artifacts are ready.
        echo  Open: data\desktop-installer\latest\RMKCET-Shine.appinstaller
        echo  MSIX : desktop\out\msix\
        pause
        exit /b 0
    )

    echo.
    echo  ============================================
    echo   Packaging Hosted Desktop EXE Release...
    echo   Hosted API/App URL : !SHINE_DESKTOP_RELEASE_API_ORIGIN!
    echo   Output EXE         : desktop\out\exe
    echo   Published Channel  : data\desktop-installer
    echo  ============================================
    echo.
    call npm.cmd run desktop:release:exe
    if errorlevel 1 (
        echo.
        echo  [ERROR] Desktop EXE packaging failed.
        pause
        exit /b 1
    )
    echo.
    echo  [SUCCESS] Desktop EXE installer artifacts are ready.
    echo  Open: data\desktop-installer\latest\release.json
    echo  EXE  : desktop\out\exe\
    pause
    exit /b 0
)

if "%LAUNCH_MODE%"=="2" (
    echo  [INFO] Closing existing Shine desktop processes...
    powershell -NoProfile -ExecutionPolicy Bypass -Command "Get-Process | Where-Object { $_.Path -eq 'D:\RMKCET\rmkcet-shine\desktop\node_modules\electron\dist\electron.exe' } | Stop-Process -Force" >nul 2>&1
)

if "%LAUNCH_MODE%"=="3" (
    echo  [INFO] Closing existing Shine desktop processes...
    powershell -NoProfile -ExecutionPolicy Bypass -Command "Get-Process | Where-Object { $_.Path -eq 'D:\RMKCET\rmkcet-shine\desktop\node_modules\electron\dist\electron.exe' } | Stop-Process -Force" >nul 2>&1
)

if "%LAUNCH_MODE%"=="6" (
    echo  [INFO] Closing existing Shine desktop processes...
    powershell -NoProfile -ExecutionPolicy Bypass -Command "Get-Process | Where-Object { $_.Path -eq 'D:\RMKCET\rmkcet-shine\desktop\node_modules\electron\dist\electron.exe' } | Stop-Process -Force" >nul 2>&1
)

echo  [INFO] Checking for existing processes on required ports...
for %%P in (%PORTS_TO_KILL%) do (
    for /f "tokens=5" %%A in ('netstat -ano ^| findstr ":%%P" ^| findstr "LISTENING"') do (
        echo  [INFO] Killing process on port %%P with PID %%A
        taskkill /F /PID %%A >nul 2>&1
    )
)

echo.
echo  ============================================
echo   Starting %MODE_LABEL%...
echo   Server : http://[::1]:5001
if "%LAUNCH_MODE%"=="1" echo   Client : http://[::1]:5000
if "%LAUNCH_MODE%"=="2" echo   Client : http://[::1]:5000
if "%LAUNCH_MODE%"=="3" echo   Desktop shell : http://[::1]:5123
if "%LAUNCH_MODE%"=="6" echo   Web app : http://[::1]:5000
if "%LAUNCH_MODE%"=="6" echo   Desktop shell : http://[::1]:5123
if "%LAUNCH_MODE%"=="6" echo   Hosted URL : !SHINE_DESKTOP_RELEASE_API_ORIGIN!
if "%LAUNCH_MODE%"=="6" echo   Installer : !SHINE_DESKTOP_RELEASE_API_ORIGIN!/api/desktop/installer
if "%LAUNCH_MODE%"=="6" echo   EXE build : data\desktop-installer\latest
echo   Press Ctrl+C in this window to stop the running services.
echo  ============================================
echo.

timeout /t 3 /nobreak >nul
if "%OPEN_BROWSER%"=="1" start "" http://[::1]:5000
if "%OPEN_BROWSER%"=="2" start "" http://[::1]:5000

echo  [SUCCESS] %MODE_LABEL% launch initiated in this window.
call npm.cmd run %NPM_SCRIPT%

echo.
echo  Shine Rebuild has stopped.
pause
