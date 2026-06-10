@echo off
setlocal
title RMKCET Shine Rebuild
color 0B

echo.
echo  ============================================
echo   RMKCET Shine Rebuild
echo   Starting React + Hono stack...
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

echo  [INFO] Checking for existing processes on ports 5000 and 5001...
for %%P in (5000 5001) do (
    for /f "tokens=5" %%A in ('netstat -ano ^| findstr ":%%P" ^| findstr "LISTENING"') do (
        echo  [INFO] Killing process on port %%P with PID %%A
        taskkill /F /PID %%A >nul 2>&1
    )
)

echo.
echo  ============================================
echo   Starting services...
echo   Client : http://[::1]:5000
echo   Server : http://[::1]:5001
echo   Press Ctrl+C in this window to stop both.
echo  ============================================
echo.

timeout /t 3 /nobreak >nul
start "" http://[::1]:5000

echo  [SUCCESS] Shine Rebuild launch initiated in this window.
call npm.cmd run dev

echo.
echo  Shine Rebuild has stopped.
pause
