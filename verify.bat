@echo off
setlocal
echo ======================================================
echo    Bounty Solves - Lean 4 Lake Verification
echo ======================================================
echo.

cd /d "%~dp0"

echo [1/3] Updating dependencies via lake...
call lake update
if errorlevel 1 (
    echo Error during lake update.
    pause
    exit /b %errorlevel%
)

echo.
echo [2/3] Fetching Mathlib build cache (if available)...
call lake exe cache get

echo.
echo [3/3] Building and verifying libraries...
call lake build
if errorlevel 1 (
    echo.
    echo Build / verification failed. Check the error log above.
    pause
    exit /b %errorlevel%
)

echo.
echo ======================================================
echo [SUCCESS] All libraries compiled and verified cleanly!
echo ======================================================
pause
