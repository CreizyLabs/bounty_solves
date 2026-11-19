@echo off
setlocal
echo ======================================================
echo    CreizyLabs Bounty Solves - Lean 4 Verification
echo ======================================================
echo.

cd /d "%~dp0"

echo [1/2] Fetching Mathlib build cache (if available)...
call lake exe cache get

echo.
echo [2/2] Building and verifying all 8 Lean 4 libraries...
call lake build
if errorlevel 1 (
    echo.
    echo Build / verification failed. Check the error log above.
    exit /b %errorlevel%
)

echo.
echo ======================================================
echo [SUCCESS] All 8 libraries compiled and verified cleanly!
echo ======================================================
