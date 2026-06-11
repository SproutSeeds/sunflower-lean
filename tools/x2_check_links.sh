#!/bin/sh
# X2 link-integrity check (run AFTER R3/R4/A1/A2/A3 publish).
# Usage: tools/x2_check_links.sh <arxiv-abs-url> <zenodo-doi-url>
# Checks every public surface resolves (HTTP 200/30x). Exit 0 = all good.
set -e
ARXIV="${1:?usage: x2_check_links.sh <arxiv-abs-url> <zenodo-doi-url>}"
ZENODO="${2:?usage: x2_check_links.sh <arxiv-abs-url> <zenodo-doi-url>}"
REPO=https://github.com/SproutSeeds/sunflower-lean
FAIL=0
check() {
  code=$(curl -s -o /dev/null -w "%{http_code}" -L --max-time 30 "$1")
  case "$code" in
    2*|3*) echo "OK   $code  $1" ;;
    *)     echo "FAIL $code  $1"; FAIL=1 ;;
  esac
}
check "$REPO"
check "$REPO/releases/tag/paper-v1"
check "$REPO/blob/main/FORMAL_RESULTS_M3.md"
check "$REPO/blob/main/verify_m3.sh"
check "$REPO/blob/main/REPRODUCING.md"
check "$ARXIV"
check "$ZENODO"
check "https://www.erdosproblems.com/20"
check "https://www.erdosproblems.com/857"
[ "$FAIL" -eq 0 ] && echo "X2: ALL LINKS RESOLVE" || echo "X2: FAILURES ABOVE"
exit "$FAIL"
