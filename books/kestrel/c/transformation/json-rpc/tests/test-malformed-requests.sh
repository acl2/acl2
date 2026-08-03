#!/bin/bash

# Fire malformed (and one valid) JSON-RPC requests at a running
# struct-type-split server and check the returned JSON-RPC error codes.
#
# Copyright (C) 2026 Kestrel Institute
#
# License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
#
# Author: Grant Jurgensen (grant@kestrel.edu)

################################################################################

# Prerequisite: start the server first, from THIS tests/ directory, so that the
# file paths in the requests (input-files/, out/) resolve relative to it:
#
#   ../server.sh [PORT]
#
# Then, in another terminal:
#
#   ./test-malformed-requests.sh [PORT]      (PORT defaults to 7070)
#
# Each request is sent over its own TCP connection via bash's /dev/tcp (no nc
# dependency).  The server sends a single newline-terminated response line,
# which we read back and inspect.  Exits nonzero if any case fails.

set -u

HOST=127.0.0.1
PORT="${1:-7070}"
READ_TIMEOUT=3

pass=0
fail=0

# send REQUEST; print the single-line response (empty if none within timeout).
send() {
  local req="$1" resp=""
  exec 3<>"/dev/tcp/${HOST}/${PORT}" \
    || { echo "ERROR: cannot connect to ${HOST}:${PORT} (is the server running?)"; exit 2; }
  printf '%s\n' "$req" >&3
  IFS= read -r -t "${READ_TIMEOUT}" resp <&3 || true
  exec 3>&- 3<&-
  printf '%s' "$resp"
}

# check DESC EXPECTED REQUEST, where EXPECTED is an integer error code, "OK"
# (expect a result and no error), or "NONE" (expect no response at all).
check() {
  local desc="$1" expected="$2" req="$3"
  local resp got
  resp="$(send "$req")"
  case "$expected" in
    OK)
      if [[ -n "$resp" && "$resp" != *'"error"'* && "$resp" == *'"result"'* ]]; then
        got="OK"
      else
        got="not-OK"
      fi
      ;;
    NONE)
      if [[ -z "$resp" ]]; then got="NONE"; else got="got-response"; fi
      ;;
    *)
      got="$(printf '%s' "$resp" | grep -oE '"code":-?[0-9]+' | head -n1 | sed 's/"code"://')"
      [[ -z "$got" ]] && got="(none)"
      ;;
  esac
  if [[ "$got" == "$expected" ]]; then
    printf 'PASS  %-42s expected=%s\n' "$desc" "$expected"
    pass=$((pass + 1))
  else
    printf 'FAIL  %-42s expected=%s got=%s\n' "$desc" "$expected" "$got"
    printf '        response: %s\n' "${resp:-<none>}"
    fail=$((fail + 1))
  fi
}

# Parse-layer failures (envelope checked before the method runs):
check "invalid JSON (parse error)"       -32700 '{ this is not json'
check "top-level not object/array"       -32600 '42'
check "missing jsonrpc field"            -32600 '{"method":"struct-type-split","params":{},"id":1}'
check "params wrong JSON type"           -32600 '{"jsonrpc":"2.0","method":"struct-type-split","params":5,"id":1}'

# Dispatch-layer failure:
check "method not allowed"               -32601 '{"jsonrpc":"2.0","method":"frobnicate","params":{},"id":1}'

# Invalid params (produced by the method itself):
check "missing required param"           -32602 '{"jsonrpc":"2.0","method":"struct-type-split","params":{"old-dir":"input-files"},"id":1}'
check "param wrong type"                 -32602 '{"jsonrpc":"2.0","method":"struct-type-split","params":{"old-dir":"input-files","new-dir":"out","files":["test1.c"],"struct-tag":99,"right-members":["z"]},"id":1}'
check "unsafe wrong type"                -32602 '{"jsonrpc":"2.0","method":"struct-type-split","params":{"old-dir":"input-files","new-dir":"out","files":["test1.c"],"struct-tag":"point","right-members":["z"],"unsafe":"yes"},"id":1}'
check "params is array not object"       -32602 '{"jsonrpc":"2.0","method":"struct-type-split","params":[1,2],"id":1}'
check "duplicate parameter name"         -32602 '{"jsonrpc":"2.0","method":"struct-type-split","params":{"old-dir":"input-files","old-dir":"elsewhere","new-dir":"out","files":["test1.c"],"struct-tag":"point","right-members":["z"]},"id":1}'

# Internal errors (well-formed request, fails at transform/IO time):
check "struct tag not found"             -32603 '{"jsonrpc":"2.0","method":"struct-type-split","params":{"old-dir":"input-files","new-dir":"out","files":["test1.c"],"struct-tag":"nosuchtag","right-members":["z"],"preprocess":false},"id":1}'
check "input file not found"             -32603 '{"jsonrpc":"2.0","method":"struct-type-split","params":{"old-dir":"input-files","new-dir":"out","files":["nope.c"],"struct-tag":"point","right-members":["z"],"preprocess":false},"id":1}'

# Sanity checks of the non-error paths:
check "valid request (success)"          OK     '{"jsonrpc":"2.0","method":"struct-type-split","params":{"old-dir":"input-files","new-dir":"out","files":["test1.c"],"struct-tag":"point","right-members":["z"],"new-tag":"point_right","unsafe":true,"preprocess":false},"id":1}'
check "valid notification (no response)" NONE   '{"jsonrpc":"2.0","method":"struct-type-split","params":{"old-dir":"input-files","new-dir":"out","files":["test1.c"],"struct-tag":"point","right-members":["z"],"new-tag":"point_right","unsafe":true,"preprocess":false}}'

echo
echo "Passed: ${pass}  Failed: ${fail}"
[[ "${fail}" -eq 0 ]]
