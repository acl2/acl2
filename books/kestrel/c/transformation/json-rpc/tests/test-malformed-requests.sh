#!/bin/bash

# Fire malformed (and one valid) JSON-RPC requests at a running
# C transformation server and check the returned JSON-RPC error codes.
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

# Setup: read the input file into the environment.  The environment persists
# across connections, so this sets overwrite to make reruns succeed.
check "read input file"                  OK     '{"jsonrpc":"2.0","method":"input-files","params":{"target":"orig","base-dir":"input-files","files":["test1.c"],"preprocess":false,"overwrite":true},"id":1}'

# Parse-layer failures (envelope checked before the method runs):
check "invalid JSON (parse error)"       -32700 '{ this is not json'
check "top-level not object/array"       -32600 '42'
check "missing jsonrpc field"            -32600 '{"method":"struct-type-split","params":{},"id":1}'
check "params wrong JSON type"           -32600 '{"jsonrpc":"2.0","method":"struct-type-split","params":5,"id":1}'

# Dispatch-layer failures:
check "method not allowed"               -32601 '{"jsonrpc":"2.0","method":"frobnicate","params":{},"id":1}'
check "params to no-params method"       -32602 '{"jsonrpc":"2.0","method":"list-ensembles","params":{},"id":1}'
check "no params to params method"       -32602 '{"jsonrpc":"2.0","method":"drop-ensemble","id":1}'

# Invalid params (produced by the method itself):
check "missing required param"           -32602 '{"jsonrpc":"2.0","method":"struct-type-split","params":{"source":"orig"},"id":1}'
check "param wrong type"                 -32602 '{"jsonrpc":"2.0","method":"struct-type-split","params":{"source":"orig","target":"split","struct-tag":99,"right-members":["z"],"overwrite":true},"id":1}'
check "safety-checks wrong type"         -32602 '{"jsonrpc":"2.0","method":"struct-type-split","params":{"source":"orig","target":"split","struct-tag":"point","right-members":["z"],"safety-checks":"yes","overwrite":true},"id":1}'
check "params is array not object"       -32602 '{"jsonrpc":"2.0","method":"struct-type-split","params":[1,2],"id":1}'
check "duplicate parameter name"         -32602 '{"jsonrpc":"2.0","method":"struct-type-split","params":{"source":"orig","source":"other","target":"split","struct-tag":"point","right-members":["z"],"overwrite":true},"id":1}'
check "unknown parameter name"           -32602 '{"jsonrpc":"2.0","method":"struct-type-split","params":{"source":"orig","target":"split","struct-tag":"point","right-members":["z"],"unsafe":true},"id":1}'
check "unbound source name"              -32602 '{"jsonrpc":"2.0","method":"struct-type-split","params":{"source":"nosuchname","target":"split","struct-tag":"point","right-members":["z"],"overwrite":true},"id":1}'
check "bound target without overwrite"   -32602 '{"jsonrpc":"2.0","method":"struct-type-split","params":{"source":"orig","target":"orig","struct-tag":"point","right-members":["z"]},"id":1}'
check "non-string array element"         -32602 '{"jsonrpc":"2.0","method":"input-files","params":{"target":"other","base-dir":"input-files","files":["test1.c",7],"overwrite":true},"id":1}'
check "bad preprocess-args entry"        -32602 '{"jsonrpc":"2.0","method":"input-files","params":{"target":"other","base-dir":"input-files","files":["test1.c"],"preprocess-args":{"test1.c":["-DDEBUG",7]},"overwrite":true},"id":1}'
check "drop unbound name"                -32602 '{"jsonrpc":"2.0","method":"drop-ensemble","params":{"name":"nosuchname"},"id":1}'

# Internal errors (well-formed request, fails at transform/IO time):
check "struct tag not found"             -32603 '{"jsonrpc":"2.0","method":"struct-type-split","params":{"source":"orig","target":"split","struct-tag":"nosuchtag","right-members":["z"],"overwrite":true},"id":1}'
check "input file not found"             -32603 '{"jsonrpc":"2.0","method":"input-files","params":{"target":"other","base-dir":"input-files","files":["nope.c"],"preprocess":false,"overwrite":true},"id":1}'

# Sanity checks of the non-error paths:
check "valid transformation (success)"   OK     '{"jsonrpc":"2.0","method":"struct-type-split","params":{"source":"orig","target":"split","struct-tag":"point","right-members":["z"],"new-tag":"point_right","safety-checks":false,"overwrite":true},"id":1}'
check "valid output (success)"           OK     '{"jsonrpc":"2.0","method":"output-files","params":{"source":"split","base-dir":"out"},"id":1}'
check "list ensembles (success)"         OK     '{"jsonrpc":"2.0","method":"list-ensembles","id":1}'
check "valid notification (no response)" NONE   '{"jsonrpc":"2.0","method":"struct-type-split","params":{"source":"orig","target":"split","struct-tag":"point","right-members":["z"],"new-tag":"point_right","safety-checks":false,"overwrite":true}}'

echo
echo "Passed: ${pass}  Failed: ${fail}"
[[ "${fail}" -eq 0 ]]
