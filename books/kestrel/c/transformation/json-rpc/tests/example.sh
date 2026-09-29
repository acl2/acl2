#!/bin/bash

# Send example JSON-RPC requests to a running C transformation server, one at a
# time, waiting for the response to each request before sending the next.
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
#   ./example.sh [PORT]      (PORT defaults to 7070)
#
# The requests read input-files/test1.c into the code ensemble "orig", split a
# struct type of "orig" into the code ensemble "split", write "split" to out/,
# and list the code ensembles.
#
# Each request depends on the previous ones, so they are not sent as a JSON-RPC
# batch: the JSON-RPC specification does not say in which order the requests of
# a batch are processed, or whether they are processed concurrently.
#
# No JSON parsing is needed: the server answers each request (that is not a
# notification) with a single line, so we read one line after each request.
# All the requests go over one connection (via bash's /dev/tcp).

set -u

HOST=127.0.0.1
PORT="${1:-7070}"

exec 3<>"/dev/tcp/${HOST}/${PORT}" \
  || { echo "ERROR: cannot connect to ${HOST}:${PORT} (is the server running?)"; exit 2; }

# send REQUEST: send the request, print the response, and stop if it is an
# error.  A quote in the message of an error or warning is escaped, so the
# pattern below only matches the error member of an error response.
send() {
  local resp=""
  printf '%s\n' "$1" >&3
  IFS= read -r resp <&3
  printf '%s\n' "$resp"
  if [[ "$resp" == *'"error":'* ]]; then
    echo "The request failed; stopping."
    exit 1
  fi
}

# The environment persists across connections, so the requests that create a
# code ensemble set overwrite, so that this script can be run more than once.

send '{"jsonrpc": "2.0", "method": "input-files", "params": {"output-ensemble": "orig", "base-dir": "input-files", "files": ["test1.c"], "preprocess": false, "overwrite": true}, "id": 1}'

send '{"jsonrpc": "2.0", "method": "struct-type-split", "params": {"input-ensemble": "orig", "output-ensemble": "split", "struct-tag": "point", "right-members": ["z"], "new-tag": "point_right", "safety-checks": false, "overwrite": true}, "id": 2}'

send '{"jsonrpc": "2.0", "method": "output-files", "params": {"input-ensemble": "split", "base-dir": "out"}, "id": 3}'

send '{"jsonrpc": "2.0", "method": "list-ensembles", "id": 4}'
