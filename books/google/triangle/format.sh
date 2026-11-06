#!/usr/bin/env bash
# Copyright 2026 Google LLC
# Use of this source code is governed by a BSD-style license that can be
# found in the LICENSE file.

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
TARGET_FILE="${SCRIPT_DIR}/triangle.lisp"

emacs -Q --batch "${TARGET_FILE}" \
  --eval '(setq make-backup-files nil)' \
  --eval '(lisp-mode)' \
  --eval '(setq indent-tabs-mode nil)' \
  --eval '(indent-region (point-min) (point-max) nil)' \
  --eval '(delete-trailing-whitespace)' \
  -f save-buffer

rm -f -- "${SCRIPT_DIR}"/*~
