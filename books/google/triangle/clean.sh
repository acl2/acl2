#!/usr/bin/env bash
# Copyright 2026 Google LLC
# Use of this source code is governed by a BSD-style license that can be
# found in the LICENSE file.

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "${SCRIPT_DIR}/../../.." && pwd)"

cd "${SCRIPT_DIR}"
"${REPO_ROOT}/books/build/clean.pl"
rm -f -- *~
