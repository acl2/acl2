#!/usr/bin/env bash
# Copyright 2026 Google LLC
# Use of this source code is governed by a BSD-style license that can be
# found in the LICENSE file.

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "${SCRIPT_DIR}/../../.." && pwd)"

export LISP="${LISP:-sbcl}"
export ACL2="${REPO_ROOT}/saved_acl2r"

if [[ ! -x "${ACL2}" ]]; then
  make -C "${REPO_ROOT}" LISP="${LISP}" ACL2_REAL=r
fi

"${REPO_ROOT}/books/build/cert.pl" --clean-certs -j "$(nproc)" \
  "${REPO_ROOT}/books/arithmetic-5/top.lisp"
