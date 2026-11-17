#!/usr/bin/env bash
# Copyright 2026 Google LLC
# Use of this source code is governed by a BSD-style license that can be
# found in the LICENSE file.

set -uo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "${SCRIPT_DIR}/../../.." && pwd)"
TARGET_FILE="${SCRIPT_DIR}/triangle.lisp"

LOG_FILE="$(mktemp)"
trap 'rm -f "${LOG_FILE}"' EXIT

cd "${SCRIPT_DIR}"

"${REPO_ROOT}/saved_acl2r" << 'EOF' 2>&1 | tee "${LOG_FILE}"
(mv-let (erp val state)
        (ld "triangle.lisp"
            :ld-pre-eval-print t
            :ld-error-action :return)
  (declare (ignore val))
  (if erp
      (prog2$ (cw "~%__ACL2_COMPILE_RESULT_FAILED__~%")
              (mv t nil state))
    (prog2$ (cw "~%__ACL2_COMPILE_RESULT_SUCCEEDED__~%")
            (mv nil :ok state))))
EOF
ACL2_EXIT=$?

HAS_SUCCESS_MARKER=0
if grep -q "__ACL2_COMPILE_RESULT_SUCCEEDED__" "${LOG_FILE}"; then
  HAS_SUCCESS_MARKER=1
fi

HAS_ERROR_TEXT=0
if grep -Eq '\*{8} FAILED \*{8}|^ACL2 Error|^HARD ACL2 ERROR|ABORTING from raw Lisp|^Error:|Test\? found a counterexample|Test\? failed|__ACL2_COMPILE_RESULT_FAILED__' "${LOG_FILE}"; then
  HAS_ERROR_TEXT=1
fi

echo ""
echo "========================================"
if [[ "${ACL2_EXIT}" -eq 0 && "${HAS_SUCCESS_MARKER}" -eq 1 && "${HAS_ERROR_TEXT}" -eq 0 ]]; then
  echo "RESULT: COMPILE SUCCEEDED"
  echo "========================================"
  exit 0
else
  echo "RESULT: COMPILE FAILED"
  echo "----------------------------------------"
  grep -En '\*{8} FAILED \*{8}|^ACL2 Error|^HARD ACL2 ERROR|ABORTING from raw Lisp|^Error:|Test\? found a counterexample|Test\? failed' "${LOG_FILE}" || true
  echo "========================================"
  exit 1
fi
