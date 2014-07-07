; ACL2 Sidekick
; Copyright (C) 2014 Kookamara LLC
;
; Contact:
;
;   Kookamara LLC
;   11410 Windermere Meadows
;   Austin, TX 78759, USA
;   http://www.kookamara.com/
;
; License: (An MIT/X11-style license)
;
;   Permission is hereby granted, free of charge, to any person obtaining a
;   copy of this software and associated documentation files (the "Software"),
;   to deal in the Software without restriction, including without limitation
;   the rights to use, copy, modify, merge, publish, distribute, sublicense,
;   and/or sell copies of the Software, and to permit persons to whom the
;   Software is furnished to do so, subject to the following conditions:
;
;   The above copyright notice and this permission notice shall be included in
;   all copies or substantial portions of the Software.
;
;   THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
;   IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
;   FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
;   AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
;   LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
;   FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
;   DEALINGS IN THE SOFTWARE.
;
; Original author: Jared Davis <jared@kookamara.com>

(in-package "SIDEKICK")

; This is similar in spirit to misc/disassemble.lisp but doesn't have as many
; features.  It might be that some of these features are important for Lisps
; other than CCL.

; Why not use misc/disassemble?  It prints output to some temp-disassemble.lsp
; file, which is fundamentally not thread-safe.

(defun disassemble-to-string (fn state)
  (unless (acl2::live-state-p state)
    (error "disassemble-to-string requires a live state."))
  (let* ((world  (w state))
         (fn     (acl2::deref-macro-name fn (macro-aliases world)))
         (stream (make-string-output-stream))
         (common-lisp::*standard-output* stream))
    (handler-case
     (disassemble fn)
     (error (condition)
            (format t "Error disassembling ~A.~%~A~%" fn condition)))
    (mv (get-output-stream-string stream) state)))

