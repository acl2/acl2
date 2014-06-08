; ACL2 Sidekick
; Copyright (C) 2014 Kookamara LLC
;
; Contact:
;   Kookamara LLC
;   11410 Windermere Meadows, Austin TX, 78759, USA.
;   http://www.kookamara.com/
;
; This program is free software; you can redistribute it and/or modify it under
; the terms of the GNU General Public License as published by the Free Software
; Foundation; either version 2 of the License, or (at your option) any later
; version.  This program is distributed in the hope that it will be useful but
; WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
; FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
; more details.  You should have received a copy of the GNU General Public
; License along with this program; if not, write to the Free Software
; Foundation, Inc., 51 Franklin Street, Suite 500, Boston, MA 02110-1335, USA.
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

