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
(include-book "io")
(defttag :sidekick)
(set-state-ok t)

(define disassemble-to-string ((fn symbolp) state)
  (declare (ignorable fn))
  (b* ((- (er hard? 'disassemble-to-string "Raw Lisp definition not installed?"))
       ((mv err val state) (read-acl2-oracle state))
       ((when (or err
                  (not (stringp val))))
        (mv "" state)))
    (mv val state)))

; (depends-on "disassemble-raw.lsp")
(include-raw "disassemble-raw.lsp")

(define sk-get-disassembly ((name stringp) state)
  :returns (mv json-props state)
  :mode :program
  (b* (((mv errmsg objs state) (acl2::read-string name nil))
       ((when errmsg)
        (mv (sk-json-error "Error in disassemble: parsing failed: ~a: ~a~%" name errmsg)
            state))
       ((unless (and (equal (len objs) 1)
                     (symbolp (car objs))))
        (mv (sk-json-error "Error in disassemble: not a symbol: ~a~%" name)
            state))
       ((mv disassembly state) (disassemble-to-string (car objs) state)))
    (mv (bridge::json-encode (list (cons :error nil)
                                   (cons :val disassembly)))
        state)))

