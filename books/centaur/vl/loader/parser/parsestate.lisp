; VL Verilog Toolkit
; Copyright (C) 2008-2014 Centaur Technology
;
; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/
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
; Original author: Jared Davis <jared@centtech.com>

(in-package "VL")
(include-book "../../util/warnings")
(include-book "centaur/fty/basetypes" :dir :system)

(defprod vl-parsestate
  :tag :vl-parsestate
  :layout :tree
  ;; This used to additionally contain a fast-alist for user-defined types that
  ;; we had encountered.  That has since been removed, so now there's just a
  ;; warning list.  It's probably best to keep this in its parsestate wrapper,
  ;; in case we ever want to add any other fields here.
  ((warnings vl-warninglist-p
             "Warnings created at parse time.")))

(local (xdoc::set-default-parents vl-parsestate))

(define vl-parsestate-add-warning
  :short "Extend the parse state with a new warning."
  ((warning vl-warning-p)
   (pstate  vl-parsestate-p))
  :returns (new-pstate vl-parsestate-p)
  (b* (((vl-parsestate pstate) pstate))
    (change-vl-parsestate pstate :warnings (cons warning pstate.warnings))))

;; Turns out this was never used.
;;
;; (define vl-parsestate-set-warnings
;;   ((warnings vl-warninglist-p)
;;    (pstate   vl-parsestate-p))
;;   :returns (new-pstate vl-parsestate-p)
;;   (change-vl-parsestate pstate :warnings warnings))



