; VL 2014 -- VL Verilog Toolkit, 2014 Edition
; Copyright (C) 2008-2015 Centaur Technology
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

(in-package "VL2014")
(include-book "../../util/warnings")
(include-book "centaur/fty/basetypes" :dir :system)

(fty::defalist vl-usertypes
  :key-type stringp)

(defprod vl-parsestate
  :tag :vl-parsestate
  :layout :tree
  ((usertypes vl-usertypes-p
              "Fast alist binding names of declared types (forward typedefs
               and regular typedefs) to anything, which is occasionally
               needed to distinguish between expressions and data types.")

   (warnings vl-warninglist-p
             "Warnings created at parse time.")))

(local (xdoc::set-default-parents vl-parsestate))

(define vl-parsestate-free ((pstate vl-parsestate-p))
  :short "Free fast alists associated with a parse state."
  (b* (((vl-parsestate pstate) pstate))
    (fast-alist-free pstate.usertypes)))

(define vl-parsestate-restore ((pstate vl-parsestate-p))
  :short "Build a new parse-state whose alists are fast."
  :returns (new-pstate vl-parsestate-p)
  (b* (((vl-parsestate pstate) pstate))
    (change-vl-parsestate pstate
                          :usertypes (make-fast-alist pstate.usertypes))))

(define vl-parsestate-add-user-defined-type
  :short "Extend the parse state to record that there is a new user-defined type."
  ((name stringp)
   (pstate vl-parsestate-p))
  :returns (new-pstate vl-parsestate-p)
  (b* (((vl-parsestate pstate) pstate)
       (new-usertypes (hons-acons name t pstate.usertypes)))
    (change-vl-parsestate pstate
                          :usertypes new-usertypes)))

(define vl-parsestate-is-user-defined-type-p
  :short "Check whether some name is the name of a previously-defined, user-defined type."
  ((name   stringp)
   (pstate vl-parsestate-p))
  :returns (user-defined-type-p booleanp :rule-classes :type-prescription)
  (b* (((vl-parsestate pstate) pstate))
    (consp (hons-get name pstate.usertypes))))

(define vl-parsestate-add-warning
  :short "Extend the parse state with a new warning."
  ((warning vl-warning-p)
   (pstate  vl-parsestate-p))
  :returns (new-pstate vl-parsestate-p)
  (b* (((vl-parsestate pstate) pstate))
    (change-vl-parsestate pstate :warnings (cons warning pstate.warnings))))

(define vl-parsestate-set-warnings
  ((warnings vl-warninglist-p)
   (pstate   vl-parsestate-p))
  :returns (new-pstate vl-parsestate-p)
  (change-vl-parsestate pstate :warnings warnings))



