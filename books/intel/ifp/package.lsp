; Copyright (C) Intel Corporation
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

(in-package "ACL2")

(include-book "centaur/bitops/portcullis" :dir :system)
(include-book "centaur/fty/portcullis" :dir :system)

#!ACL2
(defconst *ifp-imports*
  '(src1 src2 src3 a b c d i j k x y z))


(defpkg "IFP"
  (append '(enable* disable* e/d* e/d**)
          *standard-acl2-imports*
          set::*sets-exports*
          std::*std-exports*
          *std-pkg-symbols*
          *bitops-exports*
          *ifp-imports*
          '(rational-exponent
            rational-significand
            rational-sign)
          '(fty::defbitstruct
             fty::defprod)))

#!IFP
(defconst *ifp-exports*
  '(patbind-fp-flags
    fp-flags->ie
    fp-flags->de
    fp-flags->ze
    fp-flags->oe
    fp-flags->ue
    fp-flags->pe
    fp-flags-p
    rounding-mode-p
    rc->rounding-mode
    rounding-mode->rc

    fp-size
    fp-size->explicit-jbit
    fp-size->exp-bias
    fp-size->exp-size
    fp-size->frac-size
    fp-size->emin
    fp-size->emax
    fp-size->width
    fp-size-width
    fp-size-fix
    fp-size-p
    size ;; for the default value of fp-size's :size argument
    *fp-size-bf16*
    *fp-size-hp*
    *fp-size-sp*
    *fp-size-dp*
    *fp-size-ep*

    make-fp-value
    fp-value
    fp-value-fix
    fp-type-p
    fp-value->type
    fp-value->exp
    fp-value->frac
    fp-value->sign
    fp-value->man
    fp-value->exp-bias
    fp-value-apply-daz
    fp-value-p
    fp-value-zero
    fp-value-inf
    fp-value-qnan
    fp-value-quiet
    fp-value-indef))
