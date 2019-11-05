; SVL - Listener-based Hierachical Symbolic Vector Hardware Analysis Framework
; Copyright (C) 2019 Centaur Technology
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
; Original author: Mertcan Temel <mert@utexas.edu>


;; List of lemmas that are expected to be used by svex-simplify during svl
;; creation.


(in-package "SVL")

(defconst *svl-flatten-simplify-lemmas*
  '(;;4vec-rsh-of-4vec-concat
    ;;4vec-rsh-of-4vec-concat-2
    ;;4vec-rsh-of-4vec-rsh
    4vec-?*-of-4vec-symwildeq-1
    natp-4vec-?*
    ;;4vec-bitnot-of-4vec-rsh
    ;;4vec-bitand-of-4vec-rsh
    ;;4vec-bitor-of-4vec-rsh
    integerp-4vec-plus
    integerp-4vec-rsh
    
    ;;bits-sbits.lisp
    4vec-bitnot$-of-bits-of-same-size
    4vec-bitand$-of-bits-of-same-size
    4vec-bitand$-of-bits-of-same-size
    4vec-bitxor$-of-bits-of-same-size
    bits-of-4vec-bitnot
    bits-of-4vec-bitand
    bits-of-4vec-bitor
    bits-of-4vec-bitxor
    bits-of-4vec-bitnot$
    bits-of-4vec-bitand$
    bits-of-4vec-bitor$
    bits-of-4vec-bitxor$
    ;;4vec-bitnot-of-4vec-concat$
    bits-of-lsh-1 ;; can be in the meta function...
    bits-of-lsh-2
    bits-of-lsh-3
    ;;bits-of-rsh
    ;;4vec-rsh-of-4vec-concat$-2
    ;;4vec-rsh-of-4vec-concat$-1
    ;;4vec-concat$-of-4vec-fix
    convert-4vec-concat-to-4vec-concat$
    ;;4vec-concat-of-4vec-concat$-case-2
    ;;4vec-concat$-of-4vec-concat$-case-2
    ;;4vec-concat$-of-4vec-concat$-case-1
    ;;4vec-concat-of-4vec-concat$-case-1
    ;;bits-of-concat-1
    ;;bits-of-concat-3
    ;;bits-of-concat-2
    sbits-of-concat
    concat-of-size=0
    4vec-concat$-of-size=1-term2=0
    sbits-size=0
    sbits-of-bits
    4vec-part-install-is-sbits
    ;;bits-of-4vec-plus-is-4vec-plus
    ;;bits-of-4vec-plus-is-4vec-plus-start=0
    bits-of-4vec-?*
    bits-of-4vec-?
    bits-of-4vec-fix
    ;;bits-of-bits-2
    ;;bits-of-bits-1
    ;;bits-of-sbits-1
    ;;bits-of-sbits-2
    ;;bits-of-sbits-3
    ;;bits-of-sbits-4
    ;;bits-of-sbits-5
    bits-of-0
    bitp-implies-natp
    natp-implies-integerp
    integerp-implies-4vecp
    4vec-p-4vec-bitand$
    4vec-p-4vec-bitxor$
    4vec-p-4vec-bitor$
    4vec-p-4vec-concat$
    integerp-4vec-concat$
    natp-4vec-concat$
    bitp-4vec-concat$
    4vec-p-bits
    integerp-4vec-part-select
    integerp-bits
    natp-4vec-part-select-better
    natp-bits
    bitp-bits-size=1
    bit$-of-negated-bit
    4vec-p-4vec-bitnot
    integerp-4vec-bitnot
    integerp-4vec-bitnot$
    natp-4vec-bitnot$
    bitp-of-4vec-bitnot
    bitp-of-4vec-bitnot$
    4vec-fix-of-functions
    4vec-fix2-of-functions
    4vec-part-select-is-bits
    natp-4vec-rsh
    4vec-rsh-of-width=0

    (:executable-counterpart sv::svex-p)
    (:executable-counterpart sv::svar-p)
    (:executable-counterpart natp)
    (:executable-counterpart integerp)
    (:executable-counterpart bitp)
    (:executable-counterpart <)
    (:executable-counterpart not)
    (:executable-counterpart unary--)
    (:executable-counterpart min)
    (:executable-counterpart binary-+)
    (:executable-counterpart binary--)
    (:executable-counterpart svex-eval-wog)
    (:executable-counterpart sv::svex-env-p)
    (:executable-counterpart bits)
    (:executable-counterpart rp::rp)
    (:executable-counterpart 4vec-concat$)
    (:executable-counterpart 4vec-bitnot$)
    
    SVEX-EVAL-IS-SVEX-EVAL-WOG
    4VEC-FIX2-IS-4VEC-FIX
    bits-0-1-of-4vec-reduction-and-when-amount=1
    bits-0-1-of-4vec-reduction-and
    4vec-bitand-of-3vec-fix
    4vec-zero-ext-is-bits


    )) 
