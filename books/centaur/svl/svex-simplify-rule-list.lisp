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

(in-package "SVL")

(include-book "meta/top")


(defconst *svex-simplify-meta-rules*
  '((:META SVL::4VEC-RSH-OF-META . SV::4VEC-RSH)
    (:META SVL::SVEXL-NODE-EVAL-WOG-META-MAIN
           . SVL::SVEXL-NODE-EVAL-WOG)
    (:META SVL::SVEX-EVAL-WOG-META-MAIN
           . SVL::SVEX-EVAL-WOG)
    (:META SVL::CONCAT-META . SV::4VEC-CONCAT)
    (:META SVL::CONCAT-META . SVL::4VEC-CONCAT$)
    (:META SVL::BITS-OF-META-FN . SVL::BITS)
    (:META SVL::BITS-OF-META-FN
           . SV::4VEC-PART-SELECT)
    (:META RP::MV-NTH-META . MV-NTH)
    (:META RP::RP-EQUAL-META . EQUAL)
    (:META RP::ASSOC-EQ-VALS-META . rp::ASSOC-EQ-VALS)
    (:META RP::HONS-GET-META . HONS-GET)
    (:META RP::FAST-ALIST-FREE-META . FAST-ALIST-FREE)
    (:META RP::HONS-ACONS-META . HONS-ACONS)))

(defconst *svex-simplify-meta-rules-outside-in*
  'nil)


(progn
  (defconst *svex-simplify-rules*
    '((:rewrite concat-of-rsh-with-0-to-bits)

      (:rewrite rp::force$-of-t)
      
      (:rewrite 4vec-part-select-is-bits)
      (:rewrite equal-of-4vec-concat$)
      (:rewrite 4vec-p-of-all-4vec-fncs)
      (:rewrite 4vec-fix-wog-of-functions)
      (:rewrite 4vec-fix-of-functions)
      (:rewrite bitp-of-4vec-bitnot$)
      (:rewrite bitp-of-4vec-bitnot)
      (:rewrite natp-4vec-bitnot$)
      (:rewrite integerp-4vec-bitnot$)
      (:rewrite integerp-4vec-bitnot)
      (:rewrite 4vec-p-4vec-bitnot)
      (:rewrite bit$-of-negated-bit)
      (:rewrite bitp-bits-size=1)
      (:rewrite natp-bits)
      (:rewrite natp-4vec-part-select-better)
      (:rewrite integerp-bits)
      (:rewrite integerp-4vec-part-select)
      (:rewrite 4vec-p-bits)
      (:rewrite bitp-4vec-concat$)
      (:rewrite natp-4vec-concat$)
      (:rewrite integerp-4vec-concat$)
      (:rewrite integerp-4vec-concat$-slower)
      (:rewrite 4vec-p-4vec-concat$)
      (:rewrite 4vec-p-4vec-bitor$)
      (:rewrite 4vec-p-4vec-bitxor$)
      (:rewrite 4vec-p-4vec-bitand$)
      (:rewrite integerp-implies-4vecp)
      (:rewrite natp-implies-integerp)
      (:rewrite bitp-implies-natp)
      (:rewrite 4vec-zero-ext-is-bits)
      (:rewrite bits-of-0)
      (:rewrite bits-0-1-of-4vec-reduction-and-when-amount=1)
      (:rewrite bits-0-1-of-4vec-reduction-and)
      (:rewrite bits-of-bits-1)
      (:rewrite bits-of-bits-2)
      (:rewrite bits-of-4vec-fix)
      (:rewrite bits-of-4vec-?)
      (:rewrite bits-of-4vec-?*)
      (:rewrite bits-of-4vec-plus-is-4vec-plus-start=0)
      (:rewrite bits-of-4vec-plus-is-4vec-plus)
      (:rewrite 4vec-part-install-is-sbits)
      (:rewrite sbits-of-bits)
      (:rewrite sbits-size=0)
      (:rewrite 4vec-concat$-of-term2=0)
      (:rewrite concat-of-size=0)
      (:rewrite sbits-of-concat)
      (:rewrite bits-of-concat-2)                  ;; remove?
      (:rewrite bits-of-concat-3)                  ;; remove?
      (:rewrite bits-of-concat-1)                  ;; remove?
      (:rewrite 4vec-concat-of-4vec-concat$-case-1) ;; remove?
      (:rewrite 4vec-concat$-of-4vec-concat$-case-1) ;; remove?
      (:rewrite 4vec-concat$-of-4vec-concat$-case-2) ;; remove?
      (:rewrite 4vec-concat-of-4vec-concat$-case-2)  ;; remove?
      (:rewrite convert-4vec-concat-to-4vec-concat$)
      (:rewrite 4vec-concat$-of-4vec-fix) ;; remove?
      (:rewrite equal-of-4vec-concat$-with-size=1)
      (:rewrite 4vec-rsh-of-bits-2)       ;; remove?
      (:rewrite 4vec-rsh-of-bits-1)       ;; remove?
      (:rewrite 4vec-rsh-of-4vec-concat$-1) ;; remove?
      (:executable-counterpart 4vec-rsh-of-4vec-concat$-1-hyp)
      (:definition 4vec-rsh-of-4vec-concat$-1-hyp)
      (:rewrite 4vec-rsh-of-4vec-concat$-2) ;;remove?
      (:rewrite bits-of-rsh)                ;; remove ?
      (:rewrite bits-of-lsh-3)              ;; put in meta and remove ?
      (:rewrite bits-of-lsh-2)              ;; put in meta and remove?
      (:rewrite bits-of-lsh-1)              ;;  put in meta and remove?
      (:rewrite 4vec-bitnot-of-4vec-concat$)
      (:rewrite bits-of-4vec-bitxor$) ;; remove?
      (:rewrite bits-of-4vec-bitor$)  ;; remove ?
      (:rewrite bits-of-4vec-bitand$) ;; remove?
      (:rewrite bits-of-4vec-bitnot$) ;; remove?
      (:rewrite bits-of-4vec-bitxor) 
      (:rewrite bits-of-4vec-bitor)
      (:rewrite bits-of-4vec-bitand)
      (:rewrite sbits-of-4vec-bitand)
      (:rewrite bits-of-4vec-bitnot)
      (:rewrite sbits-of-4vec-bitnot$-with-same-size)
      (:rewrite 4vec-bitor$-of-bits-of-same-size) ;; remove? necessary?
      (:rewrite 4vec-bitand$-of-bits-of-same-size) ;; remove? necessary?
      (:rewrite 4vec-bitnot$-of-bits-of-same-size) ;; remove? necessary?
      (:rewrite bits-01-of-a-bit)

      ;; 4vec-lemmas.lisp:
      (:rewrite integerp-implies-3vec-p)
      (:rewrite 4vec-bitand-of-3vec-fix)
      (:rewrite 4vec-part-select-of-4vec-reduction-and-when-amount=1)
      (:rewrite 4vec-part-select-of-4vec-reduction-and)
      (:rewrite 4vec-part-select-of-4vec-plus-is-4vec-plus)
      (:rewrite integerp-4vec-rsh)
      (:rewrite integerp-4vec-plus)
      (:rewrite 4vec-p-of-4vec-plus++)
      (:rewrite integer-of-4vec-plus++)
      (:executable-counterpart 4vec-plus++)
      (:rewrite 4vec-part-select-of-negated-bit)
      (:rewrite 4vec-?-of-test=0)
      (:rewrite bitp-4vec-part-select-size=1)
      (:rewrite 4vec-part-select-of-4vec-?*)
      (:rewrite integerp-4vec-bitand)
      (:rewrite integerp-4vec?)
      (:rewrite 4vec-?-with-1)
      (:rewrite 4vec-?-with-0)
      (:rewrite 4vec-bitor-with-0)
      (:rewrite 4vec-bitand-with-1)
      (:rewrite 4vec-bitand-with-0)
      (:rewrite 4vec-part-select-of-4vec-bitxor$-2)
      (:rewrite 4vec-part-select-of-4vec-bitxor$-1)
      (:rewrite 4vec-part-select-of-4vec-bitor$-2)
      (:rewrite 4vec-part-select-of-4vec-bitor$-1)
      (:rewrite 4vec-part-select-of-4vec-bitand$-2)
      (:rewrite 4vec-part-select-of-4vec-bitand$-1)
      (:rewrite 4vec-part-select-of-4vec-bitnot$-2)
      (:rewrite 4vec-part-select-of-4vec-bitnot$-1)
      (:rewrite 4vec-bitxor$-of-4vec-part-select-0-same-size)
      (:rewrite 4vec-bitor$-of-4vec-part-select-0-same-size)
      (:rewrite 4vec-bitand$-of-4vec-part-select-0-same-size)
      (:rewrite 4vec-part-select-size=0)
      (:rewrite 4vec-part-select-of-4vec-?)
      (:rewrite 4vec-?*-of-4vec-symwildeq-1)
      (:rewrite natp-4vec-?*)
      (:rewrite 4vec-bitnot-of-4vec-concat)
      (:rewrite 4vec-concat-of-4vec-fix-2)
      (:rewrite 4vec-concat-of-4vec-fix)
      (:rewrite 4vec-part-select-of-4vec-part-select-2)
      (:rewrite 4vec-part-select-of-4vec-part-select-1)
      (:rewrite 4vec-rsh-0)
      (:rewrite 4vec-concat-0-0)
      (:rewrite 4vec-part-install-of-4vec-part-install-sizes=1)
      (:rewrite 4vec-rsh-of-4vec-part-select-2)
      (:rewrite 4vec-rsh-of-4vec-part-select-1)
      (:rewrite 4vec-rsh-of-bitand)
      (:rewrite 4vec-rsh-of-bitor)
      (:rewrite 4vec-rsh-of-bitxor)
      (:rewrite 4vec-rsh-of-4vec-rsh)
      (:rewrite 4vec-part-install-of-4vec-part-select)
      (:rewrite 4vec-part-install-w=0)
      (:rewrite 4vec-part-select-of-4vec-lsh-3)
      (:rewrite 4vec-part-select-of-4vec-lsh-2)
      (:rewrite 4vec-part-select-of-4vec-lsh-1)
      (:rewrite 4vec-select-of-4vec-part-install-5)
      (:rewrite 4vec-select-of-4vec-part-install-4)
      (:rewrite 4vec-select-of-4vec-part-install-3)
      (:rewrite 4vec-select-of-4vec-part-install-2)
      (:rewrite 4vec-select-of-4vec-part-install-1)
      (:rewrite 4vec-part-select-of-4vec-rsh)
      (:rewrite 4vec-zero-ext-is-4vec-concat)
      (:rewrite natp-4vec-concat)
      (:rewrite 4vec-rsh-of-4vec-concat-2)
      (:rewrite 4vec-rsh-of-4vec-concat)
      (:rewrite 4vec-part-install-of-concat)
      (:rewrite 4vec-part-select-of-concat-3)
      (:rewrite 4vec-part-select-of-concat-2)
      (:rewrite 4vec-part-select-of-concat-1)
      (:rewrite equal-of-4vec-concat-with-size=1)
      (:rewrite 4vec-concat-of-4vec-concat-2)
      (:rewrite 4vec-concat-of-4vec-concat)
      (:rewrite 4vec-concat-of-width=1-term2=0)
      (:rewrite 4vec-concat-of-width=0)
      (:rewrite 4vec-rsh-of-width=0)
      (:rewrite natp-4vec-part-select)
      (:rewrite natp-4vec-zero-ext)
      (:rewrite natp-4vec-rsh)

      (:executable-counterpart sbits)
      (:executable-counterpart 4vec-p)
      (:executable-counterpart svex-p)
      (:executable-counterpart sv::svar-p)
      (:executable-counterpart natp)
      (:executable-counterpart integerp)
      (:executable-counterpart bitp)
      (:executable-counterpart <)
      (:executable-counterpart not)
      (:executable-counterpart unary--)
      (:executable-counterpart min)
      (:executable-counterpart binary-+)
      (:executable-counterpart svex-eval-wog)
      (:executable-counterpart sv::svex-env-p)
      (:executable-counterpart bits)
      (:executable-counterpart rp::rp)
      (:executable-counterpart 4vec-concat$)
      (:executable-counterpart 4vec-bitnot$)


      (:executable-counterpart hons-get)
      (:executable-counterpart hons-acons)
      (:executable-counterpart fast-alist-free)
      (:executable-counterpart svexl-eval-wog)
      (:rewrite svexl-eval-is-svexl-eval-wog)
      (:rewrite svexl-eval-wog-for-rp)
      ;;(:rewrite rp::svexl-eval-wog-opener_lambda-opener)
      (:rewrite svexl-eval-aux-wog-nil)

      ;;(:rewrite RP::SVEXL-EVAL-AUX-WOG-CONS_LAMBDA-OPENER)
      (:rewrite svexl-eval-aux-wog-cons)
      (:rewrite svexl-eval-aux-is-svexl-eval-aux-wog)
      (:executable-counterpart svexl-eval-aux-wog)
      (:rewrite svexl-node-eval-is-svexl-node-eval-wog)
      (:rewrite svexl-nodelist-eval-is-svexl-nodelist-eval-wog)
      (:rewrite svex-apply-is-svex-apply-wog)
      (:rewrite svex-env-lookup-is-svex-env-fastlookup-wog)
      (:rewrite svexl-nodelist-eval-wog-of-nil)
      (:rewrite svexl-nodelist-eval-wog-of-cons)
      (:rewrite svexl-eval-node-of-call)
      (:rewrite svexl-eval-node-of-quoted)
      (:rewrite svexl-eval-node-of-node)
      (:rewrite svexl-eval-node-of-var)
      (:executable-counterpart svexl-node-kind-wog$inline)
      (:executable-counterpart svexl-p)
      (:executable-counterpart svex-p)

      (:executable-counterpart svexl-node-p)
      (:executable-counterpart svl::svexl->node-array$inline)
      (:executable-counterpart svl::svexl->top-node$inline)
    
      (:rewrite svexlist-eval-wog-nil-def)
      (:rewrite svexlist-eval-wog-cons-def)
      (:rewrite svex-eval-wog-of-quoted)
      (:executable-counterpart svex-kind-wog-is-quote)
      (:rewrite svex-eval-wog-of-var)
      (:definition svex-kind-wog-is-var)
      (:executable-counterpart svex-kind-wog-is-var)
      (:rewrite svex-env-fastlookup-wog-def)
      (:rewrite svex-eval-wog_opener-error)

      (:definition return-last)

      (:rewrite 4vec-?*-test=1)
      (:rewrite 4vec-?*-test=0)
      (:rewrite 3vec-fix-of-3vec-p)
      (:rewrite cdr-cons)
      (:rewrite car-cons)

      (:executable-counterpart sv::4vec-fix$inline)
      (:executable-counterpart sv::4vec-bit-extract)
      (:executable-counterpart sv::3vec-fix)
      (:executable-counterpart sv::4vec-bitnot)
      (:executable-counterpart sv::4vec-bitand)
      (:executable-counterpart sv::4vec-bitor)
      (:executable-counterpart sv::4vec-bitxor)
      (:executable-counterpart sv::4vec-res)
      (:executable-counterpart sv::4vec-resand)
      (:executable-counterpart sv::4vec-resor)
      (:executable-counterpart sv::4vec-override)
      (:executable-counterpart sv::4vec-onset)
      (:executable-counterpart sv::4vec-offset)
      (:executable-counterpart sv::4vec-reduction-and)
      (:executable-counterpart sv::4vec-reduction-or)
      (:executable-counterpart sv::4vec-parity)
      (:executable-counterpart sv::4vec-zero-ext)
      (:executable-counterpart sv::4vec-sign-ext)
      (:executable-counterpart sv::4vec-concat)
      (:executable-counterpart sv::4vec-rev-blocks)
      (:executable-counterpart sv::4vec-rsh)
      (:executable-counterpart sv::4vec-lsh)
      (:executable-counterpart sv::4vec-plus)
      (:executable-counterpart sv::4vec-minus)
      (:executable-counterpart sv::4vec-uminus)
      (:executable-counterpart sv::4vec-times)
      (:executable-counterpart sv::4vec-quotient)
      (:executable-counterpart sv::4vec-remainder)
      (:executable-counterpart sv::4vec-xdet)
      (:executable-counterpart sv::4vec-countones)
      (:executable-counterpart sv::4vec-onehot)
      (:executable-counterpart sv::4vec-onehot)
      (:executable-counterpart sv::4vec-<)
      (:executable-counterpart sv::4vec-==)
      (:executable-counterpart sv::4vec-===)
      (:executable-counterpart sv::4vec-wildeq)
      (:executable-counterpart sv::4vec-wildeq-safe)
      (:executable-counterpart sv::4vec-symwildeq)
      (:executable-counterpart sv::4vec-clog2)
      (:executable-counterpart sv::4vec-pow)
      (:executable-counterpart sv::4vec-?)
      (:executable-counterpart sv::4vec-?*)
      (:executable-counterpart sv::4vec-bit?)
      (:executable-counterpart sv::4vec-part-select)
      (:executable-counterpart sv::4vec-part-install)

      (:rewrite svexllist-eval-wog-for-rp)
      ;(:rewrite rp::svexllist-eval-wog-opener_lambda-opener)
      (:executable-counterpart svexllist->top-nodelist$inline)
      (:executable-counterpart svexllist->node-array$inline)
      (:executable-counterpart svexllist-p)
      (:executable-counterpart svexl-node-array-p)
      (:executable-counterpart svexl-node-p)
      (:executable-counterpart equal)
      (:executable-counterpart =)
      (:executable-counterpart eql)
      (:executable-counterpart len)
      (:rewrite 4vec-bitor-reorder)
      (:rewrite 4vec-p-of-svex-env-fastlookup-wog)
      (:rewrite 4vec-bitor-of-negated-same-var-with-bitnot$)
      (:rewrite 4vec-bitor-with-one)
      (:rewrite 4vec-bitand-of-4vec-concat$)
      (:rewrite 4vec-bitor-of-4vec-concat$)
      (:rewrite 4vec-bitxor-of-4vec-concat$)

      (:rewrite logxor-to-4vec-bitxor)
      (:rewrite logand-to-4vec-bitand)
      (:rewrite logior-to-4vec-bitor)
      (:rewrite ash-to-4vec-lsh)
      (:rewrite ash-to-4vec-rsh)
      (:rewrite logtail-to-4vec-rsh)
      (:rewrite loghead-to-4vec-part-select)

      
      ))

  (make-event
   `(deftheory svex-simplify-rules
      ',*svex-simplify-rules*))) 
