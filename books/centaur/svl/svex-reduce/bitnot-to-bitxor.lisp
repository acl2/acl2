; SVL - Listener-based Hierachical Symbolic Vector Hardware Analysis Framework
; Copyright (C) 2021 Centaur Technology
; Copyright (C) 2022 Intel Corporation
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
; Original author: Mertcan Temel <mert@centtech.com>

(in-package "SVL")

(include-book "centaur/sv/svex/eval" :dir :system)
(include-book "projects/rp-rewriter/top" :dir :system)

(include-book "../fnc-defs")
(include-book "svex-reduce-apply")

(local
 (include-book "../4vec-lemmas"))

(local
 (include-book "../bits-sbits"))

(local
 (rp::fetch-new-events
  (include-book "centaur/bitops/ihs-extensions" :dir :system)
  use-ihs-extensions
  :disabled t))

(local
 (rp::fetch-new-events
  (include-book "ihs/logops-lemmas" :dir :system)
  use-ihs-logops-lemmas
  :disabled t))

(local
 (rp::fetch-new-events
  (include-book "arithmetic-5/top" :dir :system)
  use-arithmetic-5
  :disabled t))

(local
 (rp::fetch-new-events
  (include-book "ihs/quotient-remainder-lemmas" :dir :system)
  use-qr-lemmas
  :disabled t))

(local
 (rp::fetch-new-events
  (include-book "centaur/bitops/equal-by-logbitp" :dir :system)
  use-equal-by-logbitp
  :disabled t))

(defines svex-convert-bitnot-to-bitxor
  :hints (("Goal"
           :in-theory (e/d (SVEX-KIND
                            SV::SVEX-COUNT) ())))
  :verify-guards nil
  (define svex-convert-bitnot-to-bitxor ((svex svex-p))
    :measure (sv::svex-count svex)
    :returns (res svex-p :hyp (and (svex-p svex)))
    (cond ((not (equal (sv::svex-kind svex) :call))
           svex)
          ((and (equal (sv::svex-call->fn svex) 'sv::bitnot)
                (equal (len (sv::svex-call->args svex)) 1))
           (svex-reduce-w/-env-apply 'sv::bitxor
                                     (hons-list -1
                                                (svex-convert-bitnot-to-bitxor
                                                 (car (sv::svex-call->args svex))))))
          (t
           (sv::svex-call (sv::svex-call->fn svex)
                          (svexlist-convert-bitnot-to-bitxor
                           (sv::svex-call->args svex))))))
  (define svexlist-convert-bitnot-to-bitxor ((lst svexlist-p))
    :measure (sv::svexlist-count lst)
    :returns (res svexlist-p :hyp (and (svexlist-p lst)))
    (if (atom lst)
        nil
      (hons (svex-convert-bitnot-to-bitxor (car lst))
            (svexlist-convert-bitnot-to-bitxor (cdr lst)))))
  ///
  (verify-guards svex-convert-bitnot-to-bitxor)

  (memoize 'svex-convert-bitnot-to-bitxor
           :condition '(equal (svex-kind svex) :call)
           ;;:aokp t
           )

  (defret-mutual <fn>-correct
    (defret <fn>-correct
      (equal (svex-eval res a)
             (svex-eval svex a))
      :fn svex-convert-bitnot-to-bitxor)
    (defret <fn>-correct
      (equal (svexlist-eval res a)
             (svexlist-eval lst a))
      :fn svexlist-convert-bitnot-to-bitxor)
    :hints (("Goal"
             :expand ((:free (x)
                             (svex-apply 'bitnot x))
                      (:free (x)
                             (svex-eval (cons 'bitxor x) a))
                      (:free (x)
                             (svex-eval (cons 'bitnot x) a))
                      (:free (x)
                             (svex-apply 'sv::bitxor x))
                      (svex-convert-bitnot-to-bitxor svex)
                      (svexlist-convert-bitnot-to-bitxor LST))
             :in-theory (e/d (4vec-bitnot-to-4vec-bitxor
                              SVEX-CALL->ARGS
                              svex-kind
                              SVEX-CALL->FN
                              4VECLIST-NTH-SAFE)
                             ())))))



(define svexalist-convert-bitnot-to-bitxor ((alist sv::svex-alist-p))
  :returns (res sv::svex-alist-p :hyp (sv::svex-alist-p alist))
  (if (atom alist)
      (progn$ (clear-memoize-table 'svex-convert-bitnot-to-bitxor)
              nil)
    (acons (caar alist)
           (svex-convert-bitnot-to-bitxor (cdar alist))
           (svexalist-convert-bitnot-to-bitxor (cdr alist))))
  ///
  (defret <fn>-correct
    (equal (svex-alist-eval res a)
           (svex-alist-eval alist a))
    :hints (("Goal"
             :expand ((SVEX-ALIST-EVAL ALIST A))
             :in-theory (e/d (SVEX-ALIST-EVAL)
                             ())))))
