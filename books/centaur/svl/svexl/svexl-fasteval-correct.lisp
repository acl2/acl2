
; SVL - Listener-based Hierachical Symbolic Vector Hardware Analysis Framework
; Copyright (C) 2021 Centaur Technology
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

(include-book "svexl-fasteval")

;; (skip-proofs
;;  (defthmd svexl-fasteval-correct
;;      (implies (and (force (svex-p svex))
;;                    (force (svex-env-p env)))
;;               (equal (svex-eval svex env)
;;                   (svexl-fasteval (svex-to-svexl svex) env)))))

;; (skip-proofs
;;  (defthmd svexllist-fasteval-correct
;;      (implies (and (force (svexlist-p lst))
;;                    (force (svex-env-p env)))
;;               (equal (svexlist-eval lst env)
;;                      (svexllist-fasteval (svexlist-to-svexllist lst) env)))))

;; (skip-proofs
;;  (defthmd svexl-alist-fasteval-correct
;;      (implies (and (force (sv::svex-alist-p alist))
;;                    (force (svex-env-p env)))
;;               (equal (sv::svex-alist-eval alist env)
;;                      (svexl-alist-fasteval (svex-alist-to-svexl-alist alist) env)))))


;; (rp::add-rp-rule svexl-fasteval-correct :disabled t)
;; (rp::add-rp-rule svexllist-fasteval-correct :disabled t)
;; (rp::add-rp-rule svexl-alist-fasteval-correct :disabled t)

(memoize 'svex-alist-to-svexl-alist)
(memoize 'svexlist-to-svexllist)
