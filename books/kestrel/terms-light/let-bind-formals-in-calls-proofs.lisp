; Proofs about let-bind-formals-in-calls-in-term
;
; Copyright (C) 2021-2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "let-bind-formals-in-calls")
(include-book "lambdas-closed-in-termp") ; todo: move proofs to separate book
(local (include-book "tools/flag" :dir :system))
(local (include-book "kestrel/typed-lists-light/pseudo-term-listp" :dir :system))
(local (include-book "kestrel/lists-light/subsetp-equal" :dir :system))

(local (make-flag let-bind-formals-in-calls-in-term))

(defthm-flag-let-bind-formals-in-calls-in-term
  (defthm free-vars-in-term-of-let-bind-formals-in-calls-in-term
    (implies (symbol-listp target-fn-formals)
             (equal (free-vars-in-term (let-bind-formals-in-calls-in-term term target-fn target-fn-formals))
                    (free-vars-in-term term)))
    :flag let-bind-formals-in-calls-in-term)
  (defthm free-vars-in-terms-of-let-bind-formals-in-calls-in-terms
    (implies (symbol-listp target-fn-formals)
             (equal (free-vars-in-terms (let-bind-formals-in-calls-in-terms terms target-fn target-fn-formals))
                    (free-vars-in-terms terms)))
    :flag let-bind-formals-in-calls-in-terms)
  :hints (("Goal" :in-theory (enable let-bind-formals-in-calls-in-term
                                     let-bind-formals-in-calls-in-terms
                                     free-vars-in-terms-when-symbol-listp))))

(defthm-flag-let-bind-formals-in-calls-in-term
  (defthm lambdas-closed-in-termp-of-let-bind-formals-in-calls-in-term
    (implies (and (lambdas-closed-in-termp term)
                  (symbol-listp target-fn-formals))
             (lambdas-closed-in-termp (let-bind-formals-in-calls-in-term term target-fn target-fn-formals)))
    :flag let-bind-formals-in-calls-in-term)
  (defthm lambdas-closed-in-termsp-of-let-bind-formals-in-calls-in-terms
    (implies (and (lambdas-closed-in-termsp terms)
                  (symbol-listp target-fn-formals))
             (lambdas-closed-in-termsp (let-bind-formals-in-calls-in-terms terms target-fn target-fn-formals)))
    :flag let-bind-formals-in-calls-in-terms)
  :hints (("Goal" :in-theory (enable let-bind-formals-in-calls-in-term
                                     let-bind-formals-in-calls-in-terms
                                     free-vars-in-terms-when-symbol-listp))))
