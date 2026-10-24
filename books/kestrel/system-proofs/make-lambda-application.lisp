; Correctness of the ACL2 system function make-lambda-application
;
; Copyright (C) 2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; MAKE-LAMBDA-APPLICATION (in translate.lisp) makes a term equivalent to BODY
;; with the FORMALS bound to the ACTUALS, dropping formals not used in BODY,
;; binding any extra free vars of BODY to themselves, and returning BODY itself
;; when no lambda is needed.  The rewriter uses it to instantiate HIDE terms
;; under the current substitution (see the HIDE cases of rewrite), and
;; translate uses it for DO loop$ bodies (see cmp-do-body-1).

;; It does not use CONS-TERM, so we state its correctness using EMPTY-EVAL,
;; which knows no functions; thus the result holds for every evaluator.

;; Compare make-lambda-application-simple-correct-1 in
;; kestrel/terms-light/make-lambda-application-simple-proofs.lisp, which needs
;; more hyps (no duplicate formals, len match, etc.).

(include-book "kestrel/evaluators/empty-eval" :dir :system)
(include-book "kestrel/terms-light/free-vars-in-term" :dir :system)
(local (include-book "kestrel/terms-light/empty-eval-helpers" :dir :system))
(local (include-book "kestrel/alists-light/alists-equiv-on" :dir :system))
(local (include-book "kestrel/alists-light/pairlis-dollar" :dir :system))
(local (include-book "kestrel/alists-light/assoc-equal" :dir :system))
(local (include-book "helpers"))
(local (include-book "kestrel/lists-light/intersection-equal" :dir :system))
(local (include-book "kestrel/lists-light/set-difference-equal" :dir :system))
(local (include-book "kestrel/lists-light/subsetp-equal" :dir :system))
(local (include-book "kestrel/lists-light/member-equal" :dir :system))
(local (include-book "kestrel/lists-light/append" :dir :system))

(local
 (defthm empty-eval-list-of-collect-by-position
   (equal (empty-eval-list (collect-by-position sub-domain full-domain full-range) a)
          (collect-by-position sub-domain full-domain (empty-eval-list full-range a)))))

;; Binding vars to their own values
(local
 (defthm cdr-of-assoc-equal-of-pairlis$-of-empty-eval-list-same
   (implies (and (member-equal key keys)
                 (symbolp key)
                 key)
            (equal (cdr (assoc-equal key (pairlis$ keys (empty-eval-list keys a))))
                   (cdr (assoc-equal key a))))
   :hints (("Goal" :in-theory (enable pairlis$ assoc-equal)))))

;; The case where the body has no free vars
(local
 (defthm equal-of-empty-eval-and-empty-eval-when-no-free-vars
   (implies (and (not (consp (free-vars-in-term body)))
                 (pseudo-termp body))
            (equal (equal (empty-eval body a1) (empty-eval body a2))
                   t))
   :hints (("Goal" :use (:instance equal-of-empty-eval-and-empty-eval-when-alists-equiv-on-alt
                                   (term body) (keys nil) (alist1 a1) (alist2 a2))))))

;; The case where the formals and actuals are the same

(local
 (defthm alists-equiv-on-of-append-of-pairlis$-of-empty-eval-list-same
   (implies (and (symbol-listp keys)
                 (not (member-equal nil keys)))
            (alists-equiv-on keys
                             (append (pairlis$ formals (empty-eval-list formals a)) a)
                             a))
   :hints (("Goal" :in-theory (enable alists-equiv-on)))))

(local
 (defthm empty-eval-of-append-of-pairlis$-of-empty-eval-list-same
   (implies (and (not (member-equal nil (free-vars-in-term body)))
                 (pseudo-termp body))
            (equal (empty-eval body (append (pairlis$ formals (empty-eval-list formals a)) a))
                   (empty-eval body a)))
   :hints (("Goal" :use (:instance equal-of-empty-eval-and-empty-eval-when-alists-equiv-on-alt
                                   (term body)
                                   (keys (free-vars-in-term body))
                                   (alist1 a)
                                   (alist2 (append (pairlis$ formals (empty-eval-list formals a)) a)))
            :in-theory (disable equal-of-empty-eval-and-empty-eval-when-alists-equiv-on-alt
                                alists-equiv-on-of-append-arg2
                                alists-equiv-on-of-append-arg3)))))

;; The main case, where a lambda is made, with extra vars

(local
 (defthm cdr-of-assoc-equal-for-make-lambda-application
   (implies (and (member-equal key vars)
                 (symbolp key)
                 key)
            (equal (cdr (assoc-equal key (append (pairlis$ (intersection-equal formals vars)
                                                           (collect-by-position vars formals vals))
                                                 (pairlis$ (set-difference-equal vars formals)
                                                           (empty-eval-list (set-difference-equal vars formals) a)))))
                   (cdr (assoc-equal key (append (pairlis$ formals vals) a)))))))

(local
 (defthm alists-equiv-on-for-make-lambda-application
   (implies (and (subsetp-equal keys vars)
                 (symbol-listp keys)
                 (not (member-equal nil keys)))
            (alists-equiv-on keys
                             (append (pairlis$ (intersection-equal formals vars)
                                               (collect-by-position vars formals vals))
                                     (pairlis$ (set-difference-equal vars formals)
                                               (empty-eval-list (set-difference-equal vars formals) a)))
                             (append (pairlis$ formals vals) a)))
   :hints (("Goal" :in-theory (e/d (alists-equiv-on) (alists-equiv-on-of-append-arg2 alists-equiv-on-of-append-arg3))))))

(local
 (defthm empty-eval-for-make-lambda-application
   (implies (and (subsetp-equal (free-vars-in-term body) vars)
                 (not (member-equal nil (free-vars-in-term body)))
                 (pseudo-termp body))
            (equal (empty-eval body (append (pairlis$ (intersection-equal formals vars)
                                                      (collect-by-position vars formals vals))
                                            (pairlis$ (set-difference-equal vars formals)
                                                      (empty-eval-list (set-difference-equal vars formals) a))))
                   (empty-eval body (append (pairlis$ formals vals) a))))
   :hints (("Goal" :use (:instance equal-of-empty-eval-and-empty-eval-when-alists-equiv-on-alt
                                   (term body)
                                   (keys (free-vars-in-term body))
                                   (alist1 (append (pairlis$ (intersection-equal formals vars)
                                                             (collect-by-position vars formals vals))
                                                   (pairlis$ (set-difference-equal vars formals)
                                                             (empty-eval-list (set-difference-equal vars formals) a))))
                                   (alist2 (append (pairlis$ formals vals) a)))
            :in-theory (disable equal-of-empty-eval-and-empty-eval-when-alists-equiv-on-alt
                                alists-equiv-on-of-append-arg2
                                alists-equiv-on-of-append-arg3)))))

;; The case where a lambda is made, with no extra vars

(local
 (defthm alists-equiv-on-for-make-lambda-application-2
   (implies (subsetp-equal keys vars)
            (alists-equiv-on keys
                             (pairlis$ (intersection-equal formals vars)
                                       (collect-by-position vars formals vals))
                             (pairlis$ formals vals)))
   :hints (("Goal" :in-theory (enable alists-equiv-on)))))

(local
 (defthm empty-eval-for-make-lambda-application-2
   (implies (and (subsetp-equal (free-vars-in-term body) vars)
                 (pseudo-termp body))
            (equal (empty-eval body (pairlis$ (intersection-equal formals vars)
                                              (collect-by-position vars formals vals)))
                   (empty-eval body (pairlis$ formals vals))))
   :hints (("Goal" :use (:instance equal-of-empty-eval-and-empty-eval-when-alists-equiv-on-alt
                                   (term body)
                                   (keys (free-vars-in-term body))
                                   (alist1 (pairlis$ (intersection-equal formals vars)
                                                     (collect-by-position vars formals vals)))
                                   (alist2 (pairlis$ formals vals)))
            :in-theory (disable equal-of-empty-eval-and-empty-eval-when-alists-equiv-on-alt)))))

(local
 (defthm empty-eval-of-append-of-pairlis$-when-closed
   (implies (and (subsetp-equal (free-vars-in-term body) formals)
                 (pseudo-termp body))
            (equal (empty-eval body (append (pairlis$ formals vals) a))
                   (empty-eval body (pairlis$ formals vals))))
   :hints (("Goal" :use (:instance equal-of-empty-eval-and-empty-eval-when-alists-equiv-on-alt
                                   (term body)
                                   (keys formals)
                                   (alist1 (append (pairlis$ formals vals) a))
                                   (alist2 (pairlis$ formals vals)))
            :in-theory (disable equal-of-empty-eval-and-empty-eval-when-alists-equiv-on-alt)))))

;; The main theorem: Evaluating the result of make-lambda-application is like
;; evaluating BODY in an alist that binds the FORMALS to the values of the
;; ACTUALS.  No assumptions about the FORMALS or ACTUALS are needed (not even
;; that their lengths match, nor that the formals are distinct).
(defthm make-lambda-application-correct
  (implies (and (not (member-equal nil (free-vars-in-term body))) ; the "variable" NIL always evaluates to NIL
                (pseudo-termp body))
           (equal (empty-eval (make-lambda-application formals body actuals) a)
                  (empty-eval body (append (pairlis$ formals (empty-eval-list actuals a)) a))))
  :hints (("Goal" :in-theory (disable empty-eval-list-of-cons))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; What MAKE-LAMBDA-APPLICATION is for: it returns BODY when no lambda is
;; needed (BODY has no variables, or the FORMALS are the ACTUALS).  Otherwise,
;; it makes a lambda application whose body is BODY and whose formals are
;; exactly the variables of BODY: none is unused, and the lambda is closed.  The
;; lambda formals are distinct if the FORMALS are, and there is one argument per
;; lambda formal.

(include-book "kestrel/terms-light/lambdas-closed-in-termp" :dir :system)
(include-book "kestrel/terms-light/no-nils-in-termp" :dir :system)
(include-book "kestrel/terms-light/no-duplicate-lambda-formals-in-termp" :dir :system)
(local (include-book "kestrel/terms-light/all-vars1" :dir :system))
(local (include-book "kestrel/lists-light/no-duplicatesp-equal" :dir :system))
(local (include-book "kestrel/typed-lists-light/symbol-listp" :dir :system))
(local (include-book "kestrel/typed-lists-light/pseudo-term-listp" :dir :system))

(defthm make-lambda-application-when-no-lambda-needed
  (implies (or (not (all-vars body))
               (equal formals actuals))
           (equal (make-lambda-application formals body actuals)
                  body)))

(defthm make-lambda-application-when-lambda-needed
  (implies (and (all-vars body)
                (not (equal formals actuals)))
           (let* ((result (make-lambda-application formals body actuals))
                  (fn (ffn-symb result)))
             (and (flambdap fn)
                  (equal (lambda-body fn) body)
                  ;; No unused formals:
                  (subsetp-equal (lambda-formals fn) (all-vars body))
                  ;; Closed:
                  (subsetp-equal (all-vars body) (lambda-formals fn))
                  (implies (no-duplicatesp-equal formals)
                           (no-duplicatesp-equal (lambda-formals fn)))
                  (equal (len (fargs result))
                         (len (lambda-formals fn)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; MAKE-LAMBDA-APPLICATION preserves the usual properties of terms.

(defthm pseudo-termp-of-make-lambda-application
  (implies (and (pseudo-termp body)
                (pseudo-term-listp actuals)
                (symbol-listp formals))
           (pseudo-termp (make-lambda-application formals body actuals))))

(defthm termp-of-make-lambda-application
  (implies (and (termp body w)
                (term-listp actuals w)
                (no-duplicatesp-equal formals)
                (equal (len formals) (len actuals)))
           (termp (make-lambda-application formals body actuals) w)))

(defthm no-nils-in-termp-of-make-lambda-application
  (implies (and (no-nils-in-termp body)
                (no-nils-in-termsp actuals)
                (pseudo-termp body)
                (equal (len formals) (len actuals)))
           (no-nils-in-termp (make-lambda-application formals body actuals))))

(defthm lambdas-closed-in-termp-of-make-lambda-application
  (implies (and (lambdas-closed-in-termp body)
                (lambdas-closed-in-termsp actuals)
                (pseudo-termp body))
           (lambdas-closed-in-termp (make-lambda-application formals body actuals)))
  :hints (("Goal" :use (:instance subsetp-equal-transitive-alt
                                  (x (free-vars-in-term body))
                                  (y (all-vars body))
                                  (z (append (intersection-equal formals (all-vars body))
                                             (set-difference-equal (all-vars body) formals)))))))

(defthm no-duplicate-lambda-formals-in-termp-of-make-lambda-application
  (implies (and (no-duplicate-lambda-formals-in-termp body)
                (no-duplicate-lambda-formals-in-termsp actuals)
                (no-duplicatesp-equal formals)
                (pseudo-termp body))
           (no-duplicate-lambda-formals-in-termp (make-lambda-application formals body actuals))))

;; The variables of the result are those of the ACTUALS and those of BODY not
;; among the FORMALS.
(local (include-book "kestrel/lists-light/remove-duplicates-equal" :dir :system))
(local (include-book "kestrel/lists-light/union-equal" :dir :system))

(local
 (defthm subsetp-equal-of-union-equal-of-remove-duplicates-equal-and-set-difference-equal
   (subsetp-equal x (union-equal (remove-duplicates-equal y)
                                 (set-difference-equal x y)))
   :hints (("Goal" :in-theory (enable subsetp-equal)))))

(defthm subsetp-equal-of-free-vars-in-term-of-make-lambda-application
  (implies (and (pseudo-termp body)
                (symbol-listp formals)
                (equal (len formals) (len actuals)))
           (subsetp-equal (free-vars-in-term (make-lambda-application formals body actuals))
                          (union-equal (free-vars-in-terms actuals)
                                       (set-difference-equal (free-vars-in-term body) formals))))
  :hints (("Goal" :in-theory (enable free-vars-in-terms-when-symbol-listp))))

;; The no-duplicates hyps above are needed: see
;; make-lambda-application-can-make-duplicate-formals in
;; make-lambda-application-tests.lisp.
