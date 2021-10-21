; Proof of correctness of expand-lambdas-in-term
;
; Copyright (C) 2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "expand-lambdas-in-term")
(include-book "kestrel/evaluators/empty-eval" :dir :system)
(local (include-book "kestrel/alists-light/assoc-equal" :dir :system))
(local (include-book "kestrel/alists-light/strip-cars" :dir :system))
(local (include-book "kestrel/alists-light/strip-cdrs" :dir :system))
(local (include-book "kestrel/alists-light/pairlis-dollar" :dir :system))
(local (include-book "kestrel/lists-light/append" :dir :system))
(local (include-book "kestrel/lists-light/nthcdr" :dir :system))
(local (include-book "kestrel/lists-light/take" :dir :system))
(local (include-book "kestrel/lists-light/member-equal" :dir :system))
(local (include-book "kestrel/lists-light/len" :dir :system))
(local (include-book "kestrel/lists-light/set-difference-equal" :dir :system))
(local (include-book "kestrel/lists-light/no-duplicatesp-equal" :dir :system))
(local (include-book "kestrel/lists-light/cons" :dir :system))
(local (include-book "kestrel/lists-light/subsetp-equal" :dir :system))
(local (include-book "kestrel/arithmetic-light/less-than" :dir :system))
(local (include-book "kestrel/typed-lists-light/symbol-listp" :dir :system))
(local (include-book "kestrel/typed-lists-light/pseudo-term-listp" :dir :system))


(local (in-theory (disable member-equal symbol-listp set-difference-equal PSEUDO-TERM-LISTP len
                           STRIP-CADRS
                           STRIP-CDRS)))

;todo: automate some of this?

(defthm cdr-of-expand-lambdas-in-terms
  (equal (cdr (expand-lambdas-in-terms terms))
         (expand-lambdas-in-terms (cdr terms)))
  :hints (("Goal" :induct (len terms)
           :in-theory (enable (:i len) expand-lambdas-in-terms))))

;; TODO: Compare to make-lambda-term.
;; maybe just call this make-lambda?
(defund wrap-term-in-lambda (body lambda-formals args)
  (declare (xargs :guard (and (pseudo-termp body)
                              (symbol-listp lambda-formals)
                              (pseudo-term-listp args)
                              (equal (len lambda-formals)
                                     (len args)))))
  (let* ((free-vars (free-vars-in-term body))
         (extra-vars (set-difference-eq free-vars lambda-formals)))
    ;; Binds the lambda-formals to their args and all other vars to themselves:
    `((lambda ,(append lambda-formals extra-vars) ,body) ,@args ,@extra-vars)))

(defthm pseudo-termp-of-wrap-term-in-lambda
  (implies (and (pseudo-termp body)
                (symbol-listp lambda-formals)
                (pseudo-term-listp args)
                (equal (len args) (len lambda-formals)))
           (pseudo-termp (wrap-term-in-lambda body lambda-formals args)))
  :hints (("Goal" :in-theory (enable wrap-term-in-lambda))))

(defthm EMPTY-EVAL-of-cdr-of-assoc-equal
  (IMPLIES (AND (SYMBOLP TERM)
                ;(MEMBER-EQUAL TERM LAMBDA-FORMALS)
        ;        (SYMBOL-LISTP LAMBDA-FORMALS)
                ;(PSEUDO-TERM-LISTP ARGS)
       ;         (EQUAL (LEN LAMBDA-FORMALS) (LEN ARGS))
                TERM)
           (EQUAL (EMPTY-EVAL (CDR (ASSOC-EQUAL TERM alist)) A)
                  (CDR (ASSOC-EQUAL TERM (PAIRLIS$ (strip-cars alist)
                                                   (EMPTY-EVAL-LIST (strip-cdrs alist)
                                                                     A))))))
  :hints (("Goal" :in-theory (enable PAIRLIS$ assoc-equal))))

(defthm empty-eval-of-wrap-term-in-lambda-when-symbolp
  (implies (and (symbolp term)
;                (symbol-listp lambda-formals)
;                (pseudo-term-listp args)
                (equal (len lambda-formals) (len args)))
           (equal (empty-eval (wrap-term-in-lambda term lambda-formals args) a)
                  (if (equal term nil) ; gross exception in defevaluator
                      nil
                    (if (member-equal term lambda-formals)
                        (empty-eval (cdr (assoc-equal term (pairlis$ lambda-formals args)))
                                     a)
                      (empty-eval term a)))))
  :hints (("Goal" :in-theory (enable wrap-term-in-lambda
                                     ;assoc-equal-iff
                                     ))))

(include-book "kestrel/alists-light/lookup-equal" :dir :system)
(include-book "kestrel/alists-light/lookup-equal-lst" :dir :system)

;this holds for any evaluator?
(defthm empty-eval-list-when-symbol-listp
  (implies (and (symbol-listp vars)
                (not (member-equal nil vars)))
           (equal (empty-eval-list vars a)
                  (lookup-equal-lst vars a)))
  :hints (("Goal" :in-theory (enable ;empty-eval-list
                              (:i len)
                              LOOKUP-EQUAL)
           :induct (len vars))))

;; Checks whether ALIST1 and ALIST2 are equivalent wrt the KEYS.  For these
;; purposes, not having a binding for a key is equivalent to binding it to nil.
(defun alists-equiv-on (keys alist1 alist2)
  (if (endp keys)
      t
    (let ((key (first keys)))
      (and (equal (cdr (assoc-equal key alist1)) ; ok if bound to nil in one alist and not bound in the other
                  (cdr (assoc-equal key alist2)))
           (alists-equiv-on (rest keys) alist1 alist2)))))

(defthm alists-equiv-on-of-union-equal
  (equal (alists-equiv-on (union-equal keys1 keys2) alist1 alist2)
         (and (alists-equiv-on keys1 alist1 alist2)
              (alists-equiv-on keys2 alist1 alist2))))

;; empty-eval gives the same result if the alist is changed to one that equivalent for the free vars of the term
(defthm-flag-free-vars-in-term
  (defthm equal-of-empty-eval-and-empty-eval-when-alists-equiv-on
    (implies (and (alists-equiv-on (free-vars-in-term term) alist1 alist2)
                  (pseudo-termp term))
             (equal (equal (empty-eval term alist1)
                           (empty-eval term alist2))
                    t))
    :flag free-vars-in-term)
  (defthm equal-of-empty-eval-list-and-empty-eval-list-when-alists-equiv-on
    (implies (and (alists-equiv-on (free-vars-in-terms terms) alist1 alist2)
                  (pseudo-term-listp terms))
             (equal (equal (empty-eval-list terms alist1)
                           (empty-eval-list terms alist2))
                    t))
    :flag free-vars-in-terms)
  :hints (("Goal" :expand (PSEUDO-TERMP TERM)
           :in-theory (e/d (free-vars-in-terms
                            empty-eval-of-fncall-args)
                           (empty-eval-of-fncall-args-back)))))

(defthm ALISTS-EQUIV-ON-of-cons-and-cons-same
  (implies (ALISTS-EQUIV-ON KEYS alist1 alist2)
           (ALISTS-EQUIV-ON KEYS
                            (CONS pair alist1)
                            (CONS pair alist2))))

(defthm ALISTS-EQUIV-ON-of-cons-and-cons-same-2
  (implies (ALISTS-EQUIV-ON (remove-equal (car pair) KEYS) alist1 alist2)
           (ALISTS-EQUIV-ON KEYS
                            (CONS pair alist1)
                            (CONS pair alist2))))

(defthm equal-of-cdr-of-assoc-equal-and-cdr-of-assoc-equal-when-alists-equiv-on
  (implies (and (alists-equiv-on keys alist1 alist2)
                (member-equal key keys))
           (equal (equal (cdr (assoc-equal key alist1))
                         (cdr (assoc-equal key alist2)))
                  t)))

(defun cdr-remove-caar-induct (x y)
  (if (endp x)
      (list x y)
    (cdr-remove-caar-induct (cdr x) (remove-equal (caar x) y))))

(defthm alists-equiv-on-of-append-and-append-same
  (implies (and (alists-equiv-on (set-difference-equal keys (strip-cars alist1))
                                 alist2
                                 alist3)
                (alistp alist1)
;                (no-duplicatesp-equal (strip-cars alist1)) ;drop?
                )
           (alists-equiv-on keys
                            (append alist1 alist2)
                            (append alist1 alist3)))
  :hints (("subgoal *1/2" :cases ((equal (car keys) (caar alist1))))
          ("Goal" :expand ((STRIP-CARS ALIST1)
                           (ALISTS-EQUIV-ON KEYS (APPEND ALIST1 ALIST2)
                                            (APPEND ALIST1 ALIST3)))
           :induct (cdr-remove-caar-induct ALIST1 keys)
           :do-not '(generalize eliminate-destructors)
           :in-theory (enable append
                              ))))

(defthm equal-of-car-of-assoc-equal-same
  (implies (alistp alist)
           (iff (equal key (car (assoc-equal key alist)))
                (or (equal key nil)
                    (assoc-equal key alist)))))

(defun cdr-remove-caar-induct-2 (x y)
  (if (or (endp x)
          (endp y))
      (list x y)
    (cdr-remove-caar-induct-2 (cdr x) (remove-equal (caar x) y))))

(defthm assoc-equal-of-pairlis$-when-not-member-equal
  (implies (not (member-equal key keys))
           (equal (assoc-equal key (pairlis$ keys vals))
                  nil)))

(defthm assoc-equal-of-pairlis$-of-lookup-equal-lst-same
  (implies (alistp alist)
           (equal (assoc-equal key (pairlis$ keys (lookup-equal-lst keys alist)))
                  (if (member-equal key keys)
                      (cons key (cdr (assoc-equal key alist)))
                    nil)))
  :hints (("Goal" :in-theory (enable assoc-equal lookup-equal-lst pairlis$ LOOKUP-EQUAL))))


(defthm alists-equiv-on-of-pairlis$-of-lookup-equal-lst-same
  (alists-equiv-on keys
                   (pairlis$ keys (lookup-equal-lst keys a))
                   a)
  :hints (("Goal" :expand (ALISTS-EQUIV-ON KEYS
                                           (PAIRLIS$ KEYS (LOOKUP-EQUAL-LST KEYS A))
                                           A)
;:induct (ALISTS-EQUIV-ON KEYS a a)
           :in-theory (enable pairlis$ lookup-equal
                              assoc-equal-iff
                              (:I len)))))

;; term may have free vars not among the lambda formals
(defthm empty-eval-of-wrap-term-in-lambda
  (implies (and (pseudo-termp term)
                (not (member-equal nil (free-vars-in-term term))) ;drop? may need the notion of alists agreeing on a set of keys not involving nil
                (equal (len lambda-formals) (len args)))
           (equal (empty-eval (wrap-term-in-lambda term lambda-formals args) a)
                  (empty-eval term
                               (append (pairlis$ lambda-formals (empty-eval-list args a)) ; these pairs may shadow pairs in a
                                       a))))
  :hints (("Goal" :in-theory (enable wrap-term-in-lambda))))

;; (thm
;;  (implies (and (consp term)
;;                (not (equal 'quote (car term)))
;;                (symbolp (car term))
;;                (symbol-alistp alist)
;;                (pseudo-term-listp (strip-cdrs alist))
;;                (pseudo-term-listp (cdr term))
;;                (equal (len lambda-formals) (len args))
;;                )
;;           (equal (empty-eval (wrap-term-in-lambda term lambda-formals args) a)
;;                  (empty-eval (cons
;;                                (car term) (KWOTE-LST (empty-eval-list (WRAP-TERMS-IN-LAMBDAS (cdr term) lambda-formals args) a)))
;;                               nil)))
;;  :hints (("Goal" :in-theory (enable wrap-term-in-lambda
;;                                     EMPTY-EVAL-OF-FNCALL-ARGS))))

(defund wrap-terms-in-lambdas (terms lambda-formals args)
  (if (endp terms)
      nil
    (cons (wrap-term-in-lambda (first terms) lambda-formals args)
          (wrap-terms-in-lambdas (rest terms) lambda-formals args))))

(defthm wrap-terms-in-lambdas-of-nil
  (equal (wrap-terms-in-lambdas nil lambda-formals args)
         nil)
  :hints (("Goal" :in-theory (enable wrap-terms-in-lambdas))))

(defthm empty-eval-list-of-wrap-terms-in-lambdas
  (implies (and (pseudo-term-listp terms)
                (not (member-equal nil (free-vars-in-terms terms))) ;drop?
                (equal (len lambda-formals) (len args)))
           (equal (empty-eval-list (wrap-terms-in-lambdas terms lambda-formals args) a)
                  (empty-eval-list terms
                                    (append (pairlis$ lambda-formals (empty-eval-list args a)) ; these pairs may shadow pairs in a
                                            a))))
  :hints (("Goal" :in-theory (enable wrap-terms-in-lambdas))))

;todo: exclude term from being nil, or containing a nil as a subterm, since defevaluator has gross behavior on nil.
;move
(defthm-flag-sublis-var-simple
  (defthm sublis-var-simple-correct
    (implies (and (symbol-alistp alist) ; usually a symbol-term-alistp
                  (pseudo-term-listp (strip-cdrs alist))
                  (pseudo-termp term)
                  (not (member-equal nil (free-vars-in-term term))))
             (equal (empty-eval (sublis-var-simple alist term) a)
                    (empty-eval (wrap-term-in-lambda term (strip-cars alist) (strip-cdrs alist)) a)))
    :flag sublis-var-simple)
  (defthm sublis-var-simple-lst-correct
    (implies (and (symbol-alistp alist) ; usually a symbol-term-alistp
                  (pseudo-term-listp (strip-cdrs alist))
                  (pseudo-term-listp terms)
                  (not (member-equal nil (free-vars-in-terms terms))))
             (equal (empty-eval-list (sublis-var-simple-lst alist terms) a)
                    (empty-eval-list (wrap-terms-in-lambdas terms (strip-cars alist) (strip-cdrs alist)) a)))
    :flag sublis-var-simple-lst)
  :hints (("Goal" :expand (PSEUDO-TERMP TERM)
           :in-theory (e/d (sublis-var-simple
                            sublis-var-simple-lst
                            MEMBER-EQUAL-OF-STRIP-CARS-IFF
                            wrap-terms-in-lambdas
                            ;;wrap-term-in-lambda
                            empty-eval-of-fncall-args)
                           (pairlis$
                            set-difference-equal
                            empty-eval-of-fncall-args-back)))))

(defthm-flag-sublis-var-simple
  (defthm sublis-var-simple-correct2
    (implies (and (symbol-alistp alist) ; usually a symbol-term-alistp
                  (pseudo-term-listp (strip-cdrs alist))
                  (pseudo-termp term)
                  (not (member-equal nil (free-vars-in-term term)))
                  (subsetp-equal (free-vars-in-term term) (strip-cars alist))
                  )
             (equal (empty-eval (sublis-var-simple alist term) a)
                    (empty-eval term (pairlis$ (strip-cars alist)
                                                (empty-eval-list (strip-cdrs alist) a)))))
    :flag sublis-var-simple)
  (defthm sublis-var-simple-lst-correct2
    (implies (and (symbol-alistp alist) ; usually a symbol-term-alistp
                  (pseudo-term-listp (strip-cdrs alist))
                  (pseudo-term-listp terms)
                  (not (member-equal nil (free-vars-in-terms terms)))
                  (subsetp-equal (free-vars-in-terms terms) (strip-cars alist)))
             (equal (empty-eval-list (sublis-var-simple-lst alist terms) a)
                    (empty-eval-list terms
                                      (pairlis$ (strip-cars alist)
                                                (empty-eval-list (strip-cdrs alist) a)))))
    :flag sublis-var-simple-lst)
  :hints (("Goal" :expand (PSEUDO-TERMP TERM)
           :in-theory (e/d (sublis-var-simple
                            sublis-var-simple-lst
                            MEMBER-EQUAL-OF-STRIP-CARS-IFF
                            wrap-terms-in-lambdas
                            ;;wrap-term-in-lambda
                            empty-eval-of-fncall-args)
                           (pairlis$
                            set-difference-equal
                            empty-eval-of-fncall-args-back)))))




(DEFTHM SUBSETP-EQUAL-OF-FREE-VARS-IN-TERM-OF-SUBLIS-VAR-SIMPLE-AND-FREE-VARS-IN-TERMS-OF-STRIP-CDRS-gen
  (IMPLIES (and (SUBSETP-EQUAL (FREE-VARS-IN-TERM TERM)
                               (STRIP-CARS ALIST))
                (subsetp-equal (FREE-VARS-IN-TERMS (STRIP-CDRS ALIST)) free))
           (SUBSETP-EQUAL (FREE-VARS-IN-TERM (SUBLIS-VAR-SIMPLE ALIST TERM))
                          free)))

(defthm free-vars-in-terms-of-true-list-fix
  (equal (free-vars-in-terms (true-list-fix terms))
         (free-vars-in-terms terms))
  :hints (("Goal" :in-theory (enable true-list-fix free-vars-in-terms))))

(defthm-flag-expand-lambdas-in-term
  (defthm free-vars-in-term-of-expand-lambdas-in-term
    (implies (and (pseudo-termp term)
                  (LAMBDAS-CLOSED-IN-TERMP term))
             (subsetp-equal (free-vars-in-term (expand-lambdas-in-term term))
                            (free-vars-in-term term)))
    :flag expand-lambdas-in-term)
  (defthm free-vars-in-terms-of-expand-lambdas-in-terms
    (implies (and (pseudo-term-listp terms)
                  (LAMBDAS-CLOSED-IN-TERMsP terms))
             (subsetp-equal (free-vars-in-terms (expand-lambdas-in-terms terms))
                            (free-vars-in-terms terms)))
    :flag expand-lambdas-in-terms)
  :hints (("Goal" :expand ((expand-lambdas-in-term terms)
                           (FREE-VARS-IN-TERM TERM))
           :do-not '(generalize eliminate-destructors)
           :in-theory (e/d (expand-lambdas-in-term
                            empty-eval-of-fncall-args
                            free-vars-in-terms
                            lambdas-closed-in-termp)
                           (empty-eval-of-fncall-args-back)))))

(defthm free-vars-in-term-of-expand-lambdas-in-term-gen
  (implies (and (pseudo-termp term)
                (LAMBDAS-CLOSED-IN-TERMP term)
                (subsetp-equal (free-vars-in-term term) free)
                )
           (subsetp-equal (free-vars-in-term (expand-lambdas-in-term term))
                          free))
  )

(defthm not-member-equal-of-free-var-in-term-of-expand-lambdas-in-term
  (implies (and (not (member-equal var (free-vars-in-term term)))
                (pseudo-termp term)
                (lambdas-closed-in-termp term))
           (not (member-equal var (free-vars-in-term (expand-lambdas-in-term term))))))

;; This is needed due to a deficiency in how deevaluator evaluates NIL, which
;; is syntactually a variable although not a legal one:
(mutual-recursion
 (defun no-nils-in-termp (term)
   (declare (xargs :guard (pseudo-termp term)))
   (if (variablep term)
       (not (equal term nil))
     (let ((fn (ffn-symb term)))
       (if (eq 'quote fn)
           t
         (and (no-nils-in-termsp (fargs term))
              (if (consp fn)
                  (no-nils-in-termp (lambda-body fn))
                t))))))
 (defun no-nils-in-termsp (terms)
   (declare (xargs :guard (pseudo-term-listp terms)))
   (if (endp terms)
       t
     (and (no-nils-in-termp (first terms))
          (no-nils-in-termsp (rest terms))))))

(defthm-flag-free-vars-in-term
  (defthm not-member-equal-of-nil-and-free-vars-in-term
    (implies (and (pseudo-termp term)
                  (no-nils-in-termp term))
             ;; This is weaker than (no-nils-in-termp term) because it doesn't
             ;; check lambda bodies:
             (not (member-equal nil (free-vars-in-term term))))
    :flag free-vars-in-term)
  (defthm not-member-equal-of-nil-and-free-vars-in-terms
    (implies (and (pseudo-term-listp terms)
                  (no-nils-in-termsp terms))
             (not (member-equal nil (free-vars-in-terms terms))))
    :flag free-vars-in-terms)
  :hints (("Goal" :expand ((expand-lambdas-in-term terms)
                           (FREE-VARS-IN-TERM TERM))
           :do-not '(generalize eliminate-destructors)
           :in-theory (e/d (expand-lambdas-in-term
                            empty-eval-of-fncall-args
                            free-vars-in-terms
                            lambdas-closed-in-termp)
                           (empty-eval-of-fncall-args-back)))))

(local
 (mutual-recursion
  ;; The whole point of this is to recur on a different alist in the lambda case
  (defund expand-lambdas-in-term-induct (term a)
    (declare (xargs :measure (acl2-count term))
             (irrelevant a))
    (if (or (variablep term)
            (fquotep term))
        term
      (let* ((args (fargs term))
             (args (expand-lambdas-in-terms-induct args a))
             (fn (ffn-symb term)))
        (if (flambdap fn)
            (let* ((lambda-body (expand-lambdas-in-term-induct (lambda-body fn)
                                                               (pairlis$ (lambda-formals fn) (empty-eval-list args a)) ;note this!
                                                               )))
              (sublis-var-simple (pairlis$ (lambda-formals fn) args) lambda-body))
          `(,fn ,@args)))))

  (defund expand-lambdas-in-terms-induct (terms a)
    (declare (xargs :measure (acl2-count terms))
             (irrelevant a))
    (if (endp terms)
        nil
      (cons (expand-lambdas-in-term-induct (first terms) a)
            (expand-lambdas-in-terms-induct (rest terms) a))))))

(local
 (make-flag expand-lambdas-in-term-induct))

(local
 (defthm-flag-expand-lambdas-in-term-induct
   (defthm expand-lambdas-in-term-induct-removal
     (equal (expand-lambdas-in-term-induct term a)
            (expand-lambdas-in-term term))
     :flag expand-lambdas-in-term-induct)
   (defthm expand-lambdas-in-terms-induct-removal
     (equal (expand-lambdas-in-terms-induct terms a)
            (expand-lambdas-in-terms terms))
     :flag expand-lambdas-in-terms-induct)
   :hints (("Goal" :in-theory (enable EXPAND-LAMBDAS-IN-TERM
                                      EXPAND-LAMBDAS-IN-TERMs
                                      EXPAND-LAMBDAS-IN-TERM-induct
                                      EXPAND-LAMBDAS-IN-TERMs-induct)))))

;; Correctness of expand-lambdas-in-term: The meaning of terms is preserved.
;; TODO: Can some assumptions be dropped?
(defthm-flag-expand-lambdas-in-term-induct
  (defthm expand-lambdas-in-term-correct
    (implies (and (pseudo-termp term)
                  (no-nils-in-termp term)
                  (lambdas-closed-in-termp term))
             (equal (empty-eval (expand-lambdas-in-term term) a)
                    (empty-eval term a)))
    :flag expand-lambdas-in-term-induct)
  (defthm expand-lambdas-in-terms-correct
    (implies (and (pseudo-term-listp terms)
                  (no-nils-in-termsp terms)
                  (lambdas-closed-in-termsp terms))
             (equal (empty-eval-list (expand-lambdas-in-terms terms) a)
                    (empty-eval-list terms a)))
    :flag expand-lambdas-in-terms-induct)
  :hints (("Goal" :expand ((expand-lambdas-in-term terms)
                           (free-vars-in-term term)
                           (lambdas-closed-in-termp term))
           :do-not '(generalize eliminate-destructors)
           :in-theory (e/d (expand-lambdas-in-term
                            empty-eval-of-fncall-args
                            free-vars-in-terms)
                           (empty-eval-of-fncall-args-back)))))
