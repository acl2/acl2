; Proofs about subst-var-deep
;
; Copyright (C) 2023-2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "subst-var-deep")
(include-book "non-trivial-formals")
(include-book "trivial-formals")
(include-book "no-nils-in-termp")
;(include-book "make-lambda-application-simple") ;rename, since make-lambda-term-simple is even simpler
(include-book "make-lambda-term-simple")
;(include-book "all-lambdas-serialized-in-termp")
(include-book "replace-corresponding-arg")
(include-book "kestrel/evaluators/empty-eval" :dir :system)
;(include-book "kestrel/alists-light/lookup-equal" :dir :system)
(include-book "kestrel/alists-light/map-lookup-equal" :dir :system)
(include-book "kestrel/alists-light/alists-equiv-on" :dir :system)
(include-book "lambdas-closed-in-termp")
(include-book "no-duplicate-lambda-formals-in-termp")
(include-book "make-lambda-terms-simple")
(local (include-book "filter-formals-and-actuals-proofs"))
(local (include-book "helpers"))
(local (include-book "empty-eval-helpers"))
(local (include-book "replace-corresponding-arg-proofs"))
(local (include-book "kestrel/lists-light/no-duplicatesp-equal" :dir :system))
(local (include-book "kestrel/alists-light/alistp" :dir :system))
(local (include-book "make-lambda-application-simple-proof"))
(local (include-book "kestrel/utilities/pseudo-termp" :dir :system))
(local (include-book "kestrel/lists-light/append" :dir :system))
(local (include-book "kestrel/lists-light/true-list-fix" :dir :system))
(local (include-book "kestrel/lists-light/intersection-equal" :dir :system))
(local (include-book "kestrel/lists-light/member-equal" :dir :system))
(local (include-book "kestrel/lists-light/subsetp-equal" :dir :system))
(local (include-book "kestrel/typed-lists-light/symbol-listp" :dir :system))
(local (include-book "kestrel/alists-light/pairlis-dollar" :dir :system))
(local (include-book "kestrel/alists-light/strip-cars" :dir :system))
(local (include-book "kestrel/alists-light/assoc-equal" :dir :system))
(local (include-book "kestrel/evaluators/empty-eval-theorems" :dir :system))

(local (in-theory (disable mv-nth)))


;; TODO: Clean up the proofs in this file, and separate them out.
;; TODO: Remove duplication between this file and subsrt-var-alt-proofs.lisp !

(defthm car-of-subst-var-deep-lst
  (equal (car (subst-var-deep-lst var replacement terms))
         (if (consp terms)
             (subst-var-deep var replacement (car terms))
           nil))
  :hints (("Goal" :expand (subst-var-deep-lst var replacement terms)
           :in-theory (enable subst-var-deep-lst))))

(defthm cdr-of-subst-var-deep-lst
  (equal (cdr (subst-var-deep-lst var replacement terms))
         (subst-var-deep-lst var replacement (cdr terms)))
  :hints (("Goal" :expand (subst-var-deep-lst var replacement terms)
           :in-theory (enable subst-var-deep-lst))))

(defthm subst-var-deep-when-symbolp
  (implies (symbolp term)
           (equal (subst-var-deep var replacement term)
                  (if (equal term var)
                      replacement
                    term)))
  :hints (("Goal" :in-theory (enable subst-var-deep))))

(local
 (defthm <=-of-len-of-non-trivial-formals-of-subst-var-deep-irrel
   (implies (and (not (member-equal var formals))
                 (symbol-listp formals))
            (<= (len (non-trivial-formals formals (subst-var-deep-lst var replacement args)))
                (len (non-trivial-formals formals args))))
   :rule-classes :linear
   :hints (("Goal" ; :expand (subst-var-deep var replacement (car args))
            :in-theory (enable non-trivial-formals
                               subst-var-deep-lst)))))

(local
 (defthm <=-of-len-of-non-trivial-formals-of-subst-var-deep-2
   (implies (and (member-equal var (non-trivial-formals formals args))
                 (no-duplicatesp-equal formals) ; ok?
                 (symbol-listp formals))
            (<= (len (non-trivial-formals formals (subst-var-deep-lst var replacement args)))
                (len (non-trivial-formals formals args))))
   :rule-classes :linear
   :hints (("Goal" ; :expand (subst-var-deep var replacement (car args))
            :in-theory (enable non-trivial-formals
                               subst-var-deep-lst)))))

     ;drop?
(local
 (defthm <=-of-len-of-non-trivial-formals-of-subst-var-deep-3
   (implies (and (not (member-equal var (trivial-formals formals args)))
;                 (no-duplicatesp-equal formals) ; ok?
                 (symbol-listp formals))
            (<= (len (non-trivial-formals formals (subst-var-deep-lst var replacement args)))
                (len (non-trivial-formals formals args))))
   :rule-classes :linear
   :hints (("Goal" ; :expand (subst-var-deep var replacement (car args))
            :in-theory (enable non-trivial-formals
                               trivial-formals
                               subst-var-deep-lst)))))

(defthm len-of-non-trivial-formals-of-replace-corresponding-arg-of-subst-var-deep-lst-linear
  (implies (symbol-listp formals)
           (<= (len (non-trivial-formals formals (replace-corresponding-arg var (subst-var-deep-lst var replacement args) var formals)))
               (len (non-trivial-formals formals args))))
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable replace-corresponding-arg non-trivial-formals subst-var-deep-lst))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(local (make-flag subst-var-deep))

;; subst-var-deep preserves closedness of lambdas.
(defthm-flag-subst-var-deep
  (defthm lambdas-closed-in-termp-of-subst-var-deep
    (implies (and (symbolp var)
                  (pseudo-termp replacement)
                  (lambdas-closed-in-termp replacement)
                  (pseudo-termp term)
                  (lambdas-closed-in-termp term))
             (lambdas-closed-in-termp (subst-var-deep var replacement term)))
    :flag subst-var-deep)
  (defthm lambdas-closed-in-termsp-of-subst-var-deep-lst
    (implies (and (symbolp var)
                  (pseudo-termp replacement)
                  (lambdas-closed-in-termp replacement)
                  (pseudo-term-listp terms)
                  (lambdas-closed-in-termsp terms))
             (lambdas-closed-in-termsp (subst-var-deep-lst var replacement terms)))
    :flag subst-var-deep-lst)
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (enable subst-var-deep
                              subst-var-deep-lst
                              lambdas-closed-in-termp))))


;gen?
(defthm-flag-subst-var-deep
  (defthm no-duplicate-lambda-formals-in-termp-of-subst-var-deep
    (implies (and (symbolp var)
                  (pseudo-termp replacement)
                  (no-duplicate-lambda-formals-in-termp replacement)
                  (pseudo-termp term)
                  (no-duplicate-lambda-formals-in-termp term))
             (no-duplicate-lambda-formals-in-termp (subst-var-deep var replacement term)))
    :flag subst-var-deep)
  (defthm no-duplicate-lambda-formals-in-termsp-of-subst-var-deep-lst
    (implies (and (symbolp var)
                  (pseudo-termp replacement)
                  (no-duplicate-lambda-formals-in-termp replacement)
                  (pseudo-term-listp terms)
                  (no-duplicate-lambda-formals-in-termsp terms))
             (no-duplicate-lambda-formals-in-termsp (subst-var-deep-lst var replacement terms)))
    :flag subst-var-deep-lst)
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (e/d (subst-var-deep
                            subst-var-deep-lst
                            pseudo-termp-when-symbolp
                            no-duplicate-lambda-formals-in-termp)
                           (pseudo-termp)))))



;; (defthm all-lambdas-serialized-in-termsp-of-mv-nth-1-of-filter-formals-and-actuals
;;   (implies (all-lambdas-serialized-in-termsp actuals)
;;            (all-lambdas-serialized-in-termsp (mv-nth 1 (filter-formals-and-actuals formals actuals formals-to-keep))))
;;   :hints (("Goal" :in-theory (enable filter-formals-and-actuals))))

;; (defthm all-lambdas-serialized-in-termsp-of-mv-nth-1-of-non-trivial-formals-and-args
;;   (implies (all-lambdas-serialized-in-termsp args)
;;            (all-lambdas-serialized-in-termsp (mv-nth 1 (non-trivial-formals-and-args formals args))))
;;   :hints (("Goal" :in-theory (enable non-trivial-formals-and-args))))


;; (defthm all-lambdas-serialized-in-termp-of-make-lambda-application-simple
;;   (implies (and (pseudo-termp body)
;;                 (symbol-listp formals)
;;                 (pseudo-term-listp actuals)
;;                 (equal (len formals) (len actuals))
;;                 (all-lambdas-serialized-in-termsp actuals)
;;                 (all-lambdas-serialized-in-termp body)
;;                 ;; move to conclusion?
;;                 (<= (len (non-trivial-formals formals actuals))
;;                       1))
;;            (all-lambdas-serialized-in-termp (make-lambda-application-simple formals actuals body)))
;;   :hints (("Goal" ; :induct (make-lambda-application-simple formals actuals body)
;;            :in-theory (e/d (make-lambda-application-simple) (mv-nth-0-of-filter-formals-and-actuals)))))

;; (defthm all-lambdas-serialized-in-termp-of-make-lambda-application-simple-strong
;;   (implies (and (pseudo-termp body)
;;                 (symbol-listp formals)
;;                 (pseudo-term-listp actuals)
;;                 (equal (len formals) (len actuals))
;;      ; move to conclusion, but some might get dropped
;;                 ;; move to conclusion? but some formals might get drpped
;;                 ;; (<= (len (non-trivial-formals formals actuals))
;;                 ;;     1)
;;                 )
;;            (equal (all-lambdas-serialized-in-termp (make-lambda-application-simple formals actuals body))
;;                   (and (<=
;;                         (len
;;                          (non-trivial-formals
;;                           (mv-nth 0 (filter-formals-and-actuals formals actuals (free-vars-in-term body)))
;;                           (mv-nth 1 (filter-formals-and-actuals formals actuals (free-vars-in-term body)))))
;;                         1)
;;                        (all-lambdas-serialized-in-termsp (mv-nth 1 (filter-formals-and-actuals formals actuals (free-vars-in-term body))))
;;                        (all-lambdas-serialized-in-termp body))))
;;   :hints (("Goal" ; :induct (make-lambda-application-simple formals actuals body)
;;            :in-theory (e/d (make-lambda-application-simple) (mv-nth-0-of-filter-formals-and-actuals)))))

;; (defthm all-lambdas-serialized-in-termsp-of-replace-corresponding-arg
;;   (implies (and (all-lambdas-serialized-in-termsp args)
;;                 (all-lambdas-serialized-in-termp new-arg))
;;            (all-lambdas-serialized-in-termsp (replace-corresponding-arg new-arg args formal formals)))
;;   :hints (("Goal" :in-theory (enable replace-corresponding-arg))))

;(local (defthm len-of-if (equal (len (if test tp ep)) (if test (len tp) (len ep)))))

;; (thm
;;  (implies (and (not (intersection-equal (free-vars-in-term replacement) formals))
;;                (member-equal var (trivial-formals formals args))
;;                (symbol-listp formals)
;;                )
;;           (<= (len (non-trivial-formals (non-trivial-formals formals args) (subst-var-deep-lst var replacement args)))
;;               (len (non-trivial-formals formals args))))
;;  :otf-flg t
;;  :hints (("Goal" :in-theory (enable non-trivial-formals trivial-formals (:d symbol-listp)))))
;; )

;; no longer true:
;;subst-var-deep cannot introduce an unserialized lambda (unlike sublis-var-simple).
;; (defthm-flag-subst-var-deep
;;   (defthm all-lambdas-serialized-in-termp-of-subst-var-deep
;;     (implies (and (symbolp var)
;;                   (pseudo-termp replacement)
;;                   (all-lambdas-serialized-in-termp replacement)
;;                   (pseudo-termp term)
;;                   (no-duplicate-lambda-formals-in-termp term)
;;                   (all-lambdas-serialized-in-termp term))
;;              (all-lambdas-serialized-in-termp (subst-var-deep var replacement term)))
;;     :flag subst-var-deep)
;;   (defthm all-lambdas-serialized-in-termsp-of-subst-var-deep-lst
;;     (implies (and (symbolp var)
;;                   (pseudo-termp replacement)
;;                   (all-lambdas-serialized-in-termp replacement)
;;                   (pseudo-term-listp terms)
;;                   (all-lambdas-serialized-in-termsp terms)
;;                   (no-duplicate-lambda-formals-in-termsp terms))
;;              (all-lambdas-serialized-in-termsp (subst-var-deep-lst var replacement terms)))
;;     :flag subst-var-deep-lst)
;;   :hints (("Goal" :do-not '(generalize eliminate-destructors)
;;            :expand ((all-lambdas-serialized-in-termp term)
;;                     (all-lambdas-serialized-in-termp (cons (car term) (subst-var-deep-lst var replacement (cdr term)))))
;;            :in-theory (e/d (subst-var-deep
;;                             subst-var-deep-lst
;;                             all-lambdas-serialized-in-termp
;;                             pseudo-termp-when-symbolp)
;;                            (pseudo-termp
;;                             no-duplicatesp-equal-of-non-trivial-formals ; why?
;;                             )))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm-flag-subst-var-deep
  (defthm no-nils-in-termp-of-subst-var-deep
    (implies (and (symbolp var)
                  var
                  (pseudo-termp replacement)
                  (no-nils-in-termp replacement)
                  (pseudo-termp term)
                  (no-duplicate-lambda-formals-in-termp term)
                  (no-nils-in-termp term))
             (no-nils-in-termp (subst-var-deep var replacement term)))
    :flag subst-var-deep)
  (defthm no-nils-in-termsp-of-subst-var-deep-lst
    (implies (and (symbolp var)
                  var
                  (pseudo-termp replacement)
                  (no-nils-in-termp replacement)
                  (pseudo-term-listp terms)
                  (no-nils-in-termsp terms)
                  (no-duplicate-lambda-formals-in-termsp terms))
             (no-nils-in-termsp (subst-var-deep-lst var replacement terms)))
    :flag subst-var-deep-lst)
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :expand ((no-nils-in-termp term)
                    (no-nils-in-termp (cons (car term) (subst-var-deep-lst var replacement (cdr term)))))
           :in-theory (e/d (subst-var-deep
                            subst-var-deep-lst
                            no-nils-in-termp
                            pseudo-termp-when-symbolp)
                           (pseudo-termp)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(local (in-theory (disable symbol-listp no-duplicatesp-equal)))

;; (defun EMPTY-EVAL-cdrs (alist a)
;;   (if (endp alist)
;;       nil
;;     (let ((pair (first alist)))
;;       (acons (car pair) (empty-eval (cdr pair) a)
;;              (EMPTY-EVAL-cdrs (rest alist) a)))))

;; ;; introduces EMPTY-EVAL-cdrs
;; (defthmd PAIRLIS$-of-empty-eval-list
;;  (equal (PAIRLIS$ keys (EMPTY-EVAL-LIST vals a))
;;         (EMPTY-EVAL-cdrs (pairlis$ keys vals) a))
;;  :hints (("Goal" :in-theory (enable pairlis$))))

;; (defthm alistp-of-empty-eval-cdrs
;;   (implies (alistp alist)
;;            (alistp (EMPTY-EVAL-cdrs alist a)))
;;   :hints (("Goal" :in-theory (enable EMPTY-EVAL-cdrs))))

;; (defthm strip-cars-of-empty-eval-cdrs
;;   (equal (strip-cars (EMPTY-EVAL-cdrs alist a))
;;          (strip-cars alist))
;;  :hints (("Goal" :in-theory (enable EMPTY-EVAL-cdrs))))

;; (defthm cdr-of-assoc-equal-of-empty-eval-cdrs
;;   (equal (cdr (assoc-equal key (empty-eval-cdrs alist a)))
;;          (empty-eval (cdr (assoc-equal key alist)) a))
;;   :hints (("Goal" :in-theory (enable assoc-equal))))

;; (defthmd lookup-equal-of-empty-eval-cdrs
;;   (equal (lookup-equal key (empty-eval-cdrs alist a))
;;          (empty-eval (lookup-equal key alist) a))
;;   :hints (("Goal" :in-theory (enable lookup-equal))))

;; (local (in-theory (enable lookup-equal-of-empty-eval-cdrs)))

;; (defthmd empty-eval-cdrs-of-pairlis$
;;   (implies (equal (len keys) (len vals))
;;            (equal (empty-eval-cdrs (pairlis$ keys vals) a)
;;                   (pairlis$ keys (empty-eval-list vals a))))
;;   :hints (("Goal" :in-theory (enable PAIRLIS$-of-empty-eval-list))))

;; (theory-invariant (incompatible (:rewrite PAIRLIS$-OF-EMPTY-EVAL-LIST) (:rewrite empty-eval-cdrs-of-pairlis$)))

;; (defthm ASSOC-EQUAL-of-EMPTY-EVAL-CDRS-iff
;;  (implies (alistp alist)
;;           (iff (ASSOC-EQUAL SOMEVAR (EMPTY-EVAL-CDRS alist a))
;;                (ASSOC-EQUAL SOMEVAR alist)))

;;  :hints (("Goal" :in-theory (enable empty-eval-cdrs assoc-equal))))

(defthm main.help.help
  (implies (and (member-eq somevar (free-vars-in-term body))
                (member-equal var (trivial-formals formals args))
                (pseudo-termp body)
                (pseudo-term-listp args)
                (no-nils-in-termp body)
                (symbol-listp formals)
                (no-duplicatesp-equal formals)
                ;; (not (member-eq nil formals))
                (subsetp-equal (free-vars-in-term body) formals))
           (equal (lookup-equal somevar
                                (cons
                                 (cons var (empty-eval replacement a))
                                 (append
                                  (pairlis$
                                   (non-trivial-formals formals args)
                                   (empty-eval-list (mv-nth '1
                                                            (non-trivial-formals-and-args formals args))
                                                    (cons (cons var (empty-eval replacement a))
                                                          a)))
                                  a)))
                  (lookup-equal somevar
                                (pairlis$ formals
                                          (empty-eval-list args
                                                           (cons (cons var (empty-eval replacement a))
                                                                 a))))))
  :hints (("Goal" :in-theory (e/d (LOOKUP-EQUAL-OF-APPEND cdr-of-assoc-equal-becomes-lookup-equal lookup-equal-of-pairlis$-of-empty-eval-list)
                                  (EMPTY-EVAL-OF-LOOKUP-EQUAL-OF-PAIRLIS$)) ; todo:looped
           :do-not '(preprocess generalize eliminate-destructors))))

;; (EMPTY-EVAL VAR (CONS (CONS VAR (EMPTY-EVAL REPLACEMENT A)) A))

;; for the proof, consider 3 cases: var, other trivial formal, non-trivial formal
(defthm main.help
  (implies (and (member-equal var (trivial-formals formals args))
                (pseudo-termp body)
                (pseudo-term-listp args)
                (no-nils-in-termp body)
                (symbol-listp formals)
                (no-duplicatesp-equal formals)
                ;(not (member-eq nil formals)) ; new
                (subsetp-equal (free-vars-in-term body) formals))
           (alists-equiv-on
            (free-vars-in-term body)
            (cons
             (cons var (empty-eval replacement a))
             (append
              (pairlis$
               (non-trivial-formals formals args)
               (empty-eval-list (mv-nth '1
                                        (non-trivial-formals-and-args formals args))
                                (cons (cons var (empty-eval replacement a))
                                      a)))
              a))
            (pairlis$ formals
                      (empty-eval-list args
                                       (cons (cons var (empty-eval replacement a))
                                             a)))))

  :hints (;; (and stable-under-simplificationp `(:in-theory (e/d (alists-equiv-on-when-agree-on-bad-guy
          ;;                                                      lookup-equal-of-append)
          ;;                                                     (EMPTY-EVAL-OF-LOOKUP-EQUAL-OF-PAIRLIS$
          ;;                                                      ))))
          ("Goal"
           :use ((:instance  alists-equiv-on-when-agree-on-bad-guy
                             (keys  (free-vars-in-term body))
                             (a1             (cons
                                              (cons var (empty-eval replacement a))
                                              (append
                                               (pairlis$
                                                (non-trivial-formals formals args)
                                                (empty-eval-list (mv-nth '1
                                                                         (non-trivial-formals-and-args formals args))
                                                                 (cons (cons var (empty-eval replacement a))
                                                                       a)))
                                               a)))
                             (a2
                              (pairlis$ formals
                                        (empty-eval-list args
                                                         (cons (cons var (empty-eval replacement a))
                                                               a)))))
                 (:instance main.help.help
                            (somevar (BAD-GUY-FOR-ALISTS-EQUIV-ON
                                      (FREE-VARS-IN-TERM BODY)
                                      (cons
                                       (cons var (empty-eval replacement a))
                                       (append
                                        (pairlis$
                                         (non-trivial-formals formals args)
                                         (empty-eval-list (mv-nth '1
                                                                  (non-trivial-formals-and-args formals args))
                                                          (cons (cons var (empty-eval replacement a))
                                                                a)))
                                        a))
                                      (pairlis$ formals
                                        (empty-eval-list args
                                                         (cons (cons var (empty-eval replacement a))
                                                               a)))))))
           :in-theory (e/d (;alists-equiv-on-when-agree-on-bad-guy
                            ;; lookup-equal-of-append
                            )
                           (;STRIP-CARS-OF-PAIRLIS$
                            EMPTY-EVAL-OF-LOOKUP-EQUAL-OF-PAIRLIS$ ;bad
                            member-equal
;                            LOOKUP-EQUAL-OF-EMPTY-EVAL-CDRS
                            ALISTS-EQUIV-ON-OF-APPEND-ARG1
                            ALISTS-EQUIV-ON-OF-CONS-ARG2
                            main.help.help)))))


;; ;; for the proof, consider 3 cases: var, other trivial formal, non-trivial formal
(defthm main
  (implies (and (member-equal var (trivial-formals formals args))
                (pseudo-termp body)
                (no-nils-in-termp body)
                (pseudo-term-listp args)
                (symbol-listp formals)
                (no-duplicatesp-equal formals)
                ;;(not (member-eq nil formals))
                (subsetp-equal (free-vars-in-term body) formals))
           (equal (empty-eval
                   body
                   (cons
                    (cons var (empty-eval replacement a))
                    (append (pairlis$ (non-trivial-formals formals args)
                                      (empty-eval-list
                                       (mv-nth 1 (non-trivial-formals-and-args formals args))
                                       (cons (cons var (empty-eval replacement a))
                                             a)))
                            a)))
                  (empty-eval
                   body
                   (pairlis$ formals
                             (empty-eval-list args
                                              (cons (cons var (empty-eval replacement a))
                                                    a))))))
  :hints (("Goal" :use main.help
           :in-theory (disable main.help))))

;(theory-invariant (incompatible (:rewrite CDR-OF-ASSOC-EQUAL-OF-EMPTY-EVAL-CDRS ) (:rewrite EMPTY-EVAL-OF-CDR-OF-ASSOC-EQUAL)))

;; The whole point of this is to recur on a different alist in the lambda case
(mutual-recursion
 ;; Replace VAR with REPLACEMENT in TERM.
 (defund induct-subst-var-deep (var replacement term a)
   (declare (xargs :measure (acl2-count term))
            (irrelevant a)
            )
   (if (variablep term)
       (if (equal term var)
            replacement
         term)
     (if (fquotep term)
         term
       (let ((fn (ffn-symb term)))
         (if (flambdap fn)
             ;; Lambda application:
             (b* ((formals (lambda-formals fn))
                    (body (lambda-body fn))
                    (args (fargs term))
                    ;;(non-trivial-formals (non-trivial-formals formals args))
                    ;;(trivial-formals (trivial-formals formals args))
                    ((mv non-trivial-formals non-trivial-args)
                     (non-trivial-formals-and-args formals args))
                    )
               (if (or (not (member-eq var formals)) ; no need to go into the body
                       (member-eq var non-trivial-formals) ; can't substitute in the body because the var is shadowed there
                       (intersection-eq (free-vars-in-term replacement) non-trivial-formals) ; can't subst in the body because the replacement term has a different meaning
                       (not (mbt (equal (len formals) (len args)))) ; for termination
                       )
                   ;; Replace in the args only:
                   (cons-with-hint fn (induct-subst-var-deep-lst var replacement args a) term)
                 ;; Var is a trivial formal.  We could just substitute in its actual, but instead we  go into the lambda-body:
                 ;; todo: just remove the formal and arg for x and call something simpler here?
                 (make-lambda-application-simple non-trivial-formals
                                                 ;; Fixup all the non-trivial args (trivial args other than var are not affected by the replacement of var)
                                                 (induct-subst-var-deep-lst var replacement non-trivial-args a)
                                                 (induct-subst-var-deep var replacement body
                                                                (append (pairlis$ non-trivial-formals
                                                                                           (empty-eval-list (induct-subst-var-deep-lst var replacement non-trivial-args a) a))
                                                                        a)))))
           ;; Not a lambda application:
           (cons ;try fcons-term
            fn
            (induct-subst-var-deep-lst var replacement (fargs term) a)))))))

 (defund induct-subst-var-deep-lst (var replacement terms a)
   (declare (xargs :measure (acl2-count terms))
            (irrelevant a))
   (if (endp terms)
       nil
     (cons (induct-subst-var-deep var replacement (first terms) a)
           (induct-subst-var-deep-lst var replacement (rest terms) a)))))

(local (make-flag induct-subst-var-deep))

;; The induct function is equal to the main function (ignoring the A argument);
(local
 (defthm-flag-induct-subst-var-deep
   (defthm subst-var-deep-induct-removal
     (equal (induct-subst-var-deep var replacement term a)
            (subst-var-deep var replacement term))
     :flag induct-subst-var-deep)
   (defthm subst-var-deep-lst-induct-removal
     (equal (induct-subst-var-deep-lst var replacement terms a)
            (subst-var-deep-lst var replacement terms))
     :flag induct-subst-var-deep-lst)
   :hints (("Goal" :in-theory (enable subst-var-deep
                                      subst-var-deep-lst
                                      induct-subst-var-deep
                                      induct-subst-var-deep-lst)))))

;; Correctness of subst-var-deep: it preserves the meaning of terms.
(defthm-flag-induct-subst-var-deep
  (defthm subst-var-deep-correct
    (implies (and (symbolp var)
                  var
                  (pseudo-termp replacement)
                  (no-nils-in-termp replacement)
                  (pseudo-termp term)
                  (lambdas-closed-in-termp term)
                  (no-duplicate-lambda-formals-in-termp term)
                  (no-nils-in-termp term)
                  (alistp a))
             (equal (empty-eval (subst-var-deep var replacement term) a)
                    (empty-eval (make-lambda-term-simple (list var) (list replacement) term) a)))
    :flag induct-subst-var-deep)
  (defthm subst-var-deep-lst-correct
    (implies (and (symbolp var)
                  var
                  (pseudo-termp replacement)
                  (no-nils-in-termp replacement)
                  (pseudo-term-listp terms)
                  (lambdas-closed-in-termsp terms)
                  (no-duplicate-lambda-formals-in-termsp terms)
                  (no-nils-in-termsp terms)
                  (alistp a))
             (equal (empty-eval-list (subst-var-deep-lst var replacement terms) a)
                    (empty-eval-list (make-lambda-terms-simple (list var) (list replacement) terms) a)))
    :flag induct-subst-var-deep-lst)
  :hints (("subgoal *1/4"  :use (:instance main (body (lambda-body (car term))) (formals (lambda-formals (car term))) (args (fargs term)))
           :in-theory (e/d (subst-var-deep
                            subst-var-deep-lst
                            make-lambda-terms-simple
                            ;;make-lambda-term-simple
                            empty-eval-of-fncall-args
                            empty-eval-of-cdr-of-assoc-equal
                            lookup-equal ; todo
                            pseudo-termp-when-symbolp
                            no-nils-in-termp)
                           (pseudo-termp
                            pairlis$
                            ;PAIRLIS$-OF-EMPTY-EVAL-LIST
                            set-difference-equal
                            empty-eval-of-fncall-args-back
                            ;CDR-OF-ASSOC-EQUAL-OF-EMPTY-EVAL-CDRS
                            )))
          ("Goal" :expand (PSEUDO-TERMP TERM)
           :do-not '(generalize eliminate-destructors)
           :in-theory (e/d (subst-var-deep
                            subst-var-deep-lst
                            make-lambda-terms-simple
                            ;;make-lambda-term-simple
                            empty-eval-of-fncall-args
                            empty-eval-of-cdr-of-assoc-equal
                            lookup-equal ; todo
                            pseudo-termp-when-symbolp
                            no-nils-in-termp)
                           (pseudo-termp
                            pairlis$
                            ;PAIRLIS$-OF-EMPTY-EVAL-LIST
                            set-difference-equal
                            empty-eval-of-fncall-args-back
                            ;CDR-OF-ASSOC-EQUAL-OF-EMPTY-EVAL-CDRS
                            )))))
