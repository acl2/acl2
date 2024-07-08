; Proofs about subst-var-alt
;
; Copyright (C) 2023 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "subst-var-alt")
(include-book "non-trivial-formals")
(include-book "trivial-formals")
(include-book "no-nils-in-termp")
;(include-book "make-lambda-application-simple") ;rename, since make-lambda-term-simple is even simpler
(include-book "make-lambda-term-simple")
(include-book "all-lambdas-serialized-in-termp")
(include-book "replace-corresponding-arg")
(include-book "kestrel/evaluators/empty-eval" :dir :system) ; move to a proofs book
;(include-book "kestrel/alists-light/lookup-equal" :dir :system)
(include-book "kestrel/alists-light/map-lookup-equal" :dir :system)
(include-book "kestrel/alists-light/alists-equiv-on" :dir :system)
(include-book "lambdas-closed-in-termp")
(include-book "no-duplicate-lambda-formals-in-termp")
(include-book "make-lambda-terms-simple")
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
(local (include-book "kestrel/alists-light/pairlis-dollar" :dir :system))
(local (include-book "kestrel/evaluators/empty-eval-theorems" :dir :system))

(local (in-theory (disable mv-nth)))

;; TODO: Clean up the proofs in this file, and separate them out.

(local
 (defthm lambdas-closed-in-termp-of-cdr-of-assoc-equal
   (implies (lambdas-closed-in-termsp (strip-cdrs alist))
            (lambdas-closed-in-termp (cdr (assoc-equal term alist))))
   :hints (("Goal" :in-theory (enable assoc-equal)))))

(defthm lambdas-closed-in-termsp-of-replace-corresponding-arg
  (implies (and (lambdas-closed-in-termsp args)
                (lambdas-closed-in-termp new-arg))
           (lambdas-closed-in-termsp (replace-corresponding-arg new-arg args formal formals)))
  :hints (("Goal" :in-theory (enable replace-corresponding-arg))))

(defthm empty-eval-list-of-replace-corresponding-arg
  (equal (empty-eval-list (replace-corresponding-arg new-arg args formal formals) a)
         (replace-corresponding-arg (empty-eval new-arg a) (empty-eval-list args a) formal formals))
  :hints (("Goal" :in-theory (enable replace-corresponding-arg))))

(defthm no-nils-in-termsp-of-replace-corresponding-arg
  (implies (and (no-nils-in-termsp args)
                (no-nils-in-termp new-arg))
           (no-nils-in-termsp (replace-corresponding-arg new-arg args formal formals)))
  :hints (("Goal" :in-theory (enable replace-corresponding-arg))))

(defthm lambdas-closed-in-termsp-of-mv-nth-1-of-non-trivial-formals-and-args
  (implies (lambdas-closed-in-termsp args)
           (lambdas-closed-in-termsp (mv-nth 1 (non-trivial-formals-and-args formals args))))
  :hints (("Goal" :in-theory (enable non-trivial-formals-and-args))))

;; End of library material

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; subst-var-alt preserves closedness of lambdas.
(defthm-flag-subst-var-alt
  (defthm lambdas-closed-in-termp-of-subst-var-alt
    (implies (and (symbolp var)
                  (pseudo-termp replacement)
                  (lambdas-closed-in-termp replacement)
                  (pseudo-termp term)
                  (lambdas-closed-in-termp term))
             (lambdas-closed-in-termp (subst-var-alt var replacement term)))
    :flag subst-var-alt)
  (defthm lambdas-closed-in-termsp-of-subst-var-alt-lst
    (implies (and (symbolp var)
                  (pseudo-termp replacement)
                  (lambdas-closed-in-termp replacement)
                  (pseudo-term-listp terms)
                  (lambdas-closed-in-termsp terms))
             (lambdas-closed-in-termsp (subst-var-alt-lst var replacement terms)))
    :flag subst-var-alt-lst)
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (enable subst-var-alt
                              subst-var-alt-lst
                              lambdas-closed-in-termp))))

(defthm subst-var-alt-when-symbolp
  (implies (symbolp term)
           (equal (subst-var-alt var replacement term)
                  (if (equal term var)
                      replacement
                    term)))
  :hints (("Goal" :in-theory (enable subst-var-alt))))

(local
 (defthm <=-of-len-of-non-trivial-formals-of-subst-var-alt-irrel
   (implies (and (not (member-equal var formals))
                 (symbol-listp formals))
            (<= (len (non-trivial-formals formals (subst-var-alt-lst var replacement args)))
                (len (non-trivial-formals formals args))))
   :rule-classes :linear
   :hints (("Goal" ; :expand (subst-var-alt var replacement (car args))
            :in-theory (enable non-trivial-formals
                               subst-var-alt-lst)))))

(local
 (defthm <=-of-len-of-non-trivial-formals-of-subst-var-alt-2
   (implies (and (member-equal var (non-trivial-formals formals args))
                 (no-duplicatesp-equal formals) ; ok?
                 (symbol-listp formals))
            (<= (len (non-trivial-formals formals (subst-var-alt-lst var replacement args)))
                (len (non-trivial-formals formals args))))
   :rule-classes :linear
   :hints (("Goal" ; :expand (subst-var-alt var replacement (car args))
            :in-theory (enable non-trivial-formals
                               subst-var-alt-lst)))))

     ;drop?
(local
 (defthm <=-of-len-of-non-trivial-formals-of-subst-var-alt-3
   (implies (and (not (member-equal var (trivial-formals formals args)))
;                 (no-duplicatesp-equal formals) ; ok?
                 (symbol-listp formals))
            (<= (len (non-trivial-formals formals (subst-var-alt-lst var replacement args)))
                (len (non-trivial-formals formals args))))
   :rule-classes :linear
   :hints (("Goal" ; :expand (subst-var-alt var replacement (car args))
            :in-theory (enable non-trivial-formals
                               trivial-formals
                               subst-var-alt-lst)))))

(defthm all-lambdas-serialized-in-termsp-of-mv-nth-1-of-filter-formals-and-actuals
  (implies (all-lambdas-serialized-in-termsp actuals)
           (all-lambdas-serialized-in-termsp (mv-nth 1 (filter-formals-and-actuals formals actuals formals-to-keep))))
  :hints (("Goal" :in-theory (enable filter-formals-and-actuals))))

(defthm all-lambdas-serialized-in-termsp-of-mv-nth-1-of-non-trivial-formals-and-args
  (implies (all-lambdas-serialized-in-termsp args)
           (all-lambdas-serialized-in-termsp (mv-nth 1 (non-trivial-formals-and-args formals args))))
  :hints (("Goal" :in-theory (enable non-trivial-formals-and-args))))

(defthm mv-nth-0-of-non-trivial-formals-and-args
  (equal (mv-nth 0 (non-trivial-formals-and-args formals args))
         (non-trivial-formals formals args))
  :hints (("Goal" :in-theory (enable non-trivial-formals-and-args
                                     non-trivial-formals))))

(defthm formals-get-shorter ;rename
 (implies
  (and
   (symbol-listp formals)
   (pseudo-term-listp actuals)
   (equal (len formals) (len actuals)))
  (<=
   (len
    (non-trivial-formals
     (mv-nth 0 (filter-formals-and-actuals formals actuals formals-to-keep))
     (mv-nth 1 (filter-formals-and-actuals formals actuals formals-to-keep))))
   (len (non-trivial-formals formals actuals))))
 :rule-classes :linear
 :hints (("Goal" :in-theory (enable non-trivial-formals filter-formals-and-actuals))))

(defthm filter-formals-and-actuals-of-nil-arg1
  (equal (filter-formals-and-actuals nil actuals formals-to-keep)
         (mv nil nil))
  :hints (("Goal" :in-theory (enable filter-formals-and-actuals))))

(defthm all-lambdas-serialized-in-termp-of-make-lambda-application-simple
  (implies (and (pseudo-termp body)
                (symbol-listp formals)
                (pseudo-term-listp actuals)
                (equal (len formals) (len actuals))
                (all-lambdas-serialized-in-termsp actuals)
                (all-lambdas-serialized-in-termp body)
                ;; move to conclusion?
                (<= (len (non-trivial-formals formals actuals))
                      1))
           (all-lambdas-serialized-in-termp (make-lambda-application-simple formals actuals body)))
  :hints (("Goal" ; :induct (make-lambda-application-simple formals actuals body)
           :in-theory (e/d (make-lambda-application-simple) (mv-nth-0-of-filter-formals-and-actuals)))))

(defthm all-lambdas-serialized-in-termp-of-make-lambda-application-simple-strong
  (implies (and (pseudo-termp body)
                (symbol-listp formals)
                (pseudo-term-listp actuals)
                (equal (len formals) (len actuals))
     ; move to conclusion, but some might get dropped
                ;; move to conclusion? but some formals might get drpped
                ;; (<= (len (non-trivial-formals formals actuals))
                ;;     1)
                )
           (equal (all-lambdas-serialized-in-termp (make-lambda-application-simple formals actuals body))
                  (and (<=
                        (len
                         (non-trivial-formals
                          (mv-nth 0 (filter-formals-and-actuals formals actuals (free-vars-in-term body)))
                          (mv-nth 1 (filter-formals-and-actuals formals actuals (free-vars-in-term body)))))
                        1)
                       (all-lambdas-serialized-in-termsp (mv-nth 1 (filter-formals-and-actuals formals actuals (free-vars-in-term body))))
                       (all-lambdas-serialized-in-termp body))))
  :hints (("Goal" ; :induct (make-lambda-application-simple formals actuals body)
           :in-theory (e/d (make-lambda-application-simple) (mv-nth-0-of-filter-formals-and-actuals)))))

(defthm no-duplicate-lambda-formals-in-termsp-of-mv-nth-1-of-non-trivial-formals-and-args
  (implies (no-duplicate-lambda-formals-in-termsp args)
           (no-duplicate-lambda-formals-in-termsp (mv-nth 1 (non-trivial-formals-and-args formals args))))
  :hints (("Goal" :in-theory (enable non-trivial-formals-and-args))))

(defthm not-member-equal-of-trivial-formals-when-member-equal-of-non-trivial-formals
  (implies (and (member-equal var (non-trivial-formals formals args))
                (no-duplicatesp-equal formals))
           (not (member-equal var (trivial-formals formals args))))
  :hints (("Goal" :in-theory (enable trivial-formals non-trivial-formals))))

(defthm member-equal-of-trivial-formals-when-not-member-equal-of-non-trivial-formals
  (implies (and (not (member-equal var (non-trivial-formals formals args)))
                (no-duplicatesp-equal formals)
                (member-equal var formals))
           (member-equal var (trivial-formals formals args)))
  :hints (("Goal" :in-theory (enable trivial-formals non-trivial-formals))))

(defthm member-equal-of-non-trivial-formals-becomes-not-member-equal-of-non-trivial-formals
  (implies (and  (no-duplicatesp-equal formals)
                 (member-equal var formals))
           (iff (member-equal var (non-trivial-formals formals args))
                (not (member-equal var (trivial-formals formals args)))))
  :hints (("Goal" :in-theory (enable trivial-formals non-trivial-formals))))

(defthm all-lambdas-serialized-in-termsp-of-replace-corresponding-arg
  (implies (and (all-lambdas-serialized-in-termsp args)
                (all-lambdas-serialized-in-termp new-arg))
           (all-lambdas-serialized-in-termsp (replace-corresponding-arg new-arg args formal formals)))
  :hints (("Goal" :in-theory (enable replace-corresponding-arg))))

     ;drop?
(defthm len-of-non-trivial-formals-of-replace-corresponding-arg-linear
  (<= (len (non-trivial-formals formals (replace-corresponding-arg var args var formals)))
      (len (non-trivial-formals formals args)))
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable replace-corresponding-arg non-trivial-formals))))

(defthm len-of-non-trivial-formals-of-replace-corresponding-arg-of-subst-var-alt-lst-linear
  (implies (symbol-listp formals)
           (<= (len (non-trivial-formals formals (replace-corresponding-arg var (subst-var-alt-lst var replacement args) var formals)))
               (len (non-trivial-formals formals args))))
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable replace-corresponding-arg non-trivial-formals subst-var-alt-lst))))

(local (defthm len-of-if (equal (len (if test tp ep)) (if test (len tp) (len ep)))))

;; (thm
;;  (implies (and (not (intersection-equal (free-vars-in-term replacement) formals))
;;                (member-equal var (trivial-formals formals args))
;;                (symbol-listp formals)
;;                )
;;           (<= (len (non-trivial-formals (non-trivial-formals formals args) (subst-var-alt-lst var replacement args)))
;;               (len (non-trivial-formals formals args))))
;;  :otf-flg t
;;  :hints (("Goal" :in-theory (enable non-trivial-formals trivial-formals (:d symbol-listp)))))
;; )

;; subst-var-alt cannot introduce an unserialized lambda (unlike sublis-var-simple).
(defthm-flag-subst-var-alt
  (defthm all-lambdas-serialized-in-termp-of-subst-var-alt
    (implies (and (symbolp var)
                  (pseudo-termp replacement)
                  (all-lambdas-serialized-in-termp replacement)
                  (pseudo-termp term)
                  (no-duplicate-lambda-formals-in-termp term)
                  (all-lambdas-serialized-in-termp term))
             (all-lambdas-serialized-in-termp (subst-var-alt var replacement term)))
    :flag subst-var-alt)
  (defthm all-lambdas-serialized-in-termsp-of-subst-var-alt-lst
    (implies (and (symbolp var)
                  (pseudo-termp replacement)
                  (all-lambdas-serialized-in-termp replacement)
                  (pseudo-term-listp terms)
                  (all-lambdas-serialized-in-termsp terms)
                  (no-duplicate-lambda-formals-in-termsp terms))
             (all-lambdas-serialized-in-termsp (subst-var-alt-lst var replacement terms)))
    :flag subst-var-alt-lst)
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :expand ((all-lambdas-serialized-in-termp term)
                    (all-lambdas-serialized-in-termp (cons (car term) (subst-var-alt-lst var replacement (cdr term)))))
           :in-theory (e/d (subst-var-alt
                            subst-var-alt-lst
                            all-lambdas-serialized-in-termp
                            pseudo-termp-when-symbolp)
                           (pseudo-termp)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm no-nils-in-termsp-of-mv-nth-1-of-filter-formals-and-actuals
  (implies (and (no-nils-in-termsp actuals)
                (equal (len formals) (len actuals)))
           (no-nils-in-termsp (mv-nth 1 (filter-formals-and-actuals formals actuals formals-to-keep))))
  :hints (("Goal" :in-theory (enable filter-formals-and-actuals))))

(defthm no-nils-in-termsp-of-mv-nth-1-of-non-trivial-formals-and-args
  (implies (and (no-nils-in-termsp args)
                (equal (len formals) (len args)))
           (no-nils-in-termsp (mv-nth 1 (non-trivial-formals-and-args formals args))))
  :hints (("Goal" :in-theory (enable non-trivial-formals-and-args))))

     ;move
(defthm no-nils-in-termp-of-map-lookup-equal
  (implies (and (member-equal key (strip-cars alist))
                (no-nils-in-termsp (strip-cdrs alist))
                )
           (no-nils-in-termp (lookup-equal key alist)))
  :hints (("Goal" :in-theory (enable lookup-equal))))

     ;move
(defthm no-nils-in-termsp-of-map-lookup-equal
  (implies (and (subsetp-equal keys (strip-cars alist))
                (no-nils-in-termsp (strip-cdrs alist))
                )
           (no-nils-in-termsp (map-lookup-equal keys alist)))
  :hints (("Goal" :in-theory (enable map-lookup-equal))))

(defthm-flag-subst-var-alt
  (defthm no-nils-in-termp-of-subst-var-alt
    (implies (and (symbolp var)
                  var
                  (pseudo-termp replacement)
                  (no-nils-in-termp replacement)
                  (pseudo-termp term)
                  (no-duplicate-lambda-formals-in-termp term)
                  (no-nils-in-termp term))
             (no-nils-in-termp (subst-var-alt var replacement term)))
    :flag subst-var-alt)
  (defthm no-nils-in-termsp-of-subst-var-alt-lst
    (implies (and (symbolp var)
                  var
                  (pseudo-termp replacement)
                  (no-nils-in-termp replacement)
                  (pseudo-term-listp terms)
                  (no-nils-in-termsp terms)
                  (no-duplicate-lambda-formals-in-termsp terms))
             (no-nils-in-termsp (subst-var-alt-lst var replacement terms)))
    :flag subst-var-alt-lst)
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :expand ((no-nils-in-termp term)
                    (no-nils-in-termp (cons (car term) (subst-var-alt-lst var replacement (cdr term)))))
           :in-theory (e/d (subst-var-alt
                            subst-var-alt-lst
                            no-nils-in-termp
                            pseudo-termp-when-symbolp)
                           (pseudo-termp)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


;; true for any eval
(defthm empty-eval-list-of-kwote-lst
  (equal (empty-eval-list (kwote-lst vals) a)
         (true-list-fix vals)))

;; The whole point of this is to recur on a different alist in the lambda case
(mutual-recursion
 ;; Replace VAR with REPLACEMENT in TERM.
 (defund induct-subst-var-alt (var replacement term a)
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
                       )
                   ;;(not (member-eq var trivial-formals))
                   ;; Replace in the args only:
                   (cons ;try fcons-term
                    fn
                    (induct-subst-var-alt-lst var replacement args a))
                 ;; Var is a trivial formal.  Avoid making its formal non-trivial:
                 (if (or (intersection-eq (free-vars-in-term replacement)
                                          non-trivial-formals)
                         (not (mbt (equal (len formals) (len args)))))
                     ;; Possible clash, so be conservative: just wrap a binding of var around the term:
                     (make-lambda-application-simple (list var) (list replacement) term)
                   ;; No clash, so we can move into the body:
                   (make-lambda-application-simple non-trivial-formals
                                                   ;; Fixup all the non-trivial args (trivial args other than var are not affected by the subst)
                                                   (induct-subst-var-alt-lst var replacement non-trivial-args a)
                                                   (induct-subst-var-alt var replacement body
                                                                          ;note this!:
                                                                         (append (pairlis$ non-trivial-formals
                                                                                           (empty-eval-list (induct-subst-var-alt-lst var replacement non-trivial-args a) a))
                                                                                 a))))))
           ;; Not a lambda application:
           (cons ;try fcons-term
            fn
            (induct-subst-var-alt-lst var replacement (fargs term) a)))))))

 (defund induct-subst-var-alt-lst (var replacement terms a)
   (declare (xargs :measure (acl2-count terms))
            (irrelevant a))
   (if (endp terms)
       nil
     (cons (induct-subst-var-alt var replacement (first terms) a)
           (induct-subst-var-alt-lst var replacement (rest terms) a)))))

(local (make-flag induct-subst-var-alt))

;true of any evalauator
(defthm car-of-empty-eval-list
  (equal (car (empty-eval-list terms a))
         (empty-eval (car terms) a)))

(defthm cdr-of-assoc-equal-of-pairlis$-of-empty-eval-list-when-member-equal-of-trivial-formals
  (implies (and (member-equal var (trivial-formals formals args))
     ;               (member-equal var formals)  ;drop?
     ;              (symbol-listp formals)
                (no-duplicatesp-equal formals)
                var
                (symbolp var))
           (equal (cdr (assoc-equal var (pairlis$ formals (empty-eval-list args a))))
                  (cdr (assoc-equal var a)) ; (empty-eval var a)
                  ))
  :hints (("Goal" :in-theory (enable trivial-formals pairlis$))))

;; slight rephrasing of the above
(defthm cdr-of-assoc-equal-of-pairlis$-of-empty-eval-list-when-not-member-equal-of-non-trivial-formals
  (implies (and (not (member-equal var (non-trivial-formals formals args)))
                (member-equal var formals)
     ;              (symbol-listp formals)
                (no-duplicatesp-equal formals)
                var
                (symbolp var))
           (equal (cdr (assoc-equal var (pairlis$ formals (empty-eval-list args a))))
                  (cdr (assoc-equal var a)) ; (empty-eval var a)
                  ))
  :hints (("Goal" :in-theory (enable trivial-formals pairlis$))))

(defthm helper1
  (implies (and (not (intersection-equal vars (non-trivial-formals formals args)))
                (no-duplicatesp-equal formals)
                (symbol-listp formals)
                (symbol-listp vars)
                (not (member-equal nil vars)))
           (alists-equiv-on vars
                            (append (pairlis$ formals (empty-eval-list args a)) a)
                            a))
  :hints (("Goal" :in-theory (enable alists-equiv-on symbol-listp intersection-equal))))

(local (in-theory (disable symbol-listp no-duplicatesp-equal)))

(defthm helper2
  (implies (and (not (intersection-equal (free-vars-in-term replacement) (non-trivial-formals formals args)))
                (no-duplicatesp-equal formals)
                (symbol-listp formals)
                (pseudo-termp replacement)
                (no-nils-in-termp replacement))
           (equal (empty-eval replacement (append (pairlis$ formals (empty-eval-list args a)) a))
                  (empty-eval replacement a)))
  :hints (("Goal" :in-theory (disable alists-equiv-on-of-append-arg1))))


(local
 (defthm-flag-induct-subst-var-alt
   (defthm subst-var-alt-induct-removal
     (equal (induct-subst-var-alt var replacement term a)
            (subst-var-alt var replacement term))
     :flag induct-subst-var-alt)
   (defthm subst-var-alt-lst-induct-removal
     (equal (induct-subst-var-alt-lst var replacement terms a)
            (subst-var-alt-lst var replacement terms))
     :flag induct-subst-var-alt-lst)
   :hints (("Goal" :in-theory (enable subst-var-alt
                                      subst-var-alt-lst
                                      induct-subst-var-alt
                                      induct-subst-var-alt-lst)))))

(defthm no-duplicatesp-equal-of-non-trivial-formals
  (implies (no-duplicatesp-equal formals)
           (no-duplicatesp-equal (non-trivial-formals formals args)))
  :hints (("Goal" :in-theory (enable non-trivial-formals no-duplicatesp-equal))))

     ;dup
(defthm empty-eval-of-append-irrel-arg1
  (implies (and (not (intersection-equal (free-vars-in-term term) (strip-cars a1)))
                (alistp a1)
                (pseudo-termp term))
           (equal (empty-eval term (append a1 a2))
                  (empty-eval term a2)))
  :hints (("Goal" :in-theory (enable append subsetp-equal))))

     ;todo: nested induction
(defthmd alists-equiv-on-of-cons-arg2-fw
  (implies (if (member-equal (car pair) keys)
               (and (equal (cdr pair) (cdr (assoc-equal (car pair) a2)))
                    (alists-equiv-on (remove-equal (car pair) keys) a1 a2))
             (alists-equiv-on keys a1 a2))
           (alists-equiv-on keys (cons pair a1) a2))
  :hints (("Goal" :in-theory (enable alists-equiv-on remove-equal))))

(defthmd alists-equiv-on-of-cons-arg2-back
  (implies (alists-equiv-on keys (cons pair a1) a2)
           (if (member-equal (car pair) keys)
               (and (equal (cdr pair) (cdr (assoc-equal (car pair) a2)))
                    (alists-equiv-on (remove-equal (car pair) keys) a1 a2))
             (alists-equiv-on keys a1 a2)))
  :hints (("Goal" :in-theory (enable alists-equiv-on))))

(defthm alists-equiv-on-of-cons-arg2
  (equal (alists-equiv-on keys (cons pair a1) a2)
         (if (member-equal (car pair) keys)
             (and (equal (cdr pair) (cdr (assoc-equal (car pair) a2)))
                  (alists-equiv-on (remove-equal (car pair) keys) a1 a2))
           (alists-equiv-on keys a1 a2)))
  :hints (("Goal" :use (alists-equiv-on-of-cons-arg2-fw
                        alists-equiv-on-of-cons-arg2-back))))

;; Returns (mv foundp bd-guy)

(defun bad-guy-for-alists-equiv-on-aux (keys a1 a2)
  (if (endp keys)
      (mv nil nil)
    (let ((key (first keys)))
      (if (not (equal (lookup-equal key a1) (lookup-equal key a2)))
          (mv t key)
        (mv-let (foundp bad-guy)
          (bad-guy-for-alists-equiv-on-aux (rest keys) a1 a2)
          (if foundp
              (mv t bad-guy)
            (mv nil nil)))))))

(defund bad-guy-for-alists-equiv-on (keys a1 a2)
  (mv-let (foundp bad-guy)
    (bad-guy-for-alists-equiv-on-aux keys a1 a2)
    (if foundp
        bad-guy
      (first keys))))

(defthmd alists-equiv-on-when-agree-on-bad-guy-helper
  (iff (alists-equiv-on keys a1 a2)
       (not (mv-nth 0 (bad-guy-for-alists-equiv-on-aux keys a1 a2)))
       )
  :hints (("Goal" :in-theory (enable alists-equiv-on lookup-equal))))

(defthmd alists-equiv-on-when-agree-on-bad-guy
  (iff (alists-equiv-on keys a1 a2)
       (or (not (consp keys))
           (equal (lookup-equal (bad-guy-for-alists-equiv-on keys a1 a2) a1)
                  (lookup-equal (bad-guy-for-alists-equiv-on keys a1 a2) a2))))
  :hints (("Goal" :in-theory (enable lookup-equal
                                     bad-guy-for-alists-equiv-on
                                     alists-equiv-on-when-agree-on-bad-guy-helper))))

(defthm member-equal-of-bad-guy-for-alists-equiv-on-sam
  (implies (consp keys)
           (member-equal (bad-guy-for-alists-equiv-on keys a1 a2) keys))
  :hints (("Goal" :in-theory (enable BAD-GUY-FOR-ALISTS-EQUIV-ON))))

(defun EMPTY-EVAL-cdrs (alist a)
  (if (endp alist)
      nil
    (let ((pair (first alist)))
      (acons (car pair) (empty-eval (cdr pair) a)
             (EMPTY-EVAL-cdrs (rest alist) a)))))

(defthm PAIRLIS$-of-empty-eval-list
 (equal (PAIRLIS$ keys (EMPTY-EVAL-LIST vals a))
        (EMPTY-EVAL-cdrs (pairlis$ keys vals) a))
 :hints (("Goal" :in-theory (enable pairlis$))))

(defthm alistp-of-empty-eval-cdrs
  (implies (alistp alist)
           (alistp (EMPTY-EVAL-cdrs alist a)))
  :hints (("Goal" :in-theory (enable EMPTY-EVAL-cdrs))))

(defthm strip-cars-of-empty-eval-cdrs
  (equal (strip-cars (EMPTY-EVAL-cdrs alist a))
         (strip-cars alist))
 :hints (("Goal" :in-theory (enable EMPTY-EVAL-cdrs))))

(defthm cdr-of-assoc-equal-of-empty-eval-cdrs
  (equal (cdr (assoc-equal key (empty-eval-cdrs alist a)))
         (empty-eval (cdr (assoc-equal key alist)) a))
  :hints (("Goal" :in-theory (enable assoc-equal))))

(defthm lookup-equal-of-empty-eval-cdrs
  (equal (lookup-equal key (empty-eval-cdrs alist a))
         (empty-eval (lookup-equal key alist) a))
  :hints (("Goal" :in-theory (enable lookup-equal))))

(defthmd empty-eval-cdrs-of-pairlis$
  (implies (equal (len keys) (len vals))
           (equal (empty-eval-cdrs (pairlis$ keys vals) a)
                  (pairlis$ keys (empty-eval-list vals a)))))

(theory-invariant (incompatible (:rewrite PAIRLIS$-OF-EMPTY-EVAL-LIST) (:rewrite empty-eval-cdrs-of-pairlis$)))

(defthm cdr-of-assoc-equal-of-pairlis$_when-member-equal-of-trivial-formals
  (implies (and (MEMBER-EQUAL VAR (TRIVIAL-FORMALS FORMALS ARGS))
                (no-duplicatesp-equal formals))
           (equal (CDR (ASSOC-EQUAL VAR (PAIRLIS$ FORMALS ARGS)))
                  var))
  :hints (("Goal" :in-theory (enable PAIRLIS$ trivial-formals))))

(defthm symbolp-when-MEMBER-EQUAL-of-trivial-formals
  (implies (and (MEMBER-EQUAL VAR (TRIVIAL-FORMALS FORMALS ARGS))
                (symbol-listp formals))
           (symbolp var))
  :hints (("Goal" :in-theory (enable TRIVIAL-FORMALS))))

(defthm lookup-equal-of-pairlis$-when-member-equal-of-trivial-formals
  (IMPLIES (AND (MEMBER-EQUAL SOMEVAR (TRIVIAL-FORMALS FORMALS ARGS))
                (no-duplicatesp-equal formals))
           (equal (LOOKUP-EQUAL SOMEVAR (PAIRLIS$ FORMALS ARGS))
                  somevar))
  :hints (("Goal" :in-theory (enable TRIVIAL-FORMALS pairlis$ lookup-equal assoc-equal))))

(defthm ASSOC-EQUAL-of-EMPTY-EVAL-CDRS-iff
 (implies (alistp alist)
          (iff (ASSOC-EQUAL SOMEVAR (EMPTY-EVAL-CDRS alist a))
               (ASSOC-EQUAL SOMEVAR alist)))

 :hints (("Goal" :in-theory (enable empty-eval-cdrs assoc-equal))))

(defthm LOOKUP-EQUAL-of-PAIRLIS$-of-NON-TRIVIAL-FORMALS-and-mv-nth-1-of-NON-TRIVIAL-FORMALS-AND-ARGS
 (implies (no-duplicatesp-equal formals)
          (equal (LOOKUP-EQUAL var (PAIRLIS$ (NON-TRIVIAL-FORMALS FORMALS ARGS)
                                             ;; could name this non-trivial-args:
                                             (MV-NTH 1 (NON-TRIVIAL-FORMALS-AND-ARGS FORMALS ARGS))))
                 (if (member-equal var (NON-TRIVIAL-FORMALS FORMALS ARGS))
                     (lookup-equal var (pairlis$ formals args))
                   nil)))
 :hints (("Goal" :in-theory (enable NON-TRIVIAL-FORMALS NON-TRIVIAL-FORMALS-and-args pairlis$))))

(defthmd cdr-of-assoc-equal-becomes-lookup-equal
  (equal (cdr (assoc-equal key alist))
         (lookup-equal key alist))
  :hints (("Goal" :in-theory (enable lookup-equal))))

(theory-invariant (incompatible (:rewrite cdr-of-assoc-equal-becomes-lookup-equal) (:definition lookup-equal)))

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
                                 (binary-append
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
  :hints (("Goal" :in-theory (e/d (LOOKUP-EQUAL-OF-APPEND cdr-of-assoc-equal-becomes-lookup-equal)
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
             (binary-append
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

  :hints ( ;; (and stable-under-simplificationp `(:in-theory (e/d (alists-equiv-on-when-agree-on-bad-guy
          ;;                                                      lookup-equal-of-append)
          ;;                                                     (EMPTY-EVAL-OF-LOOKUP-EQUAL-OF-PAIRLIS$
          ;;                                                      ))))
          ("Goal"
           :use ((:instance  alists-equiv-on-when-agree-on-bad-guy
                             (keys  (free-vars-in-term body))
                             (a1             (cons
                                              (cons var (empty-eval replacement a))
                                              (binary-append
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
                                       (binary-append
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
           :in-theory (e/d ( ;alists-equiv-on-when-agree-on-bad-guy
     ;                                   lookup-equal-of-append
                            ) ( ;STRIP-CARS-OF-PAIRLIS$
                            EMPTY-EVAL-OF-LOOKUP-EQUAL-OF-PAIRLIS$ ;bad
                            member-equal
                            LOOKUP-EQUAL-OF-EMPTY-EVAL-CDRS
                            ALISTS-EQUIV-ON-OF-APPEND-ARG1
                            ALISTS-EQUIV-ON-OF-CONS-ARG2
                            main.help.help
                            ))))
  :otf-flg t)


;; ;; for the proof, consider 3 cases: var, other trivial formal, non-trivial formal
;(skip-proofs
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
;)

(theory-invariant (incompatible (:rewrite CDR-OF-ASSOC-EQUAL-OF-EMPTY-EVAL-CDRS ) (:rewrite EMPTY-EVAL-OF-CDR-OF-ASSOC-EQUAL)))

;; subst-var-alt preserves the meaning of terms
(defthm-flag-induct-subst-var-alt
  (defthm subst-var-alt-correct
    (implies (and (symbolp var)
                  var
                  (pseudo-termp replacement)
                  (no-nils-in-termp replacement)
                  (pseudo-termp term)
                  (lambdas-closed-in-termp term)
                  (no-duplicate-lambda-formals-in-termp term)
                  (no-nils-in-termp term)
                  (alistp a))
             (equal (empty-eval (subst-var-alt var replacement term) a)
                    (empty-eval (make-lambda-term-simple (list var) (list replacement) term) a)))
    :flag induct-subst-var-alt)
  (defthm subst-var-alt-lst-correct
    (implies (and (symbolp var)
                  var
                  (pseudo-termp replacement)
                  (no-nils-in-termp replacement)
                  (pseudo-term-listp terms)
                  (lambdas-closed-in-termsp terms)
                  (no-duplicate-lambda-formals-in-termsp terms)
                  (no-nils-in-termsp terms)
                  (alistp a))
             (equal (empty-eval-list (subst-var-alt-lst var replacement terms) a)
                    (empty-eval-list (make-lambda-terms-simple (list var) (list replacement) terms) a)))
    :flag induct-subst-var-alt-lst)
  :otf-flg t
  :hints (("subgoal *1/4"  :use (:instance main (body (lambda-body (car term))) (formals (lambda-formals (car term))) (args (fargs term)))
           :in-theory (e/d (subst-var-alt
                            subst-var-alt-lst
     ;MEMBER-EQUAL-OF-STRIP-CARS-IFF
                            make-lambda-terms-simple
                            ;;make-lambda-term-simple
                            empty-eval-of-fncall-args
                            empty-eval-of-cdr-of-assoc-equal
                            lookup-equal ; todo
                            pseudo-termp-when-symbolp
                            )
                           (pseudo-termp
                            pairlis$
                            PAIRLIS$-OF-EMPTY-EVAL-LIST
                            set-difference-equal
                            empty-eval-of-fncall-args-back
                            CDR-OF-ASSOC-EQUAL-OF-EMPTY-EVAL-CDRS)))
          ("Goal" :expand (PSEUDO-TERMP TERM)
           :do-not '(generalize eliminate-destructors)
           :in-theory (e/d (subst-var-alt
                            subst-var-alt-lst
     ;MEMBER-EQUAL-OF-STRIP-CARS-IFF
                            make-lambda-terms-simple
                            ;;make-lambda-term-simple
                            empty-eval-of-fncall-args
                            empty-eval-of-cdr-of-assoc-equal
                            lookup-equal ; todo
                            pseudo-termp-when-symbolp
                            )
                           (pseudo-termp
                            pairlis$
                            PAIRLIS$-OF-EMPTY-EVAL-LIST
                            set-difference-equal
                            empty-eval-of-fncall-args-back
                            CDR-OF-ASSOC-EQUAL-OF-EMPTY-EVAL-CDRS)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm no-duplicate-lambda-formals-in-termsp-of-mv-nth-1-of-filter-formals-and-actuals
  (implies (no-duplicate-lambda-formals-in-termsp actuals)
           (no-duplicate-lambda-formals-in-termsp (mv-nth 1 (filter-formals-and-actuals formals actuals formals-to-keep))))
  :hints (("Goal" :in-theory (enable filter-formals-and-actuals))))

(defthm no-duplicatesp-equal-of-mv-nth-0-of-filter-formals-and-actuals
  (implies (no-duplicatesp-equal formals)
           (no-duplicatesp-equal (mv-nth 0 (filter-formals-and-actuals formals actuals formals-to-keep))))
  :hints (("Goal" :in-theory (enable filter-formals-and-actuals))))

(defthm no-duplicate-lambda-formals-in-termsp-of-map-lookup-equal
  (implies (no-duplicate-lambda-formals-in-termsp (strip-cdrs alist))
           (no-duplicate-lambda-formals-in-termsp (map-lookup-equal keys alist)))
  :hints (("Goal" :in-theory (enable map-lookup-equal))))

;move
(defthm no-duplicate-lambda-formals-in-termp-of-make-lambda-application-simple
  (implies (and (pseudo-termp body)
                (no-duplicate-lambda-formals-in-termp body)
                (symbol-listp formals)
                (no-duplicatesp-equal formals)
                (pseudo-term-listp actuals)
                (no-duplicate-lambda-formals-in-termsp actuals)
                (equal (len formals) (len actuals)))
           (no-duplicate-lambda-formals-in-termp (make-lambda-application-simple formals actuals body)))
  :hints (("Goal" :in-theory (e/d (make-lambda-application-simple
                                   no-duplicate-lambda-formals-in-termp)
                                  (mv-nth-0-of-filter-formals-and-actuals len)))))

;gen?
(defthm-flag-subst-var-alt
  (defthm no-duplicate-lambda-formals-in-termp-of-subst-var-alt
    (implies (and (symbolp var)
                  (pseudo-termp replacement)
                  (no-duplicate-lambda-formals-in-termp replacement)
                  (pseudo-termp term)
                  (no-duplicate-lambda-formals-in-termp term))
             (no-duplicate-lambda-formals-in-termp (subst-var-alt var replacement term)))
    :flag subst-var-alt)
  (defthm no-duplicate-lambda-formals-in-termsp-of-subst-var-alt-lst
    (implies (and (symbolp var)
                  (pseudo-termp replacement)
                  (no-duplicate-lambda-formals-in-termp replacement)
                  (pseudo-term-listp terms)
                  (no-duplicate-lambda-formals-in-termsp terms))
             (no-duplicate-lambda-formals-in-termsp (subst-var-alt-lst var replacement terms)))
    :flag subst-var-alt-lst)
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (e/d (subst-var-alt
                            subst-var-alt-lst
                            pseudo-termp-when-symbolp
                            no-duplicate-lambda-formals-in-termp)
                           (pseudo-termp)))))
