; A tool to substitute lambda formals when we can do so without causing clashes
;
; Copyright (C) 2024-2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; todo: split proofs into separate book

(include-book "lambdas-closed-in-termp")
(include-book "no-duplicate-lambda-formals-in-termp")
(include-book "no-nils-in-termp")
(include-book "kestrel/alists-light/map-lookup-equal" :dir :system)
(include-book "kestrel/evaluators/empty-eval" :dir :system)
(include-book "non-trivial-formals")
(include-book "trivial-formals")
(include-book "sublis-var-simple")
(local (include-book "helpers"))
(local (include-book "empty-eval-helpers"))
(local (include-book "kestrel/alists-light/symbol-alistp" :dir :system))
(local (include-book "kestrel/lists-light/subsetp-equal" :dir :system))
(local (include-book "kestrel/lists-light/no-duplicatesp-equal" :dir :system))
(local (include-book "kestrel/lists-light/intersection-equal" :dir :system))
(local (include-book "kestrel/lists-light/set-difference-equal" :dir :system))
(local (include-book "kestrel/lists-light/remove-equal" :dir :system))
(local (include-book "kestrel/lists-light/append" :dir :system))
(local (include-book "kestrel/lists-light/len" :dir :system))
(local (include-book "kestrel/lists-light/list-sets" :dir :system))
(local (include-book "kestrel/typed-lists-light/symbol-listp" :dir :system))
(local (include-book "kestrel/typed-lists-light/pseudo-term-listp" :dir :system))
(local (include-book "kestrel/lists-light/member-equal" :dir :system))
(local (include-book "kestrel/lists-light/true-list-fix" :dir :system))
(local (include-book "sublis-var-simple-proofs"))
(local (include-book "kestrel/alists-light/pairlis-dollar" :dir :system))
(local (include-book "kestrel/typed-lists-light/pseudo-term-listp" :dir :system))
(local (include-book "kestrel/lists-light/take" :dir :system))
(local (include-book "kestrel/lists-light/nthcdr" :dir :system))
;(local (include-book "subst-var-alt-proofs")) ; todo, for pairlis$-of-empty-eval-list, which introduces empty-eval-cdrs -- why?

(local (in-theory (enable sublis-var-simple-correct-3)))

(local (in-theory (disable ;get-args-for-formals
                           intersection-equal set-difference-equal member-equal subsetp-equal true-listp)))

;(local (in-theory (disable lookup-equal-of-empty-eval-cdrs)))

(theory-invariant (incompatible (:rewrite empty-eval-of-lookup-equal-of-pairlis$)
                                (:rewrite lookup-equal-of-empty-eval-cdrs)))

(local (in-theory (enable ;true-listp-when-symbol-listp-rewrite-unlimited
                          pseudo-term-listp-when-symbol-listp)))

;; (defthmd len-of-get-args-for-formals
;;   (implies (and (no-duplicatesp-equal formals)
;;                 (no-duplicatesp-equal target-formals))
;;            (equal (len (get-args-for-formals formals args target-formals))
;;                   (len (intersection-equal formals target-formals))))
;;   :hints (("Goal" :in-theory (enable get-args-for-formals intersection-equal))))

(local
  (defun cdr-remove-equal-induct (x y)
    (if (endp x)
        (list x y)
      (cdr-remove-equal-induct (cdr x) (remove-equal (car x) y)))))

(defthm len-of-intersection-equal-when-subsetp-equal
  (implies (and (subsetp-equal y x)
                (no-duplicatesp-equal x)
                (no-duplicatesp-equal y))
           (equal (len (intersection-equal x y))
                  (len y)))
  :hints (("Goal" ;; :induct (intersection-equal x y)
           :induct (cdr-remove-equal-induct x y)
           :in-theory (enable subsetp-equal intersection-equal no-duplicatesp-equal))))

;; (defthm len-of-get-args-for-formals-2
;;   (implies (and (subsetp-equal target-formals formals)
;;                 (no-duplicatesp-equal formals)
;;                 (no-duplicatesp-equal target-formals))
;;            (equal (len (get-args-for-formals formals args target-formals))
;;                   (len target-formals)))
;;   :hints (("Goal" :in-theory (enable len-of-get-args-for-formals))))

;; (defthm intersection-equal-of-cdr-arg2-when-not-member-equal-of-car
;;   (implies (and ;(no-duplicatesp-equal x)
;;                 (no-duplicatesp-equal y))
;;            (equal (intersection-equal y (cdr x))
;;                   (if (member-equal (car x) y)
;;                       (remove-equal (car x) (intersection-equal y x))
;;                     (intersection-equal y x))))
;;   :hints (("Goal" :in-theory (enable intersection-equal))))

(defthm intersection-equal-of-cdr-arg2-when-not-member-equal-of-car
  (implies (not (member-equal (car x) y))
           (equal (intersection-equal y (cdr x))
                  (intersection-equal y x)))
  :hints (("Goal" :in-theory (enable intersection-equal))))

;; (defthm len-of-intersection-equal-of-cdr-arg2-when-not-member-equal-of-car
;;   (implies (and (member-equal (car x) y)
;;                 (no-duplicatesp x)
;;                 (no-duplicatesp y))
;;            (equal (len (intersection-equal y (cdr x)))
;;                   (+ -1 (len (intersection-equal y x)))))
;;   :hints (("Goal" :in-theory (enable intersection-equal))))

;; (defthm len-of-intersection-equal-helper
;;   (implies (and (no-duplicatesp-equal x)
;;                 (no-duplicatesp-equal y))
;;            (equal (len (intersection-eq x y))
;;                   (len (intersection-eq y x))))
;;   :hints (("Goal" :induct (intersection-equal x y)
;;            :do-not '(generalize eliminate-destructors)
;;            :expand ((intersection-equal x y)
;;                     (intersection-equal y x))
;;            :in-theory (enable subsetp-equal intersection-equal))))

(defthm subsetp-equal-of-free-vars-in-term-of-lookup-equal-and-free-vars-in-terms-of-map-lookup-equal
  (implies (member-equal key keys)
           (subsetp-equal (free-vars-in-term (lookup-equal key alist))
                          (free-vars-in-terms (map-lookup-equal keys alist))))
  :hints (("Goal" :in-theory (enable map-lookup-equal))))

(defthm subsetp-equal-of-append-of-set-difference-equal-same
  (equal (subsetp-equal x (append c (set-difference-equal z c)))
         (subsetp-equal x (append c z)))
  :hints (("Goal" :in-theory (enable subsetp-equal))))

(defthm subsetp-equal-of-free-vars-in-term-of-cdr-of-assoc-equal-and-free-vars-in-terms-of-map-lookup-equal
  (implies (member-equal key keys)
           (subsetp-equal (free-vars-in-term (cdr (assoc-equal key alist)))
                          (free-vars-in-terms (map-lookup-equal keys alist))))
  :hints (("Goal" :in-theory (enable map-lookup-equal lookup-equal))))

(defthm not-intersection-equal-of-set-difference-equal-same-arg2-arg2
  (not (intersection-equal x (set-difference-equal y x)))
  :hints (("Goal" :in-theory (enable intersection-equal
                                     set-difference-equal))))

(defthm set-difference-equal-of-remove-equal-when-not-member-equal
  (implies (not (member-equal a x))
           (equal (set-difference-equal x (remove-equal a y))
                  (set-difference-equal x y)))
  :hints (("Goal" :in-theory (enable set-difference-equal remove-equal))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; ;; This adds any extra vars needed to make the lambda closed.
;; (defund make-lambda-application-simpler (formals actuals body)
;;   (declare (xargs :guard (and (pseudo-termp body)
;;                               (symbol-listp formals)
;;                               (pseudo-term-listp actuals)
;;                               (equal (len formals) (len actuals)))))
;;   (let ((free-vars (free-vars-in-term body)))
;;     (let* ((extra-vars (set-difference-eq free-vars formals))
;;            (new-formals (append formals extra-vars))
;;            (new-actuals (append actuals extra-vars)))
;;       (cons (cons 'lambda
;;                   (cons new-formals (cons body 'nil)))
;;             new-actuals))))

;think about the order!

(local (in-theory (disable pairlis$)))

(defthm pseudo-termp-of-lookup-equal-of-pairlis$ ;gen?
  (implies (pseudo-term-listp args)
           (pseudo-termp (lookup-equal key (pairlis$ formals args))))
  :hints (("Goal" :in-theory (enable lookup-equal assoc-equal pairlis$))))

(defthm pseudo-term-listp-of-map-lookup-equal-of-pairlis$ ;gen?
  (implies (pseudo-term-listp args)
           (pseudo-term-listp (map-lookup-equal keys (pairlis$ formals args))))
  :hints (("Goal" :in-theory (enable map-lookup-equal))))

;; ;get rid of one?
;; (defthm mv-nth-of-1-filter-formals-and-actuals
;;   (equal (mv-nth 1 (filter-formals-and-actuals formals actuals formals-to-keep))
;;          (get-args-for-formals formals actuals formals-to-keep))
;;   :hints (("Goal" :in-theory (enable filter-formals-and-actuals
;;                                      get-args-for-formals))))


;; (defthm get-args-for-formals-of-cons-arg3-when-not-member-equal
;;   (implies (not (member-equal f formals))
;;            (equal (get-args-for-formals formals args (cons f target-formals))
;;                   (get-args-for-formals formals args target-formals)))
;;   :hints (("Goal" :in-theory (enable get-args-for-formals))))

;; (defthm lookup-equal-helper
;;   (implies (and (not (member-equal bg formals-to-subst))
;;                 (no-duplicatesp-equal formals))
;;            (equal (lookup-equal
;;                     bg
;;                     (pairlis$
;;                       (set-difference-equal formals formals-to-subst)
;;                       (empty-eval-list
;;                         (get-args-for-formals formals args
;;                                               (set-difference-equal formals formals-to-subst))
;;                         a)))
;;                   (lookup-equal bg (pairlis$ formals (empty-eval-list args a)))))
;;   :hints (("Goal" :in-theory (e/d (pairlis$
;;                                    empty-eval-cdrs-of-pairlis$
;;                                    get-args-for-formals
;;                                    set-difference-equal
;;                                    no-duplicatesp-equal)
;;                                   (pairlis$-of-empty-eval-list)))))


(defthm if-helper (equal (equal (if test x y) y) (if test (equal x y) t)))

(local (in-theory (disable empty-eval-of-lookup-equal-of-pairlis$)))
(local (in-theory (enable lookup-equal-of-pairlis$-of-empty-eval-list)))

(theory-invariant (incompatible (:rewrite empty-eval-of-lookup-equal-of-pairlis$)
                                (:rewrite lookup-equal-of-pairlis$-of-empty-eval-list)))

;; (defthm get-args-for-formals-of-true-list-fix-arg3
;;   (equal (get-args-for-formals formals args (true-list-fix f))
;;          (get-args-for-formals formals args f))
;;   :hints (("Goal" :in-theory (enable get-args-for-formals))))

;; (defthm get-args-for-formals-same
;;   (implies (and (subsetp-equal formals formals2)
;;                 (equal (len formals) (len args)))
;;            (equal (get-args-for-formals formals args formals2)
;;                   (true-list-fix args)))
;;   :hints (("Goal" :in-theory (enable get-args-for-formals))))

;; (defthm lookup-equal-helper2
;;   (implies (and (not (member-equal b formals-to-subst))
;;                 ;(subsetp-equal formals-to-subst formals)
;;                 (equal (len formals) (len args))
;;                 (no-duplicatesp-equal formals)
;;                 )
;;            (equal (lookup-equal b (pairlis$ (set-difference-equal formals formals-to-subst)
;;                                             (get-args-for-formals formals args (set-difference-equal formals formals-to-subst))))
;;                   (lookup-equal b (pairlis$ formals args))))
;;   :hints (("Goal"  ;:induct (cdr-remove-equal-induct formals-to-subst formals)
;;            :do-not '(generalize eliminate-destructors)
;;            :expand (set-difference-equal formals formals-to-subst)
;;            :in-theory (enable get-args-for-formals set-difference-equal pairlis$ subsetp-equal member-equal
;;                               no-duplicatesp-equal))))

;; (defun inductf (x y z)
;;   (if (endp x)
;;       (list x y z)
;;     (inductf (cdr x) (remove-equal (car x) y)  (remove-equal (lookup-equal (car x) y))))

;; does the order of the formals-to-subst matter?

;; (thm
;;   (implies (and (member-equal b formals-to-subst)
;;                 (subsetp-equal formals-to-subst formals)
;;                 (equal (len formals) (len args))
;;                 (no-duplicatesp-equal formals))
;;            (equal (lookup-equal b (pairlis$ formals-to-subst (get-args-for-formals formals args formals-to-subst)))
;;                   (lookup-equal b (pairlis$ formals args))))
;;   :hints (("Goal" :do-not '(generalize eliminate-destructors)
;;            :induct (cdr-remove-equal-induct formals-to-subst formals)
;;            :expand (pairlis$ formals-to-subst
;;                       (get-args-for-formals formals args formals-to-subst))
;;            :in-theory (enable get-args-for-formals pairlis$ lookup-equal subsetp-equal member-equal))))

(defthm lookup-equal-of-pairlis$-of-map-lookup-equal-same-keys
  (equal (lookup-equal key (pairlis$ keys (map-lookup-equal keys alist)))
         (if (member-equal key keys)
             (lookup-equal key alist)
           nil))
  :hints (("Goal" :expand (pairlis$ keys vals)
           :in-theory (enable map-lookup-equal pairlis$))))

(defthm lookup-equal-of-pairlis$-same
  (equal (lookup-equal key (pairlis$ keys keys))
         (if (member-equal key keys)
             key
           nil))
  :hints (("Goal" :in-theory (enable pairlis$))))


;; (defthm-flag-free-vars-in-term
;;   (defthm theorem-for-free-vars-in-term
;;     (iff (member-equal var (free-vars-in-term (sublis-var-simple alist term)))
;;          (or (and (member-equal var (free-vars-in-term term))
;;                   (not (member-equal var (strip-cars alist))))
;;              (member-equal var (free-vars-in-terms (map-lookup-equal
;;                                                      (intersection-equal (strip-cars alist)
;;                                                                          (free-vars-in-term term))
;;                                                      alist)))))
;;     :flag free-vars-in-term)
;;   (defthm theorem-for-free-vars-in-terms
;;     (iff (member-equal var (free-vars-in-terms (sublis-var-simple-lst alist terms)))
;;          (or (and (member-equal var (free-vars-in-terms terms))
;;                   (not (member-equal var (strip-cars alist))))
;;              (member-equal var (free-vars-in-terms (map-lookup-equal
;;                                                      (intersection-equal (strip-cars alist)
;;                                                                          (free-vars-in-terms terms))
;;                                                      alist)))))
;;     :flag free-vars-in-terms)

;;   :hints (("Goal" :in-theory (enable free-vars-in-term
;;                                      free-vars-in-terms
;;                                      sublis-var-simple
;;                                      sublis-var-simple-lst))))

(defthm empty-eval-of-append-only-arg1
  (implies (and (subsetp-equal (free-vars-in-term term) (strip-cars a1))
                (alistp a1)
                (pseudo-termp term))
           (equal (empty-eval term (append a1 a2))
                  (empty-eval term a1)))
  :hints (("Goal" :in-theory (enable append subsetp-equal))))

(local
  (defthmd equal-of-empty-eval-and-empty-eval-when-alists-equiv-on-special-forced
    (implies (and (force (alists-equiv-on (free-vars-in-term term)
                                          alist1 alist2))
                  (pseudo-termp term))
             (equal (equal (empty-eval term alist1)
                           (empty-eval term alist2))
                    t))))

(local (in-theory (disable assoc-equal len)))

(defthm not-assoc-equal-of-nil
  (not (assoc-equal key nil))
  :hints (("Goal" :in-theory (enable assoc-equal))))

;todo: chose one!
(defthm equal-of-cdr-of-assoc-equal-and-lookup-equal
  (equal (equal (cdr (assoc-equal key alist)) (lookup-equal key alist))
         t)
  :hints (("Goal" :in-theory (enable lookup-equal))))

;;todo: prove and use above.  also use in expand-lambdas?
;reorder args?
(defund subst-formal-in-lambda-application (formals body args formal-to-subst)
  (declare (xargs :guard (and (symbol-listp formals)
                              (no-duplicatesp-equal formals)
                              (pseudo-termp body)
                              (pseudo-term-listp args)
                              (member-equal formal-to-subst (non-trivial-formals formals args)) ; doesn't make sense to subst a trivial formal
                              ;; the arg being put in for formal-to-subst cannot mention any of the remaining non-trivial formals:
                              ;; this avoid clashes:
                              (not (intersection-eq (free-vars-in-term (lookup-equal formal-to-subst (pairlis$ formals args)))
                                                    (remove-equal formal-to-subst (non-trivial-formals formals args)))))
                  :guard-hints (("Goal" :in-theory (enable symbolp-when-member-equal-and-symbol-listp)))))
  (b* ((alist (pairlis$ formals args))
       (arg-to-subst (lookup-equal formal-to-subst alist)) ; optimize?  maybe get the position of the forma
       (arg-to-subst-vars (free-vars-in-term arg-to-subst))
       (remaining-formals (remove-eq formal-to-subst formals))
       (remaining-args (map-lookup-equal remaining-formals alist)) ; just remove the arg corresponding to the formal-to-subst?
       ;(remaining-non-trivial-formals (non-trivial-formals remaining-formals remaining-args))
       ;(clashing-vars (intersection-eq (free-vars-in-terms args-to-subst) remaining-non-trivial-formals))
       ;; ((when clashing-vars) ; can't happen if we assume the guard
       ;;  (er hard 'subst-some-formals-in-lambda-application "Variable clash on ~x0." clashing-vars)
       ;;  `((lambda ,formals ,body) ,@args))
       (body (sublis-var-simple (acons formal-to-subst arg-to-subst nil) body)))
    ;; todo: this can add back formal in a different position:
    ;;(make-lambda-application-simpler remaining-formals remaining-args body)
    (let ((extra-vars (set-difference-equal arg-to-subst-vars remaining-formals)))
      `((lambda ,(append remaining-formals extra-vars) ,body) ,@remaining-args ,@extra-vars))))

    ;; (if (member-eq formal-to-subst arg-to-subst-vars)
    ;;     ;; keep this formal (but not it is a trivial formal):
    ;;     (let ((extra-vars (set-difference-equal arg-to-subst-vars formals)))
    ;;       `((lambda ,(append formals extra-vars) body) ,@args ,@extra-vars))


;;(use-trivial-ancestors-check)

;; (subst-formal-in-lambda-application '(x y z) '(foo x y z) '((f x) (f y) (f z)) 'x)

;; (thm
;;   (implies (and (symbol-listp vars)
;;                 (not (member-equal nil vars)))
;;            (equal (empty-eval term (binary-append a1 (pairlis$ vars (empty-eval-list vars a))))
;;                   (empty-eval term (append a1 a))))
;;   :hints (("Goal" :in-theory (disable pairlis$-of-empty-eval-list))))

(local (in-theory (enable not-member-equal-of-nil-when-no-nils-in-termsp)))

;; (thm
;;   (implies (no-nils-in-termp term)
;;            (not (member-equal 'nil (free-vars-in-term term)))))

;; (local
;;   (defthm empty-eval-cdrs-of-append
;;     (equal (empty-eval-cdrs (append x y) a)
;;            (append (empty-eval-cdrs x a) (empty-eval-cdrs y a)))))

(defthm member-equal-of-trivial-formals-helper
  (implies (and (member-equal x formals)
                (no-duplicatesp formals))
           (iff (member-equal x (trivial-formals formals args))
                (not (member-equal x (non-trivial-formals formals args)))))
  :hints (("Goal" :in-theory (enable trivial-formals
                                     non-trivial-formals))))

(local (in-theory (disable member-equal-of-non-trivial-formals-becomes-not-member-equal-of-non-trivial-formals))) ; bad name?

(local
  (defthm not-member-equal-of-bad-guy-for-alists-equiv-on-when-not-intersection-equal
    (implies (and (not (intersection-equal set keys))
                  (consp keys))
             (not (member-equal (bad-guy-for-alists-equiv-on keys a1 a2) set)))
    :hints (("Goal" :use (member-equal-of-bad-guy-for-alists-equiv-on-sam) ; fix name
             :in-theory (disable member-equal-of-bad-guy-for-alists-equiv-on-sam
                                 member-equal-of-bad-guy-for-alists-equiv-when-subsetp-equal)))))

(local
  (defthm not-member-equal-of-bad-guy-for-alists-equiv-on-when-not-intersection-equal-gen
    (implies (and (not (intersection-equal (remove-equal formal-to-subst set) keys))
                  (not (equal formal-to-subst (bad-guy-for-alists-equiv-on keys a1 a2)))
                  (consp keys))
             (not (member-equal (bad-guy-for-alists-equiv-on keys a1 a2) set)))
    :hints (("Goal" :use (member-equal-of-bad-guy-for-alists-equiv-on-sam) ; fix name
             :in-theory (disable member-equal-of-bad-guy-for-alists-equiv-on-sam
                                 member-equal-of-bad-guy-for-alists-equiv-when-subsetp-equal)))))

;; Correctness theorem for subst-formal-in-lambda-application.  Shows that it
;; doesn't change the meaning of terms.
(defthm empty-eval-of-subst-formal-in-lambda-application-correct
  (implies (and (symbol-listp formals)
;                (not (member-equal nil formals))
                (no-duplicatesp-equal formals)
                (equal (len formals) (len args))
                (pseudo-termp body)
                (pseudo-term-listp args)
                (member-equal formal-to-subst (non-trivial-formals formals args)) ; doesn't make sense to subst a trivial formal
                ;; the arg being put in for formal-to-subst cannot mention any of the remaining non-trivial formals:
                ;; this avoid clashes:
                (not (intersection-eq (free-vars-in-term (lookup-equal formal-to-subst (pairlis$ formals args)))
                                      (remove-equal formal-to-subst (non-trivial-formals formals args))))
                (no-nils-in-termp body)
                (no-nils-in-termsp args)
                ;; the lambda must be closed:
                (subsetp-equal (free-vars-in-term body) formals))
           (equal (empty-eval (subst-formal-in-lambda-application formals body args formal-to-subst) a)
                  (empty-eval `((lambda ,formals ,body) ,@args) a)))
  :hints (("[2]Goal" :in-theory (e/d (;make-lambda-application-simple
                                      ;; make-lambda-term-simple
                                      ;; make-lambda-application-simpler
                              ;intersection-equal-of-set-difference-equal-when-subsetp-equal
                                      alists-equiv-on-when-agree-on-bad-guy
                                      lookup-equal-of-append
;                                      empty-eval-cdrs-of-pairlis$
                                      symbolp-when-member-equal-and-symbol-listp
                                      not-member-equal-of-nil-when-no-nils-in-termsp)
                                     (len
                                      alistp
                                      nthcdr-of-append-gen
                                      strip-cdrs-of-pairlis$
                                      pairlis$-of-append-arg1
                                      ;pairlis$-of-empty-eval-list
                                      no-duplicatesp-equal-when-no-duplicatesp-equal-of-cdr ; looped with trivial ancestors check mod
                                      intersection-equal-when-not-intersection-equal-of-cdr-arg2-iff
                                      ))
           :cases ((member-equal (bad-guy-for-alists-equiv-on
                                   (free-vars-in-term (lookup-equal formal-to-subst
                                                                    (pairlis$ formals args)))
                                   (append
                                     (pairlis$
                                       (remove-equal formal-to-subst formals)
                                       (map-lookup-equal (remove-equal formal-to-subst formals)
                                                         (pairlis$ formals (empty-eval-list args a))))
                                     (pairlis$
                                       (set-difference-equal
                                         (free-vars-in-term (lookup-equal formal-to-subst
                                                                          (pairlis$ formals args)))
                                         (remove-equal formal-to-subst formals))
                                       (empty-eval-list
                                         (set-difference-equal
                                           (free-vars-in-term (lookup-equal formal-to-subst
                                                                            (pairlis$ formals args)))
                                           (remove-equal formal-to-subst formals))
                                         a)))
                                   a) (trivial-formals formals args)))
           )
          ("[1]Subgoal 1" :in-theory (e/d (;make-lambda-application-simple
                                           ;; make-lambda-term-simple
                                           ;; make-lambda-application-simpler
                              ;intersection-equal-of-set-difference-equal-when-subsetp-equal
                                           alists-equiv-on-when-agree-on-bad-guy
                                           lookup-equal-of-append
;                                           empty-eval-cdrs-of-pairlis$
                                           symbolp-when-member-equal-and-symbol-listp
                                           not-member-equal-of-nil-when-no-nils-in-termsp)
                                          (len
                                           alistp
                                           nthcdr-of-append-gen
                                           strip-cdrs-of-pairlis$
                                           pairlis$-of-append-arg1
                                           ;pairlis$-of-empty-eval-list
                                           no-duplicatesp-equal-when-no-duplicatesp-equal-of-cdr ; looped with trivial ancestors check mod
                                           intersection-equal-when-not-intersection-equal-of-cdr-arg2-iff
                                           )))
          ("[1]Subgoal 2" :in-theory (e/d (;make-lambda-application-simple
                                           ;; make-lambda-term-simple
                                           ;; make-lambda-application-simpler
                              ;intersection-equal-of-set-difference-equal-when-subsetp-equal
                                           alists-equiv-on-when-agree-on-bad-guy
                                           lookup-equal-of-append
;                                           empty-eval-cdrs-of-pairlis$
                                           symbolp-when-member-equal-and-symbol-listp
                                           not-member-equal-of-nil-when-no-nils-in-termsp
                                           equal-of-empty-eval-and-empty-eval-when-alists-equiv-on-special-forced
                                           )
                                          (len
                                           alistp
                                           nthcdr-of-append-gen
                                           strip-cdrs-of-pairlis$
                                           pairlis$-of-append-arg1
                                           ;pairlis$-of-empty-eval-list
                                           no-duplicatesp-equal-when-no-duplicatesp-equal-of-cdr ; looped with trivial ancestors check mod
                                           intersection-equal-when-not-intersection-equal-of-cdr-arg2-iff
                                           )))
          ("Goal" :do-not '(generalize eliminate-destructors)
;           :cases ((member-eq formal-to-subst (free-vars-in-term (lookup-equal formal-to-subst (pairlis$ formals args)))))
           :in-theory (e/d (subst-formal-in-lambda-application
                            ;;make-lambda-application-simple
                            ;; make-lambda-term-simple
                            ;; make-lambda-application-simpler
                              ;intersection-equal-of-set-difference-equal-when-subsetp-equal
                            alists-equiv-on-when-agree-on-bad-guy
                            lookup-equal-of-append
;                            empty-eval-cdrs-of-pairlis$
                            symbolp-when-member-equal-and-symbol-listp
                            equal-of-empty-eval-and-empty-eval-when-alists-equiv-on-special-forced
                            )
                           (len
                            alistp
                            nthcdr-of-append-gen
                            strip-cdrs-of-pairlis$
                            pairlis$-of-append-arg1
                            ;pairlis$-of-empty-eval-list
                            no-duplicatesp-equal-when-no-duplicatesp-equal-of-cdr ; looped with trivial ancestors check mod
                            intersection-equal-when-not-intersection-equal-of-cdr-arg2-iff
                            pairlis$-of-append-and-append
                            empty-eval-list-of-append
                            empty-eval-list-when-symbol-listp
                            empty-eval-list-of-cons
                            )))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;can we do them one by one?  maybe not, given the condition on clashes (removing more might help avoid clashes for others)

;; formals and args must have the same length
(defund subst-formals-in-lambda-application (formals body args formals-to-subst)
  (declare (xargs :guard (and (symbol-listp formals)
                              ;(no-duplicatesp-equal formals) ; put back?
                              (pseudo-termp body)
                              (pseudo-term-listp args)
                              (true-listp formals-to-subst)
                              (subsetp-equal formals-to-subst (non-trivial-formals formals args)) ; doesn't make sense to subst a trivial formal
                              ;; the args being put in for the formals-to-subst cannot mention any of the remaining non-trivial formals:
                              ;; this avoid clashes:
                              ;; (not (intersection-eq (free-vars-in-terms (map-lookup-equal formals-to-subst (pairlis$ formals args)))
                              ;;                       (set-difference-equal (non-trivial-formals formals args) formals-to-subst)))
                              )
                  :guard-hints (("Goal" :in-theory (enable symbolp-when-member-equal-and-symbol-listp)))))
  (b* ((alist (pairlis$ formals args))
       (args-to-subst (map-lookup-equal formals-to-subst alist)) ; optimize?  maybe get the position of the formals
       (args-to-subst-vars (free-vars-in-terms args-to-subst))
       (remaining-formals (set-difference-eq formals formals-to-subst))
       (remaining-args (map-lookup-equal remaining-formals alist)) ; just remove the args corresponding to the formals-to-subst?
       ;(remaining-non-trivial-formals (non-trivial-formals remaining-formals remaining-args))
       ;(clashing-vars (intersection-eq (free-vars-in-terms args-to-subst) remaining-non-trivial-formals))
       ;; ((when clashing-vars) ; can't happen if we assume the guard
       ;;  (er hard 'subst-some-formals-in-lambda-application "Variable clash on ~x0." clashing-vars)
       ;;  `((lambda ,formals ,body) ,@args))
       (new-body (sublis-var-simple (pairlis$ formals-to-subst args-to-subst) body))
       ;; todo: this can add back formal in a different position:
       ;;(make-lambda-application-simpler remaining-formals remaining-args new-body)
       (extra-vars (set-difference-equal args-to-subst-vars remaining-formals))
       (new-formals (append remaining-formals extra-vars))
       (new-args (append remaining-args extra-vars)))
    (if nil ; (equal new-formals new-args) ; avoid trivial lambda ;; todo: put back!
        new-body
      `((lambda ,new-formals ,new-body) ,@new-args))))

(defthm pseudo-termp-of-subst-formals-in-lambda-application
  (implies (and (symbol-listp formals)
                (pseudo-termp body)
                (pseudo-term-listp args)
                (symbol-listp formals-to-subst) ; drop?
                )
           (pseudo-termp (subst-formals-in-lambda-application formals body args formals-to-subst)))
  :hints (("Goal" :in-theory (enable subst-formals-in-lambda-application))))

(defthm no-nils-in-termp-of-subst-formals-in-lambda-application
  (implies (and (symbol-listp formals)
                (pseudo-termp body)
                (pseudo-term-listp args)
;                (symbol-listp formals-to-subst) ; drop?
                (no-nils-in-termp body)
                (no-nils-in-termsp args)
                (subsetp-equal formals-to-subst formals)
                (equal (len args) (len formals))
                )
           (no-nils-in-termp (subst-formals-in-lambda-application formals body args formals-to-subst)))
  :hints (("Goal" :in-theory (enable subst-formals-in-lambda-application))))

;drop some hyps?
(defthm lambdas-closed-in-termp-of-subst-formals-in-lambda-application
  (implies (and (symbol-listp formals)
                (pseudo-termp body)
                (pseudo-term-listp args)
;                (symbol-listp formals-to-subst) ; drop?
                (lambdas-closed-in-termp body)
                (lambdas-closed-in-termsp args)
                (subsetp-equal formals-to-subst formals)
                (equal (len args) (len formals))
                ;; the lambda must be closed:
                (subsetp-equal (free-vars-in-term body) formals)
                )
           (lambdas-closed-in-termp (subst-formals-in-lambda-application formals body args formals-to-subst)))
  :hints (("Goal" :expand (lambdas-closed-in-termp body)
           :in-theory (enable subst-formals-in-lambda-application lambdas-closed-in-termp))))

(defthm no-duplicate-lambda-formals-in-termp-of-subst-formals-in-lambda-application
  (implies (and (pseudo-term-listp args)
                (no-duplicate-lambda-formals-in-termp body)
                (no-duplicate-lambda-formals-in-termsp args)
                (no-duplicatesp-equal formals))
           (no-duplicate-lambda-formals-in-termp (subst-formals-in-lambda-application formals body args formals-to-subst)))
  :hints (("Goal" :expand (no-duplicate-lambda-formals-in-termp body)
           :in-theory (enable subst-formals-in-lambda-application no-duplicate-lambda-formals-in-termp))))

;; Justifies skipping the call to subst-formals-in-lambda-application if formals-to-subst is nil
(defthm subst-formals-in-lambda-application-of-nil-arg4
  (implies (and (true-listp formals)
                (no-duplicatesp-equal formals)
                (pseudo-termp body)
                (true-listp args)
                (equal (len args) (len formals)))
           (equal (subst-formals-in-lambda-application formals body args nil)
                  `((lambda ,formals ,body) ,@args)))
  :hints (("Goal" :in-theory (enable subst-formals-in-lambda-application))))

;; (thm
;;   (implies (and (not (intersection-eq (free-vars-in-terms (map-lookup-equal formals-to-subst (pairlis$ formals args)))
;;                                       (set-difference-equal (non-trivial-formals formals args) formals-to-subst)))
;;                 (member-equal fts formals-to-subst))
;;            (not (intersection-equal (non-trivial-formals formals args)
;;                                     (free-vars-in-term (lookup-equal fts (pairlis$ formals args)))))))

(local
  (defthm not-member-equal-of-bad-guy-for-alists-equiv-on-when-not-intersection-equal-alt
    (implies (and (not (intersection-equal keys set)) ; flipped
                  (consp keys))
             (not (member-equal (bad-guy-for-alists-equiv-on keys a1 a2) set)))
    :hints (("Goal" :use (member-equal-of-bad-guy-for-alists-equiv-on-sam) ; fix name
             :in-theory (disable member-equal-of-bad-guy-for-alists-equiv-on-sam
                                 member-equal-of-bad-guy-for-alists-equiv-when-subsetp-equal)))))

(local
  (defthm not-member-equal-of-bad-guy-for-alists-equiv-on-when-not-intersection-equal-alt-gen
    (implies (and (not (intersection-equal keys (set-difference-equal set diff))) ; flipped
                  (not (member-equal (bad-guy-for-alists-equiv-on keys a1 a2) diff))
                  (consp keys))
             (not (member-equal (bad-guy-for-alists-equiv-on keys a1 a2) set)))
    :hints (("Goal" :use (member-equal-of-bad-guy-for-alists-equiv-on-sam) ; fix name
             :in-theory (disable member-equal-of-bad-guy-for-alists-equiv-on-sam
                                 member-equal-of-bad-guy-for-alists-equiv-when-subsetp-equal)))))

;; formals-to-subst is a free var
(local
  (defthm bad-guy-helper
    (implies (and (not (intersection-equal (free-vars-in-terms (map-lookup-equal formals-to-subst (pairlis$ formals args)))
                                           (set-difference-equal (non-trivial-formals formals args) formals-to-subst)))
                  (not (member-equal (bad-guy-for-alists-equiv-on (free-vars-in-term (lookup-equal fts (pairlis$ formals args))) a1 a2)
                                     formals-to-subst))
                  (member-equal fts formals-to-subst)
                  (consp (free-vars-in-term (lookup-equal fts (pairlis$ formals args))))
                  )
             (not (member-equal (bad-guy-for-alists-equiv-on (free-vars-in-term (lookup-equal fts (pairlis$ formals args))) a1 a2)
                                (non-trivial-formals formals args))))
    :hints (("Goal"
             :use (:instance not-member-equal-of-bad-guy-for-alists-equiv-on-when-not-intersection-equal-alt-gen
                             (keys (free-vars-in-term (lookup-equal fts (pairlis$ formals args))))
                             (set (non-trivial-formals formals args))
                             (diff formals-to-subst)
                             )
             :in-theory (disable intersection-equal-commutative-iff
                                 not-member-equal-of-bad-guy-for-alists-equiv-on-when-not-intersection-equal-alt-gen
                                 )))))

(local (in-theory (disable intersection-equal-commutative-iff))) ; or drop this by rephrasing hyps above

;; Correctness theorem for subst-formal-in-lambda-application.  Shows that it
;; doesn't change the meaning of terms.
(defthm empty-eval-of-subst-formals-in-lambda-application-correct
  (implies (and
             ;; the args being put in for the formals-to-subst cannot mention any of the remaining non-trivial formals:
             ;; this avoid clashes:
             (not (intersection-eq (free-vars-in-terms (map-lookup-equal formals-to-subst (pairlis$ formals args)))
                                   (set-difference-equal (non-trivial-formals formals args) formals-to-subst)))
             (subsetp-equal formals-to-subst (non-trivial-formals formals args)) ; doesn't make sense to subst trivial formals
             (symbol-listp formals)
;             (not (member-equal nil formals))
             (no-duplicatesp-equal formals)
             (equal (len formals) (len args))
             (pseudo-termp body)
             (pseudo-term-listp args)
             (true-listp formals-to-subst)
             (no-nils-in-termp body)
             (no-nils-in-termsp args)
                ;; the lambda must be closed:
             (subsetp-equal (free-vars-in-term body) formals))
           (equal (empty-eval (subst-formals-in-lambda-application formals body args formals-to-subst) a)
                  (empty-eval `((lambda ,formals ,body) ,@args) a)))
  :hints (("[2]Goal" :in-theory (e/d (;make-lambda-application-simple
                                      ;; make-lambda-term-simple
                                      ;; make-lambda-application-simpler
                              ;intersection-equal-of-set-difference-equal-when-subsetp-equal
                                      alists-equiv-on-when-agree-on-bad-guy
                                      lookup-equal-of-append
;                                      empty-eval-cdrs-of-pairlis$
                                      symbolp-when-member-equal-and-symbol-listp
                                      not-member-equal-of-nil-when-no-nils-in-termsp
                                      )
                                     (len
                                      alistp
                                      nthcdr-of-append-gen
                                      strip-cdrs-of-pairlis$
                                      pairlis$-of-append-arg1
                                      ;pairlis$-of-empty-eval-list
                                      no-duplicatesp-equal-when-no-duplicatesp-equal-of-cdr ; looped with trivial ancestors check mod
                                      intersection-equal-when-not-intersection-equal-of-cdr-arg2-iff
                                      ;bad-guy-helper
                                      ))
           ;; :use (:instance bad-guy-helper
           ;;                 (fts (bad-guy-for-alists-equiv-on
           ;;                        (free-vars-in-term body)
           ;;                        (append
           ;;                          (pairlis$
           ;;                            formals-to-subst
           ;;                            (map-lookup-equal
           ;;                              formals-to-subst
           ;;                              (pairlis$
           ;;                                formals
           ;;                                (empty-eval-list
           ;;                                  args
           ;;                                  (append
           ;;                                    (pairlis$ (set-difference-equal formals formals-to-subst)
           ;;                                              (map-lookup-equal
           ;;                                                (set-difference-equal formals formals-to-subst)
           ;;                                                (pairlis$ formals (empty-eval-list args a))))
           ;;                                    (pairlis$
           ;;                                      (set-difference-equal
           ;;                                        (free-vars-in-terms
           ;;                                          (map-lookup-equal formals-to-subst
           ;;                                                            (pairlis$ formals args)))
           ;;                                        (set-difference-equal formals formals-to-subst))
           ;;                                      (empty-eval-list
           ;;                                        (set-difference-equal
           ;;                                          (free-vars-in-terms
           ;;                                            (map-lookup-equal formals-to-subst
           ;;                                                              (pairlis$ formals args)))
           ;;                                          (set-difference-equal formals formals-to-subst))
           ;;                                        a)))))))
           ;;                          (pairlis$
           ;;                            (set-difference-equal formals formals-to-subst)
           ;;                            (map-lookup-equal (set-difference-equal formals formals-to-subst)
           ;;                                              (pairlis$ formals (empty-eval-list args a))))
           ;;                          (pairlis$
           ;;                            (set-difference-equal
           ;;                              (free-vars-in-terms (map-lookup-equal formals-to-subst
           ;;                                                                    (pairlis$ formals args)))
           ;;                              (set-difference-equal formals formals-to-subst))
           ;;                            (empty-eval-list
           ;;                              (set-difference-equal
           ;;                                (free-vars-in-terms (map-lookup-equal formals-to-subst
           ;;                                                                      (pairlis$ formals args)))
           ;;                                (set-difference-equal formals formals-to-subst))
           ;;                              a)))
           ;;                        (pairlis$ formals (empty-eval-list args a)))))
           :cases ((member-equal (bad-guy-for-alists-equiv-on
                                   (free-vars-in-term
                                     (lookup-equal
                                       (bad-guy-for-alists-equiv-on
                                         (free-vars-in-term body)
                                         (append
                                           (pairlis$
                                             formals-to-subst
                                             (map-lookup-equal
                                               formals-to-subst
                                               (pairlis$
                                                 formals
                                                 (empty-eval-list
                                                   args
                                                   (append
                                                     (pairlis$ (set-difference-equal formals formals-to-subst)
                                                               (map-lookup-equal
                                                                 (set-difference-equal formals formals-to-subst)
                                                                 (pairlis$ formals (empty-eval-list args a))))
                                                     (pairlis$
                                                       (set-difference-equal
                                                         (free-vars-in-terms
                                                           (map-lookup-equal formals-to-subst
                                                                             (pairlis$ formals args)))
                                                         (set-difference-equal formals formals-to-subst))
                                                       (empty-eval-list
                                                         (set-difference-equal
                                                           (free-vars-in-terms
                                                             (map-lookup-equal formals-to-subst
                                                                               (pairlis$ formals args)))
                                                           (set-difference-equal formals formals-to-subst))
                                                         a)))))))
                                           (pairlis$
                                             (set-difference-equal formals formals-to-subst)
                                             (map-lookup-equal (set-difference-equal formals formals-to-subst)
                                                               (pairlis$ formals (empty-eval-list args a))))
                                           (pairlis$
                                             (set-difference-equal
                                               (free-vars-in-terms (map-lookup-equal formals-to-subst
                                                                                     (pairlis$ formals args)))
                                               (set-difference-equal formals formals-to-subst))
                                             (empty-eval-list
                                               (set-difference-equal
                                                 (free-vars-in-terms (map-lookup-equal formals-to-subst
                                                                                       (pairlis$ formals args)))
                                                 (set-difference-equal formals formals-to-subst))
                                               a)))
                                         (pairlis$ formals (empty-eval-list args a)))
                                       (pairlis$ formals args)))
                                   (append
                                     (pairlis$
                                       (set-difference-equal formals formals-to-subst)
                                       (map-lookup-equal (set-difference-equal formals formals-to-subst)
                                                         (pairlis$ formals (empty-eval-list args a))))
                                     (pairlis$
                                       (set-difference-equal
                                         (free-vars-in-terms (map-lookup-equal formals-to-subst
                                                                               (pairlis$ formals args)))
                                         (set-difference-equal formals formals-to-subst))
                                       (empty-eval-list
                                         (set-difference-equal
                                           (free-vars-in-terms (map-lookup-equal formals-to-subst
                                                                                 (pairlis$ formals args)))
                                           (set-difference-equal formals formals-to-subst))
                                         a)))
                                   a) (trivial-formals formals args)))
           )
          ("[1]Subgoal 1" :in-theory (e/d (;make-lambda-application-simple
                                           ;; make-lambda-term-simple
                                           ;; make-lambda-application-simpler
                              ;intersection-equal-of-set-difference-equal-when-subsetp-equal
                                           alists-equiv-on-when-agree-on-bad-guy
                                           lookup-equal-of-append
;                                           empty-eval-cdrs-of-pairlis$
                                           symbolp-when-member-equal-and-symbol-listp
                                           not-member-equal-of-nil-when-no-nils-in-termsp
                                           )
                                          (len
                                           alistp
                                           nthcdr-of-append-gen
                                           strip-cdrs-of-pairlis$
                                           pairlis$-of-append-arg1
                                           ;pairlis$-of-empty-eval-list
                                           no-duplicatesp-equal-when-no-duplicatesp-equal-of-cdr ; looped with trivial ancestors check mod
                                           intersection-equal-when-not-intersection-equal-of-cdr-arg2-iff
                                           )))
          ("[1]Subgoal 2" :in-theory (e/d (;make-lambda-application-simple
                                           ;; make-lambda-term-simple
                                           ;; make-lambda-application-simpler
                              ;intersection-equal-of-set-difference-equal-when-subsetp-equal
                                           alists-equiv-on-when-agree-on-bad-guy
                                           lookup-equal-of-append
;                                           empty-eval-cdrs-of-pairlis$
                                           symbolp-when-member-equal-and-symbol-listp
                                           not-member-equal-of-nil-when-no-nils-in-termsp
                                           equal-of-empty-eval-and-empty-eval-when-alists-equiv-on-special-forced
                                           )
                                          (len
                                           alistp
                                           nthcdr-of-append-gen
                                           strip-cdrs-of-pairlis$
                                           pairlis$-of-append-arg1
                                           ;pairlis$-of-empty-eval-list
                                           no-duplicatesp-equal-when-no-duplicatesp-equal-of-cdr ; looped with trivial ancestors check mod
                                           intersection-equal-when-not-intersection-equal-of-cdr-arg2-iff
                                           )))
          ("Goal" :do-not '(generalize eliminate-destructors)
;           :cases ((member-eq formal-to-subst (free-vars-in-term (lookup-equal formal-to-subst (pairlis$ formals args)))))
           :in-theory (e/d (subst-formals-in-lambda-application
;make-lambda-application-simple
                            ;; make-lambda-term-simple
                            ;; make-lambda-application-simpler
                              ;intersection-equal-of-set-difference-equal-when-subsetp-equal
                            alists-equiv-on-when-agree-on-bad-guy
                            lookup-equal-of-append
;                            empty-eval-cdrs-of-pairlis$
                            symbolp-when-member-equal-and-symbol-listp
                            equal-of-empty-eval-and-empty-eval-when-alists-equiv-on-special-forced
                            true-listp-when-symbol-listp-rewrite-unlimited
                            )
                           (len
                            alistp
                            nthcdr-of-append-gen
                            strip-cdrs-of-pairlis$
                            pairlis$-of-append-arg1
                            ;pairlis$-of-empty-eval-list
                            no-duplicatesp-equal-when-no-duplicatesp-equal-of-cdr ; looped with trivial ancestors check mod
                            intersection-equal-when-not-intersection-equal-of-cdr-arg2-iff
                            pairlis$-of-append-and-append
                            empty-eval-list-of-append
                            empty-eval-list-when-symbol-listp
                            empty-eval-list-of-cons
                            )))))

;drop some hyps?
(defthm subsetp-equal-of-free-vars-in-term-of-subst-formals-in-lambda-application
  (implies (and (symbol-listp formals)
                (pseudo-termp body)
                (pseudo-term-listp args)
;                (symbol-listp formals-to-subst) ; drop?
;                (lambdas-closed-in-termp body)
 ;               (lambdas-closed-in-termsp args)
                (subsetp-equal formals-to-subst formals)
                (equal (len args) (len formals))
                ;; the lambda must be closed:
  ;              (subsetp-equal (free-vars-in-term body) formals)
                )
           (subsetp-equal (free-vars-in-term (subst-formals-in-lambda-application formals body args formals-to-subst))
                          (free-vars-in-terms args)))
  :hints (("Goal"; :expand (lambdas-closed-in-termp body)
           :in-theory (enable subst-formals-in-lambda-application lambdas-closed-in-termp
                              free-vars-in-terms-when-symbol-listp))))
