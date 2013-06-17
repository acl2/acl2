


(in-package "GL")

(include-book "shape-spec-defs")
(include-book "gtypes")
(include-book "gl-doc-string")
(include-book "symbolic-arithmetic-fns")

(local (include-book "gtype-thms"))
(local (include-book "data-structures/no-duplicates" :dir :system))
(local (include-book "tools/mv-nth" :dir :system))
(local (include-book "centaur/bitops/ihsext-basics" :dir :system))
(local (include-book "arithmetic/top-with-meta" :dir :system))
(local (include-book "centaur/misc/fast-alists" :dir :system))


(defund slice-to-bdd-env (slice env)
  (declare (xargs :guard (and (alistp slice)
                              (nat-listp (strip-cars slice))
                              (true-listp env))
                  :verify-guards nil))
  (if (atom slice)
      env
    (bfr-set-var (caar slice) (cdar slice)
                 (slice-to-bdd-env (cdr slice) env))))

;; (local
;;  (defthm true-listp-slice-to-bdd-env
;;    (implies (true-listp env)
;;             (true-listp (slice-to-bdd-env slice env)))
;;    :hints(("Goal" :in-theory (enable slice-to-bdd-env)))))

(verify-guards slice-to-bdd-env
               :hints (("goal" :in-theory (enable nat-listp))))

(local
 (defthm nat-listp-true-listp
   (implies (nat-listp x)
            (true-listp x))
   :hints(("Goal" :in-theory (enable nat-listp)))
   :rule-classes (:rewrite :forward-chaining)))


(defund number-spec-indices (nspec)
  (declare (xargs :guard (number-specp nspec)
                  :guard-hints (("goal" :in-theory (enable number-specp)))))
  (append (car nspec)
          (and (consp (cdr nspec))
               (append (cadr nspec)
                       (and (consp (cddr nspec))
                            (append (caddr nspec)
                                    (and (consp (cdddr nspec))
                                         (cadddr nspec))))))))

(local
 (defthm nat-listp-append
   (implies (and (nat-listp a)
                 (nat-listp b))
            (nat-listp (append a b)))
   :hints(("Goal" :in-theory (enable nat-listp append)))))

(local
 (defthm true-listp-append
   (implies (true-listp b)
            (true-listp (append a b)))))

(defthm nat-listp-number-spec-indices
  (implies (number-specp nspec)
           (nat-listp (number-spec-indices nspec)))
  :hints(("Goal" :in-theory (enable number-specp number-spec-indices))))

(defund shape-spec-indices (x)
  (declare (xargs :guard (shape-specp x)
                  :verify-guards nil))
  (if (atom x)
      nil
    (pattern-match x
      ((g-number nspec)
       (number-spec-indices nspec))
      ((g-integer sign bits &)
       (cons sign bits))
      ((g-integer? sign bits & intp)
       (list* intp sign bits))
      ((g-boolean n) (list n))
      ((g-var &) nil)
      ((g-ite if then else)
       (append (shape-spec-indices if)
               (shape-spec-indices then)
               (shape-spec-indices else)))
      ((g-concrete &) nil)
      ((g-call & args & &) (shape-spec-indices args))
      (& (append (shape-spec-indices (car x))
                 (shape-spec-indices (cdr x)))))))

(defthm nat-listp-shape-spec-indices
  (implies (shape-specp x)
           (nat-listp (shape-spec-indices x)))
  :hints(("Goal" :in-theory (enable shape-specp shape-spec-indices
                                    nat-listp))))

(verify-guards shape-spec-indices
               :hints (("goal" :in-theory (enable shape-specp))))

(defund shape-spec-vars (x)
  (declare (xargs :guard (shape-specp x)
                  :verify-guards nil))
  (if (atom x)
      nil
    (pattern-match x
      ((g-number &) nil)
      ((g-integer & & v) (list v))
      ((g-integer? & & v &) (list v))
      ((g-boolean &) nil)
      ((g-var v) (list v))
      ((g-ite if then else)
       (append (shape-spec-vars if)
               (shape-spec-vars then)
               (shape-spec-vars else)))
      ((g-concrete &) nil)
      ((g-call & args & &) (shape-spec-vars args))
      (& (append (shape-spec-vars (car x))
                 (shape-spec-vars (cdr x)))))))

(local
 (defthm true-listp-shape-spec-vars
   (true-listp (shape-spec-vars x))
   :hints(("Goal" :in-theory (enable shape-spec-vars)))))

(verify-guards shape-spec-vars
               :hints(("Goal" :in-theory (enable shape-specp))))





(defund numlist-to-vars (lst)
  (declare (xargs :guard (nat-listp lst)
                  :guard-hints (("goal" :in-theory (enable nat-listp)))))
  (if (atom lst)
      nil
    (cons (bfr-var (car lst))
          (numlist-to-vars (cdr lst)))))

(defund num-spec-to-num-gobj (nspec)
  (declare (xargs :guard (number-specp nspec)
                  :guard-hints (("goal" :in-theory (enable number-specp)))))
  (cons (numlist-to-vars (car nspec))
        (and (consp (cdr nspec))
             (cons (numlist-to-vars (cadr nspec))
                   (and (consp (cddr nspec))
                        (cons (numlist-to-vars (caddr nspec))
                              (and (consp (cdddr nspec))
                                   (list (numlist-to-vars
                                          (cadddr nspec))))))))))

(defund shape-spec-to-gobj (x)
  (declare (xargs :guard (shape-specp x)
                  :guard-hints (("goal" :in-theory (enable shape-specp)))))
  (if (atom x)
      x
    (pattern-match x
      ((g-number nspec)
       (g-number (num-spec-to-num-gobj nspec)))
      ((g-integer sign bits var)
       (g-apply 'logapp
                (list (len bits)
                      (g-number (list (append (numlist-to-vars bits) (list nil))))
                      (g-apply 'int-set-sign
                               (list (g-boolean (bfr-var sign))
                                     (g-var var))))))
      ((g-integer? sign bits var intp)
       (g-apply 'maybe-integer
                (list
                 (g-apply 'logapp
                          (list (len bits)
                                (g-number (list (append (numlist-to-vars bits) (list nil))))
                                (g-apply 'int-set-sign
                                         (list (g-boolean (bfr-var sign))
                                               (g-var var)))))
                 (g-var var)
                 (g-boolean (bfr-var intp)))))
      ((g-boolean n) (g-boolean (bfr-var n)))
      ((g-var &) x)
      ((g-ite if then else)
       (g-ite (shape-spec-to-gobj if)
              (shape-spec-to-gobj then)
              (shape-spec-to-gobj else)))
      ((g-concrete &) x)
      ((g-call fn args & &) (g-apply fn (shape-spec-to-gobj args)))
      (& (gl-cons (shape-spec-to-gobj (car x))
                  (shape-spec-to-gobj (cdr x)))))))






;; (local
;;  (defthm bfr-listp-numlist-to-vars
;;    (implies (nat-listp x)
;;             (bfr-listp (numlist-to-vars x)))
;;    :hints(("Goal" :in-theory (enable numlist-to-vars nat-listp)))))

;; (local
;;  (defthm wf-g-numberp-num-spec-to-num-gobj
;;    (implies (number-specp x)
;;             (wf-g-numberp (num-spec-to-num-gobj x)))
;;    :hints(("Goal" :in-theory (enable wf-g-numberp num-spec-to-num-gobj
;;                                      number-specp)))))

;; (defthm gobjectp-shape-spec-to-gobj
;;   (implies (shape-specp x)
;;            (gobjectp (shape-spec-to-gobj x)))
;;   :hints(("Goal" :in-theory
;;           (enable gobjectp-def shape-specp shape-spec-to-gobj g-var-p
;;                   g-concrete-p tag))))


(local
 (defthm subsetp-equal-append
   (equal (subsetp-equal (append x y) z)
          (and (subsetp-equal x z)
               (subsetp-equal y z)))))


(local
 (defthm hons-assoc-equal-append
   (implies (and (alistp v1)
                 (member-equal key (strip-cars v1)))
            (equal (hons-assoc-equal key (append v1 v2))
                   (hons-assoc-equal key v1)))
   :hints(("Goal" :in-theory (enable hons-assoc-equal)))))

(local
 (defthm hons-assoc-equal-append-2
   (implies (and (alistp v1)
                 (not (member-equal key (strip-cars v1))))
            (equal (hons-assoc-equal key (append v1 v2))
                   (hons-assoc-equal key v2)))
   :hints(("Goal" :in-theory (enable hons-assoc-equal)))))

(local
 (defthm member-strip-cars-nth-slice-1
   (implies (and (integerp n)
                 (<= 0 n)
                 (member-equal n (strip-cars bsl1)))
            (equal (bfr-lookup n (slice-to-bdd-env (append bsl1 bsl2) env))
                   (bfr-lookup n (slice-to-bdd-env bsl1 env))))
   :hints(("Goal" :in-theory (enable slice-to-bdd-env)))))

(local
 (defthm member-strip-cars-nth-slice-2
   (implies (and (integerp n)
                 (<= 0 n)
                 (nat-listp (strip-cars bsl1))
                 (not (member-equal n (strip-cars bsl1))))
            (equal (bfr-lookup n (slice-to-bdd-env (append bsl1 bsl2) env))
                   (bfr-lookup n (slice-to-bdd-env bsl2 env))))
   :hints(("Goal" :in-theory (enable strip-cars slice-to-bdd-env nat-listp)))))



;; (local
;;  (defthm bfr-eval-irrelevant-update
;;    (equal (bfr-eval (bfr-var n) (bfr-set-var m x env))
;;           (if (equal (nfix n) (nfix m))
;;               (if x t nil)
;;             (bfr-eval (bfr-var n) env)))))

(local
 (defthm bfr-eval-list-numlist-subset-append
   (implies (and (nat-listp lst)
                 (subsetp-equal lst (strip-cars bsl1)))
            (equal (bfr-eval-list (numlist-to-vars lst)
                                  (slice-to-bdd-env (append bsl1 bsl2) env))
                   (bfr-eval-list (numlist-to-vars lst)
                                  (slice-to-bdd-env bsl1 env))))
   :hints(("Goal" :in-theory (enable numlist-to-vars
                                     slice-to-bdd-env
                                     subsetp-equal
                                     nat-listp)
           :induct (numlist-to-vars lst)))))

(local
 (defthm bfr-eval-list-numlist-no-intersect-append
   (implies (and (nat-listp lst)
                 (nat-listp (strip-cars bsl1))
                 (not (intersectp-equal lst (strip-cars bsl1))))
            (equal (bfr-eval-list (numlist-to-vars lst)
                                  (slice-to-bdd-env (append bsl1 bsl2) env))
                   (bfr-eval-list (numlist-to-vars lst)
                                  (slice-to-bdd-env bsl2 env))))
   :hints(("Goal" :in-theory (enable numlist-to-vars
                                     slice-to-bdd-env
                                     nat-listp)
           :induct (numlist-to-vars lst)))))

;; (local
;;  (defthm g-boolean-p-gobj-fix
;;    (equal (g-boolean-p (gobj-fix x))
;;           (and (gobjectp x)
;;                (g-boolean-p x)))
;;    :hints(("Goal" :in-theory (enable gobj-fix)))))

;; (local
;;  (defthm g-number-p-gobj-fix
;;    (equal (g-number-p (gobj-fix x))
;;           (and (gobjectp x)
;;                (g-number-p x)))
;;    :hints(("Goal" :in-theory (enable gobj-fix)))))

;; (local
;;  (defthm g-ite-p-gobj-fix
;;    (equal (g-ite-p (gobj-fix x))
;;           (and (gobjectp x)
;;                (g-ite-p x)))
;;    :hints(("Goal" :in-theory (enable gobj-fix)))))

;; (local
;;  (defthm g-var-p-gobj-fix
;;    (equal (g-var-p (gobj-fix x))
;;           (and (gobjectp x)
;;                (g-var-p x)))
;;    :hints(("Goal" :in-theory (enable gobj-fix)))))

;; (local
;;  (defthm g-apply-p-gobj-fix
;;    (equal (g-apply-p (gobj-fix x))
;;           (and (gobjectp x)
;;                (g-apply-p x)))
;;    :hints(("Goal" :in-theory (enable gobj-fix)))))

;; (local
;;  (defthm g-concrete-p-gobj-fix
;;    (equal (g-concrete-p (gobj-fix x))
;;           (or (not (gobjectp x))
;;               (g-concrete-p x)))
;;    :hints(("Goal" :in-theory (enable gobj-fix)))))




(def-eval-g sspec-geval
  (logapp int-set-sign maybe-integer
          cons car cdr consp if not equal nth len iff
          shape-spec-slice-to-env
          ss-append-envs
          shape-spec-obj-in-range-iff
          shape-spec-obj-in-range
          shape-spec-env-slice
          shape-spec-iff-env-slice))



(local (in-theory (disable logapp integer-length
                           loghead logtail sspec-geval
                           acl2::member-equal-of-strip-cars-when-member-equal-of-hons-duplicated-members-aux
                           acl2::consp-of-car-when-alistp
                           sets::double-containment)))

(defun expands-with-hint (def expands)
  (if (atom expands)
      nil
    (cons `(:with ,def ,(car expands))
          (expands-with-hint def (cdr expands)))))

(defthm bfr-eval-list-of-append
  (equal (bfr-eval-list (append a b) env)
         (append (bfr-eval-list a env)
                 (bfr-eval-list b env))))

(local (in-theory (enable gl-cons)))

(local
 (defthm shape-spec-to-gobj-eval-slice-subset-append-1
   (implies (and (shape-specp x)
                 (alistp vsl1)
                 (subsetp-equal (shape-spec-indices x)
                                (strip-cars bsl1)))
            (equal (sspec-geval
                    (shape-spec-to-gobj x)
                    (cons (slice-to-bdd-env
                           (append bsl1 bsl2) env)
                          vsl1))
                   (sspec-geval
                    (shape-spec-to-gobj x)
                    (cons (slice-to-bdd-env
                           bsl1 env)
                          vsl1))))
   :hints(("Goal" :in-theory (e/d (break-g-number
                                   num-spec-to-num-gobj
                                   number-spec-indices
                                   number-specp
                                   subsetp-equal
                                   (:induction shape-spec-to-gobj))
                                  (member-equal
                                   acl2::list-fix-when-true-listp
                                   acl2::list-fix-when-len-zero
                                   acl2::consp-by-len
                                   boolean-listp
                                   binary-append))
           :induct (shape-spec-to-gobj x)
           :expand ((shape-spec-to-gobj x)
                    (shape-spec-indices x)
                    (shape-spec-vars x)
                    (shape-specp x)))
          (and stable-under-simplificationp
               (let ((calls (acl2::find-calls-of-fns-term
                             (car (last clause)) '(sspec-geval) nil)))
                 (and calls
                      `(:computed-hint-replacement t
                        :expand ,(expands-with-hint 'sspec-geval calls)))))
          (and stable-under-simplificationp
               '(:in-theory (enable g-boolean->bool
                                    g-apply->fn
                                    g-apply->args))))))


(local
 (defthm shape-spec-to-gobj-eval-slice-subset-append-2
   (implies (and (shape-specp x)
                 (alistp vsl1)
                 (subsetp-equal (shape-spec-vars x)
                                (strip-cars vsl1)))
            (equal (sspec-geval
                    (shape-spec-to-gobj x)
                    (cons (slice-to-bdd-env
                           bsl1 env)
                          (append vsl1 vsl2)))
                   (sspec-geval
                    (shape-spec-to-gobj x)
                    (cons (slice-to-bdd-env
                           bsl1 env)
                          vsl1))))
   :hints(("Goal" :in-theory (e/d (break-g-number
                                   num-spec-to-num-gobj
                                   number-spec-indices
                                   number-specp
                                   subsetp-equal
                                   hons-assoc-equal
                                   strip-cars
                                   (:induction shape-spec-to-gobj))
                                  (member-equal
                                   acl2::list-fix-when-true-listp
                                   acl2::list-fix-when-len-zero
                                   acl2::consp-by-len
                                   boolean-listp
                                   binary-append))
           :induct (shape-spec-to-gobj x)
           :expand ((shape-spec-to-gobj x)
                    (shape-spec-indices x)
                    (shape-spec-vars x)
                    (shape-specp x)))
          (and stable-under-simplificationp
               (let ((calls (acl2::find-calls-of-fns-term
                             (car (last clause)) '(sspec-geval) nil)))
                 `(:computed-hint-replacement t
                   :expand ,(expands-with-hint 'sspec-geval calls)))))))



(local
 (defthm shape-spec-to-gobj-eval-slice-no-intersect-append-1
   (implies (and (shape-specp x)
                 (alistp vsl1)
                 (nat-listp (strip-cars bsl1))
                 (not (intersectp-equal
                       (shape-spec-indices x)
                       (strip-cars bsl1))))
            (equal (sspec-geval
                    (shape-spec-to-gobj x)
                    (cons (slice-to-bdd-env
                           (append bsl1 bsl2) env)
                          vsl1))
                   (sspec-geval
                    (shape-spec-to-gobj x)
                    (cons (slice-to-bdd-env
                           bsl2 env)
                          vsl1))))
   :hints(("Goal" :in-theory (e/d (break-g-number
                                   num-spec-to-num-gobj
                                   number-spec-indices
                                   number-specp
                                   (:induction shape-spec-to-gobj))
                                  (member-equal
                                   acl2::list-fix-when-true-listp
                                   acl2::list-fix-when-len-zero
                                   acl2::consp-by-len
                                   boolean-listp
                                   binary-append))
           :induct (shape-spec-to-gobj x)
           :expand ((shape-spec-to-gobj x)
                    (shape-spec-indices x)
                    (shape-spec-vars x)
                    (shape-specp x)))
          (and stable-under-simplificationp
               (let ((calls (acl2::find-calls-of-fns-term
                             (car (last clause)) '(sspec-geval) nil)))
                 `(:computed-hint-replacement t
                   :expand ,(expands-with-hint 'sspec-geval calls)))))))


(local
 (defthm shape-spec-to-gobj-eval-slice-no-intersect-append-2
   (implies (and (shape-specp x)
                 (alistp vsl1)
                 (not (intersectp-equal (shape-spec-vars x)
                                        (strip-cars vsl1))))
            (equal (sspec-geval
                    (shape-spec-to-gobj x)
                    (cons (slice-to-bdd-env
                           bsl1 env)
                          (append vsl1 vsl2)))
                   (sspec-geval
                    (shape-spec-to-gobj x)
                    (cons (slice-to-bdd-env
                           bsl1 env)
                          vsl2))))
   :hints(("Goal" :in-theory (e/d (break-g-number
                                   num-spec-to-num-gobj
                                   number-spec-indices
                                   number-specp
                                   subsetp-equal
                                   (:induction shape-spec-to-gobj))
                                  (member-equal
                                   acl2::list-fix-when-true-listp
                                   acl2::list-fix-when-len-zero
                                   acl2::consp-by-len
                                   acl2::hons-assoc-equal-append
                                   boolean-listp
                                   binary-append))
           :induct (shape-spec-to-gobj x)
           :expand ((shape-spec-to-gobj x)
                    (shape-spec-indices x)
                    (shape-spec-vars x)
                    (shape-specp x)))
          (and stable-under-simplificationp
               (let ((calls (acl2::find-calls-of-fns-term
                             (car (last clause)) '(sspec-geval) nil)))
                 `(:computed-hint-replacement t
                   :expand ,(expands-with-hint 'sspec-geval calls)))))))


(local
 (defthm alistp-append
   (implies (and (alistp a) (alistp b))
            (alistp (append a b)))))

(local
 (defthm alistp-integer-env-slice
   (alistp (mv-nth 1 (integer-env-slice n m)))
   :hints(("Goal" :in-theory (enable integer-env-slice)))))

(local
 (defthm alistp-natural-env-slice
   (alistp (mv-nth 1 (natural-env-slice n m)))
   :hints(("Goal" :in-theory (enable natural-env-slice)))))

(local
 (defthm alistp-number-spec-env-slice
   (alistp (mv-nth 1 (number-spec-env-slice n m)))
   :hints(("Goal" :in-theory (enable number-spec-env-slice)))))

(local
 (defthm alistp-shape-spec-arbitrary-slice-1
   (alistp (mv-nth 1 (shape-spec-arbitrary-slice x)))
   :hints(("Goal" :in-theory (enable shape-spec-arbitrary-slice)))))

(local
 (defthm alistp-shape-spec-iff-env-slice-2
   (alistp (mv-nth 2 (shape-spec-iff-env-slice x obj)))
   :hints(("Goal" :in-theory (enable shape-spec-iff-env-slice)))))

(local
 (defthm alistp-shape-spec-env-slice-2
   (alistp (mv-nth 2 (shape-spec-env-slice x obj)))
   :hints(("Goal" :in-theory (enable shape-spec-env-slice)))))

(local
 (defthm strip-cars-append
   (equal (strip-cars (append a b))
          (append (strip-cars a) (strip-cars b)))))


(local
 (defthm subsetp-equal-append2
   (implies (or (subsetp-equal x y)
                (subsetp-equal x z))
            (subsetp-equal x (append y z)))))

(local
 (defthm shape-spec-vars-subset-cars-arbitrary-env-slice
   (equal (strip-cars (mv-nth 1 (shape-spec-arbitrary-slice x)))
          (shape-spec-vars x))
   :hints(("Goal" :in-theory (enable shape-spec-vars
                                     shape-spec-arbitrary-slice)))))

(local
 (defthm shape-spec-vars-subset-cars-iff-env-slice
   (equal
    (strip-cars (mv-nth 2 (shape-spec-iff-env-slice x obj)))
    (shape-spec-vars x))
   :hints(("Goal" :in-theory (enable shape-spec-iff-env-slice
                                     shape-spec-vars)))))

(local
 (defthm shape-spec-vars-subset-cars-env-slice
   (equal
    (strip-cars (mv-nth 2 (shape-spec-env-slice x obj)))
    (shape-spec-vars x))
   :hints(("Goal" :in-theory (enable shape-spec-env-slice
                                     shape-spec-vars)))))

(local
 (defthm subsetp-cars-integer-env-slice
   (implies (nat-listp n)
            (equal (strip-cars (mv-nth 1 (integer-env-slice n m))) n))
   :hints(("Goal" :in-theory (enable integer-env-slice nat-listp)))))

(local
 (defthm subsetp-cars-natural-env-slice
   (implies (nat-listp n)
            (equal (strip-cars (mv-nth 1 (natural-env-slice n m))) n))
   :hints(("Goal" :in-theory (enable natural-env-slice nat-listp)))))


(local
 (defthm nat-listp-append-nil
   (implies (nat-listp x)
            (equal (append x nil) x))
   :hints(("Goal" :in-theory (enable nat-listp)))))

(local
 (defthm number-spec-indices-subset-cars-number-spec-env-slice
   (implies (number-specp n)
            (equal (strip-cars (mv-nth 1 (number-spec-env-slice n m)))
                   (number-spec-indices n)))
   :hints(("Goal" :in-theory (enable number-spec-env-slice
                                     number-spec-indices
                                     number-specp)))))


(local
 (defthm shape-spec-indices-subset-cars-arbitrary-env-slice
   (implies (shape-specp x)
            (equal (strip-cars (mv-nth 0 (shape-spec-arbitrary-slice x)))
                   (shape-spec-indices x)))
   :hints (("goal" :in-theory (enable shape-spec-arbitrary-slice
                                      shape-spec-indices
                                      shape-specp)))))


(local
 (defthm shape-spec-indices-subset-cars-iff-env-slice
   (implies (shape-specp x)
            (equal (strip-cars (mv-nth 1 (shape-spec-iff-env-slice x obj)))
                   (shape-spec-indices x)))
   :hints (("goal" :in-theory (enable shape-spec-iff-env-slice
                                      shape-spec-indices
                                      shape-specp)))))

(local
 (defthm shape-spec-indices-subset-cars-env-slice
   (implies (shape-specp x)
            (equal (strip-cars (mv-nth 1 (shape-spec-env-slice x obj)))
                   (shape-spec-indices x)))
   :hints (("goal" :in-theory (enable shape-spec-env-slice
                                      shape-spec-indices
                                      shape-specp)))))

(local
 (defthm subsetp-equal-cons-cdr
   (implies (subsetp-equal x y)
            (subsetp-equal x (cons z y)))))

(local
 (defthm subsetp-equal-when-equal
   (subsetp-equal x x)))


;; (local(defthm no-intersect-cons-cdr
;;   (implies (and (not (intersectp-equal a b))
;;                 (not (member-equal c a)))
;;            (not (intersectp-equal a (cons c b)))))

;; (defthm no-intersect-non-cons
;;   (implies (atom b)
;;            (not (intersectp-equal a b))))

(local
 (defthm nat-listp-append
   (implies (and (nat-listp a)
                 (nat-listp b))
            (nat-listp (append a b)))
   :hints(("Goal" :in-theory (enable nat-listp)))))





(local
 (defthm sspec-geval-of-g-ite
   (equal (sspec-geval (g-ite if then else) env)
          (if (sspec-geval if env)
              (sspec-geval then env)
            (sspec-geval else env)))
   :hints(("Goal" :in-theory (enable sspec-geval)))))


(local
 (encapsulate nil

   (defthm sspec-geval-when-g-concrete-tag
     (implies (equal (tag x) :g-concrete)
              (equal (sspec-geval x env)
                     (g-concrete->obj x)))
     :hints(("Goal" :in-theory (e/d (tag sspec-geval))))
     :rule-classes ((:rewrite :backchain-limit-lst 0)))))


(local
 (encapsulate nil
   (defthm sspec-geval-when-g-var-tag
     (implies (equal (tag x) :g-var)
              (equal (sspec-geval x env)
                     (cdr (hons-assoc-equal (g-var->name x) (cdr env)))))
     :hints(("Goal" :in-theory (enable tag sspec-geval))))))

(local (in-theory (disable member-equal equal-of-booleans-rewrite binary-append
                           intersectp-equal subsetp-equal)))

;; (in-theory (disable no-duplicates-append-implies-no-intersect))

(local
 (encapsulate nil
   (local (in-theory (disable sets::double-containment
                              acl2::no-duplicatesp-equal-non-cons
                              acl2::no-duplicatesp-equal-when-atom
                              acl2::subsetp-car-member
                              acl2::append-when-not-consp
                              tag-when-atom
                              sspec-geval)))
   (defthm shape-spec-to-gobj-eval-iff-slice
     (implies (and (shape-specp x)
                   (no-duplicatesp (shape-spec-indices x))
                   (no-duplicatesp (shape-spec-vars x))
                   (mv-nth 0 (shape-spec-iff-env-slice x obj)))
              (iff (sspec-geval
                    (shape-spec-to-gobj x)
                    (cons (slice-to-bdd-env
                           (mv-nth 1 (shape-spec-iff-env-slice x obj))
                           env)
                          (mv-nth 2 (shape-spec-iff-env-slice x obj))))
                   obj))
     :hints(("Goal" :in-theory (enable (:induction shape-spec-iff-env-slice))
             :induct (shape-spec-iff-env-slice x obj)
             :expand ((:free (obj) (shape-spec-iff-env-slice x obj))
                      (shape-spec-indices x)
                      (shape-spec-vars x)
                      (shape-spec-to-gobj x)
                      (shape-specp x)
                      (:free (a b env)
                             (sspec-geval (cons a b) env))))
            (and stable-under-simplificationp
                 '(:in-theory (enable sspec-geval)))
            (and stable-under-simplificationp
                 '(:in-theory (enable slice-to-bdd-env sspec-geval)))))))

(local
 (defthm bfr-eval-list-numlist-update-non-member
   (implies (and (natp n) (nat-listp lst)
                 (not (member-equal n lst)))
            (equal (bfr-eval-list (numlist-to-vars lst)
                                  (bfr-set-var n x env))
                   (bfr-eval-list (numlist-to-vars lst) env)))
   :hints(("Goal" :in-theory (enable numlist-to-vars bfr-eval-list
                                     nat-listp member-equal)))))


(local
 (defthm consp-numlist-to-vars
   (equal (consp (numlist-to-vars x))
          (consp x))
   :hints(("Goal" :in-theory (enable numlist-to-vars)))))



(local
 (defthm v2i-redef
   (equal (v2i x)
          (if (atom x)
              0
            (if (atom (cdr x))
                (if (car x) -1 0)
              (logcons (if (car x) 1 0) (v2i (cdr x))))))
   :hints(("Goal" :in-theory (enable v2i acl2::ash**))
          (and stable-under-simplificationp
               '(:in-theory (enable logcons))))
   :rule-classes ((:definition :clique (v2i)
                   :controller-alist ((v2i t))))))

(local
 (defthm v2n-redef
   (equal (v2n x)
          (if (atom x)
              0
            (logcons (if (car x) 1 0) (v2n (cdr x)))))
   :hints(("Goal" :in-theory (enable v2n acl2::ash**))
          (and stable-under-simplificationp
               '(:in-theory (enable logcons))))
   :rule-classes ((:definition :clique (v2n)
                   :controller-alist ((v2n t))))))

(local
 (encapsulate nil
   (local (in-theory (e/d* (acl2::ihsext-recursive-redefs) (floor))))
   (defthm eval-slice-integer-env-slice
     (implies (and (mv-nth 0 (integer-env-slice lst n))
                   (no-duplicatesp lst)
                   (integerp n)
                   (nat-listp lst))
              (equal (v2i (bfr-eval-list
                           (numlist-to-vars lst)
                           (slice-to-bdd-env (mv-nth 1 (integer-env-slice lst n)) env)))
                     n))
     :hints(("Goal" :in-theory (enable integer-env-slice
                                       numlist-to-vars
                                       bfr-eval-list
                                       v2i nat-listp
                                       slice-to-bdd-env
                                       integer-env-slice
                                       logbitp)
             :induct (integer-env-slice lst n))))

   (defthm eval-slice-natural-env-slice
     (implies (and (mv-nth 0 (natural-env-slice lst n))
                   (no-duplicatesp lst)
                   (natp n)
                   (nat-listp lst))
              (equal (v2n (bfr-eval-list
                           (numlist-to-vars lst)
                           (slice-to-bdd-env (mv-nth 1 (natural-env-slice lst n)) env)))
                     n))
     :hints(("Goal" :in-theory (enable natural-env-slice
                                       numlist-to-vars
                                       bfr-eval-list
                                       v2n nat-listp
                                       slice-to-bdd-env
                                       natural-env-slice
                                       logbitp)
             :induct (natural-env-slice lst n))))


   (defthm realpart-when-imagpart-0
     (implies (and (acl2-numberp x)
                   (equal (imagpart x) 0))
              (equal (realpart x) x)))

   (defthm numerator-when-denominator-1
     (implies (and (rationalp x)
                   (equal (denominator x) 1))
              (equal (numerator x) x)))


   (defthm integerp-when-denominator-1
     (implies (rationalp x)
              (equal (equal (denominator x) 1)
                     (integerp x))))))


;; (local
;;  (defthmd g-var-p-implies-gobjectp
;;    (implies (g-var-p x)
;;             (gobjectp x))
;;    :hints (("goal" :in-theory (enable gobjectp-def g-var-p tag)))
;;    :rule-classes ((:rewrite :backchain-limit-lst 0))))

;; (local
;;  (defthm gobjectp-g-number
;;    (implies (wf-g-numberp x)
;;             (gobjectp (g-number x)))
;;    :hints(("Goal" :in-theory (enable gobjectp-def g-number-p tag)))))

;; (local
;;  (defthmd g-concrete-p-gobjectp1
;;    (implies (g-concrete-p x)
;;             (gobjectp x))
;;    :hints(("Goal" :in-theory (enable gobjectp-def g-concrete-p tag)))
;;    :rule-classes ((:rewrite :backchain-limit-lst 0))))

;; (local (defthm loghead-non-integer
;;          (implies (not (integerp x))
;;                   (equal (loghead n x) 0))
;;          :hints(("Goal" :in-theory (enable loghead)))
;;          :rule-classes ((:rewrite :backchain-limit-lst 0))))

;; (local (defthm logcdr-non-integer
;;          (implies (not (integerp x))
;;                   (equal (logcdr x) 0))
;;          :hints(("Goal" :in-theory (enable logcdr)))))


(local (defun cdr-logcdr (bits x)
         (if (atom bits)
             x
           (cdr-logcdr (cdr bits) (logcdr x)))))

(defthm natural-env-slice-ok-of-loghead
  (mv-nth 0 (natural-env-slice bits (loghead (len bits) x)))
  :hints(("Goal" :in-theory (enable len acl2::loghead** acl2::logtail**)
          :expand ((:free (x)(natural-env-slice bits x)))
          :induct (cdr-logcdr bits x))))

(defthm v2i-of-append
  (implies (consp b)
           (equal (v2i (append a b))
                  (logapp (len a) (v2n a) (v2i b))))
  :hints(("Goal" :in-theory (e/d* (acl2::ihsext-recursive-redefs append len))
          :induct (append a b))))

(defthm len-bfr-eval-list
  (equal (len (bfr-eval-list x env)) (len x)))

(defthm len-numlist-to-vars
  (equal (len (numlist-to-vars bits)) (len bits))
  :hints(("Goal" :in-theory (enable numlist-to-vars))))

(defthm logapp-of-loghead
  (equal (logapp n (loghead n x) y)
         (logapp n x y))
  :hints(("Goal" :in-theory (enable* acl2::ihsext-inductions
                                     acl2::ihsext-recursive-redefs))))

(defthm logapp-to-logtail
  (equal (logapp n obj (logtail n obj))
         (ifix obj))
  :hints(("Goal" :in-theory (enable* acl2::ihsext-inductions
                                     acl2::ihsext-recursive-redefs))))

(defthm int-set-sign-of-own-sign
  (implies (integerp x)
           (equal (int-set-sign (< x 0) x)
                  x))
  :hints(("Goal" :in-theory (e/d* (int-set-sign
                                   acl2::ihsext-inductions
                                   acl2::ihsext-recursive-redefs))))
  :otf-flg t)


(local
 (encapsulate nil
   (local (in-theory
           (e/d () (;; gobjectp-tag-rw-to-types
                    ;; gobjectp-ite-case
                    ;; sspec-geval-non-gobjectp
                    break-g-number
                    sets::double-containment))))

   (local (defthm g-keyword-symbolp-of-shape-spec-to-gobj
            (equal (g-keyword-symbolp (shape-spec-to-gobj x))
                   (g-keyword-symbolp x))
            :hints(("Goal" :in-theory (enable shape-spec-to-gobj)))))
   (local (defthm not-equal-shape-spec-to-gobj-keyword
            (implies (and (not (g-keyword-symbolp x))
                          (g-keyword-symbolp y))
                     (not (equal (shape-spec-to-gobj x) y)))
            :rule-classes ((:rewrite :backchain-limit-lst (0 1)))))
   (local (defthm g-keyword-symbolp-compound-recognizer
            (implies (g-keyword-symbolp x)
                     (and (symbolp x)
                          (not (booleanp x))))
            :rule-classes :compound-recognizer))
   (local (defthm shape-spec-to-gobj-when-atom
            (implies (atom x)
                     (equal (shape-spec-to-gobj x) x))
            :hints(("Goal" :in-theory (enable shape-spec-to-gobj)))
            :rule-classes ((:rewrite :backchain-limit-lst 0))))


   (local (defthm kwote-lst-of-cons
            (equal (kwote-lst (cons a b))
                   (cons (kwote a) (kwote-lst b)))))
   (local (in-theory (disable kwote-lst)))

   (defthm shape-spec-to-gobj-eval-slice
     (implies (and (shape-specp x)
                   (no-duplicatesp (shape-spec-indices x))
                   (no-duplicatesp (shape-spec-vars x))
                   (mv-nth 0 (shape-spec-env-slice x obj)))
              (equal (sspec-geval
                      (shape-spec-to-gobj x)
                      (cons (slice-to-bdd-env
                             (mv-nth 1 (shape-spec-env-slice x obj))
                             env)
                            (mv-nth 2 (shape-spec-env-slice x obj))))
                     obj))
     :hints(("Goal" ;; :in-theory (enable shape-spec-to-gobj
                    ;;                    shape-spec-indices
                    ;;                    shape-spec-vars
                    ;;                    shape-spec-env-slice
                    ;;                    shape-specp)
             :in-theory (enable (:i shape-spec-env-slice))
             :expand ((shape-spec-to-gobj x)
                      (shape-spec-to-gobj obj)
                      (shape-spec-indices x)
                      (shape-spec-vars x)
                      (shape-specp x)
                      (shape-spec-env-slice x obj))
             :induct (shape-spec-env-slice x obj))
            (and stable-under-simplificationp
                 '(:in-theory (enable slice-to-bdd-env)
                   :expand ((:free (x y env)
                             (sspec-geval (cons x y) env)))))
            (and stable-under-simplificationp
                 '(:in-theory (enable sspec-geval break-g-number
                                      number-spec-env-slice
                                      number-specp
                                      number-spec-indices
                                      num-spec-to-num-gobj)))))))
  
(local
 (defthm alistp-shape-spec-arbitrary-slice-0
   (alistp (mv-nth 0 (shape-spec-arbitrary-slice x)))
   :hints(("Goal" :in-theory (enable shape-spec-arbitrary-slice)))))

(local
 (defthm alistp-shape-spec-iff-env-slice-1
   (alistp (mv-nth 1 (shape-spec-iff-env-slice x obj)))
   :hints(("Goal" :in-theory (enable shape-spec-iff-env-slice)))))


(local
 (defthm alistp-shape-spec-env-slice-1
   (alistp (mv-nth 1 (shape-spec-env-slice x obj)))
   :hints(("Goal" :in-theory (enable shape-spec-env-slice)))))

(defund shape-spec-to-env (x obj)
  (declare (xargs :guard (shape-specp x)))
  (mv-let (ok bsl vsl)
    (shape-spec-env-slice x obj)
    (declare (ignore ok))
    (cons (slice-to-bdd-env bsl nil) vsl)))



(local
 (defthm shape-spec-obj-in-range-iff-shape-spec-iff-env-slice
   (iff (mv-nth 0 (shape-spec-iff-env-slice x obj))
        (shape-spec-obj-in-range-iff x obj))
   :hints(("Goal" :in-theory (enable shape-spec-obj-in-range-iff
                                     shape-spec-iff-env-slice)))))


(local
 (encapsulate nil
   (local (in-theory (e/d (ash) (floor))))
   (local (include-book "ihs/ihs-lemmas" :dir :system))
   ;; (local (defthm expt-2-of-posp
   ;;          (implies (posp x)
   ;;                   (integerp (* 1/2 (expt 2 x))))
   ;;          :rule-classes nil))
   ;; (local
   ;;  (encapsulate nil
   ;;    (local (defthm rw-equal-minus
   ;;             (implies (and (posp x) (rationalp y))
   ;;                      (equal (equal (expt 2 x) (- y))
   ;;                             (equal (- (expt 2 x)) y)))))
   ;;    (defthm negative-expt-2-of-posp
   ;;      (implies (and (posp x) (rationalp y)
   ;;                    (equal (expt 2 x) (- y)))
   ;;               (integerp (* 1/2 y)))
   ;;      :rule-classes nil)))

   (defthm integer-in-range-integer-env-slice
     (implies (integerp obj)
              (equal (mv-nth 0 (integer-env-slice vlist obj))
                     (integer-in-range vlist obj)))
     :hints(("Goal" :in-theory (enable* integer-env-slice
                                        integer-in-range))))))

(local
 (encapsulate nil
   (local (include-book "ihs/ihs-lemmas" :dir :system))
   (local (in-theory (e/d (ash) (floor))))

   (defthm natural-in-range-natural-env-slice
     (implies (natp obj)
              (equal (mv-nth 0 (natural-env-slice vlist obj))
                     (natural-in-range vlist obj)))
     :hints(("Goal" :in-theory (enable natural-env-slice
                                       natural-in-range))))))

(local
 (defthm number-spec-in-range-number-spec-env-slice
   (equal (mv-nth 0 (number-spec-env-slice nspec obj))
          (number-spec-in-range nspec obj))
   :hints(("Goal" :in-theory (enable number-spec-env-slice
                                     number-spec-in-range)))))

(local
 (defthm shape-spec-obj-in-range-env-slice
   (iff (mv-nth 0 (shape-spec-env-slice x obj))
        (shape-spec-obj-in-range x obj))
   :hints(("Goal" :in-theory (enable shape-spec-obj-in-range
                                     shape-spec-env-slice)))))
              



(defthm shape-spec-to-gobj-eval-env
  (implies (and (shape-specp x)
                (no-duplicatesp (shape-spec-indices x))
                (no-duplicatesp (shape-spec-vars x))
                (shape-spec-obj-in-range x obj))
           (equal (sspec-geval
                   (shape-spec-to-gobj x)
                   (shape-spec-to-env x obj))
                  obj))
  :hints(("Goal" :in-theory (enable shape-spec-to-env))))




(defun shape-spec-to-gobj-list (x)
  (if (atom x)
      nil
    (cons (shape-spec-to-gobj (car x))
          (shape-spec-to-gobj-list (cdr x)))))

(defun shape-spec-listp (x)
  (if (atom x)
      (equal x nil)
    (and (shape-specp (car x))
         (shape-spec-listp (cdr x)))))

;; (defthm shape-spec-listp-impl-shape-spec-to-gobj-list
;;   (implies (shape-spec-listp x)
;;            (equal (shape-spec-to-gobj x)
;;                   (shape-spec-to-gobj-list x)))
;;   :hints(("Goal" :induct (shape-spec-to-gobj-list x)
;;           :expand ((shape-spec-to-gobj x))
;;           :in-theory (enable tag))))





(defthm shape-spec-listp-implies-shape-specp
  (implies (shape-spec-listp x)
           (shape-specp x))
  :hints(("Goal" :expand ((shape-specp x))
          :in-theory (enable tag)
          :induct (shape-spec-listp x))))



       




(defun shape-specs-to-interp-al (bindings)
  (if (atom bindings)
      nil
    (cons (cons (caar bindings) (gl::shape-spec-to-gobj (cadar bindings)))
          (shape-specs-to-interp-al (cdr bindings)))))






;; (defthm shape-spec-alt-definition
;;   (equal (shape-spec-obj-in-range x obj)
;;          (if (atom x)
;;              (equal obj x)
;;            (case (car x)
;;              (:g-number (number-spec-in-range (cdr x) obj))
;;              (:g-boolean (booleanp obj))
;;              (:g-var t)
;;              (:g-concrete (equal obj (cdr x)))
;;              (:g-ite (let ((test (cadr x)) (then (caddr x)) (else (cdddr x)))
;;                        (or (and (shape-spec-obj-in-range-iff test t)
;;                                 (shape-spec-obj-in-range then obj))
;;                            (and (shape-spec-obj-in-range-iff test nil)
;;                                 (shape-spec-obj-in-range else obj)))))
;;              (t (and (consp obj)
;;                      (shape-spec-obj-in-range (car x) (car obj))
;;                      (shape-spec-obj-in-range (cdr x) (cdr obj)))))))
;;   :hints(("Goal" :in-theory (enable tag g-number->num g-concrete->obj
;;                                     g-ite->test g-ite->then g-ite->else)
;;           :expand ((shape-spec-obj-in-range x obj))))
;;   :rule-classes ((:definition :controller-alist ((shape-spec-obj-in-range t
;;                                                                           nil)))))

;; (local
;;  (defun shape-spec-alt-induction (x obj)
;;    (if (atom x)
;;        (equal obj x)
;;      (case (car x)
;;        (:g-number (number-spec-in-range (cdr x) obj))
;;        (:g-boolean (booleanp obj))
;;        (:g-var t)
;;        (:g-concrete (equal obj (cdr x)))
;;        (:g-ite (let ((then (caddr x)) (else (cdddr x)))
;;                  (list (shape-spec-alt-induction then obj)
;;                        (shape-spec-alt-induction else obj))))
;;        (t (list (shape-spec-alt-induction (car x) (car obj))
;;                 (shape-spec-alt-induction (cdr x) (cdr obj))))))))



(in-theory (disable shape-spec-obj-in-range))

;; (local (in-theory (disable shape-spec-alt-definition)))


(defthm shape-spec-obj-in-range-open-cons
  (implies (and (not (g-keyword-symbolp (car obj)))
                (not (eq (car obj) :g-integer))
                (not (eq (car obj) :g-integer?))
                (not (eq (car obj) :g-call))
                (consp obj))
           (equal (shape-spec-obj-in-range obj (cons carx cdrx))
                  (and (shape-spec-obj-in-range (car obj) carx)
                       (shape-spec-obj-in-range (cdr obj) cdrx))))
  :hints(("Goal" :in-theory (enable shape-spec-obj-in-range
                                    g-keyword-symbolp-def
                                    member-equal)))
  :rule-classes ((:rewrite :backchain-limit-lst (1 0 0 0 0))))

(defun binary-and* (a b)
  (declare (xargs :guard t))
  (and a b))

(defun and*-macro (lst)
  (if (atom lst)
      t
    (if (atom (cdr lst))
        (car lst)
      (list 'binary-and* (car lst)
            (and*-macro (cdr lst))))))

(defmacro and* (&rest lst)
  (and*-macro lst))

(add-binop and* binary-and*)

(defcong iff equal (and* a b) 1)

(defcong iff iff (and* a b) 2)

(defthm and*-rem-first
  (implies a
           (equal (and* a b) b)))

(defthm and*-rem-second
  (implies b
           (iff (and* a b) a)))

(defthm and*-nil-first
  (equal (and* nil b) nil))

(defthm and*-nil-second
  (equal (and* a nil) nil))

(defthm and*-forward
  (implies (and* a b) (and a b))
  :rule-classes :forward-chaining)

(defthmd ash-1-is-expt-2
  (implies (natp n)
           (equal (ash 1 n) (expt 2 n)))
  :hints(("Goal" :in-theory (enable ash floor))))

(defthmd natp-len-minus-one
  (implies (consp X)
           (natp (+ -1 (len x)))))

(defthm shape-spec-obj-in-range-open-g-integer
  (equal (shape-spec-obj-in-range `(:g-integer . ,rest) x)
         (integerp x))
  :hints(("Goal" :in-theory (enable shape-spec-obj-in-range))))

(defthm shape-spec-obj-in-range-open-integer
  (equal (shape-spec-obj-in-range `(:g-number ,bits) x)
         (if (consp bits)
             (and* (integerp x)
                   (<= (- (expt 2 (1- (len bits)))) x)
                   (< x (expt 2 (1- (len bits)))))
           (equal x 0)))
  :hints(("Goal" :in-theory (enable shape-spec-obj-in-range 
                                    number-spec-in-range
                                    integer-in-range
                                    g-number->num
                                    natp-len-minus-one
                                    ash-1-is-expt-2))))

(defthm shape-spec-obj-in-range-open-boolean
  (equal (shape-spec-obj-in-range `(:g-boolean . ,bit) x)
         (booleanp x))
  :hints(("Goal" :in-theory (enable shape-spec-obj-in-range))))



(defthm shape-spec-obj-in-range-open-atom
  (implies (atom a)
           (equal (shape-spec-obj-in-range a x)
                  (equal x a)))
  :hints(("Goal" :in-theory (enable shape-spec-obj-in-range
                                    g-concrete->obj)))
  :rule-classes ((:rewrite :backchain-limit-lst 1)))

(defthm shape-spec-obj-in-range-backchain-atom
  (implies (and (atom a)
                (equal x a))
           (equal (shape-spec-obj-in-range a x) t))
  :hints(("Goal" :in-theory (enable shape-spec-obj-in-range
                                    g-concrete->obj)))
  :rule-classes ((:rewrite :backchain-limit-lst 1)))

(defund list-of-g-booleansp (lst)
  (if (atom lst)
      (eq lst nil)
    (and (consp (car lst))
         (eq (caar lst) :g-boolean)
         (list-of-g-booleansp (cdr lst)))))

(defthm shape-spec-obj-in-range-open-list-of-g-booleans
  (implies (list-of-g-booleansp lst)
           (equal (shape-spec-obj-in-range lst obj)
                  (and* (boolean-listp obj)
                        (equal (len obj) (len lst)))))
  :hints(("Goal" ; :induct (shape-spec-obj-in-range lst obj)
          :induct (shape-spec-obj-in-range lst obj)
          :in-theory (enable shape-spec-obj-in-range tag
                             list-of-g-booleansp
                             boolean-listp))))


(defthm shape-spec-obj-in-range-backchain-list-of-g-booleans
  (implies (and (list-of-g-booleansp lst)
                (boolean-listp obj)
                (equal (len obj) (len lst)))
           (equal (shape-spec-obj-in-range lst obj) t)))


(defthm shape-spec-obj-in-range-solve-integer?
  (equal (shape-spec-obj-in-range `(:g-integer? . ,rest) x) t)
  :hints(("Goal" :in-theory (enable shape-spec-obj-in-range))))

(defthm shape-spec-obj-in-range-backchain-g-integer
  (implies (integerp x)
           (equal (shape-spec-obj-in-range `(:g-integer . ,rest) x)
                  t))
  :hints(("Goal" :in-theory (enable shape-spec-obj-in-range))))


(defthm shape-spec-obj-in-range-backchain-integer-1
  (implies (and (consp bits)
                (integerp x)
                (<= (- (expt 2 (1- (len bits)))) x)
                (< x (expt 2 (1- (len bits)))))
           (equal (shape-spec-obj-in-range `(:g-number ,bits) x) t))
  :hints (("goal" :use shape-spec-obj-in-range-open-integer))
  :rule-classes ((:rewrite :backchain-limit-lst (0 nil nil nil))))

(defthm shape-spec-obj-in-range-backchain-integer-2
  (implies (and (not (consp bits))
                (equal x 0))
           (equal (shape-spec-obj-in-range `(:g-number ,bits) x) t))
  :hints (("goal" :use shape-spec-obj-in-range-open-integer))
  :rule-classes ((:rewrite :backchain-limit-lst (0 nil))))

(defthm shape-spec-obj-in-range-backchain-boolean
  (implies (booleanp x)
           (equal (shape-spec-obj-in-range `(:g-boolean . ,bit) x) t)))

(defthm shape-spec-obj-in-range-var
  (equal (shape-spec-obj-in-range `(:g-var . ,v) x) t)
  :hints(("Goal" :in-theory (enable shape-spec-obj-in-range tag))))

(defthm shape-spec-obj-in-range-open-concrete
  (equal (shape-spec-obj-in-range `(:g-concrete . ,obj) x)
         (equal x obj))
  :hints(("Goal" :in-theory (enable shape-spec-obj-in-range tag
                                    g-concrete->obj))))



(defthm shape-spec-obj-in-range-backchain-concrete
  (implies (equal x obj)
           (equal (shape-spec-obj-in-range `(:g-concrete . ,obj) x)
                  t)))

(defthmd len-plus-one
  (implies (and (syntaxp (quotep n))
                (integerp n))
           (equal (equal (+ 1 (len lst)) n)
                  (equal (len lst) (1- n)))))

(defthmd len-zero
  (equal (equal (len lst) 0)
         (not (consp lst))))



;; These two rulesets will be used in the default coverage hints as a phased
;; simplification approach.  The backchain ruleset will be tried first to
;; reduce the goals to as few as possible clauses with conclusions that are
;; calls of shape-spec-obj-in-range on "atomic" shape specs (numbers, booleans,
;; concretes.)  Then shape-spec-obj-in-range-open will 
(def-ruleset! shape-spec-obj-in-range-backchain
  '(shape-spec-obj-in-range-open-cons
    shape-spec-obj-in-range-solve-integer?
    shape-spec-obj-in-range-backchain-g-integer
    shape-spec-obj-in-range-backchain-integer-1
    shape-spec-obj-in-range-backchain-integer-2
    shape-spec-obj-in-range-backchain-boolean
    shape-spec-obj-in-range-backchain-concrete
    shape-spec-obj-in-range-backchain-atom
    shape-spec-obj-in-range-backchain-list-of-g-booleans
    shape-spec-obj-in-range-var 
    car-cons cdr-cons natp-compound-recognizer
    (shape-spec-obj-in-range) (g-keyword-symbolp) (ash)
    (expt) (unary--) (binary-+) (consp) (integerp) (len)
    (car) (cdr) (booleanp) (list-of-g-booleansp) (tag)
    eql len-plus-one len-zero (zp) (boolean-listp) (true-listp)))

(def-ruleset! shape-spec-obj-in-range-open
  '(shape-spec-obj-in-range-open-cons
    shape-spec-obj-in-range-solve-integer?
    shape-spec-obj-in-range-open-g-integer
    shape-spec-obj-in-range-open-integer
    shape-spec-obj-in-range-open-boolean
    shape-spec-obj-in-range-open-concrete
    shape-spec-obj-in-range-open-atom
    shape-spec-obj-in-range-open-list-of-g-booleans
    shape-spec-obj-in-range-var
    and*-rem-first and*-rem-second
    acl2::iff-implies-equal-and*-1
    acl2::iff-implies-iff-and*-2
    car-cons cdr-cons natp-compound-recognizer
    (shape-spec-obj-in-range) (g-keyword-symbolp) (ash)
    (expt) (unary--) (binary-+) (consp) (integerp) (len)
    (car) (cdr) (booleanp) (list-of-g-booleansp) (tag) eql
    len-plus-one len-zero (zp) (boolean-listp) (true-listp)))
    



(defdoc shape-specs ":Doc-section ACL2::GL
Simplified symbolic objects useful for coverage proofs in GL~/

Shape specifiers are a simplified format of GL symbolic objects,
capable of representing Booleans, numbers, and conses, as well as
unconstrained variables and if-then-else objects.  While less
expressive than full-fledged symbolic objects, shape spec objects make
it easier to prove coverage lemmas necessary for proving theorems by
symbolic simulation.  Here, we document common constructions of
shape-spec objects and what it means to prove coverage.~/

------------------------------------------------------

CREATING SHAPE SPEC OBJECTS
Shape spec objects are a straightforward transformation of symbolic
objects: wherever a BDD occurs in a symbolic object, a shape specifier
instead contains a natural number representing a BDD variable.
Furthermore, ~c[G-APPLY] constructs are prohibited, and the BDD
variable numbers used in an shape spec may not repeat, nor may the
variable names used in ~c[G-VAR] constructs.  See
~il[GL::SYMBOLIC-OBJECTS].  The most common and useful constructions
of shape spec objects are as follows:

 (:G-BOOLEAN . <num>)
Represents a Boolean.

 (:G-NUMBER  <list-of-nums>)
Represents a two's-complement integer with bits corresponding to the
list, least significant bit first.  Rationals and complex rationals
are also available; ~l[GL::SYMBOLIC-OBJECTS].  A :G-NUMBER construct with
a list of length ~c[N] represents integers ~c[X] where
 ~c[(<= (- (expt 2 n) x)] and ~c[(< x (expt 2 n))].

 (<Car> . <Cdr>)
Represents a cons; Car and Cdr should be well-formed shape specifiers.

 <Atom>
Represents the atom itself; must not be one of the six distinguished
keyword symbols :G-CONCRETE, :G-BOOLEAN, :G-NUMBER, :G-ITE, :G-VAR, or
:G-APPLY.

------------------------------------------------------

WHAT IS A COVERAGE PROOF?
In order to prove a theorem by symbolic simulation, one binds each
variable mentioned in the theorem to a symbolic object and then
symbolically simulates the conclusion of the theorem on these symbolic
objects.  If the result is true, what can we conclude?  It depends on
the coverage of the symbolic inputs.  For example, one might
symbolically simulate the term ~c[(< (+ A B) 7)] with ~c[A] and ~c[B]
bound to symbolic objects representing two-bit natural numbers and
recieve a result of ~c[T].  From this, it would be fallacious to
conclude ~c[(< (+ 6 8) 7)], because the symbolic simulation didn't
cover the case where ~c[A] was 6 and ~c[B] 7.  In fact, it isn't
certain that we can conclude ~c[(< (+ 2 2) 7)] from our symbolic
simulation, because the symbolic object bindings for ~c[A] and ~c[B]
might have interedependencies such that ~c[A] and ~c[B] can't
simultaneously represent 2.  (For example, the bindings could be such
that bit 0 of ~c[A] and ~c[B] are always opposite.)  In order to prove
a useful theorem from the result of such a symbolic simulation, we
must show that some set of concrete input vectors is covered by the
symbolic objects bound to ~c[A] and ~c[B].  But in general, it is a
tough computational problem to determine the set of concrete input
vectors that are covered by a given symbolic input vector.

To make these determinations easier, shape spec objects are somewhat
restricted.  Whereas symbolic objects generally use BDDs to represent
individual Booleans or bits of numeric values (~l[GL::SYMBOLIC-OBJECTS]),
shape specs instead use natural numbers representing UBDD variables.
Additionally, shape specs are restricted such that no BDD variable
number may be used more than once among the bindings for the variables
of a theorem; this is to prevent interdependencies among them.

While in general it is a difficult problem to determine whether a
symbolic object can evaluate to a given concrete object, a function
~c[SHAPE-SPEC-OBJ-IN-RANGE] can make that determination about shape
specs.  ~c[SHAPE-SPEC-OBJ-IN-RANGE] takes two arguments, a shape spec
and some object, and returns T if that object is in the coverage set
of the shape spec, and NIL otherwise.  Therefore, if we wish to
conclude that shape specs bound to ~c[A] and ~c[B] cover all two-bit
natural numbers, we may prove the following theorem:
~bv[]
 (implies (and (natp a) (< a 4)
               (natp b) (< b 4))
          (shape-spec-obj-in-range (list a-binding b-binding)
                                   (list a b)))
~ev[]

When proving a theorem using the GL clause processor, variable
bindings are given as shape specs so that coverage obligations may be
stated in terms of ~c[SHAPE-SPEC-OBJ-IN-RANGE].  The shape specs are
converted to symbolic objects and may be parametrized based on some
restrictions from the hypotheses, restricting their range further.
Thus, in order to prove a theorem about fixed-length natural numbers,
for example, one may provide a shape specifier that additionally
covers negative integers of the given length; parametrization can then
restrict the symbolic inputs used in the simulation to only cover the
naturals, while the coverage proof may still be done using the
simpler, unparametrized shape spec.
~/
")




(defund shape-spec-call-free (x)
  (declare (xargs :guard t))
  (or (atom x)
      (pattern-match x
        ((g-number &) t)
        ((g-boolean &) t)
        ((g-integer & & &) t)
        ((g-integer? & & & &) t)
        ((g-var &) t)
        ((g-ite test then else)
         (and (shape-spec-call-free test)
              (shape-spec-call-free then)
              (shape-spec-call-free else)))
        ((g-concrete &) t)
        ((g-call & & & &) nil)
        (& (and (shape-spec-call-free (car x))
                (shape-spec-call-free (cdr x)))))))

(local
 (defsection shape-spec-call-free
   

   (local (in-theory (enable shape-spec-call-free)))

   (defthm shape-spec-call-free-by-tag
     (implies (and (or (g-keyword-symbolp (tag x))
                       (member (tag x) '(:g-integer :g-integer?)))
                   (not (eq (tag x) :g-ite))
                   (not (eq (tag x) :g-apply))
                   (not (eq (tag x) :g-call)))
              (shape-spec-call-free x))
     :hints(("Goal" :in-theory (enable g-keyword-symbolp))))

   (Defthm shape-spec-call-free-when-atom
     (implies (not (consp x))
              (shape-spec-call-free x))
     :rule-classes ((:rewrite :backchain-limit-lst 0)))))

(defsection car-term
  (defund car-term (x)
    (declare (xargs :guard (pseudo-termp x)))
    (if (and (consp x)
             (eq (car x) 'cons))
        (cadr x)
      `(car ,x)))
  (local (in-theory (enable car-term)))
  (defthm pseudo-termp-car-term
    (implies (pseudo-termp x)
             (pseudo-termp (car-term x))))

  (defthm car-term-correct
    (equal (sspec-geval-ev (car-term x) a)
           (car (sspec-geval-ev x a)))))

(defsection cdr-term
  (defund cdr-term (x)
    (declare (xargs :guard (pseudo-termp x)))
    (if (and (consp x)
             (eq (car x) 'cons))
        (caddr x)
      `(cdr ,x)))
  (local (in-theory (enable cdr-term)))
  (defthm pseudo-termp-cdr-term
    (implies (pseudo-termp x)
             (pseudo-termp (cdr-term x))))

  (defthm cdr-term-correct
    (equal (sspec-geval-ev (cdr-term x) a)
           (cdr (sspec-geval-ev x a)))))



(defsection make-nth-terms
  (defund make-nth-terms (x start n)
    (declare (xargs :guard (and (natp start) (natp n))))
    (if (zp n)
        nil
      (cons `(nth ',(lnfix start) ,x)
            (make-nth-terms x (1+ (lnfix start)) (1- n)))))

  (local (in-theory (enable make-nth-terms)))

  (defthm pseudo-term-listp-make-nth-terms
    (implies (and (pseudo-termp x)
                  (natp start))
             (pseudo-term-listp (make-nth-terms x start n)))
    :hints(("Goal" :in-theory (enable make-nth-terms))))

  (defthm ev-of-make-nth-terms
    (equal (sspec-geval-ev-lst (make-nth-terms x start n) a)
           (take n (nthcdr start (sspec-geval-ev x a))))
    :hints(("Goal" :in-theory (enable acl2::take-redefinition
                                      nthcdr)))))

(defsection shape-spec-oblig-term

  ;; (defund sspec-apply-get-inverse-fn (fn state)
  ;;   (declare (xargs :stobjs state))
  ;;   (b* ((inverse (cdr (hons-assoc-equal fn (table-alist
  ;;                                            'gl-inverse-functions (w
  ;;                                                                   state))))))
  ;;     (and (symbolp inverse)
  ;;          (not (eq inverse 'quote))
  ;;          inverse)))

  ;; (defthm sspec-apply-get-inverse-type
  ;;   (symbolp (sspec-apply-get-inverse-fn fn state))
  ;;   :hints(("Goal" :in-theory (enable sspec-apply-get-inverse-fn)))
  ;;   :rule-classes :type-prescription)

  ;; (defthm sspec-apply-get-inverse-not-equote
  ;;   (not (equal (sspec-apply-get-inverse-fn fn state) 'quote))
  ;;   :hints(("Goal" :in-theory (enable sspec-apply-get-inverse-fn))))

  (definlined ss-unary-function-fix (x)
    (declare (xargs :guard (ss-unary-functionp x)))
    (mbe :logic (if (ss-unary-functionp x)
                    x
                  nil)
         :exec x))

  (defthm ss-unary-functionp-of-ss-unary-function-fix
    (ss-unary-functionp (ss-unary-function-fix x))
    :hints(("Goal" :in-theory (enable ss-unary-function-fix))))

  (defthm pseudo-termp-with-unary-function
    (implies (and (ss-unary-functionp f)
                  (pseudo-termp arg))
             (pseudo-termp (list f arg)))
    :hints(("Goal" :in-theory (enable ss-unary-functionp))))

  (defund shape-spec-oblig-term (x obj-term iff-flg)
    (declare (xargs :guard (and (shape-specp x)
                                (pseudo-termp obj-term))
                    :guard-hints (("goal" :expand ((shape-specp x)
                                                   (:free (a b) (pseudo-termp
                                                                 (cons a b))))
                                   :in-theory (disable pseudo-termp)))
                    :guard-debug t))
    (if (shape-spec-call-free x)
        `(,(if iff-flg 'shape-spec-obj-in-range-iff 'shape-spec-obj-in-range)
          ',x ,obj-term)
      (pattern-match x
        ((g-ite test then else)
         `(if (if ,(shape-spec-oblig-term test ''t t)
                  ,(shape-spec-oblig-term then obj-term iff-flg)
                'nil)
              't
            (if ,(shape-spec-oblig-term test ''nil t)
                ,(shape-spec-oblig-term else obj-term iff-flg)
              'nil)))
        ((g-call fn args inverse arity)
         (b* ((inverse (ss-unary-function-fix inverse))
              (arity (lnfix arity))
              (inverse-term `(,inverse ,obj-term))
              (nths (make-nth-terms inverse-term 0 arity)))
           `(if ,(shape-spec-oblig-term args inverse-term nil)
                (if (equal (len ,inverse-term) ',arity)
                    (,(if iff-flg 'iff 'equal)
                     (,fn . ,nths)
                     ,obj-term)
                  'nil)
              'nil)))
        (& (if iff-flg
               obj-term
             `(if (consp ,obj-term)
                  (if ,(shape-spec-oblig-term (car x) (car-term obj-term) nil) 
                      ,(shape-spec-oblig-term (cdr x) (cdr-term obj-term) nil)
                    'nil)
                'nil))))))

  


  (defund shape-spec-env-term (x obj-term iff-flg)
    (declare (xargs :guard (and (shape-specp x)
                                (pseudo-termp obj-term))
                    :guard-hints (("goal" :expand ((shape-specp x)
                                                   (:free (a b) (pseudo-termp
                                                                 (cons a b))))
                                   :in-theory (disable pseudo-termp)))
                    :guard-debug t))
    (if (shape-spec-call-free x)
        `(shape-spec-slice-to-env
          (,(if iff-flg 'shape-spec-iff-env-slice 'shape-spec-env-slice)
           ',x ,obj-term))
      (pattern-match x
        ((g-ite test then else)
         (b* ((then-term (shape-spec-env-term then obj-term iff-flg))
              (else-term (shape-spec-env-term else obj-term iff-flg))
              (both `(ss-append-envs ,then-term ,else-term)))
           `(if (if ,(shape-spec-oblig-term test ''t t)
                    ,(shape-spec-oblig-term then obj-term iff-flg)
                  'nil)
                (ss-append-envs
                 ,(shape-spec-env-term test ''t t)
                 ,both)
              (ss-append-envs
               ,(shape-spec-env-term test ''nil t)
               ,both))))
        ((g-call & args inverse &)
         (b* ((inverse (ss-unary-function-fix inverse))
              (inverse-term `(,inverse ,obj-term)))
           (shape-spec-env-term args inverse-term nil)))
        (& `(ss-append-envs
             ,(shape-spec-env-term (car x) (car-term obj-term) nil) 
             ,(shape-spec-env-term (cdr x) (cdr-term obj-term) nil))))))

  (local (in-theory (enable shape-spec-oblig-term shape-spec-env-term)))



  (defthm pseudo-termp-shape-spec-oblig-term
    (implies (and (pseudo-termp obj-term)
                  (shape-specp x))
             (pseudo-termp (shape-spec-oblig-term x obj-term iff-flg)))
    :hints(("Goal" :induct (shape-spec-oblig-term x obj-term iff-flg)
            :in-theory (disable pseudo-termp)
            :expand ((shape-specp x)
                     (:free (a b) (pseudo-termp (cons a b)))))))

  (defthm pseudo-termp-shape-spec-env-term
    (implies (and (pseudo-termp obj-term)
                  (shape-specp x))
             (pseudo-termp (shape-spec-env-term x obj-term iff-flg)))
    :hints(("Goal" :induct (shape-spec-env-term x obj-term iff-flg)
            :in-theory (disable pseudo-termp)
            :expand ((shape-specp x)
                     (:free (a b) (pseudo-termp (cons a b)))))))

  (defthm indices-of-shape-spec-env-term
    (implies (shape-specp x)
             (equal (strip-cars
                     (car (sspec-geval-ev (shape-spec-env-term x obj-term iff-flg) a)))
                    (shape-spec-indices x)))
    :hints (("goal" :induct (shape-spec-env-term x obj-term iff-flg)
             :expand ((shape-spec-indices x)
                      (shape-specp x)))
            (and stable-under-simplificationp
                 '(:use ((:instance shape-spec-indices-subset-cars-env-slice
                          (obj (sspec-geval-ev obj-term a)))
                         (:instance shape-spec-indices-subset-cars-iff-env-slice
                          (obj (sspec-geval-ev obj-term a))))
                   :in-theory (disable shape-spec-indices-subset-cars-env-slice
                                       shape-spec-indices-subset-cars-iff-env-slice)))))

  (defthm vars-of-shape-spec-env-term
    (implies (shape-specp x)
             (equal (strip-cars
                     (cdr (sspec-geval-ev (shape-spec-env-term x obj-term iff-flg) a)))
                    (shape-spec-vars x)))
    :hints (("goal" :induct (shape-spec-env-term x obj-term iff-flg)
             :expand ((shape-spec-vars x)
                      (shape-specp x)))
            (and stable-under-simplificationp
                 '(:use ((:instance shape-spec-vars-subset-cars-env-slice
                          (obj (sspec-geval-ev obj-term a)))
                         (:instance shape-spec-vars-subset-cars-iff-env-slice
                          (obj (sspec-geval-ev obj-term a))))
                   :in-theory (disable shape-spec-vars-subset-cars-env-slice
                                       shape-spec-vars-subset-cars-iff-env-slice)))))

  (defthm alistp-car-shape-spec-env-term
    (alistp (car (sspec-geval-ev (shape-spec-env-term x obj-term iff-flg) a))))

  (defthm alistp-cdr-shape-spec-env-term
    (alistp (cdr (sspec-geval-ev (shape-spec-env-term x obj-term iff-flg) a))))

  (local (defthm g-keyword-symbolp-of-shape-spec-to-gobj
           (equal (g-keyword-symbolp (shape-spec-to-gobj x))
                  (g-keyword-symbolp x))
           :hints(("Goal" :in-theory (enable shape-spec-to-gobj)))))

  ;; (local (defthm equal-keyword-shape-spec-to-gobj
  ;;          (implies (and (syntaxp (quotep key))
  ;;                        (g-keyword-symbolp key))
  ;;                   (equal (equal (shape-spec-to-gobj x) key)
  ;;                          (equal x key)))
  ;;          :hints(("Goal" :in-theory (enable shape-spec-to-gobj)))))

  (defthm sspec-geval-of-gl-cons
    (equal (sspec-geval (gl-cons a b) env)
           (cons (sspec-geval a env)
                 (sspec-geval b env)))
    :hints(("Goal" :in-theory (enable sspec-geval g-keyword-symbolp))))

  (defthm sspec-geval-of-g-apply
    (equal (sspec-geval (g-apply fn args) env)
           (sspec-geval-ev (cons fn (kwote-lst (sspec-geval args env))) nil))
    :hints(("Goal" :in-theory (enable sspec-geval g-keyword-symbolp))))


  ;; (local (defthm non-keyword-symbol-by-shape-spec-call-free
  ;;          (implies (and (not (shape-spec-call-free x))
  ;;                        (not (eq (tag x) :g-ite))
  ;;                        (not (eq (tag x) :g-apply)))
  ;;                   (not (g-keyword-symbolp (tag x))))
  ;;          :hints(("Goal" :in-theory (enable g-keyword-symbolp)))))


  (local (in-theory (disable shape-spec-call-free)))

  (local (in-theory (disable iff kwote-lst)))

  (local
   (progn

     (defthm shape-spec-to-gobj-of-cons
       (implies (and (not (shape-spec-call-free x))
                     (not (member (tag x) '(:g-ite :g-call))))
                (equal (shape-spec-to-gobj x)
                       (gl-cons (shape-spec-to-gobj (car x))
                                (shape-spec-to-gobj (cdr x)))))
       :hints(("Goal" :in-theory (enable shape-spec-to-gobj))))

     (defthm shape-spec-indices-of-cons
       (implies (and (not (shape-spec-call-free x))
                     (not (member (tag x) '(:g-ite :g-call))))
                (equal (shape-spec-indices x)
                       (append (shape-spec-indices (car x))
                               (shape-spec-indices (cdr x)))))
       :hints(("Goal" :in-theory (enable shape-spec-indices))))

     (defthm shape-spec-vars-of-cons
       (implies (and (not (shape-spec-call-free x))
                     (not (member (tag x) '(:g-ite :g-call))))
                (equal (shape-spec-vars x)
                       (append (shape-spec-vars (car x))
                               (shape-spec-vars (cdr x)))))
       :hints(("Goal" :in-theory (enable shape-spec-vars))))

     (defthm shape-specp-car/cdr
       (implies (and (not (shape-spec-call-free x))
                     (not (member (tag x) '(:g-ite :g-call)))
                     (shape-specp x))
                (and (shape-specp (car x))
                     (shape-specp (cdr x))))
       :hints(("Goal" :in-theory (enable shape-specp))))

     (defthm shape-spec-to-gobj-of-g-call
       (implies (equal (tag x) :g-call)
                (equal (shape-spec-to-gobj x)
                       (g-apply (g-call->fn x)
                                (shape-spec-to-gobj (g-call->args x)))))
       :hints(("Goal" :in-theory (enable shape-spec-to-gobj))))

     (defthm shape-spec-indices-of-g-call
       (implies (equal (tag x) :g-call)
                (equal (shape-spec-indices x)
                       (shape-spec-indices (g-call->args x))))
       :hints(("Goal" :in-theory (enable shape-spec-indices))))

     (defthm shape-spec-vars-of-g-call
       (implies (equal (tag x) :g-call)
                (equal (shape-spec-vars x)
                       (shape-spec-vars (g-call->args x))))
       :hints(("Goal" :in-theory (enable shape-spec-vars))))

     (defthm shape-specp-g-call
       (implies (and (equal (tag x) :g-call)
                     (shape-specp x))
                (and (shape-specp (g-call->args x))
                     (symbolp (g-call->fn x))
                     (not (equal (g-call->fn x) 'quote))
                     (ss-unary-functionp (g-call->inverse x))
                     (natp (g-call->arity x))))
       :hints(("Goal" :in-theory (enable shape-specp))))

     (defthm shape-spec-to-gobj-of-g-ite
       (implies (equal (tag x) :g-ite)
                (equal (shape-spec-to-gobj x)
                       (g-ite (shape-spec-to-gobj (g-ite->test x))
                              (shape-spec-to-gobj (g-ite->then x))
                              (shape-spec-to-gobj (g-ite->else x)))))
       :hints(("Goal" :in-theory (enable shape-spec-to-gobj))))

     (defthm shape-spec-indices-of-g-ite
       (implies (equal (tag x) :g-ite)
                (equal (shape-spec-indices x)
                       (append (shape-spec-indices (g-ite->test x))
                               (shape-spec-indices (g-ite->then x))
                               (shape-spec-indices (g-ite->else x)))))
       :hints(("Goal" :in-theory (enable shape-spec-indices))))

     (defthm shape-spec-vars-of-g-ite
       (implies (equal (tag x) :g-ite)
                (equal (shape-spec-vars x)
                       (append (shape-spec-vars (g-ite->test x))
                               (shape-spec-vars (g-ite->then x))
                               (shape-spec-vars (g-ite->else x)))))
       :hints(("Goal" :in-theory (enable shape-spec-vars))))

     (defthm shape-specp-g-ite
       (implies (and (equal (tag x) :g-ite)
                     (shape-specp x))
                (and (shape-specp (g-ite->test x))
                     (shape-specp (g-ite->then x))
                     (shape-specp (g-ite->else x))))
       :hints(("Goal" :in-theory (enable shape-specp))))))

  (local (in-theory (disable not)))

  (local (in-theory (disable (:t shape-spec-oblig-term)
                             (:t shape-spec-env-term)
                             shape-spec-call-free-by-tag
                             acl2::consp-by-len
                             acl2::true-listp-append
                             acl2::no-duplicatesp-equal-when-atom
                             acl2::no-duplicatesp-equal-non-cons
                             acl2::consp-of-append
                             default-car
                             tag-when-atom
                             default-cdr)))

  (local (defthm shape-spec-oblig-term-correct-lemma
           (let ((env (sspec-geval-ev (shape-spec-env-term
                                       x obj-term iff-flg)
                                      a)))
             (implies (and (sspec-geval-ev (shape-spec-oblig-term x obj-term iff-flg) a)
                           (shape-specp x)
                           (no-duplicatesp (shape-spec-indices x))
                           (no-duplicatesp (shape-spec-vars x)))
                      (if iff-flg
                          (iff (sspec-geval (shape-spec-to-gobj x)
                                            (cons (slice-to-bdd-env (car env) ee)
                                                  (cdr env)))
                               (sspec-geval-ev obj-term a))
                        (equal (sspec-geval (shape-spec-to-gobj x)
                                            (cons (slice-to-bdd-env (car env) ee)
                                                  (cdr env)))
                               (sspec-geval-ev obj-term a)))))
           :hints (("goal" :induct (shape-spec-oblig-term
                                    x obj-term iff-flg)
                    :in-theory (e/d (sspec-geval-ev-of-fncall-args)
                                    (gl-cons (:d shape-spec-env-term)
                                             (:d shape-spec-oblig-term)))
                    :expand ((:free (iff-flg) (shape-spec-env-term
                                               x obj-term iff-flg))
                             (:free (iff-flg) (shape-spec-oblig-term
                                               x obj-term iff-flg)))
                    :do-not-induct t))
           :rule-classes nil
           ;; (shape-specp x)
           ;; (shape-spec-indices x)
           ;; (shape-spec-vars x)
           ;; (:with sspec-geval
           ;;  (:free (a b env) (sspec-geval (cons a b) env)))
           ))

  (defthm shape-spec-oblig-term-correct
    (let ((env (sspec-geval-ev (shape-spec-env-term
                                x obj-term nil)
                               a)))
      (implies (and (sspec-geval-ev (shape-spec-oblig-term x obj-term nil) a)
                    (shape-specp x)
                    (no-duplicatesp (shape-spec-indices x))
                    (no-duplicatesp (shape-spec-vars x)))
               (equal (sspec-geval (shape-spec-to-gobj x)
                                   (cons (slice-to-bdd-env (car env) ee)
                                         (cdr env)))
                      (sspec-geval-ev obj-term a))))
    :hints (("goal" :use ((:instance shape-spec-oblig-term-correct-lemma
                           (iff-flg nil))))))

  (defthm shape-spec-oblig-term-correct-iff
    (let ((env (sspec-geval-ev (shape-spec-env-term
                                x obj-term t)
                               a)))
      (implies (and (sspec-geval-ev (shape-spec-oblig-term x obj-term t) a)
                    (shape-specp x)
                    (no-duplicatesp (shape-spec-indices x))
                    (no-duplicatesp (shape-spec-vars x)))
               (iff (sspec-geval (shape-spec-to-gobj x)
                                 (cons (slice-to-bdd-env (car env) ee)
                                       (cdr env)))
                    (sspec-geval-ev obj-term a))))
    :hints (("goal" :use ((:instance shape-spec-oblig-term-correct-lemma
                           (iff-flg t)))))))


