


(in-package "GL")

(include-book "gtypes")
(include-book "gl-doc-string")
(local (include-book "gtype-thms"))
(local (include-book "data-structures/no-duplicates" :dir :system))
(local (include-book "tools/mv-nth" :dir :system))
(local (include-book "ihs/ihs-lemmas" :dir :system))
(local (include-book "centaur/misc/fast-alists" :dir :system))

; Modified slightly 12/4/2012 by Matt K. to be redundant with new ACL2
; definition.
(defund nat-listp (l)
  (declare (xargs :guard t))
  (cond ((atom l)
         (eq l nil))
        (t (and (natp (car l))
                (nat-listp (cdr l))))))

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


;; An shape spec is an object that is similar to a g object, but a) where there
;; would be BDDs in a g object, there are natural numbers in an shape spec, and
;; b) no G-APPLY constructs are allowed in an shape spec.

(defund number-specp (nspec)
  (declare (xargs :guard t))
  (and (consp nspec)
       (nat-listp (car nspec))
       (if (atom (cdr nspec))
           (not (cdr nspec))
         (and (nat-listp (cadr nspec))
              (if (atom (cddr nspec))
                  (not (cddr nspec))
                (and (nat-listp (caddr nspec))
                     (if (atom (cdddr nspec))
                         (not (cdddr nspec))
                         (nat-listp (cadddr nspec)))))))))


(defund shape-specp (x)
  (declare (xargs :guard t))
  (if (atom x)
      (not (g-keyword-symbolp x))
    (case (tag x)
      (:g-number (and (g-number-p x)
                      (number-specp (g-number->num x))))
      (:g-boolean (and (g-boolean-p x)
                       (natp (g-boolean->bool x))))
      (:g-concrete (g-concrete-p x))
      (:g-var (g-var-p x))
      (:g-ite
       (and (g-ite-p x)
            (shape-specp (g-ite->test x))
            (shape-specp (g-ite->then x))
            (shape-specp (g-ite->else x))))
      (:g-apply nil)
      (otherwise (and (shape-specp (car x))
                      (shape-specp (cdr x)))))))



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

(local
 (defthm nat-listp-number-spec-indices
   (implies (number-specp nspec)
            (nat-listp (number-spec-indices nspec)))
   :hints(("Goal" :in-theory (enable number-specp number-spec-indices)))))

(defund shape-spec-indices (x)
  (declare (xargs :guard (shape-specp x)
                  :verify-guards nil))
  (if (atom x)
      nil
    (pattern-match x
      ((g-number nspec)
       (number-spec-indices nspec))
      ((g-boolean n) (list n))
      ((g-var &) nil)
      ((g-ite if then else)
       (append (shape-spec-indices if)
               (shape-spec-indices then)
               (shape-spec-indices else)))
      ((g-concrete &) nil)
      (& (append (shape-spec-indices (car x))
                 (shape-spec-indices (cdr x)))))))

(local
 (defthm nat-listp-shape-spec-indices
   (implies (shape-specp x)
            (nat-listp (shape-spec-indices x)))
   :hints(("Goal" :in-theory (enable shape-specp shape-spec-indices nat-listp)))))

(verify-guards shape-spec-indices
               :hints (("goal" :in-theory (enable shape-specp))))

(defund shape-spec-vars (x)
  (declare (xargs :guard (shape-specp x)
                  :verify-guards nil))
  (if (atom x)
      nil
    (pattern-match x
      ((g-number &) nil)
      ((g-boolean &) nil)
      ((g-var v) (list v))
      ((g-ite if then else)
       (append (shape-spec-vars if)
               (shape-spec-vars then)
               (shape-spec-vars else)))
      ((g-concrete &) nil)
      (& (append (shape-spec-vars (car x))
                 (shape-spec-vars (cdr x)))))))

(local
 (defthm true-listp-shape-spec-vars
   (true-listp (shape-spec-vars x))
   :hints(("Goal" :in-theory (enable shape-spec-vars)))))

(verify-guards shape-spec-vars
               :hints(("Goal" :in-theory (enable shape-specp))))




(defund integer-env-slice (vlist obj)
  (declare (xargs :guard (and (nat-listp vlist)
                              (integerp obj))
                  :guard-hints(("Goal" :in-theory (enable nat-listp)))))
  (if (atom vlist)
      (mv (eql obj 0) nil)
    (if (atom (cdr vlist))
        (if (eql obj 0)
            (mv t (list (cons (car vlist) nil)))
          (mv (eql obj -1) (list (cons (car vlist) t))))
      (mv-let (rest-ok rest-bslice)
        (integer-env-slice (cdr vlist) (ash obj -1))
        (mv rest-ok (cons (cons (car vlist) (logbitp 0 obj)) rest-bslice))))))

(local
 (defthm true-listp-integer-env-slice
   (true-listp (mv-nth 1 (integer-env-slice vlist obj)))
   :hints(("Goal" :in-theory (enable integer-env-slice)))))

(defund natural-env-slice (vlist obj)
  (declare (xargs :guard (and (nat-listp vlist)
                              (integerp obj))
                  :guard-hints(("Goal" :in-theory (enable nat-listp)))))
  (if (atom vlist)
      (mv (eql obj 0) nil)
    (mv-let (rest-ok rest-bslice)
      (natural-env-slice (cdr vlist) (ash obj -1))
      (mv rest-ok (cons (cons (car vlist) (logbitp 0 obj)) rest-bslice)))))

(local
 (defthm true-listp-natural-env-slice
   (true-listp (mv-nth 1 (natural-env-slice vlist obj)))
   :hints(("Goal" :in-theory (enable natural-env-slice)))))

(defund number-spec-env-slice (nspec obj)
  (declare (xargs :guard (number-specp nspec)
                  :guard-hints(("Goal" :in-theory (enable number-specp)))))
  (mv-let (rn-ok rn-bspec)
    (integer-env-slice (car nspec) (numerator (realpart (fix obj))))
    (if (consp (cdr nspec))
        (mv-let (rd-ok rd-bspec)
          (natural-env-slice (cadr nspec) (denominator (realpart (fix obj))))
          (if (consp (cddr nspec))
              (mv-let (in-ok in-bspec)
                (integer-env-slice
                 (caddr nspec) (numerator (imagpart (fix obj))))
                (if (consp (cdddr nspec))
                    (mv-let (id-ok id-bspec)
                      (natural-env-slice
                       (cadddr nspec)
                       (denominator (imagpart (fix obj))))
                      (mv (and (acl2-numberp obj)
                               rn-ok rd-ok in-ok id-ok)
                          (append rn-bspec rd-bspec
                                  in-bspec id-bspec)))
                  (mv (and (acl2-numberp obj)
                           (eql (denominator (imagpart obj)) 1)
                           rn-ok rd-ok in-ok)
                      (append rn-bspec rd-bspec
                              in-bspec))))
            (mv (and (acl2-numberp obj)
                     (eql (imagpart obj) 0)
                     rn-ok rd-ok)
                (append rn-bspec rd-bspec))))
      (mv (and (acl2-numberp obj)
               (eql (denominator (realpart obj)) 1)
               (eql (imagpart obj) 0) rn-ok)
          rn-bspec))))

(local
 (defthm true-listp-number-spec-env-slice-1
   (true-listp (mv-nth 1 (number-spec-env-slice nspec obj)))
   :hints(("Goal" :in-theory (enable number-spec-env-slice)))))

(defun shape-spec-arbitrary-slice (x)
  (declare (xargs :guard (shape-specp x)
                  :verify-guards nil))
  (if (atom x)
      (mv nil nil)
    (pattern-match x
      ((g-number nspec)
       (mv-let (ok bsl)
         (number-spec-env-slice nspec 0)
         (declare (ignore ok))
         (mv bsl nil)))
      ((g-boolean n) (mv (list (cons n nil)) nil))
      ((g-var v) (mv nil (list (cons v nil))))
      ((g-ite if then else)
       (b* (((mv if-bsl if-vsl)
             (shape-spec-arbitrary-slice if))
            ((mv then-bsl then-vsl)
             (shape-spec-arbitrary-slice then))
            ((mv else-bsl else-vsl)
             (shape-spec-arbitrary-slice else)))
         (mv (append if-bsl then-bsl else-bsl)
             (append if-vsl then-vsl else-vsl))))
      ((g-concrete &) (mv nil nil))
      (& (b* (((mv car-bsl car-vsl)
               (shape-spec-arbitrary-slice (car x)))
              ((mv cdr-bsl cdr-vsl)
               (shape-spec-arbitrary-slice (cdr x))))
           (mv (append car-bsl cdr-bsl)
               (append car-vsl cdr-vsl)))))))

(local
 (defthm true-listp-shape-spec-arbitrary-slice-1
   (true-listp (mv-nth 1 (shape-spec-arbitrary-slice x)))))

(local
 (defthm true-listp-shape-spec-arbitrary-slice-0
   (true-listp (mv-nth 0 (shape-spec-arbitrary-slice x)))))

(verify-guards shape-spec-arbitrary-slice
               :hints(("Goal" :in-theory (enable shape-specp))))

(defund shape-spec-iff-env-slice (x obj)
  (declare (xargs :guard (shape-specp x)
                  :verify-guards nil))
  (if (atom x)
      (mv (iff x obj) nil nil)
    (pattern-match x
      ((g-number nspec)
       (mv-let (ok bsl)
         (number-spec-env-slice nspec 0)
         (declare (ignore ok))
         (mv obj bsl nil)))
      ((g-boolean n) (mv t (list (cons n obj)) nil))
      ((g-var v) (mv t nil (list (cons v obj))))
      ((g-ite if then else)
       (b* (((mv then-ok then-bslice then-vslice)
             (shape-spec-iff-env-slice then obj))
            ((mv else-ok else-bslice else-vslice)
             (shape-spec-iff-env-slice else obj))
            ((mv if-t-ok if-t-bslice if-t-vslice)
             (shape-spec-iff-env-slice if t))
            ((mv if-nil-ok if-nil-bslice if-nil-vslice)
             (shape-spec-iff-env-slice if nil)))
         (if (and then-ok if-t-ok)
             (mv t (append if-t-bslice then-bslice else-bslice)
                 (append if-t-vslice then-vslice else-vslice))
           (mv (and else-ok if-nil-ok)
               (append if-nil-bslice then-bslice else-bslice)
               (append if-nil-vslice then-vslice else-vslice)))))
      ((g-concrete y) (mv (iff y obj) nil nil))
      (& (b* (((mv car-bsl car-vsl)
               (shape-spec-arbitrary-slice (car x)))
              ((mv cdr-bsl cdr-vsl)
               (shape-spec-arbitrary-slice (cdr x))))
           (mv obj
               (append car-bsl cdr-bsl)
               (append car-vsl cdr-vsl)))))))

(local
 (defthm true-listp-shape-spec-iff-env-slice-1
   (true-listp (mv-nth 1 (shape-spec-iff-env-slice x obj)))
   :hints(("Goal" :in-theory (enable shape-spec-iff-env-slice)))))

(local
 (defthm true-listp-shape-spec-iff-env-slice-2
   (true-listp (mv-nth 2 (shape-spec-iff-env-slice x obj)))
   :hints(("Goal" :in-theory (enable shape-spec-iff-env-slice)))))

(verify-guards shape-spec-iff-env-slice
               :hints(("Goal" :in-theory (enable shape-specp))))

(defund shape-spec-env-slice (x obj)
  (declare (xargs :guard (shape-specp x)
                  :verify-guards nil))
  (if (atom x)
      (mv (equal x obj) nil nil)
    (pattern-match x
      ((g-number nspec)
       (mv-let (ok bspec)
         (number-spec-env-slice nspec obj)
         (mv ok bspec nil)))
      ((g-boolean n)
       (mv (booleanp obj)
           (list (cons n obj))
           nil))
      ((g-var v) (mv t nil (list (cons v obj))))
      ((g-ite if then else)
       (b* (((mv then-ok then-bslice then-vslice)
             (shape-spec-env-slice then obj))
            ((mv else-ok else-bslice else-vslice)
             (shape-spec-env-slice else obj))
            ((mv if-t-ok if-t-bslice if-t-vslice)
             (shape-spec-iff-env-slice if t))
            ((mv if-nil-ok if-nil-bslice if-nil-vslice)
             (shape-spec-iff-env-slice if nil)))
         (if (and then-ok if-t-ok)
             (mv t (append if-t-bslice then-bslice else-bslice)
                 (append if-t-vslice then-vslice else-vslice))
           (mv (and else-ok if-nil-ok)
               (append if-nil-bslice then-bslice else-bslice)
               (append if-nil-vslice then-vslice else-vslice)))))
      ((g-concrete y)
       (mv (equal obj y) nil nil))
      (& (b* (((mv car-ok car-bslice car-vslice)
               (shape-spec-env-slice (car x) (ec-call (car obj))))
              ((mv cdr-ok cdr-bslice cdr-vslice)
               (shape-spec-env-slice (cdr x) (ec-call (cdr obj)))))
           (mv (and (consp obj) car-ok cdr-ok)
               (append car-bslice cdr-bslice)
               (append car-vslice cdr-vslice)))))))

(local
 (defthm true-listp-shape-spec-env-slice-1
   (true-listp (mv-nth 1 (shape-spec-env-slice x obj)))
   :hints(("Goal" :in-theory (enable shape-spec-env-slice)))))

(local
 (defthm true-listp-shape-spec-env-slice-2
   (true-listp (mv-nth 2 (shape-spec-env-slice x obj)))
   :hints(("Goal" :in-theory (enable shape-spec-env-slice)))))

(verify-guards shape-spec-env-slice
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
      ((g-boolean n) (g-boolean (bfr-var n)))
      ((g-var &) x)
      ((g-ite if then else)
       (g-ite (shape-spec-to-gobj if)
              (shape-spec-to-gobj then)
              (shape-spec-to-gobj else)))
      ((g-concrete &) x)
      (& (cons (shape-spec-to-gobj (car x))
               (shape-spec-to-gobj (cdr x)))))))






(local
 (defthm bfr-listp-numlist-to-vars
   (implies (nat-listp x)
            (bfr-listp (numlist-to-vars x)))
   :hints(("Goal" :in-theory (enable numlist-to-vars nat-listp)))))

(local
 (defthm wf-g-numberp-num-spec-to-num-gobj
   (implies (number-specp x)
            (wf-g-numberp (num-spec-to-num-gobj x)))
   :hints(("Goal" :in-theory (enable wf-g-numberp num-spec-to-num-gobj
                                     number-specp)))))

(defthm gobjectp-shape-spec-to-gobj
  (implies (shape-specp x)
           (gobjectp (shape-spec-to-gobj x)))
  :hints(("Goal" :in-theory
          (enable gobjectp-def shape-specp shape-spec-to-gobj g-var-p
                  g-concrete-p tag))))


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
                   (hons-assoc-equal key v1)))))

(local
 (defthm hons-assoc-equal-append-2
   (implies (and (alistp v1)
                 (not (member-equal key (strip-cars v1))))
            (equal (hons-assoc-equal key (append v1 v2))
                   (hons-assoc-equal key v2)))))

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
   :hints(("Goal" :in-theory (enable slice-to-bdd-env nat-listp)))))



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

(local
 (defthm g-boolean-p-gobj-fix
   (equal (g-boolean-p (gobj-fix x))
          (and (gobjectp x)
               (g-boolean-p x)))
   :hints(("Goal" :in-theory (enable gobj-fix)))))

(local
 (defthm g-number-p-gobj-fix
   (equal (g-number-p (gobj-fix x))
          (and (gobjectp x)
               (g-number-p x)))
   :hints(("Goal" :in-theory (enable gobj-fix)))))

(local
 (defthm g-ite-p-gobj-fix
   (equal (g-ite-p (gobj-fix x))
          (and (gobjectp x)
               (g-ite-p x)))
   :hints(("Goal" :in-theory (enable gobj-fix)))))

(local
 (defthm g-var-p-gobj-fix
   (equal (g-var-p (gobj-fix x))
          (and (gobjectp x)
               (g-var-p x)))
   :hints(("Goal" :in-theory (enable gobj-fix)))))

(local
 (defthm g-apply-p-gobj-fix
   (equal (g-apply-p (gobj-fix x))
          (and (gobjectp x)
               (g-apply-p x)))
   :hints(("Goal" :in-theory (enable gobj-fix)))))

(local
 (defthm g-concrete-p-gobj-fix
   (equal (g-concrete-p (gobj-fix x))
          (or (not (gobjectp x))
              (g-concrete-p x)))
   :hints(("Goal" :in-theory (enable gobj-fix)))))


(local
 (defthm shape-spec-to-gobj-eval-slice-subset-append-1
   (implies (and (shape-specp x)
                 (alistp vsl1)
                 (subsetp-equal (shape-spec-indices x)
                                (strip-cars bsl1)))
            (equal (generic-geval
                    (shape-spec-to-gobj x)
                    (cons (slice-to-bdd-env
                           (append bsl1 bsl2) env)
                          vsl1))
                   (generic-geval
                    (shape-spec-to-gobj x)
                    (cons (slice-to-bdd-env
                           bsl1 env)
                          vsl1))))
   :hints(("Goal" :in-theory (e/d (break-g-number
                                   num-spec-to-num-gobj
                                   number-spec-indices
                                   number-specp
                                   subsetp-equal
                                   wf-g-numberp-simpler-def
                                   (:induction shape-spec-to-gobj))
                                  (member-equal
                                   boolean-listp
                                   binary-append))
           :induct (shape-spec-to-gobj x)
           :expand ((shape-spec-to-gobj x)
                    (shape-spec-indices x)
                    (shape-spec-vars x)
                    (shape-specp x)))
          (and stable-under-simplificationp
               (flag::expand-calls-computed-hint
                acl2::clause '(generic-geval))))))


(local
 (defthm shape-spec-to-gobj-eval-slice-subset-append-2
   (implies (and (shape-specp x)
                 (alistp vsl1)
                 (subsetp-equal (shape-spec-vars x)
                                (strip-cars vsl1)))
            (equal (generic-geval
                    (shape-spec-to-gobj x)
                    (cons (slice-to-bdd-env
                           bsl1 env)
                          (append vsl1 vsl2)))
                   (generic-geval
                    (shape-spec-to-gobj x)
                    (cons (slice-to-bdd-env
                           bsl1 env)
                          vsl1))))
   :hints(("Goal" :in-theory (e/d (break-g-number
                                   num-spec-to-num-gobj
                                   number-spec-indices
                                   number-specp
                                   subsetp-equal
                                   wf-g-numberp-simpler-def
                                   (:induction shape-spec-to-gobj))
                                  (member-equal
                                   boolean-listp
                                   binary-append))
           :induct (shape-spec-to-gobj x)
           :expand ((shape-spec-to-gobj x)
                    (shape-spec-indices x)
                    (shape-spec-vars x)
                    (shape-specp x)))
          (and stable-under-simplificationp
               (flag::expand-calls-computed-hint
                acl2::clause '(generic-geval))))))



(local
 (defthm shape-spec-to-gobj-eval-slice-no-intersect-append-1
   (implies (and (shape-specp x)
                 (alistp vsl1)
                 (nat-listp (strip-cars bsl1))
                 (not (intersectp-equal
                       (shape-spec-indices x)
                       (strip-cars bsl1))))
            (equal (generic-geval
                    (shape-spec-to-gobj x)
                    (cons (slice-to-bdd-env
                           (append bsl1 bsl2) env)
                          vsl1))
                   (generic-geval
                    (shape-spec-to-gobj x)
                    (cons (slice-to-bdd-env
                           bsl2 env)
                          vsl1))))
   :hints(("Goal" :in-theory (e/d (break-g-number
                                   num-spec-to-num-gobj
                                   number-spec-indices
                                   number-specp
                                   wf-g-numberp-simpler-def
                                   (:induction shape-spec-to-gobj))
                                  (member-equal
                                   boolean-listp
                                   binary-append))
           :induct (shape-spec-to-gobj x)
           :expand ((shape-spec-to-gobj x)
                    (shape-spec-indices x)
                    (shape-spec-vars x)
                    (shape-specp x)))
          (and stable-under-simplificationp
               (flag::expand-calls-computed-hint
                acl2::clause '(generic-geval))))))


(local
 (defthm shape-spec-to-gobj-eval-slice-no-intersect-append-2
   (implies (and (shape-specp x)
                 (alistp vsl1)
                 (not (intersectp-equal (shape-spec-vars x)
                                        (strip-cars vsl1))))
            (equal (generic-geval
                    (shape-spec-to-gobj x)
                    (cons (slice-to-bdd-env
                           bsl1 env)
                          (append vsl1 vsl2)))
                   (generic-geval
                    (shape-spec-to-gobj x)
                    (cons (slice-to-bdd-env
                           bsl1 env)
                          vsl2))))
   :hints(("Goal" :in-theory (e/d (break-g-number
                                   num-spec-to-num-gobj
                                   number-spec-indices
                                   number-specp
                                   subsetp-equal
                                   wf-g-numberp-simpler-def
                                   (:induction shape-spec-to-gobj))
                                  (member-equal
                                   acl2::hons-assoc-equal-append
                                   boolean-listp
                                   binary-append))
           :induct (shape-spec-to-gobj x)
           :expand ((shape-spec-to-gobj x)
                    (shape-spec-indices x)
                    (shape-spec-vars x)
                    (shape-specp x)))
          (and stable-under-simplificationp
               (flag::expand-calls-computed-hint
                acl2::clause '(generic-geval))))))


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
 (defthm generic-geval-of-g-ite
   (implies (and (gobjectp if) (gobjectp then) (gobjectp else))
            (equal (generic-geval (g-ite if then else) env)
                   (if (generic-geval if env)
                       (generic-geval then env)
                     (generic-geval else env))))
   :hints(("Goal" :in-theory (enable generic-geval)))))


(local
 (encapsulate nil
   (local
    (defthm g-concrete-tag-gobjectp
      (implies (equal (car x) :g-concrete)
               (gobjectp x))
      :hints(("Goal" :in-theory (enable gobjectp-def g-concrete-p tag)))
      :rule-classes ((:rewrite :backchain-limit-lst 0))))

   (defthm generic-geval-when-g-concrete-tag
     (implies (equal (tag x) :g-concrete)
              (equal (generic-geval x env)
                     (g-concrete->obj x)))
     :hints(("Goal" :in-theory (enable tag g-concrete-p generic-geval)))
     :rule-classes ((:rewrite :backchain-limit-lst 0)))))


(local
 (encapsulate nil
   (local
    (defthm g-var-tag-gobjectp
      (implies (equal (car x) :g-var)
               (gobjectp x))
      :hints(("Goal" :in-theory (enable gobjectp-def g-var-p tag)))))
   (defthm generic-geval-when-g-var-tag
     (implies (equal (tag x) :g-var)
              (equal (generic-geval x env)
                     (cdr (hons-assoc-equal (g-var->name x) (cdr env)))))
     :hints(("Goal" :in-theory (enable tag g-var-p generic-geval))))))

(local (in-theory (disable member-equal equal-of-booleans-rewrite binary-append
                           intersectp-equal subsetp-equal
                           tag-when-g-var-p
                           tag-when-g-ite-p
                           tag-when-g-apply-p
                           tag-when-g-number-p
                           tag-when-g-boolean-p
                           tag-when-g-concrete-p)))

;; (in-theory (disable no-duplicates-append-implies-no-intersect))

(local
 (encapsulate nil
   (local (in-theory (disable gobjectp-cons-case
                              sets::double-containment
                              generic-geval-non-gobjectp
                              acl2::no-duplicatesp-equal-non-cons
                              acl2::subsetp-car-member-equal
                              g-ite-p-gobj-fix
                              generic-geval)))
   (defthm shape-spec-to-gobj-eval-iff-slice
     (implies (and (shape-specp x)
                   (no-duplicatesp (shape-spec-indices x))
                   (no-duplicatesp (shape-spec-vars x))
                   (mv-nth 0 (shape-spec-iff-env-slice x obj)))
              (iff (generic-geval
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
                             (generic-geval (cons a b) env))))
            (and stable-under-simplificationp
                 '(:in-theory (enable generic-geval)))
            (and stable-under-simplificationp
                 '(:in-theory (enable slice-to-bdd-env generic-geval)))))))

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
 (encapsulate nil
   (local (in-theory (e/d (ash) (floor))))
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


(local
 (defthmd g-var-p-implies-gobjectp
   (implies (g-var-p x)
            (gobjectp x))
   :hints (("goal" :in-theory (enable gobjectp-def g-var-p tag)))
   :rule-classes ((:rewrite :backchain-limit-lst 0))))

(local
 (defthm gobjectp-g-number
   (implies (wf-g-numberp x)
            (gobjectp (g-number x)))
   :hints(("Goal" :in-theory (enable gobjectp-def g-number-p tag)))))

(local
 (defthmd g-concrete-p-gobjectp1
   (implies (g-concrete-p x)
            (gobjectp x))
   :hints(("Goal" :in-theory (enable gobjectp-def g-concrete-p tag)))
   :rule-classes ((:rewrite :backchain-limit-lst 0))))



(local
 (encapsulate nil
   (local (in-theory
           (e/d () (gobjectp-tag-rw-to-types
                    gobjectp-ite-case
                    generic-geval-non-gobjectp
                    break-g-number
                    gobj-fix-when-not-gobjectp))))
   (defthm shape-spec-to-gobj-eval-slice
     (implies (and (shape-specp x)
                   (no-duplicatesp (shape-spec-indices x))
                   (no-duplicatesp (shape-spec-vars x))
                   (mv-nth 0 (shape-spec-env-slice x obj)))
              (equal (generic-geval
                      (shape-spec-to-gobj x)
                      (cons (slice-to-bdd-env
                             (mv-nth 1 (shape-spec-env-slice x obj))
                             env)
                            (mv-nth 2 (shape-spec-env-slice x obj))))
                     obj))
     :hints(("Goal" :in-theory (enable shape-spec-to-gobj
                                       shape-spec-indices
                                       shape-spec-vars
                                       shape-spec-env-slice
                                       shape-specp)
             :induct (shape-spec-env-slice x obj))
            (and stable-under-simplificationp
                 '(:in-theory (enable generic-geval break-g-number
                                      number-spec-env-slice
                                      number-specp
                                      number-spec-indices
                                      wf-g-numberp-simpler-def
                                      num-spec-to-num-gobj)))
            (and stable-under-simplificationp
                 '(:in-theory (enable slice-to-bdd-env generic-geval
                                      gobj-fix gobjectp)))))))
  
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


(defund shape-spec-obj-in-range-iff (x obj)
  (declare (xargs :guard (shape-specp x)
                  :guard-hints(("Goal" :in-theory (enable shape-specp)))))
  (if (atom x)
      (iff x obj)
    (pattern-match x
      ((g-number &)
       obj)
      ((g-boolean &) t)
      ((g-var &) t)
      ((g-ite if then else)
       (or (and (shape-spec-obj-in-range-iff if t)
                (shape-spec-obj-in-range-iff then obj))
           (and (shape-spec-obj-in-range-iff if nil)
                (shape-spec-obj-in-range-iff else obj))))
      ((g-concrete y) (iff y obj))
      (& obj))))

(local
 (defthm shape-spec-obj-in-range-iff-shape-spec-iff-env-slice
   (iff (mv-nth 0 (shape-spec-iff-env-slice x obj))
        (shape-spec-obj-in-range-iff x obj))
   :hints(("Goal" :in-theory (enable shape-spec-obj-in-range-iff
                                     shape-spec-iff-env-slice)))))

(defund integer-in-range (vlist obj)
  (declare (xargs :guard t))
  (and (integerp obj)
       (if (atom vlist)
           (eql obj 0)
         (and (<= (- (ash 1 (len (cdr vlist)))) obj)
              (< obj (ash 1 (len (cdr vlist))))))))

(local
 (encapsulate nil
   (local (include-book "ihs/ihs-lemmas" :dir :system))
   (local (in-theory (e/d (ash) (floor))))
   (local (defthm expt-2-of-posp
            (implies (posp x)
                     (integerp (* 1/2 (expt 2 x))))
            :rule-classes nil))
   (local
    (encapsulate nil
      (local (defthm rw-equal-minus
               (implies (and (posp x) (rationalp y))
                        (equal (equal (expt 2 x) (- y))
                               (equal (- (expt 2 x)) y)))))
      (defthm negative-expt-2-of-posp
        (implies (and (posp x) (rationalp y)
                      (equal (expt 2 x) (- y)))
                 (integerp (* 1/2 y)))
        :rule-classes nil)))

   (defthm integer-in-range-integer-env-slice
     (implies (integerp obj)
              (equal (mv-nth 0 (integer-env-slice vlist obj))
                     (integer-in-range vlist obj)))
     :hints(("Goal" :in-theory (enable integer-env-slice
                                       integer-in-range))
            ("Subgoal *1/4.4"
             :use ((:instance negative-expt-2-of-posp
                              (x (+ 1 (len (cddr vlist))))
                              (y obj))))))))

(defund natural-in-range (vlist obj)
  (declare (xargs :guard t))
  (and (natp obj)
       (and (<= 0 obj)
            (< obj (ash 1 (len vlist))))))

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

(defund number-spec-in-range (nspec obj)
  (declare (xargs :guard (number-specp nspec)
                  :guard-hints(("Goal" :in-theory (enable number-specp)))))
  (and (acl2-numberp obj)
       (integer-in-range (car nspec) (numerator (realpart obj)))
       (if (consp (cdr nspec))
           (and (natural-in-range (cadr nspec) (denominator (realpart obj)))
                (if (consp (cddr nspec))
                    (and (integer-in-range
                          (caddr nspec) (numerator (imagpart obj)))
                         (if (consp (cdddr nspec))
                             (natural-in-range
                              (cadddr nspec) (denominator (imagpart obj)))
                           (eql (denominator (imagpart obj)) 1)))
                  (rationalp obj)))
         (integerp obj))))

(local
 (defthm number-spec-in-range-number-spec-env-slice
   (equal (mv-nth 0 (number-spec-env-slice nspec obj))
          (number-spec-in-range nspec obj))
   :hints(("Goal" :in-theory (enable number-spec-env-slice
                                     number-spec-in-range)))))


(defund shape-spec-obj-in-range (x obj)
  (declare (xargs :guard (shape-specp x)
                  :guard-hints(("Goal" :in-theory (enable shape-specp)))))
  (if (atom x)
      (equal x obj)
    (pattern-match x
      ((g-number n) (number-spec-in-range n obj))
      ((g-boolean &) (booleanp obj))
      ((g-var &) t)
      ((g-concrete y) (equal y obj))
      ((g-ite if then else)
       (or (and (shape-spec-obj-in-range-iff if t)
                (shape-spec-obj-in-range then obj))
           (and (shape-spec-obj-in-range-iff if nil)
                (shape-spec-obj-in-range else obj))))
      (& (and (consp obj)
              (shape-spec-obj-in-range (car x) (car obj))
              (shape-spec-obj-in-range (cdr x) (cdr obj)))))))

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
           (equal (generic-geval
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

(defthm shape-spec-listp-impl-shape-spec-to-gobj-list
  (implies (shape-spec-listp x)
           (equal (shape-spec-to-gobj x)
                  (shape-spec-to-gobj-list x)))
  :hints(("Goal" :induct (shape-spec-to-gobj-list x)
          :expand ((shape-spec-to-gobj x))
          :in-theory (enable tag))))





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






(defthm shape-spec-alt-definition
  (equal (shape-spec-obj-in-range x obj)
         (if (atom x)
             (equal obj x)
           (case (car x)
             (:g-number (number-spec-in-range (cdr x) obj))
             (:g-boolean (booleanp obj))
             (:g-var t)
             (:g-concrete (equal obj (cdr x)))
             (:g-ite (let ((test (cadr x)) (then (caddr x)) (else (cdddr x)))
                       (or (and (shape-spec-obj-in-range-iff test t)
                                (shape-spec-obj-in-range then obj))
                           (and (shape-spec-obj-in-range-iff test nil)
                                (shape-spec-obj-in-range else obj)))))
             (t (and (consp obj)
                     (shape-spec-obj-in-range (car x) (car obj))
                     (shape-spec-obj-in-range (cdr x) (cdr obj)))))))
  :hints(("Goal" :in-theory (enable tag g-number->num g-concrete->obj
                                    g-ite->test g-ite->then g-ite->else)
          :expand ((shape-spec-obj-in-range x obj))))
  :rule-classes ((:definition :controller-alist ((shape-spec-obj-in-range t
                                                                          nil)))))

(local
 (defun shape-spec-alt-induction (x obj)
   (if (atom x)
       (equal obj x)
     (case (car x)
       (:g-number (number-spec-in-range (cdr x) obj))
       (:g-boolean (booleanp obj))
       (:g-var t)
       (:g-concrete (equal obj (cdr x)))
       (:g-ite (let ((then (caddr x)) (else (cdddr x)))
                 (list (shape-spec-alt-induction then obj)
                       (shape-spec-alt-induction else obj))))
       (t (list (shape-spec-alt-induction (car x) (car obj))
                (shape-spec-alt-induction (cdr x) (cdr obj))))))))



(in-theory (disable shape-spec-obj-in-range))

(local (in-theory (disable shape-spec-alt-definition)))


(defthm shape-spec-obj-in-range-open-cons
  (implies (and (not (g-keyword-symbolp (car obj)))
                (consp obj))
           (equal (shape-spec-obj-in-range obj (cons carx cdrx))
                  (and (shape-spec-obj-in-range (car obj) carx)
                       (shape-spec-obj-in-range (cdr obj) cdrx))))
  :hints(("Goal" :in-theory (enable shape-spec-alt-definition
                                    g-keyword-symbolp-def
                                    member-equal)))
  :rule-classes ((:rewrite :backchain-limit-lst (1 0))))

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

(defthm shape-spec-obj-in-range-open-integer
  (equal (shape-spec-obj-in-range `(:g-number ,bits) x)
         (if (consp bits)
             (and* (integerp x)
                   (<= (- (expt 2 (1- (len bits)))) x)
                   (< x (expt 2 (1- (len bits)))))
           (equal x 0)))
  :hints(("Goal" :in-theory (enable shape-spec-alt-definition
                                    number-spec-in-range
                                    integer-in-range
                                    g-number->num
                                    natp-len-minus-one
                                    ash-1-is-expt-2))))

(defthm shape-spec-obj-in-range-open-boolean
  (equal (shape-spec-obj-in-range `(:g-boolean . ,bit) x)
         (booleanp x))
  :hints(("Goal" :in-theory (enable shape-spec-alt-definition))))



(defthm shape-spec-obj-in-range-open-atom
  (implies (atom a)
           (equal (shape-spec-obj-in-range a x)
                  (equal x a)))
  :hints(("Goal" :in-theory (enable shape-spec-alt-definition
                                    g-concrete->obj)))
  :rule-classes ((:rewrite :backchain-limit-lst 1)))

(defthm shape-spec-obj-in-range-backchain-atom
  (implies (and (atom a)
                (equal x a))
           (equal (shape-spec-obj-in-range a x) t))
  :hints(("Goal" :in-theory (enable shape-spec-alt-definition
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
          :induct (shape-spec-alt-induction lst obj)
          :in-theory (enable shape-spec-alt-definition tag
                             list-of-g-booleansp
                             boolean-listp))))


(defthm shape-spec-obj-in-range-backchain-list-of-g-booleans
  (implies (and (list-of-g-booleansp lst)
                (boolean-listp obj)
                (equal (len obj) (len lst)))
           (equal (shape-spec-obj-in-range lst obj) t)))



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
    (car) (cdr) (booleanp) (list-of-g-booleansp)
    eql len-plus-one len-zero (zp) (boolean-listp) (true-listp)))

(def-ruleset! shape-spec-obj-in-range-open
  '(shape-spec-obj-in-range-open-cons
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
    (car) (cdr) (booleanp) (list-of-g-booleansp) eql
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
