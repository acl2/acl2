

(in-package "GL")


(include-book "symbolic-arithmetic-fns")
(local (include-book "hyp-fix-logic"))
(include-book "g-if")
(local (include-book "eval-g-base-help"))
(include-book "eval-g-base")



;; This introduces a symbolic counterpart function for EQUAL (more
;; specifically, for ALWAYS-EQUAL, which is defined as EQUAL) that takes a
;; shortcut.  In many cases, it's easy to tell that two symbolic objects are
;; always equal, or that they're sometimes unequal, but it may be very
;; expensive to determine exactly when they're equal or unequal, which the
;; original symbolic counterpart of EQUAL tries to do in all cases.  This
;; function will instead try to cheaply determine whether the objects are
;; always equal, and if not, it will try to cheaply come up with a
;; counterexample or else produce an APPLY object.  In the counterexample case,
;; the object it produces looks something like this:
;; (g-ite (g-boolean <counterexample-bdd>) nil (g-apply 'equal (list a b))).
;; That is, in some particular case (when <counterexample-bdd> is true) the
;; equality is known to be untrue, and in all other cases it's unknown.
;; In odd cases such as numbers wherein the denominators are nontrivial, we'll
;; just punt and produce an apply object.



(defun acl2::always-equal (x y)
  (declare (Xargs :guard t))
  (equal x y))

;; X and Y should be unequal BDDs.  This produces a BDD with one path to a T,
;; with the guarantee that X and Y are unequal on that path.
(defun ctrex-for-always-equal (x y)
  (declare (xargs :guard t :measure (+ (acl2-count x) (acl2-count y))))
  (if (and (atom x) (atom y))
      t
    (b* (((mv xa xd) (if (consp x) (mv (car x) (cdr x)) (mv x x)))
         ((mv ya yd) (if (consp y) (mv (car y) (cdr y)) (mv y y))))
      (if (hqual xa ya)
          (cons nil (ctrex-for-always-equal xd yd))
        (cons (ctrex-for-always-equal xa ya) nil)))))

(local
 (progn
   (defun ctrex-for-always-equal-ind (x y env)
     (declare (xargs :measure (+ (acl2-count x) (acl2-count y))))
     (if (and (atom x) (atom y))
         env
       (b* (((mv xa xd) (if (consp x) (mv (car x) (cdr x)) (mv x x)))
            ((mv ya yd) (if (consp y) (mv (car y) (cdr y)) (mv y y))))
         (if (hqual xa ya)
             (cons nil (ctrex-for-always-equal-ind xd yd (cdr env)))
           (cons (ctrex-for-always-equal-ind xa ya (cdr env)) nil)))))

   (defthmd ctrex-for-always-equal-correct
     (implies (and (acl2::ubddp x) (acl2::ubddp y) (not (equal x y))
                   (acl2::eval-bdd (ctrex-for-always-equal x y) env))
              (not (equal (acl2::eval-bdd x env) (acl2::eval-bdd y env))))
     :hints (("goal" :induct (ctrex-for-always-equal-ind x y env)
              :in-theory (enable acl2::eval-bdd acl2::ubddp))))

   (defthm ctrex-for-always-equal-correct2
     (implies (and (acl2::ubddp x) (acl2::ubddp y) (not (equal x y))
                   (equal (acl2::eval-bdd x env) (acl2::eval-bdd y env)))
              (not (acl2::eval-bdd (ctrex-for-always-equal x y) env)))
     :hints(("Goal" :in-theory (enable ctrex-for-always-equal-correct))))
      
   (defthm acl2::ubddp-ctrex-for-always-equal
     (acl2::ubddp (ctrex-for-always-equal a b))
     :hints(("Goal" :in-theory (enable acl2::ubddp))))))




;; This produces either: a BDD with one path to a T, with the guarantee that X
;; and Y are unequal on that path and that the hyp holds on that path; or NIL,
;; meaning X and Y are equal everywhere the hyp holds.

;; This is used as a helper function for the top-level
;; ctrex-for-always-equal-under-hyp, but it is actually complete; the top-level
;; function just tries to find an easier answer first.
(defun ctrex-for-always-equal-under-hyp1 (x y hyp)
  (declare (xargs :guard t))
  (cond ((hqual x y) nil)
        ((eq hyp nil) nil)
        ((atom hyp) (ctrex-for-always-equal x y))
        ((and (atom x) (atom y))
         (ctrex-for-always-equal hyp nil))
        ((eq (cdr hyp) nil)
         (let ((res
                (ctrex-for-always-equal-under-hyp1
                 (if (consp x) (car x) x)
                 (if (consp y) (car y) y)
                 (car hyp))))
           (and res (cons res nil))))
        ((eq (car hyp) nil)
         (let ((res (ctrex-for-always-equal-under-hyp1
                     (if (consp x) (cdr x) x)
                     (if (consp y) (cdr y) y)
                     (cdr hyp))))
           (and res (cons nil res))))
        (t (let ((x1 (acl2::q-and hyp x))
                 (y1 (acl2::q-and hyp y)))
             (if (hqual x1 y1)
                 nil
               (ctrex-for-always-equal x1 y1))))))

(local
 (defthm ctrex-for-always-equal-under-hyp1-ubddp
   (implies (and (acl2::ubddp x) (acl2::ubddp y) (acl2::ubddp hyp))
            (acl2::ubddp (ctrex-for-always-equal-under-hyp1 x y hyp)))
   :hints(("Goal" :in-theory (enable acl2::ubddp)
           :induct (ctrex-for-always-equal-under-hyp1 x y hyp)))))







(local
 (progn


   (defun ctrex-for-always-equal-under-hyp-ind (x y hyp env)
     (cond ((hqual x y) env)
           ((eq hyp nil) env)
           ((atom hyp) env)
           (t (if (car env)
                  (ctrex-for-always-equal-under-hyp-ind
                   (if (consp x) (car x) x)
                   (if (consp y) (car y) y)
                   (car hyp) (cdr env))
                (ctrex-for-always-equal-under-hyp-ind
                 (if (consp x) (cdr x) x)
                 (if (consp y) (cdr y) y)
                 (cdr hyp) (cdr env))))))

   (defthm ctrex-for-always-equal-under-hyp1-correct1
     (implies (and (not (and (acl2::eval-bdd hyp env)
                             (not (equal (acl2::eval-bdd x env) (acl2::eval-bdd y env)))))
                   (acl2::ubddp x) (acl2::ubddp y) (acl2::ubddp hyp))
              (not (acl2::eval-bdd (ctrex-for-always-equal-under-hyp1 x y hyp) env)))
     :hints(("Goal" :in-theory (e/d* (acl2::ubddp)
                                     (ctrex-for-always-equal-under-hyp1
                                      acl2::eval-bdd-when-qs-subset
                                      ctrex-for-always-equal
                                      acl2::eval-bdd-when-not-consp
                                      acl2::eval-bdd-of-non-consp-cheap
                                      acl2::ubddp-compound-recognizer
                                      (:rules-of-class :type-prescription :here)
;                                      acl2::eval-bdd-booleanp
                                      equal-of-booleans-rewrite)
                                     ((:type-prescription acl2::eval-bdd)))
             :induct (ctrex-for-always-equal-under-hyp-ind x y hyp env)
             :expand
             ((:free (x y) (ctrex-for-always-equal-under-hyp1 x y hyp))
              (:free (x y) (ctrex-for-always-equal-under-hyp1 x y t))
              (:free (x y) (ctrex-for-always-equal-under-hyp1 x y nil))
              (:free (x y env) (acl2::eval-bdd (cons x y) env))
              (:free (env) (acl2::eval-bdd x env))
              (:free (env) (acl2::eval-bdd y env))))))

   (defthm hyp-eval-lemma
     (implies (and (syntaxp (eq hyp 'hyp)) (consp hyp))
              (and (implies (and (not (car env))
                                 (not (acl2::eval-bdd (cdr hyp) (cdr env))))
                            (not (acl2::eval-bdd hyp env)))
                   (implies (and (car env)
                                 (not (acl2::eval-bdd (car hyp) (cdr env))))
                            (not (acl2::eval-bdd hyp env)))))
     :hints(("Goal" :in-theory (enable acl2::eval-bdd))))


   (defthm ctrex-for-always-equal-under-hyp1-correct2
     (implies (and (bind-free '((env . (cdr env))) (env))
                   (not (equal (acl2::eval-bdd x env) (acl2::eval-bdd y env)))
                   (acl2::eval-bdd hyp env)
                   (acl2::ubddp x) (acl2::ubddp y) (acl2::ubddp hyp))
              (ctrex-for-always-equal-under-hyp1 x y hyp))
     :hints(("Goal" :in-theory (e/d* (acl2::ubddp)
                                     (ctrex-for-always-equal-under-hyp1
                                      acl2::eval-bdd-when-qs-subset
                                      ctrex-for-always-equal
                                      acl2::eval-bdd-when-not-consp
                                      ; acl2::eval-bdd-of-non-consp-cheap
                                      equal-of-booleans-rewrite
                                      (:rules-of-class :type-prescription :here))
                                     ((:type-prescription acl2::eval-bdd)
                                      (:type-prescription ctrex-for-always-equal)))
             :induct (ctrex-for-always-equal-under-hyp-ind x y hyp env)
             :do-not-induct t
             :expand
             ((:free (x y) (ctrex-for-always-equal-under-hyp1 x y hyp))
              (:free (x y) (ctrex-for-always-equal-under-hyp1 x y t))
              (:free (x y) (ctrex-for-always-equal-under-hyp1 x y nil))))
            (and stable-under-simplificationp
                 '(:clause-processor
                   (acl2::eval-bdd-cp 
                    clause (list '(x y hyp)
                                 (let ((world (w state))) (acl2::bdd-patterns))
                                 ;; '(env)
                                 t))))
            (and stable-under-simplificationp
                 '(:expand ((acl2::eval-bdd x env)
                            (acl2::eval-bdd y env))))))))





(in-theory (Disable ctrex-for-always-equal-under-hyp1))



(defun ctrex-for-always-equal-under-hyp (x y hyp)
  (declare (xargs :guard t :measure (acl2-count hyp)))
  (cond ((hqual x y) nil)
        ((eq hyp nil) nil)
        ((atom hyp) (ctrex-for-always-equal x y))
        ((eq (cdr hyp) nil)
         (let ((res (ctrex-for-always-equal-under-hyp
                     (if (consp x) (car x) x)
                     (if (consp y) (car y) y)
                     (car hyp))))
           (and res (cons res nil))))
        ((eq (car hyp) nil)
         (let ((res (ctrex-for-always-equal-under-hyp
                     (if (consp x) (cdr x) x)
                     (if (consp y) (cdr y) y)
                     (cdr hyp))))
           (and res (cons nil res))))
        ;; The bad case here is when x and y are equal wherever the hyp holds
        ;; and unequal everywhere else. 
        ;; Possible ways to deal with this: Q-AND the hyp with each arg and
        ;; compare equality, or else recur on the car and then the cdr.  
        ;; We take a hybrid approch: recur down the car in hopes of finding an
        ;; easy counterexample, then at each level, use the Q-AND approch on
        ;; the cdr.
        (t (let ((car-result (ctrex-for-always-equal-under-hyp
                              (if (consp x) (car x) x)
                              (if (consp y) (car y) y)
                              (car hyp))))
             (if car-result
                 (cons car-result nil)
               (let ((cdr-result (ctrex-for-always-equal-under-hyp1
                                  (if (consp x) (cdr x) x)
                                  (if (consp y) (cdr y) y)
                                  (cdr hyp))))
                 (and cdr-result
                      (cons nil cdr-result))))))))

(local (defthm ctrex-for-always-equal-under-hyp-ubddp
         (implies (and (acl2::ubddp x) (acl2::ubddp y) (acl2::ubddp hyp))
                  (acl2::ubddp (ctrex-for-always-equal-under-hyp x y hyp)))
         :hints(("Goal" :in-theory (enable acl2::ubddp)))))

;; (local (defthm ctrex-for-always-equal-under-hyp-bfr-p
;;          (implies (and (not (bfr-mode))
;;                        (bfr-p x) (bfr-p y) (bfr-p hyp))
;;                   (bfr-p (ctrex-for-always-equal-under-hyp x y hyp)))
;;          :hints(("Goal" :use ctrex-for-always-equal-under-hyp-ubddp
;;                  :in-theory (e/d (bfr-p booleanp)
;;                                  (ctrex-for-always-equal-under-hyp-ubddp))))))


(local
 (defthm ctrex-for-always-equal-under-hyp-correct1
   (implies (and (acl2::eval-bdd (ctrex-for-always-equal-under-hyp x y hyp) env)
                 (acl2::ubddp x) (acl2::ubddp y) (acl2::ubddp hyp))
            (and (acl2::eval-bdd hyp env)
                 (equal (acl2::eval-bdd x env)
                        (not (acl2::eval-bdd y env)))))
   :hints(("Goal" :in-theory (e/d* (acl2::ubddp)
                                   (ctrex-for-always-equal-under-hyp
                                    acl2::eval-bdd-when-qs-subset
                                    equal-of-booleans-rewrite
                                    ctrex-for-always-equal
                                    acl2::eval-bdd-when-not-consp
                                    (:rules-of-class :type-prescription :here))
                                   ((:type-prescription acl2::eval-bdd)))
           :induct (ctrex-for-always-equal-under-hyp-ind x y hyp env)
           :expand
             ((:free (x y) (ctrex-for-always-equal-under-hyp x y hyp))
              (:free (x y) (ctrex-for-always-equal-under-hyp x y t))
              (:free (x y) (ctrex-for-always-equal-under-hyp x y nil))
              (:free (x y env) (acl2::eval-bdd (cons x y) env))
              (:free (env) (acl2::eval-bdd x env))
              (:free (env) (acl2::eval-bdd y env))
              (:free (env) (acl2::eval-bdd hyp env)))))))

(local
 (defthm ctrex-for-always-equal-under-hyp-correct2
   (implies (and (not (equal (acl2::eval-bdd x env) (acl2::eval-bdd y env)))
                 (acl2::eval-bdd hyp env)
                 (acl2::ubddp x) (acl2::ubddp y) (acl2::ubddp hyp))
            (ctrex-for-always-equal-under-hyp x y hyp))
   :hints(("Goal" :in-theory (e/d* (acl2::ubddp)
                                   (ctrex-for-always-equal-under-hyp
                                    ;ctrex-for-always-equal-under-hyp1-correct2
                                    ctrex-for-always-equal-under-hyp-correct1
                                    acl2::eval-bdd-when-qs-subset
                                    ctrex-for-always-equal
                                    acl2::eval-bdd-when-not-consp
                                    ; acl2::eval-bdd-of-non-consp-cheap
                                    equal-of-booleans-rewrite
                                    (:rules-of-class :type-prescription :here))
                                   ((:type-prescription acl2::eval-bdd)
                                    (:type-prescription ctrex-for-always-equal)))
           :induct (ctrex-for-always-equal-under-hyp-ind x y hyp env)
           :do-not-induct t
           :expand
           ((:free (x y) (ctrex-for-always-equal-under-hyp x y hyp))
            (:free (x y) (ctrex-for-always-equal-under-hyp x y t))
            (:free (x y) (ctrex-for-always-equal-under-hyp x y nil))))
          (and stable-under-simplificationp
               '(:clause-processor
                 (acl2::eval-bdd-cp 
                  clause (list '(x y hyp)
                               (let ((world (w state))) (acl2::bdd-patterns))
                               ;; '(env)
                               t))))
          (and stable-under-simplificationp
               '(:expand ((acl2::eval-bdd x env)
                          (acl2::eval-bdd y env)
                          (acl2::eval-bdd hyp env)
                          (acl2::eval-bdd hyp nil)))))))



;; (local
;;  (defthm ctrex-for-always-equal-under-hyp-correct1-bfr
;;    (implies (and (not (bfr-mode))
;;                  (bfr-eval (ctrex-for-always-equal-under-hyp x y hyp) env)
;;                  (bfr-p x) (bfr-p y) (bfr-p hyp))
;;             (and (bfr-eval hyp env)
;;                  (equal (bfr-eval x env)
;;                         (not (bfr-eval y env)))))
;;    :hints(("goal" :in-theory
;;            (e/d* (bfr-p bfr-eval booleanp)
;;                  (ctrex-for-always-equal-under-hyp-correct1))
;;            :use ctrex-for-always-equal-under-hyp-correct1))))

;; (local
;;  (defthm ctrex-for-always-equal-under-hyp-correct2-bfr
;;    (implies (and (not (bfr-mode))
;;                  (not (equal (bfr-eval x env) (bfr-eval y env)))
;;                  (bfr-eval hyp env)
;;                  (bfr-p x) (bfr-p y) (bfr-p hyp))
;;             (ctrex-for-always-equal-under-hyp x y hyp))
;;    :hints(("goal" :in-theory
;;            (e/d* (bfr-p bfr-eval booleanp)
;;                  (ctrex-for-always-equal-under-hyp-correct2))
;;            :use ctrex-for-always-equal-under-hyp-correct2))))





(defun always-equal-uu (x y)
  (declare (xargs :guard t :measure (+ (acl2-count x) (acl2-count y))))
  (if (and (atom x) (atom y))
      (mv t t)
    (b* (((mv xa xd) (if (consp x) (mv (car x) (cdr x)) (mv nil nil)))
         ((mv ya yd) (if (consp y) (mv (car y) (cdr y)) (mv nil nil)))
         ((when (hqual xa ya)) (always-equal-uu xd yd))
         (xa (acl2::ubdd-fix xa))
         (ya (acl2::ubdd-fix ya))
         ((when (hqual xa ya)) (always-equal-uu xd yd)))
      (mv nil (ctrex-for-always-equal xa ya)))))

(defun always-equal-ss-under-hyp (x y hyp)
  (declare (xargs :guard t :measure (+ (acl2-count x) (acl2-count y))))
  (b* (((mv xa xd xend) (if (consp x)
                            (if (consp (cdr x))
                                (mv (car x) (cdr x) nil)
                              (mv (car x) x t))
                          (mv nil nil t)))
       ((mv ya yd yend) (if (consp y)
                            (if (consp (cdr y))
                                (mv (car y) (cdr y) nil)
                              (mv (car y) y t))
                          (mv nil nil t)))
       ((when (hqual xa ya))
        (if (and xend yend)
            (mv t t)
          (always-equal-ss-under-hyp xd yd hyp)))
       (xa (acl2::ubdd-fix xa))
       (ya (acl2::ubdd-fix ya))
       (res (ctrex-for-always-equal-under-hyp xa ya hyp)))
    (if (eq res nil)
        (if (and xend yend)
            (mv t t)
          (always-equal-ss-under-hyp xd yd hyp))
      (mv nil res))))




(local
 (encapsulate nil
  
   (local
    (progn
      (include-book "arithmetic/top-with-meta" :dir :system)

      (defthm even-not-equal-odd
        (implies (and (evenp x) (evenp y))
                 (not (equal x (+ 1 y)))))

      (defthm *-2-not-minus-1
        (implies (integerp n)
                 (not (equal (* 2 n) -1)))
        :hints (("goal" :use ((:instance even-not-equal-odd
                               (x (* 2 n)) (y -2))))))

      (defthm evenp-ash-1
        (implies (integerp x)
                 (evenp (ash x 1)))
        :hints(("Goal" :in-theory (enable ash))))

      (defthm natp-ash-1
        (implies (natp x)
                 (natp (ash x 1)))
        :hints(("Goal" :in-theory (enable ash)))
        :rule-classes :type-prescription)

      (defthm equal-ash-n
        (implies (and (integerp x) (integerp n))
                 (equal (equal (ash x 1) n)
                        (equal x (* 1/2 n))))
        :hints(("Goal" :in-theory (enable ash))))

      (defthm half-of-ash
        (implies (integerp x)
                 (equal (* 1/2 (ash x 1)) x))
        :hints(("Goal" :in-theory (enable ash))))))



   (defthm always-equal-uu-correct
     (mv-let (always-equal ctrex-bdd)
       (always-equal-uu x y)
       (implies (and (not (bfr-mode)))
                (and (implies always-equal
                              (equal (bfr-list->u x env)
                                     (bfr-list->u y env)))
                     (implies (and (not always-equal)
                                   (bfr-eval ctrex-bdd env))
                              (not (equal (bfr-list->u x env)
                                          (bfr-list->u y env)))))))
     :hints(("Goal" 
             :induct (always-equal-uu x y))
            '(:use ((:instance ctrex-for-always-equal-correct
                               (x (and (consp x) (acl2::ubdd-fix (car x))))
                               (y (and (consp y) (acl2::ubdd-fix (car y)))))
                    (:instance acl2::eval-bdd-ubdd-fix
                     (x (car x)))
                    (:instance acl2::eval-bdd-ubdd-fix
                     (x (car y))))
              :in-theory (e/d (bfr-eval bfr-eval-list)
                              (acl2::eval-bdd-ubdd-fix)))))

   (defthm always-equal-ss-under-hyp-correct
     (mv-let (always-equal ctrex-bdd)
       (always-equal-ss-under-hyp x y hyp)
       (and (implies (and always-equal
                          (not (bfr-mode))
                          (acl2::ubddp hyp)
                          (bfr-eval hyp env))
                     (equal (bfr-list->s x env)
                            (bfr-list->s y env)))
            (implies (and (not (bfr-mode))
                          (bfr-eval ctrex-bdd env)
                          (acl2::ubddp hyp)
                          (not always-equal))
                     (and (bfr-eval hyp env)
                          (not (equal (bfr-list->s x env)
                                      (bfr-list->s y env)))))))
     :hints(("Goal" :in-theory (e/d* (bfr-list->s bfr-eval scdr s-endp)
                                     (ctrex-for-always-equal-under-hyp-correct1
                                      ctrex-for-always-equal-under-hyp-correct2
                                      ctrex-for-always-equal-under-hyp
;                                      bfr-eval-when-qs-subset
                                      default-cdr default-car
                                      natp-ash-1 default-+-1 default-+-2
                                      hyp-eval-lemma
                                      acl2::eval-bdd-ubdd-fix
;;                                       bfr-eval-when-not-consp
;;                                       bfr-eval-of-non-consp-cheap
;;                                       bfr-eval-when-non-consp-values
                                      (:definition always-equal-ss-under-hyp)
                                      (:rules-of-class :type-prescription
                                                       :here))
                                     ((:type-prescription bfr-eval)
                                      (:type-prescription ash)))
             :induct (always-equal-ss-under-hyp x y hyp)
             :expand ((always-equal-ss-under-hyp x y hyp)
                      (always-equal-ss-under-hyp x nil hyp)
                      (always-equal-ss-under-hyp nil y hyp)
                      (always-equal-ss-under-hyp nil nil hyp)))
            '(:use ((:instance ctrex-for-always-equal-under-hyp-correct1
                     (x (and (consp x) (acl2::ubdd-fix (car x))))
                     (y (and (consp y) (acl2::ubdd-fix (car y)))))
                    (:instance ctrex-for-always-equal-under-hyp-correct2
                     (x (and (consp x) (acl2::ubdd-fix (car x))))
                     (y (and (consp y) (acl2::ubdd-fix (car y)))))
                    (:instance acl2::eval-bdd-ubdd-fix
                     (x (car x)))
                    (:instance acl2::eval-bdd-ubdd-fix
                     (x (car y))))))
     :rule-classes ((:rewrite :match-free :all)))))
                           


;; (local
;;  (progn



;;    (defthm bfr-p-always-equal-uu
;;      (implies (not (bfr-mode))
;;               (bfr-p (mv-nth 1 (always-equal-uu a b)))))

;;    (defthm bfr-p-always-equal-ss-under-hyp
;;      (implies (and (not (bfr-mode))
;;                    (bfr-p hyp) (bfr-listp a) (bfr-listp b))
;;               (bfr-p (mv-nth 1 (always-equal-ss-under-hyp a b hyp))))
;;      :hints (("goal" :induct (always-equal-ss-under-hyp a b hyp)
;;               :in-theory (disable (:definition always-equal-ss-under-hyp)))
;;              (and stable-under-simplificationp
;;                   (flag::expand-calls-computed-hint
;;                    clause '(always-equal-ss-under-hyp)))))))





(defun always-equal-of-numbers (a b hyp)
  (declare (xargs :guard (and (not (bfr-mode))
                              (general-numberp a)
                              (general-numberp b))))
  (b* (((mv arn ard ain aid)
        (general-number-components a))
       ((mv brn brd bin bid)
        (general-number-components b))
       ((unless (and (equal ard '(T))
                     (equal aid '(T))
                     (equal brd '(T))
                     (equal bid '(T))))
        (prog2$ (cw "Bad denominators: ~x0~%"
                    (list (equal ard '(T))
                          (equal aid '(T))
                          (equal brd '(T))
                          (equal bid '(T))))
                (g-apply 'equal (gl-list a b))))
       (uhyp (acl2::ubdd-fix hyp))
       ((mv requal rctrex)
        (always-equal-ss-under-hyp arn brn uhyp))
       ((unless requal)
        (prog2$ (cw "reals, ctrex: ~x0~%" rctrex)
                (g-if (mk-g-boolean rctrex)
                      nil
                      (g-apply 'equal (gl-list a b)))))
       ((mv iequal ictrex)
        (always-equal-ss-under-hyp ain bin uhyp))
       ((unless iequal)
        (prog2$ (cw "imags, ctrex: ~x0~%" rctrex)
                (g-if (mk-g-boolean ictrex)
                      nil
                      (g-apply 'equal (gl-list a b))))))
    t))

;; (local (defthm always-equal-of-numbers-gobjectp
;;          (implies (and (not (bfr-mode))
;;                        (gobjectp a)
;;                        (general-numberp a)
;;                        (gobjectp b)
;;                        (general-numberp b)
;;                        (bfr-p hyp))
;;                   (gobjectp (always-equal-of-numbers a b hyp)))))



(local (defthm eval-g-base-apply-of-equal
         (equal (eval-g-base-ev (list 'equal
                                      (list 'quote x)
                                      (list 'quote y))
                                a)
                (equal x y))))

(local (defthm eval-g-base-apply-of-equal-kwote-lst
         (equal (eval-g-base-ev (cons 'equal
                                      (kwote-lst (list x y)))
                                a)
                (equal x y))))

(local (defthm equal-of-components-to-number-fn
         (implies (and (integerp arn) (integerp ain)
                       (integerp brn) (integerp bin))
                  (equal (equal (components-to-number-fn
                                 arn 1 ain 1)
                                (components-to-number-fn
                                 brn 1 bin 1))
                         (and (equal arn brn)
                              (equal ain bin))))))

(local (defthm bfr-eval-of-ubdd-fix
         (implies (not (bfr-mode))
                  (equal (bfr-eval (acl2::ubdd-fix x) env)
                         (bfr-eval x env)))
         :hints(("Goal" :in-theory (enable bfr-eval)))))

(local (defthm always-equal-of-numbers-correct
         (implies (and (not (bfr-mode))
                       (general-numberp a)
                       (general-numberp b)
                       (bfr-eval hyp (car env)))
                  (equal (eval-g-base (always-equal-of-numbers a b hyp) env)
                         (equal (eval-g-base a env)
                                (eval-g-base b env))))
         :hints(("Goal" :in-theory (enable* (:ruleset general-object-possibilities)
                                            ctrex-for-always-equal-correct
                                            boolean-list-bfr-eval-list)))))

(in-theory (disable always-equal-of-numbers))


(defun always-equal-of-booleans (a b hyp)
  (declare (xargs :guard (and (not (bfr-mode))
                              (general-booleanp a)
                              (general-booleanp b))))
  (let ((av (general-boolean-value a))
        (bv (general-boolean-value b)))
    (or (hqual av bv)
        (let* ((av (acl2::ubdd-fix av))
               (bv (acl2::ubdd-fix bv)))
          (or (hqual av bv)
              (g-if
               (mk-g-boolean
                (ctrex-for-always-equal-under-hyp
                 av bv (acl2::ubdd-fix hyp)))
               nil
               (g-apply 'equal (gl-list a b))))))))

;; (local (defthm always-equal-of-booleans-gobjectp
;;          (implies (and (not (bfr-mode))
;;                        (gobjectp a)
;;                        (general-booleanp a)
;;                        (gobjectp b)
;;                        (general-booleanp b)
;;                        (bfr-p hyp))
;;                   (gobjectp (always-equal-of-booleans a b hyp)))))

(local (defthm always-equal-of-booleans-correct
         (implies (and (not (bfr-mode))
                       (general-booleanp a)
                       (general-booleanp b)
                       (bfr-eval hyp (car env)))
                  (equal (eval-g-base (always-equal-of-booleans a b hyp) env)
                         (equal (eval-g-base a env)
                                (eval-g-base b env))))
         :hints(("Goal" :in-theory (e/d (bfr-eval)
                                        (ctrex-for-always-equal-under-hyp-correct1
                                         acl2::eval-bdd-ubdd-fix))
                 :use ((:instance ctrex-for-always-equal-under-hyp-correct1
                        (x (acl2::ubdd-fix (general-boolean-value a)))
                        (y (acl2::ubdd-fix (general-boolean-value b)))
                        (hyp (acl2::ubdd-fix hyp))
                        (env (car env)))
                       (:instance acl2::eval-bdd-ubdd-fix
                        (x (general-boolean-value a))
                        (env (car env)))
                       (:instance acl2::eval-bdd-ubdd-fix
                        (x (general-boolean-value b))
                        (env (car env))))))))

(in-theory (disable always-equal-of-booleans))




(defun g-always-equal-core (a b hyp clk)
  (declare (xargs :measure (+ (acl2-count a) (Acl2-count b))
                  :guard (and (not (bfr-mode))
                              (natp clk))
                  :verify-guards nil))
  (cond ((hqual a b) t)
        ((and (general-concretep a) (general-concretep b))
         (hons-equal (general-concrete-obj a) (general-concrete-obj b)))
        ((zp clk)
         (g-apply 'equal (gl-list a b)))
        ((or (atom a)
             (not (member-eq (tag a) '(:g-ite :g-var :g-apply))))
         (cond ((or (atom b)
                    (not (member-eq (tag b) '(:g-ite :g-var :g-apply))))
                (cond
                 ((general-booleanp a)
                  (and (general-booleanp b)
                       (always-equal-of-booleans a b hyp)))
                 ((general-booleanp b) nil)
                 ((general-numberp a)
                  (and
                   (general-numberp b)
                   (always-equal-of-numbers a b hyp)))
                 ((general-numberp b) nil)
                 ((general-consp a)
                  (and
                   (general-consp b)
                   (let ((car-equal
                          (g-always-equal-core
                           (general-consp-car a)
                           (general-consp-car b)
                           hyp clk)))
                     (if (eq car-equal t)
                         (g-always-equal-core
                          (general-consp-cdr a)
                          (general-consp-cdr b)
                          hyp clk)
                       (g-if car-equal
                             (g-apply 'equal (gl-list a b))
                             nil)))))
                 (t nil)))
               ((eq (tag b) :g-ite)
                (if (zp clk)
                    (g-apply 'equal (gl-list a b))
                  (let* ((test (g-ite->test b))
                         (then (g-ite->then b))
                         (else (g-ite->else b)))
                    (g-if test
                          (g-always-equal-core a then hyp clk)
                          (g-always-equal-core a else hyp clk)))))
               (t (g-apply 'equal (gl-list a b)))))
        ((eq (tag a) :g-ite)
         (if (zp clk)
             (g-apply 'equal (gl-list a b))
           (let* ((test (g-ite->test a))
                  (then (g-ite->then a))
                  (else (g-ite->else a)))
             (g-if test
                   (g-always-equal-core then b hyp clk)
                   (g-always-equal-core else b hyp clk)))))
        (t (g-apply 'equal (gl-list a b)))))


;; (cond ((and (general-concretep a) (general-concretep b))
;;          (hqual (general-concrete-obj a) (general-concrete-obj b)))
;;       ((zp clk)
;;          (g-apply 'equal (list a b)))
;;         (t (pattern-match a
;;              ((g-ite test then else)
;;               (g-if test
;;                     (g-always-equal-core then b hyp clk)
;;                     (g-always-equal-core else b hyp clk)))
;;              (& (pattern-match b
;;                   ((g-ite test then else)
;;                    (g-if test
;;                          (g-always-equal-core a then hyp clk)
;;                          (g-always-equal-core a else hyp clk)))
;;                   ((g-var &)
;;                    (or (equal a b)
;;                        (g-apply 'equal (list a b))))
;;                   ((g-apply fn args)
;;                    (pattern-match a
;;                      ((g-apply !fn aargs)
;;                       (g-if (g-always-equal-core aargs args hyp clk)
;;                             t
;;                             (g-apply 'equal (list a b))))
;;                      (& (g-apply 'equal (list a b)))))
;;                   (& (pattern-match a
;;                        ((g-var &) (g-apply 'equal (list a b)))
;;                        ((g-apply & &) (g-apply 'equal (list a b)))
;;                        (& (cond
;;                            ((hqual a b) t)
;;                            ((general-booleanp a)
;;                             (and (general-booleanp b)
;;                                  (always-equal-of-booleans a b hyp)))
;;                            ((general-booleanp b) nil)
;;                            ((general-numberp a)
;;                             (and
;;                              (general-numberp b)
;;                              (always-equal-of-numbers a b hyp)))
;;                            ((general-numberp b) nil)
;;                            ((general-consp a)
;;                             (and
;;                              (general-consp b)
;;                              (let ((car-equal
;;                                     (g-always-equal-core
;;                                      (general-consp-car a)
;;                                      (general-consp-car b)
;;                                      hyp clk)))
;;                                (if (eq car-equal t)
;;                                    (g-always-equal-core
;;                                     (general-consp-cdr a)
;;                                     (general-consp-cdr b)
;;                                     hyp clk)
;;                                  (g-if car-equal
;;                                        (g-apply 'equal (list a b))
;;                                        nil)))))
;;                            (t nil)))))))))))

;; (defthm g-always-equal-core-gobjectp
;;   (implies (and (not (bfr-mode))
;;                 (bfr-p hyp))
;;            (gobjectp (g-always-equal-core x y hyp clk)))
;;   :hints (("Goal" :in-theory (e/d* (booleanp-gobjectp)
;;                                    ((:definition g-always-equal-core)
;;                                     general-boolean-value
;;                                     general-boolean-value-cases
;;                                     gobj-fix-when-not-gobjectp
;;                                     gobj-fix-when-gobjectp
;;                                     gobjectp-def
;;                                     general-concretep-def
;;                                     hyp-fix
;;                                     ctrex-for-always-equal
;;                                     (:type-prescription booleanp)
;;                                     (:type-prescription gobj-fix)
;;                                     (:ruleset gl-tag-rewrites)
;;                                     (:rules-of-class :type-prescription :here)
;;                                     equal-of-booleans-rewrite
;;                                     (force)))
;;            :induct (g-always-equal-core x y hyp clk)
;;            :expand ((g-always-equal-core x y hyp clk)
;;                     (g-always-equal-core x x hyp clk))
;;            :do-not-induct t)))


(encapsulate nil
  (local (in-theory (e/d* ()
                         (g-always-equal-core
                          equal-of-booleans-rewrite
                          iff-implies-equal-not
                          (:type-prescription true-under-hyp)
                          (:type-prescription false-under-hyp)
                          (:type-prescription general-booleanp)
                          (:type-prescription general-numberp)
                          (:type-prescription acl2::ubddp)
                          (:type-prescription general-concretep)
                          (:type-prescription bfr-=-uu)
                          ;; (:type-prescription assume-true-under-hyp2)
                          ;; (:type-prescription assume-false-under-hyp2)
                          ;(:type-prescription assume-true-under-hyp)
                          ;(:type-prescription assume-false-under-hyp)
                          (:meta mv-nth-cons-meta)
                          zp-open default-<-2 default-<-1
                          (:type-prescription zp)
                          (:type-prescription hyp-fix)
                          default-car default-cdr
                          general-concretep-def
                          ctrex-for-always-equal
                          hyp-fix
                          (:rules-of-class :type-prescription :here)
                          not)
                         ((:type-prescription general-number-components)))))
  (verify-guards g-always-equal-core))


(encapsulate nil

  (local (include-book "clause-processors/just-expand" :dir :system))
  (local
   (in-theory (e/d** (possibilities-for-x-1
                      possibilities-for-x-2
                      possibilities-for-x-3
                      possibilities-for-x-4
                      possibilities-for-x-5
                      possibilities-for-x-6
                      possibilities-for-x-7
                      possibilities-for-x-8
                      possibilities-for-x-9

                      g-if-geval-meta-correct-eval-g-base
                      g-or-geval-meta-correct-eval-g-base
                      eval-g-base-g-apply
                      eval-g-base-of-gl-cons
                      eval-g-base-non-cons
                      general-boolean-value-cases
                      bfr-eval-booleanp
                      mk-g-boolean-correct-for-eval-g-base
                      geval-g-if-marker-eval-g-base
                      geval-g-or-marker-eval-g-base
                      
                      general-concretep-not-general-consp
                      general-concretep-not-general-booleanp
                      general-concretep-not-general-numberp
                      general-concrete-obj-when-consp-for-eval-g-base
                      general-concrete-obj-when-numberp
                      general-concrete-obj-when-booleanp
                      general-concrete-obj-when-atom
                      general-concretep-atom
                      general-numberp-of-atom
                      general-booleanp-of-atom

                      (:type-prescription bfr-eval)
                      (:type-prescription components-to-number-fn)
                      (:rules-of-class :executable-counterpart :here)
                      booleanp-compound-recognizer

                      gtests-g-test-marker
                      
                      bfr-eval-bfr-binary-and
                      bfr-eval-bfr-not
                      bfr-eval-bfr-binary-or
                      gtests-nonnil-correct-for-eval-g-base
                      hyp-fix-correct 
                      always-equal-of-numbers-correct
                      always-equal-of-booleans-correct
                      
                      bfr-eval-g-hyp-marker
                      cons-equal

                      eval-g-base-apply-of-equal-kwote-lst
                      eval-g-base-list-of-gl-cons

                      general-concrete-obj-of-atomic-constants
                      general-concretep-of-atomic-constants
                      hons-equal acl2::always-equal
                      (:induction g-always-equal-core))
                     ((general-concrete-obj)
                      (general-concretep)
                      (kwote-lst)))))

  (defthm g-always-equal-core-correct
    (implies (and (not (bfr-mode))
                  (bfr-eval hyp (car env)))
             (equal (eval-g-base (g-always-equal-core x y hyp clk) env)
                    (acl2::always-equal (eval-g-base x env)
                                        (eval-g-base y env))))
    :hints ((acl2::just-induct-and-expand
             (g-always-equal-core x y hyp clk))
            (and stable-under-simplificationp
                 '(:expand ((g-always-equal-core x y hyp clk)
                            (g-always-equal-core x x hyp clk)
                            (g-always-equal-core x y hyp clk)
                            (g-always-equal-core x x hyp clk)
                            (eval-g-base x env)
                            (eval-g-base y env)
                            (eval-g-base nil env)
                            (eval-g-base t env)
                            (eval-g-base-list nil env))
                   :do-not-induct t)))))

(in-theory (disable g-always-equal-core))
