
(in-package "GL")

(include-book "g-if")
(include-book "g-primitives-help")
(include-book "symbolic-arithmetic-fns")
(include-book "eval-g-base")
;(include-book "tools/with-arith5-help" :dir :system)
(local (include-book "symbolic-arithmetic"))
(local (include-book "eval-g-base-help"))
(local (include-book "hyp-fix-logic"))
;(local (allow-arith5-help))

(local (in-theory (disable acl2::revappend-removal)))




;; ;; This brings if-then-elses up from atoms to the top level of a cons tree.
;; (defun propagate-ites-above-conses (x )
;;   (declare (xargs :guard (gobjectp x)))
;;   (if (general-concretep x)
;;       x
;;     (pattern-match x
;;       ((g-ite test then else)
;;        (g-ite test (propagate-ites-above-conses then)
;;               (propagate-ites-above-conses else)))
;;       ((g-apply & &) x)
;;       ((g-var &) x)
;;       ((g-number &) x)
;;       ((g-boolean &) x)
;;       (& (if (general-concretep (car x))
;;              (cons (car x)
;;                    (propagate-ites-above-conses

(local (in-theory (disable member-eq)))

(defun revappend-concrete (a b)
  (declare (xargs :guard (true-listp a)))
  (if (endp a)
      b
    (revappend-concrete (cdr a)
                        (cons (mk-g-concrete (car a)) b))))

(local
 (progn
   (defthm gobjectp-revappend-concrete
     (implies (gobjectp b)
              (gobjectp (revappend-concrete a b))))

   (defthm revappend-concrete-correct
     (implies (gobjectp b)
              (equal (eval-g-base (revappend-concrete a b) env)
                     (revappend a (eval-g-base b env))))
     :hints(("Goal" :induct (revappend-concrete a b)
             :in-theory (enable revappend)
             :expand ((eval-g-base (cons (mk-g-concrete (car a)) b) env)))))))


;; Collect concrete characters onto "pre".
(defun coerce-string (x pre hyp)
  (declare (xargs :guard (and (gobjectp x)
                              (bfr-p hyp)
                              (true-listp pre))
                  :verify-guards nil))
  (if (or (general-concretep x) (atom x))
      (mk-g-concrete
       (ec-call (coerce (revappend pre (general-concrete-obj x)) 'string)))
    (pattern-match x
      ((g-ite test then else)
       (g-if test
             (coerce-string then pre hyp)
             (coerce-string else pre hyp)))
      ((g-apply & &) (g-apply 'coerce (list (revappend-concrete pre x) 'string)))
      ((g-var &) (g-apply 'coerce (list (revappend-concrete pre x) 'string)))
      ((g-number &)
       (mk-g-concrete
        (ec-call (coerce (revappend pre nil) 'string))))
      ((g-boolean &)
       (mk-g-concrete
        (ec-call (coerce (revappend pre nil) 'string))))
      ((g-concrete obj)
       ;; Actually taken care of by the first IF.
       (mk-g-concrete
        (ec-call (coerce (revappend pre obj) 'string))))
      (& (if (or (general-concretep (car x))
                 (atom (car x)))
             (coerce-string (cdr x) (cons (general-concrete-obj (car x)) pre)
                            hyp)
           (pattern-match (car x)
             ((g-ite test then else)
              (g-if test
                    (coerce-string (cons then (cdr x)) pre hyp)
                    (coerce-string (cons else (cdr x)) pre hyp)))
             ((g-apply & &) (g-apply 'coerce (list (revappend-concrete pre x)
                                                   'string)))
             ((g-var &) (g-apply 'coerce (list (revappend-concrete pre x)
                                               'string)))
             (&
              (coerce-string (cdr x) (cons (code-char 0) pre) hyp))))))))


(local
 (progn
   (defthm gobjectp-coerce-string
     (implies (and (gobjectp x)
                   (bfr-p hyp))
              (gobjectp (coerce-string x pre hyp)))
     :hints(("Goal" :in-theory (e/d () ((:definition coerce-string)))
             :induct (coerce-string x pre hyp)
             :expand ((coerce-string x pre hyp)))))

   (defthmd atom-impl-general-concretep-1
     (implies (and (gobjectp x)
                   (not (consp x)))
              (general-concretep x))
     :hints(("Goal" :in-theory (enable general-concretep-def gobjectp-def)))
     :rule-classes ((:rewrite :backchain-limit-lst 1)))

   (defthm gobjectp-car-cdr-when-cons
     (implies (and (gobjectp x)
                   (consp x)
                   (not (g-ite-p x))
                   (not (g-apply-p x))
                   (not (g-var-p x))
                   (not (g-number-p x))
                   (not (g-boolean-p x))
                   (not (g-concrete-p x)))
              (and (gobjectp (car x))
                   (gobjectp (cdr x)))))))

(verify-guards
 coerce-string
 :hints(("Goal" :in-theory (e/d (atom-impl-general-concretep-1)
                                (coerce-string
                                 gobjectp-cons-case
                                 )))))


(local
 (encapsulate
   nil

   (local
    (progn
      (defthm coerce-non-character-list
        (implies (syntaxp (not (equal (acl2::mfc-rw `(character-listp ,x) t t mfc state) acl2::*t*)))
                 (equal (coerce x 'string)
                        (coerce (make-character-list x) 'string)))
        :hints (("goal" :use (:instance completion-of-coerce
                                        (y 'string)))))

      (defthm make-character-list-character-list
        (character-listp (make-character-list x)))

      (defthm make-character-list-revappend
        (equal (make-character-list (revappend a b))
               (revappend (make-character-list a) (make-character-list b))))

      (defthm revappend-non-character-list-not-character-list
        (implies (not (character-listp x))
                 (not (character-listp (revappend y x)))))

      (defthm revappend-character-lists
        (implies (and (character-listp x)
                      (character-listp y))
                 (character-listp (revappend y x))))))

   (defthm coerce-revappend-atom
     (implies (and (syntaxp (not (equal x ''nil)))
                   (atom x))
              (equal (coerce (revappend y x) 'string)
                     (coerce (revappend y nil) 'string))))))

(local (defthm eval-g-base-general-concrete-obj
         (implies (general-concretep x)
                  (equal (eval-g-base x env)
                         (general-concrete-obj x)))
         :hints (("goal" :expand ((eval-g-base x env))
                  :use ((:theorem (implies (general-concretep x)
                                           (gobjectp x)))))
                 (and stable-under-simplificationp
                      '(:in-theory (enable general-concretep
                                           gobjectp))))
         :rule-classes ((:rewrite :backchain-limit-lst 0))))

(local
 (encapsulate nil

   (local
    (progn
      (defthmd coerce-non-character-list
        (implies (syntaxp (not (equal (acl2::mfc-rw `(character-listp ,x) t t mfc state) acl2::*t*)))
                 (equal (coerce x 'string)
                        (coerce (make-character-list x) 'string)))
        :hints (("goal" :use (:instance completion-of-coerce
                                        (y 'string)))))

      (defthm make-character-list-character-list
        (character-listp (make-character-list x)))

      (defthm make-character-list-revappend
        (equal (make-character-list (revappend a b))
               (revappend (make-character-list a) (make-character-list b))))

      (defthm revappend-non-character-list-not-character-list
        (implies (not (character-listp x))
                 (not (character-listp (revappend y x)))))

      (defthm revappend-character-lists
        (implies (and (character-listp x)
                      (character-listp y))
                 (character-listp (revappend y x))))))

   (local (defthm coerce-revappend-atom
            (implies (and (syntaxp (not (equal x ''nil)))
                          (atom x))
                     (equal (coerce (revappend y x) 'string)
                            (coerce (revappend y nil) 'string)))
            :hints(("Goal" :in-theory (enable coerce-non-character-list)))))


   (local (defthm coerce-string-non-consp
            (implies (not (consp x))
                     (equal (coerce x 'string)
                            ""))))

   (local (defthm consp-eval-g-base-boolean
            (implies (and (gobjectp x)
                          (g-boolean-p x))
                     (not (consp (eval-g-base x env))))
            :hints(("Goal" :in-theory (enable eval-g-base)))))

   (local (defthm consp-eval-g-base-number
            (implies (and (gobjectp x)
                          (g-number-p x))
                     (not (consp (eval-g-base x env))))
            :hints(("Goal" :in-theory (enable eval-g-base)))))

   (local (defthm general-concrete-obj-atom
            (implies (atom x)
                     (equal (general-concrete-obj x) x))
            :hints(("Goal" :in-theory (enable general-concrete-obj)))))

;;    (local (defthm eval-g-base-not-character-p
;;             (implies (and (gobjectp x)
;;                           (not (general-concretep x))
;;                           (not (g-ite-p x))
;;                           (not (g-apply-p x))
;;                           (not (g-var-p x)))
;;                      (not (characterp (eval-g-base x env))))
;;             :hints(("Goal" :in-theory (enable (:induction eval-g-base)
;;                                               general-concretep-def)
;;                     :induct (eval-g-base x env)
;;                     :expand ((:with eval-g-base (eval-g-base x env)))))))


   (local (defthm eval-g-base-atom
            (implies (and (not (consp x)) (gobjectp x))
                     (equal (eval-g-base x env) x))
            :hints(("Goal" :in-theory (enable eval-g-base)))
            :rule-classes ((:rewrite :backchain-limit-lst (0 nil)))))



   (defthm coerce-string-correct
     (implies (and (bfr-eval hyp (car env))
                   (bfr-p hyp)
                   (gobjectp x))
              (equal (eval-g-base (coerce-string x pre hyp) env)
                     (coerce (revappend pre (eval-g-base x env)) 'string)))
     :hints(("Goal" :in-theory (e/d* ( general-concrete-obj
                                       concrete-gobjectp-def
                                       general-concretep-def)
                                     ((:definition coerce-string)
                                      member eval-g-base
                                      equal-of-booleans-rewrite
                                      bfr-eval-booleanp
                                      bool-cond-itep-eval
                                      default-car
                                      eval-g-base-alt-def
                                      general-number-components-ev
                                      ))
             :induct (coerce-string x pre hyp)
             :expand ((coerce-string x pre hyp)
                      (:with eval-g-base (eval-g-base x env))))
            (and stable-under-simplificationp
                 '(:in-theory
                   (e/d (coerce-non-character-list
                         general-concrete-obj
                         concrete-gobjectp-def
                         general-concretep-def)
                        ((:definition coerce-string)
                         member eval-g-base
                         equal-of-booleans-rewrite
                         bfr-eval-booleanp
                         bool-cond-itep-eval
                         default-car
                         eval-g-base-alt-def
                         general-number-components-ev
                         ))
                   :expand ((:with eval-g-base (eval-g-base (car x) env)))))))))

(defun coerce-list (x hyp)
  (declare (xargs :guard (and (gobjectp x)
                              (bfr-p hyp))
                  :verify-guards nil))
  (if (or (general-concretep x) (atom x))
      (mk-g-concrete
       (ec-call (coerce (general-concrete-obj x) 'list)))
    (pattern-match x
      ((g-ite test then else)
       (g-if test
             (coerce-list then hyp)
             (coerce-list else hyp)))
      ((g-apply & &) (g-apply 'coerce (list x 'list)))
      ((g-var &) (g-apply 'coerce (list x 'list)))
      (& nil))))


(local
 (defthm gobjectp-coerce-list
   (implies (and (gobjectp x)
                 (bfr-p hyp))
            (gobjectp (coerce-list x hyp)))
   :hints (("goal" :in-theory (e/d () ((:definition coerce-list)))
            :induct (coerce-list x hyp)
            :expand ((coerce-list x hyp))))))

(verify-guards
 coerce-list
 :hints(("Goal" :in-theory (e/d (atom-impl-general-concretep-1)
                                (coerce-list)))))


(encapsulate nil
  (local (in-theory (disable member-equal)))

  (local (defthm stringp-eval-g-base
           (implies (and (gobjectp x)
                         (not (general-concretep x))
                         (not (g-ite-p x))
                         (not (g-apply-p x))
                         (not (g-var-p x)))
                    (not (stringp (eval-g-base x env))))
           :hints(("Goal" :in-theory (e/d ((:induction eval-g-base)
                                           general-concretep-def)
                                          (gobjectp-cons-case))
                   :induct (eval-g-base x env)
                   :expand ((:with eval-g-base (eval-g-base x env)))))))



  (defthm coerce-list-correct
    (implies (and (bfr-eval hyp (car env))
                  (bfr-p hyp)
                  (gobjectp x))
             (equal (eval-g-base (coerce-list x hyp) env)
                    (coerce (eval-g-base x env) 'list)))
    :hints(("Goal" :in-theory (e/d* (; (:ruleset g-correct-lemmas)
                                     eval-g-base-general-concrete-obj
                                     eval-g-base)
                                    ((:definition coerce-list)
                                     eval-g-base-alt-def))
            :induct (coerce-list x hyp)
            :expand ((coerce-list x hyp)))
           (and stable-under-simplificationp
                '(:in-theory (enable general-concrete-obj))))))

(in-theory (disable coerce-list coerce-string))

(def-g-fn coerce
  `(if (general-concretep y)
       (if (eq (general-concrete-obj y) 'list)
           (coerce-list x hyp)
         (coerce-string x nil hyp))
     (pattern-match y
       ((g-ite ytest ythen yelse)
        (if (zp clk)
            (g-apply 'coerce (list x y))
          (g-if ytest
                (,gfn x ythen hyp clk)
                (,gfn x yelse hyp clk))))
       ((g-apply & &)
        (g-apply 'coerce (list x y)))
       ((g-var &)
        (g-apply 'coerce (list x y)))
       (& (coerce-string x nil hyp)))))


(def-gobjectp-thm coerce
  :hints `(("Goal" :in-theory (disable gobj-fix-when-not-gobjectp
                                       hyp-fix-of-hyp-fixedp
                                       (:definition ,gfn))
            :induct (,gfn x y hyp clk)
            :expand ((,gfn x y hyp clk)))))

(verify-g-guards
 coerce
 :hints `(("Goal" :in-theory (disable ,gfn))))

(local
 (defthm eval-g-base-not-equal-list
   (implies (and (gobjectp y)
                 (not (general-concretep y))
                 (not (g-ite-p y))
                 (not (g-apply-p y))
                 (not (g-var-p y)))
            (not (equal (eval-g-base y env) 'list)))
   :hints(("Goal" :in-theory (e/d ((:induction eval-g-base)
                                   general-concretep-def)
                                  (gobjectp-cons-case
                                   eval-g-base-alt-def))
           :induct (eval-g-base y env)
           :expand ((:with eval-g-base (eval-g-base y env)))))))



(def-g-correct-thm coerce eval-g-base
  :hints `(("Goal" :in-theory (e/d* (atom-impl-general-concretep-1
                                     eval-g-base)
                                    ((:definition ,gfn)
                                     eval-concrete-gobjectp
                                     ; eval-g-base-non-gobjectp

                                     ; eval-g-base-g-concrete
                                     bfr-eval-booleanp
                                     bool-cond-itep-eval
                                     general-boolean-value-correct
                                     ; eval-g-non-keyword-cons
                                     equal-of-booleans-rewrite
                                     ; g-eval-non-consp
                                     general-number-components-ev
                                     gobj-fix-when-not-gobjectp
                                     hyp-fix-of-hyp-fixedp
                                     ; hyp-and-not-false-test-is-and
                                     default-car default-cdr
                                     (:rules-of-class :type-prescription :here)
                                     ; non-consp-eval-correct
                                     ; eval-g-base-g-apply-p
                                     eval-g-base-alt-def
                                     eval-g-base-not-equal-list))
            :induct (,gfn x y hyp clk)
            :expand ((,gfn x y hyp clk)))
           (and stable-under-simplificationp
                '(:in-theory (enable general-concrete-obj-correct
                                     eval-g-base-not-equal-list)))))

