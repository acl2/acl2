

(in-package "GL")

(include-book "gtype-thms")
(include-book "general-objects")



(defthmd generic-geval-g-boolean
  (implies (and (g-boolean-p x)
                (gobjectp x))
           (equal (generic-geval x env)
                  (bfr-eval (g-boolean->bool x) (car env))))
  :hints(("Goal" :expand ((generic-geval x env))))
  :rule-classes ((:rewrite :backchain-limit-lst (0 nil))))



(defthm general-booleanp-booleanp
  (implies (and (gobjectp x)
                (general-booleanp x))
           (booleanp (generic-geval x env)))
  :hints(("Goal" :in-theory (enable generic-geval
                                    (:type-prescription bfr-eval)))))

(defthm general-booleanp-of-atomic-constant
  (implies (and (syntaxp (quotep x))
                (atom x))
           (equal (general-booleanp x)
                  (booleanp x))))




(defthm general-boolean-value-cases
  (and (implies (atom x)
                (equal (general-boolean-value x) x))
       (implies (and (consp x) (equal (tag x) :g-boolean))
                (equal (general-boolean-value x)
                       (g-boolean->bool x)))
       (implies (and (consp x) (equal (tag x) :g-concrete))
                (equal (general-boolean-value x)
                       (g-concrete->obj x))))
  :hints (("goal" :in-theory (enable g-concrete->obj g-boolean->bool
                                     general-boolean-value))))


(defthm bfr-p-general-boolean-value
  (implies (and (gobjectp x) (general-booleanp x))
           (bfr-p (general-boolean-value x)))
  :hints (("goal" :in-theory (enable gobjectp gobject-hierarchy
                                     bfr-p-of-boolean))))

(defthm general-boolean-value-correct
  (implies (and (general-booleanp x) (gobjectp x))
           (equal (generic-geval x env)
                  (bfr-eval (general-boolean-value x) (car env))))
  :hints (("goal" :in-theory (enable generic-geval)))
  :rule-classes ((:rewrite :backchain-limit-lst (0 nil))))


(in-theory (disable general-booleanp general-boolean-value))








(defthm general-numberp-eval-to-numberp
  (implies (and (general-numberp x) (gobjectp x))
           (acl2-numberp (generic-geval x env)))
  :hints (("goal" :expand (generic-geval x env))))


(defthm boolean-listp-n2v
  (boolean-listp (n2v n))
  :hints(("Goal" :in-theory (enable n2v))))

(defthm boolean-listp-i2v
  (boolean-listp (i2v n))
  :hints(("Goal" :in-theory (enable i2v))))

(defthm number-to-components-boolean-listps
  (and (boolean-listp (mv-nth 0 (number-to-components n)))
       (boolean-listp (mv-nth 1 (number-to-components n)))
       (boolean-listp (mv-nth 2 (number-to-components n)))
       (boolean-listp (mv-nth 3 (number-to-components n)))))



(defthm v2n-us
  (implies (natp n)
           (equal (v2n (n2v n)) n))
  :hints (("goal" :in-theory (disable floor))))

(defthm v2n-non-natp
  (implies (not (natp n))
           (equal (v2n (n2v n)) 0)))

(defthm acl2-numberp-v2n
  (and (acl2-numberp (v2n x))
       (rationalp (v2n x))
       (integerp (v2n x))
       (natp (v2n x)))
  :rule-classes (:rewrite :type-prescription))


(defthm number-to-components-components-to-number
  (b* (((mv rnum rden inum iden)
        (number-to-components n)))
    (implies (acl2-numberp n)
             (and (equal (components-to-number
                          (v2i rnum)
                          (v2n rden)
                          (v2i inum)
                          (v2n iden))
                         n)
                  (equal (components-to-number
                          (v2i (bfr-eval-list rnum env))
                          (v2n (bfr-eval-list rden env))
                          (v2i (bfr-eval-list inum env))
                          (v2n (bfr-eval-list iden env)))
                         n))))
  :hints (("goal" :in-theory (enable components-to-number-alt-def))))








(defthm general-number-components-bfr-listps
  (implies (and (gobjectp n) (general-numberp n))
           (and (bfr-listp (mv-nth 0 (general-number-components n)))
                (bfr-listp (mv-nth 1 (general-number-components n)))
                (bfr-listp (mv-nth 2 (general-number-components n)))
                (bfr-listp (mv-nth 3 (general-number-components n)))))
  :hints (("goal" :in-theory (e/d (wf-g-numberp-simpler-def gobjectp gobject-hierarchy)
                                  ((force))))))


(defthm general-number-components-ev
  (implies (and (gobjectp a)
                (general-numberp a))
           (mv-let (rn rd in id)
             (general-number-components a)
             (flet ((uval (n env)
                          (v2n (bfr-eval-list n (car env))))
                    (sval (n env)
                          (v2i (bfr-eval-list n (car env)))))
               (equal (generic-geval a env)
                      (components-to-number
                       (sval rn env)
                       (uval rd env)
                       (sval in env)
                       (uval id env))))))
  :hints (("goal" :in-theory (enable generic-geval
                                     components-to-number-alt-def))))

(in-theory (disable general-number-components
                    general-numberp))



(local (defthm nth-open-when-constant-idx
         (implies (syntaxp (quotep n))
                  (equal (nth n x)
                         (if (zp n) (car x)
                           (nth (1- n) (cdr x)))))))
                       


(defthm gobjectp-bfr-listp-break-g-number
  (implies (and (gobjectp x)
                (g-number-p x))
           (and (bfr-listp (mv-nth 0 (break-g-number (g-number->num x))))
                (bfr-listp (mv-nth 1 (break-g-number (g-number->num x))))
                (bfr-listp (mv-nth 2 (break-g-number (g-number->num x))))
                (bfr-listp (mv-nth 3 (break-g-number (g-number->num x))))))
  :hints (("goal" :in-theory (enable gobjectp wf-g-numberp gobject-hierarchy)
           :do-not-induct t)))

(in-theory (disable break-g-number))










(defthm consp-general-consp
  (implies (general-consp x)
           (consp (generic-geval x env)))
  :hints (("goal" :expand ((generic-geval x env)
                           (gobj-fix x)))))

(defthm general-consp-car-gobjectp
  (implies (and (gobjectp x) (general-consp x))
           (gobjectp (general-consp-car x))))

(defthm general-consp-car-correct
  (implies (and (gobjectp x) (general-consp x))
           (equal (generic-geval (general-consp-car x) env)
                  (car (generic-geval x env))))
  :hints (("goal" :in-theory (enable generic-geval))))

(defthm general-consp-car-acl2-count
  (implies (and (gobjectp x) (general-consp x))
           (< (acl2-count (general-consp-car x)) (acl2-count x)))
  :hints (("goal" :in-theory (enable mk-g-concrete g-concrete
                                     g-concrete->obj)))
  :rule-classes (:rewrite :linear))

(defthm general-consp-cdr-gobjectp
  (implies (and (gobjectp x) (general-consp x))
           (gobjectp (general-consp-cdr x))))

(defthm general-consp-cdr-correct
  (implies (and (gobjectp x) (general-consp x))
           (equal (generic-geval (general-consp-cdr x) env)
                  (cdr (generic-geval x env))))
  :hints (("goal" :in-theory (enable generic-geval))))

(defthm general-consp-cdr-acl2-count
  (implies (and (gobjectp x) (general-consp x))
           (< (acl2-count (general-consp-cdr x)) (acl2-count x)))
  :hints (("goal" :in-theory (enable mk-g-concrete g-concrete g-concrete->obj)))
  :rule-classes (:rewrite :linear))

(in-theory (disable general-consp general-consp-car general-consp-cdr))









(defthm general-concrete-atom-gobjectp
  (implies (general-concrete-atom x)
           (gobjectp x))
  :hints(("Goal" :in-theory (enable gobjectp g-concrete-p
                                    gobject-hierarchy tag))))

(defthm atom-general-concrete-atom
  (implies (general-concrete-atom x)
           (atom (generic-geval x env)))
  :hints (("goal" :in-theory (enable generic-geval))))


(defthm general-concrete-atom-val-gobjectp
  (implies (general-concrete-atom x)
           (gobjectp (general-concrete-atom-val x)))
  :hints (("goal" :in-theory (enable gobjectp))))



(defthm general-concrete-atom-val-correct
  (implies (and (gobjectp x) (general-concrete-atom x))
           (equal (generic-geval (general-concrete-atom-val x) env)
                  (generic-geval x env)))
  :hints (("goal" :in-theory (enable generic-geval))))

(in-theory (disable general-concrete-atom general-concrete-atom-val
                    general-concrete-atom-gobjectp))




(defun general-concretep-ind (x)
  (if (atom x)
      (not (g-keyword-symbolp x))
    (if (or (g-concrete-p x)
            (g-boolean-p x)
            (g-number-p x)
            (g-ite-p x)
            (g-apply-p x)
            (g-var-p x))
        t
      (list (general-concretep-ind (car x))
            (general-concretep-ind (cdr x))))))


(defthm general-concretep-def
  (equal (general-concretep x)
         (if (atom x)
             (not (g-keyword-symbolp x))
           (if (g-concrete-p x)
               t
             (and (not (g-boolean-p x))
                  (not (g-number-p x))
                  (not (g-ite-p x))
                  (not (g-apply-p x))
                  (not (g-var-p x))
                  (general-concretep (car x))
                  (general-concretep (cdr x))))))
  :hints (("goal" :induct (general-concretep-ind x)
           :in-theory
           (e/d** (gobjectp-boolean-case
                   gobjectp-number-case
                   gobjectp-apply-case
                   (:induction general-concretep-ind)))
           :expand ((gobject-hierarchy x)
                    (general-concretep x)
                    (general-concretep (car x))
                    (general-concretep (cdr x))))
          '(:use ((:instance gobject-hierarchy-possibilities)
                  (:instance gobject-hierarchy-possibilities
                             (x (car x)))
                  (:instance gobject-hierarchy-possibilities
                             (x (cdr x))))))
  :rule-classes :definition)


(defthmd general-concretep-gobjectp
  (implies (general-concretep x)
           (gobjectp x))
  :hints(("Goal" :in-theory (enable gobjectp general-concretep))))

(defthm general-concretep-of-atomic-constants
  (implies (and (syntaxp (quotep x))
                (atom x))
           (equal (general-concretep x)
                  (not (g-keyword-symbolp x))))
  :hints(("Goal" :in-theory (e/d () (general-concretep)))))

(in-theory (disable general-concretep (general-concretep)))

(defthmd general-concrete-gobject-car-and-cdr
  (implies (and (general-concretep x)
                (consp x)
                (not (g-concrete-p x)))
           (and (gobjectp (car x))
                (gobjectp (cdr x))))
  :hints(("Goal" :in-theory (e/d (g-concrete-p
                                  tag
                                  general-concretep-gobjectp)
                                 (general-concretep))
          :expand ((:with general-concretep-def (general-concretep x))
                   (:with gobjectp-def (gobjectp x))))))

(verify-guards general-concrete-obj-aig
 :hints (("goal" :in-theory (enable general-concrete-gobject-car-and-cdr))))

(verify-guards general-concrete-obj-bdd
 :hints (("goal" :in-theory (enable general-concrete-gobject-car-and-cdr))))

(verify-guards
 general-concrete-obj
 :hints
 (("goal" :in-theory (enable general-concrete-gobject-car-and-cdr))))


    

;; (defun general-concretep (x)
;;   (declare (xargs :guard (gobjectp x)))
;;   (or (concrete-gobjectp x)
;;       (g-concrete-p x)))

;; (defun general-concrete-obj (x)
;;   (declare (xargs :guard (and (gobjectp x)
;;                               (general-concretep x))))
;;   (if (g-concrete-p x)
;;       (g-concrete->obj x)
;;     x))



(defthmd general-concrete-obj-correct
  (implies (general-concretep x)
           (equal (generic-geval x env)
                  (general-concrete-obj x)))
  :hints(("Goal" :in-theory (enable general-concretep-gobjectp
                                    eval-concrete-gobjectp
                                    g-concrete-p)
          :induct (general-concrete-obj x)
          :expand ((general-concretep x)
                   (generic-geval x env)
                   (general-concrete-obj x)))))

(defthmd general-concrete-obj-correct-gobj-fix
  (implies (general-concretep (gobj-fix x))
           (equal (general-concrete-obj (gobj-fix x))
                  (generic-geval x env)))
  :hints(("Goal" :use ((:instance general-concrete-obj-correct
                                  (x (gobj-fix x))))
          :in-theory (disable general-concretep general-concrete-obj gobj-fix
                              general-concrete-obj-correct)))
  :rule-classes ((:rewrite :backchain-limit-lst 0)))

(defthm general-concrete-obj-of-atomic-constants
  (implies (and (syntaxp (quotep x))
                (atom x))
           (equal (general-concrete-obj x)
                  x)))

(in-theory (disable general-concretep general-concrete-obj
                    (general-concrete-obj)))



(defthm general-concretep-mk-g-concrete
  (general-concretep (mk-g-concrete x))
  :hints(("Goal" :in-theory (enable general-concretep-def
                                    mk-g-concrete))
         (and stable-under-simplificationp
              '(:in-theory (enable general-concretep
                                   concrete-gobjectp)))))

(defthm general-concrete-obj-mk-g-concrete
  (equal (general-concrete-obj (mk-g-concrete x))
         x)
  :hints(("Goal" :in-theory (enable general-concrete-obj
                                    concrete-gobjectp-def
                                    mk-g-concrete))))


(defthmd general-concretep-atom
  (implies (and (not (consp x)) (gobjectp x))
           (general-concretep x))
  :hints(("Goal" :in-theory (enable general-concretep-def gobjectp-def)))
  :rule-classes ((:rewrite :backchain-limit-lst (0 nil))))





(defthm bfr-p-bool-cond-itep-cond
  (implies (and (gobjectp x)
                (bool-cond-itep x))
           (bfr-p (bool-cond-itep-cond x))))


(defthm gobjectp-bool-cond-itep-truebr
  (implies (and (gobjectp x)
                (bool-cond-itep x))
           (gobjectp (bool-cond-itep-truebr x))))

(defthm gobjectp-bool-cond-itep-falsebr
  (implies (and (gobjectp x)
                (bool-cond-itep x))
           (gobjectp (bool-cond-itep-falsebr x))))

(defthm bool-cond-itep-eval
  (implies (and (bool-cond-itep x)
                (gobjectp x))
           (equal (generic-geval x env)
                  (if (bfr-eval (bool-cond-itep-cond x) (car env))
                      (generic-geval (bool-cond-itep-truebr x) env)
                    (generic-geval (bool-cond-itep-falsebr x) env))))
  :hints (("goal" :in-theory (enable generic-geval)))
  :rule-classes ((:rewrite :backchain-limit-lst (0 nil))))

(defthm acl2-count-bool-cond-itep-truebr
  (implies (and (gobjectp x) (bool-cond-itep x))
           (< (acl2-count (bool-cond-itep-truebr x))
              (acl2-count x)))
  :rule-classes :linear)

(defthm acl2-count-bool-cond-itep-falsebr
  (implies (and (gobjectp x) (bool-cond-itep x))
           (< (acl2-count (bool-cond-itep-falsebr x))
              (acl2-count x)))
  :rule-classes :linear)

(in-theory (disable bool-cond-itep bool-cond-itep-cond bool-cond-itep-truebr
                    bool-cond-itep-falsebr))









(local 
 (defthm g-concrete-p-impl-not-general-concretep-car
   (implies (g-concrete-p x)
            (not (general-concretep (car x))))
   :hints(("Goal" :in-theory (enable g-concrete-p tag)))))


(local (defthm general-concrete-obj-cons
         (implies (and (general-concretep (car x))
                       (general-concretep (cdr x))
                       (consp x))
                  (equal (general-concrete-obj x)
                         (cons (general-concrete-obj (car x))
                               (general-concrete-obj (cdr x)))))
         :hints(("Goal" :in-theory (enable general-concretep-def
                                           concrete-gobjectp-def
                                           general-concrete-obj)))
         :rule-classes ((:rewrite :backchain-limit-lst 0))))

(local (defthm general-boolean-value-alt
         (equal (general-boolean-value x)
                (cond ((atom x) x)
                      ((g-concrete-p x) (g-concrete->obj x))
                      (t (g-boolean->bool x))))
         :hints(("Goal" :in-theory (enable g-boolean->bool g-concrete->obj
                                           general-boolean-value)))
         :rule-classes :definition))

(defthm generic-geval-alt-def
  (implies (gobjectp x)
           (equal (generic-geval x env)
                  (cond
                   ((general-concretep x)
                    (general-concrete-obj x))
                   ((general-booleanp x)
                    (bfr-eval (general-boolean-value x) (car env)))
                   ((general-numberp x)
                    (b* (((mv rn rd in id)
                          (general-number-components x)))
                      (flet ((uval (n env)
                                   (v2n (bfr-eval-list n (car env))))
                             (sval (n env)
                                   (v2i (bfr-eval-list n (car env)))))
                        (components-to-number (sval rn env)
                                              (uval rd env)
                                              (sval in env)
                                              (uval id env)))))
                   ((general-consp x)
                    (cons (generic-geval (general-consp-car x) env)
                          (generic-geval (general-consp-cdr x) env)))
                   ((g-ite-p x)
                    (if (generic-geval (g-ite->test x) env)
                        (generic-geval (g-ite->then x) env)
                      (generic-geval (g-ite->else x) env)))
                   ((g-apply-p x)
                    (apply-stub (g-apply->fn x)
                                (generic-geval (g-apply->args x) env)))
                   (t
                    (cdr (hons-assoc-equal (g-var->name x) (cdr env)))))))
  :hints (("goal" ;; :induct (generic-geval x env)
           :in-theory (e/d** (general-concretep-def
                              (:induction generic-geval)
                              general-numberp general-booleanp
                              general-consp eq gobjectp-tag-rw-to-types
                              gobj-fix-when-gobjectp gobjectp-def
                              general-concrete-obj-cons
                              atom
                              acl2::cons-car-cdr
; not-g-keyword-symbolp-tag
                              g-keyword-symbolp-def member-equal
                              general-boolean-value-alt
                              general-number-components
                              booleanp-compound-recognizer
                              general-concrete-obj
                              general-consp-car
                              general-consp-cdr
                              general-concrete-obj-correct
                              ;; Jared: changed from hons-get-fn-do-hopy to hons-get for new hons code
                              hons-get))
           :do-not-induct t
           :expand ((generic-geval x env))))
  :rule-classes :definition)


(in-theory (disable generic-geval-alt-def))








(defthm possibilities-for-x
  (implies (gobjectp x)
           (and (implies (general-concretep x)
                         (and (not (g-ite-p x))
                              (not (g-apply-p x))
                              (not (g-var-p x))))
                (implies (not (consp x))
                         (and (general-concretep x)
                              (not (general-consp x))))
                (implies (general-booleanp x)
                         (and (not (general-numberp x))
                              (not (general-consp x))
                              (not (g-ite-p x))
                              (not (g-apply-p x))
                              (not (g-var-p x))))
                (implies (general-numberp x)
                         (and (not (general-booleanp x))
                              (not (general-consp x))
                              (not (g-ite-p x))
                              (not (g-apply-p x))
                              (not (g-var-p x))))
                (implies (general-consp x)
                         (and (not (general-booleanp x))
                              (not (general-numberp x))
                              (not (g-ite-p x))
                              (not (g-apply-p x))
                              (not (g-var-p x))))
                (implies (g-ite-p x)
                         (and (not (general-concretep x))
                              (not (general-consp x))
                              (not (general-booleanp x))
                              (not (general-numberp x))
                              (not (g-apply-p x))
                              (not (g-var-p x))))
                (implies (g-apply-p x)
                         (and (not (general-concretep x))
                              (not (general-consp x))
                              (not (general-booleanp x))
                              (not (general-numberp x))
                              (not (g-ite-p x))
                              (not (g-var-p x))))
                (implies (g-var-p x)
                         (and (not (general-concretep x))
                              (not (general-consp x))
                              (not (general-booleanp x))
                              (not (general-numberp x))
                              (not (g-ite-p x))
                              (not (g-apply-p x))))
                (implies (and (not (general-concretep x))
                              (not (general-consp x))
                              (not (general-booleanp x))
                              (not (general-numberp x))
                              (not (g-ite-p x))
                              (not (g-apply-p x)))
                         (g-var-p x))))
  :hints(("Goal" :in-theory (enable gobjectp-def general-concretep-def
                                    general-booleanp general-numberp
                                    general-consp g-keyword-symbolp-def
                                    member-equal
                                    gobjectp-tag-rw-to-types)
          :do-not-induct t))
  :rule-classes nil)


(defthm possibilities-for-x-1
  (implies (and (general-concretep x)
                (gobjectp x))
           (and (not (g-ite-p x))
                (not (g-apply-p x))
                (not (g-var-p x))))
  :hints (("Goal" :by possibilities-for-x))
  :rule-classes ((:rewrite :backchain-limit-lst 0)))


(defthm possibilities-for-x-2
  (implies (and (not (consp x))
                (gobjectp x))
           (and (general-concretep x)
                (not (general-consp x))))
  :hints (("Goal" :by possibilities-for-x))
  :rule-classes ((:rewrite :backchain-limit-lst 0)))

(defthm possibilities-for-x-3
  (implies (and (general-booleanp x)
                (gobjectp x))
           (and (not (general-numberp x))
                (not (general-consp x))
                (not (g-ite-p x))
                (not (g-apply-p x))
                (not (g-var-p x))))
  :hints (("Goal" :by possibilities-for-x))
  :rule-classes ((:rewrite :backchain-limit-lst 0)))

(defthm possibilities-for-x-4
  (implies (and (general-numberp x)
                (gobjectp x))
           (and (not (general-booleanp x))
                (not (general-consp x))
                (not (g-ite-p x))
                (not (g-apply-p x))
                (not (g-var-p x))))
  :hints (("Goal" :by possibilities-for-x))
  :rule-classes ((:rewrite :backchain-limit-lst 0)))

(defthm possibilities-for-x-5
  (implies (and (general-consp x)
                (gobjectp x))
           (and (not (general-booleanp x))
                (not (general-numberp x))
                (not (g-ite-p x))
                (not (g-apply-p x))
                (not (g-var-p x))))
  :hints (("Goal" :by possibilities-for-x))
  :rule-classes ((:rewrite :backchain-limit-lst 0)))

(defthm possibilities-for-x-6
  (implies (and (g-ite-p x)
                (gobjectp x))
           (and (not (general-concretep x))
                (not (general-consp x))
                (not (general-booleanp x))
                (not (general-numberp x))
                (not (g-apply-p x))
                (not (g-var-p x))))
  :hints (("Goal" :by possibilities-for-x))
  :rule-classes ((:rewrite :backchain-limit-lst 0)))

(defthm possibilities-for-x-7
  (implies (and (g-apply-p x)
                (gobjectp x))
           (and (not (general-concretep x))
                (not (general-consp x))
                (not (general-booleanp x))
                (not (general-numberp x))
                (not (g-ite-p x))
                (not (g-var-p x))))
  :hints (("Goal" :by possibilities-for-x))
  :rule-classes ((:rewrite :backchain-limit-lst 0)))

(defthm possibilities-for-x-8
  (implies (and (g-var-p x)
                (gobjectp x))
           (and (not (general-concretep x))
                (not (general-consp x))
                (not (general-booleanp x))
                (not (general-numberp x))
                (not (g-ite-p x))
                (not (g-apply-p x))))
  :hints (("Goal" :by possibilities-for-x))
  :rule-classes ((:rewrite :backchain-limit-lst 0)))

(defthm possibilities-for-x-9
  (implies (and (not (general-concretep x))
                (not (general-consp x))
                (not (general-booleanp x))
                (not (general-numberp x))
                (not (g-ite-p x))
                (not (g-apply-p x))
                (gobjectp x))
           (g-var-p x))
  :hints (("Goal" :by possibilities-for-x))
  :rule-classes ((:rewrite :backchain-limit-lst 0)))


(def-ruleset! general-object-possibilities
  '(possibilities-for-x-1
    possibilities-for-x-2
    possibilities-for-x-3
    possibilities-for-x-4
    possibilities-for-x-5
    possibilities-for-x-6
    possibilities-for-x-7
    possibilities-for-x-8
    possibilities-for-x-9))

(in-theory (disable* (:ruleset general-object-possibilities)))










(defthm general-concretep-not-general-numberp
  (implies (and (general-concretep x)
                (not (general-numberp x)))
           (not (acl2-numberp (general-concrete-obj x))))
  :hints(("Goal" :in-theory (enable general-concretep-def general-numberp
                                    gobjectp-tag-rw-to-types
                                    general-concretep-gobjectp
                                    general-concrete-obj)
          :expand ((general-concrete-obj x))
          :do-not-induct t))
  :rule-classes (:rewrite :type-prescription))

(defthm general-concretep-not-general-booleanp
  (implies (and (general-concretep x)
                (not (general-booleanp x)))
           (not (booleanp (general-concrete-obj x))))
  :hints(("Goal" :in-theory (enable general-concretep-def general-booleanp
                                    gobjectp-tag-rw-to-types
                                    general-concretep-gobjectp
                                    general-concrete-obj)
          :expand ((general-concrete-obj x))
          :do-not-induct t))
  :rule-classes :type-prescription)

(defthm general-concretep-not-general-consp
  (implies (and (general-concretep x)
                (not (general-consp x)))
           (not (consp (general-concrete-obj x))))
  :hints(("Goal" :in-theory (enable general-concretep-def general-consp
                                    gobjectp-tag-rw-to-types
                                    general-concretep-gobjectp
                                    concrete-gobjectp
                                    g-keyword-symbolp-def
                                    member-equal
                                    general-concrete-obj)
          :expand ((general-concrete-obj x))
          :do-not-induct t))
  :rule-classes :type-prescription)



(defthm general-concrete-obj-when-consp
  (implies (and (bind-free '((env . env)) (env))
                (gobjectp x)
                (general-consp x)
                (general-concretep x))
           (equal (general-concrete-obj x)
                  (cons (generic-geval (general-consp-car x) env)
                        (generic-geval (general-consp-cdr x) env))))
  :hints(("Goal" :in-theory (e/d (general-consp-car
                                  general-consp-cdr
                                  general-consp
                                  general-concretep-def
                                  generic-geval-alt-def
                                  eval-concrete-gobjectp
                                  general-concrete-obj
                                  concrete-gobjectp-def))
          :do-not-induct t))
  :rule-classes ((:rewrite :backchain-limit-lst 0)))

(defthm general-concrete-obj-when-numberp
  (implies (and (bind-free '((env . env)) (env))
                (general-concretep x)
                (general-numberp x)
                (gobjectp x))
           (mv-let (rn rd in id)
             (general-number-components x)
             (equal (general-concrete-obj x)
                    (components-to-number-fn
                     (v2i (bfr-eval-list rn (car env)))
                     (v2n (bfr-eval-list rd (car env)))
                     (v2i (bfr-eval-list in (car env)))
                     (v2n (bfr-eval-list id (car env)))))))
  :hints(("Goal" :in-theory (enable ;general-concretep-def
                             general-numberp
                             gobjectp-def
                             general-concrete-obj
                             general-number-components
                             break-g-number)
          :expand ((general-concretep x))
          :do-not-induct t))
  :rule-classes ((:rewrite :backchain-limit-lst 0)))

(defthm general-concrete-obj-when-booleanp
  (implies (and (bind-free '((env . env)) (env))
                (general-concretep x)
                (general-booleanp x)
                (gobjectp x))
           (equal (general-concrete-obj x)
                  (bfr-eval (general-boolean-value x) (car env))))
  :hints(("Goal" :in-theory (enable general-booleanp
                                    gobjectp-def
                                    general-concrete-obj
                                    general-boolean-value)
          :expand ((general-concretep x))
          :do-not-induct t))
  :rule-classes ((:rewrite :backchain-limit-lst 0)))


(defthmd not-general-numberp-not-acl2-numberp
  (implies (and (gobjectp x)
                (not (general-numberp x))
                (not (g-ite-p x))
                (not (g-apply-p x))
                (not (g-var-p x)))
           (not (acl2-numberp (generic-geval x env))))
  :hints (("goal" :use possibilities-for-x
           :expand ((generic-geval x env))
           :in-theory (disable general-consp-car-correct
                               general-consp-cdr-correct)
           :do-not-induct t)))
