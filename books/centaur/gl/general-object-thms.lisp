; GL - A Symbolic Simulation Framework for ACL2
; Copyright (C) 2008-2013 Centaur Technology
;
; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/
;
; License: (An MIT/X11-style license)
;
;   Permission is hereby granted, free of charge, to any person obtaining a
;   copy of this software and associated documentation files (the "Software"),
;   to deal in the Software without restriction, including without limitation
;   the rights to use, copy, modify, merge, publish, distribute, sublicense,
;   and/or sell copies of the Software, and to permit persons to whom the
;   Software is furnished to do so, subject to the following conditions:
;
;   The above copyright notice and this permission notice shall be included in
;   all copies or substantial portions of the Software.
;
;   THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
;   IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
;   FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
;   AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
;   LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
;   FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
;   DEALINGS IN THE SOFTWARE.
;
; Original author: Sol Swords <sswords@centtech.com>

(in-package "GL")
(include-book "gtype-thms")
(include-book "general-objects")


(defthmd generic-geval-g-boolean
  (implies (g-boolean-p x)
           (equal (generic-geval x env)
                  (bfr-eval (g-boolean->bool x) (car env))))
  :hints(("Goal" :expand ((generic-geval x env))))
  :rule-classes ((:rewrite :backchain-limit-lst 0)))



(defthm general-booleanp-booleanp
  (implies (general-booleanp x)
           (booleanp (generic-geval x env)))
  :hints(("Goal" :in-theory (enable generic-geval
                                    (:type-prescription bfr-eval)))))

(defthm general-booleanp-of-atom
  (implies (not (consp x))
           (equal (general-booleanp x)
                  (booleanp x)))
  :rule-classes ((:rewrite :backchain-limit-lst 0)))


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


(defthm general-boolean-value-correct
  (implies (general-booleanp x)
           (equal (generic-geval x env)
                  (bfr-eval (general-boolean-value x) (car env))))
  :hints (("goal" :in-theory (enable generic-geval)))
  :rule-classes ((:rewrite :backchain-limit-lst 0)))

(defthm pbfr-depends-on-of-general-boolean-value
  (implies (and (not (gobj-depends-on k p x))
                (general-booleanp x))
           (not (pbfr-depends-on k p (general-boolean-value x))))
  :hints(("Goal" :in-theory (enable general-booleanp general-boolean-value
                                    booleanp))))


(in-theory (disable general-booleanp general-boolean-value))








(defthm general-numberp-eval-to-numberp
  (implies (general-numberp x)
           (acl2-numberp (generic-geval x env)))
  :hints (("goal" :expand (generic-geval x env))))


(defthm boolean-listp-n2v
  (boolean-listp (n2v n))
  :hints(("Goal" :in-theory (e/d (n2v bfr-ucons) (logcar logcdr)))))

(defthm boolean-listp-i2v
  (boolean-listp (i2v n))
  :hints(("Goal" :in-theory (e/d (i2v bfr-scons) (logcar logcdr)))))

(defthm number-to-components-boolean-listps
  (and (boolean-listp (mv-nth 0 (number-to-components n)))
       (boolean-listp (mv-nth 1 (number-to-components n)))
       (boolean-listp (mv-nth 2 (number-to-components n)))
       (boolean-listp (mv-nth 3 (number-to-components n)))))



;; (defthm v2n-us
;;   (implies (natp n)
;;            (equal (v2n (n2v n)) n))
;;   :hints (("goal" :in-theory (disable floor))))

;; (defthm v2n-non-natp
;;   (implies (not (natp n))
;;            (equal (v2n (n2v n)) 0)))

;; (defthm acl2-numberp-v2n
;;   (and (acl2-numberp (v2n x))
;;        (rationalp (v2n x))
;;        (integerp (v2n x))
;;        (natp (v2n x)))
;;   :rule-classes (:rewrite :type-prescription))


(defthm number-to-components-components-to-number
  (b* (((mv rnum rden inum iden)
        (number-to-components n)))
    (implies (acl2-numberp n)
             (equal (components-to-number
                     (bfr-list->s rnum env)
                     (bfr-list->u rden env)
                     (bfr-list->s inum env)
                     (bfr-list->u iden env))
                    n)))
  :hints (("goal" :in-theory (enable components-to-number-alt-def))))








;; (defthm general-number-components-bfr-listps
;;   (implies (and (gobjectp n) (general-numberp n))
;;            (and (bfr-listp (mv-nth 0 (general-number-components n)))
;;                 (bfr-listp (mv-nth 1 (general-number-components n)))
;;                 (bfr-listp (mv-nth 2 (general-number-components n)))
;;                 (bfr-listp (mv-nth 3 (general-number-components n)))))
;;   :hints (("goal" :in-theory (e/d (wf-g-numberp-simpler-def gobjectp gobject-hierarchy)
;;                                   ((force))))))


(defthm general-number-components-ev
  (implies (general-numberp a)
           (mv-let (rn rd in id)
             (general-number-components a)
             (flet ((uval (n env)
                          (bfr-list->u n (car env)))
                    (sval (n env)
                          (bfr-list->s n (car env))))
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

(defthm pbfr-depends-on-of-general-number-components
  (implies (and (general-numberp x)
                (not (gobj-depends-on k p x)))
           (b* (((mv rn rd in id) (general-number-components x)))
             (and (not (pbfr-list-depends-on k p rn))
                  (not (pbfr-list-depends-on k p rd))
                  (not (pbfr-list-depends-on k p in))
                  (not (pbfr-list-depends-on k p id)))))
  :hints(("Goal" :in-theory (enable general-number-components)
          :expand ((gobj-depends-on k p x)
                   (general-numberp x)))))



(local (defthm nth-open-when-constant-idx
         (implies (syntaxp (quotep n))
                  (equal (nth n x)
                         (if (zp n) (car x)
                           (nth (1- n) (cdr x)))))))


(defthm general-numberp-of-atom
  (implies (not (consp x))
           (equal (general-numberp x)
                  (acl2-numberp x)))
  :hints(("Goal" :in-theory (enable general-numberp)))
  :rule-classes ((:rewrite :backchain-limit-lst 0)))


;; (defthm gobjectp-bfr-listp-break-g-number
;;   (implies (g-number-p x)
;;            (and (bfr-listp (mv-nth 0 (break-g-number (g-number->num x))))
;;                 (bfr-listp (mv-nth 1 (break-g-number (g-number->num x))))
;;                 (bfr-listp (mv-nth 2 (break-g-number (g-number->num x))))
;;                 (bfr-listp (mv-nth 3 (break-g-number (g-number->num x))))))
;;   :hints (("goal" :do-not-induct t)))

(in-theory (disable break-g-number))










(defthm consp-general-consp
  (implies (general-consp x)
           (consp (generic-geval x env)))
  :hints (("goal" :expand ((generic-geval x env)))))

;; (defthm general-consp-car-gobjectp
;;   (implies (general-consp x)
;;            (gobjectp (general-consp-car x))))

(defthm general-consp-car-correct
  (implies (general-consp x)
           (equal (generic-geval (general-consp-car x) env)
                  (car (generic-geval x env))))
  :hints (("goal" :in-theory (enable generic-geval))))

(defthm general-consp-car-acl2-count
  (implies (general-consp x)
           (< (acl2-count (general-consp-car x)) (acl2-count x)))
  :hints (("goal" :in-theory (enable mk-g-concrete g-concrete
                                     g-concrete->obj)))
  :rule-classes (:rewrite :linear))

;; (defthm general-consp-cdr-gobjectp
;;   (implies ( (gobjectp x) (general-consp x))
;;            (gobjectp (general-consp-cdr x))))

(defthm general-consp-cdr-correct
  (implies (general-consp x)
           (equal (generic-geval (general-consp-cdr x) env)
                  (cdr (generic-geval x env))))
  :hints (("goal" :in-theory (enable generic-geval))))

(defthm general-consp-cdr-acl2-count
  (implies (general-consp x)
           (< (acl2-count (general-consp-cdr x)) (acl2-count x)))
  :hints (("goal" :in-theory (enable mk-g-concrete g-concrete g-concrete->obj)))
  :rule-classes (:rewrite :linear))

(defthm gobj-depends-on-of-general-consp
  (implies (and (not (gobj-depends-on k p x))
                (general-consp x))
           (and (not (gobj-depends-on k p (general-consp-car x)))
                (not (gobj-depends-on k p (general-consp-cdr x)))))
  :hints(("Goal" :in-theory (enable general-consp
                                    general-consp-car
                                    general-consp-cdr
                                    g-keyword-symbolp-def))))


(in-theory (disable general-consp general-consp-car general-consp-cdr))









;; (defthm general-concrete-atom-gobjectp
;;   (implies (general-concrete-atom x)
;;            (gobjectp x))
;;   :hints(("Goal" :in-theory (enable gobjectp g-concrete-p
;;                                     gobject-hierarchy tag))))

(defthm atom-general-concrete-atom
  (implies (general-concrete-atom x)
           (atom (generic-geval x env)))
  :hints (("goal" :in-theory (enable generic-geval))))


;; (defthm general-concrete-atom-val-gobjectp
;;   (implies (general-concrete-atom x)
;;            (gobjectp (general-concrete-atom-val x)))
;;   :hints (("goal" :in-theory (enable gobjectp))))



(defthm general-concrete-atom-val-correct
  (implies (general-concrete-atom x)
           (equal (generic-geval (general-concrete-atom-val x) env)
                  (generic-geval x env)))
  :hints (("goal" :in-theory (enable generic-geval))))

(in-theory (disable general-concrete-atom general-concrete-atom-val))




(defun general-concretep-ind (x)
  (if (atom x)
      x
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
             t
           (if (g-concrete-p x)
               t
             (and (not (g-boolean-p x))
                  (not (g-number-p x))
                  (not (g-ite-p x))
                  (not (g-apply-p x))
                  (not (g-var-p x))
                  (general-concretep (car x))
                  (general-concretep (cdr x))))))
  :hints(("Goal" :in-theory (enable gobject-hierarchy-lite)))
  :rule-classes :definition)


;; (defthmd general-concretep-gobjectp
;;   (implies (general-concretep x)
;;            (gobjectp x))
;;   :hints(("Goal" :in-theory (enable gobjectp general-concretep))))

(defthm general-concretep-of-atomic-constants
  (implies (and (syntaxp (quotep x))
                (atom x))
           (equal (general-concretep x) t))
  :hints(("Goal" :in-theory (e/d () (general-concretep)))))

(in-theory (disable general-concretep (general-concretep)))

;; (defthmd general-concrete-gobject-car-and-cdr
;;   (implies (and (general-concretep x)
;;                 (consp x)
;;                 (not (g-concrete-p x)))
;;            (and (gobjectp (car x))
;;                 (gobjectp (cdr x))))
;;   :hints(("Goal" :in-theory (e/d (g-concrete-p
;;                                   tag
;;                                   general-concretep-gobjectp)
;;                                  (general-concretep))
;;           :expand ((:with general-concretep-def (general-concretep x))
;;                    (:with gobjectp-def (gobjectp x))))))


;; (verify-guards general-concrete-obj-aig
;;   :hints (("goal" :in-theory (e/d (general-concrete-gobject-car-and-cdr
;;                                    gobject-hierarchy-lite->aig)
;;                                   (gobject-hierarchy-lite-redef)))))


;; (verify-guards general-concrete-obj-bdd
;;   :hints (("goal" :in-theory (e/d (general-concrete-gobject-car-and-cdr
;;                                    gobject-hierarchy-lite->bdd)
;;                                   (gobject-hierarchy-lite-redef)))))

(verify-guards
 general-concrete-obj)


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



(defthm generic-geval-when-concrete-gobjectp
  (implies (concrete-gobjectp x)
           (equal (generic-geval x env)
                  x))
  :hints(("Goal" :in-theory (enable concrete-gobjectp
                                    gobject-hierarchy-lite
                                    generic-geval)))
  :rule-classes ((:rewrite :backchain-limit-lst 0)))

(defthmd general-concrete-obj-correct
  (implies (general-concretep x)
           (equal (generic-geval x env)
                  (general-concrete-obj x)))
  :hints(("Goal"
          :induct (general-concrete-obj x)

          :expand ((general-concretep x)
                   (generic-geval x env)
                   (concrete-gobjectp x)
                   (general-concrete-obj x)))))

;; (defthmd general-concrete-obj-correct-gobj-fix
;;   (implies (general-concretep (gobj-fix x))
;;            (equal (general-concrete-obj (gobj-fix x))
;;                   (generic-geval x env)))
;;   :hints(("Goal" :use ((:instance general-concrete-obj-correct
;;                                   (x (gobj-fix x))))
;;           :in-theory (disable general-concretep general-concrete-obj gobj-fix
;;                               general-concrete-obj-correct)))
;;   :rule-classes ((:rewrite :backchain-limit-lst 0)))

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
  (implies (not (consp x))
           (general-concretep x))
  :hints(("Goal" :in-theory (enable general-concretep-def)))
  :rule-classes ((:rewrite :backchain-limit-lst 0)))





;; (defthm bfr-p-bool-cond-itep-cond
;;   (implies (bool-cond-itep x)
;;            (bfr-p (bool-cond-itep-cond x))))


;; (defthm gobjectp-bool-cond-itep-truebr
;;   (implies (and (gobjectp x)
;;                 (bool-cond-itep x))
;;            (gobjectp (bool-cond-itep-truebr x))))

;; (defthm gobjectp-bool-cond-itep-falsebr
;;   (implies (and (gobjectp x)
;;                 (bool-cond-itep x))
;;            (gobjectp (bool-cond-itep-falsebr x))))

(defthm bool-cond-itep-eval
  (implies (bool-cond-itep x)
           (equal (generic-geval x env)
                  (if (bfr-eval (bool-cond-itep-cond x) (car env))
                      (generic-geval (bool-cond-itep-truebr x) env)
                    (generic-geval (bool-cond-itep-falsebr x) env))))
  :hints (("goal" :in-theory (enable generic-geval)))
  :rule-classes ((:rewrite :backchain-limit-lst 0)))

(defthm acl2-count-bool-cond-itep-truebr
  (implies (bool-cond-itep x)
           (< (acl2-count (bool-cond-itep-truebr x))
              (acl2-count x)))
  :rule-classes :linear)

(defthm acl2-count-bool-cond-itep-falsebr
  (implies (bool-cond-itep x)
           (< (acl2-count (bool-cond-itep-falsebr x))
              (acl2-count x)))
  :rule-classes :linear)

(in-theory (disable bool-cond-itep bool-cond-itep-cond bool-cond-itep-truebr
                    bool-cond-itep-falsebr))









;; (local
;;  (defthm g-concrete-p-impl-not-general-concretep-car
;;    (implies (g-concrete-p x)
;;             (not (general-concretep (car x))))
;;    :hints(("Goal" :in-theory (enable g-concrete-p tag)))))


;; (defthmd general-concrete-obj-cons
;;   (implies (and (general-concretep (car x))
;;                 (general-concretep (cdr x))
;;                 (consp x))
;;            (equal (general-concrete-obj x)
;;                   (cons (general-concrete-obj (car x))
;;                         (general-concrete-obj (cdr x)))))
;;   :hints(("Goal" :in-theory (enable general-concretep-def
;;                                     concrete-gobjectp-def
;;                                     general-concrete-obj)))
;;   :rule-classes ((:rewrite :backchain-limit-lst 0)))

(defthmd general-boolean-value-alt
  (equal (general-boolean-value x)
         (cond ((atom x) x)
               ((g-concrete-p x) (g-concrete->obj x))
               (t (g-boolean->bool x))))
  :hints(("Goal" :in-theory (enable g-boolean->bool g-concrete->obj
                                    general-boolean-value)))
  :rule-classes :definition)

(defthm generic-geval-alt-def
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
                          (bfr-list->u n (car env)))
                    (sval (n env)
                          (bfr-list->s n (car env))))
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
           (and (not (eq (g-apply->fn x) 'quote))
                (generic-geval-ev
                 (cons (g-apply->fn x)
                       (kwote-lst
                        (generic-geval-list (g-apply->args x) env)))
                 nil)))
          (t
           (cdr (hons-assoc-equal (g-var->name x) (cdr env))))))
  :hints (("goal" ;; :induct (generic-geval x env)
           :in-theory (e/d** (general-concretep-def
                              (:induction generic-geval)
                              general-numberp general-booleanp
                              general-consp eq
                              atom
                              acl2::cons-car-cdr
                              concrete-gobjectp-def
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
  :rule-classes
  ((:definition :clique (generic-geval generic-geval-list)
    :controller-alist ((generic-geval t nil)
                       (generic-geval-list t nil)))))


(in-theory (disable generic-geval-alt-def))








(defthm possibilities-for-x
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
                (g-var-p x)))
  :hints(("Goal" :in-theory (enable general-concretep-def
                                    general-booleanp general-numberp
                                    general-consp g-keyword-symbolp-def
                                    member-equal)
          :do-not-induct t))
  :rule-classes nil)


(defthm possibilities-for-x-1
  (implies (general-concretep x)
           (and (not (g-ite-p x))
                (not (g-apply-p x))
                (not (g-var-p x))))
  :hints (("Goal" :by possibilities-for-x))
  :rule-classes :forward-chaining)


(defthm possibilities-for-x-2
  (implies (not (consp x))
           (and (general-concretep x)
                (not (general-consp x))))
  :hints (("Goal" :by possibilities-for-x))
  :rule-classes ((:rewrite :backchain-limit-lst 0)))

(defthm possibilities-for-x-3
  (implies (general-booleanp x)
           (and (not (general-numberp x))
                (not (general-consp x))
                (not (g-ite-p x))
                (not (g-apply-p x))
                (not (g-var-p x))))
  :hints (("Goal" :by possibilities-for-x))
  :rule-classes :forward-chaining)

(defthm possibilities-for-x-4
  (implies (general-numberp x)
           (and (not (general-booleanp x))
                (not (general-consp x))
                (not (g-ite-p x))
                (not (g-apply-p x))
                (not (g-var-p x))))
  :hints (("Goal" :by possibilities-for-x))
  :rule-classes :forward-chaining)

(defthm possibilities-for-x-5
  (implies (general-consp x)
           (and (not (general-booleanp x))
                (not (general-numberp x))
                (not (g-ite-p x))
                (not (g-apply-p x))
                (not (g-var-p x))))
  :hints (("Goal" :by possibilities-for-x))
  :rule-classes :forward-chaining)

(defthm possibilities-for-x-6
  (implies (g-ite-p x)
           (and (not (general-concretep x))
                (not (general-consp x))
                (not (general-booleanp x))
                (not (general-numberp x))))
  :hints (("Goal" :by possibilities-for-x))
  :rule-classes ((:rewrite :backchain-limit-lst 0)))

(defthm possibilities-for-x-7
  (implies (g-apply-p x)
           (and (not (general-concretep x))
                (not (general-consp x))
                (not (general-booleanp x))
                (not (general-numberp x))))
  :hints (("Goal" :by possibilities-for-x))
  :rule-classes ((:rewrite :backchain-limit-lst 0)))

(defthm possibilities-for-x-8
  (implies (g-var-p x)
           (and (not (general-concretep x))
                (not (general-consp x))
                (not (general-booleanp x))
                (not (general-numberp x))))
  :hints (("Goal" :by possibilities-for-x))
  :rule-classes ((:rewrite :backchain-limit-lst 0)))

(defthm possibilities-for-x-9
  (implies (and (not (general-concretep x))
                (not (general-consp x))
                (not (general-booleanp x))
                (not (general-numberp x))
                (not (g-ite-p x))
                (not (g-apply-p x)))
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
                                    general-concrete-obj)
          :expand ((general-concrete-obj x))
          :do-not-induct t))
  :rule-classes (:rewrite :type-prescription))

(defthm general-concretep-not-general-booleanp
  (implies (and (general-concretep x)
                (not (general-booleanp x)))
           (not (booleanp (general-concrete-obj x))))
  :hints(("Goal" :in-theory (enable general-concretep-def general-booleanp
                                    general-concrete-obj)
          :expand ((general-concrete-obj x))
          :do-not-induct t))
  :rule-classes :type-prescription)

(defthm general-concretep-not-general-consp
  (implies (and (general-concretep x)
                (not (general-consp x)))
           (not (consp (general-concrete-obj x))))
  :hints(("Goal" :in-theory (enable general-concretep-def general-consp
                                    concrete-gobjectp
                                    g-keyword-symbolp-def
                                    member-equal
                                    general-concrete-obj)
          :expand ((general-concrete-obj x))
          :do-not-induct t))
  :rule-classes :type-prescription)



(defthm general-concrete-obj-when-consp
  (implies (and (bind-free '((env . env)) (env))
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
                (general-numberp x))
           (mv-let (rn rd in id)
             (general-number-components x)
             (equal (general-concrete-obj x)
                    (components-to-number-fn
                     (bfr-list->s rn (car env))
                     (bfr-list->u rd (car env))
                     (bfr-list->s in (car env))
                     (bfr-list->u id (car env))))))
  :hints(("Goal" :in-theory (enable ;general-concretep-def
                             general-numberp
                             general-concrete-obj
                             general-number-components
                             break-g-number)
          :expand ((general-concretep x))
          :do-not-induct t))
  :rule-classes ((:rewrite :backchain-limit-lst 0)))

(defthm general-concrete-obj-when-booleanp
  (implies (and (bind-free '((env . env)) (env))
                (general-concretep x)
                (general-booleanp x))
           (equal (general-concrete-obj x)
                  (bfr-eval (general-boolean-value x) (car env))))
  :hints(("Goal" :in-theory (enable general-booleanp
                                    general-concrete-obj
                                    general-boolean-value)
          :expand ((general-concretep x))
          :do-not-induct t))
  :rule-classes ((:rewrite :backchain-limit-lst 0)))


(defthmd not-general-numberp-not-acl2-numberp
  (implies (and (not (general-numberp x))
                (not (g-ite-p x))
                (not (g-apply-p x))
                (not (g-var-p x)))
           (not (acl2-numberp (generic-geval x env))))
  :hints (("goal" :use possibilities-for-x
           :expand ((generic-geval x env))
           :in-theory (disable general-consp-car-correct
                               general-consp-cdr-correct)
           :do-not-induct t)))

(defthm general-concrete-obj-when-atom
  (implies (not (consp x))
           (equal (general-concrete-obj x) x))
  :hints(("Goal" :in-theory (enable general-concrete-obj)))
  :rule-classes ((:rewrite :backchain-limit-lst 0)))
