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

(include-book "gtypes")


;; -------------------------
;; Concrete-gobjectp
;; -------------------------

(defun concrete-gobjectp-ind (x)
  (if (atom x)
      x
    (and (not (g-concrete-p x))
         (not (g-boolean-p x))
         (not (g-integer-p x))
         (not (g-ite-p x))
         (not (g-apply-p x))
         (not (g-var-p x))
         (list (concrete-gobjectp-ind (car x))
               (concrete-gobjectp-ind (cdr x))))))


(defthm gobject-hierarchy-lite-possibilities
  (or (equal (gobject-hierarchy-lite x) nil)
      (equal (gobject-hierarchy-lite x) 'concrete)
      (equal (gobject-hierarchy-lite x) 'general))
  :hints(("Goal" :in-theory (enable gobject-hierarchy-lite)))
  :rule-classes ((:forward-chaining :trigger-terms ((gobject-hierarchy-lite x)))))

(defthm concrete-gobjectp-def
  (equal (concrete-gobjectp x)
         (if (atom x)
             t
           (and (not (g-concrete-p x))
                (not (g-boolean-p x))
                (not (g-integer-p x))
                (not (g-ite-p x))
                (not (g-apply-p x))
                (not (g-var-p x))
                (concrete-gobjectp (car x))
                (concrete-gobjectp (cdr x)))))
  :hints (("goal" :induct (concrete-gobjectp-ind x)
           :expand ((gobject-hierarchy-lite x))
           :in-theory (enable concrete-gobjectp)))
  :rule-classes :definition)


;; (defthmd concrete-gobjectp-gobjectp
;;   (implies (concrete-gobjectp x)
;;            (gobjectp x))
;;   :hints(("Goal" :in-theory
;;           (enable concrete-gobjectp gobjectp))))

(defthmd eval-concrete-gobjectp
  (implies (concrete-gobjectp x)
           (equal (generic-geval x env) x))
  :hints (("goal" :induct (concrete-gobjectp-ind x)
           :expand ((generic-geval x env))
           :in-theory
           (e/d** (generic-geval
                   concrete-gobjectp-ind
                   concrete-gobjectp-def
                   acl2::cons-car-cdr)))))

(defthmd gobj-depends-on-when-concrete-gobjectp
  (implies (concrete-gobjectp x)
           (not (gobj-depends-on k p x)))
  :hints (("goal" :induct (concrete-gobjectp-ind x)
           :expand ((gobj-depends-on k p x)))))

(in-theory (disable concrete-gobjectp-def))


(local (in-theory (enable generic-geval)))

(defthm mk-g-concrete-correct
  (equal (generic-geval (mk-g-concrete x) b)
         x)
  :hints(("Goal" :in-theory
          (enable eval-concrete-gobjectp
                  mk-g-concrete))))

(defthm g-concrete-quote-correct
  (equal (generic-geval (g-concrete-quote x) b)
         x)
  :hints(("Goal" :in-theory
          (enable eval-concrete-gobjectp
                  concrete-gobjectp-def
                  g-concrete-quote))))


(defthm gobj-depends-on-of-mk-g-concrete
  (not (gobj-depends-on k p (mk-g-concrete x)))
  :hints(("Goal" :in-theory (enable gobj-depends-on mk-g-concrete
                                    gobj-depends-on-when-concrete-gobjectp))))

(defthm gobj-depends-on-of-g-concrete-quote
  (not (gobj-depends-on k p (g-concrete-quote x)))
  :hints(("Goal" :in-theory (enable gobj-depends-on g-concrete-quote))))


(defthm mk-g-ite-correct
  (equal (generic-geval (mk-g-ite c x y) b)
         (if (generic-geval c b)
             (generic-geval x b)
           (generic-geval y b)))
  :hints(("Goal" :in-theory (enable mk-g-ite)
          :do-not-induct t)
         (and stable-under-simplificationp
              '(:expand ((generic-geval c b)))))
  :otf-flg t)

(defthm gobj-depends-on-of-mk-g-ite-rw
  (implies (and (not (gobj-depends-on k p c))
                (not (gobj-depends-on k p x))
                (not (gobj-depends-on k p y)))
           (not (gobj-depends-on k p (mk-g-ite c x y))))
  :hints(("Goal" :in-theory (enable mk-g-ite))))


(defthm mk-g-boolean-correct
  (equal (generic-geval (mk-g-boolean x) env)
         (bfr-eval x (car env)))
  :hints(("Goal" :in-theory (enable mk-g-boolean))))

(defthm gobj-depends-on-of-mk-g-boolean
  (equal (gobj-depends-on k p (mk-g-boolean x))
         (pbfr-depends-on k p x))
  :hints(("Goal" :in-theory (enable mk-g-boolean booleanp))))



;; (defthm car-mk-g-number
;;   (implies (consp (mk-g-number a b c d e f))
;;            (eq (car (mk-g-number a b c d e f)) :g-number)))


;; (defthm nonzero-natp-implies-us
;;   (implies (and (natp x) (not (eql x 0)))
;;            (n2v x))
;;   :hints(("Goal" :in-theory (e/d (n2v bfr-ucons) (logcar logcdr)))))


(defthm bfr-eval-booleanp
  (implies (booleanp x)
           (equal (bfr-eval x env) x))
  :hints (("goal" :in-theory (enable bfr-eval)))
  :rule-classes ((:rewrite :backchain-limit-lst 0)))


(local (defthm bfr-list->s-when-boolean-list
         (implies (and (syntaxp (not (equal env ''nil)))
                       (boolean-listp bits))
                  (equal (bfr-list->s bits env)
                         (bfr-list->s bits nil)))
         :hints(("Goal" :in-theory (enable bfr-list->s boolean-listp scdr)))))

(defthm mk-g-integer-correct
  (equal (generic-geval (mk-g-integer bits) env)
         (bfr-list->s bits (car env)))
  :hints(("Goal" :in-theory (enable mk-g-integer))))

(local (defthm pbfr-list-depends-on-of-boolean-list
         (implies (boolean-listp x)
                  (not (pbfr-list-depends-on k p x)))
         :hints(("Goal" :in-theory (enable pbfr-list-depends-on)))))

(defthm gobj-depends-on-of-mk-g-integer
  (equal (gobj-depends-on k p (mk-g-integer x))
         (pbfr-list-depends-on k p x))
  :hints(("Goal" :in-theory (enable mk-g-integer))))








;; -------------------------
;; Cons
;; -------------------------



;; (defthm gobjectp-cons
;;   (implies (and (gobjectp x) (gobjectp y))
;;            (gobjectp (cons x y)))
;;   :hints (("goal" :expand ((:with gobjectp-def
;;                                   (gobjectp (cons x y)))
;;                            (g-boolean-p (cons x y))
;;                            (g-number-p (cons x y))
;;                            (g-concrete-p (cons x y))
;;                            (g-ite-p (cons x y))
;;                            (g-var-p (cons x y))
;;                            (g-apply-p (cons x y))
;;                            (tag (cons x y)))
;;            :do-not-induct t
;;            :in-theory (disable (force)))))


(defthm generic-geval-cons
  (implies (not (g-keyword-symbolp x))
           (equal (generic-geval (cons x y) env)
                  (cons (generic-geval x env)
                        (generic-geval y env))))
  :hints (("goal" :expand ((generic-geval (cons x y) env))
           :in-theory (e/d (tag)))))

(defthm generic-geval-non-cons
  (implies (not (consp x))
           (equal (generic-geval x env) x))
  :hints (("goal" :expand ((:with generic-geval (generic-geval x env)))
           :do-not-induct t))
  :rule-classes ((:rewrite :backchain-limit-lst 0)))

(defthm g-keyword-symbolp-compound-recognizer
  (implies (g-keyword-symbolp x)
           (and (symbolp x)
                (not (booleanp x))))
  :rule-classes :compound-recognizer)

;; (defthm gobjectp-gl-cons
;;   (gobjectp (gl-cons x y)))

(defthm generic-geval-gl-cons
  (equal (generic-geval (gl-cons x y) env)
         (cons (generic-geval x env)
               (generic-geval y env))))

(defthm gobj-depends-on-of-gl-cons
  (equal (gobj-depends-on k p (gl-cons x y))
         (or (gobj-depends-on k p x)
             (gobj-depends-on k p y)))
  :hints(("Goal" :in-theory (enable gl-cons)
          :expand ((gobj-depends-on k p (cons x y))))))

(defthm generic-geval-list-gl-cons
  (equal (generic-geval-list (gl-cons x y) env)
         (cons (generic-geval x env)
               (generic-geval-list y env)))
  :hints(("Goal" :expand ((:free (x) (generic-geval-list (cons x y) env))))))

(defthm gobj-list-depends-on-of-gl-cons
  (equal (gobj-list-depends-on k p (gl-cons x y))
         (or (gobj-depends-on k p x)
             (gobj-list-depends-on k p y)))
  :hints(("Goal" :in-theory (enable gl-cons))))

(defthm generic-geval-list-atom
  (implies (not (consp x))
           (equal (generic-geval-list x env) nil))
  :hints(("Goal" :expand ((generic-geval-list x env))))
  :rule-classes ((:rewrite :backchain-limit-lst 0)))

(in-theory (disable gl-cons))

(defthmd generic-geval-of-gobj-list
  (implies (and (gobj-listp x)
                (consp x))
           (equal (generic-geval x env)
                  (cons (generic-geval (car x) env)
                        (generic-geval (cdr x) env))))
  :hints(("Goal" :use ((:instance generic-geval-gl-cons
                        (x (car x)) (y (cdr x))))
          :in-theory (enable gl-cons gobj-listp))))



;; -------------------------
;; Apply
;; -------------------------


;; (defthm gobjectp-g-apply
;;   (implies (and (symbolp fn)
;;                 (gobjectp args))
;;            (gobjectp (g-apply fn args)))
;;   :hints (("goal" :expand ((gobjectp (g-apply fn args))))))


;; (defthm gobjectp-g-apply->args
;;   (implies (and (gobjectp x)
;;                 (g-apply-p x))
;;            (gobjectp (g-apply->args x)))
;;   :hints(("Goal" :in-theory (e/d (gobjectp) ((force))))))


(defthm generic-geval-g-apply
  (implies (not (equal fn 'quote))
           (equal (generic-geval (g-apply fn args) env)
                  (generic-geval-ev (cons fn (kwote-lst (generic-geval-list args env)))
                                    nil)))
  :hints (("goal" :expand ((generic-geval (g-apply fn args) env))
           :in-theory (enable generic-geval-apply))))

(defthmd generic-geval-g-apply-p
  (implies (and (g-apply-p x)
                (not (equal (g-apply->fn x) 'quote)))
           (equal (generic-geval x env)
                  (generic-geval-ev
                   (cons (g-apply->fn x)
                         (kwote-lst (generic-geval-list (g-apply->args x) env)))
                   nil)))
  :hints (("goal" :expand ((generic-geval x env))
           :in-theory (enable generic-geval-apply)))
  :rule-classes ((:rewrite :backchain-limit-lst 0)))





(defsection gobj-depends-on

  (local (in-theory (enable gobj-depends-on)))

  (defthm gobj-list-depends-on-of-g-apply->args
    (implies (and (not (gobj-depends-on k p x))
                  (eq (tag x) :g-apply))
             (not (gobj-list-depends-on k p (g-apply->args x)))))

  (defthm gobj-depends-on-of-g-ite->test
    (implies (and (not (gobj-depends-on k p x))
                  (eq (tag x) :g-ite))
             (not (gobj-depends-on k p (g-ite->test x)))))

  (defthm gobj-depends-on-of-g-ite->then
    (implies (and (not (gobj-depends-on k p x))
                  (eq (tag x) :g-ite))
             (not (gobj-depends-on k p (g-ite->then x)))))

  (defthm gobj-depends-on-of-g-ite->else
    (implies (and (not (gobj-depends-on k p x))
                  (eq (tag x) :g-ite))
             (not (gobj-depends-on k p (g-ite->else x)))))

  (defthm gobj-depends-on-car-of-gobj-list
    (implies (not (gobj-list-depends-on k p x))
             (not (gobj-depends-on k p (car x)))))

  (defthm gobj-list-depends-on-cdr-of-gobj-list
    (implies (not (gobj-list-depends-on k p x))
             (not (gobj-list-depends-on k p (cdr x)))))

  (defthm gobj-list-depends-on-of-cons
    (equal (gobj-list-depends-on k p (cons a b))
           (not (and (not (gobj-depends-on k p a))
                     (not (gobj-list-depends-on k p b))))))

  (defthm gobj-list-depends-on-of-atom
    (implies (not (consp x))
             (equal (gobj-list-depends-on k p x) nil))
    :rule-classes ((:rewrite :backchain-limit-lst 0)))

  (defthm gobj-depends-on-car-of-gobj
    (implies (and (not (gobj-depends-on k p x))
                  (NOT (EQUAL (TAG X) :G-CONCRETE))
                  (NOT (EQUAL (TAG X) :G-BOOLEAN))
                  (NOT (EQUAL (TAG X) :G-INTEGER))
                  (NOT (EQUAL (TAG X) :G-ITE))
                  (NOT (EQUAL (TAG X) :G-VAR))
                  (NOT (EQUAL (TAG X) :G-APPLY)))
             (not (gobj-depends-on k p (car x)))))

  (defthm gobj-depends-on-cdr-of-gobj
    (implies (and (not (gobj-depends-on k p x))
                  (NOT (EQUAL (TAG X) :G-CONCRETE))
                  (NOT (EQUAL (TAG X) :G-BOOLEAN))
                  (NOT (EQUAL (TAG X) :G-INTEGER))
                  (NOT (EQUAL (TAG X) :G-ITE))
                  (NOT (EQUAL (TAG X) :G-VAR))
                  (NOT (EQUAL (TAG X) :G-APPLY)))
             (not (gobj-depends-on k p (cdr x)))))

  (defthm gobj-depends-on-of-g-boolean->bool
    (implies (and (not (gobj-depends-on k p x))
                  (eq (tag x) :g-boolean))
             (not (pbfr-depends-on k p (g-boolean->bool x)))))

  (defthm gobj-depends-on-of-g-integer->bits
    (implies (and (not (gobj-depends-on k p x))
                  (eq (tag x) :g-integer))
             (not (pbfr-list-depends-on k p (g-integer->bits x)))))

  (defthm-gobj-flag
    (defthm generic-geval-of-set-var-when-gobj-depends-on
      (implies (and (not (gobj-depends-on k p x))
                    (bfr-eval p env)
                    (bfr-eval p (bfr-set-var k v env)))
               (equal (generic-geval x (cons (bfr-param-env p (bfr-set-var k v env))
                                             var-env))
                      (generic-geval x (cons (bfr-param-env p env)
                                             var-env))))
      :hints ('(:expand ((:free (env) (:with generic-geval (generic-geval x env))))))
      :flag gobj)
    (defthm generic-geval-list-of-set-var-when-gobj-depends-on
      (implies (and (not (gobj-list-depends-on k p x))
                    (bfr-eval p env)
                    (bfr-eval p (bfr-set-var k v env)))
               (equal (generic-geval-list x (cons (bfr-param-env p (bfr-set-var k v env))
                                                  var-env))
                      (generic-geval-list x (cons (bfr-param-env p env)
                                                  var-env))))
      :hints ('(:expand ((:free (env) (generic-geval-list x env)))))
      :flag list))

  (defthm gobj-depends-on-of-atom
    (implies (not (consp x))
             (not (gobj-depends-on k p x)))
    :rule-classes ((:rewrite :backchain-limit-lst 0)))

  (defthm gobj-depends-on-of-cons
    (implies (not (g-keyword-symbolp x))
             (equal (gobj-depends-on k p (cons x y))
                    (not (and (not (gobj-depends-on k p x))
                              (not (gobj-depends-on k p y))))))
    :hints(("Goal" :in-theory (enable g-keyword-symbolp))))



  (defthm gobj-depends-on-of-g-apply
    (equal (gobj-depends-on k p (g-apply fn args))
           (gobj-list-depends-on k p args)))

  (defthm gobj-depends-on-of-g-ite
    (equal (gobj-depends-on k p (g-ite test then else))
           (not (and (not (gobj-depends-on k p test))
                     (not (gobj-depends-on k p then))
                     (not (gobj-depends-on k p else))))))

  (defthm gobj-depends-on-of-g-boolean
    (equal (gobj-depends-on k p (g-boolean bool))
           (pbfr-depends-on k p bool)))

  (defthm gobj-depends-on-of-g-concrete
    (equal (gobj-depends-on k p (g-concrete val)) nil))

  (defthm gobj-depends-on-of-g-var
    (equal (gobj-depends-on k p (g-var val)) nil))


  (defthm gobj-depends-on-when-g-concrete
    (implies (equal (tag x) :g-concrete)
             (equal (gobj-depends-on k p x) nil))
    :hints (("goal" :expand ((not (gobj-depends-on k p x)))))
    :rule-classes ((:rewrite :backchain-limit-lst 0)))

  (defthm gobj-depends-on-when-g-var
    (implies (equal (tag x) :g-var)
             (equal (gobj-depends-on k p x) nil))
    :hints (("goal" :expand ((gobj-depends-on k p x))))
    :rule-classes ((:rewrite :backchain-limit-lst 0))))
