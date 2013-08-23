; GL - A Symbolic Simulation Framework for ACL2
; Copyright (C) 2008-2013 Centaur Technology
;
; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/
;
; This program is free software; you can redistribute it and/or modify it under
; the terms of the GNU General Public License as published by the Free Software
; Foundation; either version 2 of the License, or (at your option) any later
; version.  This program is distributed in the hope that it will be useful but
; WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
; FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
; more details.  You should have received a copy of the GNU General Public
; License along with this program; if not, write to the Free Software
; Foundation, Inc., 51 Franklin Street, Suite 500, Boston, MA 02110-1335, USA.
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
         (not (g-number-p x))
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
                (not (g-number-p x))
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
  :hints(("Goal" :in-theory (enable mk-g-boolean booleanp pbfr-depends-on))))



;; (defthm car-mk-g-number
;;   (implies (consp (mk-g-number a b c d e f))
;;            (eq (car (mk-g-number a b c d e f)) :g-number)))


;; (defthm nonzero-natp-implies-us
;;   (implies (and (natp x) (not (eql x 0)))
;;            (n2v x))
;;   :hints(("Goal" :in-theory (e/d (n2v bfr-ucons) (logcar logcdr)))))

(encapsulate nil
  (local (include-book "arithmetic/top-with-meta" :dir :system))
  (local (in-theory (enable components-to-number-fn)))
  (defthm components-to-number-norm-zeros1
    (implies (syntaxp (not (equal iden ''1)))
             (equal (components-to-number rnum rden 0 iden)
                    (components-to-number rnum rden 0  1))))

  (defthm components-to-number-norm-zeros2
    (implies (syntaxp (not (equal inum ''0)))
             (equal (components-to-number rnum rden inum 0)
                    (components-to-number rnum rden 0    1))))

  (defthm components-to-number-norm-zeros3
    (implies (syntaxp (not (equal rden ''1)))
             (equal (components-to-number 0 rden inum iden)
                    (components-to-number 0 1    inum iden))))
  (defthm components-to-number-norm-zeros4
    (implies (syntaxp (not (equal rnum ''0)))
             (equal (components-to-number rnum 0    inum iden)
                    (components-to-number 0    1    inum iden))))

  (defthm components-to-number-alt-def
    (equal (components-to-number rnum rden inum iden)
           (complex (* rnum (/ rden))
                    (* inum (/ iden))))
    :rule-classes :definition)

  (defthm components-to-number-correct
    (implies (acl2-numberp x)
             (equal (components-to-number (numerator (realpart x))
                                          (denominator (realpart x))
                                          (numerator (imagpart x))
                                          (denominator (imagpart x)))
                    x))
    :hints (("goal" :in-theory (enable components-to-number-alt-def)))))



(defthm bfr-eval-booleanp
  (implies (booleanp x)
           (equal (bfr-eval x env) x))
  :hints (("goal" :in-theory (enable bfr-eval)))
  :rule-classes ((:rewrite :backchain-limit-lst 0)))



;; (defthm generic-geval-non-gobjectp
;;   (implies (not (gobjectp x))
;;            (equal (generic-geval x env) x))
;;   :hints(("Goal" :in-theory (enable gobj-fix))))

;; (defthm generic-geval-gobj-fix
;;   (equal (generic-geval (gobj-fix x) env)
;;          (generic-geval x env))
;;   :hints(("Goal" :in-theory (enable gobj-fix))))



(encapsulate nil
  (local (include-book "arithmetic/top-with-meta" :dir :system))
  (local (in-theory
          (e/d*
           (boolean-list-bfr-eval-list)
           (generic-geval mk-g-number
; (components-to-number)
                          components-to-number
                          components-to-number-alt-def
                          bfr-eval bfr-eval-list natp
                          n2v i2v default-car default-cdr
                          (:rules-of-class :type-prescription :here)
                          acl2::cancel_times-equal-correct
                          acl2::cancel_plus-equal-correct
                          equal-of-booleans-rewrite
                          default-+-2 default-+-1 acl2::natp-rw
                          len)
           ((:type-prescription g-number$inline)))))
  (local (defthm len-open-cons
           (equal (len (cons x y))
                  (+ 1 (len y)))
           :hints(("Goal" :in-theory (enable len)))))

  (local (defthm boolean-listp-scdr
           (implies (boolean-listp x)
                    (boolean-listp (scdr x)))
           :hints(("Goal" :in-theory (enable scdr)))))

  (local (defthm bfr-list->s-of-boolean-list-norm
           (implies (and (syntaxp (not (equal env ''nil)))
                         (boolean-listp x))
                    (equal (bfr-list->s x env)
                           (bfr-list->s x nil)))))

  (local (defthm bfr-list->u-of-boolean-list-norm
           (implies (and (syntaxp (not (equal env ''nil)))
                         (boolean-listp x))
                    (equal (bfr-list->u x env)
                           (bfr-list->u x nil)))))

  ;; (local (defthm bfr-list->u-of-list-fix
  ;;          (equal (bfr-list->u (acl2::list-fix x) env)
  ;;                 (bfr-list->u x env))))

  ;; (local (defthm bfr-list->s-of-list-fix
  ;;          (equal (bfr-list->s (acl2::list-fix x) env)
  ;;                 (bfr-list->s x env))))

  (defthm mk-g-number-correct
    (flet ((to-nat (n env) (if (natp n) n (bfr-list->u n (car env))))
           (to-int (n env) (if (integerp n) n (bfr-list->s n (car env)))))
      (equal (generic-geval (mk-g-number rnum rden inum iden) env)
             (components-to-number (to-int rnum env)
                                   (to-nat rden env)
                                   (to-int inum env)
                                   (to-nat iden env))))
    :hints (("Goal" :do-not preprocess)
            ;; '(:cases ((and (integerp rnum) (natp rden)
            ;;                (integerp inum) (natp iden))))
            '(:expand ((:free (a c d f)
                              (mk-g-number a c d f))))
            '(:expand ((:free (a b)
                              (generic-geval
                               (complex a b) env))
                       (:free (x)
                              (generic-geval
                               (g-number x) env))))
            (and stable-under-simplificationp
                 '(:in-theory (e/d (components-to-number-alt-def natp))))))

  (defthm pbfr-depends-on-list-of-boolean-listp
    (implies (and (syntaxp (quotep lst))
                  (boolean-listp lst))
             (not (pbfr-list-depends-on k p lst)))
    :hints(("Goal" :in-theory (enable pbfr-list-depends-on))))

  (local (defthm gobj-depends-on-of-g-number
           (equal (gobj-depends-on k p (g-number n))
                  (or (pbfr-list-depends-on k p (car n))
                      (pbfr-list-depends-on k p (cadr n))
                      (pbfr-list-depends-on k p (caddr n))
                      (pbfr-list-depends-on k p (cadddr n))))
           :hints(("Goal" :in-theory (e/d (break-g-number
                                           default-car default-cdr)
                                          ((pbfr-list-depends-on)))))))

  (local (in-theory (disable gobj-depends-on
                             sets::double-containment
                             default-<-1
                             default-<-2)))

  (defthm gobj-depends-on-of-mk-g-number
    (implies (and (or (integerp rnum)
                      (not (pbfr-list-depends-on k p rnum)))
                  (or (natp rden)
                      (not (pbfr-list-depends-on k p rden)))
                  (or (integerp inum)
                      (not (pbfr-list-depends-on k p inum)))
                  (or (natp iden)
                      (not (pbfr-list-depends-on k p iden))))
             (not (gobj-depends-on k p (mk-g-number-fn rnum rden inum iden))))
    :hints(("Goal" :in-theory (e/d (mk-g-number-fn
                                    (:t components-to-number-fn))
                                   ((pbfr-list-depends-on) max
                                    gobj-depends-on
                                    bfr-list->s
                                    bfr-list->u
                                    norm-bvec-s
                                    norm-bvec-u))
            :expand ((:free (a b c d)
                      (gobj-depends-on k p
                       (components-to-number-fn a b c d)))
                     (mk-g-number-fn rnum rden inum iden))))))






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
                  (NOT (EQUAL (TAG X) :G-NUMBER))
                  (NOT (EQUAL (TAG X) :G-ITE))
                  (NOT (EQUAL (TAG X) :G-VAR))
                  (NOT (EQUAL (TAG X) :G-APPLY)))
             (not (gobj-depends-on k p (car x)))))

  (defthm gobj-depends-on-cdr-of-gobj
    (implies (and (not (gobj-depends-on k p x))
                  (NOT (EQUAL (TAG X) :G-CONCRETE))
                  (NOT (EQUAL (TAG X) :G-BOOLEAN))
                  (NOT (EQUAL (TAG X) :G-NUMBER))
                  (NOT (EQUAL (TAG X) :G-ITE))
                  (NOT (EQUAL (TAG X) :G-VAR))
                  (NOT (EQUAL (TAG X) :G-APPLY)))
             (not (gobj-depends-on k p (cdr x)))))

  (defthm gobj-depends-on-of-g-boolean->bool
    (implies (and (not (gobj-depends-on k p x))
                  (eq (tag x) :g-boolean))
             (not (pbfr-depends-on k p (g-boolean->bool x)))))

  (defthm gobj-depends-on-of-g-number->num-0
    (implies (and (not (gobj-depends-on k p x))
                  (eq (tag x) :g-number))
             (not (pbfr-list-depends-on k p (mv-nth 0 (break-g-number (g-number->num x)))))))

  (defthm gobj-depends-on-of-g-number->num-1
    (implies (and (not (gobj-depends-on k p x))
                  (eq (tag x) :g-number))
             (not (pbfr-list-depends-on k p (mv-nth 1 (break-g-number (g-number->num x)))))))

  (defthm gobj-depends-on-of-g-number->num-2
    (implies (and (not (gobj-depends-on k p x))
                  (eq (tag x) :g-number))
             (not (pbfr-list-depends-on k p (mv-nth 2 (break-g-number (g-number->num x)))))))

  (defthm gobj-depends-on-of-g-number->num-3
    (implies (and (not (gobj-depends-on k p x))
                  (eq (tag x) :g-number))
             (not (pbfr-list-depends-on k p (mv-nth 3 (break-g-number
                                                       (g-number->num x)))))))

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

  (defthm gobj-depends-on-of-g-number
    (equal (gobj-depends-on k p (g-number num))
           (not (b* (((mv rn rd in id) (break-g-number num)))
                  (and (not (pbfr-list-depends-on k p rn))
                       (not (pbfr-list-depends-on k p rd))
                       (not (pbfr-list-depends-on k p in))
                       (not (pbfr-list-depends-on k p id)))))))

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
