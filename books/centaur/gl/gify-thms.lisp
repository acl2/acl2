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
;; (include-book "gify-clause-proc")
(include-book "std/basic/two-nats-measure" :dir :system)
(include-book "generic-geval")
(include-book "gtypes")
(include-book "general-objects")
(include-book "gl-mbe")
(local (include-book "gtype-thms"))
(local (include-book "general-object-thms"))
(local (include-book "hyp-fix"))


;; These events are included here redundantly to avoid having to include all
;; the above (locally-included) books everywhere we want a GL clause processor.

;; (defthm gobjectp-g-apply
;;   (implies (and (symbolp fn)
;;                 (gobjectp args))
;;            (gobjectp (g-apply fn args))))

;; (defthm gobjectp-gl-cons
;;   (gobjectp (gl-cons x y)))

;; (defthm gobjectp-mk-g-concrete
;;   (gobjectp (mk-g-concrete x))
;;   :hints (("goal" :in-theory
;;            (enable gobjectp gobject-hierarchy mk-g-concrete
;;                    concrete-gobjectp-def))))

;; (defthm gobjectp-g-concrete-quote
;;   (gobjectp (g-concrete-quote x))
;;   :hints (("goal" :in-theory
;;            (enable gobjectp gobject-hierarchy g-concrete-quote))))

;; (defthm gobjectp-gobj-fix
;;   (gobjectp (gobj-fix x)))

(defthm mk-g-ite-correct
  (equal (generic-geval (mk-g-ite c x y) b)
         (if (generic-geval c b)
             (generic-geval x b)
           (generic-geval y b))))

(defthm mk-g-boolean-correct
  (equal (generic-geval (mk-g-boolean x) env)
         (bfr-eval x (car env)))
  :hints(("Goal" :in-theory (enable mk-g-boolean))))

(defthm mk-g-concrete-correct
  (equal (generic-geval (mk-g-concrete x) b)
         x))

(defthm g-concrete-quote-correct
  (equal (generic-geval (g-concrete-quote x) b)
         x)
  :hints(("Goal" :in-theory
          (enable eval-concrete-gobjectp
                  concrete-gobjectp-def
                  g-concrete-quote))))

;; (defthm gobj-fix-when-gobjectp
;;   (implies (gobjectp x)
;;            (equal (gobj-fix x) x))
;;   :hints(("Goal" :in-theory (enable gobj-fix))))

(defthm generic-geval-gl-cons
  (equal (generic-geval (gl-cons x y) env)
         (cons (generic-geval x env)
               (generic-geval y env))))

(defthm generic-geval-list-gl-cons
  (equal (generic-geval-list (gl-cons x y) env)
         (cons (generic-geval x env)
               (generic-geval-list y env)))
  :hints(("Goal" :expand ((:free (x) (generic-geval-list (cons x y) env))))))

(defthm generic-geval-list-atom
  (implies (not (consp x))
           (equal (generic-geval-list x env) nil))
  :hints(("Goal" :expand ((generic-geval-list x env))))
  :rule-classes ((:rewrite :backchain-limit-lst 0)))

(defthm generic-geval-g-apply
  (implies (not (equal fn 'quote))
           (equal (generic-geval (g-apply fn args) env)
                  (generic-geval-ev (cons fn (kwote-lst (generic-geval-list args env)))
                                    nil)))
  :hints (("goal" :expand ((generic-geval (g-apply fn args) env))
           :in-theory (enable generic-geval-apply))))

(defthm generic-geval-nil
  (equal (generic-geval nil env) nil))

(defthm generic-geval-non-cons
  (implies (not (consp x))
           (equal (generic-geval x env) x))
  :rule-classes ((:rewrite :backchain-limit-lst 0)))

;; (defthm generic-geval-g-apply
;;   (implies (not (eq fn 'quote))
;;            (equal (generic-geval (g-apply fn args) env)
;;                   (generic-geval-ev (cons fn (kwote-lst (generic-geval-list args env)))
;;                                     nil))))

;; (defthm generic-geval-gobj-fix
;;   (equal (generic-geval (gobj-fix x) env)
;;          (generic-geval x env)))

;; (defthm general-concrete-obj-correct-gobj-fix
;;   (implies (general-concretep (gobj-fix x))
;;            (equal (general-concrete-obj (gobj-fix x))
;;                   (generic-geval x env)))
;;   :rule-classes ((:rewrite :backchain-limit-lst 0)))

(defthmd general-concrete-obj-correct
  (implies (general-concretep x)
           (equal (generic-geval x env)
                  (general-concrete-obj x))))

;; (defthm hyp-fix-bfr-p
;;   (bfr-p (hyp-fix x hyp)))


(defthm natp-of-nfix
  (natp (nfix x)))

(defthm nfix-natp
  (implies (natp n)
           (equal (nfix n) n))
  :rule-classes ((:rewrite :backchain-limit-lst 0)))

;; (defthm bfr-p-bfr-fix
;;   (bfr-p (bfr-fix x)))


;; (add-to-ruleset! g-gobjectp-lemmas '(g-if-gobjectp-meta-correct
;;                                      gobjectp-g-if-marker
;;                                      g-or-gobjectp-meta-correct
;;                                      gobjectp-g-or-marker
;;                                      gobjectp-g-apply
;;                                      gobjectp-gobj-fix
;;                                      gobjectp-g-test-marker
;;                                      gobjectp-g-branch-marker
;;                                      gtests-wfp
;;                                      gobjectp-gl-cons
;;                                      bfr-p-bfr-binary-and
;;                                      bfr-p-bfr-not
;;                                      bfr-p-bfr-binary-or
;;                                      bfr-p-bfr-fix
;;                                      bfr-and-of-nil
;;                                      bfr-or-of-t
;;                                      gobjectp-mk-g-concrete
;;                                      gobjectp-g-concrete-quote
;;                                      gobjectp-of-atomic-constants
;;                                      hyp-fix-bfr-p
;;                                      bfr-and-of-nil
;;                                      bfr-or-of-t
;;                                      (g-keyword-symbolp)
;;                                      gl-aside gl-error-is-nil))

(def-ruleset! generic-geval-g-correct-lemmas
  '(generic-geval-gl-cons
    generic-geval-nil
    generic-geval-g-apply
    generic-geval-list-gl-cons
    generic-geval-list-atom
    mk-g-ite-correct
    mk-g-boolean-correct
    mk-g-concrete-correct
    g-concrete-quote-correct
    general-concrete-obj-correct))


(def-ruleset! g-correct-lemmas '(bfr-eval-bfr-binary-and
                                 bfr-eval-bfr-binary-or
                                 bfr-eval-bfr-not
                                 gl-aside
                                 gl-error-is-nil
                                 bfr-equiv-is-an-equivalence
                                 bfr-equiv-implies-equal-bfr-eval-1
                                 bfr-and-of-nil
                                 bfr-or-of-t
                                 (g-keyword-symbolp)
                                 gl-aside gl-error-is-nil))

;; (defthm bfr-fix-x-is-x-when-bfr-p
;;   (implies (bfr-p x)
;;            (equal (bfr-fix x) x)))

;; (defthm gobjectp-mk-g-ite
;;   (gobjectp (mk-g-ite c x y)))


(def-ruleset! g-guard-lemmas '(natp-compound-recognizer
                               ;; gobj-fix-when-gobjectp
                               natp-of-nfix gl-aside
                               ;; bfr-p-bfr-fix
                               ;; bfr-fix-x-is-x-when-bfr-p
                               ;; gobjectp-gobj-ite-merge
                               ;; gobjectp-mk-g-ite
                               ;; mk-g-bdd-ite-gobjectp
                               gl-error-is-nil
                               ;; bfr-p-g-hyp-marker
                               bfr-and-of-nil
                               bfr-or-of-t
                               (g-keyword-symbolp)
                               gl-aside gl-error-is-nil
                               ))


(defthmd <-asym (not (< a a)))

(def-ruleset! clk-measure-rules
  '((:compound-recognizer natp-compound-recognizer)
    (:compound-recognizer acl2::zp-compound-recognizer)
    (:definition nfix)
    (:definition not)
    (:executable-counterpart <)
    (:executable-counterpart eql)
    (:executable-counterpart equal)
    (:executable-counterpart if)
    (:executable-counterpart nfix)
    (:rewrite <-asym)
    (:rewrite nfix-natp)
    (:rewrite acl2::o-p-of-two-nats-measure)
    (:rewrite acl2::o<-of-two-nats-measure)))
