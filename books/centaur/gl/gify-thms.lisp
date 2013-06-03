

(in-package "GL")

(include-book "gify-clause-proc")

(local (include-book "gtype-thms"))
(local (include-book "gobjectp-thms"))
(local (include-book "general-object-thms"))
(local (include-book "hyp-fix-logic"))
(include-book "std/misc/two-nats-measure" :dir :system)

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

(defthm generic-geval-nil
  (equal (generic-geval nil env) nil))

(defthm generic-geval-non-cons
  (implies (not (consp x))
           (equal (generic-geval x env) x))
  :rule-classes ((:rewrite :backchain-limit-lst 0)))

(defthm generic-geval-g-apply
  (equal (generic-geval (g-apply fn args) env)
         (generic-geval-ev (cons fn (kwote-lst (generic-geval args env)))
                           nil)))

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

(defthm hyp-fix-correct
    (implies (bfr-eval hyp env)
             (equal (bfr-eval (hyp-fix x hyp) env)
                    (bfr-eval x env)))
    :hints(("Goal" :in-theory (enable bfr-and))))

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
    mk-g-ite-correct
    mk-g-boolean-correct
    mk-g-concrete-correct
    g-concrete-quote-correct
    gtests-nonnil-correct
    gtests-obj-correct
    gobj-ite-merge-correct
    general-concrete-obj-correct))


(def-ruleset! g-correct-lemmas '(bfr-eval-bfr-binary-and
                                 bfr-eval-bfr-binary-or
                                 bfr-eval-bfr-not
                                 hyp-fix-correct
                                 gl-aside
                                 gl-error-is-nil
                                 gtests-g-test-marker
                                 bfr-equiv-is-an-equivalence
                                 bfr-equiv-implies-equal-bfr-eval-1
                                 bfr-eval-g-hyp-marker
                                 bfr-and-of-nil
                                 bfr-or-of-t
                                 (g-keyword-symbolp)
                                 gl-aside gl-error-is-nil))

;; (defthm bfr-fix-x-is-x-when-bfr-p
;;   (implies (bfr-p x)
;;            (equal (bfr-fix x) x)))

;; (defthm gobjectp-mk-g-ite
;;   (gobjectp (mk-g-ite c x y)))


(def-ruleset! g-guard-lemmas '(gtestsp-gtests
                               natp-compound-recognizer
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
