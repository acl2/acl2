; Copyright (C) 2026, Matt Kaufmann
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

(in-package "ZF")

(include-book "base")

(defun bijection (f)
  (and (funp f)
       (funp (inverse f))))

(defthmz bijection-inverse
  (implies (force (relation-p f))
           (equal (bijection (inverse f))
                  (bijection f)))
  :props (zfc prod2$prop inverse$prop))

(defthm binjection-forward
  (implies (bijection f)
           (and (funp f)
                (funp (inverse f))))
  :rule-classes :forward-chaining)

(include-book "restrict")

;;;<<Begin proof by Claude, Opus 6.8 max effort, of bijection-union2
;;;  (original :props : (zfc prod2$prop inverse$prop domain$prop diff$prop restrict$prop).>>

; Used (locally) to discharge inverse-compose and bijection-union2 below.
(local (include-book "projects/set-theory/inverse" :dir :system))

; ----------------------------------------------------------------------------
; Proof of bijection-union2.  Since (bijection h) = (funp h) /\ (funp (inverse
; h)) and (inverse (union2 f g)) = (union2 (inverse f) (inverse g)), the result
; reduces to a characterization of when the union of two functions is a function
; (funp-union2-general, below): they must agree on the intersection of their
; domains.  Applying that to f,g and to (inverse f),(inverse g), and noting that
; the agreement of the inverses on (int2 (image f) (image g)) is equivalent --
; given that f and g already agree on their common domain -- to (equal (int2
; (image f) (image g)) (image (restrict f (int2 (domain f) (domain g))))), yields
; the theorem.  The supporting lemmas are local.
; ----------------------------------------------------------------------------

; A union of two functions is a function exactly when they agree on the
; intersection of their domains.
(local
 (defthmz funp-union2-general-back
   (implies (and (funp f) (funp g)
                 (equal (restrict f (int2 (domain f) (domain g)))
                        (restrict g (int2 (domain f) (domain g)))))
            (funp (union2 f g)))
   :hints (("Goal"
            :expand ((funp (union2 f g)))
            :in-theory (enable in-union2 restrict$comprehension in-int2))
           ("Subgoal 2.3"
            :use ((:instance restrict$comprehension
                             (p (car (funp-witness (union2 f g))))
                             (f f) (s (int2 (domain f) (domain g))))
                  (:instance restrict$comprehension
                             (p (car (funp-witness (union2 f g))))
                             (f g) (s (int2 (domain f) (domain g))))))
           ("Subgoal 2.2"
            :use ((:instance restrict$comprehension
                             (p (mv-nth 1 (funp-witness (union2 f g))))
                             (f f) (s (int2 (domain f) (domain g))))
                  (:instance restrict$comprehension
                             (p (mv-nth 1 (funp-witness (union2 f g))))
                             (f g) (s (int2 (domain f) (domain g)))))))
   :props (zfc domain$prop diff$prop restrict$prop)))

(local
 (defthmz funp-subset
   (implies (and (funp h) (subset k h))
            (funp k))
   :hints (("Goal"
            :expand ((funp k) (relation-p k))
            :use ((:instance funp-necc (f h)
                             (p1 (mv-nth 0 (funp-witness k)))
                             (p2 (mv-nth 1 (funp-witness k))))
                  (:instance subset-preserves-in-1
                             (a (mv-nth 0 (funp-witness k))) (x k) (y h))
                  (:instance subset-preserves-in-1
                             (a (mv-nth 1 (funp-witness k))) (x k) (y h))
                  (:instance subset-preserves-in-1
                             (a (relation-p-witness k)) (x k) (y h)))))
   :props (zfc)))

(local
 (defthmz in-restrict-f-implies-in-restrict-g
   (implies (and (funp (union2 f g))
                 (in p (restrict f (int2 (domain f) (domain g)))))
            (in p (restrict g (int2 (domain f) (domain g)))))
   :hints (("Goal"
            :in-theory (enable restrict$comprehension in-int2 in-union2)
            :use ((:instance funp-necc (f (union2 f g))
                             (p1 p)
                             (p2 (cons (car p) (apply g (car p)))))
                  (:instance in-cons-apply (x (car p)) (f g)))))
   :props (zfc domain$prop diff$prop restrict$prop)
   :rule-classes nil))

(local
 (defthmz in-restrict-g-implies-in-restrict-f
   (implies (and (funp (union2 f g))
                 (in p (restrict g (int2 (domain f) (domain g)))))
            (in p (restrict f (int2 (domain f) (domain g)))))
   :hints (("Goal"
            :in-theory (enable restrict$comprehension in-int2 in-union2)
            :use ((:instance funp-necc (f (union2 f g))
                             (p1 p)
                             (p2 (cons (car p) (apply f (car p)))))
                  (:instance in-cons-apply (x (car p)) (f f)))))
   :props (zfc domain$prop diff$prop restrict$prop)
   :rule-classes nil))

(local
 (defthmz restrict-agree-from-funp-union2
   (implies (funp (union2 f g))
            (equal (restrict f (int2 (domain f) (domain g)))
                   (restrict g (int2 (domain f) (domain g)))))
   :hints (("Goal"
            :in-theory (enable subset)
            :use ((:instance extensionality
                             (x (restrict f (int2 (domain f) (domain g))))
                             (y (restrict g (int2 (domain f) (domain g)))))
                  (:instance in-restrict-f-implies-in-restrict-g
                             (p (subset-witness (restrict f (int2 (domain f) (domain g)))
                                                (restrict g (int2 (domain f) (domain g))))))
                  (:instance in-restrict-g-implies-in-restrict-f
                             (p (subset-witness (restrict g (int2 (domain f) (domain g)))
                                                (restrict f (int2 (domain f) (domain g)))))))))
   :props (zfc domain$prop diff$prop restrict$prop)))

(local
 (defthmz funp-union2-general
   (equal (funp (union2 f g))
          (and (funp f) (funp g)
               (equal (restrict f (int2 (domain f) (domain g)))
                      (restrict g (int2 (domain f) (domain g))))))
   :hints (("Goal"
            :use (funp-union2-general-back
                  restrict-agree-from-funp-union2
                  (:instance funp-subset (h (union2 f g)) (k f))
                  (:instance funp-subset (h (union2 f g)) (k g)))))
   :props (zfc domain$prop diff$prop restrict$prop)))

(local
 (defthmz inverse-union2
   (equal (inverse (union2 r1 r2))
          (union2 (inverse r1) (inverse r2)))
   :hints (("Goal" :in-theory (enable extensionality)))
   :props (zfc prod2$prop inverse$prop)))

; f and g agree (as functions) at each point of the intersection of their domains.
(local
 (defthmz apply-equal-on-int2-domain
   (implies (and (funp f) (funp g)
                 (equal (restrict f (int2 (domain f) (domain g)))
                        (restrict g (int2 (domain f) (domain g))))
                 (in y (int2 (domain f) (domain g))))
            (equal (apply f y) (apply g y)))
   :hints (("Goal"
            :in-theory (e/d (restrict$comprehension in-int2) (apply-car-is-cdr))
            :use ((:instance restrict$comprehension
                             (p (cons y (apply f y))) (f f) (s (int2 (domain f) (domain g))))
                  (:instance restrict$comprehension
                             (p (cons y (apply f y))) (f g) (s (int2 (domain f) (domain g))))
                  (:instance in-cons-apply (x y) (f f))
                  (:instance apply-car-is-cdr (f g) (p (cons y (apply f y)))))))
   :props (zfc domain$prop diff$prop restrict$prop)
   :rule-classes nil))

; The image of (restrict f (int2 (domain f) (domain g))) is contained in (and,
; when the inverses also agree, equal to) (int2 (image f) (image g)).
(local
 (defthmz subset-img-int
   (implies (and (funp f) (funp g)
                 (equal (restrict f (int2 (domain f) (domain g)))
                        (restrict g (int2 (domain f) (domain g)))))
            (subset (image (restrict f (int2 (domain f) (domain g))))
                    (int2 (image f) (image g))))
   :hints (("Goal"
            :in-theory (enable subset in-int2)
            :use ((:instance image-restrict (fn f) (s (int2 (domain f) (domain g))))
                  (:instance image-restrict (fn g) (s (int2 (domain f) (domain g))))
                  (:instance subset-preserves-in-1
                             (a (subset-witness (image (restrict f (int2 (domain f) (domain g))))
                                                (int2 (image f) (image g))))
                             (x (image (restrict f (int2 (domain f) (domain g))))) (y (image f)))
                  (:instance subset-preserves-in-1
                             (a (subset-witness (image (restrict f (int2 (domain f) (domain g))))
                                                (int2 (image f) (image g))))
                             (x (image (restrict g (int2 (domain f) (domain g))))) (y (image g))))))
   :props (zfc prod2$prop domain$prop inverse$prop diff$prop restrict$prop)))

(local
 (defthmz subset-int-img
   (implies (and (funp f) (funp g) (funp (inverse f)) (funp (inverse g))
                 (equal (restrict f (int2 (domain f) (domain g)))
                        (restrict g (int2 (domain f) (domain g))))
                 (equal (restrict (inverse f) (int2 (image f) (image g)))
                        (restrict (inverse g) (int2 (image f) (image g)))))
            (subset (int2 (image f) (image g))
                    (image (restrict f (int2 (domain f) (domain g))))))
   :hints (("Goal"
            :in-theory (enable subset in-int2 domain-inverse)
            :use ((:instance apply-equal-on-int2-domain (f (inverse f)) (g (inverse g))
                             (y (subset-witness (int2 (image f) (image g))
                                                (image (restrict f (int2 (domain f) (domain g)))))))
                  (:instance apply-apply-inverse (f f)
                             (x (subset-witness (int2 (image f) (image g))
                                                (image (restrict f (int2 (domain f) (domain g)))))))
                  (:instance in-image-implies-in-apply-inverse-domain (r f) (d (domain f))
                             (y (subset-witness (int2 (image f) (image g))
                                                (image (restrict f (int2 (domain f) (domain g)))))))
                  (:instance in-image-implies-in-apply-inverse-domain (r g) (d (domain g))
                             (y (subset-witness (int2 (image f) (image g))
                                                (image (restrict f (int2 (domain f) (domain g)))))))
                  (:instance domain-restrict-3 (f f) (s (int2 (domain f) (domain g)))
                             (x (apply (inverse f)
                                       (subset-witness (int2 (image f) (image g))
                                                       (image (restrict f (int2 (domain f) (domain g))))))))
                  (:instance apply-restrict (f f) (x (int2 (domain f) (domain g)))
                             (a (apply (inverse f)
                                       (subset-witness (int2 (image f) (image g))
                                                       (image (restrict f (int2 (domain f) (domain g))))))))
                  (:instance in-apply-image (r (restrict f (int2 (domain f) (domain g))))
                             (x (apply (inverse f)
                                       (subset-witness (int2 (image f) (image g))
                                                       (image (restrict f (int2 (domain f) (domain g)))))))))))
   :props (zfc prod2$prop domain$prop inverse$prop diff$prop restrict$prop)))

; An injective function has unique preimages.
(local
 (defthmz preimage-unique
   (implies (and (funp (inverse f)) (in (cons a y) f) (in (cons b y) f))
            (equal a b))
   :hints (("Goal"
            :in-theory (enable in-inverse)
            :use ((:instance funp-necc (f (inverse f)) (p1 (cons y a)) (p2 (cons y b))))))
   :props (zfc prod2$prop inverse$prop domain$prop)
   :rule-classes nil))

(local
 (defthmz in-restrict-inv-f-implies-in-restrict-inv-g
   (implies (and (funp f) (funp g) (funp (inverse f)) (funp (inverse g))
                 (equal (restrict f (int2 (domain f) (domain g)))
                        (restrict g (int2 (domain f) (domain g))))
                 (equal (int2 (image f) (image g))
                        (image (restrict f (int2 (domain f) (domain g)))))
                 (in p (restrict (inverse f) (int2 (image f) (image g)))))
            (in p (restrict (inverse g) (int2 (image f) (image g)))))
   :hints (("Goal"
            :in-theory (enable in-int2 in-inverse)
            :use ((:instance in-image-necc
                             (x (car p)) (f (restrict f (int2 (domain f) (domain g)))))
                  (:instance preimage-unique
                             (a (cdr p))
                             (b (apply (inverse (restrict f (int2 (domain f) (domain g)))) (car p)))
                             (y (car p)) (f f))
                  (:instance restrict$comprehension
                             (p (cons (cdr p) (car p))) (f f) (s (int2 (domain f) (domain g))))
                  (:instance restrict$comprehension
                             (p (cons (cdr p) (car p))) (f g) (s (int2 (domain f) (domain g))))
                  (:instance restrict$comprehension
                             (p (cons (apply (inverse (restrict f (int2 (domain f) (domain g)))) (car p))
                                      (car p)))
                             (f f) (s (int2 (domain f) (domain g)))))))
   :props (zfc prod2$prop domain$prop inverse$prop diff$prop restrict$prop)
   :rule-classes nil))

(local
 (defthmz in-restrict-inv-g-implies-in-restrict-inv-f
   (implies (and (funp f) (funp g) (funp (inverse f)) (funp (inverse g))
                 (equal (restrict f (int2 (domain f) (domain g)))
                        (restrict g (int2 (domain f) (domain g))))
                 (equal (int2 (image f) (image g))
                        (image (restrict f (int2 (domain f) (domain g)))))
                 (in p (restrict (inverse g) (int2 (image f) (image g)))))
            (in p (restrict (inverse f) (int2 (image f) (image g)))))
   :hints (("Goal"
            :in-theory (enable in-int2 in-inverse)
            :use ((:instance in-image-necc
                             (x (car p)) (f (restrict g (int2 (domain f) (domain g)))))
                  (:instance preimage-unique
                             (a (cdr p))
                             (b (apply (inverse (restrict g (int2 (domain f) (domain g)))) (car p)))
                             (y (car p)) (f g))
                  (:instance restrict$comprehension
                             (p (cons (cdr p) (car p))) (f g) (s (int2 (domain f) (domain g))))
                  (:instance restrict$comprehension
                             (p (cons (cdr p) (car p))) (f f) (s (int2 (domain f) (domain g))))
                  (:instance restrict$comprehension
                             (p (cons (apply (inverse (restrict g (int2 (domain f) (domain g)))) (car p))
                                      (car p)))
                             (f g) (s (int2 (domain f) (domain g)))))))
   :props (zfc prod2$prop domain$prop inverse$prop diff$prop restrict$prop)
   :rule-classes nil))

(local
 (defthmz inverse-restrict-agree
   (implies (and (funp f) (funp g) (funp (inverse f)) (funp (inverse g))
                 (equal (restrict f (int2 (domain f) (domain g)))
                        (restrict g (int2 (domain f) (domain g))))
                 (equal (int2 (image f) (image g))
                        (image (restrict f (int2 (domain f) (domain g))))))
            (equal (restrict (inverse f) (int2 (image f) (image g)))
                   (restrict (inverse g) (int2 (image f) (image g)))))
   :hints (("Goal"
            :in-theory (enable subset)
            :use ((:instance extensionality
                             (x (restrict (inverse f) (int2 (image f) (image g))))
                             (y (restrict (inverse g) (int2 (image f) (image g)))))
                  (:instance in-restrict-inv-f-implies-in-restrict-inv-g
                             (p (subset-witness (restrict (inverse f) (int2 (image f) (image g)))
                                                (restrict (inverse g) (int2 (image f) (image g))))))
                  (:instance in-restrict-inv-g-implies-in-restrict-inv-f
                             (p (subset-witness (restrict (inverse g) (int2 (image f) (image g)))
                                                (restrict (inverse f) (int2 (image f) (image g)))))))))
   :props (zfc prod2$prop domain$prop inverse$prop diff$prop restrict$prop)))

(defthmz bijection-union2
  (equal (bijection (union2 f g))
         (and (bijection f)
              (bijection g)
              (let ((common-domain (int2 (domain f) (domain g))))
                (and (equal (restrict f common-domain)
                            (restrict g common-domain))
                     (equal (int2 (image f) (image g))
                            (image (restrict f common-domain)))))))
  :hints (("Goal"
           :in-theory (e/d (bijection domain-inverse) (funp-union2-general-back))
           :use ((:instance funp-union2-general (f f) (g g))
                 (:instance funp-union2-general (f (inverse f)) (g (inverse g)))
                 inverse-union2
                 inverse-restrict-agree
                 subset-img-int
                 subset-int-img
                 (:instance extensionality
                            (x (int2 (image f) (image g)))
                            (y (image (restrict f (int2 (domain f) (domain g)))))))))
  :props (zfc prod2$prop inverse$prop domain$prop diff$prop restrict$prop))

;;;<<End proof by Claude, Opus 6.8 max effort, of bijection-union2.>>

;;;<<Begin proof by Claude, Opus 6.8 max effort, of inverse-compose
;;;  (original :props : (zfc prod2$prop inverse$prop compose$prop))>>

; The bijection hypotheses say exactly that f and g are injective functions
; (injective-funp and bijection have the same definition), so this is a
; corollary of inverse-compose-strong (in projects/set-theory/inverse.lisp).
(defthmz inverse-compose
; !! This should probably be moved to another book.
  (implies (and (bijection f)
                (bijection g)
                (equal (image g) (domain f)))
           (equal (inverse (compose f g))
                  (compose (inverse g) (inverse f))))
  :hints (("Goal" :use inverse-compose-strong
           :in-theory (e/d (bijection injective-funp) (inverse-compose-strong))))
  :props (zfc prod2$prop rcompose$prop compose$prop domain$prop inverse$prop))

;;;<<End proof by Claude, Opus 6.8 max effort, of inverse-compose.>>

(defthmz bijection-compose
  (implies (and (force (bijection f))
                (force (bijection g))
                (force (equal (image g) (domain f))))
           (bijection (compose f g)))
  :props (zfc prod2$prop inverse$prop compose$prop domain$prop rcompose$prop))

(in-theory (disable bijection))
