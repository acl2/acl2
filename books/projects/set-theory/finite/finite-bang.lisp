; Copyright (C) 2026, Matt Kaufmann
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; This book develops an alternative to the function, finite, based on the
; existence of a bijection from a natural number onto the set rather than
; merely a surjection.  It also proves the two notions to be equivalent in
; theorem finite-is-finite!, which we leave disabled.  If one proves the
; finite! property for some term, then one can state that property for finite
; by enabling finite-is-finite! in a hint, to reduce the theorem about finite
; to the theorem already proved about finite!.

(in-package "ZF")

(include-book "base")
(include-book "../bijection")
(include-book "finite-union2")
(include-book "../utilities/defthme")
(local (include-book "../set-algebra"))

(defun-sk finite! (s)
  (exists f
    (and (bijection f)
         (natp (domain f))
         (equal s (image f)))))

(in-theory (disable finite!))

(defthmd finite!-implies-finite
  (implies (finite! s)
           (finite s))
  :hints (("Goal" :in-theory (enable finite!))))

(defun collapse-enum (f s n)

; F is a function whose restriction to n maps onto a superset of s, as in the
; definition of finite.  We return a function mapping some m <= n one-one onto
; s.

  (cond ((zp n) 0)
        ((in (apply f (1- n)) s)
         (let ((g (collapse-enum f
                                 (diff s (singleton (apply f (1- n))))
                                 (1- n))))
           (union2 g (singleton (cons (domain g) (apply f (1- n)))))))
        (t
         (collapse-enum f s (1- n)))))

(defthmdz n+1-as-union2-fold
  (implies (natp n)
           (equal (union2 n (pair n n))
                  (+ 1 n)))
  :hints (("Goal" :use n+1-as-union2)))

(theory-invariant (incompatible (:rewrite n+1-as-union2-fold)
                                (:rewrite n+1-as-union2)))

(defthmz natp-domain-collapse-enum
  (natp (domain (collapse-enum f s n)))
  :rule-classes (:type-prescription)
  :hints (("Goal" :in-theory (enable n+1-as-union2-fold)))
  :props (zfc domain$prop))

; Necessary for bijection-collapse-enum, at least:
(local (in-theory (disable diff-distributes-over-diff)))

(defthmz bijection-0
  (bijection 0)
  :hints (("Goal" :in-theory (enable bijection)))
  :props (zfc prod2$prop inverse$prop))

(in-theory (disable (:e bijection)))

(defthmz bijection-singleton
  (bijection (pair (cons x y) (cons x y)))
  :hints (("Goal" :in-theory (enable bijection funp)))
  :props (zfc prod2$prop inverse$prop))

(defthme int2-x-singleton-x
  (equal (int2 x (pair x x))
         0)
  :props (zfc diff$prop))

(encapsulate
  ()

; This proof is from claude code, effort high, Sonnet 4.6.  The input included
; the events above and a skip-proofs around the lemma image-singleton, which
; had no :hints or :props.  I have marked the two lemmas as local and wrapped
; with encapsulate.

; Here is claude's recap:

;   recap: Goal was to remove the skip-proofs wrapper on image-singleton in
;   claude.lsp. I proved it via forward/backward subset lemmas, renamed the
;   file to claude.lisp, and certified it successfully.

(local (defthmz image-singleton-forward
         (implies (in elt (image (pair (cons x y) (cons x y))))
                  (in elt (pair y y)))
         :hints (("Goal"
                  :in-theory (e/d (in-pair) (in-image-necc))
                  :use (:instance in-image-necc
                                  (x elt)
                                  (f (pair (cons x y) (cons x y))))))
         :props (zfc prod2$prop inverse$prop domain$prop)))

(local (defthmz image-singleton-backward
         (implies (in elt (pair y y))
                  (in elt (image (pair (cons x y) (cons x y)))))
         :hints (("Goal"
                  :in-theory (enable in-pair)
                  :use (:instance in-image-suff
                                  (p (cons x y))
                                  (r (pair (cons x y) (cons x y)))
                                  (y elt))))
         :props (zfc prod2$prop inverse$prop domain$prop)))

(defthmz image-singleton
  (equal (image (pair (cons x y) (cons x y)))
         (pair y y))
  :hints (("Goal"
           :in-theory (union-theories '(extensionality
                                        image-singleton-forward
                                        image-singleton-backward)
                                      (theory 'minimal-theory))
           :expand ((subset (image (pair (cons x y) (cons x y))) (pair y y))
                    (subset (pair y y) (image (pair (cons x y) (cons x y)))))))
  :props (zfc prod2$prop inverse$prop domain$prop))
)

(defthme int2-diff-x-y-y
  (equal (int2 (diff x y) y)
         0)
  :props (zfc diff$prop))

;;;<<Begin proof by Claude, Opus 6.8 max effort, of bijection-collapse-enum-1
;;;  and bijection-collapse-enum-2.  In each of those, Claude added the
;;;  hypothesis (not (zp n)).>>

; Supporting lemmas for bijection-collapse-enum-1 and bijection-collapse-enum-2.
; The key fact is that restricting f to a natural number n (= {0,...,n-1})
; produces, in its image, exactly one more value than restricting to n-1,
; namely (apply f (+ -1 n)); see image-restrict-plus1.

; (restrict f s) distributes over a union of index sets.
(defthmz restrict-union2-sets-1
  (subset (restrict f (union2 a b))
          (union2 (restrict f a) (restrict f b)))
  :hints (("Goal" :in-theory (enable subset)))
  :props (zfc restrict$prop)
  :rule-classes nil)

(defthmz restrict-union2-sets-2
  (subset (union2 (restrict f a) (restrict f b))
          (restrict f (union2 a b)))
  :hints (("Goal" :in-theory (enable subset)))
  :props (zfc restrict$prop)
  :rule-classes nil)

(defthmz restrict-union2-sets
  (equal (restrict f (union2 a b))
         (union2 (restrict f a) (restrict f b)))
  :hints (("Goal" :use (restrict-union2-sets-1 restrict-union2-sets-2
                        (:instance extensionality
                                   (x (restrict f (union2 a b)))
                                   (y (union2 (restrict f a) (restrict f b)))))))
  :props (zfc restrict$prop))

; A member of (restrict f {m}), when f is a function and m is in its domain, is
; the pair <m, (apply f m)>.
(defthmz in-restrict-singleton-implies
  (implies (and (funp f) (in p (restrict f (pair m m))))
           (equal p (cons m (apply f m))))
  :hints (("Goal"
           :in-theory (e/d (restrict$comprehension in-pair) (in-cons-apply))
           :use ((:instance apply-car-is-cdr (p p)))))
  :props (zfc restrict$prop domain$prop)
  :rule-classes nil)

(defthmz restrict-singleton-is-pair
  (implies (and (funp f) (in m (domain f)))
           (equal (restrict f (pair m m))
                  (pair (cons m (apply f m)) (cons m (apply f m)))))
  :hints (("Goal"
           :in-theory (e/d (subset restrict$comprehension in-pair) (in-cons-apply))
           :use ((:instance extensionality
                            (x (restrict f (pair m m)))
                            (y (pair (cons m (apply f m)) (cons m (apply f m)))))
                 (:instance in-restrict-singleton-implies
                            (p (subset-witness (restrict f (pair m m))
                                               (pair (cons m (apply f m))
                                                     (cons m (apply f m))))))
                 (:instance in-cons-apply (x m)))))
  :props (zfc prod2$prop diff$prop restrict$prop domain$prop inverse$prop))

(defthmz image-restrict-singleton
  (implies (and (funp f) (in m (domain f)))
           (equal (image (restrict f (pair m m)))
                  (pair (apply f m) (apply f m))))
  :hints (("Goal" :in-theory (enable restrict-singleton-is-pair)))
  :props (zfc prod2$prop diff$prop restrict$prop domain$prop inverse$prop))

; (restrict f (+ 1 m)) adds the single index m to (restrict f m).
(defthmz restrict-plus1
  (implies (natp m)
           (equal (restrict f (+ 1 m))
                  (union2 (restrict f m) (restrict f (pair m m)))))
  :hints (("Goal" :use ((:instance n+1-as-union2 (n m))
                        (:instance restrict-union2-sets (a m) (b (pair m m))))))
  :props (zfc restrict$prop))

; KEY: the image of (restrict f (+ 1 m)) is that of (restrict f m) together with
; the single new value (apply f m).
(defthmz image-restrict-plus1
  (implies (and (funp f) (natp m) (in m (domain f)))
           (equal (image (restrict f (+ 1 m)))
                  (union2 (image (restrict f m))
                          (pair (apply f m) (apply f m)))))
  :hints (("Goal" :in-theory (enable restrict-plus1)))
  :props (zfc prod2$prop diff$prop restrict$prop domain$prop inverse$prop))

; Two set facts: s is contained in (union2 a {b}) iff (s minus {b}) is contained
; in a; and, when b is not in s, iff s is contained in a.
(defthmz subset-diff-singleton-iff-1
  (implies (subset s (union2 a (pair b b)))
           (subset (diff s (pair b b)) a))
  :hints (("Goal"
           :in-theory (enable subset in-union2 in-pair in-diff)
           :use ((:instance subset-preserves-in-1
                            (a (subset-witness (diff s (pair b b)) a))
                            (x s)
                            (y (union2 a (pair b b)))))))
  :props (zfc diff$prop)
  :rule-classes nil)

(defthmz subset-diff-singleton-iff-2
  (implies (subset (diff s (pair b b)) a)
           (subset s (union2 a (pair b b))))
  :hints (("Goal"
           :in-theory (enable subset in-union2 in-pair in-diff)
           :use ((:instance subset-preserves-in-1
                            (a (subset-witness s (union2 a (pair b b))))
                            (x (diff s (pair b b)))
                            (y a)))))
  :props (zfc diff$prop)
  :rule-classes nil)

; Matt K. mod (changing Claude's contribution): I'm making the following lemma
; local because it caused the proof to fail for lemma
; hp-cons-hp-list-car-hp-list-cdr-lemma-1-1 in community book
; projects/hol-in-acl2/acl2/hol.lisp.
(local
(defthmz subset-diff-singleton-iff
  (equal (subset s (union2 a (pair b b)))
         (subset (diff s (pair b b)) a))
  :hints (("Goal" :use (subset-diff-singleton-iff-1 subset-diff-singleton-iff-2)))
  :props (zfc diff$prop))
)

(defthmz subset-union2-singleton-not-in
  (implies (not (in b s))
           (equal (subset s (union2 a (pair b b)))
                  (subset s a)))
  :hints (("Goal"
           :in-theory (enable subset in-union2 in-pair)
           :use ((:instance subset-preserves-in-1
                            (a (subset-witness s a))
                            (x s) (y (union2 a (pair b b))))
                 (:instance subset-preserves-in-1
                            (a (subset-witness s (union2 a (pair b b))))
                            (x s) (y a)))))
  :props (zfc))

; The (not (zp n)) hypothesis on this lemma and the next is necessary.  These
; lemmas are intended for the recursive "predecessor" case, where (+ -1 n) is the
; natural number n-1.  But at n=0 the term (+ -1 n) is -1, which is not a natural
; number, and the two sides come apart.  For example, with f = 0 and s = (pair 0
; 0): the left side is (subset (diff (pair 0 0) (pair 0 0)) (image (restrict 0
; -1))) = (subset 0 0) = t, while the right side is (subset (pair 0 0) (image
; (restrict 0 0))) = (subset (pair 0 0) 0) = nil.  Since the collapse-enum
; inductions apply these rules only in the recursive (not (zp n)) case, the added
; hypothesis is harmless downstream.
(defthmz bijection-collapse-enum-1
  (implies (and (funp f)
                (subset n (domain f))
                (natp n)
                (not (zp n)))
           (equal (subset (diff s
                                (pair (apply f (+ -1 n))
                                      (apply f (+ -1 n))))
                          (image (restrict f (+ -1 n))))
                  (subset s (image (restrict f n)))))
  :hints (("Goal"
           :in-theory (enable subset-diff-singleton-iff in-natp)
           :use ((:instance image-restrict-plus1 (m (+ -1 n))))))
  :props (zfc prod2$prop diff$prop restrict$prop domain$prop diff$prop
              inverse$prop))

(defthmz bijection-collapse-enum-2
  (implies (and (funp f)
                (subset n (domain f))
                (natp n)
                (not (zp n))
                (not (in (apply f (+ -1 n)) s)))
           (equal (subset s (image (restrict f (+ -1 n))))
                  (subset s (image (restrict f n)))))
  :hints (("Goal"
           :in-theory (enable subset-union2-singleton-not-in in-natp)
           :use ((:instance image-restrict-plus1 (m (+ -1 n))))))
  :props (zfc prod2$prop diff$prop restrict$prop domain$prop
              inverse$prop))

;;;<<End proof by Claude, Opus 6.8 max effort, of bijection-collapse-enum-1
;;;  and bijection-collapse-enum-2.>>

(defthme union2-diff-singleton
  (implies (in x s)
           (equal (union2 (pair x x)
                          (diff s (pair x x)))
                  s))
  :props (zfc diff$prop))

(defthmz image-collapse-enum
  (implies (and (funp f)
                (case-split (subset s (image (restrict f n))))
                (natp n)
                (subset n (domain f)))
           (equal (image (collapse-enum f s n))
                  s))
  :hints (("Goal"
           :restrict ((subset-transitivity ((y n))))))
  :props (zfc prod2$prop diff$prop restrict$prop domain$prop diff$prop
              inverse$prop))

(defthmz bijection-collapse-enum
  (implies (and (funp f)
                (subset n (domain f))
                (natp n)
                (subset s (image (restrict f n))))
           (bijection (collapse-enum f s n)))
  :hints (("Goal"
           :induct (collapse-enum f s n)
           :restrict ((subset-transitivity
                       ((y n))))))
  :props (zfc prod2$prop diff$prop restrict$prop domain$prop
              inverse$prop))

(defthmdz finite-implies-finite!
  (implies (finite s)
           (finite! s))
  :hints (("Goal"
           :expand ((finite s))
           :restrict
           ((finite!-suff
             ((f (collapse-enum (finite-witness s)
                                s
                                (domain (finite-witness s)))))))))
  :props (zfc prod2$prop diff$prop restrict$prop domain$prop
              inverse$prop))

(defthmdz finite-is-finite!
  (equal (finite s)
         (finite! s))
  :hints (("Goal" :use (finite-implies-finite!
                        finite!-implies-finite)))
  :props (zfc prod2$prop diff$prop restrict$prop domain$prop
              inverse$prop))
