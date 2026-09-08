; Copyright (C) 2026, Matt Kaufmann
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

(in-package "ZF")

(include-book "../inverse")

(include-book "base")

; (shift-domain f n) adds n to each first component of f:
; {<a,b> \in (prod2 (omega) (image f)) : <a-n,b> \in f}
(zsub shift-domain (f n)        ; name, args
      x                         ; x
      (prod2 (omega) (image f)) ; s
      (and (consp x)
           (in (cons (- (car x) n) (cdr x)) f))) ; u

(defun concat-finseqs (f1 f2)
  (union2 f1 (shift-domain f2 (domain f1))))

(defthmz relation-p-shift-domain
  (relation-p (shift-domain f1 n))
  :hints (("Goal" :in-theory (enable relation-p)))
  :props (zfc prod2$prop shift-domain$prop))

(defthmz funp-shift-domain
  (implies (funp f1)
           (funp (shift-domain f1 n)))
  :hints (("Goal"
           :expand ((funp (shift-domain f1 n)))
           :in-theory (disable funp-necc)
           :use ((:instance
                  funp-necc
                  (f f1)
                  (p1 (let ((w1 (car (funp-witness (shift-domain f1 n)))))
                        (cons (+ (- n) (car w1)) (cdr w1))))
                  (p2 (let ((w1 (car (funp-witness (shift-domain f1 n))))
                            (w2 (mv-nth 1 (funp-witness (shift-domain f1 n)))))
                        (cons (+ (- n) (car w1)) (cdr w2))))))))
  :props (zfc prod2$prop shift-domain$prop))

(defthmz in-domain-shift-domain-1
  (implies (natp (domain f))
           (implies (in n (domain (shift-domain f k)))
                    (and (natp n)
                         (<= k n)
                         (< n (+ k (domain f))))))
  :hints (("Goal"
           :use ((:instance in-domain-rewrite (x n) (r (shift-domain f k)))
                 (:instance in-car-domain-alt
                            (p (cons (+ (- k) n)
                                     (apply (shift-domain f k) n)))
                            (x (+ (- k) n))
                            (r f)))
           :in-theory (e/d (natp in-natp)
                           (in-cons-apply in-car-domain in-car-domain-alt))))
  :props (zfc prod2$prop domain$prop shift-domain$prop)
  :rule-classes nil)

(defthmz in-domain-finseq
  (implies (and (funp f)
                (natp (domain f)))
           (equal (in n (domain f))
                  (and (natp n)
                       (< n (domain f)))))
  :hints (("Goal" :in-theory (enable in-natp))))

(defthmz in-domain-shift-domain-2
  (implies (and (natp (domain f))
                (natp k))
           (implies (and (natp n)
                         (<= k n)
                         (< n (+ k (domain f))))
                    (in n (domain (shift-domain f k)))))
  :hints (("Goal"
           :use ((:instance in-car-domain
                            (p (cons n (apply f (- n k))))
                            (r (shift-domain f k))))
           :in-theory (enable natp)))
  :props (zfc prod2$prop domain$prop shift-domain$prop inverse$prop)
  :rule-classes nil)

(defthmz in-domain-shift-domain
  (implies (and (funp f)
                (natp (domain f))
                (natp k))
           (equal (in n (domain (shift-domain f k)))
                  (and (natp n)
                       (<= k n)
                       (< n (+ k (domain f))))))
  :hints (("Goal" :use (in-domain-shift-domain-1 in-domain-shift-domain-2)))
  :props (zfc prod2$prop domain$prop shift-domain$prop inverse$prop))

(defthmz shift-domain-provides-disjoint-domain-lemma
  (implies (and (funp f1) (natp (domain f1))
                (funp f2) (natp (domain f2)))
           (subset (int2 (domain f1)
                         (domain (shift-domain f2 (domain f1))))
                   0))
  :hints (("Goal" :in-theory (e/d (subset) (subset-x-0))))
  :props (zfc diff$prop prod2$prop domain$prop shift-domain$prop inverse$prop))

(defthmz shift-domain-provides-disjoint-domain
  (implies (and (funp f1) (natp (domain f1))
                (funp f2) (natp (domain f2)))
           (equal (int2 (domain f1)
                        (domain (shift-domain f2 (domain f1))))
                  0))
  :hints (("Goal" :in-theory (enable extensionality)))
  :props (zfc diff$prop prod2$prop domain$prop shift-domain$prop inverse$prop))

(defthmz funp-concat-finseqs
  (implies (and (funp f1) (natp (domain f1))
                (funp f2) (natp (domain f2)))
           (funp (concat-finseqs f1 f2)))
  :props (zfc domain$prop diff$prop prod2$prop shift-domain$prop inverse$prop))

(defthmz inverse-union2
  (equal (inverse (union2 r1 r2))
         (union2 (inverse r1) (inverse r2)))
  :hints (("Goal" :in-theory (enable extensionality)))
  :props (zfc prod2$prop inverse$prop))

(defthmz image-union2
  (equal (image (union2 r1 r2))
         (union2 (image r1) (image r2)))
  :hints (("Goal" :in-theory (e/d (image) (domain-inverse))))
  :props (zfc prod2$prop inverse$prop domain$prop))

(defthmz domain-concat-finseqs
  (implies (and (natp (domain f1))
                (funp f2)
                (natp (domain f2)))
           (equal (domain (concat-finseqs f1 f2))
                  (+ (domain f1) (domain f2))))
  :hints (("Goal"
           :in-theory
           (enable in-natp concat-finseqs extensionality-rewrite subset)))
  :props (zfc domain$prop prod2$prop shift-domain$prop inverse$prop))

(defthmz natp-domain-forward
  (implies (and (in (cons x y) r)
                (relation-p r)
                (natp (domain r)))
           (natp x))
  :hints (("Goal"
           :use ((:instance in-car-domain (p (cons x y))))
           :in-theory (disable in-car-domain in-car-domain-alt)))
  :rule-classes :forward-chaining
  :props (zfc domain$prop))

(defthm arith-hack-1
  (implies (natp n)
           (equal (+ k (- k) n)
                  n)))

(defthmz image-shift-domain-1

; Proof:
; Choose x s.t. <x,y> \in f
;   :use (in-image-necc (x y) (f f))
;   so x = (apply (inverse f) y).
; Then <x+k,y> \in (shift-domain f k).
; So y \in (image (shift-domain f k)).
;   :restrict (in-image-suff (p <x+k,y>)).

  (implies (and (funp f)
                (natp (domain f))
                (natp k))
           (implies (in y (image f))
                    (in y (image (shift-domain f k)))))
  :hints (("Goal"
           :use ((:instance in-image-necc (x y) (f f)))
           :in-theory (e/d (natp) (in-image-necc))
           :restrict ((in-image-suff
                       ((p (cons (+ k (apply (inverse f) y))
                                 y))))))) 
  :props (zfc domain$prop diff$prop prod2$prop shift-domain$prop inverse$prop))

(defthmz image-shift-domain-2

; Proof:
; Choose x s.t. <x,y> \in (shift-domain f k)
;   :use (in-image-necc (x y) )
;   so x = (apply (inverse (shift-domain f k)) y).
; Then <x-k,y> \in f.
; So y \in (image f).
;   :restrict (in-image-suff (p <x-k,y>)).

  (implies (and (funp f)
                (natp (domain f))
                (natp k))
           (implies (in y (image (shift-domain f k)))
                    (in y (image f))))
  :hints (("Goal"
           :use ((:instance in-image-necc (x y) (f (shift-domain f k))))
           :in-theory (e/d (natp) (in-image-necc))
           :restrict ((in-image-suff
                       ((p (cons (+ (- k) (apply (inverse (shift-domain f k)) y))
                                 y))))))) 
  :props (zfc domain$prop diff$prop prod2$prop shift-domain$prop inverse$prop))

(defthmz image-shift-domain
  (implies (and (funp f)
                (natp (domain f))
                (natp k))
           (equal (image (shift-domain f k))
                  (image f)))
  :hints (("Goal"
           :in-theory (enable extensionality-rewrite subset)
           :use (image-shift-domain-1 image-shift-domain-2)))
  :props (zfc domain$prop diff$prop prod2$prop shift-domain$prop inverse$prop))

(defthmz image-concat-finseqs
  (implies (and (funp f1) (natp (domain f1))
                (funp f2) (natp (domain f2)))
           (equal (image (concat-finseqs f1 f2))
                  (union2 (image f1) (image f2))))
  :props (zfc domain$prop diff$prop prod2$prop shift-domain$prop inverse$prop))

(defthmz finite-union2-lemma
  (implies (and (funp f1)
                (natp (domain f1))
                (subset s1 (image f1))
                (funp f2)
                (natp (domain f2))
                (subset s2 (image f2))
                (zfc))
           (finite (union2 s1 s2)))
  :hints (("Goal" :restrict ((finite-suff ((f (concat-finseqs f1 f2)))))))
  :props (zfc domain$prop diff$prop prod2$prop shift-domain$prop inverse$prop))

(defthmz finite-union2
  (implies (and (finite s1)
                (finite s2))
           (finite (union2 s1 s2)))
  :hints (("Goal" :expand ((finite s1) (finite s2))))
  :props (zfc domain$prop diff$prop prod2$prop shift-domain$prop inverse$prop))

