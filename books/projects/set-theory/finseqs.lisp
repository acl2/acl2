; Copyright (C) 2025, Matt Kaufmann
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

(in-package "ZF")

(include-book "fun-space")
(include-book "set-algebra")
(include-book "restrict")
(include-book "ordinals")

(zsub finseqs (s)                  ; name, args
      fn                           ; x
      (powerset (prod2 (omega) s)) ; s
      (and (funp fn)
           (in (domain fn) (omega)))
      )

(local (defthmz in-finseqs-lemma
         (implies (and (funp fn)
                       (natp (domain fn))
                       (subset (image fn) a))
                  (subset fn (prod2 (omega) a)))
         :props (zfc prod2$prop domain$prop inverse$prop finseqs$prop)
         :hints (("Goal"
                  :restrict
                  ((subset-transitivity
                    ((y (prod2 (domain fn) (image fn))))))))))

(local (defthm iff-implies-equal
         (implies (and (booleanp x) (booleanp y))
                  (equal (equal x y)
                         (iff x y)))))

(defthmz in-finseqs ; alternate form of finseqs$comprehension
  (equal (in fn (finseqs a))
         (and (funp fn)
              (in (domain fn) (omega))
              (subset (image fn) a)))
  :props (zfc prod2$prop domain$prop inverse$prop finseqs$prop))

; The next several events resulted from attempts to prove theorems in community
; book projects/hol-in-acl2/examples/eval-poly-support.lisp.

(defthmz finseq-admit
  (implies (and (funp fn)
                (natp (domain fn))
                (not (equal fn 0)))
           (< (int2 (domain fn) (+ -1 (domain fn)))
              (domain fn)))
  :props (zfc domain$prop diff$prop)
  :hints (("Goal" :use ((:instance int2-predecessor-natp (n (domain fn)))))))

(defun finseq-to-list (fn)

; This is not entirely general, since fn need only be in (finseqs (prod2
; (omega) s)) for some s.  But it's sufficient for our purposes.

  (declare (xargs :guard (and (in fn (finseqs (prod2 (omega) (omega))))
                              (zfc)
                              (prod2$prop)
                              (domain$prop)
                              (inverse$prop)
                              (restrict$prop)
                              (diff$prop)
                              (finseqs$prop))
                  :guard-hints (("Goal"
                                 :restrict
                                 ((subset-transitivity
                                   ((y (image fn)))))))
                  :measure (if (and (in fn (finseqs (prod2 (omega) (omega))))
                                    (zfc)
                                    (prod2$prop)
                                    (domain$prop)
                                    (inverse$prop)
                                    (restrict$prop)
                                    (diff$prop)
                                    (finseqs$prop))
                               (domain fn)
                             0)))
  (cond ((not (mbt (and (in fn (finseqs (prod2 (omega) (omega))))
                        (zfc)
                        (prod2$prop)
                        (domain$prop)
                        (inverse$prop)
                        (restrict$prop)
                        (diff$prop)
                        (finseqs$prop)
                        t)))
         :fail)
        ((eql fn 0)
         nil)
        (t (let ((n (1- (domain fn))))
             (cons (apply fn n)
                   (finseq-to-list (restrict fn n)))))))

(in-theory (disable (:e finseq-to-list)))

(defthmz consp-finseq-to-list-type-prescription
  (implies (and (funp fn)
                (natp (domain fn))
                (not (equal fn 0))
                (subset (image fn)
                        (prod2 (omega) (omega))))
           (consp (finseq-to-list fn)))
  :props (zfc prod2$prop domain$prop inverse$prop restrict$prop diff$prop
              finseqs$prop)
  :hints (("Goal" :expand ((finseq-to-list fn))))
  :rule-classes :type-prescription)

(defthmz last-finseq-type

; This could be generalized to (prod2 s1 s2), to conclude membership, for the
; car and cdr in the conclusion, in s1 and s2 respectively.

  (implies (and (funp fn)
                (natp (domain fn))
                (not (equal fn 0))
                (subset (image fn) (prod2 (omega) (omega))))
           (and (consp (apply fn
                              (+ -1 (domain fn))))
                (natp (car (apply fn
                                  (+ -1 (domain fn)))))
                (natp (cdr (apply fn
                                  (+ -1 (domain fn)))))))
  :hints (("Goal"
           :in-theory (e/d (in-natp)
                           (in-apply-image in-apply-image-force))
           :use ((:instance in-apply-image (r fn)
                            (x (+ -1 (domain fn)))))))
  :props (zfc domain$prop prod2$prop inverse$prop))

(defthmz natp-finseq-cdr
  (implies (and (natp (domain fn))
                (funp fn)
                (not (subset fn 0)))
           (natp (1- (domain fn))))
  :props (zfc domain$prop)
  :rule-classes :forward-chaining)

(local (defthmz in-n-minus-1
         (implies (and (natp n)
                       (in a n)
                       (not (equal a (1- n))))
                  (in a (1- n)))
         :hints (("Goal"
                  :in-theory
                  (e/d (in-natp)
                       (ordinal-proper-subset-is-element))))))

(defthmz finseq-fold-1-1
  (implies (and (funp fn)
                (natp (domain fn))
                (not (in (car p) (+ -1 (domain fn))))
                (in p fn))
           (equal (cons (+ -1 (domain fn))
                        (apply fn (+ -1 (domain fn))))
                  p))
  :props (zfc domain$prop))

(defthmz finseq-fold-1
  (implies (and (funp fn)
                (natp (domain fn))
                (not (subset fn 0))
                (in p fn))
           (in p
               (union2 (restrict fn (+ -1 (domain fn)))
                       (pair (cons (+ -1 (domain fn))
                                   (apply fn (+ -1 (domain fn))))
                             (cons (+ -1 (domain fn))
                                   (apply fn (+ -1 (domain fn))))))))
  :props (zfc domain$prop restrict$prop))

(defthmz finseq-fold
  (implies (and (funp fn)
                (natp (domain fn))
                (not (equal fn 0)))
           (equal (union2 (restrict fn
                                    (+ -1 (domain fn)))
                          (pair (cons (+ -1 (domain fn))
                                      (apply fn (+ -1 (domain fn))))
                                (cons (+ -1 (domain fn))
                                      (apply fn
                                             (+ -1 (domain fn))))))
                  fn))
  :instructions ((:in-theory (e/d (extensionality-rewrite in-natp)
                                  (subset-x-0 ordinal-proper-subset-is-element)))
                 :bash (:rewrite subset-criterion)
                 :promote (:rewrite finseq-fold-1))
  :props (zfc domain$prop restrict$prop))
