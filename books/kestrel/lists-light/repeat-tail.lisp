; A simple, tail-recursive version of repeat
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2019 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; STATUS: In-progress

(include-book "repeat")

;todo: compare to make-list
(defund repeat-tail (n v acc)
  (declare (type t n v acc))
  (if (if (integerp n)
          (<= n 0)
        t)
      acc
    (repeat-tail (1- n) v (cons v acc))))

(defthm car-of-repeat-tail
  (equal (car (repeat-tail n v acc))
         (if (posp n)
             v
           (car acc)))
  :hints (("Goal" :induct (repeat-tail n v acc)
           :in-theory (enable repeat-tail))))

(defthm len-of-repeat-tail
  (equal (len (repeat-tail n v acc))
         (+ (nfix n) (len acc)))
  :hints (("Goal" :in-theory (enable repeat-tail))))

(defthmd repeat-becomes-repeat-tail-helper
  (implies (natp n)
           (equal (append (repeat n v) acc)
                  (repeat-tail n v acc)))
  :hints (("Goal" :induct (repeat-tail n v acc)
           :in-theory (e/d (repeat-tail repeat-opener-end)
                           (;list::open-equiv
                            ;list::equal-append-reduction!
                            ;LIST::APPEND-REPEAT-SINGLETON-SAME ;looped
                            )))))

;to prevent repeat from executing with huge n, we use the following scheme:
;never execute repeat, but rewrite repeat on small constant arguments to repeat-tail and execute repeat-tail
(defthm repeat-becomes-repeat-tail
  (implies (and (syntaxp (and (quotep n)
                              (quotep v)))
                (< n 10000)
                (natp n))
           (equal (repeat n v)
                  (repeat-tail n v nil)))
  :hints (("Goal" :use (:instance repeat-becomes-repeat-tail-helper (acc nil)))))

(in-theory (disable (:executable-counterpart repeat)))
