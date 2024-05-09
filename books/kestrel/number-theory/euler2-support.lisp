; Number Theory Library
; Quadratic Residue
;
; Copyright (C) 2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric McCarthy (mccarthy@kestrel.edu)
;
; NOTE: DRAFT

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(local (include-book "arithmetic-5/top" :dir :system))

;; Thanks to David Russinoff for the proof of Euler's Criterion
(include-book "projects/numbers/support/euler" :dir :system)

(local (in-theory (disable acl2::floor-mod-elim acl2::mod-theorem-one-b)))


;; Some theorems to make it easier to prove that a given field element
;; has or does not have a square root.
;; See quadratic-residue.lisp

(defthmd euler-criterion-2a
    (implies (and (dm::primep p)
                  (not (= p 2))
                  (integerp m)
                  (not (dm::divides p m))
                  (dm::residue m p))
             (equal (mod (expt m (/ (1- p) 2)) p)
                    1))
  :hints (("Goal" :in-theory (disable dm::p-1-even)
                  :use ((:instance dm::euler-lemma (m m) (p p))
                        (:instance dm::p-1-even (p p))
                        (:instance dm::wilson (p p))
                        (:instance rtl::mod-times-mod
                                   (a (- (expt m (/ (1- p) 2)))) (b -1) (c -1) (n p))))))


(defthmd euler-criterion-2b
    (implies (and (dm::primep p)
                  (not (= p 2))
                  (integerp m)
                  (not (dm::divides p m))
                  (not (dm::residue m p)))
             (equal (mod (expt m (/ (1- p) 2)) p)
                    (1- p)))
  :hints (("Goal" :in-theory (disable dm::p-1-even)
                  :use ((:instance dm::euler-lemma (m m) (p p))
                        (:instance dm::p-1-even (p p))
                        (:instance dm::wilson (p p))
                        (:instance rtl::mod-times-mod
                                   (a (- (expt m (/ (1- p) 2)))) (b -1) (c -1) (n p))))))
