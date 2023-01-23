; Tests of the R1CS formalization
;
; Copyright (C) 2019-2022 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "R1CS")

;; Tests of the R1CS formalization.

(include-book "kestrel/utilities/deftest" :dir :system)
(include-book "r1cs")
(include-book "rules")
(local (include-book "kestrel/prime-fields/bind-free-rules" :dir :system))

(acl2::deftest
  (assert-event (r1cs-constraintp (r1cs-constraint (list 0 1) ;a
                                                   (list 1 1) ;b
                                                   (list 1 0) ;c
                                                   ))))

(acl2::deftest
  (assert-event
   (good-r1cs-constraintp (r1cs-constraint (list 0 1) ;a
                                           (list 1 1) ;b
                                           (list 1 0) ;c
                                           )
                          7 ;use 7 as the prime
                          )))

(acl2::deftest
  (defconst *vitalik-r1cs*
    (r1cs
     97
     '(x1 x2 x3 x4 x5) ;not sure how to divide the vars into the 3 classes
     ;; the
     (list (r1cs-constraint '(5 0 0 0 0 1) ;a
                            '(1 0 0 0 0 0) ;b
                            '(0 0 1 0 0 0) ;c
                            ))))

  (assert-event (r1csp *vitalik-r1cs*))

  (assert-event
   (r1cs-holdsp *vitalik-r1cs*
                '((x1 . 3)
                  (x2 . 35)
                  (x3 . 9)
                  (x4 . 27)
                  (x5 . 30)))))

;; Example from https://medium.com/@VitalikButerin/quadratic-arithmetic-programs-from-zero-to-hero-f6d558cea649
(acl2::deftest
  (defconst *prime* 997) ; just pick a prime that's reasonably large

  (defconst *vitalik-r1cs-2*
    (r1cs
     *prime*
     ;; vars:
     '( ; 1 (implicit)
       x
       ~out ;; the tilde is just part of the name of this var
       sym_1
       y
       sym_2)
     (list
      ;; sym_1 = x*x:
      (r1cs-constraint '(0 1 0 0 0 0) ;a
                       '(0 1 0 0 0 0) ;b
                       '(0 0 0 1 0 0) ;c
                       )
      ;; y = sym_1 * x:
      (r1cs-constraint '(0 0 0 1 0 0) ;a
                       '(0 1 0 0 0 0) ;b
                       '(0 0 0 0 1 0) ;c
                       )
      ;; sym_2 = y + x:
      (r1cs-constraint '(0 1 0 0 1 0) ;a
                       '(1 0 0 0 0 0) ;b
                       '(0 0 0 0 0 1) ;c
                       )
      ;; ~out = sym_2 + 5:
      (r1cs-constraint '(5 0 0 0 0 1) ;a
                       '(1 0 0 0 0 0) ;b
                       '(0 0 1 0 0 0) ;c
                       ))))

  (assert-event (r1csp *vitalik-r1cs-2*))

  (assert-event
   (r1cs-holdsp *vitalik-r1cs-2*
                '((x . 3)
                  (~out . 35)
                  (sym_1 . 9)
                  (y . 27)
                  (sym_2 . 30))))

  ;; Show that the r1cs implies that ~out=x+x^3+5.
  (defthm vitalik-r1cs-correct
    (implies (and (pfield::fep x *prime*)
                  (pfield::fep ~out *prime*)
                  (pfield::fep sym_1 *prime*)
                  (pfield::fep y *prime*)
                  (pfield::fep sym_2 *prime*)
                  (r1cs-holdsp *vitalik-r1cs-2*
                               `((x . ,x)
                                 (~out . ,~out)
                                 (sym_1 . ,sym_1)
                                 (y . ,y)
                                 (sym_2 . ,sym_2))))
             (equal ~out
                    ;; x+x^3+5 :
                    (pfield::add x
                                 (pfield::add (pfield::pow x 3 *prime*)
                                              5
                                              *prime*)
                                 *prime*)))
    :rule-classes nil
    :hints (("Goal" :in-theory (enable r1cs-constraint-holdsp pfield::pow-opener))))

  ;; Show that, if x+x^3+5, then there exist values of the intermediate vars
  ;; that make the whole R1CS hold:
  (defthm vitalik-r1cs-correct-2
    (implies (and (pfield::fep x *prime*)
                  (pfield::fep ~out *prime*)
                  (equal ~out
                         ;; x+x^3+5 :
                         (pfield::add x
                                      (pfield::add (pfield::pow x 3 *prime*)
                                                   5
                                                   *prime*)
                                      *prime*)))
             (r1cs-holdsp *vitalik-r1cs-2*
                          `((x . ,x)
                            (~out . ,~out)
                            (sym_1 . ,(pfield::mul x x *prime*))
                            (y . ,(pfield::mul (pfield::mul x x *prime*) x *prime*))
                            (sym_2 . ,(pfield::add (pfield::mul (pfield::mul x x *prime*) x *prime*) x *prime*))))
             )
    :rule-classes nil
    :hints (("Goal" :in-theory (enable r1cs-constraint-holdsp pfield::pow-opener)))))
