; Copyright (C) 2025, Matt Kaufmann
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; The lemmas in this book were derived from those in eval-poly-thy.lisp so as
; to provide better (and necessary) support for proofs in
; eval-poly-support.lisp.  In fact, in earlier work they were in that book.
; But by putting them in to the present book, we draw attention to how we might
; modify these generated lemmas in the future, either by changing their
; generation or by using tools to create the modified versions.

(in-package "HOL")

(include-book "eval-poly-thy")
(include-book "../acl2/lemmas")

(DEFTHM HOL{EVAL_POLY}0-alt
  (IMPLIES (AND (ALIST-SUBSETP (EVAL-POLY$HTA) HTA)
                (HPP V HTA)
                (EQUAL (HP-TYPE V) (TYP :NUM))
                (equal x (HP-NIL (TYP (:HASH :NUM :NUM))))
                (FORCE (EVAL-POLY$PROP)))
           (EQUAL (HAP* (EVAL_POLY (TYP (:ARROW* (:LIST (:HASH :NUM :NUM))
                                                 :NUM :NUM)))
                        x
                        V)
                  (HP-NUM 0)))
  :hints (("Goal"
           :use HOL{EVAL_POLY}0
           :in-theory (disable HOL{EVAL_POLY}0))))

(DEFTHM HOL{EVAL_POLY}1-alt
  (let* ((car (hp-list-car x))
         (c (hp-hash-car car))
         (e (hp-hash-cdr car))
         (r (hp-list-cdr x)))
    (IMPLIES
     (AND (ALIST-SUBSETP (EVAL-POLY$HTA) HTA)
          (force (hpp x hta))
          (force (equal (hp-type x) (TYP (:LIST (:HASH :NUM :NUM)))))
          (force (HPP V HTA))
          (force (EQUAL (HP-TYPE V) (TYP :NUM)))
          (FORCE (EVAL-POLY$PROP))
          (hp-cons-p x)
          (hp-comma-p (hp-list-car x))
          (zf::diff$prop)
          (zf::restrict$prop))
     (EQUAL (HAP* (EVAL_POLY (TYP (:ARROW* (:LIST (:HASH :NUM :NUM))
                                           :NUM :NUM)))
                  x
                  V)
            (HP+ (HP* c
                      (HAP* (EXP (TYP (:ARROW* :NUM :NUM :NUM)))
                            V E))
                 (HAP* (EVAL_POLY (TYP (:ARROW* (:LIST (:HASH :NUM :NUM))
                                                :NUM :NUM)))
                       R V)))))
  :hints (("Goal"
           :use (:instance HOL{EVAL_POLY}1
                           (c (hp-hash-car (hp-list-car x)))
                           (e (hp-hash-cdr (hp-list-car x)))
                           (r (hp-list-cdr x)))
           :in-theory (disable hol{eval_poly}1))))

(DEFTHM HOL{SUC}-alt

; This variant of HOL::HOL{SUC} forces the second and third hypotheses.
; Perhaps such hypotheses should be forced by default.

  (IMPLIES (AND (ALIST-SUBSETP (EVAL-POLY$HTA) HTA)
                (force (HPP M HTA))
                (force (EQUAL (HP-TYPE M) (TYP :NUM)))
                (FORCE (EVAL-POLY$PROP)))
           (EQUAL (HAP* (SUC (TYP (:ARROW* :NUM :NUM)))
                        M)
                  (HP+ (HP-NUM 1) M))))

(DEFTHM HOL{EXP}-alt

; Combine HOL{EXP}0 and HOL{EXP}1 for just the case that the exponent (on which
; recursion is imagined) is a symbol.

  (IMPLIES (AND (ALIST-SUBSETP (EVAL-POLY$HTA) HTA)
                (acl2::syntaxp (acl2::symbolp n))
                (HPP M HTA)
                (EQUAL (HP-TYPE M) (TYP :NUM))
                (HPP N HTA)
                (EQUAL (HP-TYPE N) (TYP :NUM))
                (FORCE (EVAL-POLY$PROP)))
           (EQUAL (HAP* (EXP (TYP (:ARROW* :NUM :NUM :NUM)))
                        m
                        n)
                  (acl2::if
                   (equal (hp-value N) 0)
                   (HP-NUM 1)
                   (HP* M
                        (HAP* (EXP (TYP (:ARROW* :NUM :NUM :NUM)))
                              M (zf::make-hp (acl2::1- (hp-value N)) :num))))))
  :hints (("Goal"
           :in-theory (disable hol{exp}0 hol{exp}1)
           :use ((:instance HOL{EXP}0
                            (hta hta)
                            (m m))
                 (:instance HOL{EXP}1
                            (hta hta)
                            (m m)
                            (n (zf::make-hp (acl2::1- (hp-value N)) :num)))))))

#!HOL
(DEFTHM HOL{SUM_POLYS}0-alt

; Modify HOL{SUM_POLYS}0 by introducing variables x and y into LHS to enable
; more matching.

  (IMPLIES (and (hp-nil-p x (typ (:hash :num :num)))
                (hp-nil-p y (typ (:hash :num :num)))
                (FORCE (EVAL-POLY$PROP)))
           (EQUAL (HAP* (SUM_POLYS (TYP (:ARROW* (:LIST (:HASH :NUM :NUM))
                                                 (:LIST (:HASH :NUM :NUM))
                                                 (:LIST (:HASH :NUM :NUM)))))
                        x
                        y)
                  (HP-NIL (TYP (:HASH :NUM :NUM)))))
  :hints (("Goal"
           :in-theory (disable HOL{SUM_POLYS}0)
           :use HOL{SUM_POLYS}0)))

#!HOL
(DEFTHM HOL{SUM_POLYS}1-alt

; Modify HOL{SUM_POLYS}1 by introducing variables x and y into LHS to enable
; more matching.

  (IMPLIES (AND (ALIST-SUBSETP (EVAL-POLY$HTA) HTA)
                (hp-nil-p x (typ (:hash :num :num)))
                (force (hpp y hta))
                (force (equal (hp-type y) (TYP (:LIST (:HASH :NUM :NUM)))))
                (FORCE (EVAL-POLY$PROP)))
           (EQUAL (HAP* (SUM_POLYS (TYP (:ARROW* (:LIST (:HASH :NUM :NUM))
                                                 (:LIST (:HASH :NUM :NUM))
                                                 (:LIST (:HASH :NUM :NUM)))))
                        x
                        y)
                  y))
  :hints (("Goal"
           :in-theory (disable HOL{SUM_POLYS}1)
           :cases ((hp-nil-p y (typ (:hash :num :num))))
           :use (HOL{SUM_POLYS}0
                 (:instance HOL{SUM_POLYS}1
                            (v6 (hp-list-car y))
                            (v7 (hp-list-cdr y)))))))

#!HOL
(DEFTHM HOL{SUM_POLYS}2-alt

; Modify HOL{SUM_POLYS}2 by introducing variables x and y into LHS to enable
; more matching.

  (IMPLIES (AND (ALIST-SUBSETP (EVAL-POLY$HTA) HTA)
                (force (hpp x hta))
                (force (equal (hp-type x) (TYP (:LIST (:HASH :NUM :NUM)))))
                (hp-nil-p y (typ (:hash :num :num)))
                (FORCE (EVAL-POLY$PROP)))
           (EQUAL (HAP* (SUM_POLYS (TYP (:ARROW* (:LIST (:HASH :NUM :NUM))
                                                 (:LIST (:HASH :NUM :NUM))
                                                 (:LIST (:HASH :NUM :NUM)))))
                        x
                        y)
                  x))
  :hints (("Goal"
           :in-theory (disable HOL{SUM_POLYS}2)
           :cases ((hp-nil-p x (typ (:hash :num :num))))
           :use (HOL{SUM_POLYS}0
                 (:instance HOL{SUM_POLYS}2
                            (v2 (hp-list-car x))
                            (v3 (hp-list-cdr x)))))))
#!HOL
(DEFTHM HOL{SUM_POLYS}3-alt

; Modify HOL{SUM_POLYS}3 by introducing variables x and y into LHS to enable
; more matching.

  (let* ((car1 (hp-list-car x))
         (c1 (hp-hash-car car1))
         (e1 (hp-hash-cdr car1))
         (r1 (hp-list-cdr x))
         (car2 (hp-list-car y))
         (c2 (hp-hash-car car2))
         (e2 (hp-hash-cdr car2))
         (r2 (hp-list-cdr y)))
    (IMPLIES (AND (ALIST-SUBSETP (EVAL-POLY$HTA) HTA)
                  (force (hpp x hta))
                  (force (equal (hp-type x) (TYP (:LIST (:HASH :NUM :NUM)))))
                  (not (equal (hp-value x) 0))
                  (force (hpp y hta))
                  (force (equal (hp-type y) (TYP (:LIST (:HASH :NUM :NUM)))))
                  (not (equal (hp-value y) 0))
                  (FORCE (EVAL-POLY$PROP)))
             (EQUAL
              (HAP* (SUM_POLYS (TYP (:ARROW* (:LIST (:HASH :NUM :NUM))
                                             (:LIST (:HASH :NUM :NUM))
                                             (:LIST (:HASH :NUM :NUM)))))
                    x
                    y)
              (HAP*
               (COND (TYP (:ARROW* :BOOL (:LIST (:HASH :NUM :NUM))
                                   (:LIST (:HASH :NUM :NUM))
                                   (:LIST (:HASH :NUM :NUM)))))
               (HP= E1 E2)
               (HP-CONS (HP-COMMA (HP+ C1 C2) E1)
                        (HAP* (SUM_POLYS (TYP (:ARROW* (:LIST (:HASH :NUM :NUM))
                                                       (:LIST (:HASH :NUM :NUM))
                                                       (:LIST (:HASH :NUM :NUM)))))
                              R1 R2))
               (HAP*
                (COND (TYP (:ARROW* :BOOL (:LIST (:HASH :NUM :NUM))
                                    (:LIST (:HASH :NUM :NUM))
                                    (:LIST (:HASH :NUM :NUM)))))
                (HP< E1 E2)
                (HP-CONS (HP-COMMA C2 E2)
                         (HAP* (SUM_POLYS (TYP (:ARROW* (:LIST (:HASH :NUM :NUM))
                                                        (:LIST (:HASH :NUM :NUM))
                                                        (:LIST (:HASH :NUM :NUM)))))
                               (HP-CONS (HP-COMMA C1 E1) R1)
                               R2))
                (HP-CONS (HP-COMMA C1 E1)
                         (HAP* (SUM_POLYS (TYP (:ARROW* (:LIST (:HASH :NUM :NUM))
                                                        (:LIST (:HASH :NUM :NUM))
                                                        (:LIST (:HASH :NUM :NUM)))))
                               R1 (HP-CONS (HP-COMMA C2 E2) R2))))))))
  :hints (("Goal"
           :in-theory (disable HOL{SUM_POLYS}3)
           :use (:instance HOL{SUM_POLYS}3
                           (c1 (hp-hash-car (hp-list-car x)))
                           (e1 (hp-hash-cdr (hp-list-car x)))
                           (r1 (hp-list-cdr x))
                           (c2 (hp-hash-car (hp-list-car y)))
                           (e2 (hp-hash-cdr (hp-list-car y)))
                           (r2 (hp-list-cdr y))))))

#!hol
(DEFTHM HOL{COND} ; combines HOL{COND}0 and HOL{COND}1
  (IMPLIES (AND (ALIST-SUBSETP (EVAL-POLY$HTA) HTA)
                (force (HPP X HTA))
                (force (EQUAL (HP-TYPE X) (TYP A)))
                (force (HPP Y HTA))
                (force (EQUAL (HP-TYPE Y) (TYP A)))
                (force (hpp test hta))
                (force (equal (hp-type test) :bool))
                (FORCE (EVAL-POLY$PROP)))
           (EQUAL (HAP* (COND (TYP (:ARROW* :BOOL A A A)))
                        test
                        X Y)
                  (acl2::if (zf::hp-value test) x y)))
  :hints (("Goal"
           :in-theory #!zf(disable hta0 (:e hta0))
           :use (HOL{COND}0
                 HOL{COND}1
                 (:instance zf::hp-type-bool-cases
                            (zf::hta hta)
                            (zf::x test))))))
