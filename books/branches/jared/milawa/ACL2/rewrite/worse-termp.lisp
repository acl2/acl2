;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;           __    __        __    __                                        ;;
;;          /  \  /  \      (__)  |  |    ____   ___      __    ____         ;;
;;         /    \/    \      __   |  |   / _  |  \  \ __ /  /  / _  |        ;;
;;        /  /\    /\  \    |  |  |  |  / / | |   \  '  '  /  / / | |        ;;
;;       /  /  \__/  \  \   |  |  |  |  \ \_| |    \  /\  /   \ \_| |        ;;
;;      /__/          \__\  |__|  |__|   \____|     \/  \/     \____|        ;;
;; ~ ~~ \  ~ ~  ~_~~ ~/~ /~ | ~|~ | ~| ~ /~_ ~|~ ~  ~\  ~\~ ~  ~ ~  |~~    ~ ;;
;;  ~ ~  \~ \~ / ~\~ / ~/ ~ |~ | ~|  ~ ~/~/ | |~ ~~/ ~\/ ~~ ~ / / | |~   ~   ;;
;; ~ ~  ~ \ ~\/ ~  \~ ~/ ~~ ~__|  |~ ~  ~ \_~  ~  ~  .__~ ~\ ~\ ~_| ~  ~ ~~  ;;
;;  ~~ ~  ~\  ~ /~ ~  ~ ~  ~ __~  |  ~ ~ \~__~| ~/__~   ~\__~ ~~___~| ~ ~    ;;
;; ~  ~~ ~  \~_/  ~_~/ ~ ~ ~(__~ ~|~_| ~  ~  ~~  ~  ~ ~~    ~  ~   ~~  ~  ~  ;;
;;                                                                           ;;
;;            A   R e f l e c t i v e   P r o o f   C h e c k e r            ;;
;;                                                                           ;;
;;       Copyright (C) 2005-2009 by Jared Davis <jared@cs.utexas.edu>        ;;
;;                                                                           ;;
;; This program is free software; you can redistribute it and/or modify it   ;;
;; under the terms of the GNU General Public License as published by the     ;;
;; Free Software Foundation; either version 2 of the License, or (at your    ;;
;; option) any later version.                                                ;;
;;                                                                           ;;
;; This program is distributed in the hope that it will be useful, but       ;;
;; WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABIL-  ;;
;; ITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public      ;;
;; License for more details.                                                 ;;
;;                                                                           ;;
;; You should have received a copy of the GNU General Public License along   ;;
;; with this program (see the file COPYING); if not, write to the Free       ;;
;; Software Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA    ;;
;; 02110-1301, USA.                                                          ;;
;;                                                                           ;;
;;                                                                           ;;
;; EXTRA COPYRIGHT NOTICE.                                                   ;;
;;                                                                           ;;
;; This file is derived from type-set-b.lisp in the ACL2 3.1 sources.  I     ;;
;; have copied or adapted many of the comments verbatim, and the functions   ;;
;; have also been adapted to my system.  Of course, ACL2 is also GPL'd       ;;
;; software, so there is no impact on Milawa's license.                      ;;
;;                                                                           ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "MILAWA")
(include-book "../logic/subtermp")
(include-book "../logic/term-order")
(set-verify-guards-eagerness 2)
(set-case-split-limitations nil)
(set-well-founded-relation ord<)
(set-measure-function rank)



;; (rw.pseudo-variantp x y)
;;
;; According to ACL2's comments, this function is supposed to check that y is
;; the same as x "up to the variables".  For example:
;;
;;   (rw.pseudo-variantp '(f a) '(f (g b))) = t
;;   (rw.pseudo-variantp '(f (g b)) '(f a)) = nil
;;
;; But this is not quite what the function does.  As a special twist, it
;; doesn't allow variables to be replaced by constants.
;;
;;   (rw.pseudo-variantp '(f a) '(f '3)) = nil
;;
;; This is apparently done to ensure that rw.pseudo-variantp never returns true
;; if x is worse than y.

(defund rw.flag-pseudo-variantp (flag x y)
  (declare (xargs :guard (if (equal flag 'term)
                             (and (logic.termp x)
                                  (logic.termp y))
                           (and (equal flag 'list)
                                (logic.term-listp x)
                                (logic.term-listp y)))))
  (if (equal flag 'term)
      (cond ((logic.variablep x)
             (not (logic.constantp y)))
            ((logic.constantp x)
             (equal x y))
            ((logic.functionp x)
             (and (logic.functionp y)
                  (equal (logic.function-name x) (logic.function-name y))
                  (rw.flag-pseudo-variantp 'list (logic.function-args x) (logic.function-args y))))
            ((logic.lambdap x)
             (and (logic.lambdap y)
                  (equal (logic.lambda-formals x) (logic.lambda-formals y))
                  (equal (logic.lambda-body x) (logic.lambda-body y))
                  (rw.flag-pseudo-variantp 'list (logic.lambda-actuals x) (logic.lambda-actuals y))))
            (t nil))
    (if (and (consp x)
             (consp y))
        (and (rw.flag-pseudo-variantp 'term (car x) (car y))
             (rw.flag-pseudo-variantp 'list (cdr x) (cdr y)))
     t)))

(definlined rw.pseudo-variantp (x y)
  (declare (xargs :guard (and (logic.termp x)
                              (logic.termp y))))
  (rw.flag-pseudo-variantp 'term x y))

(definlined rw.pseudo-variant-listp (x y)
  (declare (xargs :guard (and (logic.term-listp x)
                              (logic.term-listp y))))
  (rw.flag-pseudo-variantp 'list x y))





;; (rw.worse-termp x y)
;;
;; This is a heuristic function for ancestor checking.  It is based on ACL2's
;; basic-worse-than function.  This function was redesigned in ACL2 2.6 when
;; performance problems were encountered, and we base our version on ACL2
;; 3.1's, which is really quite complex and still has potentially bad cases for
;; its performance.
;;
;; We do not implement ACL2's evg-occur and occur functions, which are based on
;; the funny idea of constants as (s (s (s 0))) and so forth.  This probably
;; won't affect much in practice, since we don't have strings, rationals,
;; negative numbers, and so forth which actually cause those issues.  Instead,
;; we just use our subterm function.

(defund rw.flag-worsep (flag x y)
  (declare (xargs :guard (cond ((or (equal flag 'worse-termp)
                                    (equal flag 'some-subterm-worse-than-or-equalp)
                                    (equal flag 'basic-worse-termp))
                                (and (logic.termp x)
                                     (logic.termp y)))

                               ((or (equal flag 'worse-than-listp)
                                    (equal flag 'some-subterm-worse-than-or-equal-listp))
                                (and (logic.term-listp x)
                                     (logic.termp y)))

                               (t ;; (or (equal flag 'some-less-ugly-than-correspondingp)
                                  ;;     (equal flag 'some-worse-than-correspondingp))
                                (and (logic.term-listp x)
                                     (logic.term-listp y))))
                  :measure (two-nats-measure (+ (rank x) (rank y))
                                             (if (equal flag 'basic-worse-termp) 1 2))))
  (cond ((equal flag 'worse-termp)
         (cond ((rw.flag-worsep 'basic-worse-termp x y)
                t)
               ((rw.pseudo-variantp x y)
                nil)
               ((logic.functionp x)
                (rw.flag-worsep 'worse-than-listp (logic.function-args x) y))
               ((logic.lambdap x)
                (rw.flag-worsep 'worse-than-listp (logic.lambda-actuals x) y))
               (t nil)))

        ((equal flag 'worse-than-listp)
         ;; "We determine whether some element of x contains a subterm that is
         ;; worse-than or equal to y.  The subterm in question may be the
         ;; element of x itself.  That is, we use ``subterm'' in the ``not
         ;; necessarily proper subterm'' sense."
         (if (consp x)
             (or (rw.flag-worsep 'some-subterm-worse-than-or-equalp (car x) y)
                 (rw.flag-worsep 'worse-than-listp (cdr x) y))
           nil))

        ((equal flag 'some-subterm-worse-than-or-equalp)
         (cond ((logic.variablep x)
                (equal x y))
               ((if (rw.pseudo-variantp x y) ; like worse-than-or-equal, below
                    (equal x y)
                  (rw.flag-worsep 'basic-worse-termp x y))
                t)
               ((logic.constantp x)
                nil)
               ((logic.functionp x)
                (rw.flag-worsep 'some-subterm-worse-than-or-equal-listp (logic.function-args x) y))
               ((logic.lambdap x)
                (rw.flag-worsep 'some-subterm-worse-than-or-equal-listp (logic.lambda-actuals x) y))
               (t nil)))

        ((equal flag 'some-subterm-worse-than-or-equal-listp)
         (if (consp x)
             (or (rw.flag-worsep 'some-subterm-worse-than-or-equalp (car x) y)
                 (rw.flag-worsep 'some-subterm-worse-than-or-equal-listp (cdr x) y))
           nil))

        ((equal flag 'basic-worse-termp)
         ;; "We say that x is basic-worse-than y if:
         ;;
         ;;   - y is a variable and x properly contains it, e.g., (F A B) is
         ;;     basic-worse-than A;
         ;;
         ;;   - y is a quote and x is either not a quote or is a bigger quote, e.g.,
         ;;     both X and '124 are basic-worse-than '17 and '(A B C D E) is worse
         ;;     than 'X; or
         ;;
         ;;   - x and y are applications of the same function and no argument of y is
         ;;     uglier than the corresponding arg of x, and some argument of x is
         ;;     worse-than the corresponding arg of y.
         ;;
         ;; The last case is illustrated by the fact that (F A B) is basic-worse-than
         ;; (F A '17), because B is worse than '17, but (F '17 B) is not
         ;; basic-worse-than (F A '17) because A is worse than '17.
         ;;
         ;; Think of y as the old goal and x as the new goal.  Do we want to cut off
         ;; backchaining?  Yes, if x is basic-worse-than y.  So would we backchain
         ;; from (F A '17) to (F '17 B)?  Yes, because even though one argument (the
         ;; second) got worse (it went from 17 to B) another argument (the first) got
         ;; better (it went from A to 17)."
         (cond ((logic.constantp x)
                ;; A constant is only worse than a smaller constant.
                (and (logic.constantp y)
                     (<< (logic.unquote y) (logic.unquote x))))
               ((logic.variablep x)
                ;; A variable is only worse than a constant.
                (logic.constantp y))
               ((logic.constantp y)
                ;; Any non-constant is worse than a constant.
                t)
               ((logic.variablep y)
                ;; A term is only worse than a variable if it properly contains
                ;; the variable.  We don't have to check equality because we
                ;; know x is not a variable already.
                (logic.subtermp y x))
               ((logic.functionp x)
                (and (logic.functionp y)
                     (equal (logic.function-name x) (logic.function-name y))
                     (not (rw.pseudo-variantp x y))
                     (let ((args-x (logic.function-args x))
                           (args-y (logic.function-args y)))
                       (and (not (rw.flag-worsep 'some-less-ugly-than-correspondingp args-x args-y))
                            (rw.flag-worsep 'some-worse-than-correspondingp args-x args-y)))))
               ((logic.lambdap x)
                (and (logic.lambdap y)
                     (equal (logic.lambda-formals x) (logic.lambda-formals y))
                     (equal (logic.lambda-body x) (logic.lambda-body y))
                     (not (rw.pseudo-variantp x y))
                     (let ((args-x (logic.lambda-actuals x))
                           (args-y (logic.lambda-actuals y)))
                       (and (not (rw.flag-worsep 'some-less-ugly-than-correspondingp args-x args-y))
                            (rw.flag-worsep 'some-worse-than-correspondingp args-x args-y)))))
               (t nil)))

        ((equal flag 'some-less-ugly-than-correspondingp)
         ;; "Is some element of y uglier than the corresponding element of x?
         ;; Technically, bi is uglier than ai if ai is atomic (a variable or
         ;; constant) and bi is not, or bi is worse-than ai."
         (and (consp x)
              (consp y)
              (or (and (or (logic.variablep (car x))
                           (logic.constantp (car x)))
                       (not (or (logic.variablep (car y))
                                (logic.constantp (car y)))))
                  (rw.flag-worsep 'worse-termp (car y) (car x))
                  (rw.flag-worsep 'some-less-ugly-than-correspondingp (cdr x) (cdr y)))))

        (t ;; some-worse-than-correspondingp
         (and (consp x)
              (consp y)
              (or (rw.flag-worsep 'worse-termp (car x) (car y))
                  (rw.flag-worsep 'some-worse-than-correspondingp (cdr x) (cdr y)))))))

(definlined rw.worse-termp (x y)
  (declare (xargs :guard (and (logic.termp x)
                              (logic.termp y))))
  (rw.flag-worsep 'worse-termp x y))

(definlined rw.worse-than-listp (x y)
  (declare (xargs :guard (and (logic.term-listp x)
                              (logic.termp y))))
  (rw.flag-worsep 'worse-than-listp x y))

(definlined rw.some-subterm-worse-than-or-equalp (x y)
  (declare (xargs :guard (and (logic.termp x)
                              (logic.termp y))))
  (rw.flag-worsep 'some-subterm-worse-than-or-equalp x y))

(definlined rw.some-subterm-worse-than-or-equal-listp (x y)
  (declare (xargs :guard (and (logic.term-listp x)
                              (logic.termp y))))
  (rw.flag-worsep 'some-subterm-worse-than-or-equal-listp x y))

(definlined rw.basic-worse-termp (x y)
  (declare (xargs :guard (and (logic.termp x)
                              (logic.termp y))))
  (rw.flag-worsep 'basic-worse-termp x y))

(definlined rw.some-less-ugly-than-correspondingp (x y)
  (declare (xargs :guard (and (logic.term-listp x)
                              (logic.term-listp y))))
  (rw.flag-worsep 'some-less-ugly-than-correspondingp x y))

(definlined rw.some-worse-than-correspondingp (x y)
  (declare (xargs :guard (and (logic.term-listp x)
                              (logic.term-listp y))))
  (rw.flag-worsep 'some-worse-than-correspondingp x y))



(definlined rw.worse-than-or-equal-termp (x y)
  (declare (xargs :guard (and (logic.termp x)
                              (logic.termp y))))
  ;; "This function is supposed to be equivalent to
  ;; (or (equal term1 term2) (worse-than term1 term2)).
  ;;
  ;; Clearly, that is equivalent to
  ;;
  ;; (if (pseudo-variantp term1 term2)
  ;;     (or (equal term1 term2) (worse-than term1 term2))
  ;;     (or (equal term1 term2) (worse-than term1 term2)))
  ;;
  ;; But if pseudo-variantp is true, then worse-than must return nil.
  ;; And if pseudo-variantp is nil, then the equal returns nil.  So we
  ;; can simplify the if above to:"
  (if (rw.pseudo-variantp x y)
      (equal x y)
    (rw.worse-termp x y)))






#|

;; Here are some comments and tests from the ACL2 sources.  My adapted
;; functions are apparently somewhat slower than ACL2's, even though I'm using
;; a 2.8 GHz Pentium D instead of a 330 MHz Pentium II.

; It turns out that without the use of pseudo-variantp in the definition of
; worse-than, below, worse-than's cost grows exponentially on pseudo-variant
; terms.  Consider the sequence of terms (f a a), (f a (f a a)), ..., and the
; corresponding sequence with variable symbol b used in place of a.  Call these
; terms a1, a2, ..., and b1, b2, ...  Then if pseudo-variantp were redefined to
; return nil, here are the real times taken to do (worse-than a1 b1),
; (worse-than a2 b2), ...  0.000, 0.000, 0.000, 0.000, 0.000, 0.000, 0.000,
; 0.020, 0.080, 0.300, 1.110, 4.230, 16.390.  This was measured on a 330 MHz
; Pentium II.

(ACL2::comp t)

(list (ACL2::time$ (rw.worse-termp '(f a a)
                                   '(f b b)))

      (ACL2::time$ (rw.worse-termp '(f a (f a a))
                                   '(f b (f b b))))

      (ACL2::time$ (rw.worse-termp '(f a (f a (f a a)))
                                   '(f b (f b (f b b)))))

      (ACL2::time$ (rw.worse-termp '(f a (f a (f a (f a a))))
                                   '(f b (f b (f b (f b b))))))

      (ACL2::time$ (rw.worse-termp '(f a (f a (f a (f a (f a a)))))
                                   '(f b (f b (f b (f b (f b b)))))))

      (ACL2::time$ (rw.worse-termp '(f a (f a (f a (f a (f a (f a a))))))
                                   '(f b (f b (f b (f b (f b (f b b))))))))

      (ACL2::time$ (rw.worse-termp '(f a (f a (f a (f a (f a (f a (f a a)))))))
                                   '(f b (f b (f b (f b (f b (f b (f b b)))))))))

      (ACL2::time$ (rw.worse-termp '(f a (f a (f a (f a (f a (f a (f a (f a a))))))))
                                   '(f b (f b (f b (f b (f b (f b (f b (f b b))))))))))

      (ACL2::time$ (rw.worse-termp '(f a (f a (f a (f a (f a (f a (f a (f a (f a a)))))))))
                                   '(f b (f b (f b (f b (f b (f b (f b (f b (f b b)))))))))))

      (ACL2::time$ (rw.worse-termp '(f a (f a (f a (f a (f a (f a (f a (f a (f a (f a a))))))))))
                                   '(f b (f b (f b (f b (f b (f b (f b (f b (f b (f b b))))))))))))

      (ACL2::time$ (rw.worse-termp '(f a (f a (f a (f a (f a (f a (f a (f a (f a (f a (f a a)))))))))))
                                   '(f b (f b (f b (f b (f b (f b (f b (f b (f b (f b (f b b)))))))))))))

      (ACL2::time$ (rw.worse-termp '(f a (f a (f a (f a (f a (f a (f a (f a (f a (f a (f a (f a a))))))))))))
                                   '(f b (f b (f b (f b (f b (f b (f b (f b (f b (f b (f b (f b b))))))))))))))

      (ACL2::time$ (rw.worse-termp '(f a (f a (f a (f a (f a (f a (f a (f a (f a (f a (f a (f a (f a a)))))))))))))
                                   '(f b (f b (f b (f b (f b (f b (f b (f b (f b (f b (f b (f b (f b b)))))))))))))))
      )

; If pseudo-variantp is defined so that instead of (not (quotep term2)) it
; insists of (variablep term2) when (variablep term1), then the following
; sequence goes exponential even though the preceding one does not.

(list (ACL2::time$ (rw.worse-termp '(f a (f a (f a (f a (f a (f a (f a (f a (f a a)))))))))
                                   '(f b (f b (f b (f b (f b (f b (f b (f b (f b b)))))))))))

      (ACL2::time$ (rw.worse-termp '(f a (f a (f a (f a (f a (f a (f a (f a (f a a)))))))))
                                   '(f b (f b (f b (f b (f b (f b (f b (f b (f b (f b b))))))))))))

      (ACL2::time$ (rw.worse-termp '(f a (f a (f a (f a (f a (f a (f a (f a (f a a)))))))))
                                   '(f b (f b (f b (f b (f b (f b (f b (f b (f b (f b (f b b)))))))))))))

      (ACL2::time$ (rw.worse-termp '(f a (f a (f a (f a (f a (f a (f a (f a (f a a)))))))))
                                   '(f b (f b (f b (f b (f b (f b (f b (f b (f b (f b (f b (f b b))))))))))))))

      (ACL2::time$ (rw.worse-termp '(f a (f a (f a (f a (f a (f a (f a (f a (f a a)))))))))
                                   '(f b (f b (f b (f b (f b (f b (f b (f b (f b (f b (f b (f b (f b b)))))))))))))))

      (ACL2::time$ (rw.worse-termp '(f a (f a (f a (f a (f a (f a (f a (f a (f a a)))))))))
                                   '(f b (f b (f b (f b (f b (f b (f b (f b (f b (f b (f b (f b (f b (f b b))))))))))))))))

      (ACL2::time$ (rw.worse-termp '(f a (f a (f a (f a (f a (f a (f a (f a (f a a)))))))))
                                   '(f b (f b (f b (f b (f b (f b (f b (f b (f b (f b (f b (f b (f b (f b (f b b)))))))))))))))))

      (ACL2::time$ (rw.worse-termp '(f a (f a (f a (f a (f a (f a (f a (f a (f a a)))))))))
                                   '(f b (f b (f b (f b (f b (f b (f b (f b (f b (f b (f b (f b (f b (f b (f b (f b b))))))))))))))))))

      (ACL2::time$ (rw.worse-termp '(f a (f a (f a (f a (f a (f a (f a (f a (f a a)))))))))
                                   '(f b (f b (f b (f b (f b (f b (f b (f b (f b (f b (f b (f b (f b (f b (f b (f b (f b b)))))))))))))))))))
      )

; With times of 0.000, 0.120, 0.250, 0.430, etc.  But with the current
; definition of pseudo-variantp, the sequence above is flat.  However, the
; sequence with the terms commuted grows exponentially, still:

(list (ACL2::time$ (rw.worse-termp '(f b (f b (f b (f b (f b (f b (f b (f b (f b b)))))))))
                                   '(f a (f a (f a (f a (f a (f a (f a (f a (f a a)))))))))))

      (ACL2::time$ (rw.worse-termp '(f b (f b (f b (f b (f b (f b (f b (f b (f b (f b b))))))))))
                                   '(f a (f a (f a (f a (f a (f a (f a (f a (f a a)))))))))))

      (ACL2::time$ (rw.worse-termp '(f b (f b (f b (f b (f b (f b (f b (f b (f b (f b (f b b)))))))))))
                                   '(f a (f a (f a (f a (f a (f a (f a (f a (f a a)))))))))))

      (ACL2::time$ (rw.worse-termp '(f b (f b (f b (f b (f b (f b (f b (f b (f b (f b (f b (f b b))))))))))))
                                   '(f a (f a (f a (f a (f a (f a (f a (f a (f a a)))))))))))

      (ACL2::time$ (rw.worse-termp '(f b (f b (f b (f b (f b (f b (f b (f b (f b (f b (f b (f b (f b b)))))))))))))
                                   '(f a (f a (f a (f a (f a (f a (f a (f a (f a a)))))))))))

      (ACL2::time$ (rw.worse-termp '(f b (f b (f b (f b (f b (f b (f b (f b (f b (f b (f b (f b (f b (f b b))))))))))))))
                                   '(f a (f a (f a (f a (f a (f a (f a (f a (f a a)))))))))))

      (ACL2::time$ (rw.worse-termp '(f b (f b (f b (f b (f b (f b (f b (f b (f b (f b (f b (f b (f b (f b (f b b)))))))))))))))
                                   '(f a (f a (f a (f a (f a (f a (f a (f a (f a a)))))))))))

      (ACL2::time$ (rw.worse-termp '(f b (f b (f b (f b (f b (f b (f b (f b (f b (f b (f b (f b (f b (f b (f b (f b b))))))))))))))))
                                   '(f a (f a (f a (f a (f a (f a (f a (f a (f a a)))))))))))

      (ACL2::time$ (rw.worse-termp '(f b (f b (f b (f b (f b (f b (f b (f b (f b (f b (f b (f b (f b (f b (f b (f b (f b b)))))))))))))))))
                                   '(f a (f a (f a (f a (f a (f a (f a (f a (f a a))))))))))))

; Real times: 0.000, 0.000, 0.010, 0.000, 0.010, 0.020, 0.040, 0.100, 0.210,
; ...


(list (ACL2::time$ (ACL2::worse-than '(f b (f b (f b (f b (f b (f b (f b (f b (f b b)))))))))
                                     '(f a (f a (f a (f a (f a (f a (f a (f a (f a a)))))))))))

      (ACL2::time$ (ACL2::worse-than '(f b (f b (f b (f b (f b (f b (f b (f b (f b (f b b))))))))))
                                     '(f a (f a (f a (f a (f a (f a (f a (f a (f a a)))))))))))

      (ACL2::time$ (ACL2::worse-than '(f b (f b (f b (f b (f b (f b (f b (f b (f b (f b (f b b)))))))))))
                                     '(f a (f a (f a (f a (f a (f a (f a (f a (f a a)))))))))))

      (ACL2::time$ (ACL2::worse-than '(f b (f b (f b (f b (f b (f b (f b (f b (f b (f b (f b (f b b))))))))))))
                                     '(f a (f a (f a (f a (f a (f a (f a (f a (f a a)))))))))))

      (ACL2::time$ (ACL2::worse-than '(f b (f b (f b (f b (f b (f b (f b (f b (f b (f b (f b (f b (f b b)))))))))))))
                                     '(f a (f a (f a (f a (f a (f a (f a (f a (f a a)))))))))))

      (ACL2::time$ (ACL2::worse-than '(f b (f b (f b (f b (f b (f b (f b (f b (f b (f b (f b (f b (f b (f b b))))))))))))))
                                     '(f a (f a (f a (f a (f a (f a (f a (f a (f a a)))))))))))

      (ACL2::time$ (ACL2::worse-than '(f b (f b (f b (f b (f b (f b (f b (f b (f b (f b (f b (f b (f b (f b (f b b)))))))))))))))
                                     '(f a (f a (f a (f a (f a (f a (f a (f a (f a a)))))))))))

      (ACL2::time$ (ACL2::worse-than '(f b (f b (f b (f b (f b (f b (f b (f b (f b (f b (f b (f b (f b (f b (f b (f b b))))))))))))))))
                                     '(f a (f a (f a (f a (f a (f a (f a (f a (f a a)))))))))))

      (ACL2::time$ (ACL2::worse-than '(f b (f b (f b (f b (f b (f b (f b (f b (f b (f b (f b (f b (f b (f b (f b (f b (f b b)))))))))))))))))
                                     '(f a (f a (f a (f a (f a (f a (f a (f a (f a a))))))))))))

|#