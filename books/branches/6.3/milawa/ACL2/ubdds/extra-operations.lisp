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
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Milawa implementation of UBDDs
;;
;; This file is derived from the ACL2 UBDD library that was originally
;; developed by Warren Hunt and Bob Boyer, and later extended by Jared Davis
;; and Sol Swords.  See books/centaur/ubdds/ in an ACL2 distribution.

(in-package "MILAWA")
(include-book "core")
(set-verify-guards-eagerness 2)
(set-case-split-limitations nil)
(set-well-founded-relation ord<)
(set-measure-function rank)

; Note: for simplicity I don't reimplement the fancy opportunistic laziness
; stuff that the ACL2 BDD library uses.  Milawa's UBDD.AND is just a function,
; and both arguments get evaluated.

(local (defun ubdd.binop-induct (x y vals)
         (cond ((atom x)
                (list x y vals))
               ((atom y)
                nil)
               ((car vals)
                (ubdd.binop-induct (car x) (car y) (cdr vals)))
               (t
                (ubdd.binop-induct (cdr x) (cdr y) (cdr vals))))))

(defsection ubdd.and

  (defund ubdd.and (x y)
    (declare (xargs :guard t))
    (cond ((atom x)
           (if x
               ;; [Jared hack]: normalize in the atom case for fewer hyps
               (if (atom y)
                   (if y t nil)
                 y)
             nil))
          ((atom y)
           ;; We know x is not an atom, so no need to normalize
           (if y x nil))
          ((hons-equal x y)
           x)
          (t
           (ubdd.cons (ubdd.and (car x) (car y))
                      (ubdd.and (cdr x) (cdr y))))))

  (defthm ubdd.and-of-nil-left
    (equal (ubdd.and nil x) nil)
    :hints(("Goal" :expand (ubdd.and nil x))))

  (defthm ubdd.and-of-nil-right
    (equal (ubdd.and x nil) nil)
    :hints(("Goal" :expand (ubdd.and x nil))))

  (defthm ubdd.and-of-t-left-slow
    (equal (ubdd.and t x) (if (consp x) x (if x t nil)))
    :hints(("Goal" :expand (ubdd.and t x))))

  (defthm ubdd.and-of-t-right-slow
    (equal (ubdd.and x t) (if (consp x) x (if x t nil)))
    :hints(("Goal" :expand (ubdd.and x t))))

  (defthm ubdd.and-of-self-slow
    (equal (ubdd.and x x) (if (consp x) x (if x t nil)))
    :hints(("Goal" :expand (ubdd.and x x))))

  (defthm ubddp-of-ubdd.and
    (implies (and (force (ubddp x))
                  (force (ubddp y)))
             (equal (ubddp (ubdd.and x y))
                    t))
    :hints(("Goal"
            :in-theory (enable (:induction ubdd.and))
            :expand ((ubdd.and x y)))))

  (defthm ubdd.eval-of-ubdd.and
    (equal (ubdd.eval (ubdd.and x y) values)
           (and (ubdd.eval x values)
                (ubdd.eval y values)))
    :hints(("Goal"
            :induct (ubdd.binop-induct x y values)
            :expand ((ubdd.and x y)
                     (ubdd.eval x values)
                     (ubdd.eval y values)
                     (:free (a b) (ubdd.eval (cons a b) values))))))

  (defthm ubdd.and-symmetric
    (equal (ubdd.and x y)
           (ubdd.and y x))
    :hints(("Goal"
            :in-theory (enable (:induction ubdd.and))
            :expand ((ubdd.and x y)
                     (ubdd.and y x)))))

  (defthm canonicalize-ubdd.and
    (implies (and (force (ubddp x))
                  (force (ubddp y)))
             (equal (ubdd.and x y)
                    (ubdd.ite x y nil)))
    :hints(("Goal" :use ((:instance ubdd.badguy-differentiates
                                    (x (ubdd.and x y))
                                    (y (ubdd.ite x y nil)))))))

  (defthm ubdd.and-of-t-left-aggressive
    (implies (force (ubddp x))
             (equal (ubdd.and t x) x)))

  (defthm ubdd.and-of-t-right-aggressive
    (implies (force (ubddp x))
             (equal (ubdd.and x t) x)))

  (defthm ubdd.and-of-self-aggressive
    (implies (force (ubddp x))
             (equal (ubdd.and x x) x))))



(defsection ubdd.or

  (defund ubdd.or (x y)
    (declare (xargs :guard t))
    (cond ((atom x)
           (if x
               t
             ;; [Jared hack]: normalize atoms
             (if (atom y) (if y t nil) y)))
          ((atom y)
           ;; We know x is not an atom, so no need to normalize.
           (if y t x))
          ((hons-equal x y)
           x)
          (t
           (let ((l (ubdd.or (car x) (car y)))
                 (r (ubdd.or (cdr x) (cdr y))))
             (ubdd.cons l r)))))

  (defthm ubdd.or-of-nil-left-slow
    (equal (ubdd.or nil x) (if (consp x) x (if x t nil)))
    :hints(("Goal" :expand (ubdd.or nil x))))

  (defthm ubdd.or-of-nil-right-slow
    (equal (ubdd.or x nil) (if (consp x) x (if x t nil)))
    :hints(("Goal" :expand (ubdd.or x nil))))

  (defthm ubdd.or-of-t-left
    (equal (ubdd.or t x) t)
    :hints(("Goal" :expand (ubdd.or t x))))

  (defthm ubdd.or-of-t-right
    (equal (ubdd.or x t) t)
    :hints(("Goal" :expand (ubdd.or x t))))

  (defthm ubdd.or-of-self-slow
    (equal (ubdd.or x x)
           (if (consp x) x (if x t nil)))
    :hints(("Goal" :expand (ubdd.or x x))))

  (defthm ubddp-of-ubdd.or
    (implies (and (force (ubddp x))
                  (force (ubddp y)))
             (equal (ubddp (ubdd.or x y))
                    t))
    :hints(("Goal"
            :induct (ubdd.or x y)
            :in-theory (enable (:induction ubdd.or))
            :expand ((ubdd.or x y)))))

  (defthm ubdd.eval-of-ubdd.or
    (equal (ubdd.eval (ubdd.or x y) values)
           (or (ubdd.eval x values)
               (ubdd.eval y values)))
    :hints(("Goal"
            :induct (ubdd.binop-induct x y values)
            :expand ((ubdd.or x y)
                     (ubdd.eval x values)
                     (ubdd.eval y values)
                     (:free (a b) (ubdd.eval (cons a b) values))))))

  (defthm ubdd.or-symmetric
    (equal (ubdd.or x y)
           (ubdd.or y x))
    :hints(("Goal"
            :induct (ubdd.or x y)
            :in-theory (enable (:induction ubdd.or))
            :expand ((ubdd.or x y)
                     (ubdd.or y x)))))

  (defthm canonicalize-ubdd.or
    (implies (and (force (ubddp x))
                  (force (ubddp y)))
             (equal (ubdd.or x y)
                    (ubdd.ite x t y)))
    :hints(("Goal" :use ((:instance ubdd.badguy-differentiates
                                    (x (ubdd.or x y))
                                    (y (ubdd.ite x t y)))))))

  (defthm ubdd.or-of-nil-left-aggressive
    (implies (force (ubddp x))
             (equal (ubdd.or nil x) x))
    :hints(("Goal" :use ((:instance ubdd.badguy-differentiates
                                    (x (ubdd.or nil x))
                                    (y x))))))

  (defthm ubdd.or-of-nil-right-aggressive
    (implies (force (ubddp x))
             (equal (ubdd.or x nil) x))
    :hints(("Goal" :use ((:instance ubdd.badguy-differentiates
                                    (x (ubdd.or x nil))
                                    (y x))))))

  (defthm ubdd.or-of-self-aggressive
    (implies (force (ubddp x))
             (equal (ubdd.or x x) x))
    :hints(("Goal" :use ((:instance ubdd.badguy-differentiates
                                    (x (ubdd.or x x))
                                    (y x)))))))



; BOZO.  The ACL2 ubdd library currently has q-implies, q-or-c2, q-and-c1,
; etc., as a custom, recursive functions.  But I think it's probably better to
; implement these as wrappers.  After all, we generally expect ubdd.not to be
; free, so wouldn't it be better to tap into the ubdd.or memo table?  I should
; try this at Centaur and see how performance compares, but we probably don't
; use implies enough to matter.

(definline ubdd.implies (x y)
  (declare (xargs :guard t))
  (ubdd.or (ubdd.not x) y))

(definline ubdd.or-c2 (x y)
  (declare (xargs :guard t))
  (ubdd.or x (ubdd.not y)))

(definline ubdd.and-c1 (x y)
  (declare (xargs :guard t))
  (ubdd.and (ubdd.not x) y))

(definline ubdd.and-c2 (x y)
  (declare (xargs :guard t))
  (ubdd.and x (ubdd.not y)))



(defsection ubdd.xor

  (defund ubdd.xor (x y)
    (declare (xargs :guard t))
    (cond ((atom x)
           (if x (ubdd.not y) y))
          ((atom y)
           (if y (ubdd.not x) x))
          ((hons-equal x y)
           nil)
          (t
           (ubdd.cons (ubdd.xor (car x) (car y))
                      (ubdd.xor (cdr x) (cdr y))))))

  (local (in-theory (disable canonicalize-ubdd.not)))

  (defthm ubdd.xor-of-self
    (equal (ubdd.xor x x)
           nil)
    :hints(("Goal"
            :expand ((ubdd.xor x x)
                     (ubdd.not x)))))

; BOZO these t/nil rules aren't in the ACL2 ubdd library; it would probably be
; good to add them.

  (defthm ubdd.xor-of-t-left
    (equal (ubdd.xor t x)
           (ubdd.not x))
    :hints(("Goal" :expand (ubdd.xor t x))))

  (defthm ubdd.xor-of-t-right
    (equal (ubdd.xor x t)
           (ubdd.not x))
    :hints(("Goal" :expand ((ubdd.xor x t)
                            (ubdd.not x)))))

  (defthm ubdd.xor-of-nil-left
    (equal (ubdd.xor nil x)
           x)
    :hints(("Goal" :expand (ubdd.xor nil x))))

  (defthm ubdd.xor-of-nil-right-slow
    ;; bozo kind of a weird asymmetry here?
    (equal (ubdd.xor x nil)
           (if (consp x) x (if x t nil)))
    :hints(("Goal" :expand ((ubdd.xor x nil)
                            (ubdd.not x)))))

  (defthm ubddp-of-ubdd.xor
    (implies (and (force (ubddp x))
                  (force (ubddp y)))
             (equal (ubddp (ubdd.xor x y))
                    t))
    :hints(("Goal"
            :in-theory (enable (:induction ubdd.xor))
            :expand ((ubdd.xor x y)))))

  (defthm ubdd.eval-of-ubdd.xor
    (equal (ubdd.eval (ubdd.xor x y) values)
           (if (ubdd.eval x values)
               (not (ubdd.eval y values))
             (ubdd.eval y values)))
    :hints(("Goal"
            :induct (ubdd.binop-induct x y values)
            :expand ((ubdd.xor x y)
                     (ubdd.eval x values)
                     (ubdd.eval y values)
                     (:free (a b) (ubdd.eval (cons a b) values))))))

  (defthm canonicalize-ubdd.xor
    (implies (and (force (ubddp x))
                  (force (ubddp y)))
             (equal (ubdd.xor x y)
                    (ubdd.ite x (ubdd.not y) y)))
    :hints(("Goal" :use ((:instance ubdd.badguy-differentiates
                                    (x (ubdd.xor x y))
                                    (y (ubdd.ite x (ubdd.not y) y))))))))


; BOZO the ACL2 ubdd library currently has ubdd.iff as its own recursive
; function, but I suspect this wrapper aprpoach is better:

(definline ubdd.iff (x y)
  (ubdd.not (ubdd.xor x y)))

(definline ubdd.nand (x y)
  (ubdd.not (ubdd.and x y)))

(definline ubdd.nor (x y)
  (ubdd.not (ubdd.or x y)))


(defsection ubdd.var

  (defund ubdd.var (i)
    ;; Creates the (nfix i)th BDD variable.
    (declare (xargs :guard t
                    :measure (nfix i)))
    (if (zp i)
        (hons t nil)
      (let ((prev (ubdd.var (- i 1))))
        (hons prev prev))))

  (defthm ubdd.var-under-iff
    (iff (ubdd.var i)
         t)
    :hints(("Goal" :expand (ubdd.var i))))

  (defthm consp-of-ubdd.var
    (equal (consp (ubdd.var i))
           t)
    :hints(("Goal" :expand (ubdd.var i))))

  (defthm ubddp-ubdd.var
    (ubddp (ubdd.var i))
    :hints(("Goal"
            :induct (ubdd.var i)
            :in-theory (enable (:induction ubdd.var))
            :expand ((ubdd.var i)))))

  (defthm ubdd.eval-of-ubdd.var-and-nil
    (not (ubdd.eval (ubdd.var i) nil))
    :hints(("Goal"
            :in-theory (enable (:induction ubdd.var))
            :induct (ubdd.var i)
            :expand ((ubdd.var i)
                     (:free (a b) (ubdd.eval (cons a b) nil))))))

  (local (defun my-induct (i lst)
           (declare (xargs :measure (nfix i)))
           (if (zp i)
               lst
             (my-induct (- i 1) (cdr lst)))))

  (defthm ubdd.eval-of-ubdd.var
    (equal (ubdd.eval (ubdd.var i) lst)
           (if (nth i lst) t nil))
    :hints(("Goal"
            :in-theory (enable (:induction ubdd.var))
            :induct (my-induct i lst)
            :expand ((ubdd.var i)
                     (nth i lst)
                     (:free (a b) (ubdd.eval (cons a b) lst))))))

  (local (defun ubdd.vars-ind (i j)
           (declare (xargs :measure (nfix i)))
           (if (or (zp i) (zp j))
               i
             (ubdd.vars-ind (- i 1) (- j 1)))))

  (defthmd equal-of-cons-rewrite-full
    (equal (equal (cons a b) x)
           (and (consp x)
                (equal (car x) a)
                (equal (cdr x) b))))

  (defthm ubdd.vars-equal
    (equal (equal (ubdd.var i) (ubdd.var j))
           (equal (nfix i) (nfix j)))
    :hints(("Goal"
            :in-theory (enable equal-of-cons-rewrite-full)
            :induct (ubdd.vars-ind i j)
            :expand ((ubdd.var i)
                     (ubdd.var j))))))

