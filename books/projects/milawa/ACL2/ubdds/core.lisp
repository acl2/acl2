; Milawa - A Reflective Theorem Prover
; Copyright (C) 2005-2009 Kookamara LLC
;
; Contact:
;
;   Kookamara LLC
;   11410 Windermere Meadows
;   Austin, TX 78759, USA
;   http://www.kookamara.com/
;
; License: (An MIT/X11-style license)
;
;   Permission is hereby granted, free of charge, to any person obtaining a
;   copy of this software and associated documentation files (the "Software"),
;   to deal in the Software without restriction, including without limitation
;   the rights to use, copy, modify, merge, publish, distribute, sublicense,
;   and/or sell copies of the Software, and to permit persons to whom the
;   Software is furnished to do so, subject to the following conditions:
;
;   The above copyright notice and this permission notice shall be included in
;   all copies or substantial portions of the Software.
;
;   THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
;   IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
;   FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
;   AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
;   LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
;   FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
;   DEALINGS IN THE SOFTWARE.
;
; Original author: Jared Davis <jared@kookamara.com>

;; Milawa implementation of UBDDs
;;
;; This file is derived from the ACL2 UBDD library that was originally
;; developed by Warren Hunt and Bob Boyer, and later extended by Jared Davis
;; and Sol Swords.  See books/centaur/ubdds/ in an ACL2 distribution.

(in-package "MILAWA")
(include-book "../utilities/deflist")
(set-verify-guards-eagerness 2)
(set-case-split-limitations nil)
(set-well-founded-relation ord<)
(set-measure-function rank)

(definline hons (x y)
  ;; BOZO move to primitives
  (mbe :logic (cons x y)
       :exec (acl2::hons x y)))

(definline hons-equal (x y)
  ;; BOZO move to primitives
  (mbe :logic (equal x y)
       :exec (acl2::hons-equal x y)))

(definline atom (x)
  ;; BOZO move to primitives?
  (not (consp x)))


(defsection ubddp

  ;; This is similar to the :exec version of acl2::ubddp, but we take advantage
  ;; of CAR/CDR's safer Milawa definitions

  (defund ubddp (x)
    (declare (xargs :guard t))
    (cond ((equal x t) t)
          ((equal x nil) t)
          (t (let ((a (car x))
                   (d (cdr x)))
               (cond ((equal a t)
                      (cond ((equal d nil) t)
                            ((equal d t) nil)
                            (t (ubddp d))))
                     ((equal a nil)
                      (cond ((equal d nil) nil)
                            ((equal d t) t)
                            (t (ubddp d))))
                     (t (and (ubddp a) (ubddp d))))))))

  (defthm ubddp-when-not-consp
    (implies (not (consp x))
             (equal (ubddp x)
                    (or (equal x t)
                        (equal x nil))))
    :hints(("Goal" :expand (ubddp x))))

  (defthm booleanp-of-ubddp
    (booleanp (ubddp x))
    :hints(("Goal"
            :in-theory (enable (:induction ubddp))
            :expand (ubddp x))))

  (defthm ubddp-of-cons
    (equal (ubddp (cons a b))
           (and (ubddp a)
                (ubddp b)
                (or (consp a)
                    (not (equal a b)))))
    :hints(("Goal" :expand ((ubddp (cons a b)))))))


(deflist ubdd-listp (x)
  (ubddp x)
  :guard t)


(defsection ubdd.eval

  ;; This follows ACL2::eval-bdd, but is slightly simpler because we don't need
  ;; a special case for (atom values) with Milawa's safer car/cdr behavior.

  (defund ubdd.eval (x values)
    (declare (xargs :guard t))
    (if (consp x)
        (ubdd.eval (if (car values) (car x) (cdr x))
                   (cdr values))
      (if x t nil)))

  (defthm ubdd.eval-when-not-consp
    (implies (not (consp x))
             (equal (ubdd.eval x values)
                    (if x t nil)))
    :hints(("Goal" :expand (ubdd.eval x values))))

  (defthm ubdd.eval-of-nil
    (equal (ubdd.eval nil values)
           nil)
    :hints(("Goal" :expand (ubdd.eval nil values))))

  (defthm ubdd.eval-of-t
    (equal (ubdd.eval t values)
           t)
    :hints(("Goal" :expand (ubdd.eval nil values))))

  (defthm ubdd.eval-when-non-consp-values
    (implies (and (syntaxp (not (equal values ''nil)))
                  (not (consp values)))
             (equal (ubdd.eval x values)
                    (ubdd.eval x nil)))
    :hints(("Goal" :expand ((ubdd.eval x values)
                            (ubdd.eval x nil)))))

  (defthm booleanp-of-ubdd.eval
    (booleanp (ubdd.eval x values))
    :hints(("Goal"
            :expand ((ubdd.eval x values))
            :in-theory (enable (:induction ubdd.eval))
            :induct (ubdd.eval x values)))))

(defprojection
  :list (ubdd.eval-list x values)
  :element (ubdd.eval x values)
  :nil-preservingp t)



(defsection ubdd.max-depth

  (defund ubdd.max-depth (x)
    (declare (xargs :guard t))
    (if (consp x)
        (+ 1 (max (ubdd.max-depth (car x))
                  (ubdd.max-depth (cdr x))))
      0))

  (defthm ubdd.max-depth-when-not-consp
    (implies (not (consp x))
             (equal (ubdd.max-depth x)
                    0))
    :hints(("Goal" :expand (ubdd.max-depth x))))

  (defthm ubdd.max-depth-of-cons
    (equal (ubdd.max-depth (cons a b))
           (+ 1 (max (ubdd.max-depth a)
                     (ubdd.max-depth b))))
    :hints(("Goal" :expand (ubdd.max-depth (cons a b))))))



(definline ubdd.truebranch (x)
  ;; Like acl2::qcar, the true branch of a ubdd.  We generally leave this
  ;; enabled!
  (declare (xargs :guard t))
  (if (consp x) (car x) x))

(definline ubdd.falsebranch (x)
  ;; Like acl2::ubdd.falsebranch, the false branch of a ubdd.  We generally
  ;; leave this enabled!
  (declare (xargs :guard t))
  (if (consp x) (cdr x) x))



(defsection ubdd.badguy

  (defund ubdd.badguy-aux (x y)
    ;; Returns (CONS SUCCESSP VALUES)
    (declare (xargs :measure (+ (rank x) (rank y))
                    :hints(("Goal"
                            :in-theory (enable ubdd.truebranch
                                               ubdd.falsebranch)))))
    (if (or (consp x) (consp y))
        ;; At least one of them is a cons.  We descend both trees and try to
        ;; discover a path that will break their equality.
        (let* ((try1 (ubdd.badguy-aux (ubdd.truebranch x) (ubdd.truebranch y)))
               (try1-successp (car try1))
               (try1-values   (cdr try1)))
          (if try1-successp
              (cons t (cons t try1-values))
            (let* ((try2          (ubdd.badguy-aux (ubdd.falsebranch x) (ubdd.falsebranch y)))
                   (try2-successp (car try2))
                   (try2-values   (cdr try2)))
              (if try2-successp
                  (cons t (cons nil try2-values))
                (cons nil nil)))))
      ;; Otherwise, both are atoms.  If they are equal, then we have failed to
      ;; find a conflicting path.  But if they are not equal, then this path
      ;; violates their success.
      (cons (not (equal x y)) nil)))

  (defthm ubdd.badguy-aux-when-not-consps
    (implies (and (not (consp x))
                  (not (consp y)))
             (equal (ubdd.badguy-aux x y)
                    (cons (not (equal x y)) nil)))
    :hints(("Goal" :expand (ubdd.badguy-aux x y))))

  (defthmd ubdd.badguy-aux-lemma1
    (implies (and (car (ubdd.badguy-aux x y))
                  (ubddp x)
                  (ubddp y))
             (equal (equal (ubdd.eval x (cdr (ubdd.badguy-aux x y)))
                           (ubdd.eval y (cdr (ubdd.badguy-aux x y))))
                    nil))
    :hints(("Goal"
            :in-theory (enable (:induction ubdd.badguy-aux))
            :induct (ubdd.badguy-aux x y)
            :expand ((ubdd.badguy-aux x y)
                     (ubdd.badguy-aux x t)
                     (ubdd.badguy-aux x nil)
                     (ubdd.badguy-aux t y)
                     (ubdd.badguy-aux nil y)
                     (:free (bdd val1 vals)
                            (ubdd.eval bdd (cons val1 vals)))))))

  (defthmd ubdd.badguy-aux-lemma2
    (implies (and (ubddp x)
                  (ubddp y))
             (equal (car (ubdd.badguy-aux x y))
                    (not (equal x y))))
    :hints(("Goal"
            :in-theory (enable (:induction ubdd.badguy-aux))
            :induct (ubdd.badguy-aux x y)
            :expand ((ubdd.badguy-aux x y)
                     (ubdd.badguy-aux x t)
                     (ubdd.badguy-aux x nil)
                     (ubdd.badguy-aux t y)
                     (ubdd.badguy-aux nil y)))))

  (defthm ubdd.badguy-aux-lemma3
    (<= (len (cdr (ubdd.badguy-aux x y)))
        (max (ubdd.max-depth x) (ubdd.max-depth y)))
    :hints(("Goal"
            :in-theory (enable (:induction ubdd.badguy-aux))
            :induct (ubdd.badguy-aux x y)
            :expand ((ubdd.badguy-aux x y)
                     ;; not necessary, but these speed up the proof
                     (ubdd.max-depth x)
                     (ubdd.max-depth y)))))


  (defund ubdd.badguy-extend (lst n)
    (declare (xargs :guard (natp n)
                    :measure (nfix n)))
    (cond ((zp n)
           lst)
          ((consp lst)
           (cons (car lst) (ubdd.badguy-extend (cdr lst) (- n 1))))
          (t
           (cons nil (ubdd.badguy-extend lst (- n 1))))))

  (defthm ubdd.badguy-extend-when-zp
    (implies (zp n)
             (equal (ubdd.badguy-extend lst n)
                    lst))
    :hints(("Goal" :expand (ubdd.badguy-extend lst n))))

  (defthm ubdd.badguy-extend-of-cons
    (equal (ubdd.badguy-extend (cons a b) n)
           (cons a (ubdd.badguy-extend b (- n 1))))
    :hints(("Goal" :expand (ubdd.badguy-extend (cons a b) n))))

  (defthm len-of-ubdd.badguy-extend
    (equal (len (ubdd.badguy-extend lst n))
           (max (len lst) n))
    :hints(("Goal"
            :in-theory (enable (:induction ubdd.badguy-extend))
            :expand ((ubdd.badguy-extend lst n)
                     (ubdd.badguy-extend lst 1)))))

  (local (defun eval-extend-induct (x lst n)
           (declare (xargs :measure (nfix n)))
           (if (zp n)
               (cons lst x)
             (if (atom lst)
                 (list (eval-extend-induct (car x) lst (- n 1))
                       (eval-extend-induct (cdr x) lst (- n 1)))
               (list (eval-extend-induct (car x) (cdr lst) (- n 1))
                     (eval-extend-induct (cdr x) (cdr lst) (- n 1)))))))

  (defthm ubdd.eval-of-ubdd.badguy-extend
    (equal (ubdd.eval x (ubdd.badguy-extend lst n))
           (ubdd.eval x lst))
    :hints (("goal"
             :induct (eval-extend-induct x lst n)
             :expand ((ubdd.badguy-extend lst n)
                      (ubdd.eval x lst)
                      (ubdd.eval x nil)
                      (:free (x val1 vals)
                             (ubdd.eval x (cons val1 vals)))))))


  (defund ubdd.badguy (x y)
    ;; like badguy-aux except that we always know the values returned
    ;; have the max depth allowed
    (declare (xargs :guard t))
    (let* ((aux         (ubdd.badguy-aux x y))
           (different-p (car aux))
           (values      (ubdd.badguy-extend (cdr aux)
                                            (max (ubdd.max-depth x)
                                                 (ubdd.max-depth y)))))
      (cons different-p values)))

  (defthm len-of-ubdd.badguy
    (equal (len (cdr (ubdd.badguy x y)))
           (max (ubdd.max-depth x)
                (ubdd.max-depth y)))
    :hints(("Goal" :in-theory (e/d (ubdd.badguy)
                                   (ubdd.badguy-aux-lemma3))
            :use ((:instance ubdd.badguy-aux-lemma3)))))

  (defthmd ubdd.badguy-differentiates
    (implies (and (car (ubdd.badguy x y))
                  (ubddp x)
                  (ubddp y))
             (not (equal (ubdd.eval x (cdr (ubdd.badguy x y)))
                         (ubdd.eval y (cdr (ubdd.badguy x y))))))
    :hints(("Goal" :in-theory (enable ubdd.badguy
                                      ubdd.badguy-aux-lemma1))))

  (defthm car-of-ubdd.badguy
    (implies (and (ubddp x)
                  (ubddp y))
             (equal (car (ubdd.badguy x y))
                    (not (equal x y))))
    :hints(("Goal" :in-theory (enable ubdd.badguy
                                      ubdd.badguy-aux-lemma2)))))




;; [Jared]: It'd probably make sense to automate ubdd.badguy-differentiates
;; like we do in the ACL2 UBDD library, and if we get into heavy proofs about
;; UBDD operations (e.g., bddify) then we might well want to do this.  But for
;; now I'm going to just do things more manually.

(defsection ubdd.not

  (defund ubdd.not (x)
    (declare (xargs :guard t))
    (if (consp x)
        (hons (ubdd.not (car x))
              (ubdd.not (cdr x)))
      (if x nil t)))

  (defthm consp-of-ubdd.not
    (equal (consp (ubdd.not x))
           (consp x))
    :hints(("Goal"
            :in-theory (enable (:induction ubdd.not))
            :expand (ubdd.not x))))

  (defthmd lemma1-for-ubddp-of-ubdd.not
    (implies (and (not (equal a t))
                  (ubddp a))
             (iff (ubdd.not a)
                  t))
    :hints(("Goal" :expand ((ubddp a)
                            (ubdd.not a)))))

  (defthmd lemma2-for-ubddp-of-ubdd.not
    (implies (and a
                  (ubddp a))
             (equal (equal t (ubdd.not a))
                    nil))
    :hints(("Goal" :expand ((ubddp a)
                            (ubdd.not a)))))

  (defthm ubddp-of-ubdd.not
    (implies (force (ubddp x))
             (equal (ubddp (ubdd.not x))
                    t))
    :hints(("Goal"
            :in-theory (enable (:induction ubdd.not)
                               lemma1-for-ubddp-of-ubdd.not
                               lemma2-for-ubddp-of-ubdd.not)
            :expand ((ubdd.not x)))))

  (defthm ubdd.eval-of-ubdd.not
    (equal (ubdd.eval (ubdd.not x) values)
           (not (ubdd.eval x values)))
    :hints(("Goal"
            :in-theory (enable (:induction ubdd.eval))
            :expand ((ubdd.not x)
                     (ubdd.eval x values)
                     (:free (a b) (ubdd.eval (cons a b) values)))))))


(definline ubdd.cons (truebranch falsebranch)
  ;; Like acl2::qcons, builds a ubdd from the true/false branches.  We generally
  ;; leave this enabled!
  (declare (xargs :guard t))
  (if (if (equal truebranch t)
          (equal falsebranch t)
        (and (equal truebranch nil)
             (equal falsebranch nil)))
      truebranch
    (hons truebranch falsebranch)))


(defsection ubdd.ite

  ;; This is still more complex than absolutely necessary, e.g., it lets us
  ;; take advantage of UBDD.NOT where possible.  But it doesn't do quite so
  ;; much as the ACL2 Q-ITE macro to optimize the order of evaluation, etc.

  (local (in-theory (disable ubdd.eval-when-non-consp-values
                             same-length-prefixes-equal-cheap
                             not-equal-when-less
                             not-equal-when-less-two
                             car-when-memberp-of-singleton-list-cheap
                             consp-when-true-listp-cheap
                             car-when-memberp-and-not-memberp-of-cdr-cheap
                             consp-when-nonempty-subset-cheap
                             consp-when-memberp-cheap
                             cdr-when-true-listp-with-len-free-past-the-end
                             consp-of-cdr-when-memberp-not-car-cheap
                             consp-of-cdr-when-len-two-cheap
                             natp-of-len-free
                             consp-of-cdr-when-tuplep-2-cheap
                             consp-of-cdr-when-tuplep-3-cheap
                             consp-of-cdr-with-len-free
                             consp-when-natp-cheap
                             cdr-under-iff-with-len-free-in-bound
                             cdr-under-iff-when-true-listp-with-len-free)))

  (defund ubdd.ite (x y z)
    (declare (xargs :guard t))
    (if (consp x)
        (let ((y (if (hons-equal x y) t y))               ;; (IF X X Z) = (IF X T Z)
              (z (if (hons-equal x z) nil z)))            ;; (IF X Y X) = (IF X Y NIL)
          (cond
           ((hons-equal y z) y)                           ;; (IF X Y Y) = Y
           ((and (equal y t) (equal z nil)) x)            ;; (IF X T NIL) = X
           ((and (equal y nil) (equal z t)) (ubdd.not x)) ;; (IF X NIL T) = (NOT X)
           (t
            (ubdd.cons (ubdd.ite (car x)
                                 (ubdd.truebranch y)
                                 (ubdd.truebranch z))
                       (ubdd.ite (cdr x)
                                 (ubdd.falsebranch y)
                                 (ubdd.falsebranch z))))))
      (if (equal x nil)
          z
        y)))

  (defthm ubdd.ite-of-t
    (equal (ubdd.ite t x y)
           x)
    :hints(("Goal" :expand (ubdd.ite t x y))))

  (defthm ubdd.ite-of-nil
    (equal (ubdd.ite nil x y)
           y)
    :hints(("Goal" :expand (ubdd.ite nil x y))))

  (local (defun ubdd.ite-induct (x y z)
           (cond ((not x) (list x y z))
                 ((atom x) nil)
                 (t (let ((y (if (equal x y) t y))
                          (z (if (equal x z) nil z)))
                      (list (ubdd.ite-induct (car x)
                                             (ubdd.truebranch y)
                                             (ubdd.truebranch z))
                            (ubdd.ite-induct (cdr x)
                                             (ubdd.falsebranch y)
                                             (ubdd.falsebranch z))))))))

  (defthm ubddp-of-ubdd.ite
    (implies (and (force (ubddp x))
                  (force (ubddp y))
                  (force (ubddp z)))
             (equal (ubddp (ubdd.ite x y z))
                    t))
    :hints(("Goal"
            :in-theory (disable car-cdr-elim)
            :induct (ubdd.ite-induct x y z)
            :expand ((:free (y z) (ubdd.ite x y z))
                     (ubddp x)
                     (ubddp y)
                     (ubddp z)))))

  (local (defun ubdd.ite-induct-vals (x y z vals)
           (cond ((not x) (list x y z vals))
                 ((atom x) nil)
                 (t (let ((y (if (equal x y) t y))
                          (z (if (equal x z) nil z)))
                      (cond ((car vals)
                             (ubdd.ite-induct-vals (car x)
                                                   (ubdd.truebranch y)
                                                   (ubdd.truebranch z)
                                                   (cdr vals)))
                            (t
                             (ubdd.ite-induct-vals (cdr x)
                                                   (ubdd.falsebranch y)
                                                   (ubdd.falsebranch z)
                                                   (cdr vals)))))))))

  (defthm ubdd.eval-of-ubdd.ite
    (equal (ubdd.eval (ubdd.ite x y z) values)
           (if (ubdd.eval x values)
               (ubdd.eval y values)
             (ubdd.eval z values)))
    :hints(("Goal"
            :in-theory (disable car-cdr-elim)
            :do-not '(generalize fertilize eliminate-destructors)
            :induct (ubdd.ite-induct-vals x y z values)
            :expand ((:free (y z) (ubdd.ite x y z))
                     (:free (a b) (ubdd.eval (cons a b) values))
                     (ubdd.eval x values)
                     (ubdd.eval y values)
                     (ubdd.eval z values))))))

(defthm canonicalize-ubdd.not
  (implies (force (ubddp x))
           (equal (ubdd.not x)
                  (ubdd.ite x nil t)))
  :hints(("Goal"
          :use ((:instance ubdd.badguy-differentiates
                           (x (ubdd.not x))
                           (y (ubdd.ite x nil t)))))))


;; Once we get everything into a ubdd.ite form, we'll often want to apply
;; some of the simple reductions you would expect.  The order of these
;; rules is important --- to avoid loops, you want the T and NIL cases
;; to come last.

;; !!! I think we should maybe be able to get some more of these
;; hypothesis free if we change ubdd.ite around a bit so that it
;; coerces atoms into booleans.  Would performance be okay?

(defthm |(ubdd.ite x (ubdd.ite y nil t) z)|
  (implies (and (syntaxp (not (equal z ''t))) ;; Prevents loops (see next rule)
                (force (ubddp x))
                (force (ubddp y))
                (force (ubddp z)))
           (equal (ubdd.ite x (ubdd.ite y nil t) z)
                  (ubdd.ite y
                         (ubdd.ite x nil z)
                         (ubdd.ite x t z))))
  :hints(("Goal"
          :use ((:instance ubdd.badguy-differentiates
                           (x (ubdd.ite x (ubdd.ite y nil t) z))
                           (y (ubdd.ite y
                                        (ubdd.ite x nil z)
                                        (ubdd.ite x t z))))))))


(defthm |(ubdd.ite x (ubdd.ite y nil t) t)|
  ;; ACL2's loop-stopper works.
  (implies (and (force (ubddp x))
                (force (ubddp y))
                (force (ubddp z)))
           (equal (ubdd.ite x (ubdd.ite y nil t) t)
                  (ubdd.ite y (ubdd.ite x nil t) t)))
  :hints(("Goal"
          :use ((:instance ubdd.badguy-differentiates
                           (x (ubdd.ite x (ubdd.ite y nil t) t))
                           (y (ubdd.ite y (ubdd.ite x nil t) t)))))))

(defthm |(ubdd.ite (ubdd.ite a b c) x y)|
  (implies (and (force (ubddp a))
                (force (ubddp b))
                (force (ubddp c))
                (force (ubddp x))
                (force (ubddp y)))
           (equal (ubdd.ite (ubdd.ite a b c) x y)
                  (ubdd.ite a
                         (ubdd.ite b x y)
                         (ubdd.ite c x y))))
  :hints(("Goal"
          :use ((:instance ubdd.badguy-differentiates
                           (x (ubdd.ite (ubdd.ite a b c) x y))
                           (y (ubdd.ite a
                                        (ubdd.ite b x y)
                                        (ubdd.ite c x y))))))))

(defthm |(ubdd.ite x y y)|
  (equal (ubdd.ite x y y)
         y)
  :hints(("Goal" :expand (ubdd.ite x y y))))

(defthm |(ubdd.ite x x y)|
  (implies (and (force (ubddp x))
                (force (ubddp y)))
           (equal (ubdd.ite x x y)
                  (ubdd.ite x t y)))
  :hints(("Goal"
          :use ((:instance ubdd.badguy-differentiates
                           (x (ubdd.ite x x y))
                           (y (ubdd.ite x t y)))))))

(defthm |(ubdd.ite x y x)|
  (equal (ubdd.ite x y x)
         (ubdd.ite x y nil))
  :hints(("Goal" :expand ((ubdd.ite x y x)
                          (ubdd.ite x y nil)))))

(defthm |(ubdd.ite x t nil)|
  (implies (force (ubddp x))
           (equal (ubdd.ite x t nil)
                  x))
  :hints(("Goal" :expand (ubdd.ite x t nil))))

(defthm |(ubdd.ite non-nil y z)|
  (implies (and (atom x) x)
           (equal (ubdd.ite x y z)
                  y))
  :hints(("Goal" :expand (ubdd.ite x y z))))


