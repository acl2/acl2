; equal-by-g.lisp -- theorem for pick-a-point proofs of record equality
;
; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/
;
; This program is free software; you can redistribute it and/or modify it under
; the terms of the GNU General Public License as published by the Free Software
; Foundation; either version 2 of the License, or (at your option) any later
; version.  This program is distributed in the hope that it will be useful but
; WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
; FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
; more details.  You should have received a copy of the GNU General Public
; License along with this program; if not, write to the Free Software
; Foundation, Inc., 51 Franklin Street, Suite 500, Boston, MA 02110-1335, USA.
;
; Original author: Jared Davis <jared@centtech.com>

(in-package "ACL2")
(include-book "records")

; This book introduces a generic theorem that can be functionally instantiated
; to carry out pick-a-point proofs that records are equal.  The constraint is
; given by the following encapsulate.

(encapsulate
  (((equal-by-g-hyp) => *)
   ((equal-by-g-lhs) => *)
   ((equal-by-g-rhs) => *))

  (local (defun equal-by-g-hyp () nil))
  (local (defun equal-by-g-lhs () nil))
  (local (defun equal-by-g-rhs () nil))

  (defthm equal-by-g-constraint
    (implies (equal-by-g-hyp)
             (equal (g arbitrary-key (equal-by-g-lhs))
                    (g arbitrary-key (equal-by-g-rhs))))))

; Given this constraint, we prove the following theorem:
;
; (defthm equal-by-g
;   (implies (equal-by-g-hyp)
;            (equal (equal-by-g-lhs)
;                   (equal-by-g-rhs))))
;
; You can functionally instantiate this theorem with your choice of hyp, lhs,
; and rhs to showing that two records are equal by showing any arbitrary field
; is the same in both records.



; The proof starts with introducing a constructive witness that can find a
; mismatch between two well-formed records (i.e., between two valid rcdp's).
; Our badguy says what kind of mismatch it has found.

(local (defthm rcdp-of-cdr
         (implies (rcdp x)
                  (rcdp (cdr x)))))


(local
 (defun badguy (x y)
   (cond ((atom x)
          (if (atom y)
              nil
            (cons :extra-in-y (car y))))
         ((atom y)
          (cons :extra-in-x (car x)))
         ((equal (car x) (car y))
          (badguy (cdr x) (cdr y)))
         ((<< (caar x) (caar y))
          (cons :extra-in-x (car x)))
         ((equal (caar x) (caar y))
          (cons :mismatch (car x)))
         (t
          (cons :extra-in-y (car y))))))


; Now we just have a bunch of cases to deal with the different kinds of
; problems that the badguy might have reported.

(local
 (encapsulate
  ()
  (local (defthm l0
           (implies (and (<< (cadr (badguy x y)) a)
                         (equal (car (badguy x y)) :extra-in-x)
                         (rcdp x)
                         (<< b (caar x)))
                    (not (<< a b)))))

  (defthm lookup-in-x-when-extra-in-x
    (implies (and (equal (car (badguy x y)) :extra-in-x)
                  (rcdp x)
                  (rcdp y))
             (g-aux (cadr (badguy x y)) x))
    :hints(("Goal" :do-not '(generalize fertilize))))))

(local
 (encapsulate
   ()
   (local (defthm l0
            (implies (and (equal (car (badguy x y)) :extra-in-x)
                          (<< a (caar x))
                          (<< (cadr (badguy x y)) a)
                          (rcdp x))
                     (not (<< a (caar y))))))

   (defthm lookup-in-y-when-extra-in-x
     (implies (and (equal (car (badguy x y)) :extra-in-x)
                   (rcdp x)
                   (rcdp y))
              (and (not (g-aux (cadr (badguy x y)) y))))
     :hints(("Goal" :do-not '(generalize fertilize))))))

(local
 (encapsulate
   ()
   (local (defthm l0
            (implies (and (<< (cadr (badguy x y)) a)
                          (equal (car (badguy x y)) :extra-in-y)
                          (<< b (caar x))
                          (rcdp y)
                          (<< b (caar y)))
                     (not (<< a b)))))

   (defthm lookup-in-y-when-extra-in-y
     (implies (and (equal (car (badguy x y)) :extra-in-y)
                   (rcdp x)
                   (rcdp y))
              (g-aux (cadr (badguy x y)) y))
     :hints(("Goal" :do-not '(generalize fertilize))))))

(local
 (encapsulate
   ()
   (local (defthm l0
            (implies (and (equal (car (badguy x y)) :extra-in-y)
                          (<< a (caar x))
                          (<< (cadr (badguy x y)) a)
                          (rcdp y))
                     (not (<< a (caar y))))))

   (defthm lookup-in-x-when-extra-in-y
     (implies (and (equal (car (badguy x y)) :extra-in-y)
                   (rcdp x)
                   (rcdp y))
              (not (g-aux (cadr (badguy x y)) x)))
     :hints(("Goal" :do-not '(generalize fertilize))))))

(local
 (encapsulate
   ()
   (local (defthm l0
            (implies (and (<< (cadr (badguy x y)) a)
                          (equal (car (badguy x y)) :mismatch)
                          (rcdp x)
                          (rcdp y)
                          (<< b (caar x))
                          (<< b (caar y)))
                     (not (<< a b)))))

   (local (defthm l1
            (implies (and (equal (car (badguy x y)) :mismatch)
                          (rcdp x)
                          (rcdp y)
                          (<< a (caar x))
                          (<< (cadr (badguy x y)) a))
                     (not (<< a (caar y))))))

   (defthm mismatch-when-mismatch
     (implies (and (equal (car (badguy x y)) :mismatch)
                   (rcdp x)
                   (rcdp y))
              (equal (equal (g-aux (cadr (badguy x y)) x)
                            (g-aux (cadr (badguy x y)) y))
                     nil))
     :hints(("goal" :do-not '(generalize fertilize))))))


; It's easy to see that these are the only cases, and hence it is clear that
; the badguy works and if it reports a mismatch, it really is a mismatch.

(local (defthm badguy-cases
         (or (not (badguy x y))
             (equal (car (badguy x y)) :mismatch)
             (equal (car (badguy x y)) :extra-in-x)
             (equal (car (badguy x y)) :extra-in-y))
         :rule-classes nil))

(local (defthm g-aux-of-badguy
         (implies (and (badguy x y)
                       (rcdp x)
                       (rcdp y))
                  (not (equal (g-aux (cadr (badguy x y)) x)
                              (g-aux (cadr (badguy x y)) y))))
         :hints(("Goal"
                 :do-not-induct t
                 :do-not '(eliminate-destructors generalize fertilize)
                 :use ((:instance badguy-cases))))))


; The other critical fact is that the badguy always finds a mismatch between
; any non-equal records.  This follows from its definition.

(local (defthm badguy-unless-equal
         (implies (and (not (equal x y))
                       (rcdp x)
                       (rcdp y))
                  (badguy x y))))



; The badguy itself isn't sufficient because we need to deal with ill-formed
; records and the whole invertible mapping trick.  So, the "worseguy" is like
; the badguy but carries out the mapping if necessary.

(local
 (defun worseguy (x y)
  (badguy (acl2->rcd x)
          (acl2->rcd y))))

(local
 (defthm acl2->rcd-returns-rcdp
   (rcdp (acl2->rcd x))
   :hints(("Goal" :in-theory (enable acl2->rcd)))))


; From the main proof about the badguy, it follows that if the worseguy says
; there is a mismatch, it's a true mismatch for G.

(local
 (defthm worseguy-finds-counterexample
   (implies (worseguy x y)
            (not (equal (g (cadr (worseguy x y)) x)
                        (g (cadr (worseguy x y)) y))))
   :hints(("Goal" :in-theory (enable g)))))


; All that remains is to show that the worseguy always finds a mismatch for
; any non-equal objects.  We can approach this by cases.
;
; 1. Suppose X and Y are well-formed records, i.e., (not (IFRP X)) and (not (IFRP
; Y)).  Then they are both RCDP's, and the ACL2->RCD conversions are the
; identity, and so (worseguy x y) is just (badguy x y) and we're since we know
; that badguy finds a mismatch when given non-equal RCDP's.
;
; 2. Suppose X and Y are both ill-formed records, i.e., (IFRP X) and (IFRP Y).
; Then, the ACL2->RCD conversions will turn them both into RCDP's, in
; particular ((NIL . X)) and ((NIL . Y)).  Obviously these disagree about the
; value of the key NIL when X != Y, so we're done.
;
; 3. WLOG, suppose X is a well-formed record but Y is not.  Then, the ACL2->RCD
; conversion will leave X alone, but will turn Y into ((NIL . Y)).  We need to
; show that BADGUY will find a mismatch on these RCDP's.  Well, above we proved
; that that badguy always finds a mismatch between two RCDP's unless they're
; equal, so it would suffice to show that X is not equal to ((NIL . Y)).  And
; this is trivial: since Y is ill-formed, ((NIL . Y)) is ill-formed, and since
; above we assumed X was well-formed, this cannot be.

(local (defthm rcdp-unless-ifrp
         (implies (not (ifrp x))
                  (rcdp x))))

(local (defthm main-lemma-for-case-3
         (implies (and (not (ifrp x)) ;; it therefore must be an rcdp.
                       (ifrp y))
                  (not (equal x (list (cons nil y)))))))

(local (defthm corollary-for-case-3
         (implies (and (not (ifrp x)) ;; it therefore must be an rcdp.
                       (ifrp y))
                  (badguy x (list (cons nil y))))
         :hints(("Goal"
                 :in-theory (disable badguy-unless-equal)
                 :use ((:instance badguy-unless-equal
                                  (x x)
                                  (y (list (cons nil y)))))))))

(local (defthm worseguy-unless-equal
         (implies (not (equal x y))
                  (worseguy x y))
         :hints(("Goal"
                 :in-theory (enable acl2->rcd ifrp)
                 :do-not-induct t
                 :do-not '(generalize fertilize)))))

(defthm equal-by-g
  (implies (equal-by-g-hyp)
           (equal (equal-by-g-lhs)
                  (equal-by-g-rhs)))
  :hints(("Goal"
          :in-theory (disable worseguy-finds-counterexample
                              worseguy)
          :use ((:instance worseguy-finds-counterexample
                           (x (equal-by-g-lhs))
                           (y (equal-by-g-rhs)))))))
