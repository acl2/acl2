; ACL2 Version 8.3 -- A Computational Logic for Applicative Common Lisp
; Copyright (C) 2021, Regents of the University of Texas

; This version of ACL2 is a descendent of ACL2 Version 1.9, Copyright
; (C) 1997 Computational Logic, Inc.  See the documentation topic NOTE-2-0.

; This program is free software; you can redistribute it and/or modify
; it under the terms of the LICENSE file distributed with ACL2.

; This program is distributed in the hope that it will be useful,
; but WITHOUT ANY WARRANTY; without even the implied warranty of
; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
; LICENSE for more details.

; Written by:  Matt Kaufmann               and J Strother Moore
; email:       Kaufmann@cs.utexas.edu      and Moore@cs.utexas.edu
; Department of Computer Science
; University of Texas at Austin
; Austin, TX 78712 U.S.A.

(in-package "ACL2")


;=================================================================


; We continue our development of linear arithmetic.  In particular,
; we define the functions add-polys and linearize.


;=================================================================


; Add-polys

(defun polys-from-type-set (term force-flag dwp type-alist ens wrld ttree)

; If possible, we create a list of polys based upon the type-set
; of term.

; Warning: This function should not be used with any terms that are
; not legitimate pot-vars.  See the definition of good-pot-varp.
; Assuming that term is a legitimate pot-label --- meets all the
; invariants --- we do not have to normalize any of the polys below.

; We check that term is OK and throw an error if not.  It would,
; however, not be very expensive to wrap the below in a call to
; normalize-poly-lst, and thereby avoid the potential error situation.

  (if (good-pot-varp term)
    (mv-let (ts ts-ttree)
      (type-set term force-flag dwp type-alist ens wrld ttree nil nil)
      (cond ((ts-subsetp ts *ts-zero*)
             (list
              ;; 0 <= term
              (add-linear-terms :rhs term
                                (base-poly ts-ttree
                                           '<=
                                           t
                                           nil))
              ;; term <= 0
              (add-linear-terms :lhs term
                                (base-poly ts-ttree
                                           '<=
                                           t
                                           nil))))
            ((ts-subsetp ts *ts-one*)
             (list
              ;; 1 <= term
              (add-linear-terms :lhs *1*
                                :rhs term
                                (base-poly ts-ttree
                                           '<=
                                           t
                                           nil))
              ;; term <= 1
              (add-linear-terms :lhs term
                                :rhs *1*
                                (base-poly ts-ttree
                                           '<=
                                           t
                                           nil))))
            ((ts-subsetp ts *ts-bit*)
             (list
              ;; 0 <= term
              (add-linear-terms :lhs *0*
                                :rhs term
                                (base-poly ts-ttree
                                           '<=
                                           t
                                           nil))
              ;; term <= 1
              (add-linear-terms :lhs term
                                :rhs *1*
                                (base-poly ts-ttree
                                           '<=
                                           t
                                           nil))))
            ((ts-subsetp ts *ts-integer>1*)
             (list
              ;; 2 <= term
              (add-linear-terms :lhs *2*
                                :rhs term
                                (base-poly ts-ttree
                                           '<=
                                           t
                                           nil))))
            ((ts-subsetp ts *ts-positive-integer*)
             (list
              ;; 1 <= term
              (add-linear-terms :lhs *1*
                                :rhs term
                                (base-poly ts-ttree
                                           '<=
                                           t
                                           nil))))
            ((ts-subsetp ts *ts-negative-integer*)
             (list
              ;; term <= -1
              (add-linear-terms :lhs term
                                :rhs ''-1
                                (base-poly ts-ttree
                                           '<=
                                           t
                                           nil))))
            ((ts-subsetp ts
                         #-:non-standard-analysis *ts-positive-rational*
                         #+:non-standard-analysis *ts-positive-real*)
             (list
              ;; 0 < term
              (add-linear-terms :rhs term
                                (base-poly ts-ttree
                                           '<
                                           t
                                           nil))))
            ((ts-subsetp ts
                         #-:non-standard-analysis *ts-negative-rational*
                         #+:non-standard-analysis *ts-negative-real*)
             (list
              ;; term < 0
              (add-linear-terms :lhs term
                                (base-poly ts-ttree
                                           '<
                                           t
                                           nil))))
            ((ts-subsetp ts
                         #-:non-standard-analysis *ts-non-negative-rational*
                         #+:non-standard-analysis *ts-non-negative-real*)
             (list
              ;; 0 <= term
              (add-linear-terms :rhs term
                                (base-poly ts-ttree
                                           '<=
                                           t
                                           nil))))
            ((ts-subsetp ts
                         #-:non-standard-analysis *ts-non-positive-rational*
                         #+:non-standard-analysis *ts-non-positive-real*)
             (list
              ;; term <= 0
              (add-linear-terms :lhs term
                                (base-poly ts-ttree
                                           '<=
                                           t
                                           nil))))
            ((ts-subsetp ts (ts-union *ts-non-positive-rational*
                                      *ts-one*))
             (list
              ;; term <= 1
              (add-linear-terms :lhs term
                                :rhs *1*
                                (base-poly ts-ttree
                                           '<=
                                           t
                                           nil))))
            (t
             nil)))
    (er hard 'inverse-polys
        "A presumptive pot-label, ~x0,  has turned out to be illegitimate. ~
         If possible, please send a script reproducing this error ~
         to the authors of ACL2."
        term)))

(defun add-type-set-polys (var-lst new-pot-lst old-pot-lst
                           already-noted-vars
                           pt nonlinearp
                           type-alist ens force-flg wrld)

; We have just finished adding a bunch of polys to a pot-lst.  In ACL2
; versions prior to 2.7, these polys were canceled against any
; type-set information on the fly.  We now add the type-set
; information explicitly.  This function checks which pots have been
; modified (any new polys in these pots would have been canceled
; against type-set knowledge in the past), derives polys (using
; type-set information) about the vars of the modified pots, and adds
; them to the pots.

  (cond ((null var-lst)
         (let ((new-var-lst (changed-pot-vars new-pot-lst old-pot-lst
                                              already-noted-vars)))
           (if new-var-lst
               (add-type-set-polys new-var-lst
                                   new-pot-lst new-pot-lst
                                   new-var-lst
                                   pt nonlinearp
                                   type-alist ens force-flg wrld)
             (mv nil new-pot-lst))))
        (t
         (mv-let (contradictionp new-new-pot-lst)
           (add-polys0 (polys-from-type-set (car var-lst)
                                            force-flg
                                            nil ;;; dwp
                                            type-alist
                                            ens
                                            wrld
                                            nil) ;;; ttree
                       new-pot-lst pt nonlinearp t)
           (cond (contradictionp
                  (mv contradictionp nil))
                 (t
                  (add-type-set-polys (cdr var-lst)
                                      new-new-pot-lst old-pot-lst
                                      already-noted-vars
                                      pt nonlinearp
                                      type-alist ens force-flg wrld)))))))

(defun add-polynomial-inequalities (lst pot-lst pt nonlinearp type-alist ens
                                        force-flg wrld)

; Wrapper for the old add-polys (now add-polys0) so that we can
; eliminate the use of cancel-poly-against-type-set from within add-poly.

; We add the polys in lst to the pot-lst, and then call add-type-set-polys
; which performs a similar function to the old calls to
; cancel-poly-against-type-set.

; Historical Note:  The nearest approximation to this function in Nqthm
; was named add-equations.

  (mv-let (contradictionp new-pot-lst)
          (add-polys0 lst pot-lst pt nonlinearp t)
          (cond (contradictionp
                 (mv contradictionp nil))
                (t
                 (let ((changed-pot-vars
                        (changed-pot-vars new-pot-lst pot-lst nil)))
                   (add-type-set-polys changed-pot-vars
                                       new-pot-lst new-pot-lst
                                       changed-pot-vars
                                       pt nonlinearp
                                       type-alist ens force-flg wrld))))))

#-acl2-loop-only
(defparameter *add-polys-counter*

; This is used by dmr-string to show the cumulative number of calls of
; add-polys, as requested by Robert Krug.

  0)

(defun add-polys (lst pot-lst pt nonlinearp type-alist ens force-flg wrld)
  #-acl2-loop-only
  (when (f-get-global 'dmrp *the-live-state*)
    (return-from
     add-polys
     (progn
       (incf *add-polys-counter*)
       (pstk
        (add-polynomial-inequalities lst pot-lst pt nonlinearp type-alist ens
                                     force-flg wrld)))))
  (add-polynomial-inequalities lst pot-lst pt nonlinearp type-alist ens
                               force-flg wrld))


;=================================================================


; Linearize

(mutual-recursion

(defun eval-ground-subexpressions1 (term ens wrld safe-mode gc-off ttree
                                         hands-off-fns memo)

; We do not evaluate ground calls of the function symbols listed in
; hands-off-fns.

; Memo is an alist that saves results.  Typically it associates a ground
; subexpression G with a quoted constant resulting from evaluation of G; but if
; that evaluation fails then G is associated with either a term provably equal
; to G when some argument was changed by evaluation, else with nil.  For
; simplicity we don't bother saving such results for calls of IF or for lambda
; applications.  Suppose for example that term is (if tst tbr fbr), tst
; evaluates to nil, and fbr is a call of a function symbol other than IF that
; evaluates to the quoted constant fbr'; then we add (cons fbr fbr') to memo
; but we do not add (cons term fbr') to memo.  If necessary it shouldn't be too
; difficult to save such additional information in memo.

  (cond
   ((or (variablep term)
        (fquotep term)
        (eq (ffn-symb term) 'hide))
    (mv nil term ttree memo))
   ((flambda-applicationp term)
    (mv-let
      (flg args ttree memo)
      (eval-ground-subexpressions1-lst (fargs term) ens wrld safe-mode gc-off
                                       ttree
                                       hands-off-fns
                                       memo)
      (cond
       ((all-quoteps args)
        (mv-let
          (flg val ttree memo)
          (eval-ground-subexpressions1
           (sublis-var (pairlis$ (lambda-formals (ffn-symb term)) args)
                       (lambda-body (ffn-symb term)))
           ens wrld safe-mode gc-off ttree hands-off-fns memo)
          (declare (ignore flg))
          (mv t val ttree memo)))
       (flg

; We could look for just those args that are quoteps, and substitute those,
; presumably then calling make-lambda-application to create a lambda out of the
; result.  But we'll put that off for another time, or even indefinitely,
; noting that through Version_2.9.4 we did not evaluate any ground lambda
; applications.

        (mv t (cons-term (ffn-symb term) args) ttree memo))
       (t (mv nil term ttree memo)))))
   ((eq (ffn-symb term) 'if)
    (mv-let
      (flg1 arg1 ttree memo)
      (eval-ground-subexpressions1 (fargn term 1) ens wrld safe-mode gc-off
                                   ttree hands-off-fns memo)
      (cond
       ((quotep arg1)
        (if (cadr arg1)
            (mv-let
              (flg2 arg2 ttree memo)
              (eval-ground-subexpressions1 (fargn term 2) ens wrld safe-mode
                                           gc-off ttree hands-off-fns memo)
              (declare (ignore flg2))
              (mv t arg2 ttree memo))
          (mv-let
            (flg3 arg3 ttree memo)
            (eval-ground-subexpressions1 (fargn term 3) ens wrld safe-mode
                                         gc-off ttree hands-off-fns memo)
            (declare (ignore flg3))
            (mv t arg3 ttree memo))))
       (t (mv-let
            (flg2 arg2 ttree memo)
            (eval-ground-subexpressions1 (fargn term 2) ens wrld safe-mode
                                         gc-off ttree hands-off-fns memo)
            (mv-let
              (flg3 arg3 ttree memo)
              (eval-ground-subexpressions1 (fargn term 3) ens wrld safe-mode
                                           gc-off ttree hands-off-fns memo)
              (mv (or flg1 flg2 flg3)
                  (if (or flg1 flg2 flg3)
                      (fcons-term* 'if arg1 arg2 arg3)
                    term)
                  ttree
                  memo)))))))
   (t
    (let ((pair (assoc-equal term memo)))
      (cond
       (pair
        (mv t (or (cdr pair) term) ttree memo))
       (t (mv-let
            (flg args ttree memo)
            (eval-ground-subexpressions1-lst (fargs term) ens wrld safe-mode
                                             gc-off ttree hands-off-fns memo)
            (cond

; The following test was taken from rewrite with a few modifications
; for the formals used.

             ((and (logicp (ffn-symb term) wrld) ; maybe fn is being admitted
                   (all-quoteps args)
                   (enabled-xfnp (ffn-symb term) ens wrld)
                   (not (member-eq (ffn-symb term) hands-off-fns))

; We don't mind disallowing constrained functions that have attachments,
; because the call of ev-fncall below disallows the use of attachments (last
; parameter, aok, is nil).

                   (not (getpropc (ffn-symb term) 'constrainedp nil wrld)))
              (mv-let
                (erp val)
                (pstk
                 (ev-fncall-w (ffn-symb term)
                              (strip-cadrs args)
                              wrld
                              nil ; user-stobj-alist
                              safe-mode gc-off
                              t ; hard-error-returns-nilp
                              nil ; aok
                              ))
                (cond
                 (erp
                  (cond (flg
                         (let ((new-term (cons-term (ffn-symb term) args)))
                           (mv t
                               new-term
                               ttree
                               (acons term new-term memo))))
                        (t (mv nil term ttree (acons term nil memo)))))
                 (t (let ((kwote-val (kwote val)))
                      (mv t
                          kwote-val
                          (push-lemma (fn-rune-nume (ffn-symb term) nil t wrld)
                                      ttree)
                          (acons term kwote-val memo)))))))
             (flg (mv t (cons-term (ffn-symb term) args) ttree memo))
             (t (mv nil term ttree memo))))))))))

(defun eval-ground-subexpressions1-lst (lst ens wrld safe-mode gc-off ttree
                                            hands-off-fns memo)
  (cond ((null lst) (mv nil nil ttree memo))
        (t (mv-let
            (flg1 x ttree memo)
            (eval-ground-subexpressions1 (car lst) ens wrld safe-mode gc-off
                                         ttree hands-off-fns memo)
            (mv-let
             (flg2 y ttree memo)
             (eval-ground-subexpressions1-lst (cdr lst) ens wrld safe-mode
                                              gc-off ttree hands-off-fns memo)
             (mv (or flg1 flg2)
                 (if (or flg1 flg2)
                     (cons x y)
                   lst)
                 ttree
                 memo))))))
)

(defun eval-ground-subexpressions (term ens wrld state ttree)
  (mv-let (flg x ttree memo)
    (eval-ground-subexpressions1 term ens wrld
                                 (f-get-global 'safe-mode state)
                                 (gc-off state)
                                 ttree
                                 nil
                                 nil)
    (declare (ignore memo))
    (mv flg x ttree)))

(defun eval-ground-subexpressions-lst (lst ens wrld state ttree)
  (mv-let (flg x ttree memo)
    (eval-ground-subexpressions1-lst lst ens wrld
                                     (f-get-global 'safe-mode state)
                                     (gc-off state)
                                     ttree
                                     nil
                                     nil)
    (declare (ignore memo))
    (mv flg x ttree)))

(defun poly-set (op poly1 poly2)

; Suppose linearize is called on some term, term.  The output of
; linearize is either nil, (list (list poly1 poly2)), or (list (list
; poly1) (list poly2)).  An answer of the first form means "no
; arithmetic information can be extracted from the assumption that
; term is true."  An answer of the second form means "both poly1 and
; poly2 are true if term is true."  An answer of the third form means
; "either poly1 or poly2 is true if term is true."

; This functions takes two polys and an operation, op, and constructs
; the answer returned by linearize.  Op is either 'and or 'or and
; determines whether we construct (list (list poly1 poly2)), when
; op='and, or (list (list poly1) (list poly2)), when op='or.

; However, there are two special cases.

; First, it is sometimes the case that we want to construct an 'and
; but only have one poly, the other one being nil.  This may happen
; when we were going to construct an 'or but noticed that one branch
; is contradictory.  When this happens it is always poly1 that is nil
; and poly2 that we want to return.

; Second, it may happen that either or both of the polys are silly in
; the sense that they are based on false assumptions.  Since silly polys
; are logically true, we act accordingly.  Thus, if we are to return
; a conjunction and one of the polys is silly we return the other.
; But if we are to return a disjunction and one is silly, we return nil,
; meaning we could extract no arithmetic information.  For example,
; suppose poly2 is silly and we are to return (list (list poly1) (list poly2)).
; Then the silliness of poly2 means the second disjunct is true, which
; is represented here as (list (list poly1) nil).  That, by the way, was
; nqthm's answer in this case.  However, this disjunct gives the caller
; no help because it means either poly1 is true or T is true.  So we
; just tell the caller "no information".

; Note about Nqthm:  As remarked above, nqthm's linearize can return
; (list (list poly1) nil).  How is this used?  It is put on the
; split-lst when we start adding polynomials to the pot.  We then see if
; we can get a contradiction from one side and if so, we assume the other.
; We certainly can't get a contradiction from the nil side.  Suppose
; we got a contradiction from the other.  Then we'd assume the other
; side, which is a no-op.  The end result is that returning such an
; answer causes work but is guaranteed to have no effect.

; It is unlikely that we can generate a silly poly2 without generating a
; silly poly1, since silliness stems from requiring a false rationalp
; assumption.  However, rather than convince ourselves that they are
; both silly if either is, we'll just check both.

  (cond ((eq op 'and)
         (cond ((or (eq poly1 nil)
                    (silly-polyp poly1))
                (cond ((silly-polyp poly2) nil)
                      (t (list (list poly2)))))
               ((silly-polyp poly2)
                (list (list poly1)))
               (t (list (list poly1 poly2)))))
        ((or (silly-polyp poly1)
             (silly-polyp poly2))
         nil)
        ((impossible-polyp poly1)
         (list (list (change poly poly2
                             :ttree
                             (cons-tag-trees (access poly poly1 :ttree)
                                             (access poly poly2 :ttree))
                             :parents
                             (marry-parents (access poly poly1 :parents)
                                            (access poly poly2 :parents))))))
        ((impossible-polyp poly2)
         (list (list (change poly poly1
                             :ttree
                             (cons-tag-trees (access poly poly1 :ttree)
                                             (access poly poly2 :ttree))
                             :parents
                             (marry-parents (access poly poly1 :parents)
                                            (access poly poly2 :parents))))))
        (t (list (list poly1) (list poly2)))))

;; Historical Comment from Ruben Gamboa:
;; I changed complex-rational to complex, and rational to real,
;; to stand for the non-zero numbers.

(defun linearize1 (term positivep type-alist ens force-flg wrld ttree state)

; See the comment in linearize.  Linearize1 does all the work of linearize
; except that the latter maps normalize-poly over the former.

    (mv-let (flg temp ttree)
      (eval-ground-subexpressions term ens wrld state ttree)
      (declare (ignore flg))
     (mv-let
      (not-flg atm)
      (strip-not temp)

; Let us pause for a moment here.  Term is the original term we are to
; linearize and is preserved for the use of add-linear-assumption.  Temp is
; the result of replacing all ground subexpressions in term by their
; values, and atm is temp with any 'not stripped off.  Recall that we
; are attempting to derive a contradiction by assuming either (1) that
; term is true if positivep is true, or (2) that term is false if
; positivep is false.  Since not-flg tells us whether atm is the
; negation of term/temp, we use it to reset positivep to reflect its
; new role with respect to atm.

      (let ((positivep (if not-flg (not positivep) positivep)))
        (cond
         ((inequalityp atm)
          (let ((lhs (fargn atm 1))
                (rhs (fargn atm 2)))
            (mv-let (ts-lhs ts-ttree)
              (type-set lhs force-flg nil type-alist ens wrld ttree nil nil)
              (mv-let (ts-rhs ts-ttree)
                (type-set rhs force-flg nil type-alist ens wrld ts-ttree nil
                          nil)
                (if positivep ; (< lhs rhs)
                    (cond
                     ((and (ts-integerp ts-lhs)
                           (ts-integerp ts-rhs))

; (implies (and (< lhs rhs)
;               (integerp lhs)
;               (integerp rhs))
;          (<= (1+ lhs) rhs))

                      (poly-set 'and
                                nil
                                (add-linear-terms
                                 :lhs lhs
                                 :lhs *1*
                                 :rhs rhs
                                 (base-poly ts-ttree
                                            '<=
                                            t
                                            nil))))
                     (t ; still (< lhs rhs), but not both integerp
                      (poly-set 'and
                                nil
                                (add-linear-terms
                                 :lhs lhs
                                 :rhs rhs
                                 (let ((rationalp-flg
                                        (and (ts-real/rationalp ts-lhs)
                                             (ts-real/rationalp ts-rhs))))
                                   (base-poly0 (if rationalp-flg
                                                   ts-ttree
                                                 ttree)

; :Parent wart:

; In a slight break from tradition (here and in three other places below that
; refer to this comment), we use the parents from the original ttree.  When
; fixing a (probably long-standing) bug in Version_3.0.1 by recording ts-ttree
; above in the case that rationalp-flg is true, we found that the regression
; suite broke in three places without this tweak on the parents.  Since
; rationalp-flg is only used in non-linear arithmetic, this seems like a minor
; break from our traditional propagation of parent trees.  We considered making
; a similar change for all calls of base-poly in this function, but that led to
; a proof failure in community book
; books/workshops/2004/schmaltz-borrione/support/routing_defuns.lisp that
; looked like it would be painful to fix, and we took that as a sign that such
; loss of backward compatibility could be painful for other users, and
; potentially even a bad heuristic.

                                               (collect-parents ttree)
                                               '<
                                               rationalp-flg
                                               nil))))))

; The (not positivep) case.  Note:
; (implies (not (< lhs rhs))
;          (<= rhs lhs))

                  (poly-set 'and
                            nil
                            (add-linear-terms
                             :lhs rhs
                             :rhs lhs
                             (let ((rationalp-flg
                                    (and (ts-real/rationalp ts-lhs)
                                         (ts-real/rationalp ts-rhs))))
                               (base-poly0 (if rationalp-flg ts-ttree ttree)

; See the "break from tradition" comment above for a discussion of the
; parents.

                                           (collect-parents ttree)
                                           '<=
                                           rationalp-flg
                                           nil)))))))))
         ((equalityp atm)
          (let ((lhs (fargn atm 1))
                (rhs (fargn atm 2)))
            (mv-let (ts-lhs ts-ttree)
              (type-set lhs force-flg nil type-alist ens wrld ttree nil nil)
              (mv-let (ts-rhs ts-ttree)
                (type-set rhs force-flg nil type-alist ens wrld ts-ttree nil
                          nil)

; Here is the one place that we can construct a poly which is derived
; from a negated equality.  Note that the final argument to base-poly
; is 'T.

                (if positivep

; (implies (equal lhs rhs)
;          (and (<= lhs rhs) (<= rhs lhs)))

                    (let ((rationalp-flg (and (ts-real/rationalp ts-lhs)
                                              (ts-real/rationalp ts-rhs))))
                      (poly-set 'and
                                (add-linear-terms
                                 :lhs lhs
                                 :rhs rhs
                                 (base-poly0 (if rationalp-flg ts-ttree ttree)

; See the "break from tradition" comment above for a discussion of the
; parents.

                                             (collect-parents ttree)
                                             '<=
                                             rationalp-flg
                                             t))
                                (add-linear-terms
                                 :lhs rhs
                                 :rhs lhs
                                 (base-poly0 (if rationalp-flg ts-ttree ttree)

; See the "break from tradition" comment above for a discussion of the
; parents.

                                             (collect-parents ttree)
                                             '<=
                                             rationalp-flg
                                             t))))

; Other case: (not (equal lhs rhs)).  But we need additional (type) information
; in order to derive inequalities.

                  (cond ((and (ts-subsetp ts-lhs *ts-integer*)
                              (ts-subsetp ts-rhs *ts-integer*))

; (implies (and (not (equal lhs rhs))
;               (integerp lhs)
;               (integerp rhs))
;          (or (<= (1+ lhs) rhs)
;              (<= (1+ rhs) lhs)))

                         (poly-set 'or
                                   (add-linear-terms
                                    :lhs lhs
                                    :lhs *1*
                                    :rhs rhs
                                    (base-poly ts-ttree
                                               '<=
                                               t
                                               nil))
                                   (add-linear-terms
                                    :lhs rhs
                                    :lhs *1*
                                    :rhs lhs
                                    (base-poly ts-ttree
                                               '<=
                                               t
                                               nil))))
                        ((if (ts-subsetp ts-lhs *ts-acl2-number*)
                             (or (ts-subsetp ts-rhs *ts-acl2-number*)
                                 (ts-disjointp ts-lhs *ts-zero*))
                           (and (ts-subsetp ts-rhs *ts-acl2-number*)
                                (ts-disjointp ts-rhs *ts-zero*)))

; (implies (and (not (equal lhs rhs))
;               (or (and (acl2-numberp lhs)
;                        (acl2-numberp rhs))
;                   (and (acl2-numberp lhs)
;                        (not (equal lhs 0)))
;                   (and (acl2-numberp rhs)
;                        (not (equal rhs 0)))))
;          (or (< lhs rhs)
;              (< rhs lhs)))

                         (let ((rationalp-flg
                                (and (ts-real/rationalp ts-lhs)
                                     (ts-real/rationalp ts-rhs))))
                           (poly-set 'or
                                     (add-linear-terms
                                      :lhs lhs
                                      :rhs rhs
                                      (base-poly ts-ttree
                                                 '<
                                                 rationalp-flg
                                                 nil))
                                     (add-linear-terms
                                      :lhs rhs
                                      :rhs lhs
                                      (base-poly ts-ttree
                                                 '<
                                                 rationalp-flg
                                                 nil)))))
                        ((and (ts-acl2-numberp ts-lhs)
                              force-flg
                              (ts-intersectp ts-rhs *ts-acl2-number*))

; (implies (and (not (equal lhs rhs))
;               (acl2-numberp lhs)
;               (force (acl2-numberp rhs)))
;          (or (< lhs rhs)
;              (< rhs lhs)))

                         (mv-let (flg new-ttree)
                                 (add-linear-assumption
                                  term
                                  `(acl2-numberp ,rhs)
                                  type-alist ens
                                  (immediate-forcep nil ens)
                                  force-flg wrld ts-ttree)

; We strongly suspect that add-linear-assumption will succeed with flg =
; :added, since (ts-intersectp ts-rhs *ts-acl2-number*).  But we do not depend
; on this without checking it.  Indeed, it fails for the following example,
; sent to us by Sol Swords.

;   (defstub bar-p (x) nil)
;   (defstub foo (x) nil)
;
;   (defaxiom type-of-foo
;      (implies (force (bar-p x))
;               (or (and (rationalp (foo x))
;                        (<= 0 (foo x)))
;                   (equal (foo x) nil)))
;      :rule-classes :type-prescription)
;
;   (thm (implies (not (rationalp (foo x))) (equal 0 (foo x))))

                                 (cond
                                  ((and (not (eq flg :failed))
                                        (not (eq flg :known-false)))
                                   (poly-set 'or
                                             (add-linear-terms
                                              :lhs lhs
                                              :rhs rhs
                                              (base-poly new-ttree
                                                         '<
                                                         nil
                                                         nil))
                                             (add-linear-terms
                                              :lhs rhs
                                              :rhs lhs
                                              (base-poly new-ttree
                                                         '<
                                                         nil
                                                         nil))))
                                  (t nil))))
                        ((and (ts-acl2-numberp ts-rhs)
                              force-flg
                              (ts-intersectp ts-lhs *ts-acl2-number*))

; (implies (and (not (equal lhs rhs))
;               (acl2-numberp rhs)
;               (force (acl2-numberp lhs)))
;          (or (< lhs rhs)
;              (< rhs lhs)))

                         (mv-let (flg new-ttree)
                                 (add-linear-assumption
                                  term
                                  `(acl2-numberp ,lhs)
                                  type-alist ens
                                  (immediate-forcep nil ens)
                                  force-flg wrld ts-ttree)
                                 (cond
                                  ((and (not (eq flg :failed))
                                        (not (eq flg :known-false)))
                                   (poly-set 'or
                                             (add-linear-terms
                                              :lhs lhs
                                              :rhs rhs
                                              (base-poly new-ttree
                                                         '<
                                                         nil
                                                         nil))
                                             (add-linear-terms
                                              :lhs rhs
                                              :rhs lhs
                                              (base-poly new-ttree
                                                         '<
                                                         nil
                                                         nil))))
                                  (t nil))))
                        (t
                         nil)))))))
       ((quotep atm)

; This is a strange one.  It can happen that the
; eval-ground-subexpressions can reduce the term to a constant.  We
; saw this happen in a bug reported by Jun Sawada.  Suppose (<= 2 (foo
; x)) is a :LINEAR lemma about foo.  Suppose we wish to prove (not
; (equal 1 (foo 3))).  This should be obvious.  But we assume the
; negation of the conclusion and get (foo 3) = 1.  We then find the
; linear lemma and instantiate it to get (<= 2 (foo 3)).  We then
; rewrite-linear-concl and get (<= 2 1), which we eval to 'nil!  If we
; do not recognize that we've succeeded here, we do not prove the
; theorem because all manner of other heuristics prevent us from using
; (<= 2 (foo x)) against the current literal.  Not surprisingly, this
; is an example of tail biting: we've used the negation of the goal to
; prevent ourselves from proving it!  One could probably construct a
; more insidious example of tail biting from this example -- an
; example that is not solved by the hack here of recognizing when eval
; solved our problem -- by arranging for rewrite-linear-concl to
; rewrite the inequality to something that we can't use but which
; doesn't eval to nil.

; Here is another curious example:

;    ACL2 !>
;    (thm
;     (implies (and (not (consp x))
;                   (true-listp x))
;              (equal (reverse (reverse x)) x)))
;
;    But simplification reduces this to T, using the :executable-counterparts
;    of EQUAL and REVERSE and linear arithmetic.
;
;    Q.E.D.
;
;    Summary
;    Form:  ( THM ...)
;    Rules: ((:DEFINITION NOT)
;            (:EXECUTABLE-COUNTERPART EQUAL)
;            (:EXECUTABLE-COUNTERPART REVERSE)
;            (:FAKE-RUNE-FOR-LINEAR NIL))
;    Warnings:  None
;    Time:  0.01 seconds (prove: 0.01, print: 0.00, other: 0.00)
;
;    Proof succeeded.

; Note the presence of (:FAKE-RUNE-FOR-LINEAR NIL).
; This oddity is due to the fact that we now rewrite all terms (not
; just the conclusion of linear lemmas) before adding them to the
; linear-pot-lst.

        (if positivep

; Recall that we are hoping to derive a contradiction from assuming atm
; true.  Hence, we win iff atm is 'NIL.

            (if (equal atm *nil*)
                (poly-set 'and
                          nil
                          (impossible-poly ttree))
              nil)

; We are hoping to derive a contradiction from assuming atm false.  Hence,
; we win iff atm is not 'NIL.

          (if (not (equal atm *nil*))
              (poly-set 'and
                        nil
                        (impossible-poly ttree))
              nil)))
       (t nil))))))

(defun linearize (term positivep type-alist ens force-flg wrld ttree state)

; If positivep we are to linearize term; else we are to linearize the negation
; of term.  The linearization of a term is either NIL, meaning no linear
; information was extracted from the term; or else it is a list of length 1
; containing a list of polynomials ((p1...pn)) such that term implies their
; conjunction (p1&...&pn); or else it is a list of length 2, ((p1...pn)
; (q1...qn)), such that term implies the disjunction (p1&...&pn) \/
; (q1&...&qn).  The claim that the term implies the polys has to be taken with
; a grain of salt: the additional 'assumptions in the ttree fields of the polys
; must be considered.

; There are two situations where this code might add an assumption to the polys
; it creates.  The first is that we sometimes call type-set and may get back a
; ttree with assumptions in it, which then infect our polys.  The second
; involves the linearization of negative equalities, where we insist that both
; x and y be numeric in order to derive (or (< x y) (< y x)) from (not (equal x
; y)).  Otherwise, we do not add any assumptions to our polys.

; We store ttree in the ttree of the poly.

; Trace Note:
;   (trace (linearize
;           :entry
;           (list* (car si::arglist) (cadr si::arglist) (caddr si::arglist)
;                  '|ens| (car (cddddr si::arglist)) '(|wrld| |ttree| |state|))
;           :exit
;           (cond ((null (car values)) (list nil))
;                 ((null (cdr (car values)))
;                  (list (cons 'and (show-poly-lst (car (car values))))))
;                 (t (list
;                     (list 'or
;                           (cons 'and (show-poly-lst (car (car values))))
;                           (cons 'and (show-poly-lst (cadr (car values))))))))))

  (let ((temp (linearize1 term positivep type-alist ens
                          force-flg wrld ttree state)))
    (cond ((null temp)
           nil)
          ((null (cdr temp))
           (list (normalize-poly-lst (car temp))))
          (t
           (list (normalize-poly-lst (car temp))
                 (normalize-poly-lst (cadr temp)))))))

(defun linearize-lst1
  (term-lst ttrees positivep type-alist ens force-flg wrld state
            poly-lst split-lst)
  (cond ((null term-lst)
         (mv (reverse poly-lst) (reverse split-lst)))
        (t (let ((lst (linearize (car term-lst)
                                 positivep
                                 type-alist ens force-flg wrld
                                 (car ttrees)
                                 state)))
             (cond
              ((null lst)
               (linearize-lst1 (cdr term-lst)
                               (cdr ttrees)
                               positivep
                               type-alist ens force-flg wrld state
                               poly-lst split-lst))
              ((null (cdr lst))
               (linearize-lst1 (cdr term-lst)
                               (cdr ttrees)
                               positivep
                               type-alist ens force-flg wrld state
                               (revappend (car lst) poly-lst) split-lst))
              (t
               (linearize-lst1 (cdr term-lst)
                               (cdr ttrees)
                               positivep
                               type-alist ens force-flg wrld state
                               poly-lst (cons lst split-lst))))))))

(defun linearize-lst
  (term-lst ttrees positivep type-alist ens force-flg wrld state)

; This function linearizes every term in term-lst, using the parity
; indicated by positivep, and type-alist and wrld.  This effectively
; assumes true/false (as per positivep) each term in term-lst and produces
; some polys.  Ttrees is in weak 1:1 correspondence with term-lst and
; enumerates the parent trees to use for each term in all the polys
; generated for the term; if ttrees is nil, no parent tree is stored.

; We return two values, poly-lst and split-lst.  The first is a list of
; polys that may be assumed true.  I.e., all these polys are implied by the
; assumption of term-lst.  The second is a list of doublets (lst1 lst2),
; such that each lst is a list of polys and the assumption of term-lst
; implies one of either lst1 or lst2 for each doublet.

  (linearize-lst1 term-lst ttrees positivep type-alist ens force-flg wrld state
                  nil nil))


