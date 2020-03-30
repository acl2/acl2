; ACL2 Version 8.2 -- A Computational Logic for Applicative Common Lisp
; Copyright (C) 2019, Regents of the University of Texas

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

(defun select-x-cl-set (cl-set induct-hint-val)

; This function produces the clause set we explore to collect
; induction candidates.  The x in this name means "explore."  If
; induct-hint-val is non-nil and non-t, we use the user-supplied
; induction hint value (which, if t means use cl-set); otherwise, we
; use cl-set.

  (cond ((null induct-hint-val) cl-set)
        ((equal induct-hint-val *t*) cl-set)
        (t (list (list induct-hint-val)))))

(defun unchangeables (formals args quick-block-info subset ans)

; We compute the set of all variable names occurring in args in
; unchanging measured formal positions.  We accumulate the answer onto
; ans.

  (cond ((null formals) ans)
        ((and (member-eq (car formals) subset)
              (eq (car quick-block-info) 'unchanging))
         (unchangeables (cdr formals) (cdr args) (cdr quick-block-info) subset
                        (all-vars1 (car args) ans)))
        (t
         (unchangeables (cdr formals) (cdr args) (cdr quick-block-info) subset
                        ans))))

(defun changeables (formals args quick-block-info subset ans)

; We compute the args in changing measured formal positions.  We
; accumulate the answer onto ans.

  (cond ((null formals) ans)
        ((and (member-eq (car formals) subset)
              (not (eq (car quick-block-info) 'unchanging)))
         (changeables (cdr formals) (cdr args) (cdr quick-block-info)
                      subset
                      (cons (car args) ans)))
        (t
         (changeables (cdr formals) (cdr args) (cdr quick-block-info)
                      subset
                      ans))))

(defun sound-induction-principle-mask1 (formals args quick-block-info
                                                subset
                                                unchangeables
                                                changeables)
; See sound-induction-principle-mask.

  (cond
   ((null formals) nil)
   (t (let ((var (car formals))
            (arg (car args))
            (q (car quick-block-info)))
        (mv-let (mask-ele new-unchangeables new-changeables)
          (cond ((member-eq var subset)
                 (cond ((eq q 'unchanging)
                        (mv 'unchangeable unchangeables changeables))
                       (t (mv 'changeable unchangeables changeables))))
                ((and (variablep arg)
                      (eq q 'unchanging))
                 (cond ((member-eq arg changeables)
                        (mv nil unchangeables changeables))
                       (t (mv 'unchangeable
                              (add-to-set-eq arg unchangeables)
                              changeables))))
                ((and (variablep arg)
                      (not (member-eq arg changeables))
                      (not (member-eq arg unchangeables)))
                 (mv 'changeable
                     unchangeables
                     (cons arg changeables)))
                (t (mv nil unchangeables changeables)))
          (cons mask-ele
                (sound-induction-principle-mask1 (cdr formals)
                                                 (cdr args)
                                                 (cdr quick-block-info)
                                                 subset
                                                 new-unchangeables
                                                 new-changeables)))))))

(defun sound-induction-principle-mask (term formals quick-block-info subset)

; Term is a call of some fn on some args.  The formals and
; quick-block-info are those of fn, and subset is one of fn's measured
; subset (a subset of formals).  We wish to determine, in the
; terminology of ACL, whether the induction applies to term.  If so we
; return a mask indicating how to build the substitutions for the
; induction from args and the machine for fn.  Otherwise we return
; nil.

; Let the changeables be those args that are in measured formal
; positions that sometimes change in the recursion.  Let the
; unchangeables be all of the variables occurring in measured actuals
; that never change in recursion.  The induction applies if
; changeables is a sequence of distinct variable names and has an
; empty intersection with unchangeables.

; If the induction is applicable then the substitutions should
; substitute for the changeables just as the recursion would, and hold
; each unchangeable fixed -- i.e., substitute each for itself.  With
; such substitutions it is possible to prove the measure lemmas
; analogous to those proved when justification of subset was stored,
; except that the measure is obtained by instantiating the measure
; term used in the justification by the measured actuals in unchanging
; slots.  Actual variables that are neither among the changeables or
; unchangeables may be substituted for arbitrarily.

; If the induction is applicable we return a mask with as many
; elements as there are args.  For each arg the mask contains either
; 'changeable, 'unchangeable, or nil.  'Changeable means the arg
; should be instantiated as specified in the recursion.  'Unchangeable
; means each var in the actual should be held fixed.  Nil means that
; the corresponding substitution pairs in the machine for the function
; should be ignored.

; Abstractly, this function builds the mask by first putting either
; 'changeable or 'unchangeable in each measured slot.  It then fills
; in the remaining slots from the left so as to permit the actual to
; be instantiated or held fixed as desired by the recursion, provided
; that in so doing it does not permit substitutions for previously
; allocated actuals.

  (let ((unchangeables
         (unchangeables formals (fargs term) quick-block-info subset nil))
        (changeables
         (changeables formals (fargs term) quick-block-info subset nil)))
    (cond ((or (not (no-duplicatesp-equal changeables))
               (not (all-variablep changeables))
               (intersectp-eq changeables unchangeables))
           nil)
          (t (sound-induction-principle-mask1 formals
                                              (fargs term)
                                              quick-block-info
                                              subset
                                              unchangeables
                                              changeables)))))


(defrec candidate
  (score controllers changed-vars unchangeable-vars
         tests-and-alists-lst justification induction-term other-terms
         xinduction-term xother-terms xancestry
         ttree)
  nil)

; This record is used to represent one of the plausible inductions that must be
; considered.  The SCORE represents some fairly artificial estimation of how
; many terms in the conjecture want this induction.  CONTROLLERS is the list of
; the controllers -- including unchanging controllers -- for all the inductions
; merged to form this one.  The CHANGED-VARS is a list of all those variables
; that will be instantiated (non-identically) in some induction hypotheses.
; Thus, CHANGED-VARS include both variables that actually contribute to why
; some measure goes down and variables like accumulators that are just along
; for the ride.  UNCHANGEABLE-VARS is a list of all those vars which may not be
; changed by any substitution if this induction is to be sound for the reasons
; specified.  TESTS-AND-ALISTS-LST is a list of TESTS-AND-ALISTS which
; indicates the case analysis for the induction and how the various induction
; hypotheses are obtained via substitutions.  JUSTIFICATION is the
; JUSTIFICATION that justifies this induction, and INDUCTION-TERM is the term
; that suggested this induction and from which you obtain the actuals to
; substitute into the template.  OTHER-TERMS are the induction-terms of
; candidates that have been merged into this one for heuristic reasons.

; Because of induction rules we can think of some terms being aliases for
; others.  We have to make a distinction between the terms in the conjecture
; that suggested an induction and the actual terms that suggested the
; induction.  For example, if an induction rule maps (fn x y) to (recur x y),
; then (recur x y) will be the INDUCTION-TERM because it suggested the
; induction and we will, perhaps, have to recover its induction machine or
; quick block information to implement various heuristics.  But we do not wish
; to report (recur x y) to the user, preferring instead to report (fn x y).
; Therefore, corresponding to INDUCTION-TERM and OTHER-TERMS we have
; XINDUCTION-TERM and XOTHER-TERMS, which are maintained in exactly the same
; way as their counterparts but which deal completely with the user-level view
; of the induction.  In practice this means that we will initialize the
; XINDUCTION-TERM field of a candidate with the term from the conjecture,
; initialize the INDUCTION-TERM with its alias, and then merge the fields
; completely independently but analogously.  XANCESTRY is a field maintained by
; merging to contain the user-level terms that caused us to change our
; tests-and-alists.  (Some candidates may be flushed or merged into this one
; without changing it.)

; The ttree of a candidate contains 'LEMMA tags listing the :induction rules
; (if any) involved in the suggestion of the candidate.

(defun count-non-nils (lst)
  (cond ((null lst) 0)
        ((car lst) (1+ (count-non-nils (cdr lst))))
        (t (count-non-nils (cdr lst)))))

(defun controllers (formals args subset ans)
  (cond ((null formals) ans)
        ((member (car formals) subset)
         (controllers (cdr formals) (cdr args) subset
                      (all-vars1 (car args) ans)))
        (t (controllers (cdr formals) (cdr args) subset ans))))

(defun changed/unchanged-vars (x args mask ans)
  (cond ((null mask) ans)
        ((eq (car mask) x)
         (changed/unchanged-vars x (cdr args) (cdr mask)
                                 (all-vars1 (car args) ans)))
        (t (changed/unchanged-vars x (cdr args) (cdr mask) ans))))

(defrec tests-and-alists (tests alists) nil)

(defun tests-and-alists/alist (alist args mask call-args)

; Alist is an alist that maps the formals of some fn to its actuals,
; args.  Mask is a sound-induction-principle-mask indicating the args
; for which we will build substitution pairs.  Call-args is the list of
; arguments to some recursive call of fn occurring in the induction
; machine for fn.  We build an alist mapping the masked args to the
; instantiations (under alist) of the values in call-args.

  (cond
   ((null mask) nil)
   ((null (car mask))
    (tests-and-alists/alist alist (cdr args) (cdr mask) (cdr call-args)))
   ((eq (car mask) 'changeable)
    (cons (cons (car args)
                (sublis-var alist (car call-args)))
          (tests-and-alists/alist alist
                                  (cdr args)
                                  (cdr mask)
                                  (cdr call-args))))
   (t (let ((vars (all-vars (car args))))
        (append (pairlis$ vars vars)
                (tests-and-alists/alist alist
                                        (cdr args)
                                        (cdr mask)
                                        (cdr call-args)))))))

(defun tests-and-alists/alists (alist args mask calls)

; Alist is an alist that maps the formals of some fn to its actuals,
; args.  Mask is a sound-induction-principle-mask indicating the args
; for which we will build substitution pairs.  Calls is the list of
; calls for a given case of the induction machine.  We build the alists
; from those calls.

  (cond
   ((null calls) nil)
   (t (cons (tests-and-alists/alist alist args mask (fargs (car calls)))
            (tests-and-alists/alists alist args mask (cdr calls))))))

; The following record contains the tests leading to a collection of
; recursive calls at the end of a branch through a defun.  In general,
; the calls may not be to the function being defuned but rather to
; some other function in the same mutually recursive clique, but in
; the context of induction we know that all the calls are to the same
; fn because we haven't implemented mutually recursive inductions yet.

; A list of these records constitute the induction machine for a function.

(defrec tests-and-calls (tests . calls) nil)

; The justification record contains a subset of the formals of the function
; under which it is stored.  Only the subset, ruler-extenders, and subversive-p
; fields have semantic content!  The other fields are the domain predicate, mp;
; the relation, rel, which is well-founded on mp objects; and the mp-measure
; term which has been proved to decrease in the recursion.  The latter three
; fields are correct at the time the function is admitted, but note that they
; might all be local and hence have disappeared by the time these fields are
; read.  Thus, we include them only for heuristic purposes, for example as used
; in community book books/workshops/2004/legato/support/generic-theories.lisp.

; A list of justification records is stored under each function symbol by the
; defun principle.

(defrec justification
  (subset . ((subversive-p . (mp . rel))
             (measure . ruler-extenders)))
  nil)

(defun tests-and-alists (alist args mask tc)

; Alist is an alist that maps the formals of some fn to its actuals,
; args.  Mask is a sound-induction-principle-mask indicating the args
; for which we will build substitution pairs.  Tc is one of the
; tests-and-calls in the induction machine for the function.  We make
; a tests-and-alists record containing the instantiated tests of tc
; and alists derived from the calls of tc.

  (make tests-and-alists
        :tests (sublis-var-lst alist (access tests-and-calls tc :tests))
        :alists (tests-and-alists/alists alist
                                        args
                                        mask
                                        (access tests-and-calls tc :calls))))

(defun tests-and-alists-lst (alist args mask machine)

; We build a list of tests-and-alists from machine, instantiating it
; with alist, which is a map from the formals of the function to the
; actuals, args.  Mask is the sound-induction-principle-mask that
; indicates the args for which we substitute.

  (cond
   ((null machine) nil)
   (t (cons (tests-and-alists alist args mask (car machine))
            (tests-and-alists-lst alist args mask (cdr machine))))))

(defun flesh-out-induction-principle (term formals justification mask machine
                                           xterm ttree)

; Term is a call of some function the indicated formals and induction machine.
; Justification is its 'justification and mask is a sound-induction-
; principle-mask for the term.  We build the induction candidate suggested by
; term.

  (make candidate
        :score
        (/ (count-non-nils mask) (length mask))

        :controllers
        (controllers formals (fargs term)
                     (access justification justification :subset)
                     nil)

        :changed-vars
        (changed/unchanged-vars 'changeable (fargs term) mask nil)

        :unchangeable-vars
        (changed/unchanged-vars 'unchangeable (fargs term) mask nil)

        :tests-and-alists-lst
        (tests-and-alists-lst (pairlis$ formals (fargs term))
                              (fargs term) mask machine)

        :justification justification

        :induction-term term
        :xinduction-term xterm

        :other-terms nil
        :xother-terms nil
        :xancestry nil
        :ttree ttree))

(defun intrinsic-suggested-induction-cand
  (induction-rune term formals quick-block-info justification machine xterm
                  ttree)

; Note: An "intrinsically suggested" induction scheme is an induction scheme
; suggested by a justification of a recursive function.  The rune controlling
; the intrinsic suggestion from the justification of fn is (:induction fn).  We
; distinguish between intrinsically suggested inductions and those suggested
; via records of induction-rule type.  Intrinsic inductions have no embodiment
; as induction-rules but are, instead, the basis of the semantics of such
; rules.  That is, the inductions suggested by (fn x y) is the union of those
; suggested by the terms to which it is linked via induction-rules together
; with the intrinsic suggestion for (fn x y).

; Term, above, is a call of some fn with the given formals, quick-block-info,
; justification and induction machine.  We return a list of induction
; candidates, said list either being empty or the singleton list containing the
; induction candidate intrinsically suggested by term.  Xterm is logically
; unrelated to term and is the term appearing in the original conjecture from
; which we (somehow) obtained term for consideration.

  (let ((mask (sound-induction-principle-mask term formals
                                              quick-block-info
                                              (access justification
                                                      justification
                                                      :subset))))
    (cond
     (mask
      (list (flesh-out-induction-principle term formals
                                           justification
                                           mask
                                           machine
                                           xterm
                                           (push-lemma induction-rune
                                                       ttree))))
     (t nil))))

; The following is now defined in rewrite.lisp.

; (defrec induction-rule (nume (pattern . condition) scheme . rune) nil)

(mutual-recursion

(defun apply-induction-rule (rule term type-alist xterm ttree seen ens wrld)

; We apply the induction-rule, rule, to term, and return a possibly empty list
; of suggested inductions.  The basic idea is to check that the rule is enabled
; and that the :pattern of the rule matches term.  If so, we check that the
; :condition of the rule is true under the current type-alist.  This check is
; heuristic only and so we indicate that the guards have been checked and we
; allow forcing.  We ignore the ttree because we are making a heuristic choice
; only.  If type-set says the :condition is non-nil, we fire the rule by
; instantiating the :scheme and recursively getting the suggested inductions
; for that term.  Note that we are not recursively exploring the instantiated
; scheme but just getting the inductions suggested by its top-level function
; symbol.

; Seen is a list of numes of induction-rules already encountered, used in order
; to prevent infinite loops.  The following are two examples that looped before
; the use of this list of numes seen.

; From Daron Vroon:

;  (defun zip1 (xs ys)
;    (declare (xargs :measure (acl2-count xs)))
;    (cond ((endp xs) nil)
;          ((endp ys) nil)
;          (t (cons (cons (car xs) (car ys)) (zip1 (cdr xs) (cdr ys))))))

;  (defun zip2 (xs ys)
;    (declare (xargs :measure (acl2-count ys)))
;    (cond ((endp xs) nil)
;          ((endp ys) nil)
;          (t (cons (cons (car xs) (car ys)) (zip2 (cdr xs) (cdr ys))))))

;  (defthm zip1-zip2-ind
;    t
;    :rule-classes ((:induction :pattern (zip1 xs ys)
;                               :scheme (zip2 xs ys))))

;  (defthm zip2-zip1-ind
;    t
;    :rule-classes ((:induction :pattern (zip2 xs ys)
;                               :scheme (zip1 xs ys))))

;  (defstub foo (*) => *)

;  ;; the following overflows the stack.
;  (thm
;   (= (zip1 (foo xs) ys)
;      (zip2 (foo xs) ys)))

; From Pete Manolios:

;  (defun app (x y)
;    (if (endp x)
;        y
;      (cons (car x) (app (cdr x) y))))

;  (defthm app-ind
;    t
;    :rule-classes ((:induction :pattern (app x y)
;                               :condition (and (true-listp x) (true-listp y))
;                               :scheme (app x y))))

;  (in-theory (disable (:induction app)))

;  (defthm app-associative
;    (implies (and (true-listp a)
;                  (true-listp b)
;                  (true-listp c))
;             (equal (app (app a b) c)
;                    (app a (app b c)))))

  (let ((nume (access induction-rule rule :nume)))
    (cond
     ((and (not (member nume seen))
           (enabled-numep nume ens))
      (mv-let
       (ans alist)
       (one-way-unify (access induction-rule rule :pattern)
                      term)
       (cond
        (ans
         (with-accumulated-persistence
          (access induction-rule rule :rune)
          (suggestions)
          suggestions
          (mv-let
           (ts ttree1)
           (type-set (sublis-var alist
                                 (access induction-rule rule :condition))
                     t nil type-alist ens wrld nil nil nil)
           (declare (ignore ttree1))
           (cond
            ((ts-intersectp *ts-nil* ts) nil)
            (t (let ((term1 (sublis-var alist
                                        (access induction-rule rule :scheme))))
                 (cond ((or (variablep term1)
                            (fquotep term1))
                        nil)
                       (t (suggested-induction-cands term1 type-alist
                                                     xterm
                                                     (push-lemma
                                                      (access induction-rule
                                                              rule
                                                              :rune)
                                                      ttree)
                                                     nil ; eflg
                                                     (cons nume seen)
                                                     ens wrld)))))))))
        (t nil))))
     (t nil))))

(defun suggested-induction-cands1
  (induction-rules term type-alist xterm ttree eflg seen ens wrld)

; We map down induction-rules and apply each enabled rule to term, which is
; known to be an application of the function symbol fn to some args.  Each rule
; gives us a possibly empty list of suggested inductions.  We append all these
; suggestions together.  In addition, if fn is recursively defined and is
; enabled (or, even if fn is disabled if we are exploring a user-supplied
; induction hint) we collect the intrinsic suggestion for term as well.

; Seen is a list of numes of induction-rules already encountered, used in order
; to prevent infinite loops.

; Eflg represents an "enable flag".  When true, an induction rune that
; represents the induction scheme of a recursive definition must be enabled in
; order to be applicable.  When false (nil), it may be applied regardless.

  (cond
   ((null induction-rules)
    (let* ((fn (ffn-symb term))
           (machine (getpropc fn 'induction-machine nil wrld)))
      (cond
       ((null machine) nil)
       (t

; Historical note:  Before Version_2.6 we had the following note:

;   Note: The intrinsic suggestion will be non-nil only if (:INDUCTION fn) is
;   enabled and so here we have a case in which two runes have to be enabled
;   (the :DEFINITION and the :INDUCTION runes) to get the desired effect.  It
;   is not clear if this is a good design but at first sight it seems to
;   provide upward compatibility because in Nqthm a disabled function suggests
;   no inductions.

; We no longer make any such requirement:  the test above (t) replaces the
; following.

;       (or (enabled-fnp fn nil ens wrld)
;           (and induct-hint-val
;                (not (equal induct-hint-val *t*))))
        
        (let ((induction-rune (list :induction (ffn-symb term))))
          (and (or (null eflg)
                   (enabled-runep induction-rune ens wrld))
               (intrinsic-suggested-induction-cand
                induction-rune
                term
                (formals fn wrld)
                (getpropc fn 'quick-block-info
                          '(:error "See SUGGESTED-INDUCTION-CANDS1.")
                          wrld)
                (getpropc fn 'justification
                          '(:error "See SUGGESTED-INDUCTION-CANDS1.")
                          wrld)
                machine
                xterm
                ttree)))))))
   (t (append (apply-induction-rule (car induction-rules)
                                    term type-alist
                                    xterm ttree seen ens wrld)
              (suggested-induction-cands1 (cdr induction-rules)
                                          term type-alist
                                          xterm ttree eflg seen ens wrld)))))

(defun suggested-induction-cands
  (term type-alist xterm ttree eflg seen ens wrld)

; Term is some fn applied to args.  Xterm is some term occurring in the
; conjecture we are exploring and is the term upon which this induction
; suggestion will be "blamed" and from which we have obtained term via
; induction-rules.  We return all of the induction candidates suggested by
; term.  Lambda applications suggest no inductions.  Disabled functions suggest
; no inductions -- unless we are applying the user's induct hint value (in
; which case we, quite reasonably, assume every function in the value is worthy
; of analysis since any function could have been omitted).

; Seen is a list of numes of induction-rules already encountered, used in order
; to prevent infinite loops.

  (cond
   ((flambdap (ffn-symb term)) nil)
   (t (suggested-induction-cands1
       (getpropc (ffn-symb term) 'induction-rules nil wrld)
       term type-alist xterm ttree eflg seen ens wrld))))
)

(mutual-recursion

(defun get-induction-cands (term type-alist ens wrld ans)

; We explore term and accumulate onto ans all of the induction
; candidates suggested by it.

  (cond ((variablep term) ans)
        ((fquotep term) ans)
        ((eq (ffn-symb term) 'hide)
         ans)
        (t (get-induction-cands-lst
            (fargs term)
            type-alist ens wrld
            (append (suggested-induction-cands term type-alist
                                               term nil
                                               t ; eflg
                                               nil ens wrld)
                    ans)))))

(defun get-induction-cands-lst (lst type-alist ens wrld ans)

; We explore the list of terms, lst, and accumulate onto ans all of
; the induction candidates.

  (cond ((null lst) ans)
        (t (get-induction-cands
            (car lst)
            type-alist ens wrld
            (get-induction-cands-lst
             (cdr lst)
             type-alist ens wrld ans)))))

)

(defun get-induction-cands-from-cl-set1 (cl-set ens oncep-override wrld state
                                                ans)

; We explore cl-set and accumulate onto ans all of the induction
; candidates.

  (cond
   ((null cl-set) ans)
   (t (mv-let (contradictionp type-alist fc-pairs)
              (forward-chain-top 'induct
                                 (car cl-set) nil t
                                 nil ; do-not-reconsiderp
                                 wrld ens oncep-override state)

; We need a type-alist with which to compute induction aliases.  It is of
; heuristic use only, so we may as well turn the force-flg on.  We assume no
; contradiction is found.  If by chance one is, then type-alist is nil, which
; is an acceptable type-alist.

              (declare (ignore contradictionp fc-pairs))
              (get-induction-cands-lst
               (car cl-set)
               type-alist ens wrld
               (get-induction-cands-from-cl-set1 (cdr cl-set)
                                                 ens oncep-override wrld state
                                                 ans))))))

(defun get-induction-cands-from-cl-set (cl-set pspv wrld state)

; We explore cl-set and collect all induction candidates.

  (let ((rcnst (access prove-spec-var pspv :rewrite-constant)))
    (get-induction-cands-from-cl-set1 cl-set
                                      (access rewrite-constant
                                              rcnst
                                              :current-enabled-structure)
                                      (access rewrite-constant
                                              rcnst
                                              :oncep-override)
                                      wrld
                                      state
                                      nil)))

; That completes the development of the code for exploring a clause set
; and gathering the induction candidates suggested.

; Section:  Pigeon-Holep

; We next develop pigeon-holep, which tries to fit some "pigeons" into
; some "holes" using a function to determine the sense of the word
; "fit".  Since ACL2 is first-order we can't pass arbitrary functions
; and hence we pass symbols and define our own special-purpose "apply"
; that interprets the particular symbols passed to calls of
; pigeon-holep.

; However, it turns out that the applications of pigeon-holep require
; passing functions that themselves call pigeon-holep.  And so
; pigeon-holep-apply is mutually recursive with pigeon-holep (but only
; because the application functions use pigeon-holep).

(mutual-recursion

(defun pigeon-holep-apply (fn pigeon hole)

; See pigeon-holep for the problem and terminology.  This function
; takes a symbol denoting a predicate and two arguments.  It applies
; the predicate to the arguments.  When the predicate holds we say
; the pigeon argument "fits" into the hole argument.

  (case fn
        (pair-fitp

; This predicate is applied to two pairs, each taken from two substitutions.
; We say (v1 . term1) (the "pigeon") fits into (v2 . term2) (the "hole")
; if v1 is v2 and term1 occurs in term2.

         (and (eq (car pigeon) (car hole))
              (occur (cdr pigeon) (cdr hole))))

        (alist-fitp

; This predicate is applied to two substitutions. We say the pigeon
; alist fits into the hole alist if each pair of the pigeon fits into
; a pair of the hole and no pair of the hole is used more than once.

         (pigeon-holep pigeon hole nil 'pair-fitp))

        (tests-and-alists-fitp

; This predicate is applied to two tests-and-alists records.  The
; first fits into the second if the tests of the first are a subset
; of those of the second and either they are both base cases (i.e., have
; no alists) or each substitution of the first fits into a substitution of
; the second, using no substitution of the second more than once.

         (and (subsetp-equal (access tests-and-alists pigeon :tests)
                             (access tests-and-alists hole :tests))
              (or (and (null (access tests-and-alists pigeon :alists))
                       (null (access tests-and-alists hole :alists)))
                  (pigeon-holep (access tests-and-alists pigeon :alists)
                                (access tests-and-alists hole :alists)
                                nil
                                'alist-fitp))))))

(defun pigeon-holep (pigeons holes filled-holes fn)

; Both pigeons and holes are lists of arbitrary objects.  The holes
; are implicitly enumerated left-to-right from 0.  Filled-holes is a
; list of the indices of holes we consider "filled."  Fn is a
; predicate known to pigeon-holep-apply.  If fn applied to a pigeon and
; a hole is non-nil, then we say the pigeon "fits" into the hole.  We
; can only "put" a pigeon into a hole if the hole is unfilled and the
; pigeon fits.  The act of putting the pigeon into the hole causes the
; hole to become filled.  We return t iff it is possible to put each
; pigeon into a hole under these rules.

  (cond
   ((null pigeons) t)
   (t (pigeon-holep1 (car pigeons)
                     (cdr pigeons)
                     holes 0
                     holes filled-holes fn))))

(defun pigeon-holep1 (pigeon pigeons lst n holes filled-holes fn)

; Lst is a terminal sublist of holes, whose first element has index n.
; We map over lst looking for an unfilled hole h such that (a) we can
; put pigeon into h and (b) we can dispose of the rest of the pigeons
; after filling h.

  (cond
   ((null lst) nil)
   ((member n filled-holes)
    (pigeon-holep1 pigeon pigeons (cdr lst) (1+ n) holes filled-holes fn))
   ((and (pigeon-holep-apply fn pigeon (car lst))
         (pigeon-holep pigeons holes
                       (cons n filled-holes)
                       fn))
    t)
   (t (pigeon-holep1 pigeon pigeons (cdr lst) (1+ n)
                     holes filled-holes fn))))

)

(defun flush-cand1-down-cand2 (cand1 cand2)

; This function takes two induction candidates and determines whether
; the first is subsumed by the second.  If so, it constructs a new
; candidate that is logically equivalent (vis a vis the induction
; suggested) to the second but which now carries with it the weight
; and heuristic burdens of the first.

  (cond
   ((and (subsetp-eq (access candidate cand1 :changed-vars)
                     (access candidate cand2 :changed-vars))
         (subsetp-eq (access candidate cand1 :unchangeable-vars)
                     (access candidate cand2 :unchangeable-vars))
         (pigeon-holep (access candidate cand1 :tests-and-alists-lst)
                       (access candidate cand2 :tests-and-alists-lst)
                       nil
                       'tests-and-alists-fitp))
    (change candidate cand2
            :score (+ (access candidate cand1 :score)
                      (access candidate cand2 :score))
            :controllers (union-eq (access candidate cand1 :controllers)
                                   (access candidate cand2 :controllers))
            :other-terms (add-to-set-equal
                          (access candidate cand1 :induction-term)
                          (union-equal
                           (access candidate cand1 :other-terms)
                           (access candidate cand2 :other-terms)))
            :xother-terms (add-to-set-equal
                           (access candidate cand1 :xinduction-term)
                           (union-equal
                            (access candidate cand1 :xother-terms)
                            (access candidate cand2 :xother-terms)))
            :ttree (cons-tag-trees (access candidate cand1 :ttree)
                                   (access candidate cand2 :ttree))))
   (t nil)))

(defun flush-candidates (cand1 cand2)

; This function determines whether one of the two induction candidates
; given flushes down the other and if so returns the appropriate
; new candidate.  This function is a mate and merge function used
; by m&m and is hence known to m&m-apply.

  (or (flush-cand1-down-cand2 cand1 cand2)
      (flush-cand1-down-cand2 cand2 cand1)))

; We now begin the development of the merging of two induction
; candidates.  The basic idea is that if two functions both replace x
; by x', and one of them simultaneously replaces a by a' while the
; other replaces b by b', then we should consider inducting on x, a,
; and b, by x', a', and b'.  Of course, by the time we get here, the
; recursion is coded into substitution alists: ((x . x') (a . a')) and
; ((x . x') (b . b')).  We merge these two alists into ((x . x') (a .
; a') (b . b')).  The merge of two sufficiently compatible alists is
; accomplished by just unioning them together.

; The key ideas are (1) recognizing when two alists are describing the
; "same" recursive step (i.e., they are both replacing x by x', where
; x is somehow a key variable); (2) observing that they do not
; explicitly disagree on what to do with the other variables.

(defun alists-agreep (alist1 alist2 vars)

; Two alists agree on vars iff for each var in vars the image of var under
; the first alist is equal to that under the second.

  (cond ((null vars) t)
        ((equal (let ((temp (assoc-eq (car vars) alist1)))
                  (cond (temp (cdr temp))(t (car vars))))
                (let ((temp (assoc-eq (car vars) alist2)))
                  (cond (temp (cdr temp))(t (car vars)))))
         (alists-agreep alist1 alist2 (cdr vars)))
        (t nil)))

(defun irreconcilable-alistsp (alist1 alist2)

; Two alists are irreconcilable iff there is a var v that they both
; explicitly map to different values.  Put another way, there exists a
; v such that (v . a) is a member of alist1 and (v . b) is a member of
; alist2, where a and b are different.  If two substitutions are
; reconcilable then their union is a substitution.

; We rely on the fact that this function return t or nil.

  (cond ((null alist1) nil)
        (t (let ((temp (assoc-eq (caar alist1) alist2)))
             (cond ((null temp)
                    (irreconcilable-alistsp (cdr alist1) alist2))
                   ((equal (cdar alist1) (cdr temp))
                    (irreconcilable-alistsp (cdr alist1) alist2))
                   (t t))))))

(defun affinity (aff alist1 alist2 vars)

; We say two alists that agree on vars but are irreconcilable are
; "antagonists".  Two alists that agree on vars and are not irreconcilable
; are "mates".

; Aff is either 'antagonists or 'mates and denotes one of the two relations
; above.  We return t iff the other args are in the given relation.

  (and (alists-agreep alist1 alist2 vars)
       (eq (irreconcilable-alistsp alist1 alist2)
           (eq aff 'antagonists))))

(defun member-affinity (aff alist alist-lst vars)

; We determine if some member of alist-lst has the given affinity with alist.

  (cond ((null alist-lst) nil)
        ((affinity aff alist (car alist-lst) vars)
         t)
        (t (member-affinity aff alist (cdr alist-lst) vars))))

(defun occur-affinity (aff alist lst vars)

; Lst is a list of tests-and-alists.  We determine whether alist has
; the given affinity with some alist in lst.  We call this occur
; because we are looking inside the elements of lst.  But it is
; technically a misnomer because we don't look inside recursively; we
; treat lst as though it were a list of lists.

  (cond
   ((null lst) nil)
   ((member-affinity aff alist
                     (access tests-and-alists (car lst) :alists)
                     vars)
    t)
   (t (occur-affinity aff alist (cdr lst) vars))))

(defun some-occur-affinity (aff alists lst vars)

; Lst is a list of tests-and-alists.  We determine whether some alist
; in alists has the given affinity with some alist in lst.

  (cond ((null alists) nil)
        (t (or (occur-affinity aff (car alists) lst vars)
               (some-occur-affinity aff (cdr alists) lst vars)))))

(defun all-occur-affinity (aff alists lst vars)

; Lst is a list of tests-and-alists.  We determine whether every alist
; in alists has the given affinity with some alist in lst.

  (cond ((null alists) t)
        (t (and (occur-affinity aff (car alists) lst vars)
                (all-occur-affinity aff (cdr alists) lst vars)))))

(defun contains-affinity (aff lst vars)

; We determine if two members of lst have the given affinity.

  (cond ((null lst) nil)
        ((member-affinity aff (car lst) (cdr lst) vars) t)
        (t (contains-affinity aff (cdr lst) vars))))

; So much for general-purpose scanners.  We now develop the predicates
; that are used to determine if we can merge lst1 into lst2 on vars.
; See merge-tests-and-alists-lsts for extensive comments on the ideas
; behind the following functions.

(defun antagonistic-tests-and-alists-lstp (lst vars)

; Lst is a list of tests-and-alists.  Consider just the set of all
; alists in lst.  We return t iff that set contains an antagonistic
; pair.

; We operate as follows.  Each element of lst contains some alists.
; We take the first element and ask whether its alists contain an
; antagonistic pair.  If so, we're done.  Otherwise, we ask whether
; any alist in that first element is antagonistic with the alists in
; the rest of lst.  If so, we're done.  Otherwise, we recursively
; look at the rest of lst.

  (cond
   ((null lst) nil)
   (t (or (contains-affinity
           'antagonists
           (access tests-and-alists (car lst) :alists)
           vars)
          (some-occur-affinity
           'antagonists
           (access tests-and-alists (car lst) :alists)
           (cdr lst)
           vars)
          (antagonistic-tests-and-alists-lstp (cdr lst) vars)))))

(defun antagonistic-tests-and-alists-lstsp (lst1 lst2 vars)

; Both lst1 and lst2 are lists of tests-and-alists.  We determine whether
; there exists an alist1 in lst1 and an alist2 in lst2 such that alist1
; and alist2 are antagonists.

  (cond
   ((null lst1) nil)
   (t (or (some-occur-affinity
           'antagonists
           (access tests-and-alists (car lst1) :alists)
           lst2
           vars)
          (antagonistic-tests-and-alists-lstsp (cdr lst1) lst2 vars)))))

(defun every-alist1-matedp (lst1 lst2 vars)

; Both lst1 and lst2 are lists of tests-and-alists.  We determine for every
; alist1 in lst1 there exists an alist2 in lst2 that agrees with alist1 on
; vars and that is not irreconcilable.

  (cond ((null lst1) t)
        (t (and (all-occur-affinity
                 'mates
                 (access tests-and-alists (car lst1) :alists)
                 lst2
                 vars)
                (every-alist1-matedp (cdr lst1) lst2 vars)))))

; The functions above are used to determine that lst1 and lst2 contain
; no antagonistic pairs, that every alist in lst1 has a mate somewhere in
; lst2, and that the process of merging alists from lst1 with their
; mates will not produce alists that are antagonistic with other alists
; in lst1.  We now develop the code for merging non-antagonistic alists
; and work up the structural hierarchy to merging lists of tests and alists.

(defun merge-alist1-into-alist2 (alist1 alist2 vars)

; We assume alist1 and alist2 are not antagonists.  Thus, either they
; agree on vars and have no explicit disagreements, or they simply
; don't agree on vars.  If they agree on vars, we merge alist1 into
; alist2 by just unioning them together.  If they don't agree on vars,
; then we merge alist1 into alist2 by ignoring alist1.

  (cond
   ((alists-agreep alist1 alist2 vars)
    (union-equal alist1 alist2))
   (t alist2)))

; Now we begin working up the structural hierarchy.  Our strategy is
; to focus on a given alist2 and hit it with every alist1 we have.
; Then we'll use that to copy lst2 once, hitting each alist2 in it
; with everything we have.  We could decompose the problem the other
; way: hit lst2 with successive alist1's.  That suffers from forcing
; us to copy lst2 repeatedly, and there are parts of that structure
; (i.e., the :tests) that don't change.

(defun merge-alist1-lst-into-alist2 (alist1-lst alist2 vars)

; Alist1-lst is a list of alists and alist2 is an alist.  We know that
; there is no antagonists between the elements of alist1-lst and in
; alist2.  We merge each alist1 into alist2 and return
; the resulting extension of alist2.

  (cond
   ((null alist1-lst) alist2)
   (t (merge-alist1-lst-into-alist2
       (cdr alist1-lst)
       (merge-alist1-into-alist2 (car alist1-lst) alist2 vars)
       vars))))

(defun merge-lst1-into-alist2 (lst1 alist2 vars)

; Given a list of tests-and-alists, lst1, and an alist2, we hit alist2
; with every alist1 in lst1.

  (cond ((null lst1) alist2)
        (t (merge-lst1-into-alist2
            (cdr lst1)
            (merge-alist1-lst-into-alist2
             (access tests-and-alists (car lst1) :alists)
             alist2
             vars)
            vars))))

; So now we write the code to copy lst2, hitting each alist in it with lst1.

(defun merge-lst1-into-alist2-lst (lst1 alist2-lst vars)
  (cond ((null alist2-lst) nil)
        (t (cons (merge-lst1-into-alist2 lst1 (car alist2-lst) vars)
                 (merge-lst1-into-alist2-lst lst1 (cdr alist2-lst) vars)))))

(defun merge-lst1-into-lst2 (lst1 lst2 vars)
  (cond ((null lst2) nil)
        (t (cons (change tests-and-alists (car lst2)
                         :alists
                         (merge-lst1-into-alist2-lst
                          lst1
                          (access tests-and-alists (car lst2) :alists)
                          vars))
                 (merge-lst1-into-lst2 lst1 (cdr lst2) vars)))))

(defun merge-tests-and-alists-lsts (lst1 lst2 vars)

; Lst1 and lst2 are each tests-and-alists-lsts from some induction
; candidates.  Intuitively, we try to stuff the alists of lst1 into
; those of lst2 to construct a new lst2 that combines the induction
; schemes of both.  If we fail we return nil.  Otherwise we return the
; modified lst2.  The modified lst2 has exactly the same tests as
; before; only its alists are different and they are different only by
; virtue of having been extended with some addition pairs.  So the
; justification of the merged induction is the same as the
; justification of the original lst2.

; Given an alist1 from lst1, which alist2's of lst2 do you extend and
; how?  Suppose alist1 maps x to x' and y to y'.  Then intuitively we
; think "the first candidate is trying to keep x and y in step, so
; that when x goes to x' y goes to y'."  So, if you see an alist in
; lst2 that is replacing x by x', one might be tempted to augment it
; by replacing y by y'.  However, what if x is just an accumulator?
; The role of vars is to specify upon which variables two
; substitutions must agree in order to be merged.  Usually, vars
; consists of the measured variables.

; So now we get a little more technical.  We will try to "merge" each
; alist1 from lst1 into each alist2 from lst2 (preserving the case structure
; of lst2).  If alist1 and alist2 do not agree on vars then their merge
; is just alist2.  If they do agree on vars, then their merge is their
; union, provided that is a substitution.  It may fail to be a substitution
; because the two alists disagree on some other variable.  In that case
; we say the two are irreconcilable.  We now give three simple examples:

; Let vars be {x}.  Let alist2 be {(x . x') (z . z')}.  If alist1 maps
; x to x'', then their merge is just alist2 because alist1 is
; addressing a different case of the induction.  If alist1 maps x to x'
; and y to y', then their merge is {(x . x') (y . y') (z . z')}.  If
; alist1 maps x to x' and z to z'', then the two are irreconcilable.
; Two irreconcilable alists that agree on vars are called "antagonists"
; because they "want" to merge but can't.  We cannot merge lst1 into lst2
; if they have an antagonistic pair between them.  If an antagonistic pair
; is discovered, the entire merge operation fails.

; Now we will successively consider each alist1 in lst1 and merge it
; into lst2, forming successive lst2's.  We insist that each alist1 of
; lst1 have at least one mate in lst2 with which it agrees and is
; reconcilable.  (Otherwise, we could merge completely disjoint
; substitutions.)

; Because we try the alist1's successively, each alist1 is actually
; merged into the lst2 produced by all the previous alist1's.  That
; produces an apparent order dependence.  However, this is avoided by
; the requirement that we never produce antagonistic pairs.

; For example, suppose that in one case of lst1, x is mapped to x' and
; y is mapped to y', but in another case x is mapped to x' and y is
; mapped to y''.  Now imagine trying to merge that lst1 into a lst2 in
; which x is mapped to x' and z is mapped to z'.  The first alist of
; lst1 extends lst2 to (((x . x') (y . y') (z . z'))).  But the second
; alist is then antagonistic.  The same thing happens if we tried the two
; alists of lst1 in the other order.  Thus, the above lst1 cannot be merged
; into lst2.  Note that they can be merged in the other order!  That is,
; lst2 can be merged into lst1, because the case structure of lst1 is
; richer.

; We can detect the situation above without forming the intermediate
; lst2.  In particular, if lst1 contains an antagonistic pair, then it
; cannot be merged with any lst2 and we can quit.

; Note: Once upon a time, indeed, for the first 20 years or so of the
; existence of the merge routine, we took the attitude that if
; irreconcilable but agreeable alists arose, then we just added to
; alist2 those pairs of alist1 that were reconcilable and we left out
; the irreconcilable pairs.  This however resulted in the system often
; merging complicated accumulator using functions (like TAUTOLOGYP)
; into simpler functions (like NORMALIZEDP) by dropping the
; accumulators that got in the way.  This idea of just not doing
; "hostile merges" is being tried out for the first time in ACL2.

  (cond ((antagonistic-tests-and-alists-lstp lst1 vars) nil)
        ((antagonistic-tests-and-alists-lstsp lst1 lst2 vars) nil)
        ((not (every-alist1-matedp lst1 lst2 vars)) nil)
        (t (merge-lst1-into-lst2 lst1 lst2 vars))))

(defun merge-cand1-into-cand2 (cand1 cand2)

; Can induction candidate cand1 be merged into cand2?  If so, return
; their merge.  The guts of this function is merge-tests-and-alists-
; lsts.  The tests preceding it are heuristic only.  If
; merge-tests-and-alists-lsts returns non-nil, then it returns a sound
; induction; indeed, it merely extends some of the substitutions in
; the second candidate.

  (let ((vars (or (intersection-eq
                   (access candidate cand1 :controllers)
                   (intersection-eq
                    (access candidate cand2 :controllers)
                    (intersection-eq
                     (access candidate cand1 :changed-vars)
                     (access candidate cand2 :changed-vars))))
                  (intersection-eq
                   (access candidate cand1 :changed-vars)
                   (access candidate cand2 :changed-vars)))))

; Historical Plaque from Nqthm:

; We once merged only if both cands agreed on the intersection of the
; changed-vars.  But the theorem that, under suitable conditions, (EV
; FLG X VA FA N) = (EV FLG X VA FA K) made us realize it was important
; only to agree on the intersection of the controllers.  Note in fact
; that we mean the changing controllers -- there seems to be no need
; to merge two inductions if they only share unchanging controllers.
; However the theorem that (GET I (SET J VAL MEM)) = ... (GET I MEM)
; ...  illustrates the situation in which the controllers, {I} and {J}
; do not even overlap; but the accumulators {MEM} do and we want a
; merge.  So we want agreement on the intersection of the changing
; controllers (if that is nonempty) or on the accumulators.

; For soundness it does not matter what list of vars we want to agree
; on because no matter what, merge-tests-and-alists-lsts returns
; either nil or an extension of the second candidate's alists.

    (cond
     ((and vars
           (not (intersectp-eq (access candidate cand1 :unchangeable-vars)
                               (access candidate cand2 :changed-vars)))
           (not (intersectp-eq (access candidate cand2 :unchangeable-vars)
                               (access candidate cand1 :changed-vars))))
      (let ((temp (merge-tests-and-alists-lsts
                   (access candidate cand1 :tests-and-alists-lst)
                   (access candidate cand2 :tests-and-alists-lst)
                   vars)))
        (cond (temp
               (make candidate
                     :score (+ (access candidate cand1 :score)
                               (access candidate cand2 :score))
                     :controllers (union-eq
                                   (access candidate cand1 :controllers)
                                   (access candidate cand2 :controllers))
                     :changed-vars (union-eq
                                    (access candidate cand1 :changed-vars)
                                    (access candidate cand2 :changed-vars))
                     :unchangeable-vars (union-eq
                                         (access candidate cand1
                                                 :unchangeable-vars)
                                         (access candidate cand2
                                                 :unchangeable-vars))
                     :tests-and-alists-lst temp
                     :justification (access candidate cand2 :justification)
                     :induction-term (access candidate cand2 :induction-term)
                     :other-terms (add-to-set-equal
                                   (access candidate cand1 :induction-term)
                                   (union-equal
                                    (access candidate cand1 :other-terms)
                                    (access candidate cand2 :other-terms)))
                     :xinduction-term (access candidate cand2 :xinduction-term)
                     :xother-terms (add-to-set-equal
                                    (access candidate cand1 :xinduction-term)
                                    (union-equal
                                     (access candidate cand1 :xother-terms)
                                     (access candidate cand2 :xother-terms)))
                     :xancestry (cond
                                ((equal temp
                                        (access candidate cand2
                                                :tests-and-alists-lst))
                                 (access candidate cand2 :xancestry))
                                (t (add-to-set-equal
                                    (access candidate cand1 :xinduction-term)
                                    (union-equal
                                     (access candidate cand1 :xancestry)
                                     (access candidate cand2 :xancestry)))))

; Note that :xancestry, computed just above, may not reflect cand1, but we
; always include the :ttree of cand1 just below.  This is deliberate, since
; cand1 is contributing to the :score, and hence the eventual induction scheme
; chosen; so we want to report its induction rules in the final proof.

                     :ttree (cons-tag-trees (access candidate cand1 :ttree)
                                            (access candidate cand2 :ttree))))
              (t nil))))
     (t nil))))

(defun merge-candidates (cand1 cand2)

; This function determines whether one of the two induction candidates
; can be merged into the other.  If so, it returns their merge.  This
; function is a mate and merge function used by m&m and is hence known
; to m&m-apply.

  (or (merge-cand1-into-cand2 cand1 cand2)
      (merge-cand1-into-cand2 cand2 cand1)))

; We now move from merging to flawing.  The idea is to determine which
; inductions get in the way of others.



(defun controller-variables1 (args controller-pocket)

; Controller-pocket is a list of t's and nil's in 1:1 correspondence with
; args, indicating which args are controllers.  We collect those controller
; args that are variable symbols.

  (cond ((null controller-pocket) nil)
        ((and (car controller-pocket)
              (variablep (car args)))
         (add-to-set-eq (car args)
                        (controller-variables1 (cdr args)
                                               (cdr controller-pocket))))
        (t (controller-variables1 (cdr args)
                                  (cdr controller-pocket)))))

(defun controller-variables (term controller-alist)

; Controller-alist comes from the def-body of the function symbol, fn, of term.
; Recall that controller-alist is an alist that associates with each function
; in fn's mutually recursive clique the controller pockets used in a given
; justification of the clique.  In induction, as things stand today, we know
; that fn is singly recursive because we don't know how to handle mutual
; recursion yet.  But no use is made of that here.  We collect all the
; variables in controller slots of term.

  (controller-variables1 (fargs term)
                         (cdr (assoc-eq (ffn-symb term)
                                        controller-alist))))

(defun induct-vars1 (lst wrld)

; Lst is a list of terms.  We collect every variable symbol occurring in a
; controller slot of any term in lst.

  (cond ((null lst) nil)
        (t (union-eq
            (controller-variables
             (car lst)
             (access def-body
                     (def-body (ffn-symb (car lst)) wrld)
                     :controller-alist))
            (induct-vars1 (cdr lst) wrld)))))

(defun induct-vars (cand wrld)

; Historical Plaque from Nqthm:

;   Get all skos occupying controller slots in any of the terms associated
;   with this candidate.

; The age of that comment is not known, but the fact that we referred
; to the variables as "skos" (Skolem constants) suggests that it may
; date from the Interlisp version.  Meta comment: Perhaps someday some
; enterprising PhD student (in History?) will invent Software
; Archaeology, in which decrepit fragments of archive tapes are pieced
; together and scrutinized for clues as to the way people thought back
; in the early days.

  (induct-vars1 (cons (access candidate cand :induction-term)
                      (access candidate cand :other-terms))
                wrld))

(defun vetoedp (cand vars lst changed-vars-flg)

; Vars is a list of variables.  We return t iff there exists a candidate
; in lst, other than cand, whose unchangeable-vars (or, if changed-vars-flg,
; changed-vars or unchangeable-vars) intersect with vars.

; This function is used both by compute-vetoes1, where flg is t and
; vars is the list of changing induction vars of cand, and by
; compute-vetoes2, where flg is nil and vars is the list of
; changed-vars cand.  We combine these two into one function simply to
; eliminate a definition from the system.

  (cond ((null lst) nil)
        ((equal cand (car lst))
         (vetoedp cand vars (cdr lst) changed-vars-flg))
        ((and changed-vars-flg
              (intersectp-eq vars
                             (access candidate (car lst) :changed-vars)))
         t)
        ((intersectp-eq vars
                        (access candidate (car lst) :unchangeable-vars))
         t)
        (t (vetoedp cand vars (cdr lst) changed-vars-flg))))

(defun compute-vetoes1 (lst cand-lst wrld)

; Lst is a tail of cand-lst.  We throw out from lst any candidate
; whose changing induct-vars intersect the changing or unchanging vars
; of another candidate in cand-lst.  We assume no two elements of
; cand-lst are equal, an invariant assured by the fact that we have
; done merging and flushing before this.

  (cond ((null lst) nil)
        ((vetoedp (car lst)
                  (intersection-eq
                   (access candidate (car lst) :changed-vars)
                   (induct-vars (car lst) wrld))
                  cand-lst
                  t)
         (compute-vetoes1 (cdr lst) cand-lst wrld))
        (t (cons (car lst)
                 (compute-vetoes1 (cdr lst) cand-lst wrld)))))

; If the first veto computation throws out all candidates, we revert to
; another heuristic.

(defun compute-vetoes2 (lst cand-lst)

; Lst is a tail of cand-lst.  We throw out from lst any candidate
; whose changed-vars intersect the unchangeable-vars of another
; candidate in cand-lst.  Again, we assume no two elements of cand-lst
; are equal.

  (cond ((null lst) nil)
        ((vetoedp (car lst)
                  (access candidate (car lst) :changed-vars)
                  cand-lst
                  nil)
         (compute-vetoes2 (cdr lst) cand-lst))
        (t (cons (car lst)
                 (compute-vetoes2 (cdr lst) cand-lst)))))

(defun compute-vetoes (cand-lst wrld)

; We try two different techniques for throwing out candidates.  If the
; first throws out everything, we try the second.  If the second throws
; out everything, we throw out nothing.

; The two are: (1) throw out a candidate if its changing induct-vars
; (the variables in control slots that change) intersect with either
; the changed-vars or the unchangeable-vars of another candidate.  (2)
; throw out a candidate if its changed-vars intersect the
; unchangeable-vars of another candidate.

; Historical Plaque from Nqthm:

;   This function weeds out "unclean" induction candidates.  The
;   intuition behind the notion "clean" is that an induction is clean
;   if nobody is competing with it for instantiation of its variables.
;   What we actually do is throw out any candidate whose changing
;   induction variables -- that is the induction variables as computed
;   by induct-vars intersected with the changed vars of candidate --
;   intersect the changed or unchanged variables of another candidate.
;   The reason we do not care about the first candidates unchanging
;   vars is as follows.  The reason you want a candidate clean is so
;   that the terms riding on that cand will reoccur in both the
;   hypothesis and conclusion of an induction.  There are two ways to
;   assure (or at least make likely) this: change the variables in the
;   terms as specified or leave them constant.  Thus, if the first
;   cand's changing vars are clean but its unchanging vars intersect
;   another cand it means that the first cand is keeping those other
;   terms constant, which is fine. (Note that the first cand would be
;   clean here.  The second might be clean or dirty depending on
;   whether its changed vars or unchanged vars intersected the first
;   cand's vars.)  The reason we check only the induction vars and not
;   all of the changed vars is if cand1's changed vars include some
;   induction vars and some accumulators and the accumulators are
;   claimed by another cand2 we believe that cand1 is still clean.
;   The motivating example was

;   (IMPLIES (MEMBER A C) (MEMBER A (UNION1 B C)))

;   where the induction on C is dirty because the induction on B and C
;   claims C, but the induction on B and C is clean because the B does
;   not occur in the C induction.  We do not even bother to check the
;   C from the (B C) induction because since it is necessarily an
;   accumulator it is probably being constructed and thus, if it
;   occurs in somebody else's ind vars it is probably being eaten so
;   it will be ok.  In formulating this heuristic we did not consider
;   the possibility that the accums of one candidate occur as
;   constants in the other.  Oh well.

;   July 20, 1978.  We have added an additional heuristic, to be
;   applied if the above one eliminates all cands.  We consider a cand
;   flawed if it changes anyone else's constants.  The motivating
;   example was GREATEST-FACTOR-LESSP -- which was previously proved
;   only by virtue of a very ugly use of the no-op fn ID to make a
;   certain induction flawed.

  (or (compute-vetoes1 cand-lst cand-lst wrld)
      (compute-vetoes2 cand-lst cand-lst)
      cand-lst))

; The next heuristic is to select complicated candidates, based on
; support for non-primitive recursive function schemas.

(defun induction-complexity1 (lst wrld)

; The "function" induction-complexity does not exist.  It is a symbol
; passed to maximal-elements-apply which calls this function on the list
; of terms supported by an induction candidate.  We count the number of
; non pr fns supported.

  (cond ((null lst) 0)
        ((getpropc (ffn-symb (car lst)) 'primitive-recursive-defunp nil wrld)
         (induction-complexity1 (cdr lst) wrld))
        (t (1+ (induction-complexity1 (cdr lst) wrld)))))

; We develop a general-purpose function for selecting maximal elements from
; a list under a measure.  That function, maximal-elements, is then used
; with the induction-complexity measure to collect both the most complex
; inductions and then to select those with the highest scores.

(defun maximal-elements-apply (fn x wrld)

; This function must produce an integerp.  This is just the apply function
; for maximal-elements.

  (case fn
        (induction-complexity
         (induction-complexity1 (cons (access candidate x :induction-term)
                                      (access candidate x :other-terms))
                                wrld))
        (score (access candidate x :score))
        (otherwise 0)))

(defun maximal-elements1 (lst winners maximum fn wrld)

; We are scanning down lst collecting into winners all those elements
; with maximal scores as computed by fn.  Maximum is the maximal score seen
; so far and winners is the list of all the elements passed so far with
; that score.

  (cond ((null lst) winners)
        (t (let ((temp (maximal-elements-apply fn (car lst) wrld)))
             (cond ((> temp maximum)
                    (maximal-elements1 (cdr lst)
                                       (list (car lst))
                                       temp fn wrld))
; PETE
; In other versions the = below is, mistakenly, an int=!

                   ((= temp maximum)
                    (maximal-elements1 (cdr lst)
                                       (cons (car lst) winners)
                                       maximum fn wrld))
                   (t
                    (maximal-elements1 (cdr lst)
                                       winners
                                       maximum fn wrld)))))))

(defun maximal-elements (lst fn wrld)

; Return the subset of lst that have the highest score as computed by
; fn.  The functional parameter fn must be known to maximal-elements-apply.
; We reverse the accumulated elements to preserve the order used by
; nqthm.

  (cond ((null lst) nil)
        ((null (cdr lst)) lst)
        (t (reverse
            (maximal-elements1 (cdr lst)
                               (list (car lst))
                               (maximal-elements-apply fn (car lst) wrld)
                               fn wrld)))))


; All that is left in the heuristic selection of the induction candidate is
; the function m&m that mates and merges arbitrary objects.  We develop that
; now.

; The following three functions are not part of induction but are
; used by other callers of m&m and so have to be introduced now
; so we can define m&m-apply and get on with induct.

(defun intersectp-eq/union-equal (x y)
  (cond ((intersectp-eq (car x) (car y))
         (cons (union-eq (car x) (car y))
               (union-equal (cdr x) (cdr y))))
        (t nil)))

(defun equal/union-equal (x y)
  (cond ((equal (car x) (car y))
         (cons (car x)
               (union-equal (cdr x) (cdr y))))
        (t nil)))

(defun subsetp-equal/smaller (x y)
  (cond ((subsetp-equal x y) x)
        ((subsetp-equal y x) y)
        (t nil)))

(defun m&m-apply (fn x y)

; This is a first-order function that really just applies fn to x and
; y, but does so only for a fixed set of fns.  In fact, this function
; handles exactly those functions that we give to m&m.

  (case fn
        (intersectp-eq/union-equal (intersectp-eq/union-equal x y))
        (equal/union-equal (equal/union-equal x y))
        (flush-candidates (flush-candidates x y))
        (merge-candidates (merge-candidates x y))
        (subsetp-equal/smaller (subsetp-equal/smaller x y))))

(defun count-off (n lst)

; Pair the elements of lst with successive integers starting at n.

  (cond ((null lst) nil)
        (t (cons (cons n (car lst))
                 (count-off (1+ n) (cdr lst))))))

(defun m&m-search (x y-lst del fn)

; Y-lst is a list of pairs, (id . y).  The ids are integers.  If id is
; a member of del, we think of y as "deleted" from y-lst.  That is,
; y-lst and del together characterize a list of precisely those y such
; that (id . y) is in y-lst and id is not in del.

; We search y-lst for the first y that is not deleted and that mates
; with x.  We return two values, the merge of x and y and the integer
; id of y.  If no such y exists, return two nils.

  (cond ((null y-lst) (mv nil nil))
        ((member (caar y-lst) del)
         (m&m-search x (cdr y-lst) del fn))
        (t (let ((z (m&m-apply fn x (cdar y-lst))))
             (cond (z (mv z (caar y-lst)))
                   (t (m&m-search x (cdr y-lst) del fn)))))))

(defun m&m1 (pairs del ans n fn)

; This is workhorse for m&m.  See that fn for a general description of
; the problem and the terminology.  Pairs is a list of pairs.  The car
; of each pair is an integer and the cdr is a possible element of the
; bag we are closing under fn.  Del is a list of the integers
; identifying all the elements of pairs that have already been
; deleted.  Abstractly, pairs and del together represent a bag we call
; the "unprocessed bag".  The elements of the unprocessed bag are
; precisely those ele such that (i . ele) is in pairs and i is not in
; del.

; Without assuming any properties of fn, this function can be
; specified as follows: If the first element, x, of the unprocessed
; bag, mates with some y in the rest of the unprocessed bag, then put
; the merge of x and the first such y in place of x, delete that y,
; and iterate.  If the first element has no such mate, put it in the
; answer accumulator ans.  N, by the way, is the next available unique
; identifier integer.

; If one is willing to make the assumptions that the mate and merge
; fns of fn are associative and commutative and have the distributive
; and non-preclusion properties, then it is possible to say more about
; this function.  The rest of this comment makes those assumptions.

; Ans is a bag with the property that no element of ans mates with any
; other element of ans or with any element of the unprocessed bag.  N
; is the next available unique identifier integer; it is always larger
; than any such integer in pairs or in del.

; Abstractly, this function closes B under fn, where B is the bag
; union of the unprocessed bag and ans.

  (cond
   ((null pairs) ans)
   ((member (caar pairs) del)
    (m&m1 (cdr pairs) del ans n fn))
   (t (mv-let (mrg y-id)
        (m&m-search (cdar pairs) (cdr pairs) del fn)
        (cond
         ((null mrg)
          (m&m1 (cdr pairs)
                del
                (cons (cdar pairs) ans)
                n fn))
         (t (m&m1 (cons (cons n mrg) (cdr pairs))
                  (cons y-id del)
                  ans
                  (1+ n)
                  fn)))))))

(defun m&m (bag fn)

; This function takes a bag and a symbol naming a dyadic function, fn,
; known to m&m-apply and about which we assume certain properties
; described below.  Let z be (m&m-apply fn x y).  Then we say x and y
; "mate" if z is non-nil.  If x and y mate, we say z is the "merge" of
; x and y.  The name of this function abbreviates the phrase "mate and
; merge".

; We consider each element, x, of bag in turn and seek the first
; successive element, y, that mates with it.  If we find one, we throw
; out both, add their merge in place of x and iterate.  If we find no
; mate for x, we deposit it in our answer accumulator.

; The specification above is explicit about the order in which we try
; the elements of the bag.  If we try to loosen the specification so
; that order is unimportant, we must require that fn have certain
; properties.  We discuss this below.

; First, note that we have implicitly assumed that mate and merge are
; commutative because we haven't said in which order we present the
; arguments.

; Second, note that if x doesn't mate with any y, we set it aside in
; our accumulating answer.  We do not even try to mate such an x with
; the offspring of the y's it didn't like.  This makes us order
; dependent.  For example, consider the bag {x y1 y2}.  Suppose x
; won't mate with either y1 or y2, but that y1 mates with y2 to
; produce y3 and x mates with y3 to produce y4.  Then if we seek mates
; for x first we find none and it gets into our final answer.  Then y1
; and y2 mate to form y3.  The final answer is hence {x y3}.  But if
; we seek mates for y1 first we find y2, produce y3, add it to the
; bag, forming {y3 x}, and then mate x with y3 to get the final answer
; {y4}.  This order dependency cannot arise if fn has the property
; that if x mates with the merge of y and z then x mates with either y
; or z.  This is called the "distributive" property of mate over merge.

; Third, note that if x does mate with y to produce z then we throw x
; out in favor of z.  Thus, x is not mated against any but the first
; y.  Thus, if we have {x y1 y2} and x mates with y1 to form z1 and x
; mates with y2 to form z2 and there are no other mates, then we can
; either get {z1 y2} or {z2 y1} as the final bag, depending on whether
; we mate x with y1 or y2.  This order dependency cannot arise if fn
; has the property that if x mates with y1 and x mates with y2, then
; (a) the merge of x and y1 mates with y2, and (b) merge has the
; "commutativity-2" (merge (merge x y1) y2) = (merge (merge x y2) y1).
; We call property (a) "non-preclusion" property of mate and merge,
; i.e., merging doesn't preclude mating.

; The commutativity-2 property is implied by associativity and (the
; already assumed commutativity).  Thus, another way to avoid the
; third order dependency is if legal merges are associative and have
; the non-preclusion property.

; Important Note: The commonly used fn of unioning together two alists
; that agree on the intersection of their domains, does not have the
; non-preclusion property!  Suppose x, y1, and y2 are all alists and
; all map A to 0.  Suppose in addition y1 maps B to 1 but y2 maps B to
; 2.  Finally, suppose x maps C to 3.  Then x mates with both y1 and
; y2.  But merging y1 into x precludes mating with y2 and vice versa.

; We claim, but do not prove, that if the mate and merge functions for
; fn are commutative and associative, and have the distributive and
; non-preclusion properties, then m&m is order independent.

; For efficiency we have chosen to implement deletion by keeping a
; list of the deleted elements.  But we cannot make a list of the
; deleted elements themselves because there may be duplicate elements
; in the bag and we need to be able to delete occurrences.  Thus, the
; workhorse function actually operates on a list of pairs, (i . ele),
; where i is a unique identification integer and ele is an element of
; the bag.  In fact we just assign the position of each occurrence to
; each element of the initial bag and thereafter count up as we
; generate new elements.
;
; See m&m1 for the details.

  (m&m1 (count-off 0 bag) nil nil (length bag) fn))

; We now develop a much more powerful concept, that of mapping m&m over the
; powerset of a set.  This is how we actually merge induction candidates.
; That is, we try to mash together every possible subset of the candidates,
; largest subsets first.  See m&m-over-powerset for some implementation
; commentary before going on.

(defun cons-subset-tree (x y)

; We are representing full binary trees of t's and nil's and
; collapsing trees of all nil's to nil and trees of all t's to t.  See
; the long comment in m&m-over-powerset.  We avoid consing when
; convenient.

  (if (eq x t)
      (if (eq y t)
          t
        (if y (cons x y) '(t)))
    (if x
        (cons x y)
      (if (eq y t)
          '(nil . t)
        (if y (cons x y) nil)))))

(defabbrev car-subset-tree (x)

; See cons-subset-tree.

  (if (eq x t) t (car x)))

(defabbrev cdr-subset-tree (x)

; See cons-subset-tree.

  (if (eq x t) t (cdr x)))

(defun or-subset-trees (tree1 tree2)

; We disjoin the tips of two binary t/nil trees.  See cons-subset-tree.

  (cond ((or (eq tree1 t)(eq tree2 t)) t)
        ((null tree1) tree2)
        ((null tree2) tree1)
        (t (cons-subset-tree (or-subset-trees (car-subset-tree tree1)
                                              (car-subset-tree tree2))
                             (or-subset-trees (cdr-subset-tree tree1)
                                              (cdr-subset-tree tree2))))))

(defun m&m-over-powerset1 (st subset stree ans fn)

; See m&m-over-powerset.

  (cond
   ((eq stree t) (mv t ans))
   ((null st)
    (let ((z (m&m subset fn)))
      (cond ((and z (null (cdr z)))
             (mv t (cons (car z) ans)))
            (t (mv nil ans)))))
   (t
    (mv-let (stree1 ans1)
      (m&m-over-powerset1 (cdr st)
                          (cons (car st) subset)
                          (cdr-subset-tree stree)
                          ans fn)
      (mv-let (stree2 ans2)
        (m&m-over-powerset1 (cdr st)
                            subset
                            (or-subset-trees
                             (car-subset-tree stree)
                             stree1)
                            ans1 fn)
        (mv (cons-subset-tree stree2 stree1) ans2))))))

(defun m&m-over-powerset (st fn)

; Fn is a function known to m&m-apply.  Let (fn* s) be defined to be z,
; if (m&m s fn) = {z} and nil otherwise.  Informally, (fn* s) is the
; result of somehow mating and merging all the elements of s into a single
; object, or nil if you can't.

; This function applies fn* to the powerset of st and collects all those
; non-nil values produced from maximal s's.  I.e., we keep (fn* s) iff it
; is non-nil and no superset of s produces a non-nil value.

; We do this amazing feat (recall that the powerset of a set of n
; things contains 2**n subsets) by generating the powerset in order
; from largest to smallest subsets and don't generate or test any
; subset under a non-nil fn*.  Nevertheless, if the size of set is
; very big, this function will get you.

; An informal specification of this function is that it is like m&m
; except that we permit an element to be merged into more than one
; other element (but an element can be used at most once per final
; element) and we try to maximize the amount of merging we can do.

; For example, if x mates with y1 to form z1, and x mates with y2 to
; form z2, and no other mates occur, then this function would
; transform {x y1 y2} into {z1 z2}.  It searches by generate and test:

;       s            (fn* s)
;    (x y1 y2)         nil
;    (x y1)            z1
;    (x y2)            z2
;    (x)              subsumed
;    (y1 y2)           nil
;    (y1)             subsumed
;    (y2)             subsumed
;    nil              subsumed

; Here, s1 is "subsumed" by s2 means s1 is a subset of s2.  (Just the
; opposite technical definition but exactly the same meaning as in the
; clausal sense.)

; The way we generate the powerset elements is suggested by the
; following trivial von Neumann function, ps, which, when called as in
; (ps set nil), calls PROCESS on each member of the powerset of set,
; in the order in which we generate them:

; (defun ps (set subset)
;  (cond ((null set) (PROCESS subset))
;        (t (ps (cdr set) (cons (car set) subset))   ;rhs
;           (ps (cdr set) subset))))                 ;lhs

; By generating larger subsets first we know that if a subset subsumes
; the set we are considering then that subset has already been
; considered.  Therefore, we need a way to keep track of the subsets
; with non-nil values.  We do this with a "subset tree".  Let U be the
; universe of objects in some order.  Then the full binary tree with
; depth |U| can be thought of as the powerset of U.  In particular,
; any branch through the tree, from top-most node to tip, represents a
; subset of U by labeling the nodes at successive depth by the
; successive elements of U (the topmost node being labeled with the
; first element of U) and adopting the convention that taking a
; right-hand (cdr) branch at a node indicates that the label is in the
; subset and a left-hand (car) branch indicates that the label is not
; in the subset.  At the tip of the tree we store a T indicating that
; the subset had a non-nil value or a NIL indicating that it had a nil
; value.

; For storage efficiency we let nil represent an arbitrarily deep full
; binary tree will nil at every tip and we let t represent the
; analogous trees with t at every tip.  Car-subset-tree,
; cdr-subset-tree and cons-subset-tree implement these abstractions.

; Of course, we don't have the tree when we start and we generate it
; as we go.  That is a really weird idea because generating the tree
; that tells us who was a subset of whom in the past seems to have little
; use as we move forward.  But that is not true.

; Observe that there is a correspondence between these trees and the
; function ps above for generating the power set.  The recursion
; labeled "rhs" above is going down the right-hand side of the tree
; and the "lhs" recursion is going down the left-hand side.  Note that
; we go down the rhs first.

; The neat fact about these trees is that there is a close
; relationship between the right-hand subtree (rhs) and left-hand
; subtree (lhs) of any given node of the tree: lhs can be obtained
; from rhs by turning some nils into ts.  The reason is that the tips
; of the lhs of a node labeled by x denote exactly the same subsets
; as the corresponding tips of the right-hand side, except that on the
; right x was present in the subset and on the left it is not.  So
; when we do the right hand side we come back with a tree and if we
; used that very tree for the left hand side (interpreting nil as
; meaning "compute it and see" and t as meaning "a superset of this
; set has non-nil value") then it is correct.  But we can do a little
; better than that because we might have come into this node with a
; tree (i.e., one to go into the right hand side with and another to go
; into the left hand side with) and so after we have gone into the
; right and come back with its new tree, we can disjoin the output of
; the right side with the input for the left side to form the tree we
; will actually use to explore the left side.

  (mv-let (stree ans)
    (m&m-over-powerset1 st nil nil nil fn)
    (declare (ignore stree))
    ans))

; Ok, so now we have finished the selection process and we begin the
; construction of the induction formula itself.


(defun all-picks2 (pocket pick ans)
; See all-picks.
  (cond ((null pocket) ans)
        (t (cons (cons (car pocket) pick)
                 (all-picks2 (cdr pocket) pick ans)))))

(defun all-picks2r (pocket pick ans)
; See all-picks.
  (cond ((null pocket) ans)
        (t (all-picks2r (cdr pocket) pick
                        (cons (cons (car pocket) pick) ans)))))

(defun all-picks1 (pocket picks ans rflg)
; See all-picks.
  (cond ((null picks) ans)
        (t (all-picks1 pocket (cdr picks)
                       (if rflg
                           (all-picks2r pocket (car picks) ans)
                         (all-picks2 pocket (car picks) ans))
                       rflg))))

(defun all-picks (pockets rflg)

; Pockets is a list of pockets, each pocket containing 0 or more
; objects.  We return a list of all the possible ways you can pick one
; thing from each pocket.  If rflg is nil initially, then the order of
; the resulting list is exactly the same as it was in nqthm.  There is
; not much else to recommend this particular choice of definition!

; Historical Plaque from Nqthm:

;   (DEFUN ALL-PICKS (POCKET-LIST)
;    (COND ((NULL POCKET-LIST) (LIST NIL))
;          (T (ITERATE FOR PICK IN (ALL-PICKS (CDR POCKET-LIST))
;                      NCONC (ITERATE FOR CHOICE IN (CAR POCKET-LIST)
;                                     COLLECT (CONS CHOICE PICK))))))

; Nqthm's construction is a very natural recursive one, except that it
; used nconc to join together the various segments of the answer.  If
; we tried the analogous construction here we would have to append the
; segments together and copy a very long list.  So we do it via an
; accumulator.  The trouble however is that we reverse the order of
; the little buckets in our answer every time we process a pocket.  We
; could avoid that if we wanted to recurse down the length of our
; answer on recursive calls, but we were afraid of running out of
; stack, and so we have coded this with tail recursion only.  We do
; non-tail recursion only over short things like individual pockets or
; the list of pockets.  And so to (a) avoid unnecessary copying, (b)
; non-tail recursion, and (c) constructing our answer in a different
; order, we introduced rflg.  Rflg causes us either to reverse or not
; reverse a certain intermediate result every other recursion.  It
; would be reassuring to see a mechanically checked proof that this
; definition of all-picks is equivalent to nqthm's.

  (cond ((null pockets) '(nil))
        (t (all-picks1 (car pockets)
                       (all-picks (cdr pockets) (not rflg))
                       nil
                       rflg))))



(defun dumb-negate-lit-lst-lst (cl-set)

; We apply dumb-negate-lit-lst to every list in cl-set and collect the
; result.  You can think of this as negating a clause set (i.e., an
; implicit conjunction of disjunctions), but you have to then imagine
; that the implicit "and" at the top has been turned into an "or" and
; vice versa at the lower level.

  (cond ((null cl-set) nil)
        (t (cons (dumb-negate-lit-lst (car cl-set))
                 (dumb-negate-lit-lst-lst (cdr cl-set))))))

(defun induction-hyp-clause-segments2 (alists cl ans)
; See induction-hyp-clause-segments1.
  (cond ((null alists) ans)
        (t (cons (sublis-var-lst (car alists) cl)
                 (induction-hyp-clause-segments2 (cdr alists) cl ans)))))

(defun induction-hyp-clause-segments1 (alists cl-set ans)

; This function applies all of the substitutions in alists to all of
; the clauses in cl-set and appends the result to ans to create one
; list of instantiated clauses.

  (cond ((null cl-set) ans)
        (t (induction-hyp-clause-segments2
            alists
            (car cl-set)
            (induction-hyp-clause-segments1 alists (cdr cl-set) ans)))))

(defun induction-hyp-clause-segments (alists cl-set)

; Cl-set is a set of clauses.  We are trying to prove the conjunction
; over that set, i.e., cl1 & cl2 ... & clk, by induction.  We are in a
; case in which we can assume every instance under alists of that
; conjunction.  Thus, we can assume any lit from cl1, any lit from
; cl2, etc., instantiated via all of the alists.  We wish to return a
; list of clause segments.  Each segment will be spliced into the a
; clause we are trying to prove and together the resulting set of
; clauses is supposed to be equivalent to assuming all instances of
; the conjunction over cl-set.

; So one way to create the answer would be to first instantiate each
; of the k clauses with each of the n alists, getting a set of n*k
; clauses.  Then we could run all-picks over that, selecting one
; literal from each of the instantiated clauses to assume.  Then we'd
; negate each literal within each pick to create a clause hypothesis
; segment.  That is nearly what we do, except that we do the negation
; first so as to share structure among the all-picks answers.


; Note: The code below calls (dumb-negate-lit lit) on each lit.  Nqthm
; used (negate-lit lit nil ...) on each lit, employing
; negate-lit-lst-lst, which has since been deleted but was strictly
; analogous to the dumb version called below.  But since the
; type-alist is nil in Nqthm's call, it seems unlikely that the
; literal will be decided by type-set.  We changed to dumb-negate-lit
; to avoid having to deal both with ttrees and the enabled structure
; implicit in type-set.

  (all-picks
   (induction-hyp-clause-segments1 alists
                                   (dumb-negate-lit-lst-lst cl-set)
                                   nil)
   nil))

(defun induction-formula3 (neg-tests hyp-segments cl ans)

; Neg-tests is the list of the negated tests of an induction
; tests-and-alists entry.  hyp-segments is a list of hypothesis clause
; segments (i.e., more negated tests), and cl is a clause.  For each
; hyp segment we create the clause obtained by disjoining the tests,
; the segment, and cl.  We conjoin the resulting clauses to ans.

; See induction-formula for a comment about this iteration.

  (cond
   ((null hyp-segments) ans)
   (t (induction-formula3 neg-tests
                          (cdr hyp-segments)
                          cl
                          (conjoin-clause-to-clause-set

; Historical Plaque from Nqthm:

;   We once implemented the idea of "homographication" in which we combined
;   both induction, opening up of the recursive fns in the conclusion, and
;   generalizing away some recursive calls.  This function did the expansion
;   and generalization.  If the idea is reconsidered the following theorems are
;   worthy of consideration:

;       (ORDERED (SORT X)),
;       (IMPLIES (ORDERED X)
;                (ORDERED (ADDTOLIST I X))),
;       (IMPLIES (AND (NUMBER-LISTP X)
;                     (ORDERED X)
;                     (NUMBERP I)
;                     (NOT (< (CAR X) I)))
;                (EQUAL (ADDTOLIST I X) (CONS I X))), and
;       (IMPLIES (AND (NUMBER-LISTP X) (ORDERED X)) (EQUAL (SORT X) X)).

; Observe that we simply disjoin the negated tests, hyp segments, and clause.
; Homographication further manipulated the clause before adding it to the
; answer.
                           (disjoin-clauses
                            neg-tests
                            (disjoin-clauses (car hyp-segments) cl))
                           ans)))))

(defun induction-formula2 (cl cl-set ta-lst ans)

; Cl is a clause in cl-set, which is a set of clauses we are proving
; by induction.  Ta-lst is the tests-and-alists-lst component of the
; induction candidate we are applying to prove cl-set.  We are now
; focused on the proof of cl, using the induction schema of ta-lst
; but getting to assume all the clauses in cl-set in our induction
; hypothesis.  We will map across ta-lst, getting a set of tests and
; some alists at each stop, and for each stop add a bunch of clauses
; to ans.

  (cond
   ((null ta-lst) ans)
   (t (induction-formula2 cl cl-set (cdr ta-lst)
                          (induction-formula3

; Note:  Nqthm used (negate-lit-lst ... nil ...), but since the
; type-alist supplied was nil, we decided it was probably no buying us
; much -- not as much as passing up the ttrees would cost in terms of
; coding work!

                           (dumb-negate-lit-lst
                            (access tests-and-alists (car ta-lst) :tests))
                           (induction-hyp-clause-segments
                            (access tests-and-alists (car ta-lst) :alists)
                            cl-set)
                           cl
                           ans)))))

(defun induction-formula1 (lst cl-set ta-lst ans)

; Lst is a tail of cl-set.  Cl-set is a set of clauses we are trying to prove.
; Ta-lst is the tests-and-alists-lst component of the induction candidate
; we wish to apply to cl-set.  We map down lst forming a set of clauses
; for each cl in lst.  Basically, the set we form for cl is of the form
; ... -> cl, where ... involves all the case analysis under the tests in
; ta-lst and all the induction hypotheses from cl-set under the alists in
; each test-and-alists.  We add our clauses to ans.

  (cond
   ((null lst) ans)
   (t (induction-formula1 (cdr lst) cl-set ta-lst
                          (induction-formula2 (car lst)
                                              cl-set ta-lst ans)))))

(defun induction-formula (cl-set ta-lst)

; Cl-set is a set of clauses we are to try to prove by induction, applying
; the inductive scheme described by the tests-and-alists-lst, ta-lst,
; of some induction candidate.  The following historical plaque tells all.

; Historical Plaque from Nqthm:

;   TESTS-AND-ALISTS-LST is a such a list that the disjunction of the
;   conjunctions of the TESTS components of the members is T.  Furthermore,
;   there exists a measure M, a well-founded relation R, and a sequence of
;   variables x1, ..., xn such that for each T&Ai in TESTS-AND-ALISTS-LST, for
;   each alist alst in the ALISTS component of T&Ai, the conjunction of the
;   TESTS component, say qi, implies that (R (M x1 ... xn)/alst (M x1 ... xn)).

;   To prove thm, the conjunction of the disjunctions of the members of CL-SET,
;   it is sufficient, by the principle of induction, to prove instead the
;   conjunction of the terms qi & thm' & thm'' ...  -> thm, where the primed
;   terms are the results of substituting the alists in the ALISTS field of the
;   ith member of TESTS-AND-ALISTS-LST into thm.

;   If thm1, thm2, ..., thmn are the disjunctions of the members of CL-SET,
;   then it is sufficient to prove all of the formulas qi & thm' & thm'' ...
;   -> thmj.  This is a trivial proposition fact, to prove (IMPLIES A (AND B
;   C)) it is sufficient to prove (IMPLIES A B) and (IMPLIES A C).

;   The (ITERATE FOR PICK ...)* expression below returns a list of
;   clauses whose conjunction propositionally implies qi & thm' &
;   thm'' ...  -> thmj, where TA is the ith member of
;   TESTS-AND-ALISTS-LST and CL is the jth member of CL-SET.  Proof:
;   Let THM have the form:
;
;        (AND (OR a1 ...)
;             (OR b1 ...)
;             ...
;             (OR z1 ...)).

;   Then qi & thm' & thm'' ... -> thmj has the form:

;       (IMPLIES (AND qi
;                     (AND (OR a1 ... )
;                          (OR b1 ... )
;                          ...
;                          (OR z1 ... ))'
;                     (AND (OR a1 ... )
;                          (OR b1 ... )
;                          ...
;                          (OR z1 ... ))''
;                     ...
;                     (AND (OR a1 ... )
;                          (OR b1 ... )
;                          ...
;                          (OR z1 ... )))'''...'
;                thmj).
;
;   Suppose this formula is false for some values of the free variables.  Then
;   under those values, each disjunction in the hypothesis is true.  Thus there
;   exists a way of choosing one literal from each of the disjunctions, all of
;   which are true.  This choice is one of the PICKs below.  But we prove that
;   (IMPLIES (AND qi PICK) thmj).

; Note: The (ITERATE FOR PICK ...) expression mentioned above is the function
; induction-formula3 above.

  (m&m (reverse (induction-formula1 cl-set cl-set ta-lst nil))
       'subsetp-equal/smaller))

; Because the preceding computation is potentially explosive we will
; sometimes reduce its complexity by shrinking the given clause set to
; a singleton set containing a unit clause.  To decide whether to do that
; we will use the following rough measures:

(defun all-picks-size (cl-set)

; This returns the size of the all-picks computed by induction-formula3.

  (cond ((null cl-set) 1)
        (t (* (length (car cl-set)) (all-picks-size (cdr cl-set))))))

(defun induction-formula-size1 (hyps-size concl-size ta-lst)

; We determine roughly the number of clauses that ta-lst will generate when
; the number of all-picks through the hypotheses is hyps-size and the
; number of conclusion clauses is concl-size.  The individual cases of
; the tests-and-alists combine additively.  But we must pick our way through
; the hyps for each instantiation.

  (cond ((null ta-lst) 0)
        (t
         (+ (* concl-size (expt hyps-size
                                (length (access tests-and-alists
                                                (car ta-lst)
                                                :alists))))
            (induction-formula-size1 hyps-size concl-size (cdr ta-lst))))))

(defun induction-formula-size (cl-set ta-lst)

; This function returns a rough upper bound on the number of clauses
; that will be generated by induction-formula on the given arguments.
; See the comment in that function.

  (induction-formula-size1 (all-picks-size cl-set)
                           (length cl-set)
                           ta-lst))

; The following constant determines the limit on the estimated number of
; clauses induct, below, will return.  When normal processing would exceed
; this number, we try to cut down the combinatorics by collapsing clauses
; back into terms.

(defconst *maximum-induct-size* 100)

; And here is how we convert a hairy set of clauses into a term when we
; have to.

(defun termify-clause-set (clauses)

; This function is similar to termify-clause except that it converts a
; set of clauses into an equivalent term.  The set of clauses is
; understood to be implicitly conjoined and we therefore produce a
; conjunction expressed as (if cl1 cl2 nil).

  (declare (xargs :guard (pseudo-term-list-listp clauses)))
  (cond ((null clauses) *t*)
        ((null (cdr clauses)) (disjoin (car clauses)))
        (t (mcons-term* 'if
                        (disjoin (car clauses))
                        (termify-clause-set (cdr clauses))
                        *nil*))))

; Once we have created the set of clauses to prove, we inform the
; simplifier of what to look out for during the early processing.

(defun inform-simplify3 (alist terms ans)

; Instantiate every term in terms with alist and add them to ans.

  (cond ((null terms) ans)
        (t (inform-simplify3 alist (cdr terms)
                             (add-to-set-equal (sublis-var alist (car terms))
                                               ans)))))

(defun inform-simplify2 (alists terms ans)

; Using every alist in alists, instantiate every term in terms and add
; them all to ans.

  (cond ((null alists) ans)
        (t (inform-simplify2 (cdr alists) terms
                             (inform-simplify3 (car alists) terms ans)))))


(defun inform-simplify1 (ta-lst terms ans)

; Using every alist mentioned in any tests-and-alists record of ta-lst
; we instantiate every term in terms and add them all to ans.

  (cond ((null ta-lst) ans)
        (t (inform-simplify1 (cdr ta-lst) terms
                             (inform-simplify2 (access tests-and-alists
                                                       (car ta-lst)
                                                       :alists)
                                               terms
                                               ans)))))


(defun inform-simplify (ta-lst terms pspv)

; Historical Plaque from Nqthm:

;   Two of the variables effecting REWRITE are TERMS-TO-BE-IGNORED-BY-REWRITE
;   and EXPAND-LST.  When any term on the former is encountered REWRITE returns
;   it without rewriting it.  Terms on the latter must be calls of defined fns
;   and when encountered are replaced by the rewritten body.

;   We believe that the theorem prover will perform significantly faster on
;   many theorems if, after an induction, it does not waste time (a) trying to
;   simplify the recursive calls introduced in the induction hypotheses and (b)
;   trying to decide whether to expand the terms inducted for in the induction
;   conclusion.  This suspicion is due to some testing done with the idea of
;   "homographication" which was just a jokingly suggested name for the idea of
;   generalizing the recursive calls away at INDUCT time after expanding the
;   induction terms in the conclusion.  Homographication speeded the
;   theorem-prover on many theorems but lost on several others because of the
;   premature generalization.  See the comment in FORM-INDUCTION-CLAUSE.

;   To avoid the generalization at INDUCT time we are going to try using
;   TERMS-TO-BE-IGNORED-BY-REWRITE.  The idea is this, during the initial
;   simplification of a clause produced by INDUCT we will have the recursive
;   terms on TERMS-TO-BE-IGNORED-BY-REWRITE.  When the clause settles down --
;   hopefully it will often be proved first -- we will restore
;   TERMS-TO-BE-IGNORED-BY-REWRITE to its pre-INDUCT value.  Note however that
;   we have to mess with TERMS-TO-BE-IGNORED-BY-REWRITE on a clause by clause
;   basis, not just once in INDUCT.

;   So here is the plan.  INDUCT will set INDUCTION-HYP-TERMS to the list of
;   instances of the induction terms, and will set INDUCTION-CONCL-TERMS to the
;   induction terms themselves.  SIMPLIFY-CLAUSE will look at the history of
;   the clause to determine whether it has settled down since induction.  If
;   not it will bind TERMS-TO-BE-IGNORED-BY-REWRITE to the concatenation of
;   INDUCTION-HYP-TERMS and its old value and will analogously bind EXPAND-LST.
;   A new process, called SETTLED-DOWN-SENT, will be used to mark when in the
;   history the clause settled down.

; In a departure from Nqthm, starting with Version_2.8, we do not wait for
; settled-down before turning off the above special consideration given to
; induction-hyp-terms and induction-concl-terms. See simplify-clause for
; details.

  (change prove-spec-var pspv
          :induction-concl-terms terms
          :induction-hyp-terms (inform-simplify1 ta-lst terms nil)))

; Ok, except for our output and putting it all together, that's induction.
; We now turn to the output.  Induct prints two different messages. One
; reports the successful choice of an induction.  The other reports failure.

(defun all-vars1-lst-lst (lst ans)

; Lst is a list of lists of terms.  For example, it might be a set of
; clauses.  We compute the set of all variables occurring in it.

  (cond ((null lst) ans)
        (t (all-vars1-lst-lst (cdr lst)
                              (all-vars1-lst (car lst) ans)))))

(defun gen-new-name1 (char-lst wrld i)
  (let ((name (intern
               (coerce
                (append char-lst
                        (explode-nonnegative-integer i 10 nil))
                'string)
               "ACL2")))
    (cond ((new-namep name wrld) name)
          (t (gen-new-name1 char-lst wrld (1+ i))))))

(defun gen-new-name (root wrld)

; Create from the symbol root a possibly different symbol that
; is a new-namep in wrld.

  (cond ((new-namep root wrld) root)
        (t (gen-new-name1 (coerce (symbol-name root) 'list) wrld 0))))

(defun unmeasured-variables3 (vars alist)
; See unmeasured-variables.
  (cond ((null alist) nil)
        ((or (member-eq (caar alist) vars)
             (eq (caar alist) (cdar alist)))
         (unmeasured-variables3 vars (cdr alist)))
        (t (cons (caar alist) (unmeasured-variables3 vars (cdr alist))))))

(defun unmeasured-variables2 (vars alists)
; See unmeasured-variables.
  (cond ((null alists) nil)
        (t (union-eq (unmeasured-variables3 vars (car alists))
                     (unmeasured-variables2 vars (cdr alists))))))

(defun unmeasured-variables1 (vars ta-lst)
; See unmeasured-variables.
  (cond ((null ta-lst) nil)
        (t (union-eq (unmeasured-variables2 vars
                                            (access tests-and-alists
                                                    (car ta-lst)
                                                    :alists))
                     (unmeasured-variables1 vars (cdr ta-lst))))))

(defun unmeasured-variables (measured-vars cand)

; Measured-vars is the :subset of measured variables from the measure of term,
; computed above, for cand.  We collect those variables that are changed by
; some substitution but are not measured by our induction measure.  These are
; simply brought to the user's attention because we find it often surprising to
; see them.

  (unmeasured-variables1 measured-vars
                         (access candidate cand :tests-and-alists-lst)))

(defun tilde-@-well-founded-relation-phrase (rel wrld)

; We return a ~@ message that prints as "the relation rel (which, by name, is
; known to be well-founded on the domain recognized by mp)" and variants of
; that obtained when name is nil (meaning the well-foundedness is built in)
; and/or mp is t (meaning the domain is the universe).

  (let* ((temp (assoc-eq rel (global-val 'well-founded-relation-alist wrld)))
         (mp (cadr temp))
         (base-symbol (base-symbol (cddr temp))))
    (msg "the relation ~x0 (which~#1~[ ~/, by ~x2, ~]is known to be ~
          well-founded~#3~[~/ on the domain recognized by ~x4~])"
         rel
         (if (null base-symbol) 0 1)
         base-symbol
         (if (eq mp t) 0 1)
         mp)))

(defun measured-variables (cand wrld)
  (all-vars1-lst
   (subcor-var-lst (formals (ffn-symb (access candidate cand :induction-term))
                            wrld)
                   (fargs (access candidate cand :induction-term))
                   (access justification
                           (access candidate cand :justification)
                           :subset))
   nil))

(defun induct-msg/continue (pool-lst
                            forcing-round
                            cl-set
                            induct-hint-val
                            len-candidates
                            len-flushed-candidates
                            len-merged-candidates
                            len-unvetoed-candidates
                            len-complicated-candidates
                            len-high-scoring-candidates
                            winning-candidate
                            estimated-size
                            clauses
                            wrld
                            state)

; Pool-lst is what is passed to form the tilde-@-pool-name-phrase (q.v.) of the
; set of clauses cl-set to which we are applying induction.  Len-candidates is
; the length of the list of induction candidates we found.
; Len-flushed-candidates is the length of the candidates after flushing some
; down others, etc.  Winning-candidate is the final selection.  Clauses is the
; clause set generated by applying winning-candidate to cl-set.  Wrld and state
; are the usual.

; This function increments timers.  Upon entry, the accumulated time is
; charged to 'prove-time.  The time spent in this function is charged
; to 'print-time.

; Warning: This function should be called under (io? prove ...).

  (declare (xargs

; Avoid blow-up from (skip-proofs (verify-termination ...)), which otherwise
; takes a long time (e.g., when executed on behalf of community books utility
; verify-guards-program).

            :normalize nil))
  (cond
   ((and (gag-mode)
         (or (eq (gag-mode-evisc-tuple state) t)
             (cdr pool-lst)))
    state)
   (t
    (pprogn
     (increment-timer 'prove-time state)
     (let* ((pool-name
             (tilde-@-pool-name-phrase forcing-round pool-lst))
            (p (cons :p
                     (merge-sort-term-order (all-vars1-lst-lst cl-set nil))))
            (measured-variables (measured-variables winning-candidate wrld))
            (unmeasured-variables (unmeasured-variables measured-variables
                                                        winning-candidate))
            (attribution-phrase (tilde-*-simp-phrase
                                 (access candidate winning-candidate :ttree))))
       (fms "~#H~[We have been told to use induction.  ~N0 induction ~
                scheme~#1~[ is~/s are~] suggested by the induction ~
                hint.~/~

                We have been told to use induction.  ~N0 induction ~
                scheme~#1~[ is~/s are~] suggested by this ~
                conjecture.~/~

                Perhaps we can prove ~@n by induction.  ~

                ~N0 induction scheme~#1~[ is~/s are~] suggested by this ~
                conjecture.~]  ~

          ~#a~[~/Subsumption reduces that number to ~n2.  ~]~

          ~#b~[~/These merge into ~n3 derived induction scheme~#4~[~/s~].  ~]~

          ~#c~[~/However, ~n5 of these ~#6~[is~/are~] flawed and so we are ~
           left with ~nq viable ~#r~[~/candidate~/candidates~].  ~]~

          ~#d~[~/By considering those suggested by the largest number of ~
                 non-primitive recursive functions, we narrow the field ~
                 to ~n7.  ~]~

          ~#e~[~/~N8 of these ~
                 ~#9~[has a score higher than the other~#A~[~/s~].  ~/~
                      are tied for the highest score.  ~]~]~

          ~#f~[~/We will choose arbitrarily among these.  ~]~

          ~|~%We will induct according to a scheme suggested by ~
          ~#h~[~pg.~/~pg, but modified to accommodate ~*i.~]~

          ~#w~[~/  ~#h~[This suggestion was~/These suggestions were~] ~
          produced using ~*x.~]  ~

          If we let ~pp denote ~@n above then the induction scheme ~
          we'll use is~|~

          ~Qsy.~

          This induction is justified by the same argument used ~
          to admit ~xj.  ~

          ~#l~[~/Note, however, that the unmeasured ~
                 variable~#m~[ ~&m is~/s ~&m are~] being instantiated.  ~]~

          When applied to the goal at hand the above induction scheme ~
          produces ~#v~[no nontautological subgoals~/one nontautological ~
          subgoal~/~no nontautological subgoals~].~

          ~#t~[~/  However, to achieve this relatively small number of ~
          cases we had to fold ~@n into a single IF-expression.  Had we ~
          left it as a set of clauses this induction would have produced ~
          approximately ~nu cases!  Chances are that this proof attempt ~
          is about to blow up in your face (and all over our memory ~
          boards).~]~|"
            (list (cons #\H (cond ((null induct-hint-val) 2)
                                  ((equal induct-hint-val *t*) 1)
                                  (t 0)))
                  (cons #\n pool-name)
                  (cons #\0 len-candidates)
                  (cons #\1 (if (int= len-candidates 1) 0 1))
                  (cons #\a (if (< len-flushed-candidates
                                   len-candidates)
                                1 0))
                  (cons #\2 len-flushed-candidates)
                  (cons #\b (if (< len-merged-candidates
                                   len-flushed-candidates)
                                1 0))
                  (cons #\3 len-merged-candidates)
                  (cons #\4 (if (int= len-merged-candidates 1) 0 1))
                  (cons #\c (if (< len-unvetoed-candidates
                                   len-merged-candidates)
                                1 0))
                  (cons #\5 (- len-merged-candidates
                               len-unvetoed-candidates))
                  (cons #\q len-unvetoed-candidates)
                  (cons #\y (gag-mode-evisc-tuple state)) ; is not t
                  (cons #\r (zero-one-or-more len-unvetoed-candidates))
                  (cons #\6 (if (int= (- len-merged-candidates
                                         len-unvetoed-candidates)
                                      1)
                                0 1))
                  (cons #\d (if (< len-complicated-candidates
                                   len-unvetoed-candidates)
                                1 0))
                  (cons #\7 len-complicated-candidates)
                  (cons #\e (if (< len-high-scoring-candidates
                                   len-complicated-candidates)
                                1 0))
                  (cons #\8 len-high-scoring-candidates)
                  (cons #\9 (if (int= len-high-scoring-candidates 1) 0 1))
                  (cons #\A (if (int= (- len-complicated-candidates
                                         len-high-scoring-candidates)
                                      1)
                                0 1))
                  (cons #\f (if (int= len-high-scoring-candidates 1) 0 1))
                  (cons #\p p)
                  (cons #\s (prettyify-clause-set
                             (induction-formula
                              (list (list p))
                              (access candidate
                                      winning-candidate
                                      :tests-and-alists-lst))
                             (let*-abstractionp state)
                             wrld))
                  (cons #\g (untranslate (access candidate winning-candidate
                                                 :xinduction-term)
                                         nil
                                         wrld))
                  (cons #\h (if (access candidate winning-candidate :xancestry)
                                1 0))
                  (cons #\i (tilde-*-untranslate-lst-phrase
                             (access candidate winning-candidate :xancestry)
                             nil wrld))
                  (cons #\j (ffn-symb
                             (access candidate winning-candidate
                                     :xinduction-term)))
                  (cons #\l (if unmeasured-variables 1 0))
                  (cons #\m unmeasured-variables)
                  (cons #\o (length clauses))
                  (cons #\t (if (> estimated-size *maximum-induct-size*)
                                1
                              0))
                  (cons #\u estimated-size)
                  (cons #\v (if (null clauses) 0 (if (cdr clauses) 2 1)))
                  (cons #\w (if (nth 4 attribution-phrase) 1 0))
                  (cons #\x attribution-phrase))
            (proofs-co state)
            state
            (term-evisc-tuple nil state)))
     (increment-timer 'print-time state)))))

(mutual-recursion

(defun rec-fnnames (term wrld)
  (cond ((variablep term) nil)
        ((fquotep term) nil)
        ((flambda-applicationp term)
         (union-eq (rec-fnnames (lambda-body (ffn-symb term)) wrld)
                   (rec-fnnames-lst (fargs term) wrld)))
        ((getpropc (ffn-symb term) 'recursivep nil wrld)
         (add-to-set-eq (ffn-symb term)
                        (rec-fnnames-lst (fargs term) wrld)))
        (t (rec-fnnames-lst (fargs term) wrld))))

(defun rec-fnnames-lst (lst wrld)
  (cond ((null lst) nil)
        (t (union-eq (rec-fnnames (car lst) wrld)
                     (rec-fnnames-lst (cdr lst) wrld)))))

)

(defun induct-msg/lose (pool-name induct-hint-val pspv state)

; We print the message that no induction was suggested.

; This function increments timers.  Upon entry, the accumulated time is
; charged to 'prove-time.  The time spent in this function is charged
; to 'print-time.

; Warning: This function should be called under (io? prove ...).

  (pprogn
   (increment-timer 'prove-time state)
   (fms "No induction schemes are suggested by ~#H~[the induction ~
         hint.~@?~/~@n.~]  Consequently, the proof attempt has failed.~|"
        (list (cons #\H (cond (induct-hint-val 0) (t 1)))
              (cons #\n pool-name)
              (cons #\?
                    (and induct-hint-val ; optimization
                         (let* ((wrld (w state))
                                (all-fns (all-fnnames induct-hint-val))
                                (rec-fns (rec-fnnames induct-hint-val wrld)))
                           (cond
                            ((null all-fns)
                             "  (Note that there is no function symbol ~
                              occurring in that hint.)")
                            ((and (null rec-fns)
                                  (null (cdr all-fns)))
                             (msg "  (Note that ~x0 is not defined ~
                                   recursively, so it cannot suggest an ~
                                   induction scheme.)"
                                  (car all-fns)))
                            ((null rec-fns)
                             "  (Note that none of its function symbols is ~
                              defined recursively, so they cannot suggest ~
                              induction schemes.)")
                            ((and (all-variablep (fargs induct-hint-val))
                                  (let ((ens (ens-from-pspv pspv)))
                                    (and
                                     (not (enabled-runep
                                           (list :induction (car rec-fns))
                                           ens
                                           wrld))
                                     (not (enabled-runep
                                           (list :definition (car rec-fns))
                                           ens
                                           wrld)))))
                             (msg "  (Note that ~x0 (including its :induction ~
                                   rune) is disabled, so it cannot suggest an ~
                                   induction scheme.  Consider providing an ~
                                   :in-theory hint that enables ~x0 or ~x1.)"
                                  (car all-fns)
                                  (list :induction (car all-fns))))
                            (t ""))))))
        (proofs-co state)
        state
        (term-evisc-tuple nil state))
   (increment-timer 'print-time state)))

; When induct is called it is supplied the hint-settings that were
; attached to the clause by the user.  Induct has the job of loading
; the hint settings into the pspv it returns.  Most of the content of
; the hint-settings is loaded into the rewrite-constant of the pspv.

(defun@par load-hint-settings-into-rcnst (hint-settings rcnst
                                                        incrmt-array-name-info
                                                        wrld ctx state)

; Certain user supplied hint settings find their way into the rewrite-constant.
; They are :expand, :restrict, :hands-off, and :in-theory.  Our convention is
; that if a given hint key/val is provided it replaces what was in the rcnst.
; Otherwise, we leave the corresponding field of rcnst unchanged.

; Incrmt-array-name-info is either a clause-id, a keyword, or nil.  If it is a
; clause-id and we install a new enabled structure, then we will use that
; clause-id to build the array name, rather than simply incrementing a suffix.
; Otherwise incrmt-array-name-info is a keyword.  A keyword value should be
; used for calls made by user applications, for example in community book
; books/tools/easy-simplify.lisp, so that enabled structures maintained by the
; ACL2 system do not lose their associated von Neumann arrays.

  (er-let*@par
   ((new-ens
     (cond
      ((assoc-eq :in-theory hint-settings)
       (load-theory-into-enabled-structure@par
        :from-hint
        (cdr (assoc-eq :in-theory hint-settings))
        nil
        (access rewrite-constant rcnst :current-enabled-structure)
        (or incrmt-array-name-info t)
        nil
        wrld ctx state))
      (t (value@par (access rewrite-constant rcnst
                            :current-enabled-structure))))))
   (value@par (change rewrite-constant rcnst
                      :rw-cache-state
                      (cond
                       ((assoc-eq :rw-cache-state hint-settings)
                        (cdr (assoc-eq :rw-cache-state hint-settings)))
                       (t (access rewrite-constant rcnst :rw-cache-state)))
                      :expand-lst
                      (cond
                       ((assoc-eq :expand hint-settings)
                        (cdr (assoc-eq :expand hint-settings)))
                       (t (access rewrite-constant rcnst :expand-lst)))
                      :restrictions-alist
                      (cond
                       ((assoc-eq :restrict hint-settings)
                        (cdr (assoc-eq :restrict hint-settings)))
                       (t (access rewrite-constant rcnst
                                  :restrictions-alist)))
                      :fns-to-be-ignored-by-rewrite
                      (cond
                       ((assoc-eq :hands-off hint-settings)
                        (cdr (assoc-eq :hands-off hint-settings)))
                       (t (access rewrite-constant rcnst
                                  :fns-to-be-ignored-by-rewrite)))
                      :current-enabled-structure
                      new-ens
                      :nonlinearp
                      (cond
                       ((assoc-eq :nonlinearp hint-settings)
                        (cdr (assoc-eq :nonlinearp hint-settings)))
                       (t (access rewrite-constant rcnst :nonlinearp)))
                      :backchain-limit-rw
                      (cond
                       ((assoc-eq :backchain-limit-rw hint-settings)
                        (cdr (assoc-eq :backchain-limit-rw hint-settings)))
                       (t (access rewrite-constant rcnst
                                  :backchain-limit-rw)))
                      :case-split-limitations
                      (cond
                       ((assoc-eq :case-split-limitations hint-settings)
                        (cdr (assoc-eq :case-split-limitations
                                       hint-settings)))
                       (t (access rewrite-constant rcnst
                                  :case-split-limitations)))))))

(defun update-hint-settings (new-hint-settings old-hint-settings)
  (cond
   ((endp new-hint-settings) old-hint-settings)
   ((assoc-eq (caar new-hint-settings) old-hint-settings)
    (update-hint-settings
     (cdr new-hint-settings)
     (cons (car new-hint-settings)
           (remove1-assoc-eq (caar new-hint-settings)
                             old-hint-settings))))
   (t (update-hint-settings
       (cdr new-hint-settings)
       (cons (car new-hint-settings) old-hint-settings)))))

; Thus, a given hint-settings causes us to modify the pspv as follows:

(defun@par load-hint-settings-into-pspv (increment-flg hint-settings pspv cl-id
                                                       wrld ctx state)

; We load the hint-settings into the rewrite-constant of pspv, thereby making
; available the :expand, :case-split-limitations, :restrict, :hands-off,
; :in-theory, and :rw-cache-state hint settings.  We also store the
; hint-settings in the hint-settings field of the pspv, making available the
; :induct and :do-not-induct hint settings.

; When increment-flg is non-nil, we want to preserve the input pspv's hint
; settings except when they collide with hint-settings.  Otherwise (for
; example, when induct is called), we completely replace the input pspv's
; :hint-settings with hint-settings.

; Warning: Restore-hint-settings-in-pspv, below, is supposed to undo these
; changes while not affecting the rest of a newly obtained pspv.  Keep these
; two functions in step.

  (er-let*@par
   ((rcnst (load-hint-settings-into-rcnst@par
            hint-settings
            (access prove-spec-var pspv :rewrite-constant)
            cl-id wrld ctx state)))
   (value@par
    (change prove-spec-var pspv
            :rewrite-constant rcnst
            :hint-settings
            (if increment-flg
                (update-hint-settings hint-settings
                                      (access prove-spec-var pspv
                                              :hint-settings))
              hint-settings)))))

(defun restore-hint-settings-in-pspv (new-pspv old-pspv)

; This considers the fields changed by load-hint-settings-into-pspv above
; and restores them in new-pspv to the values they have in old-pspv.  The
; idea is that we start with a pspv1, load hints into it to get pspv2,
; pass that around the prover and obtain pspv3 (which has a new tag-tree
; and pool etc), and then restore the hint settings as they were in pspv1.
; In this example, new-pspv would be pspv3 and old-pspv would be pspv1.

; We would like the garbage collector to free up space from obsolete arrays of
; enabled-structures.  This may be especially important with potentially many
; such arrays associated with different names, due to the new method of
; creating array names after Version_4.1, where the name is typically based on
; the clause-id.  Previously, the enabled-structure array names were created
; based on just a few possible suffixes, so it didn't seem important to make
; garbage -- each time such a name was re-used, the previous array for that
; name became garbage.  If we change how this is done, revisit the sentence
; about this function in the Essay on Enabling, Enabled Structures, and
; Theories.

  (let* ((old-rcnst (access prove-spec-var old-pspv
                            :rewrite-constant))
         (old-ens (access rewrite-constant old-rcnst
                          :current-enabled-structure))
         (old-name (access enabled-structure old-ens
                           :array-name))
         (new-rcnst (access prove-spec-var new-pspv
                            :rewrite-constant))
         (new-ens (access rewrite-constant new-rcnst
                          :current-enabled-structure))
         (new-name (access enabled-structure new-ens
                           :array-name)))
    (prog2$ (cond ((equal old-name new-name) nil)
                  (t (flush-compress new-name)))
            (change prove-spec-var new-pspv
                    :rewrite-constant old-rcnst
                    :hint-settings (access prove-spec-var old-pspv
                                           :hint-settings)))))

(defun remove-trivial-clauses (clauses wrld)
  (cond
   ((null clauses) nil)
   ((trivial-clause-p (car clauses) wrld)
    (remove-trivial-clauses (cdr clauses) wrld))
   (t (cons (car clauses)
            (remove-trivial-clauses (cdr clauses) wrld)))))

#+:non-standard-analysis
(defun non-standard-vector-check (vars accum)
  (if (null vars)
      accum
    (non-standard-vector-check (cdr vars)
                               (cons (mcons-term* 'standardp (car vars))
                                     accum))))

#+:non-standard-analysis
(defun merge-ns-check (checks clause accum)
  (if (null checks)
      accum
    (merge-ns-check (cdr checks) clause (cons (cons (car checks)
                                                    clause)
                                              accum))))

#+:non-standard-analysis
(defun trap-non-standard-vector-aux (cl-set accum-cl checks wrld)
  (cond ((null cl-set) accum-cl)
        ((classical-fn-list-p (all-fnnames-lst (car cl-set)) wrld)
         (trap-non-standard-vector-aux (cdr cl-set) accum-cl checks wrld))
        (t
         (trap-non-standard-vector-aux (cdr cl-set)
                                       (append (merge-ns-check checks
                                                               (car cl-set)
                                                               nil)
                                               accum-cl)
                                       checks
                                       wrld))))

#+:non-standard-analysis
(defun remove-adjacent-duplicates (x)

; We have slightly modified the original definition so as to match the
; definition (quite likely adapted from the original one here) in community
; book books/defsort/remove-dups.lisp.  Sol Swords points out that an
; unconditional rule true-listp-of-remove-adjacent-duplicates in that book
; relies on (list (car x)) in the second case below, rather than x.

  (declare (xargs :guard t))
  (cond ((atom x)
         nil)
        ((atom (cdr x))
         (list (car x))) ; See comment above for why this is not x.
        ((equal (car x) (cadr x))
         (remove-adjacent-duplicates (cdr x)))
        (t
         (cons (car x)
               (remove-adjacent-duplicates (cdr x))))))

(defun remove-adjacent-duplicates-eq (x)

; See remove-adjacent-duplicates.

  (declare (xargs :guard t))
  (cond ((atom x)
         nil)
        ((atom (cdr x))
         (list (car x)))
        ((eq (car x) (cadr x))
         (remove-adjacent-duplicates-eq (cdr x)))
        (t
         (cons (car x)
               (remove-adjacent-duplicates-eq (cdr x))))))

#+:non-standard-analysis
(defun non-standard-induction-vars (candidate wrld)
  (remove-adjacent-duplicates
   (merge-sort-term-order
    (append (access candidate candidate :changed-vars)

; The following line was changed after Version_3.0.1.  It seems like a correct
; change, but we'll leave this comment here until Ruben Gamboa (ACL2(r) author)
; checks this change.

            (measured-variables candidate wrld)))))

#+:non-standard-analysis
(defun trap-non-standard-vector (cl-set candidate accum-cl wrld)
  (trap-non-standard-vector-aux cl-set accum-cl
                                (non-standard-vector-check
                                 (non-standard-induction-vars
                                  candidate wrld)
                                 nil)
                                wrld))

(defun induct (forcing-round pool-lst cl-set hint-settings pspv wrld ctx state)

; We take a set of clauses, cl-set, and return four values.  The first
; is either the signal 'lose (meaning we could find no induction to do
; and have explained that to the user) or 'continue, meaning we're
; going to use induction.  The second value is a list of clauses,
; representing the induction base cases and steps.  The last two
; things are new values for pspv and state.  We modify pspv to store
; the induction-hyp-terms and induction-concl-terms for the
; simplifier.

; The clause set we explore to collect the induction candidates,
; x-cl-set, is not necessarily cl-set.  If the value, v, of :induct in
; the hint-settings is non-nil and non-*t*, then we explore the clause
; set {{v}} for candidates.

  (let ((cl-set (remove-guard-holders-lst-lst cl-set wrld))
        (pool-name
         (tilde-@-pool-name-phrase forcing-round pool-lst))
        (induct-hint-val
         (let ((induct-hint-val0
                (cdr (assoc-eq :induct hint-settings))))
           (and induct-hint-val0
                (remove-guard-holders induct-hint-val0 wrld)))))
    (mv-let
     (erp new-pspv state)
     (load-hint-settings-into-pspv
      nil
      (if induct-hint-val
          (remove1-assoc-eq :induct hint-settings)
        hint-settings)
      pspv nil wrld ctx state)
     (cond
      (erp (mv 'lose nil pspv state))
      (t
       (let* ((candidates
               (get-induction-cands-from-cl-set
                (select-x-cl-set cl-set induct-hint-val)
                new-pspv wrld state))
              (flushed-candidates
               (m&m candidates 'flush-candidates))

; In nqthm we flushed and merged at the same time.  However, flushing
; is a mate and merge function that has the distributive and non-preclusion
; properties and hence can be done with a simple m&m.  Merging on the other
; hand is preclusive and so we wait and run m&m-over-powerset to do
; that.  In nqthm, we did preclusive merging with m&m (then called
; TRANSITIVE-CLOSURE) and just didn't worry about the fact that we
; messed up some potential merges by earlier merges.  Of course, the
; powerset computation is so expensive for large sets that we can't
; just go into it blindly, so we don't use the m&m-over-powerset to do
; flushing and merging at the same time.  Flushing eliminates duplicates
; and subsumed inductions and thus shrinks the set as much as we know how.

              (merged-candidates
               (cond ((< (length flushed-candidates) 10)
                      (m&m-over-powerset flushed-candidates 'merge-candidates))
                     (t (m&m flushed-candidates 'merge-candidates))))

; Note: We really respect powerset.  If the set we're trying to merge
; has more than 10 things in it -- an arbitrary choice at the time of
; this writing -- we just do the m&m instead, which causes us to miss
; some merges because we only use each candidate once and merging
; early merges can prevent later ones.

              (unvetoed-candidates
               (compute-vetoes merged-candidates wrld))

              (complicated-candidates
               (maximal-elements unvetoed-candidates 'induction-complexity
                                 wrld))

              (high-scoring-candidates
               (maximal-elements complicated-candidates 'score wrld))
              (winning-candidate (car high-scoring-candidates)))
         (cond
          (winning-candidate
           (mv-let
            (erp candidate-ttree state)
            (accumulate-ttree-and-step-limit-into-state
             (access candidate winning-candidate :ttree)
             :skip
             state)
            (declare (ignore erp))
            (let* (

; First, we estimate the size of the answer if we persist in using cl-set.

                   (estimated-size
                    (induction-formula-size cl-set
                                            (access candidate
                                                    winning-candidate
                                                    :tests-and-alists-lst)))

; Next we create clauses, the set of clauses we wish to prove.
; Observe that if the estimated size is greater than
; *maximum-induct-size* we squeeze the cl-set into the form {{p}},
; where p is a single term.  This eliminates the combinatoric
; explosion at the expense of making the rest of the theorem prover
; suffer through opening things back up.  The idea, however, is that
; it is better to give the user something to look at, so he sees the
; problem blowing up in front of him in rewrite, than to just
; disappear into induction and never come out.  We have seen simple
; cases where failed guard conjectures would have led to inductions
; containing thousands of cases had induct been allowed to compute
; them out.

                   (clauses0
                    (induction-formula
                     (cond ((> estimated-size *maximum-induct-size*)
                            (list (list (termify-clause-set cl-set))))
                           (t cl-set))
                     (access candidate winning-candidate
                             :tests-and-alists-lst)))
                   (clauses1
                    #+:non-standard-analysis
                    (trap-non-standard-vector cl-set
                                              winning-candidate
                                              clauses0
                                              wrld)
                    #-:non-standard-analysis
                    clauses0)
                   (clauses
                    (cond ((> estimated-size *maximum-induct-size*)
                           clauses1)
                          (t (remove-trivial-clauses clauses1 wrld))))

; Now we inform the simplifier of this induction and store the ttree of
; the winning candidate into the tag-tree of the pspv.

                   (newer-pspv
                    (inform-simplify
                     (access candidate winning-candidate :tests-and-alists-lst)
                     (add-to-set-equal
                      (access candidate winning-candidate
                              :xinduction-term)
                      (access candidate winning-candidate :xother-terms))
                     (change prove-spec-var new-pspv
                             :tag-tree
                             (cons-tag-trees
                              candidate-ttree
                              (access prove-spec-var new-pspv :tag-tree))))))

; Now we print out the induct message.

              (let ((state
                     (io? prove nil state
                          (wrld clauses estimated-size winning-candidate
                                high-scoring-candidates complicated-candidates
                                unvetoed-candidates merged-candidates
                                flushed-candidates candidates induct-hint-val
                                cl-set forcing-round pool-lst)

                          (induct-msg/continue
                           pool-lst
                           forcing-round
                           cl-set
                           induct-hint-val
                           (length candidates)
                           (length flushed-candidates)
                           (length merged-candidates)
                           (length unvetoed-candidates)
                           (length complicated-candidates)
                           (length high-scoring-candidates)
                           winning-candidate
                           estimated-size
                           clauses
                           wrld
                           state))))
                (mv 'continue
                    clauses
                    newer-pspv
                    state)))))
          (t

; Otherwise, we report our failure to find an induction and return the
; 'lose signal.

           (pprogn (io? prove nil state
                        (induct-hint-val pool-name new-pspv)
                        (induct-msg/lose pool-name induct-hint-val new-pspv
                                         state))
                   (mv 'lose nil pspv state))))))))))

; We now define the elimination of irrelevance.  Logically this ought
; to be defined when the other processors are defined.  But to
; partition the literals of the clause by variables we use m&m, which
; is not defined until induction.  We could have moved m&m-apply back
; into the earlier processors, but that would require moving about a
; third of induction back there.  So we have just put all of
; irrelevance elimination here.

(defun pair-vars-with-lits (cl)

; We pair each lit of clause cl with its variables.  The variables are
; in the car of the pair, the singleton set containing the lit is in
; the cdr.

  (cond ((null cl) nil)
        (t (cons (cons (all-vars (car cl)) (list (car cl)))
                 (pair-vars-with-lits (cdr cl))))))


(mutual-recursion

(defun ffnnames-subsetp (term lst)

; Collect the ffnames in term and say whether it is a subset of lst.
; We don't consider fnnames of constants, e.g., the cons of '(a b).

  (cond ((variablep term) t)
        ((fquotep term) t)
        ((flambda-applicationp term)
         (and (ffnnames-subsetp-listp (fargs term) lst)
              (ffnnames-subsetp (lambda-body (ffn-symb term)) lst)))
        ((member-eq (ffn-symb term) lst)
         (ffnnames-subsetp-listp (fargs term) lst))
        (t nil)))

(defun ffnnames-subsetp-listp (terms lst)
  (cond ((null terms) t)
        ((ffnnames-subsetp (car terms) lst)
         (ffnnames-subsetp-listp (cdr terms) lst))
        (t nil)))
)

;; Historical Comment from Ruben Gamboa:
;; I added realp and complexp to the list of function names
;; simplification can decide.

(defun probably-not-validp (cl)

; Cl is a clause that is a subset of some clause, cl2, that has survived
; simplification.  We are considering whether cl seems useless in proving cl2;
; if so, we return t.  In particular, we return t if we think there is an
; instantiation of cl that makes each literal false.

; We have two trivial heuristics.  One is to detect whether the only function
; symbols in cl are ones that we think make up a fragment of the theory that
; simplification can decide.  The other heuristic is to bet that any cl
; consisting of a single literal which is of the form (fn v1 ... vn) or (not
; (fn v1 ... vn)), where the vi are distinct variables, is probably not valid.

; We elaborate a bit.  For eliminating irrelevance, we view a clause as

; (forall x y)(p(x) \/ q(y))

; where p(x) is a possibly irrelevant literal (or set of literals, but we focus
; here on the case of a single literal) and q(y) is the disjunction of the
; other literals.  In general, of course, each of these terms may have several
; free variables; but even in general, in order for p(x) to be a candidate for
; irrelevance, its set of variables must be disjoint from the set of variables
; in q.  In that case the clause is logically equivalent to the following.

; (forall x)p(x) \/ (forall y)q(y)

; We'd like to ignore one of those disjuncts when choosing an induction
; (actually q could itself be a disjunction on which we recur); but which one?
; If p(x) is probably not valid then we consider it reasonable to ignore p(x) in
; the hope that q(y) may be valid, and indeed provable by ACL2.

; See also the Essay on Alternate Heuristics for Eliminate-Irrelevance.

  (or (ffnnames-subsetp-listp cl '(not consp integerp rationalp
                                       #+:non-standard-analysis realp
                                       acl2-numberp
                                       true-listp complex-rationalp
                                       #+:non-standard-analysis complexp
                                       stringp characterp
                                       symbolp cons car cdr equal
                                       binary-+ unary-- < apply))
      (case-match cl
        ((('not (& . args)))

; To understand why we require args to be non-nil, see the Essay on Alternate
; Heuristics for Eliminate-Irrelevance.

         (and args ; do not drop zero-ary call (see above)
              (all-variablep args)
              (no-duplicatesp-eq args)))
        (((& . args))
         (and args  ; do not drop zero-ary call (see above)
              (all-variablep args)
              (no-duplicatesp-eq args)))
        (& nil))))

(defun irrelevant-lits (alist)

; Alist is an alist that associates a set of literals with each key.  The keys
; are irrelevant.  We consider each set of literals and decide if it is
; probably not valid.  If so we consider it irrelevant.  We return the
; concatenation of all the irrelevant literal sets.

  (cond ((null alist) nil)
        ((probably-not-validp (cdar alist))
         (append (cdar alist) (irrelevant-lits (cdr alist))))
        (t (irrelevant-lits (cdr alist)))))

(defun eliminate-irrelevance-clause (cl hist pspv wrld state)

; A standard clause processor of the waterfall.

; We return 4 values.  The first is a signal that is either 'hit, or
; 'miss.  When the signal is 'miss, the other 3 values are irrelevant.
; When the signal is 'hit, the second result is the list of new
; clauses, the third is a ttree that will become that component of the
; history-entry for this elimination, and the fourth is an
; unmodified pspv.  (We return the fourth thing to adhere to the
; convention used by all clause processors in the waterfall (q.v.).)

; Essay on Alternate Heuristics for Eliminate-Irrelevance

; The algorithm for dropping "irrelevant" literals is based on first
; partitioning the literals of a clause into components with respect to the
; symmetric binary relation defined by: two literals are related if and only if
; they share at least one free variable.  We consider two ways for a component
; to be irrelevant: either (A) its function symbols are all from among a small
; fixed set of primitives, or else (B) the component has a single literal whose
; atom is the application of a function symbol to distinct variables.
; Criterion B, however, is somewhat problematic, and below we discuss
; variations of it that we have considered.  (See function probably-not-validp
; for relevant code.)

; Through Version_7.2, Criterion B was exactly as stated above.  However, we
; encountered an unfortunate aspect of that heuristic, which is illustrated by
; the following example (which is simpler than the one actually encountered,
; but is similar in spirit).  The THM below failed to prove in Version_7.2.

;   (encapsulate
;     ((p () t)
;      (my-app (x y) t))
;     (local (defun p () t))
;     (local (defun my-app (x y) (append x y)))
;     (defthm my-app-def
;       (implies (p)
;                (equal (my-app x y)
;                       (if (consp x)
;                           (cons (car x) (my-app (cdr x) y))
;                         y)))
;       :rule-classes ((:definition
;                       :controller-alist ((my-app t nil))))))
;
;   (defun rev (x)
;     (if (consp x)
;         (my-app (rev (cdr x))
;                 (cons (car x) nil))
;       nil))
;
;   (thm (implies (and (p)
;                      (true-listp x))
;                 (equal (rev (rev x)) x)))

; The problem was that before entering a sub-induction, the hypothesis (P) --
; that is, the literal (NOT (P)) -- was dropped.  Here is the relevant portion
; of a log using Version_7.2.

;   Subgoal *1/2'5'
;   (IMPLIES (AND (P) (TRUE-LISTP X2))
;            (EQUAL (REV (MY-APP RV (LIST X1)))
;                   (CONS X1 (REV RV)))).
;
;   We suspect that the terms (TRUE-LISTP X2) and (P) are irrelevant to
;   the truth of this conjecture and throw them out.  We will thus try
;   to prove
;
;   Subgoal *1/2'6'
;   (EQUAL (REV (MY-APP RV (LIST X1)))
;          (CONS X1 (REV RV))).
;
;   Name the formula above *1.1.

; Since the exported defthm above requires (P) in order to expand MY-APP, the
; goal displayed immediately above isn't a theorem.  So we desired a
; modification of the Criterion B above, on components, that would no longer
; drop (P).

; Our initial solution was a bit elaborate.  In essence, it maintained a world
; global whose value is an alist that identifies "never irrelevant" function
; symbols.  For a rewrite rule, if a hypothesis and the left-hand side had
; disjoint sets of free variables, and the hypothesis was the application of
; some function symbol F to distinct variables, then F was identified as "never
; irrelevant".  We actually went a bit further, by associating a "parity" with
; each such function symbol, both because the hypothesis might actually be (NOT
; (F ...)) and because we allowed the left-hand side to contribute.  The
; "parity" could be t or nil, or even :both (to represent both parities).  We
; extended this world global not only for rewrite rules but also for rules of
; class :definition, :forward-chaining, :linear, and :type-prescription.

; That seemed to work well: it solved our original problem without noticeably
; slowing down the regression suite or even the time for the expensive form
; (include-book "doc/top" :dir :system).

; We then presented this change in the UT Austin ACL2 seminar, and a sequence
; of events caused us to change our heuristics again.

;   (1) During that talk, we stressed the importance of dropping irrelevant
;       literals so that an unsuitable induction isn't selected.  Marijn Heule
;       thus made the intriguing suggestion of keeping the literals and simply
;       ignoring them in our induction heuristics.
;
;   (2) We tried such a change.  Our implementation actually caused
;       eliminate-irrelevance-clause to hide the irrelevant literals rather
;       then to delete then; then, induction would unhide them immediately
;       after choosing an induction scheme.
;
;   (3) The regression exhibited failures, however, because subsumption was no
;       longer succeeding in cases where it had previously -- a goal was no
;       longer subsumed by a previous sibling, but was subsumed by the original
;       goal, causing the proof to abort immediately.  (See below for details.)
;
;   (4) So we decided to drop literals once again, rather than merely to hide
;       them.
;
;   (5) But on further reflection, it seemed a bit far-fetched that a
;       hypothesis (P1 X) could be relevant to simplifying (P2 Y Z) in the way
;       shown above that (P) can be relevant to simplifying (P2 Y Z).  We can
;       construct an example; but we think such examples are likely to be rare.
;       The failures due to lack of subsumption led us to be nervous about
;       keeping literals that Criterion B would otherwise delete.  So we
;       decided on a very simple modification of Criterion B: only drop
;       applications of functions to one or more variables.  This very limited
;       case of keeping a literal seems unlikely to interfere with subsumption,
;       since that literal could typically be reasonably expected to occur in
;       all goals that are stable under simplification.

; Returning to (3) above, here is how subsumption failed for lemma perm-del in
; community book books/models/jvm/m5/perm.lisp, when we merely applied HIDE to
; literals rather than deleting them.  In the failed proof, we see the
; following.

;   Subgoal *1.1/4'''
;   (IMPLIES (AND (NOT (HIDE (CONSP X2)))
;                 (NOT (EQUAL A X1))
;                 (MEM X1 Y)
;                 (NOT (HIDE (CONSP DL))))
;            (MEM X1 (DEL A Y))).
;
;   Name the formula above *1.1.1.

; Then later we see:

;   So we now return to *1.1.2, which is
;
;   (IMPLIES (AND (NOT (PERM (DEL X3 X4) (DEL X3 DL0)))
;                 (NOT (EQUAL X3 X1))
;                 (MEM X1 Y)
;                 (MEM X3 DL)
;                 (PERM X4 DL0))
;            (MEM X1 (DEL X3 Y))).

; In Version_7.2 and also currently, the terms with HIDE in the first goal are
; simply gone; so the first goal subsumes the second goal under the
; substitution mapping A to X3.  However, with the first goal as shown above
; (from our experiment in hiding irrelevant literals), subsumption fails
; because the hypothesis (NOT (HIDE (CONSP X2))) -- that is, the literal (HIDE
; (CONSP X2)) -- is not present in the second goal.

  (declare (ignore hist wrld state))
  (cond
   ((not (assoc-eq 'being-proved-by-induction
                   (access prove-spec-var pspv :pool)))
    (mv 'miss nil nil nil))
   (t (let* ((partitioning (m&m (pair-vars-with-lits cl)
                                'intersectp-eq/union-equal))
             (irrelevant-lits (irrelevant-lits partitioning)))
        (cond ((null irrelevant-lits)
               (mv 'miss nil nil nil))
              (t (mv 'hit
                     (list (set-difference-equal cl irrelevant-lits))
                     (add-to-tag-tree!
                      'irrelevant-lits irrelevant-lits
                      (add-to-tag-tree!
                       'clause cl nil))
                     pspv)))))))

(defun eliminate-irrelevance-clause-msg1 (signal clauses ttree pspv state)

; The arguments to this function are the standard ones for an output
; function in the waterfall.  See the discussion of the waterfall.

  (declare (ignore signal pspv clauses))
  (let* ((lits (tagged-object 'irrelevant-lits ttree))
         (clause (tagged-object 'clause ttree))
         (concl (car (last clause))))
    (cond
     ((equal (length lits)
             (length clause))
      (fms "We suspect that this conjecture is not a theorem.  We ~
            might as well be trying to prove~|"
           nil
           (proofs-co state)
           state
           (term-evisc-tuple nil state)))
     (t
      (let ((iterms (cond
                     ((member-equal concl lits)
                      (append
                       (dumb-negate-lit-lst
                        (remove1-equal concl lits))
                       (list concl)))
                     (t (dumb-negate-lit-lst lits)))))
        (fms "We suspect that the term~#0~[ ~*1 is~/s ~*1 are~] irrelevant to ~
              the truth of this conjecture and throw ~#0~[it~/them~] out.  We ~
              will thus try to prove~|"
             (list
              (cons #\0 iterms)
              (cons #\1 (tilde-*-untranslate-lst-phrase iterms t (w state))))
             (proofs-co state)
             state
             (term-evisc-tuple nil state)))))))

