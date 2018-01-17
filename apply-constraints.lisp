; ACL2 Version 8.0 -- A Computational Logic for Applicative Common Lisp
; Copyright (C) 2017, Regents of the University of Texas

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

; Many thanks to ForrestHunt, Inc. for supporting the preponderance of this
; work, and for permission to include it here.

; The Constraints on apply$

; See the Essay on the APPLY$ Integration in apply-prim.lisp for an overview.

; This file builds on top of apply-prim.lisp and introduces the the four apply$
; stubs: BADGE-USERFN, APPLY$-USERFN, UNTAME-APPLY$ and UNTAME-EV$ and
; initializes the table in which we record the badges of user-defined
; functions.

; The definition of apply$ in apply.lisp relies on the stubs BADGE-USERFN and
; APPLY$-USERFN to access information about and to apply user defined
; functions, e.g., mapping functions, like SUMLIST, defined by the user with
; defun$.  (The other two stubs just denote ``undefined'' values, e.g., used
; when an untame function is applied.)  The ``badge'' of a function describes
; how it uses its formals.  Badges report the arity of the symbol and the
; ``ilks'' of its formals (tokens indicating whether the value of the formal is
; treated as an as ordinary objects, a function, or an expression).

; The ``warrant'' of a symbol fn is a 0-ary predicate named APPLY$-WARRANT-fn,
; which specifies the badge of 'fn and the conditions under which (apply$ 'fn
; args) = (fn (car args) ... (cad...r args)).  Warrants solve the ``Local
; Problem.''

; We prove in the paper, ``Limited Second Order Functionality in a First Order
; Setting'', that for any certified user book we could attach defined functions
; to badge-userfn and apply$-userfn so that all the warrants are valid in the
; resulting evaluation theory.  This is illustrated in the Foundations group
; for two different ``user books'' under the subdirectories ex1/ and ex2/.
; This claim assures the user that theorems about apply$ (encumbered with
; warrants) are ``meaningful'' by which we mean they are not vacuous due to the
; falsity of their warrants.

(in-package "ACL2")

; Note: This entire file is processed only in pass 2.  We might be able to
; loosen that and process these events more generally.  But there is no point:
; the functions introduced here, e.g., badge-userfn and apply$-userfn, are used
; in the definitions of badge and apply$.  But those definitions use
; apply$-primp and apply$-prim, from apply-prim.lisp, which are only defined in
; pass 2.  So there's really no point in introducing badge-userfn and
; apply$-userfn any earlier.

(when-pass-2

; -----------------------------------------------------------------
; Handling the Primitives

; Reminder: The apply-prim book defines the constant *badge-prim-falist* which
; is a fast-alist with entries of the form (fn . (APPLY$-BADGE flg arity . T)).
; One should not hons-acons anything onto this object because that would steal
; the hash table out from under the current value and slow down apply$-primp
; and badge-prim which use hons-get to access this constant.

; -----------------------------------------------------------------
; BADGE-USERFN and APPLY$-USERFN

; The definition of APPLY$ relies on the constrained functions badge-userfn
; and apply$-userfn to access information about and to apply nonprimitive
; functions.

; Badge-userfn is constrained to return nil or an apply$-badge.  The latter
; are non-cheap records with token name APPLY$-BADGE and accessors
; :authorization-flg, :arity, and :ilks.  We abbreviate the :authorization-flg
; value as flg below.  If flg is t, then we know the associated function, fn,
; returns a single value and is stobj- and state-free, and treats its arguments
; as described by the ilks of the badge.  Flg is nil if fn returns multiple
; values but is otherwise ok, i.e., is stobj- and state-free and treats its
; arguments as described by the ilks.  In either case, arity is the arity of fn
; and ilks indicates how the arguments are used.  Most generally, ilks is a
; list, as long as the formals, of flags NIL, :FN, and/or :EXPR, indicating
; that the corresponding formal is used in a ``vanilla'' (conventional) way, as
; a function only inspected by APPLY$, or as an expression only inspected by
; EV$.  If the ilks is a list (c_1 ... c_arity), we say c_i is the ``ilk'' of
; the ith argument.  We make a special case of when all the formals are
; ordinary, i.e., when each ilk is NIL.  We denote this with ilks = T.  (This
; is admittedly a bit confusing, ``T is an abbreviation for a list of NILs.'')

; The reason we impose any constraint on the shape of the object returned by
; badge-userfn is so that we can verify guards for tamep and apply$ without
; having to check these facts about the badge returned.

(encapsulate
  ((badge-userfn (fn) t))
  (local (defun badge-userfn (fn)
           (declare (ignore fn))
           nil))
  (defthm badge-userfn-type
    (implies (badge-userfn fn)
             (apply$-badgep (badge-userfn fn)))
    :rule-classes
    ((:forward-chaining))))

; Note on Strengthening the Constraint in badge-userfn-type

; The constraint above says that badge-userfn either returns nil or a
; well-formed badge.  We have contemplated strengthening that constraint to add
; that on apply$ primitives and symbols listed in *apply$-boot-fns-badge-alist*
; badge-userfn is nil.  That is, the strengthened constraint would tell us we
; don't have to entertain the possibility that, e.g., (badge-userfn 'CONS) is
; non-nil.  The strengthened constraint would be:

;   (defthm badge-userfn-type
;     (and (or (null (badge-userfn fn))
;              (apply$-badgep (badge-userfn fn)))
;          (implies (or (apply$-primp fn)
;                       (assoc-eq fn *apply$-boot-fns-badge-alist*))
;                   (equal (badge-userfn fn) nil)))
;     :rule-classes
;     ((:rewrite
;       :corollary
;       (implies (or (apply$-primp fn)
;                    (assoc-eq fn *apply$-boot-fns-badge-alist*))
;                (equal (badge-userfn fn) nil)))
;      (:forward-chaining
;       :corollary (implies (badge-userfn fn)
;                           (apply$-badgep (badge-userfn fn))))))

; One can imagine that knowing the extra conjunct would make some proofs easier
; or faster, e.g., if badge-userfn is non-nil (as implied by the warrant for
; fn) then we'd know fn isn't among the ~800 primitives or the six boot
; functions.

; This additional conjunct can probably be easily added, though it would
; require moving up the definition below of *apply$-boot-fns-badge-alist* so we
; can use it in the new constraint.

; More problematically, we must make sure that concrete-badge-userfn satisfies
; the strengthened constraint.  This is difficult because concrete-badge-userfn
; is currently (partially) constrained in other-events.lisp, which is processed
; before apply$-primp and *apply$-boot-fns-badge-alist* are defined.  The only
; way we can think of to fix this would be to move the introduction of
; concrete-badge-userfn into this file and deal with any bootstrapping issues
; that come up!  If this additional constraint is added, we would have to
; change the raw Lisp definition of concrete-badge-userfn, q.v. in
; apply-raw.lisp.

; (BTW: The ``doppelganger'' of badge-userfn (which must also satisfy this
; constraint) in the Foundational work of books/projects/apply-model/ex1/ and
; ex2/ already satisfies this additional constraint because the final otherwise
; clause in the doppelganger's definition is nil.)

; On the other hand, so far, we haven't seen a proof where the stronger
; constraint is required.  It is just odd that, for all we know, (badge-userfn
; 'cons) is something weird and thought-provoking like '(APPLY$-BADGE T 2 NIL
; :FN) suggesting it's a mapping function!  That doesn't really mess us up
; because we use badge, not badge-userfn, to access badges, and badge checks
; the primitives and boot functions before relying on badge-userfn.  So the
; value of badge-userfn on primitives and boot functions is actually
; irrelevant.

; End of Note

; Apply$-userfn is constrained to being sensitive only to the first n
; arguments, where n is the arity stored in the badge.

(encapsulate
  ((apply$-userfn (fn args) t :guard (true-listp args)))
  (local (defun apply$-userfn (fn args)
           (declare (ignore fn args))
           nil))
  (defthm apply$-userfn-takes-arity-args
    (implies (badge-userfn fn)
             (equal (apply$-userfn fn args)
                    (apply$-userfn fn (take (caddr (badge-userfn fn)) args))))
    :rule-classes nil))

; These two stubs are used as the ``default values'' of (apply$ fn args) and
; (ev$ x a) when the arguments are not suitably tame.

(defstub untame-apply$ (fn args) t)
(defstub untame-ev$ (x a) t)

; The ``badge table'' is a table that associates badges with nonprimitive
; function symbols.  It is extended by def-warrant.

; Three categories of function symbols have badges:

; * ACL2 primitives -- all the primitives and their badges are listed in
;   *badge-prim-falist*, a fast alist whose length is ~800.  This constant is
;   defined in apply-prim.lisp.

; * apply$ boot fns -- six symbols built into apply$ itself, which cannot get
;   badges via the normal process available to the user because of
;   bootstrapping issues.  These are listed in the constant
;   *apply$-boot-fns-badge-alist*, defined below.

;   Historical Note: The ``apply$ boot fns'' is a relic of the pre-integration
;   days.  When apply$ was introduced as a book it would have been shocking to
;   treat BADGE, say, as a primitive because it wasn't!  Now it is perhaps more
;   natural to consider it a primitive, but we don't!

; * user-defined functions -- functions successfully processed by def-warrant
;   and listed under the key :badge-userfn-structure (currently a simple alist)
;   in the badge-table, initialized in source file apply.lisp but accumulated
;   by def-warrant.

(defconst *apply$-boot-fns-badge-alist*
  `((BADGE . ,*generic-tame-badge-1*)
    (TAMEP . ,*generic-tame-badge-1*)
    (TAMEP-FUNCTIONP . ,*generic-tame-badge-1*)
    (SUITABLY-TAMEP-LISTP . ,*generic-tame-badge-2*)
    (APPLY$ . ,*apply$-badge*)
    (EV$ . ,*ev$-badge*)))

; Badges versus Warrants

; Warrant (Merriam-Webster)
; [noun] commission or document giving authority to do something

; In our case, a warrant for function symbol fn is a 0-ary predicate named
; APPLY$-WARRANT-fn that specifies value of (badge 'fn) and the ``tameness''
; conditions under which (apply$ 'fn args) = (fn (car args) ... (cad...dr
; args)).  (Technically, the warrant specifies the values of (badge-userfn 'fn)
; and (apply$-userfn 'fn args), which allow the definitions of badge and apply$
; to simplify appropriately.)

; Derivation History: This concept was originally called an ``applicability
; hypothesis'' and variations on that theme.  We decided to replace it with a
; simpler noun.  We considered ``ticket,'' ``pass,'' ``permit,'' and
; ``warrant'' as alternative names.  We decided ``ticket'' was too trite and
; didn't convey the fact that the concept includes a description of the
; function's use of its arguments and the tameness requirements.  ``Pass'' and
; ``permit'' are already used hundreds of times in the ACL2 sources and so are
; not good candidates for a word that might still be changed.  ``Warrant'' only
; occurs about a dozen times in the ACL2 sources as an isolated word
; (``warrant\b'' or ``warranted,'' excluding ``warranty'' which occurs twice at
; the top of nearly every file).

; Some functions have badges but not warrants!  All ~800 primitives have badges
; known to the logical definition of BADGE, but these primitives do not have
; warrants: there is no APPLY$-WARRANT-CONS because the badge of cons is
; built-in.  All 6 of the apply$ boot functions have badges known to BADGE and
; do not have warrants: apply$ knows how to apply$ itself.

; Every function listed in the :badge-userfn-structure of the badge-table has a
; badge.

; But not every function listed in the :badge-userfn-structure has a warrant!

; For example, (defun$ foo (x) (mv x x)) would produce a badge but not a
; warrant; foo obeys all the rules required of warranted functions except for
; one rule: foo returns multiple values and so cannot be apply$'d (because
; apply$ returns a single value). (defun$ bar (x) (mv-let (a b) (foo x) (+ a
; b))) would produce a badge and a warrant even though it uses the unwarranted
; but badged foo.  Both foo and bar would have entries in the
; :badge-userfn-structure of the badge-table mapping them to their badges.

; If fn has a badge, bdg, in :badge-userfn-structure then fn has a warrant iff
; (access apply$-badge bdg :authorization-flg).  The warrant, if it exists, is
; named APPLY$-WARRANT-fn and takes 0 arguments.

)
