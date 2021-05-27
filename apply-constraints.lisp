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
; is a fast-alist with entries of the form (fn . (APPLY$-BADGE arity out-arity
; . T)).  One should not hons-acons anything onto this object because that
; would steal the hash table out from under the current value and slow down
; apply$-primp and badge-prim which use hons-get to access this constant.

; -----------------------------------------------------------------
; BADGE-USERFN and APPLY$-USERFN

; The definition of APPLY$ relies on the constrained functions badge-userfn
; and apply$-userfn to access information about and to apply nonprimitive
; functions.

; Badge-userfn is constrained to return nil or an apply$-badge.  The latter are
; non-cheap records with token name APPLY$-BADGE and accessors :arity,
; :out-arity, and :ilks.  The existence of a badge means the function is is
; stobj- and state-free, and treats its arguments as described by the ilks of
; the badge.  Arity is the arity of fn, out-arity is the number of values it
; returns, and ilks indicates how the arguments are used.  Most generally, ilks
; is a list, as long as the formals, of flags NIL, :FN, and/or :EXPR,
; indicating that the corresponding formal is used in a ``vanilla''
; (conventional) way, as a function only inspected by APPLY$, or as an
; expression only inspected by EV$.  If the ilks is a list (c_1 ... c_arity),
; we say c_i is the ``ilk'' of the ith argument.  We make a special case of
; when all the formals are ordinary, i.e., when each ilk is NIL.  We denote
; this with ilks = T.  (This is admittedly a bit confusing, ``T is an
; abbreviation for a list of NILs.'')

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
; require rearranging the order of some things in the sources as well as in the
; model so we can use them when we introduce the contraint.

; On the other hand, so far, we haven't seen a proof where the stronger
; constraint is required.  It is just odd that, for all we know, (badge-userfn
; 'cons) is something weird and thought-provoking like '(APPLY$-BADGE 2 1 NIL
; :FN) suggesting it's a scion!  That doesn't really mess us up because we use
; badge, not badge-userfn, to access badges, and badge checks the primitives
; and boot functions before relying on badge-userfn.  So the value of
; badge-userfn on primitives and boot functions is actually irrelevant.

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
                    (apply$-userfn fn (take (apply$-badge-arity
                                             (badge-userfn fn))
                                            args))))
    :rule-classes nil))

; Untame-apply$ is used as the ``default value'' of apply$ when apply$ doesn't
; like its arguments.  We must constrain untame-apply$ to be sensitive to just
; two arguments in order to satisfy constraints on apply$ when we make
; attachments.

(encapsulate (((untame-apply$ * *) => *
               :formals (fn args)
               :guard (true-listp args)))
  (local (defun untame-apply$ (fn args)
           (declare (ignore fn args))
           nil))
  (defthm untame-apply$-takes-arity-args
    (implies (badge-userfn fn)
             (equal (untame-apply$ fn args)
                    (untame-apply$ fn (take (apply$-badge-arity
                                             (badge-userfn fn))
                                            args))))
    :rule-classes
    ((:rewrite
      :corollary (implies (and (syntaxp (and (quotep fn)
                                             (symbolp args)))
                               (badge-userfn fn))
                          (equal (untame-apply$ fn args)
                                 (untame-apply$ fn (take (apply$-badge-arity
                                                          (badge-userfn fn))
                                                         args))))))))

; Untame-ev$ is the default value for ev$.
(defstub untame-ev$ (x a) t)

; The ``badge table'' is a table that associates badges with nonprimitive
; function symbols.  It also contains a flag on each function symbol indicating
; whether there is a warrant function for it.  The badge-table is maintained by
; defwarrant.

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

; * user-defined functions -- functions successfully processed by defwarrant
;   and listed under the key :badge-userfn-structure (currently a simple alist)
;   in the badge-table and maintained by defwarrant.

; Only function symbols in the last category may have warrants.  Primitives and
; apply$ boot fns do not need warrants because they're built into the
; definition of apply$.  It was once the case that every function in the last
; category had a warrant but that should no longer be assumed.

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

; Functions can have badges but not warrants!  Approximately 800 primitives
; have badges known to the logical definition of BADGE but do not have
; warrants: there is no APPLY$-WARRANT-CONS because the badge of cons is
; built-in.  All 6 of the apply$ boot functions have badges known to BADGE and
; do not have warrants: e.g., apply$ knows how to apply$ itself.  Once upon a
; time multi-valued user-defined functions could have badges but no warrants.
; However, now that apply$ supports such functions multi-valued functions can
; have warrants.  See the Essay on the Badge-Table in translate.lisp.

)
