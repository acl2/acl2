; Copyright (C) 2016, ForrestHunt, Inc.
; Written by Matt Kaufmann and J Moore
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; The Constraints for the General-Purpose APPLY*

; This file builds on top of apply-prim.lisp and introduces the the four apply$
; stubs: BADGE-USERFN, APPLY$-USERFN, UNTAME-APPLY$ and UNTAME-EV$ and
; initializes the table in which we record the badges of user-defined
; functions.

; This file is used as the portcullis for the ``general-purpose'' version of
; the apply.lisp book.  (We also develop a portcullis for a special-purpose
; version in which the stubs are defined to be the doppelgangers of their
; respective constrained functions as of the end of a particular user-book.
; See script.lsp.)

; The definition of apply$ in apply.lisp relies on the stubs BADGE-USERFN and
; APPLY$-USERFN to access information about and to apply user defined
; functions, e.g., mapping functions, like SUMLIST, defined by the user with
; defun$.  (The other two stubs just denote ``undefined'' values, e.g., when an
; untame function is applied.)  The ``badge'' of a function describes how it
; uses its formals, e.g., the first argument of SUMLIST is an ordinary object
; but the second argument of SUMLIST is supposed to be a tame function symbol.
; There are no axioms connecting symbols to the functions they denote or to the
; badges of those functions.  Instead, defun$ introduces a ``warrant'' which
; must be included in the governing hypotheses of any theorem whose proof
; involves reasoning about the meaning of APPLY$ on that particular function
; symbol.  The warrant of fn is a 0-ary predicate named apply$-warrant-fn,
; which specifies the badge of 'fn and the conditions under which (apply$ 'fn
; args) = (fn (car args) ... (cad...r args)).  Warrants solve the ``Local
; Problem.''  We claim that for any given user book certified on top of
; apply.lisp we could attach defined functions to badge-userfn and
; apply$-userfn so that all the warrants are valid in the resulting evaluation
; theory.  We demonstrate this for a particular book named user-book.lisp.  See
; script.lsp.  This claim assures the user that theorems about apply$
; (encumbered with warrants) are ``meaningful'' by which we mean they are not
; vacuous due to the falsity of their warrants.

; See the apply book for details.

; WARNING: The apply book sets up and maintains two data structures used to
; associate badges with primitive and nonprimitive function symbols.  These
; tables are used in the analysis of newly defined functions to make sure that
; they respect the badges of all their subroutines.  Our claim above, about
; making warrants valid, can be made false if the user messes with these data
; structures, e.g., changes the badge of a user-defined function from that
; computed and stored by defun$.  This doesn't make the system unsound.  But it
; may make theorems encumbered with warrants vacuously valid.  If and when the
; apply$ work becomes part of ACL2, these data structures must be protected
; from the user!  The easiest way to do that would add a new property, e.g.,
; BADGE, to the logical world and store each symbol's badge (if any) there.

(in-package "MODAPP")
(include-book "apply-prim")

; -----------------------------------------------------------------
; Handling the Primitives

; Reminders and Warnings: The apply-prim.lisp book, included below,
; defines APPLY$-PRIMP, BADGE-PRIM, and APPLY$-PRIM in :logic mode.  These
; functions are used to access information about and apply primitives like CAR
; and BINARY-+.  The first two are guard verified but APPLY$-PRIM cannot be
; guard verified because it may well violate guards, e.g., (apply$-prim 'CAR
; (list 7)).  To use apply$-prim in a guard verified setting (as we do in
; apply.lisp) we call it inside ec-call.  We also know via badge-prim-type that
; when (apply$-primp fn) is true then (apply$-badgep (badge-prim fn)) and
; (cdddr (badge-prim fn))=t.

; The apply-prim book also defines the constant *badge-prim-falist* which is a
; fast-alist with entries of the form (fn . (APPLY$-BADGE flg arity . T)).  One
; should not hons-acons anything onto this object because that would steal the
; hash table out from under the current value and slow down apply$-primp and
; badge-prim which use hons-get to access this constant.

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

; We have contemplated strengthening the constraint shown in badge-userfn-type
; above to:

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

; This additional conjunct is easily achieved, though it requires moving up a
; few defconsts below so we can use them in the defthm above.  It is already
; achieved by badger-userfn! in doppelgangers.lisp, where the final otherwise
; clause is nil.

; But it is hard to achieve in the our current ACL2 sources because those
; sources do not include apply-prim.lisp and so apply$-primp is not defined
; when we try to constrain concrete-badge-userfn in other-events.lisp.

; If and when apply$ is made an ACL2 primitive, we could strengthen this
; constraint.  On the other hand, so far, we haven't seen a proof where the
; stronger constraint is required.  It is just odd that, for all we know,
; (badge-userfn 'cons) is something weird and thought-provoking like
; '(APPLY$-BADGE T 2 NIL :FN) suggesting it's a mapping function!  That doesn't
; really mess us up because we use badge, not badge-userfn, to access badges,
; and badge checks the primitives and boot functions before relying on
; badge-userfn.  So the value of badge-userfn on primitives and boot functions
; is actually irrelevant.

; End of Note

; Apply$-userfn is totally unconstrained but has a guard.

(encapsulate
  ((apply$-userfn (fn args) t :guard (true-listp args)))
  (local (defun apply$-userfn (fn args)
           (declare (ignore fn args))
           nil)))

; These two stubs are used as the ``default values'' of (apply$ fn args) and
; (ev$ x a) when the arguments are not suitably tame.

(defstub untame-apply$ (fn args) t)
(defstub untame-ev$ (x a) t)

; The ``badge table'' is a table that associates badges with nonprimitive
; function symbols.  It is extended by def-warrant.  The user best not mess
; with it!

; Three categories of function symbols have badges:

; * ACL2 primitives -- all the primitives and their badges are listed in
;   *badge-prim-falist*, a fast alist whose length is ~800.  This constant is
;   defined in apply-prim.lisp.

; * apply$ boot fns -- six symbols built into apply$ itself, which cannot get
;   badges via the normal process available to the user because of
;   bootstrapping issues.  These are listed in the constant
;   *apply$-boot-fns-badge-alist*, defined here:

(defconst *apply$-boot-fns-badge-alist*
  `((BADGE . ,*generic-tame-badge-1*)
    (TAMEP . ,*generic-tame-badge-1*)
    (TAMEP-FUNCTIONP . ,*generic-tame-badge-1*)
    (SUITABLY-TAMEP-LISTP . ,*generic-tame-badge-2*)
    (APPLY$ . ,*apply$-badge*)
    (EV$ . ,*ev$-badge*)))

; * user-defined functions -- functions successfully processed by def-warrant
;   and listed under the key :badge-userfn-structure (currently a simple alist)
;   in the badge-table, initialized below but accumulated by def-warrant.  (The
;   badge-table has another key, described and initialized further below.)

(table badge-table
       :badge-userfn-structure
       nil)

; Badges versus Warrants

; Warrant (Merriam-Webster)
; [noun] commission or document giving authority to do something

; In our case, a warrant for function symbol fn is a 0-ary predicate named
; APPLY$-WARRANT-fn that specifies value of (badge 'fn) and the ``tameness''
; conditions under which (apply$ 'fn args) = (fn (car args) ... (cad...dr
; args)).

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

