; Copyright (C) 2015, Regents of the University of Texas
; Written by Matt Kaufmann (with inspiration from Alessandro Coglio and Eric Smith)
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

(in-package "APT")

;;; TABLE OF CONTENTS
;;; -----------------
;;; TODO and FIXME items to consider doing
;;; Introductory remarks
;;; Included books
;;; Functions record (fnsr) structures
;;; Generating names and lists containing names
;;; Argument processing
;;; Miscellaneous utilities
;;; Handling hypotheses
;;; Deal with whether simplification must take place
;;; Rewriting
;;; Return-last blockers
;;; Simplifying a term
;;; Additional main utilities
;;; Putting it all together

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; TODO and FIXME items to consider doing
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; - Perhaps add to ./package.lsp to eliminate "acl2::" prefixes below.
; - Consider showing simplified hypotheses, as was done before mid-October
;   2020.  Note however that now we simplify hypotheses and governors together,
;   so we would presumably show both.
; - Consider arranging that :backchain-limit and :repeat arguments are
;   consistent, in particular between s-cmd in before-vs-after-lemmas
;   and arguments to acl2::rewrite$ and acl2::rewrite$-hyps.  :Repeat seems
;   consistent at 3, but currently we use :repeat 1 for rewrite$-hyps -- that
;   seems reasonable, to avoid too much computation for too little gain -- and
;   :repeat 3 for simplifying subterms.
; - Consider whether sorting of runes can be done more efficiently, by doing
;   more sorting along the way.  Search below for merge-sort-lexorder.
; - Support stobjs.  Of course this will require preserving stobj declarations.
;   It might be up to the user to disable stobj accessors and updaters.
;   Although there might be no immediate need, there will likely be a need for
;   this.
; - Preserve type declarations (rather than just fetching old guard and
;   simplifying).  It may be best to preserve type and stobj declarations
;   exactly and only simplify the :guard; be careful about satisfies and about
;   :split-types.
; - If measure is not simplified, perhaps get it, untranslated, from the
;   original definition (so that macros are still present).  Note: Eric S. is
;   changing utility fn-measure in utilities/world.lisp.
; - Reconcile handling of :verify-guards with respect to eagerness and default
;   value, with how that's taken into account in simplify-defun-sk.  Eric
;   S. prefers that declare forms are what the user would write when doing a
;   transformation manually, so if one of the two approaches is closer to that,
;   let's probably use that one.
; - Move check-equivalence-relation to a general utilities file, and perhaps
;   define it using def-error-checker.
; - Arrange that fn-copy-name (defined in community book
;   books/kestrel/utilities/copy-def.lisp) uses fresh-logical-name-with-$s-suffix
;   to avoid redefinition errors.
; - Avoid hard error (in favor of soft error) when unknown keyword is
;   supplied.  (This applies also to simplify-defun-sk and simplify-term.)
; - Do something about the case that :untranslate is :nice-expanded, since
;   currently, LET expressions tend to remain.  Either avoid using the
;   augmented-term algorithm (see rewrite-augmented-term) if :untranslate is
;   :nice-expanded, or else perhaps eliminate :nice-expanded as a value for
;   :untranslate.
; - Preserve the well-founded relation.  Here is a test that one could add:
;     (include-book "std/basic/two-nats-measure" :dir :system)
;     (defun f (x y z)
;       (declare (xargs :measure (list x y)
;                       :well-founded-relation nat-list-<))
;       (if (zp x)
;           (if (zp y)
;               z
;             (f x (1- y) (1+ z)))
;         (f (1- x) (+ 2 3 y) (1+ z))))
;     ; Currently fails:
;     (simplify f)
; - Improve the check for no simplification in the defun-nx case.
;   Here is a test that one could add.  The problem in this case, which is
;   probably typical, is that the definition "changed" because
;   one body is
;   (PROG2$ (THROW-NONEXEC-ERROR 'F (LIST X)) X)
;   while the other is:
;   (PROG2$ (THROW-NONEXEC-ERROR 'F$1 (LIST X)) X)
;   The test:
;     (include-book "simplify-defun")
;     (defun-nx f (x)
;      x)
;     (must-fail (simplify-defun f))
; - Deal more completely with the case that :equiv specifies an equivalence
;   relation other than EQUAL but copy-def is called on a recursively-defined
;   function, rather than just causing an error that explains this isn't fully
;   supported.  See apt::simplify-failure (both the section on "Recursion and
;   equivalence relations" and the related comment in the defxdoc form) for
;   more information.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Introductory remarks
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; This section is probably woefully incomplete, but ideally will get fleshed
; out over time.

; Consider the following questions.

; - How much work should we do when simplifying each subterm?
; - How much work should we do when simplifying :assumptions?
; - How much work should we do when simplifying governors of each subterm?

; The following two goals are critical.

; (A) Don't miss important simplifications; try to do a reasonably complete
;     simplification job.

; (B) Proofs will ideally be reliable and efficient.

; Here are some relevant observations.

; (1) The before-vs-after lemma conjoins the :assumptions and governors to form
;     the top-level hypotheses.

; (2) The proof-builder then attempts to use S to simplify those top-level
;     hyps, after diving into them.  (See before-vs-after-lemmas below.)  The
;     :assumptions could therefore be used to simplify the governors, but not
;     vice-versa.  No forward-chaining or linear will be done.
;
; (3) If the resulting top-level hyps don't allow the S command to reduce the
;     "before" to the "after", then the prover is called on to do this (using
;     ORELSE).  The prover will treat the :assumptions and governors
;     symmetrically.
;
; (4) To get the greatest subterm simplification (goal A above), it makes sense
;     to try to get the greatest simplification for top-level hypothesis, since
;     presumably normal forms are best (e.g., for rewrite rules with
;     free-variable hyps and for forward-chaining).
;
; From (2) we might want to simplify the hyps and governors separately, without
; any forward-chaining or linear.  But that is in tension with (4).  Now (3)
; suggests that we would ultimately do best to mimic the prover in support of
; reliable proofs (goal B above); fortunately, this aligns with (4).  Efficient
; proofs might give (2) more weight compared to (4), but reliability is
; probably more important than efficiency, and normally we will probably get
; efficiency anyhow.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Included books
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Inclusion of this book can affect the current-theory, because of the
; sub-books included just below, which also introduce congruence runes that can
; have an effect on the simplify-defun process (search for "congruence" in
; simplify-defun-tests.lisp to see an example involving list-equiv).  So far
; I've done nothing about this, because it could be tricky to fix without
; causing other problems.  For example, we could insert (deflabel
; start-of-simplify-defun) here and insert (in-theory (current-theory
; start-of-simplify-defun)) at the end of this book.  But then if someone tries
; to get rules from an included book after including simplify-defun, e.g., from
; community book books/std/lists/list-defuns.lisp (included via a sequence of
; included books under transformations/utilities.lisp), that included book
; ("list-defuns") would be redundant and hence its rules would remain disabled.

(include-book "kestrel/utilities/system/numbered-names" :dir :system)
(include-book "kestrel/utilities/runes" :dir :system) ; for drop-fake-runes
(include-book "kestrel/utilities/system/terms" :dir :system)
(include-book "kestrel/utilities/user-interface" :dir :system) ; for control-screen-output
(include-book "kestrel/utilities/defmacroq" :dir :system)
(include-book "kestrel/std/system/install-not-normalized-dollar" :dir :system)
(include-book "kestrel/utilities/system/world-queries" :dir :system)
(include-book "kestrel/utilities/directed-untranslate" :dir :system)
(include-book "kestrel/utilities/copy-def" :dir :system) ; includes tools/flag
(include-book "utilities/process-keyword-args")
(include-book "utilities/pattern-matching-ext")
(include-book "kestrel/utilities/error-checking/top" :dir :system)
(include-book "kestrel/utilities/trans-eval-error-triple" :dir :system)
(include-book "kestrel/utilities/er-soft-plus" :dir :system)
(include-book "kestrel/utilities/orelse" :dir :system)
(include-book "kestrel/utilities/system/paired-names" :dir :system)
(include-book "kestrel/std/system/fresh-logical-name-with-dollars-suffix" :dir :system)
(include-book "kestrel/utilities/proof-builder-macros" :dir :system)
(include-book "kestrel/utilities/sublis-expr-plus" :dir :system)
(include-book "utilities/untranslate-specifiers")
(include-book "utilities/hints-specifiers")
(include-book "tools/rewrite-dollar" :dir :system)

(program)
(set-state-ok t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Functions record (fnsr) structures
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrec fnsr ; pronounced "funzer": functions record

; We are given a function symbol, :orig, and we wish to define a new function,
; :simp.  The :copy and :ncopy fields are either :orig and :simp or vice-versa.
; Our approach requires that if either :orig or :simp is defined recursively,
; then :copy is defined recursively.

  ((orig . simp)
   .
   (copy . ncopy))
  nil ; cheap could be t instead of nil
  )

(defmacro defunsr (name args &rest rest)
  (declare (xargs :guard (eq (car args) 'fnsr))) ; sanity check
  `(defun ,name ,args
     ,@(butlast rest 1)
     (let ((fn (access fnsr fnsr :orig))
           (fn-simp (access fnsr fnsr :simp))
           (fnc (access fnsr fnsr :copy))
           (fnnc (access fnsr fnsr :ncopy)))
       (declare (ignorable fn fn-simp fnc fnnc))
       ,(car (last rest)))))

(defun make-fnsr (fn fn-simp fn-simp-singly-recursivep assumptions wrld)

; "Fnsr" stands for "functions record", a record that includes these symbols.

; fn      -- the given function symbol
; fn-simp -- the new function symbol
; fnc     -- either fn or fn-simp, to be copied (see below for explanation)
; fnnc    -- whichever of fn or fn-simp is not fnc

; Essay on the Implementation of Simplify-defun

; The implementation of simplify-defun has essentially these two key steps.

; (1) Call copy-def to produce a copy of fnc, named fnc-copy, together with a
;     theorem fnc-IS-fnc-copy that equates the two.

; (2) Prove fn-BECOMES-fn-simp by functionally instantiating fnc-IS-fnc-copy,
;     mapping fnc-copy to fnnc to produce the equality of fnc with fnnc, i.e.,
;     of fn with fn-simp.

; Let's see why the proof of (2) should go through.  For simplicity we ignore
; the case that the :equiv is not equal, and we defer consideration of
; assumptions.

; The proof obligation is that fnnc satisfies the definition of fnc-copy, or
; equivalently, the following:

;   (KEY)  Fnnc satisfies the definition of fnc.

; Suppose we are given the following definition.

;   (fn x)      = body

; We have presumably simplified body to a new term, body', so that the
; following equality is provable.

;   (EQ)  body = body'

; Then we introduce the following definition, where for a term u and function
; symbols g and h, we write u[g:=h] for the result of applying to u the
; functional substitution that maps g to h.

;   (fn-simp x) = body'[fn:=fn-simp]

; There are two cases, which we will call the "fn-is-fnc" and "fn-is-fnnc"
; cases: in the first, fnc is fn and fnnc is fn-simp; while in the second it is
; the other way around, namely, fnc is fn-simp and fnnc is fn.  We consider
; those two cases below.

; First consider the fn-is-fnc case, where fnc is fn and fnnc is fn-simp.  In
; that case, (KEY) says that fn-simp satisfies the definition of fn, which is
; formalized as follows.

;   (fn-simp x) = body[fn:=fn-simp]

; Equivalently, by expanding fn-simp, this equality reduces to the following.

;   (BVAL)  body'[fn:=fn-simp] = body[fn:=fn-simp]

; This equality is exactly what we call the "before-vs-after lemma" (BVAL) --
; except in the case that :simplify-body specifies subterms, in which case this
; is provable from the set of before-vs-after lemmas.  Note that fn is
; non-recursive if and only if body[fn:=fn-simp] is body, and fn-simp is
; non-recursive if and ony if body'[fn:=fn-simp] is body'.  Thus, if fn and
; fn-simp are both non-recursive, then (BVAL) is provably because it reduces to
; (EQ).  Otherwise, however, there is no guarantee that (BVAL) is provable.
; That said, we can expect it to be reasonably common that (BVAL) doesn't
; depend logically on the definition of fn, i.e., doesn't depend on any
; properties specific to fn -- and in that case, (BVAL) is indeed provable.

; (Aside.  Perhaps some day we will check that (EQ) doesn't depend on the
; definition of fn, by checking that the runes used in simplifying body to
; body' involve only events that aren't hereditarily supported by the
; definition of fn.  That check will be imperfect, however, because it relies
; on perfect tracking of runes, which we know is not the case because of
; congruence rules.  End of aside.)

; We have seen that the fn-is-fnc case supports the proof of (BVAL) if fn and
; fn-simp are both non-recursive, and quite possibly even if they are both
; recursive since then (EQ) may hold for any function symbol in place of fn,
; which gives us (BVAL).  However, if exactly one of fn and fn-simp is
; recursive -- that is, if we are transforming a recursive function to a
; non-recursive function or vice versa -- then the provability of (BVAL) is
; suspect.  In those cases, we can simplify one side of (BVAL) but not the
; other side, as indicated just below.

;   ((BVAL) for fn recursive, fn-simp not)
;   body'              = body[fn:=fn-simp]

;   ((BVAL) for fn-simp recursive, fn not)
;   body'[fn:=fn-simp] = body

; Of course, these equalities follow from (EQ) if fn and fn-simp are provably
; equal -- but that's what we're in the process of trying to prove!  Perhaps a
; more clever implementation could deal with that problem, but we don't see
; how, so we move on to the other case.

; Consider the fn-is-fnnc case.  In that case, (KEY) says that fn satisfies
; the definition of fn-simp, as follows.

;   (fn x) = body'

; But ACL2 can easily prove this theorem because it has simplified body to
; body'; indeed, it is an immediate consequence of the following
; before-vs-after lemma in the fn-is-fnnc case (again, tweaking that argument
; slightly if :simplify-body provides subterms to simplify).

;   (BVAL)  body = body'

; So shall we adopt the fn-is-fnnc case?  Doing so would guarantee the
; provability of (BVAL).

; There is a downside to the fn-is-fnnc case if simplification is done with
; respect to assumptions.  Note that copy-def relies on a lemma saying that
; assumptions are preserved for all recursive calls.  In the fn-is-fnc case,
; where we apply copy-def to fn, that lemma is based on the induction scheme
; stored for fn, a function that is presumably familiar to the user.  But in
; the fn-is-fnnc case, that lemma is based on the induction scheme stored for
; fn-simp, which isn't even defined until after running simplify-defun.

; That is, we want the reliability of the fn-is-fnnc case for (BVAL), but we
; also prefer using the induction scheme of fn to generate the assumption
; preservation lemma in the recursive case.  So we choose cases as follows.

; - If there are assumptions and both fn and fn-simp are recursive, then use
;   fn-is-fnc, so that the assumption preservation theorem is based on the
;   induction scheme for fn.

; - Otherwise use the case fn-is-fnnc, for the following reasons.

;   - The proof of (BVAL) will always succeed, where it would likely fail in
;     the case fn-is-fnc when exactly one of fn and fn-simp is recursive.

;   - If both fn and fn-simp are non-recursive, then either case would be fine;
;     but by using fn-is-fnnc, we have the simple story that fn-is-fnnc is
;     always used except when both fn and fn-simp are recursive and there are
;     assumptions.

; The decisions above seem to leave open the possibility that (BVAL) will fail
; to prove when fn and fn-simp are both recursive and there are assumptions.
; Thus, we may later add an option that can override the choice of cases,
; especially so that we can use the reliable case fn-is-fnnc when both
; functions are recursive and there are assumptions, at the cost of generating
; an assumption preservation theorem that depends on the induction scheme for
; fn-simp instead of the one for fn.

; Note that in the case that we are simplifying a mutual-recursion, we use the
; reliable case fn-is-fnnc.  We thus avoid potentially complicating the
; implementation, which handles mutual-recursion by simplifying the bodies
; sequentially, creating fnsr records at simplification time.  Also, note that
; it could complicate copy-def if fn is fnc for some functions fn in the
; mutual-recursion nest but not others; still, we could consider allowing fn to
; be fnc if every fn-simp is recursive, but note that this information is not
; available for later functions during simplification done on earlier ones.

  (declare (xargs :guard (and (symbolp fn)
                              (plist-worldp wrld))))
  (let ((fn-is-fnc ; see Essay above
         (and fn-simp-singly-recursivep
              assumptions
              (getpropc fn 'recursivep nil wrld))))
    (make fnsr
          :orig fn
          :simp fn-simp
          :copy (if fn-is-fnc fn fn-simp)
          :ncopy (if fn-is-fnc fn-simp fn))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Generating names and lists containing names
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun fn-hyps-name (fn wrld)
  (b* (((mv name &)
        (fresh-logical-name-with-$s-suffix
         (intern$ (concatenate 'string (symbol-name fn) "-HYPS")
                  (symbol-package-name-non-cl fn))
         'function nil wrld)))
    name))

(defun hyps-preserved-thm-name (fn hyps-fn wrld)
  (declare (xargs :guard (and (symbolp fn)
                              (symbolp hyps-fn)
                              fn
                              hyps-fn
                              (plist-worldp wrld))))
  (b* (((mv name &)
        (fresh-logical-name-with-$s-suffix
         (intern$ (concatenate 'string
                               (symbol-name hyps-fn)
                               "-PRESERVED-FOR-"
                               (symbol-name fn))
                  (symbol-package-name-non-cl hyps-fn))
         nil nil wrld)))
    name))

(defun hyps-preserved-thm-name-lst (fn-hyps-alist wrld)
  (cond ((endp fn-hyps-alist) nil)
        (t (cons (hyps-preserved-thm-name (caar fn-hyps-alist)
                                          (cdar fn-hyps-alist)
                                          wrld)
                 (hyps-preserved-thm-name-lst (cdr fn-hyps-alist) wrld)))))

(defun fn-simp-name (fn new-name ctx state)
  (cond ((member-eq new-name '(nil :auto))
         (value (next-numbered-name fn (w state))))
        (t (er-progn (ensure-symbol-new-event-name
                      new-name
                      (msg "The name ~x0, which is the name proposed for the ~
                            simplified definition of ~x1,"
                           new-name fn)
                      :bad-input nil ctx state)
                     (value new-name)))))

(defun fn-runes-name (fn wrld)
  (b* (((mv name &)
        (fresh-logical-name-with-$s-suffix
         (intern$ (concatenate 'string "*" (symbol-name fn) "-RUNES*")
                  (symbol-package-name-non-cl fn))
         'acl2::const nil wrld)))
    name))

(defunsr before-vs-after-name (fnsr index wrld)
  (b* (((mv name &)
        (fresh-logical-name-with-$s-suffix
         (add-suffix fnnc
                     (concatenate
                      'string
                      "-BEFORE-VS-AFTER-"
                      (coerce (explode-nonnegative-integer index 10 nil)
                              'string)))
         nil nil wrld)))
    name))

(defun fn-simp-is-fn-name (fn fn-simp thm-name wrld)
  (cond ((member-eq thm-name '(nil :auto))
         (make-paired-name fn fn-simp 2 wrld))
        (t thm-name)))

(defun fn-simp-is-fn-lemma-name (fn fn-simp theorem-name wrld)
  (b* (((mv name &)
        (fresh-logical-name-with-$s-suffix
         (add-suffix (fn-simp-is-fn-name fn fn-simp theorem-name wrld)
                     "-LEMMA")
         nil nil wrld)))
    name))

(defun fn-hyps-alist (fnsr-lst wrld)
  (cond ((endp fnsr-lst) nil)
        (t (let* ((fnsr (car fnsr-lst))
                  (fn (access fnsr fnsr :orig))
                  (fnc (access fnsr fnsr :copy)))
             (acons fnc
                    (fn-hyps-name fn wrld)
                    (fn-hyps-alist (cdr fnsr-lst) wrld))))))

(defun fn-simp-is-fn-lemmas-used-names (fnsr-lst not-norm-event-names)
  (cond
   ((endp fnsr-lst) nil)
   (t (cons (let* ((fnsr (car fnsr-lst))
                   (fn (access fnsr fnsr :orig))
                   (fnnc (access fnsr fnsr :ncopy)))
              (if (eq fn fnnc)
                  (car not-norm-event-names)
                fnnc))
            (fn-simp-is-fn-lemmas-used-names (cdr fnsr-lst)
                                             (cdr not-norm-event-names))))))

(defun access-fnsr-copy-lst (fnsr-lst)
  (cond ((endp fnsr-lst) nil)
        (t (cons (access fnsr (car fnsr-lst) :copy)
                 (access-fnsr-copy-lst (cdr fnsr-lst))))))

(defun fn-simp-alist (clique new-name** ctx state)
  (cond ((endp clique) (value nil))
        (t (b* ((old-name (car clique))
                ((er new-name)
                 (fn-simp-name old-name (car new-name**) ctx state))
                ((er rest)
                 (fn-simp-alist (cdr clique) (cdr new-name**) ctx state)))
             (value (acons old-name new-name rest))))))

(defun fn-simp-is-fn-lemmas-fn-subst (fnsr-lst)
  (cond
   ((endp fnsr-lst) nil)
   (t (cons (let* ((fnsr (car fnsr-lst))
                   (fnc (access fnsr fnsr :copy))
                   (fnnc (access fnsr fnsr :ncopy)))
              `(,(fn-copy-name fnc) ,fnnc))
            (fn-simp-is-fn-lemmas-fn-subst (cdr fnsr-lst))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Argument processing
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; See process-keyword-args.lisp for bind-**.

(defun fix-assumptions**-1 (hyp-fn** assumptions**)
  (cond ((endp assumptions**) nil)
        ((and (eq (car hyp-fn**) nil)
              (eq (car assumptions**) nil))
         (cons '(t) (fix-assumptions**-1 (cdr hyp-fn**) (cdr assumptions**))))
        (t (cons (car assumptions**)
                 (fix-assumptions**-1 (cdr hyp-fn**) (cdr assumptions**))))))

(defun fix-assumptions** (hyp-fn** assumptions**)

; If at least one member of hyp-fn** or assumptions** is not nil, then for each
; position for which hyp-fn** and assumptions** is nil, replace nil by the list
; containing the trivial assumption t in assumptions**.

  (cond ((and (all-nils hyp-fn**)
              (all-nils assumptions**))
         assumptions**)
        (t (fix-assumptions**-1 hyp-fn** assumptions**))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Miscellaneous utilities
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun theory+expand-to-hints (theory expand)
  (let* ((expand-hint
          (and expand ; else there's nothing to expand
               `(:expand (,@expand)))))
    (and (or (not (eq theory :none))
             expand-hint)
         `(("Goal"
            ,@(and (not (eq theory :none))
                   `(:in-theory ,theory))
            ,@expand-hint)))))

(defun equiv-from-geneqv-1 (geneqv args)
  (cond ((endp geneqv) nil)
        (t (cons (fcons-term (access congruence-rule (car geneqv)
                                     :equiv)
                             args)
                 (equiv-from-geneqv-1 (cdr geneqv) args)))))

(defun equiv-from-geneqv (geneqv)

; We are given a generated equivalence relation.  (See the Essay on
; Equivalence, Refinements, and Congruence-based Rewriting in the ACL2 source
; code.)  We return a semantically equal equivalence relation, which might be a
; symbol but might be a lambda.

  (cond ((endp geneqv) 'equal)
        ((endp (cdr geneqv))
         (access congruence-rule (car geneqv) :equiv))
        (t (let ((args '(x y)))
             (make-lambda
              args
              (disjoin (equiv-from-geneqv-1 geneqv args)))))))

(defun fix-expand-hint (arg)

; This function follows source function translate-expand-hint.  Thus,
; arg is whatever the user typed after the :expand keyword.  We return
; a proper expand hint, i.e., a list of terms (or things that are like
; terms) rather than a single term (or single term-like object).

  (cond ((eq arg :lambdas) (list arg))
        ((null arg) nil)
        ((atom arg) (list arg)) ; illegal, will be caught later
        ((and (consp arg)
              (symbolp (car arg))
              (not (eq (car arg) :lambdas)))
         (list arg))
        ((and (consp arg)
              (consp (car arg))
              (eq (caar arg) 'lambda))
         (list arg))
        (t arg)))

(defun strip-nths (n lst-lst)
  (cond ((endp lst-lst) nil)
        (t (cons (nth n (car lst-lst))
                 (strip-nths n (cdr lst-lst))))))

(defun remove-nils (lst)
  (cond ((endp lst) nil)
        ((null (car lst))
         (remove-nils (cdr lst)))
        (t
         (cons (car lst)
               (remove-nils (cdr lst))))))

(defun mut-rec-induction-machines-1 (names bodies ruler-extenders-lst)

; See mut-rec-induction-machines.

  (cond ((endp bodies)
         nil)
        (t (cons (induction-machine-for-fn names
                                                 (car bodies)
                                                 (car ruler-extenders-lst))
                 (mut-rec-induction-machines-1 names
                                               (cdr bodies)
                                               (cdr ruler-extenders-lst))))))

(defun mut-rec-induction-machines (names wrld)

; We return the list of induction machines corresponding to the given list of
; function symbols of the world, wrld.  In the case that names has length 1,
; we thus return the same thing as function induction-machines, when called
; with the body and ruler-extenders of the given name.

  (mut-rec-induction-machines-1
   names
   (get-unnormalized-bodies names wrld)
   (ruler-extenders-lst names wrld)))

(defun get-def (fn wrld ev)

; We return the definition of fn in wrld, if any, without the leading defun.
; If there is no such definition, we return nil.

; Ev is optional.  If supplied, it is the value of (get-event fn wrld), which
; ideally is non-nil (else the call of get-event below will duplicate the work
; to find nil).

; This code is based on the definition of guard-raw in the ACL2 sources.

  (let ((ev (or ev (get-event fn wrld))))
    (case (car ev)
      (defun (cdr ev))
      (mutual-recursion (assoc-eq fn (strip-cdrs (cdr ev))))
      (verify-termination-boot-strap
       (cdr (cltl-def-from-name fn wrld)))
      (otherwise nil))))

(defun fn-ubody (fn fn-body wrld ev)

; Return a body of fn, preferably an untranslated body, else an unnormalized
; body.  Fn-body may be nil; otherwise it is an unnormalized body of fn in
; wrld, (body fn nil wrld).  Ev may be nil; otherwise it the value of (get-def
; fn wrld nil).

  (or (car (last (get-def fn wrld ev)))
      fn-body
      (body fn nil wrld)))

(defun congruence-runes (lst acc)
  (cond ((endp lst) acc)
        (t (congruence-runes (cdr lst)
                             (if (member-eq (caar lst)
                                            '(:congruence :equivalence))
                                 (cons (car lst) acc)
                               acc)))))

(defun clique-runic-designators (clique)
  (cond ((endp clique) nil)
        (t (append (let ((fn (car clique)))
                     `(,fn (:e ,fn) (:t ,fn)))
                   (clique-runic-designators (cdr clique))))))

(defun union-equal? (x y)
  (cond ((null y) x)
        (t (union-equal x y))))

(defun some-element-dumb-occur (lst1 term)

; This is based on ACL2 source function some-element-dumb-occur-lst.

  (cond ((null lst1) nil)
        ((dumb-occur (car lst1) term) t)
        (t (some-element-dumb-occur (cdr lst1) term))))

(defun collect-dcls-simple (lst)

; This function's sole purpose is to support get-normalize below, which may be
; eliminated; see the comment there.

; This definition is based on that of collect-dcls in the ACl2 sources.  Unlike
; that function, this function assumes that lst is the cdr of an admitted form
; (defun ...); so no errors are expected, but doc strings need to be ignored.

  (declare (xargs :mode :program))
  (cond ((endp lst) nil)
        ((stringp (car lst))
         (collect-dcls-simple (cdr lst)))
        (t (assert$ (eq (caar lst) 'declare)
                    (append (cdar lst)
                            (collect-dcls-simple (cdr lst)))))))

(defun get-normalize (name wrld default ev)

; This function assumes that name is the name of a defun, possibly defined with
; mutual-recursion.  The result is the value of :normalize in the xargs from
; that definition, except that default is the result if :normalize is not
; specified.  Default should be an object that cannot be a value for
; :normalize.  Ev may be nil; otherwise it the value of (get-def name wrld
; nil).

; NOTE: This definition, along with collect-dcls-simple just above, can
; probably be eliminated in favor of the following code from Eric Smith, once
; the relevant books are in the community books.  Eric notes that the first
; formal, name, must be the name of a defined function; but that is also
; required of the present definition.

; Eric's suggestion:

;   (include-book "utilities/defun-forms")
;   (include-book "utilities/declares0")
;
;   ;; Returns (mv normalize-presentp xarg-val-if-present)
;   (defun get-normalize (name wrld)
;      (declare (xargs :mode :program))
;      (get-xarg-from-declares :normalize
;                              (get-declares-from-event name
;                                                       (get-event name wrld))))

  (declare (xargs :mode :program))
  (let ((def (get-def name wrld ev))
        (ctx 'get-normalize))
    (cond
     ((null def) (er hard ctx
                     "Definition not found for the name ~x0"
                     name))
     (t (let ((edcls (collect-dcls-simple (butlast (cddr def) 1))))
          (get-unambiguous-xargs-flg1/edcls1
           :normalize default edcls "irrelevant string"))))))

(defun set-difference-rassoc-eq (lst alist)

; This definition is based closely on the ACL2 sources definition of function
; set-difference-assoc-eq.

  (declare (xargs :guard (and (true-listp lst)
                              (alistp alist)
                              (or (symbol-listp lst)
                                  (r-symbol-alistp alist)))
                  :mode :logic))
  (cond ((endp lst) nil)
        ((rassoc-eq (car lst) alist)
         (set-difference-rassoc-eq (cdr lst) alist))
        (t (cons (car lst) (set-difference-rassoc-eq (cdr lst) alist)))))

#!acl2
(defun geneqv-from-g?equiv (g?equiv wrld)

; This function is from the community books, file misc/expander.lisp.

; We write g?equiv to indicate that we have either a geneqv or else a symbol
; that is an equivalence relation (where nil represents equal).

  (if (symbolp g?equiv)
      (cadr (car (last (getprop
                        g?equiv
                        'congruences
                        nil
                        'current-acl2-world
                        wrld))))
    g?equiv))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Handling hypotheses
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun fn-hyps-def (fn fn-hyps hyps thyps-vars wrld)
  (assert$
   (and fn-hyps hyps) ; else don't call this function
   (let* ((fn-formals (formals fn wrld))
          (ignored-vars (set-difference-eq fn-formals thyps-vars)))
     `(defun ,fn-hyps ,fn-formals
        ,@(and ignored-vars `((declare (ignore ,@ignored-vars))))
        ,(conjoin-untranslated-terms hyps)))))

(defun hyps-preserved-thm-body (fn-hyps-call tests-and-calls-lst fn-hyps-alist
                                             wrld acc)

; Warning: call this theorem only if fn-hyps is non-nil.

; This function is the workhorse for hyps-preserved-thm.  It generates the a
; (translated) term conjoining, for each (tests . calls) in tests-and-calls-lst
; (each representing recursive calls of fn under a given set, tests, of
; rulers), the assertion that fn-hyps is preserved by the calls.

  (cond
   ((endp tests-and-calls-lst)
    (untranslate (conjoin acc) ; acc is nil if there are no calls
                 t
                 wrld))
   (t (hyps-preserved-thm-body
       fn-hyps-call (cdr tests-and-calls-lst) fn-hyps-alist wrld
       (let ((tests (access tests-and-calls
                            (car tests-and-calls-lst)
                            :tests))
             (calls (access tests-and-calls
                            (car tests-and-calls-lst)
                            :calls)))
         (if calls
             (cons (make-implication (cons fn-hyps-call tests)
                                     (conjoin (fsublis-fn-lst-simple
                                               fn-hyps-alist
                                               calls)))
                   acc)
           acc))))))

(defun assumptions-to-hyps (assumptions hyp-fn fn guard? ctx wrld state)
  (cond (hyp-fn (cond ((symbolp hyp-fn)
                       (value (list (cons hyp-fn
                                          (formals fn wrld)))))
                      (t (er-soft+ ctx :bad-input nil
                                   "The value of keyword :HYP-FN for ~x0 must ~
                                    be a symbol.  The value ~x1 is thus ~
                                    illegal."
                                   'simplify
                                   hyp-fn))))
        ((eq assumptions :guard)
         (value (list (or guard?
                          (guard-raw fn wrld)))))
        ((not (true-listp assumptions))
         (er-soft+ ctx :bad-input nil
                   "The value of keyword :ASSUMPTIONS for ~x0 must be either ~
                    :GUARD or a true list.  The value ~x1 is thus illegal."
                   'simplify
                   assumptions))
        (t (value (let ((p (position-eq :guard assumptions)))
                    (cond (p (update-nth p
                                         (or guard? (guard-raw fn wrld))
                                         assumptions))
                          (t assumptions)))))))

(defun hyps-preserved-thm (fn fn-hyps assumptions hints
                              fn-hyps-alist expand-lst
                              induction-machine flet-bindings verbose wrld ctx)

; Fn and fn-hyps are function symbols with the same formals.  Return the
; theorem saying that fn-hyps (a function symbol) is preserved in recursive
; calls of fn.

  (assert$
   fn-hyps ; else don't even call this function
   (cond
    ((null induction-machine)
     nil)
    (t
     (let* ((formals (formals fn wrld))
            (hyps-preserved-thm-name (hyps-preserved-thm-name fn fn-hyps wrld))
            (body (hyps-preserved-thm-body
                   (fcons-term fn-hyps formals)
                   induction-machine
                   fn-hyps-alist
                   wrld
                   nil))
            (lemma-name (add-suffix hyps-preserved-thm-name "-LEMMA"))
            (flet-form `(flet ,flet-bindings ,body))
            (defthm-form
              `(defthm ,lemma-name
                 ,flet-form
                 ,@(and (or hints
                            (eq assumptions :guard))
                        `(:hints
                          ,(append?
                            hints
                            (and (eq assumptions :guard)
                                 (eq (symbol-class fn wrld)
                                     :common-lisp-compliant)
                                 `((quote (:use (:guard-theorem ,fn))))))))
                 :rule-classes nil))
            (on-failure-msg
             (msg "The following :ASSUMPTIONS-PRESERVED applicability ~
                  condition has failed:~|~%~X01"
                  flet-form (evisc-tuple 12 12 nil nil))))
       `(encapsulate
          ()
          ,@(and verbose
                 `((make-event
                    (pprogn (fms "Proving :ASSUMPTIONS-PRESERVED ~
                                  applicability condition for ~x0:~|~x1~|"
                                 (list (cons #\0 ',fn)
                                       (cons #\1 ',flet-form))
                                 (standard-co state) state nil)
                            (value '(value-triple :invisible))))))
          (local
           (on-failure
            ,(if verbose
                 defthm-form
               `(with-output :off :all ,defthm-form))
            :ctx ,ctx
            :erp :condition-failed
            :val nil
            :msg ,on-failure-msg))
          (defthm ,hyps-preserved-thm-name
            ,body
            :hints
            (("Goal"
              :in-theory (theory 'minimal-theory)
              :use ,lemma-name
              ,@(and expand-lst `(:expand ,expand-lst))))
            :rule-classes nil)))))))

(defun translate-hyp-list (hyps fn ctx wrld state)

; Fn is used only to check that the vars of hyps are all among the formals of
; fn.  Fn may be nil, in which case that check is skipped.

  (mv-let (erp thyps state)
    (convert-soft-error
     :bad-input nil
     (translate-term-lst hyps
                         t ; stobjs-out
                         t ; logic-modep
                         t ; known-stobjs-lst
                         ctx wrld state))
    (cond (erp (pprogn
                (io? error nil state
                     (hyps)
                     (fms "ERROR: As noted above, translation of the ~
                           :ASSUMPTIONS, ~x0, has failed!~|"
                          (list (cons #\0 hyps))
                          (standard-co state) state nil))
                (mv erp thyps state)))
          ((null fn)
           (value thyps))
          (t (let ((formals (formals fn wrld))
                   (vars (all-vars1-lst thyps nil)))
               (cond ((subsetp-eq vars formals)
                      (value thyps))
                     (t (er-soft+ ctx :bad-input nil
                          "The variable~#0~[ ~&0 occurs~/s ~&0 occur~] free ~
                           in the :ASSUMPTIONS, ~x1, but ~#0~[is~/are~] not ~
                           among the formal parameters of the given function ~
                           symbol, ~x2."
                          (set-difference-eq vars formals)
                          hyps
                          fn))))))))

(defun simplify-hyp-list (hyps governors thints ctx state)

; Given a context formed from the given translated hypotheses and governors,
; and theory and expand derived from the top-level simplify[-defun[-sk]] call,
; we return (list* rewritten-context rrec runes) when there is no error.

  (b* ((context (append hyps governors))
       ((mv erp
            (list* ?rewritten-context rrec ttree pairs)
            state)
        (acl2::rewrite$-hyps context
                             :thints thints
                             :ctx ctx

; List explicitly some defaults as of this writing:

                             :update-rrec t
                             :repeat 1
                             :prove-forced-assumptions 't)))
    (cond
     ((null erp)
      (assert$ (null pairs) ; since :prove-forced-assumptions is t
               (value (cons rrec
                            (acl2::all-runes-in-ttree ttree nil)))))
     (t

; It should be rare or impossible to fail here, so let's call it an
; implementation error until learning that we should handle this case
; differently.

      (er-soft+ ctx :bad-input nil
                "The error noted above was caused by an attempt to build a ~
                 context from the given ~@0"
                (cond
                 (hyps
                  (cond
                   (governors (msg "list of assumptions,~|  ~y0,~|and list of ~
                                    governing IF tests,~|  ~y1."
                                   hyps governors))
                   (t (msg "list of assumptions,~|  ~y0."
                           hyps))))
                 (t (msg "list of governing IF tests,~|  ~y0."
                         governors))))))))

(defconst *must-simplify-keywords*
; Keep this in sync with the default value in (show-)simplify-defun.
  '(:body :measure :guard))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Deal with whether simplification must take place
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun check-must-simplify (x ctx state)
  (cond ((booleanp x) (value x))
        ((eq x :default) (value '(:body t :measure nil :guard nil)))
        ((and (keyword-value-listp x)
              (null (strip-keyword-list *must-simplify-keywords* x)))
         (value x))
        (t
         (er-soft+ ctx :bad-input nil
                 "The :MUST-SIMPLIFY argument must be T, NIL, :DEFAULT, or a ~
                  keyword-value-listp for which each key is ~v0."
                  *must-simplify-keywords*))))

(defun get-must-simplify (kwd x)
  (declare (xargs :guard (and (or (booleanp x)
                                  (keyword-value-listp x))
                              (member-eq kwd *must-simplify-keywords*))))
  (cond ((symbolp x) x) ; x is t or nil
        (t (cadr (assoc-keyword kwd x)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Rewriting
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun rewrite1 (tterm alist geneqv rrec ctx wrld state)

; We rewrite term under alist with the given geneqv and rewrite$-record,
; returning an error triple with non-erroneous value (cons rewritten-term
; runes).

  (b* (((er (list* rewritten-term runes pairs))
        (acl2::rewrite$
         tterm
         :alist alist
         :geneqv geneqv
         :repeat 3 ; somewhat arbitrary
         :default-hints-p nil
         :ctx ctx
         :wrld wrld
         :rrec rrec

; List explicitly some defaults as of this writing:

         :prove-forced-assumptions t
         :translate nil))
       ((when pairs)
        (er-soft+ ctx :implementation-error nil
                  "Implementation error: We are surprised to see unproved ~
                   assumptions returned by ~x0."
                  'acl2::rewrite$)))
    (value (cons rewritten-term runes))))

(defun rewrite1-lst (tterm-lst alist rrec ctx wrld state)

; See rewrite1.  This function returns (mv erp val state), where if erp is nil,
; then val is (cons rewritten-tterm-lst runes), where runes collects all runes
; used in the rewrites.

  (cond ((endp tterm-lst) (value (cons nil nil)))
        (t (b* (((er (cons new-tterm runes1))
                 (rewrite1 (car tterm-lst) alist nil rrec ctx wrld state))
                ((er (cons new-tterm-lst runes2))
                 (rewrite1-lst (cdr tterm-lst) alist rrec ctx wrld state)))
             (value (cons (cons new-tterm new-tterm-lst)
                          (union-equal? runes1 runes2)))))))

(defun term-to-lits (term wrld)

; This function may be a bit heavy-handed, but it makes convenient use of
; existing utilities to do something reasonably powerful.  We have seen an
; example where if we didn't apply this function to the conjunction of
; governors, we don't get what we want.  The example had this

;   :simplify-body
;   (if (or (not expr1)
;           expr2)
;       outputs
;     @)

; and gave us a single hypothesis of the form (not (if ...)), while the present
; code instead gave the expected list of 9 terms (note that expr1 called a
; function that is is defined to be a rather large conjunction), implicitly
; conjoined.

  (flatten-ands-in-lit
   (termify-clause-set
    (clausify term nil t (sr-limit wrld)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Return-last blockers
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; We attempt to preserve return-last calls, as in (prog2$ (cw ...) ...).  To do
; this, we replace return-last calls by corresponding functions.  Consider for
; example (prog2$ t1 t2).  It macroexpands to (return-last 'progn t1 t2), which
; we "block" by converting it to (prog2$-fn t1 t2).  Now (prog2$-fn x y) is
; defined to be (prog2$ x y), i.e., (return-last 'progn x y).  It is disabled
; by default.  Simplify does such "blocking" before simplification, which
; preserves the prog2$-fn call unless prog2$-fn is enabled or the call is
; expanded with a hint.  After simplification, "unblocking" restores the
; original call.

; The term "blocking" refers to the fact that some simplification is blocked by
; this procedure; for example (car (prog2$ (cw "hello") (cons x y)) will not
; simplify to x unless prog2$-fn is enabled.

; I considered similar treatment for all of
; *initial-logic-fns-with-raw-code*.  However, that list includes many
; functions that, conceivably, one may want to rewrite, including zp, floor,
; max, logand, take, and so on.  So we preserve only return-last, which covers
; the common case of preserving (prog2$ (cw ...) ...) provided the rules for
; fmt-to-comment-window are disabled.

#!acl2
(defconst *initial-return-last-table*

; This is exactly the code from the corresponding ACL2 definition.  We include
; it here so that if redundancy fails, we'll know to consider modifying the
; defconst form below.

  '((time$1-raw . time$1)
    (with-prover-time-limit1-raw . with-prover-time-limit1)
    (with-fast-alist-raw . with-fast-alist)
    (with-stolen-alist-raw . with-stolen-alist)
    (fast-alist-free-on-exit-raw . fast-alist-free-on-exit)
    (progn . prog2$)
    (mbe1-raw . mbe1)
    (ec-call1-raw . ec-call1)
    (with-guard-checking1-raw . with-guard-checking1)))

(defconst *return-last-blocker-alist*
  #!acl2'((time$1-raw . time$-fn)
          (with-prover-time-limit1-raw . with-prover-time-limit-fn)
          (with-fast-alist-raw . with-fast-alist-fn)
          (with-stolen-alist-raw . with-stolen-alist-fn)
          (fast-alist-free-on-exit-raw . fast-alist-free-on-exit-fn)
          (progn . prog2$-fn)
          (mbe1-raw . mbe-fn)
          (ec-call1-raw . ec-call-fn)
          (with-guard-checking1-raw . with-guard-checking-fn)))

(defun return-last-blockers-defs (alist)

; Alist is a tail of *return-last-blocker-alist*.

  (cond ((endp alist) nil)
        (t (let ((fn (cdr (car alist))))
             (list* `(defun ,fn (x y)
                       (declare
                        (xargs :guard t      ; probably unimportant
                               :mode :logic) ; superfluous (see (logic) below)
                        (ignore x))
                       y)

; For backward compatibility and overall simplicity, we avoid adding the
; following here:
;`(in-theory (disable ,fn (:e ,fn) (:t ,fn)))
; See for example the tests in simplify-defun-tests.lisp and
; simplify-defun-tests-sk.lisp containing comments about "blowing away", either
; prog2$ or ec-call.

                    (return-last-blockers-defs (cdr alist)))))))

(make-event (list* 'encapsulate nil '(logic)

; While we're at it, we arrange for cw calls to remain, by default.

                   '(in-theory (disable fmt-to-comment-window
                                        (:e fmt-to-comment-window)
                                        (:t fmt-to-comment-window)))
                   (return-last-blockers-defs *return-last-blocker-alist*)))

(mutual-recursion

(defun block-return-last (term)
  (cond ((or (variablep term)
             (fquotep term))
         (mv nil term))
        ((flambdap (ffn-symb term))
         (b* (((mv changedp1 body)
               (block-return-last (lambda-body (ffn-symb term))))
              ((mv changedp2 args)
               (block-return-last-lst (fargs term)))
              ((when (not (or changedp1 changedp2)))
               (mv nil term))
              (fn (if changedp1
                      (make-lambda (lambda-formals (ffn-symb term))
                                   body)
                    (ffn-symb term))))
           (mv t (fcons-term fn args))))
        ((eq (ffn-symb term) 'return-last)
         (b* (((mv changedp1 arg1)
               (block-return-last (fargn term 1)))
              ((mv changedp2 arg2)
               (block-return-last (fargn term 2)))
              ((mv changedp3 arg3)
               (block-return-last (fargn term 3)))
              (key (and (quotep arg1)
                        (unquote arg1)))
              (fn (and key ; optimization
                       (cdr (assoc-eq key *return-last-blocker-alist*)))))
           (cond (fn (mv t (fcons-term* fn arg2 arg3)))
                 ((or changedp1 changedp2 changedp3)
                  (mv t (fcons-term* 'return-last arg1 arg2 arg3)))
                 (t (mv nil term)))))
        (t (b* (((mv changedp args)
                 (block-return-last-lst (fargs term))))
             (if changedp
                (mv t (fcons-term (ffn-symb term) args))
               (mv nil term))))))

(defun block-return-last-lst (lst)
  (cond ((endp lst) (mv nil nil))
        (t (b* (((mv changedp1 x)
                 (block-return-last (car lst)))
                ((mv changedp2 y)
                 (block-return-last-lst (cdr lst))))
             (cond ((or changedp1 changedp2)
                    (mv t (cons x y)))
                   (t (mv nil lst)))))))
)

(mutual-recursion

(defun unblock-return-last (term)
  (cond ((or (variablep term)
             (fquotep term))
         term)
        ((flambdap (ffn-symb term))
         (fcons-term (make-lambda
                      (lambda-formals (ffn-symb term))
                      (unblock-return-last (lambda-body (ffn-symb term))))
                     (unblock-return-last-lst (fargs term))))
        (t (let ((key (car (rassoc-eq (ffn-symb term)
                                      *return-last-blocker-alist*))))
             (cond (key
                    (fcons-term 'return-last
                                (cons (kwote key)
                                      (unblock-return-last-lst (fargs term)))))
                   (t
                    (fcons-term (ffn-symb term)
                                (unblock-return-last-lst (fargs term)))))))))

(defun unblock-return-last-lst (lst)
  (cond ((endp lst) nil)
        (t (cons (unblock-return-last (car lst))
                 (unblock-return-last-lst (cdr lst))))))
)

(defun return-last-blocker-rules (alist)

; Alist is a tail of *return-last-blocker-alist*.

  (cond ((endp alist) nil)
        (t (let ((fn (cdr (car alist))))
             (list* fn
                    `(:e ,fn)
                    `(:t ,fn)
                    (return-last-blocker-rules (cdr alist)))))))

(encapsulate
  ()
  (logic)
(deftheory acl2::return-last-blockers
  (return-last-blocker-rules *return-last-blocker-alist*))
)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Simplifying a term
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun augment-term (term)

; The set of augmented terms u is defined recursively as follows.  (Note that u
; is a term with respect to a world in which :IF and :BLOCKER are ternary
; function symbols, so the usual notion of "free variables of u" makes sense.)

; - If u is a term, then u is an augmented term.  We call u an "ordinary term".

; - If u is (:IF tst tbr fbr), then u is an augmented term iff tst is a term
;   and both tbr and fbr are augmented terms, and at least one of tbr and fbr
;   is either a lambda application or is not an ordinary term.

; - If u is ((lambda (v1 ... vk) body) a1 ... ak), then each ai is an ordinary
;   term, the vi are distrinct variables, all free variables of body are among
;   the vi, and body is an augmented term.

; - If u is (:BLOCKER blocker-fn arg1 arg2), then u is an augmented term iff
;   blocker-fn is a blocker function (a cdr in *return-last-blocker-alist*) and
;   both arg1 and arg2 are augmented terms, and at least one of these two is
;   either a lambda application or is not an ordinary term.

; Note that an augmented term, u, is an ordinary term if and only if neither
; :IF nor :BLOCKER is a function symbol of u.

; This function returns (mv term' augmentedp), where term' is an augmented term
; equivalent to the input term, and augmentedp is true if and only if term' is
; not an ordinary term or has a top-level lambda.  When augmentedp is nil,
; term' = term.

  (declare (xargs :guard (pseudo-termp term)
                  :mode :logic))
  (cond ((or (variablep term)
             (fquotep term))
         (mv term nil))
        (t (let ((fn (ffn-symb term)))
             (cond ((eq fn 'if)
                    (mv-let (tbr augmentedp1)
                      (augment-term (fargn term 2))
                      (mv-let (fbr augmentedp2)
                        (augment-term (fargn term 3))
                        (cond ((or (lambda-applicationp tbr)
                                   (lambda-applicationp fbr)
                                   augmentedp1
                                   augmentedp2)
                               (mv (list :if (fargn term 1) tbr fbr)
                                   t))
                              (t (mv term nil))))))
                   ((flambdap fn)
                    (mv-let (body augmentedp)
                      (augment-term (lambda-body fn))
                      (cond (augmentedp
                             (mv (fcons-term (make-lambda (lambda-formals fn) body)
                                             (fargs term))
                                 t))
                            (t (mv term t)))))
                   ((rassoc-eq fn *return-last-blocker-alist*)
                    (mv-let (arg1 augmentedp1)
                      (augment-term (fargn term 1))
                      (mv-let (arg2 augmentedp2)
                        (augment-term (fargn term 2))
                        (cond ((or augmentedp1 augmentedp2)
                               (mv (list :blocker
; We probably don't need to quote fn, but we do so just in case some function
; crawls over the resulting pseudo-term, so that fn isn't considered to be a
; variable.
                                         (kwote fn)
                                         arg1
                                         arg2)
                                   t))
                              (t (mv term nil))))))
                   (t (mv term nil)))))))

(defun sublis-expr+ (alist term)

; This function was conceived as one for which term is the result of rewriting
; an augmented term.  We substitute formals for actuals in term, even inside
; lambda bodies when possible.

; At one time it didn't seem necessary to substitute inside lambda bodies.
; However, it can be important; for an example, search for "sublis-expr+" in
; simplify-defun-tests.lisp.

  (acl2::sublis-expr+ alist term))

(defun make-proper-lambda (formals actuals body)

; Formals is a true list of distinct variables, actuals is a true list of terms
; of the same length as formals, and body is a term.  We want to create
; something like ((lambda formals body) . actuals), but body may have free
; variables that do not belong to formals, and lambdas must be closed in ACL2.
; We add the necessary extra variables to the end of formals and actuals, as is
; done in ACL2 source function translate11-let.  Unlike translate11-let,
; however, we don't deal with declare forms here (though this code could rather
; easily be extended to do so).

  (cond
   ((equal formals actuals) ; trivial case
    body)
   (t (make-lambda-term formals actuals body))))

(defun remove-duplicate-actuals (formals actuals dup-actuals)

; At the top level, dup-actuals is nil.  Before we call generalize-to-lambda to
; replace actuals by formals in a rewritten body, we eliminate duplicated
; actuals and their corresponding formals.  To see why, consider a term (let
; ((x1 e1) (x2 e2)) body), where e1 and e2 both rewrite to e and body rewrites,
; with respect to bindings of x1 and x2 to e, to body'.  Each occurrence of e
; in body' could correspond to either x1 or x2; we don't know which (well, at
; least not without additional effort that we have not made).  So rather than
; guessing wrong, we want to avoid generalizing e to either x1 or x2.

  (cond ((endp formals) (mv nil nil))
        ((member-equal (car actuals) (cdr actuals))
         (remove-duplicate-actuals (cdr formals)
                                   (cdr actuals)
                                   (cons (car actuals) dup-actuals)))
        ((member-equal (car actuals) dup-actuals)
         (remove-duplicate-actuals (cdr formals) (cdr actuals) dup-actuals))
        (t (mv-let (f a)
             (remove-duplicate-actuals (cdr formals) (cdr actuals) dup-actuals)
             (mv (cons (car formals) f)
                 (cons (car actuals) a))))))

(defun drop-unused-formals (formals actuals body-vars candidates)
  (cond ((endp formals) (mv nil nil))
        (t (mv-let (f a)
             (drop-unused-formals (cdr formals) (cdr actuals) body-vars
                                  candidates)
             (cond ((and (member-eq (car formals) candidates)
                         (not (member-eq (car formals) body-vars)))
                    (mv f a))
                   (t (mv (cons (car formals) f)
                          (cons (car actuals) a))))))))

(defun generalize-to-lambda (formals actuals body)

; Formals is a list of distinct variables, actuals is a list of terms, and the
; two lists have the same length.  We return a term that is provably equal to
; body, but may be a lambda application obtained by abstracting some actuals to
; corresponding formals, possibly differing from the input formals although
; that difference is, ideally, small.

; This code is somewhat based on the definition of ext-rename-for-substitution
; in community book books/kestrel/apt/utilities/pattern-matching-ext.lisp.

  (b* ((body-vars (all-vars body))
       ((mv formals actuals)

; We may restrict formals and (correspondingly) actuals, and we do so here and
; in the binding of formals and actuals just below.

; The first re-binding is useful for dropping the binding of __FUNCTION__ in
; define.  It's a bit of a hack to restrict to that variable alone, but tests
; started failing when dropping all unused formals.

        (drop-unused-formals formals actuals body-vars '(__function__)))
       ((mv formals actuals)

; Suppose body is (bar 0 0 (f w)), which is the simplification of
; (let ((x 0) (y 0) (z (f w))) (foo x y z)).  We can't expect to abstract
; appropriately the first 0 to x and the second 0 to y, especially without
; knowing something about the original let expression.  So in this case we are
; happy to abstract (f w) to z, but not to abstract either occurrence of 0; we
; thus remove x and y from the formals and the two zeros from the actuals.

        (remove-duplicate-actuals formals actuals nil))
       (formals0

; We rename all formals to new formals that are disjoint from the old formals
; and from the set of variables occurring in body.  With some thought we might
; be able to be less aggressive in our renaming, but this seems simple and
; safe, and we're not terribly worried here about efficiency.

        (ext-rename-formals formals (append formals body-vars)))
       (body0 (sublis-expr (pairlis$ actuals formals0) body))
       (formals1

; At this point we could legitimately return ((lambda formals0 body0) actuals).
; But we prefer to use the original formals.  If no original formal occurs in
; body, then we can simply rename formals0 back to formals.  But we need to
; avoid formals that do occur in body.

        (ext-rename-formals formals (all-vars body0)))
       (body1 (sublis-expr+ (pairlis$ actuals formals1) body)))

; Let s be the substitution mapping formals1 to actuals.  We claim that
; body1[s] is provably equal to body.  Sublis-expr+ should give a result
; provably equal to what is given by sublis-expr, so if we let body2 =
; (sublis-expr (pairlis$ actuals formals1) body), then from provability of
; body1 = body2, we get provability of (body1 = body2)[s], i.e., of body1[s] =
; body2[s].  Thus, it suffices to show that body2[s] is provably equal to body.
; In fact, it is easy to see that these are syntactically identical.

    (make-proper-lambda formals1 actuals body1)))

(defun rewrite-augmented-term-rec (aterm alist geneqv rrec runes ctx wrld state)

; The key idea here is that when rewriting (let ((x expr)) body), we rewrite
; expr to expr', then we rewrite body with x bound to expr' to produce body',
; and finally we generalize expr' to x in body' to return (let ((x expr'))
; body').  Of course, we traffic in translated terms that use lambda instead of
; let, we allow bindings of more than one variable, and so on.

  (case-match aterm
    ((':IF tst tbr fbr)
     (b* (((er (cons tst2 runes-tst))
           (rewrite1 tst alist *geneqv-iff* rrec ctx wrld state))
          (runes (union-equal? runes-tst runes))
          (rcnst (access acl2::rewrite$-record rrec :rcnst))
          (ens (access acl2::rewrite-constant rcnst
                       :current-enabled-structure))
          (ok-to-force (acl2::ok-to-force rcnst))
          (type-alist (access acl2::rewrite$-record rrec :type-alist))
          (pot-lst (access acl2::rewrite$-record rrec :pot-lst))
          ((mv must-be-true
               must-be-false
               true-type-alist
               false-type-alist
               ts-ttree)
           (acl2::assume-true-false tst2 nil ok-to-force nil type-alist ens
                                    wrld pot-lst nil nil)))
       (cond (must-be-true
              (rewrite-augmented-term-rec tbr alist geneqv rrec
                                          (all-runes-in-ttree ts-ttree runes)
                                          ctx wrld state))
             (must-be-false
              (rewrite-augmented-term-rec fbr alist geneqv rrec
                                          (all-runes-in-ttree ts-ttree runes)
                                          ctx wrld state))
             (t (b* (((er (cons tbr2 runes))
                      (rewrite-augmented-term-rec tbr alist geneqv
                                                  (change acl2::rewrite$-record
                                                          rrec
                                                          :type-alist
                                                          true-type-alist)
                                                  runes ctx wrld state))
                     ((er (cons fbr2 runes))
                      (rewrite-augmented-term-rec fbr alist geneqv
                                                  (change acl2::rewrite$-record
                                                          rrec
                                                          :type-alist
                                                          false-type-alist)
                                                  runes ctx wrld state))
                     ((mv term ttree)
                      (rewrite-if1 tst2 tbr2 fbr2
                                   nil ; swapped-p
                                   type-alist
                                   geneqv ens ok-to-force wrld nil)))
                  (value (cons term (all-runes-in-ttree ttree runes))))))))
    ((('LAMBDA formals body) . actuals)
     (b* (((er (cons rewritten-actuals runes-actuals))
           (rewrite1-lst actuals alist rrec ctx wrld state))
          (runes (union-equal? runes-actuals runes))
          ((er (cons rewritten-body runes))
           (rewrite-augmented-term-rec body
                                       (pairlis$ formals rewritten-actuals)
                                       geneqv rrec runes ctx wrld state))
          (new-body

; I haven't given a lot of thought to the case that rewritten-body is a lambda
; application.  But my guess is that all is well as is.

           (cond
            ((some-element-dumb-occur rewritten-actuals rewritten-body)
             (generalize-to-lambda formals rewritten-actuals rewritten-body))
            (t rewritten-body))))
       (value (cons new-body runes))))
    ((':BLOCKER ('QUOTE blocker-fn) arg1 arg2)
     (let* ((rcnst (access acl2::rewrite$-record rrec :rcnst))
            (ens (access acl2::rewrite-constant rcnst
                         :current-enabled-structure)))
       (cond
        ((and (quotep arg1)
              (quotep arg2)
              (enabled-xfnp blocker-fn ens wrld))
         (value (cons arg2
                      (add-to-set-equal (list :executable-counterpart
                                              blocker-fn)
                                        runes))))
        ((enabled-numep (fn-rune-nume blocker-fn t nil wrld) ens)
         (rewrite-augmented-term-rec arg2 alist geneqv rrec runes ctx
                                     wrld state))
        (t
         (b* (((er (cons arg1-new runes))
               (rewrite-augmented-term-rec arg1 alist
; It's not clear, for all blockers, what to use for geneqv for this argument.
; So we are conservative here.
                                           nil ; geneqv
                                           rrec runes ctx wrld state))
              ((er (cons arg2-new runes))
               (rewrite-augmented-term-rec arg2 alist geneqv rrec runes ctx
                                           wrld state)))
           (value (cons (fcons-term* blocker-fn arg1-new arg2-new)
                        runes)))))))
    (& ; aterm is a term
     (b* (((er (cons new-term new-runes))
           (rewrite1 aterm alist geneqv rrec ctx wrld state)))
       (value (cons new-term
                    (union-equal? new-runes runes)))))))

(defun rewrite-with-augmentation (term alist geneqv rrec must-rewrite ctx state)

; We augment term (see augment-term) and then call the rewriter in a top-down
; traversal of the augmented term tree, with rewrite-augmented-term-rec.

  (b* ((wrld (w state))
       ((mv aterm &)
        (augment-term term))
       ((er val)
        (rewrite-augmented-term-rec aterm alist geneqv rrec nil ctx wrld
                                    state)))
    (cond ((and must-rewrite
                (equal (car val) ; rewritten-term
                       (fsublis-var alist term)))
           (er soft ctx
               "The term~%  ~x0~%with alist~%  ~x1~%failed to rewrite to a ~
                new term."
               (untranslate term nil wrld)
               (pairlis$ (strip-cars alist)
                         (pairlis$ (untranslate-lst (strip-cdrs alist) nil
                                                    wrld)
                                   nil))))
          (t (value val)))))

(defun simplify-defun-term (term alist g?equiv rrec must-rewrite ctx state)

; Warning: A more natural name for this function might be simplify-term, but
; that name has been used at times in Axe (see community books directory
; books/kestrel/axe/).

; Term is a translated term; alist maps variables to translated terms; g?equiv
; is either a geneqv or else a symbol that represents an equivalence relation
; (where nil represents equal); and rrec is a suitable rewrite$-record, as
; returned by rewrite$-hyps.  This function returns an error triple (mv erp val
; state), where if erp is nil then val is (cons rewritten-term runes).

  (with-output!
    :off prove
    (b* (((mv changedp bterm)
          (block-return-last term))
         ((mv erp (cons new-term runes) state)
          (rewrite-with-augmentation bterm
                                     alist
                                     (geneqv-from-g?equiv g?equiv (w state))
                                     rrec must-rewrite ctx state)))
      (cond
       ((msgp erp) ; failure to prove assumptions (maybe other failures too?)
        (er-soft+ ctx :condition-failed nil "~@0" erp))
       (erp

; If must-rewrite is false, then this is a somewhat surprising error.  See the
; comment above for simplify-hyps.  So let's choose :condition-failed here
; under the assumption that must-rewrite is true.

        (er-soft+ ctx :condition-failed nil
                  "Simplification failed.  Specify :simplify-body nil or ~
                   perhaps use option :must-simplify in order to avoid this ~
                   error."))
       (t (value
           (cons (if changedp
                     (unblock-return-last new-term)
                   new-term)
                 (if changedp ; then add to runes for before-vs.-after lemmas
                     (add-to-set-equal '(:definition return-last) runes)
                   runes))))))))

(defun check-simplified (old-untrans* old-trans new-untrans new-trans msg ctx
                                      state)

; Old-untrans* is named with a "*" suffix to indicate that the old untranslated
; term might have been modified, say by substituting new names for old, before
; being passed to this function.

  (cond
   ((equal new-untrans old-untrans*)
    (cond ((equal new-trans old-trans)

; Probably this case can't happen, because tool2 would cause an error.  But we
; code it up in case that changes.

           (er-soft+ ctx :no-effect nil
             "No simplification has taken place.  Specify :simplify-body nil ~
              or use option :must-simplify if you want that to be allowed."))
          (t
           (er-soft+ ctx :no-effect nil
             "Although simplification has taken place, the old and new ~
              definitions have the same bodies in user-level ~
              (\"untranslated\") syntax~@0.  Specify :simplify-body nil or ~
              use option :must-simplify to avoid this error."
             msg))))
   (t (value nil))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Additional main utilities
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrec fn-simp-body-result
  ((runes . body)
   (equalities . fnsr)
   . recursivep) ; recursivep is for the new function, rather than for the old
  nil)

(defun fn-simp-body-rec (body thyps address-subterm-governors-lst
                              geneqv thints must-simplify
                              ctx wrld state
                              runes subterm-equalities)

; See fn-simp-body.  Here we recur, simplifying at each indicated subterm.  The
; subterms aren't nested, so it's reasonable to modify body as we recur.

; Subterm-equalities is nil at the top level, and should be returned to match
; the order of the list of governors in the input
; address-subterm-governors-lst.

  (cond
   ((endp address-subterm-governors-lst)
    (value (make fn-simp-body-result
                 :runes runes
                 :body body                               ; needs substitution
                 :equalities (reverse subterm-equalities) ; may need subst.
                 :fnsr nil                                ; to be filled in
                 :recursivep nil                          ; to be filled in
                 )))
   (t
    (b* (((list* address subterm bindings governors)
          (car address-subterm-governors-lst))
         (geneqv-subterm (ext-geneqv-at-subterm body address geneqv
                                                nil ; pequiv-info
                                                (ens state)
                                                wrld))
         (equiv-at-subterm (equiv-from-geneqv geneqv-subterm))
         ((er (cons rrec runes1))
          (simplify-hyp-list thyps governors thints ctx state))
         ((er (cons new-subterm runes2))
          (simplify-defun-term subterm bindings geneqv-subterm rrec
                               (get-must-simplify :body must-simplify)
                               ctx state))
         (runes (union-equal runes1 (union-equal runes2 runes)))
         (old-subterm (sublis-var bindings subterm))
         (subterm-equality
          (if (equal old-subterm new-subterm)
              *t* ; special marker when no before-vs-after lemma
            `(,equiv-at-subterm ,old-subterm ,new-subterm)))
         (new-body (ext-fdeposit-term body address new-subterm)))
      (fn-simp-body-rec new-body thyps
                        (cdr address-subterm-governors-lst)
                        geneqv thints must-simplify
                        ctx wrld state
                        runes
                        (cons subterm-equality subterm-equalities))))))

(defun fn-simp-body (fn fn-simp mut-rec-p
                        simplify-body body thyps
                        address-subterm-governors-lst
                        geneqv thints must-simplify fn-simp-alist
                        ctx wrld state)

; We return an error triple such that, in the non-error case, the value is a
; fn-simp-body-result record.  The :equalities field of that record is a list
; of calls of equivalence relations, where that list is nil if simplify-body is
; nil.

  (cond
   ((null simplify-body)
    (let ((recursivep (recursivep fn nil wrld)))
      (value (make fn-simp-body-result
                   :runes nil
                   :body (fsublis-fn-simple fn-simp-alist body)
                   :equalities nil
                   :fnsr (make-fnsr fn fn-simp
                                    (and (not mut-rec-p) recursivep)
                                    thyps wrld)
                   :recursivep recursivep))))
   (t
    (b* (((er result) (fn-simp-body-rec body thyps
                                        address-subterm-governors-lst
                                        geneqv thints must-simplify
                                        ctx wrld state
                                        nil nil))
         (new-body (fsublis-fn-simple fn-simp-alist
                                      (access fn-simp-body-result result
                                              :body)))
         (recursivep (or mut-rec-p ; always preserve mutual-recursion
                         (ffnnamep fn-simp new-body)))
         (fnsr (make-fnsr fn fn-simp
                          (and (not mut-rec-p) recursivep)
                          thyps wrld))
         (fnc (access fnsr fnsr :copy))
         (equalities (access fn-simp-body-result result :equalities)))
      (value (change fn-simp-body-result result ; :runes is unchanged
                     :body new-body
                     :equalities (if (eq fn fnc)
                                     (fsublis-fn-lst-simple fn-simp-alist
                                                            equalities)
                                   equalities)
                     :fnsr fnsr
                     :recursivep recursivep))))))

(define-pc-macro sd-simplify-equality (s-cmd)
  (let* ((conc (conc t))
         (current-addr (current-addr t))
         (current-term (fetch-term conc current-addr)))
    (value (case-match current-term
             (('if & ''t &)
              `(do-all (:dive 1)
                       (:dive 1)
                       ,s-cmd
                       :up
                       :up
                       (:dive 3)
                       (:sd-simplify-equality ,s-cmd)))
             (& `(:do-all (:dive 1)
                          ,s-cmd))))))

(defun before-vs-after-lemmas (fnsr hyps fn-hyps-name
                                    formals governors-lst
                                    subterm-equalities fn-runes expand
                                    index wrld)
  (cond
   ((endp governors-lst)
    (assert$
     (null subterm-equalities)
     nil))
   ((equal (car subterm-equalities)
           t) ; untranslate of special marker, *t*
    (before-vs-after-lemmas fnsr hyps fn-hyps-name
                            formals
                            (cdr governors-lst)
                            (cdr subterm-equalities)
                            fn-runes
                            expand
                            (1+ index)
                            wrld))
   (t
    (let ((s-cmd
           `(:then (:succeed
                    (:s :repeat 3 ; somewhat arbitrary
                        :backchain-limit 500 ; somewhat arbitrary
                        :expand ,expand
                        :normalize nil))
                   (:prove ,@(and expand
                                  `(:hints (("Goal" :expand ,expand)))))))
          (all-hyps (append (and hyps
                                 `((,fn-hyps-name ,@formals)))
                            (car governors-lst))))
      (assert$
       (consp subterm-equalities)
       (cons
        `(defthm ,(before-vs-after-name fnsr index wrld)
           ,(implicate-untranslated-terms
             all-hyps
             (car subterm-equalities))
           :instructions
           ((:in-theory ,fn-runes)
            ,@(and all-hyps
                   `((:dive 1)
                     ,s-cmd
                     :top
                     :promote))
            ,@(and (flambda-applicationp (car subterm-equalities))

; Thus, we have a lambda generated by equiv-from-geneqv.  We expand it to get
; a term (if (equiv1 u1 u2) 't (if (equiv2 u1 u2) 't ... )).

                   '(:expand))
            (:sd-simplify-equality ,s-cmd)
            :top

            (:orelse

; We have attempted to replace each relevant equality (equal old new) by (equal
; new new), but we might instead have (equal new' new) where new' is not
; (quite?) equal to new.  It seems unrealistic to expect that our calls to the
; expander and the like during simplification -- that is, our attempts to use
; various pieces of the ACL2 prover -- would be replicated reliably by our
; proof-builder commands.  So use use :orelse here so that if our initial
; attempts fail, then we can fall back on a prover call.

             (:protect
              (:insist-all-proved

; We have seen a case where a single :s-prop invocation here is not sufficient.
; This seems to have been because the left-hand side had no LET expressions but
; the right-hand side did.

               (:succeed
                (:do-all (:repeat :s-prop)

; We have seen a case in which s-prop didn't suffice.  The remaining goal
; looked like (or (foo x y) y (... (foo x nil) ...)), where the occurrences of
; (foo x nil) are clearly false but this isn't clear to s-prop.

                         :split))))
             (:prove ,@(and expand
                            `(:hints (("Goal" :expand ,expand)))))))
;          :hints (("Goal" :in-theory ,fn-runes :expand ,expand))
           :rule-classes nil)
        (before-vs-after-lemmas fnsr hyps fn-hyps-name
                                formals
                                (cdr governors-lst)
                                (cdr subterm-equalities)
                                fn-runes
                                expand
                                (1+ index)
                                wrld)))))))

(defun sd-untranslate (term wrld)

; Here, "sd" suggests "simplify-defun" or "special-destructor".  Our goal is to
; prevent the introduction of OR in a lambda, in the case that a lambda was
; generated by equiv-from-geneqv.

  (cond ((flambda-applicationp term)
         (fcons-term (ffn-symb term)
                     (untranslate-lst (fargs term) nil wrld)))
        (t (untranslate term nil wrld))))

(defun sd-untranslate-lst (termlist wrld)
  (cond ((endp termlist) nil)
        (t (cons (sd-untranslate (car termlist) wrld)
                 (sd-untranslate-lst (cdr termlist) wrld)))))

(defun sd-new-def-event (defun? fn-simp formals fn-ruler-extenders simp-guard
                          simp-measure new-recursivep verify-guards
                          old-normalize-pair simp-body show-hints
                          termination-hints)
  `(,defun? ,fn-simp ,formals
     (declare
      (xargs ,@old-normalize-pair ; nil, (:normalize nil), nor (:normalize t)
             ,@(and fn-ruler-extenders
                    `(:ruler-extenders ,fn-ruler-extenders))
             :guard ,simp-guard
             ,@(and simp-measure

; It is possible that the original definition is recursive but the simplified
; definition is not.

                    new-recursivep
                    `(:measure ,simp-measure))
             :verify-guards ,verify-guards
             ,@(and new-recursivep
                    show-hints
                    `(:hints ,termination-hints))))
     ,simp-body))

(defun fn-simp-defs-termination-hints (hints fn wrld
                                             computed-hint-lst
                                             theory
                                             theory-alt
                                             verbose)
  (if (not (eq hints :auto))
      hints
    (let ((old-recursivep (getpropc fn 'recursivep nil wrld)))
      `(("Goal"
         ,@(and old-recursivep
                `(:instructions
                  ((:prove-termination ,fn ,theory ,theory-alt ,verbose)))))
        ,@computed-hint-lst))))

(defun fn-simp-defs-verify-guards-hints (guard-hints fn wrld
                                                     computed-hint-lst
                                                     theory
                                                     theory-alt
                                                     verbose)
  (if (not (eq guard-hints :auto))
      guard-hints
    (let ((compliant-p (eq (symbol-class fn wrld)
                           :common-lisp-compliant)))
      (cond (compliant-p
             `(("Goal"
                :instructions
                ((:prove-guard ,fn ,theory ,theory-alt ,verbose)))))
            (computed-hint-lst
             `(,@computed-hint-lst))
            (t nil)))))

; Originally, modified from simplify-term-with-tool2 as defined in
; kestrel-acl2/transformations/simplify-body.lisp:
(defun fn-simp-defs (fn fn-simp mut-rec-p hyps thyps theory equiv expand
                        new-enable
                        simplify-body
                        simplify-guard guard-hints verify-guards
                        simplify-measure measure-hints measure
                        untranslate must-simplify non-executable
                        fn-simp-alist fn-simp-is-fn-name
                        verbose ctx wrld state)

; Note that measure has already gone through a bit of checking in
; simplify-defun-fn.

  (b* ((formals (formals fn wrld))
       (fn-runes (fn-runes-name fn wrld))
       (guard-verified-p (eq (symbol-class fn wrld)
                             :common-lisp-compliant))
       (hints-from-theory+expand (theory+expand-to-hints theory expand))
       (computed-hint-lst (and (not (eq theory :none))
                               `((quote (:in-theory ,theory)))))
       (fn-body (body fn nil wrld))
       (ev (get-event fn wrld))
       ((when (null ev))
        (er-soft+ ctx :implementation-error nil
                  "There is no event for ~x0.  We thought we had checked that ~
                   ~x0 was introduced with DEFUN or DEFUN-SK."
                  fn))
       (fn-ubody (fn-ubody fn fn-body wrld ev))
       (fn-guard (guard fn nil wrld))
       (fn-ruler-extenders
        (let ((just (getpropc fn 'justification nil wrld)))
          (and just
               (let ((tmp (access justification just :ruler-extenders)))
                 (and (not (equal tmp (default-ruler-extenders wrld)))
                      tmp)))))
       ((er address-subterm-governors-lst)
        (if (not (booleanp simplify-body)) ; then non-nil value (or, error)
            (mv-let (ctx msg-or-val)
              (ext-address-subterm-governors-lst
               simplify-body fn-body ctx state)
              (cond (ctx

; Presumably we have a bad pattern, so we'll call this ":wrong-form".

                     (er-soft+ ctx :wrong-form nil "~@0" msg-or-val))
                    (t (value msg-or-val))))
          (value (list (list* nil fn-body nil nil)))))
       (governors-lst (strip-cddrs (strip-cdrs address-subterm-governors-lst)))
       ((er thints)
        (translate-hints ctx hints-from-theory+expand ctx wrld state))
       ((er body-result)
        (fn-simp-body fn fn-simp mut-rec-p
                      simplify-body fn-body thyps
                      address-subterm-governors-lst
                      (geneqv-from-g?equiv equiv wrld)
                      thints
                      (get-must-simplify :body must-simplify)
                      fn-simp-alist
                      ctx wrld state))
       (fnsr (access fn-simp-body-result body-result :fnsr))
       (new-body (access fn-simp-body-result body-result :body))
       (new-recursivep (access fn-simp-body-result body-result :recursivep))
       ((er trivial-rrec)
        (cond
         ((or simplify-guard (and measure simplify-measure)) ; optimization
          (acl2::make-rrec nil thints untranslate ctx wrld state))
         (t (value nil))))
       ((er guard-result)
        (if simplify-guard
            (simplify-defun-term fn-guard
                                 nil ; alist
                                 *geneqv-iff* trivial-rrec
                                 (get-must-simplify :guard must-simplify)
                                 ctx state)
          (value (cons fn-guard nil))))
       (new-guard (car guard-result))
       (verify-guards-p (or (eq verify-guards t)
                            (and guard-verified-p
                                 (not (eq verify-guards nil)))))
       ((er -)
        (let ((bad-fns-guard (and verify-guards-p
                                  (collect-ideals
                                   (set-difference-rassoc-eq
                                    (all-ffn-symbs new-guard nil)
                                    fn-simp-alist)
                                   wrld
                                   nil)))
              (bad-fns-body (and verify-guards-p
                                 (collect-ideals
                                  (set-difference-rassoc-eq
                                   (all-ffn-symbs new-body nil)
                                   fn-simp-alist)
                                  wrld
                                  nil))))
          (cond ((or bad-fns-guard bad-fns-body)
                 (flet ((reason (type term fns wrld)
                                (msg "its ~s0, ~x1, calls the ~
                                      non-guard-verified function~#2~[~/s~] ~
                                      ~&2"
                                     type
                                     (untranslate term nil wrld)
                                     fns)))
                   (er-soft+ ctx :condition-failed nil

; The choice of :condition-failed as the error type is perhaps controversial,
; as one could reasonably type the failure as :bad-input since guard
; verification didn't fail -- it wasn't even attempted.  But consider the
; following example.

;   (defun f1 (x) x)
;   (defun f2 (x) (declare (xargs :guard t)) x)
;   (defthm f2-is-f1 (equal (f2 x) (f1 x)))
;   (defun f3 (x) (declare (xargs :guard t)) (f2 x))
;   (in-theory (disable f1))
;   (simplify f3)

; It's not fair in this case to besmirch the simplify command with :bad-input!

                             "It is illegal to verify guards for the new ~
                              function, ~x0, because ~@1~@2."
                             fn-simp
                             (cond (bad-fns-guard
                                    (reason "guard" new-guard bad-fns-guard wrld))
                                   (t ; bad-fns-body
                                    (reason "body" new-body bad-fns-body wrld)))
                             (cond
                              ((and bad-fns-guard bad-fns-body)
                               (msg ", and ~@0"
                                    (reason "body" new-body bad-fns-body wrld)))
                              (t "")))))
                (t (value nil)))))
       ((er measure-result)
        (if (and measure simplify-measure)
            (simplify-defun-term measure
                                 nil ; alist
                                 nil ; g?equiv
                                 trivial-rrec
                                 (get-must-simplify :measure must-simplify)
                                 ctx state)
          (value (cons measure nil))))
       (defun? (if non-executable
                   (if new-enable 'defun-nx 'defund-nx)
                 (if new-enable 'defun 'defund)))
       (stobjs-out-exec (and (not non-executable)
                             (stobjs-out fn wrld)))
       (simp-body (cond
                   ((eq untranslate t)
                    (untranslate new-body nil wrld))
                   ((eq untranslate nil)
                    new-body)
                   ((eq untranslate :nice-expanded)
                    (directed-untranslate-no-lets
                     fn-ubody fn-body new-body nil stobjs-out-exec wrld))

; Otherwise untranslate is :nice, but we give special treatment for defun-nx
; (and defund-nx), to eliminate an extra prog2$.  This may not be necessary,
; since prog2$ is generally eliminated by simplification, but it's harmless
; enough and could be useful if we ever cause directed-untranslate to restore
; prog2$.

                   ((and non-executable
                         (eq (car fn-ubody) ; always true?
                             'prog2$)
                         (let ((x (directed-untranslate
                                   fn-ubody fn-body new-body nil nil wrld)))
                           (and (eq (car x) 'prog2$) ; always true?
                                (car (last x))))))
                   (t
                    (directed-untranslate
                     fn-ubody fn-body new-body nil stobjs-out-exec wrld))))
       ((er -)
        (cond ((and simplify-body
                    (get-must-simplify :body must-simplify))
               (check-simplified (if (recursivep fn nil wrld)
                                     (sublis fn-simp-alist fn-ubody)
                                   fn-ubody)
                                 fn-body simp-body new-body
                                 (if (recursivep fn nil wrld)
                                     (msg ", after replacing ~&0 by ~&1~@2 in ~
                                           the old (untranslated) body"
                                          (strip-cars fn-simp-alist)
                                          (strip-cdrs fn-simp-alist)
                                          (if (cdr fn-simp-alist)
                                              ", respectively,"
                                            ""))
                                   "")
                                 ctx state))
              (t (value nil))))
       (subterm-equalities

; At one time we untranslated the equalities.  However, that proved awkward
; because in the case that we use equiv-from-geneqv, we have a lambda with an
; embedded disjunction that untranslated terms (if x *t* y) to (or x y) which
; then translated back to (if x x y).

        (sd-untranslate-lst
         (access fn-simp-body-result body-result :equalities)
         wrld))
       (simp-guard
        (untranslate (car guard-result) nil wrld))
       (simp-measure
        (and measure-result
             (untranslate (car measure-result) nil wrld)))
       (runes0 (merge-sort-lexorder
                (union$ (access fn-simp-body-result body-result :runes)
                        (cdr guard-result)   ; possibly nil
                        (cdr measure-result) ; possibly nil
                        :test 'equal)))
       (state (cond (verbose
                     (fms "List of runes used in simplification for ~
                           ~x0:~|~x1~%"
                          (list (cons #\0 fn)
                                (cons #\1 (acl2::drop-fake-runes runes0)))
                          (standard-co state) state nil))
                    (t state)))
       (runes (if hyps
                  (add-to-set-equal `(:definition ,(fn-hyps-name fn wrld))
                                    runes0)
                runes0))
       (old-normalize (get-normalize fn wrld *unspecified-xarg-value* ev))
       (old-normalize-pair (and (not (equal old-normalize
                                            *unspecified-xarg-value*))
                                `(:normalize ,old-normalize)))
       (termination-hints (fn-simp-defs-termination-hints measure-hints fn wrld
                                                          computed-hint-lst
                                                          fn-runes
                                                          theory
                                                          verbose))
       (new-def-event-pre
        (sd-new-def-event

; It is tempting to use defun? as the first argument.  But then the later
; non-local definition will have an in-theory event in the case of defund or
; defund-nx, which might or might not be harmless (consider if
; set-in-theory-redundant-okp has been called), so we take this conservative
; approach.

         (if non-executable 'defun-nx 'defun)
         fn-simp formals fn-ruler-extenders simp-guard
         simp-measure new-recursivep nil ; verify-guards
         old-normalize-pair simp-body t termination-hints))
       (new-def-event-show
        (sd-new-def-event defun? fn-simp formals fn-ruler-extenders simp-guard
                          simp-measure new-recursivep verify-guards-p
                          old-normalize-pair simp-body nil nil))
       (verify-guards-hints
        (fn-simp-defs-verify-guards-hints guard-hints fn wrld
                                          computed-hint-lst
                                          `(cons ',fn-simp-is-fn-name
                                                 ,fn-runes)
                                          `(cons ',fn-simp-is-fn-name
                                                 ,theory)
                                          verbose))
       (new-def-event-installed
        (sd-new-def-event defun? fn-simp formals fn-ruler-extenders simp-guard
                          simp-measure new-recursivep verify-guards-p
                          old-normalize-pair simp-body nil nil))
       (verify-guards-form
        (and verify-guards-p ; else don't care
             `(verify-guards
                ,fn-simp
                ,@(and verify-guards-hints
                       `(:hints ,verify-guards-hints)))))
       (on-failure-msg
        (msg "Guard verification has failed for the new function, ~x0. ~ See ~
              :DOC apt::simplify-failure for some ways to address this ~
              failure."
             fn-simp)))
    (value ; (defun defconst &optional in-theory)
     `(,body-result
       ,new-def-event-pre
       (make-event (let ((thy (merge-sort-lexorder
                               (union-equal
                                ',(acl2::drop-fake-runes runes)
                                (acl2::congruence-theory-fn :here
                                                            (w state))))))
                     (list 'defconst ',fn-runes
                           (list 'quote thy))))
       ,(and simplify-body

; It is useful to break out this lemma, which is about the subterm that is
; being simplified rather than (in the case that :simplify-body is a pattern)
; the entire body.  For example, the form (simplify-defun outputs$6 ...) in
; MUSE/derivations/bresenham/Experiments/derivation.lisp was failing until we
; added this subterm-level lemma for simplify-defun.

             (before-vs-after-lemmas fnsr hyps (fn-hyps-name fn wrld)
                                     formals governors-lst
                                     subterm-equalities fn-runes expand
                                     0 wrld))
       ,(and verify-guards-p
             `(on-failure
               ,(if verbose
                    verify-guards-form
                  `(with-output :off :all
                     ,verify-guards-form))
               :ctx ,ctx
               :erp :condition-failed
               :val nil
               :msg ,on-failure-msg))
       ,new-def-event-installed
       ,new-def-event-show))))

(defunsr fn-simp-is-fn-lemma (fnsr fn-hyps theorem-name equiv wrld)
  (let* ((fn-formals (formals fn wrld))
         (fn-call (cons fn fn-formals))
         (fn-simp-call (cons fn-simp fn-formals))
         (equality ; we get this just right so that the :by hint will work
          (if (eq fn fnc)
              `(,equiv ,fn-call ,fn-simp-call)
            `(,equiv ,fn-simp-call ,fn-call)))
         (lemma-name ; keep in sync with similar test in fn-simp-is-fn
          (if (and (eq fn fnc) ; else order will be reversed
                   (null fn-hyps))
              (fn-simp-is-fn-name fn fn-simp theorem-name wrld)
            (fn-simp-is-fn-lemma-name fn fn-simp theorem-name wrld)))
         (hyps (and fn-hyps
                    (list (cons fn-hyps fn-formals)))))

; We could quite possibly use defthmd here instead.

    `(defthm ,lemma-name
       ,(implicate-untranslated-terms hyps equality)
       :rule-classes nil)))

(defunsr fn-simp-is-fn (fnsr fn-hyps hyps theorem-name thm-enable equiv
                             wrld)

; Warning: The function remove-final-hints-lst is ultimately called to remove
; the final hints from a list of forms produced by fn-simp-is-fn.  If you
; change this form so that it does not end with :hints xxx for some xxx, be
; sure to visit that call of remove-final-hints-lst.

  (let* ((fn-formals (formals fn wrld))
         (fn-call (cons fn fn-formals))
         (fn-simp-call (cons fn-simp fn-formals))
         (equality `(,equiv ,fn-call ,fn-simp-call))
         (defthm? (if thm-enable 'defthm 'defthmd))
         (hyps (remove-equal t (remove-equal *t* hyps))))
    `(,defthm? ,(fn-simp-is-fn-name fn fn-simp theorem-name wrld)
       ,(implicate-untranslated-terms hyps equality)
       :hints (("Goal"
                :use ,(fn-simp-is-fn-lemma-name fn fn-simp theorem-name wrld)
                :in-theory ,(and fn-hyps `'(,fn-hyps)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Putting it all together
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun simplify-defun-theory (clique-runic-designators
                              theory enable disable ctx state)
  (cond
   ((not (or (eq theory :none)
             (and (eq enable :none)
                  (eq disable :none))))
    (er-soft+ ctx :bad-input nil
      "It is illegal to supply a value other than :none for both the :theory ~
       (or :hyps-preserved-theory) argument and the corresponding :enable or ~
       :disable argument."))
   (t (cond
       ((not (eq theory :none))
        (value theory))
       (t ; hence (eq theory :none)
        (let* ((enable (if (or (eq enable :none)
                               (consp enable)
                               (null enable))
                           enable ; else expect a non-nil symbol
                         (list enable)))
               (disable (cond
                         ((member-eq disable '(:none nil))
                          clique-runic-designators)
                         (t
                          (append clique-runic-designators
                                  (if (consp disable)
                                      disable ; else expect a non-nil symbol
                                    (list disable)))))))
          (value (cond ((eq enable :none) ; just disable
                        (cons 'disable* disable))
                       (t
                        (list 'e/d* enable disable))))))))))

(defun simplify-defun-theory-lst (clique-runic-designators
                                  hyps-preserved-theory**
                                  hyps-preserved-enable**
                                  hyps-preserved-disable**
                                  ctx state)
  (cond ((endp hyps-preserved-theory**) (value nil))
        (t (er-let* ((hd (simplify-defun-theory
                          clique-runic-designators
                          (car hyps-preserved-theory**)
                          (car hyps-preserved-enable**)
                          (car hyps-preserved-disable**)
                          ctx state))
                     (tl (simplify-defun-theory-lst
                          clique-runic-designators
                          (cdr hyps-preserved-theory**)
                          (cdr hyps-preserved-enable**)
                          (cdr hyps-preserved-disable**)
                          ctx state)))
             (value (cons hd tl))))))

(defun simplify-defun-hints (clique-runic-designators hints ctx state)

; Hints is the value of a :hints argument, e.g.:
; (:assumptions-preserved (("Goal" :in-theory '(integer-listp-of-cdr))))

  (cond
   ((null hints)
    (value `(("Goal" :in-theory (disable* ,@clique-runic-designators)))))
   (t (er-let* ((kwd-alist (ensure-is-hints-specifier$ hints
                                                       '(:assumptions-preserved)
                                                       "The :HINTS input"
                                                       :bad-input
                                                       nil)))
        (assert$ (and (eq (car kwd-alist) :assumptions-preserved)
                      (null (cddr kwd-alist)))
                 (value (cadr kwd-alist)))))))

(defun simplify-defun-hints-lst (clique-runic-designators hints** ctx state)
  (cond ((endp hints**) (value nil))
        (t (er-let* ((hd (simplify-defun-hints
                          clique-runic-designators
                          (car hints**)
                          ctx state))
                     (tl (simplify-defun-hints-lst
                          clique-runic-designators
                          (cdr hints**)
                          ctx state)))
             (value (cons hd tl))))))

(defun check-equivalence-relation (equiv ctx wrld state)
  (cond ((null equiv) (value 'equal))
        ((and (symbolp equiv)
              (equivalence-relationp equiv wrld))
         (value equiv))
        (t (er-soft+ ctx :bad-input nil
                   "The :equiv argument must be a known equivalence relation ~
                    in the current ACL2 world, but ~x0 is not."
                   equiv))))

(defun simplify-defun-tuple (fn mut-rec-p clique-runic-designators
                                assumptions hyp-fn
                                theory enable disable
                                equiv expand
                                theorem-name
                                thm-enable new-enable
                                simplify-body
                                simplify-guard guard-hints
                                verify-guards
                                simplify-measure
                                measure-hints measure
                                untranslate must-simplify non-executable
                                fn-simp-alist
                                verbose wrld ctx state)

; Among the requirements of the returned tuple is that its fnsr
; corresponds to the input fn.

  (b* ((rune (fn-rune-nume fn nil nil wrld))
       (new-enable
        (if (eq new-enable :auto)
            (and rune ; true if we've done enough error checking?
                 (enabled-runep rune (ens state) wrld))
          new-enable))
       ((er hyps) (assumptions-to-hyps assumptions hyp-fn fn nil ctx wrld
                                       state))
       ((er thyps) (translate-hyp-list hyps fn ctx wrld state))
       (expand (fix-expand-hint expand))
       (fn-hyps (and hyps (fn-hyps-name fn wrld)))
       (fn-hyps-def (and hyps (fn-hyps-def fn fn-hyps hyps
                                           (all-vars1-lst thyps nil)
                                           wrld)))
       (fn-simp (cdr (assoc-eq fn fn-simp-alist)))
       ((when (not (member-eq untranslate *untranslate-specifier-keywords*)))
        (er-soft+ ctx :bad-input nil
          "The value of keyword :UNTRANSLATE for ~x0 must be ~v1.  The value ~
           ~x2 is thus illegal."
          'simplify *untranslate-specifier-keywords* untranslate))
       ((when (and hyp-fn assumptions))
        (er-soft+ ctx :bad-input nil
          "It is illegal for ~x0 to specify non-nil values for both :HYP-FN ~
           and :ASSUMPTIONS."
          'simplify))
       ((er must-simplify)
        (check-must-simplify must-simplify ctx state))
       ((er equiv)
        (check-equivalence-relation equiv ctx wrld state))
       ((er theory)
        (simplify-defun-theory clique-runic-designators theory enable disable ctx
                               state))
       ((er measure)
        (let ((measure-to-use
               (if (eq measure :auto)
                   (let ((just (getpropc fn 'justification nil wrld)))
                     (and just
                          (access justification just :measure)))
                 measure)))
          (cond ((and measure
                      (if (eq measure :auto)
                          (ffn-symb-p measure-to-use :?)
                        (and (consp measure-to-use) ; untranslated term
                             (eq (car measure-to-use)
                                 :?))))
                 (cond
                  ((eq measure :auto)
                   (er-soft+ ctx :condition-failed nil
                     "Simplify has been called on function ~x0, with the ~
                      default value :AUTO for :MEASURE.  This is illegal ~
                      because the existing definition of ~x0 uses a measure ~
                      that is a call of :?, namely, ~x1."
                     fn
                     measure-to-use))
                  (t
                   (er-soft+ ctx :condition-failed nil
                     "It is illegal to simplify the DEFUN for ~x0 because the ~
                      specified measure, ~x1, is a call of :?."
                     fn measure-to-use))))
                (t (value measure-to-use)))))
       ((er non-executable)
        (case non-executable
          ((t nil) (value non-executable))
          (:auto (value (getpropc fn 'non-executablep nil wrld)))
          (otherwise (er-soft+ ctx :bad-input nil
                       "The value of :non-executable must be ~v0; thus ~x1 is ~
                        illegal."
                       '(t nil :auto)
                       non-executable))))
       (fn-simp-is-fn-name (fn-simp-is-fn-name fn fn-simp theorem-name wrld))
       ((er (list body-result
                  new-defun-pre ; (defun foo$1 ...)
                  runes-def     ; (defconst *foo-runes* ...)
                  before-vs-after-lemmas
                  verify-guards-form? new-defun-installed new-defun-show))
        (fn-simp-defs fn fn-simp mut-rec-p hyps thyps theory equiv expand
                      new-enable simplify-body simplify-guard
                      guard-hints verify-guards simplify-measure
                      measure-hints measure untranslate must-simplify
                      non-executable fn-simp-alist fn-simp-is-fn-name
                      verbose ctx wrld state))
       (new-recursivep (access fn-simp-body-result body-result :recursivep))
       (fnsr (access fn-simp-body-result body-result :fnsr))
       (fnc (access fnsr fnsr :copy))
       (fnc-recursivep (if (eq fn fnc)
                           (recursivep fn nil wrld)
                         new-recursivep))
       (fn-simp-is-fn-lemma (fn-simp-is-fn-lemma fnsr fn-hyps theorem-name
                                                 equiv wrld))
       (fn-simp-is-fn (fn-simp-is-fn fnsr fn-hyps hyps theorem-name
                                     thm-enable equiv wrld))
       ((mv not-norm-event not-norm-event-name &)
        (install-not-normalized-event fn t nil wrld)))
    (value
     `(,not-norm-event
       ,new-defun-pre
       ,fn-hyps-def
       ,(and fn-hyps (cons fnc fn-hyps))
       ,runes-def
       ,before-vs-after-lemmas
       ,fn-simp-is-fn-lemma
       ,fn-simp-is-fn
       ,verify-guards-form?
       ,new-defun-installed
       ,new-defun-show
       ,fnsr
       ,not-norm-event-name
       ,fnc-recursivep))))

(defun simplify-defun-tuple-lst (clique mut-rec-p
                                        clique-runic-designators
                                        assumptions** hyp-fn**
                                        theory** enable** disable**
                                        equiv** expand**
                                        theorem-name**
                                        thm-enable** new-enable**
                                        simplify-body**
                                        simplify-guard** guard-hints**
                                        verify-guards
                                        simplify-measure**
                                        measure-hints**
                                        measure**
                                        untranslate** must-simplify**
                                        non-executable
                                        fn-simp-alist
                                        verbose wrld ctx state)
  (cond
   ((endp clique) (value nil))
   (t
    (er-let* ((tuple
               (simplify-defun-tuple
                (car clique) mut-rec-p clique-runic-designators
                (car assumptions**) (car hyp-fn**)
                (car theory**) (car enable**) (car disable**)
                (car equiv**) (car expand**)
                (car theorem-name**)
                (car thm-enable**) (car new-enable**)
                (car simplify-body**)
                (car simplify-guard**)
                (car guard-hints**)
                verify-guards
                (car simplify-measure**)
                (car measure-hints**) (car measure**)
                (car untranslate**) (car must-simplify**)
                non-executable
                fn-simp-alist
                verbose wrld ctx state))
              (tuple-lst
               (simplify-defun-tuple-lst
                (cdr clique) mut-rec-p clique-runic-designators
                (cdr assumptions**) (cdr hyp-fn**)
                (cdr theory**) (cdr enable**) (cdr disable**)
                (cdr equiv**) (cdr expand**)
                (cdr theorem-name**)
                (cdr thm-enable**) (cdr new-enable**)
                (cdr simplify-body**)
                (cdr simplify-guard**)
                (cdr guard-hints**)
                verify-guards
                (cdr simplify-measure**)
                (cdr measure-hints**) (cdr measure**)
                (cdr untranslate**) (cdr must-simplify**)
                non-executable
                fn-simp-alist
                verbose wrld ctx state)))
      (value (cons tuple tuple-lst))))))

(defun fn-simp-is-fn-lemmas-with-hints (fn-simp-is-fn-lemma-lst
                                        fnsr-lst
                                        before-vs-after-names
                                        fn-subst
                                        used-names)
  (cond
   ((endp fn-simp-is-fn-lemma-lst) nil)
   (t
    (cons (let* ((fnsr (car fnsr-lst))
                 (fnc (access fnsr fnsr :copy)))
            (append
             (car fn-simp-is-fn-lemma-lst)
             `(:hints
               (("Goal"
                 :by
                 (:functional-instance ,(fn-is-fn-copy-name fnc)
                                       ,@fn-subst)
                 :in-theory

; At one time we only added in the congruence-theory when the current
; function's :simplify-body was non-Boolean.  But we have seen an example where
; that didn't suffice; search for "congruence-theory" in
; simplify-defun-tests.lisp.

                 (union-theories (acl2::congruence-theory :here)
                                 (theory 'minimal-theory)))
                '(:use (,@before-vs-after-names
                        ,@used-names))))))
          (fn-simp-is-fn-lemmas-with-hints
           (cdr fn-simp-is-fn-lemma-lst)
           (cdr fnsr-lst)
           before-vs-after-names
           fn-subst
           used-names)))))

(defun hyps-preserved-thm-list-1 (fnsr-lst assumptions**
                                           hints-lst
                                           fn-hyps-alist expand-lst
                                           induction-machine-lst
                                           flet-bindings
                                           verbosity-info
                                           wrld ctx acc)
  (cond
   ((endp fnsr-lst)
    (revappend acc
               (and verbosity-info
                    `((make-event
                       (pprogn (fms "~#0~[The~/All~] :ASSUMPTIONS-PRESERVED ~
                                     applicability condition~#0~[ has~/s ~
                                     have~] been proved!~|"
                                    (list (cons #\0
                                                (if (eq ',verbosity-info
                                                        'mutual-recursion)
                                                    1
                                                  0)))
                                    (standard-co state) state nil)
                               (value '(value-triple :invisible))))))))
   (t (let* ((fnsr (car fnsr-lst))
             (fnc (access fnsr fnsr :copy))
             (fn-hyps (cdr (assoc-eq fnc fn-hyps-alist)))
             (hints (car hints-lst))
             (thm (hyps-preserved-thm fnc fn-hyps
                                      (car assumptions**)
                                      hints
                                      fn-hyps-alist expand-lst
                                      (car induction-machine-lst)
                                      flet-bindings verbosity-info wrld ctx)))
        (hyps-preserved-thm-list-1
         (cdr fnsr-lst)
         (cdr assumptions**)
         (cdr hints-lst)
         fn-hyps-alist expand-lst
         (cdr induction-machine-lst)
         flet-bindings
         verbosity-info
         wrld
         ctx
         (if thm
             (cons thm acc)
           acc))))))

(defun hyps-expand-lst (fnsr-lst fn-hyps-alist wrld)
  (cond
   ((endp fnsr-lst) nil)
   (t (let ((formals (formals (access fnsr (car fnsr-lst) :orig) wrld))
            (fn-hyps (cdar fn-hyps-alist)))
        (cons `(:free ,formals (,fn-hyps ,@formals))
              (hyps-expand-lst (cdr fnsr-lst) (cdr fn-hyps-alist) wrld))))))

(defun hyps-preserved-thm-list (clique fnsr-lst assumptions**
                                       hints-lst fn-hyps-alist
                                       fn-hyps-def-lst verbose wrld ctx)
  (assert$
   (consp clique)
   (let ((induction-machine-single-case
          (and (null (cdr clique))
               (getpropc (access fnsr (car fnsr-lst) :copy)
                         'induction-machine nil wrld))))
     (cond
      ((and (null (cdr clique))
            (null induction-machine-single-case))
       nil)
      (t
       (let* ((induction-machine-lst
               (cond
                ((null (cdr clique))
                 (assert$ induction-machine-single-case
                          (list induction-machine-single-case)))
                (t (mut-rec-induction-machines (access-fnsr-copy-lst fnsr-lst)
                                               wrld))))
              (expand-lst (hyps-expand-lst fnsr-lst fn-hyps-alist wrld)))
         (hyps-preserved-thm-list-1
          fnsr-lst assumptions** hints-lst
          fn-hyps-alist expand-lst induction-machine-lst
          (strip-cdrs fn-hyps-def-lst)
          (and verbose (if (cdr clique) 'mutual-recursion 'single-recursion))
          wrld ctx nil)))))))

(defun too-many-ifs-pre-rewrite-noop (args counts)
      (declare (ignore args counts)
               (xargs :mode :logic :guard t))
      nil)

(defun too-many-ifs-post-rewrite-noop (args val)
      (declare (ignore args val)
               (xargs :mode :logic :guard t))
      nil)

(defun map-local (forms)
  (pairlis-x1 'local (pairlis$ forms nil)))

(defun simplify-defun-heuristics (alist)

; It is a bit of overkill to make defattach-system local, since it already
; expands to a local event.  But we use make it local anyhow, so that tools
; will avoid printing these events to the screen.

  `(local
    (with-output
      :off :all
      :on error
      (progn
        (defattach-system
         too-many-ifs-pre-rewrite
         ,(or (cdr (assoc-eq 'too-many-ifs-pre-rewrite alist))
              'too-many-ifs-pre-rewrite-noop))
        (defattach-system
         too-many-ifs-post-rewrite
         ,(or (cdr (assoc-eq 'too-many-ifs-post-rewrite alist))
              'too-many-ifs-post-rewrite-noop))
        (defattach-system
         assume-true-false-aggressive-p
         ,(or (cdr (assoc-eq 'assume-true-false-aggressive-p alist))
              'constant-t-function-arity-0))

; We considered avoiding the next attachment.  Our thinking was that while we
; want to avoid swapping true and false IF-branches in order to preserve
; structure, we prefer to use the "real" prover (i.e., without the attachment
; below) when validating the simplification.  However, we seem to have found
; examples where rewrite rules that applied during the original simplification
; no longer applied during the validation.

        (defattach-system
         rewrite-if-avoid-swap
         ,(or (cdr (assoc-eq 'rewrite-if-avoid-swap alist))
              'constant-t-function-arity-0))))))

(defun remove-final-hints-lst (lst)

; Lst is a list of forms, each of which is a true-list concluding with :hints
; xxx (for some xxx that depends on the form).  We return the result of
; removing those hints.

  (cond ((endp lst) nil)
        (t (cons (let* ((form (car lst))
                        (len (length form))
                        (kwd (assert$ (<= 2 len) ; could strengthen
                                      (nth (- len 2) form))))
                   (assert$ (eq kwd :hints)
                            (butlast form 2)))
                 (remove-final-hints-lst (cdr lst))))))

(defun update-stobjs-out (fn-simp-alist installed-wrld wrld)
  (cond ((endp fn-simp-alist) wrld)
        (t (update-stobjs-out
            (cdr fn-simp-alist)
            installed-wrld
            (putprop (cdar fn-simp-alist)
                     'stobjs-out
                     (stobjs-out (caar fn-simp-alist) installed-wrld)
                     wrld)))))

(defun copy-def+-event (fnc hyps-fn hyps-preserved-thm-names equiv
                            fnc-recursivep orig ctx)

; This variant of copy-def-event is intended to be used in the implementation
; of simplify-defun under encapsulate-report-errors, to report a more useful
; error than the default when the copied function is recursive and the equiv is
; not EQUAL.

; Note that as with copy-def, hyps-fn can be an alist.

  (let ((event `(copy-def ,fnc
                          :hyps-fn ,hyps-fn
                          :hyps-preserved-thm-names ,hyps-preserved-thm-names
                          :equiv ,equiv)))
    (if (and fnc-recursivep
             (not (member-eq equiv '(nil equal))))
        `(on-failure ,event
                     :ctx ,ctx
                     :msg ,(msg "An attempt to simplify the definition of ~x0 ~
                                 has failed, probably because ~@1 is ~
                                 recursive and the equivalence relation ~
                                 specified by :EQUIV is ~x2, not ~x3.  See ~
                                 the section \"Recursion and equivalence ~
                                 relations\" in :DOC apt::simplify-failure."
                                orig
                                (if (eq fnc orig)
                                    "its definition"
                                  (msg "the definition of the new function, ~
                                        ~x0,"
                                       fnc))
                                equiv
                                'equal))
      event)))

(defun simplify-defun-form (clique mut-rec-p assumptions** hyp-fn**
                                   theory** enable** disable**
                                   equiv** expand**
                                   hints**
                                   theorem-name** new-name**
                                   thm-enable** new-enable**
                                   simplify-body**
                                   simplify-guard** guard-hints**
                                   verify-guards
                                   simplify-measure**
                                   measure-hints** measure**
                                   untranslate** must-simplify**
                                   non-executable
                                   verbose
                                   ctx state)
  (b* ((clique-runic-designators (clique-runic-designators clique))
       ((er -)
        (trans-eval '(with-output :off (event summary)
                       (set-ignore-ok t))
                    ctx state nil))
       (wrld0 (w state))
       ((er fn-simp-alist)
        (fn-simp-alist clique new-name** ctx state))
       (wrld (update-stobjs-out fn-simp-alist wrld0 wrld0))
       ((er tuple-lst)
        (simplify-defun-tuple-lst
         clique mut-rec-p
         clique-runic-designators
         assumptions** hyp-fn**
         theory** enable** disable**
         equiv** expand**
         theorem-name**
         thm-enable** new-enable**
         simplify-body**
         simplify-guard** guard-hints**
         verify-guards
         simplify-measure**
         measure-hints** measure**
         untranslate** must-simplify**
         non-executable
         fn-simp-alist
         verbose wrld ctx state))
       ((er hints-lst)
        (simplify-defun-hints-lst clique-runic-designators
                                  (or hints**

; If hints** is nil, then we convert it to a list of nils of the appropriate
; length.

                                      (make-list (length clique)))
                                  ctx
                                  state))
       (local-install-not-normalized-lst
        (strip-nths 0 tuple-lst))
       (new-defun-pre-lst
        (strip-nths 1 tuple-lst))
       (fn-hyps-def-lst
        (strip-nths 2 tuple-lst))
       (fn-hyps-names-alist
        (remove-nils (strip-nths 3 tuple-lst)))
       (runes-def-lst
        (strip-nths 4 tuple-lst))
       (before-vs-after-lemmas-lst
        (strip-nths 5 tuple-lst))
       (fn-simp-is-fn-lemma-lst
        (strip-nths 6 tuple-lst))
       (fn-simp-is-fn-lst
        (strip-nths 7 tuple-lst))
       (verify-guards-form?-lst
        (strip-nths 8 tuple-lst))
       (new-defun-installed-lst
        (strip-nths 9 tuple-lst))
       (new-defun-show-lst
        (strip-nths 10 tuple-lst))
       (fnsr-lst
        (strip-nths 11 tuple-lst))
       (not-norm-event-names
        (strip-nths 12 tuple-lst))
       (fnsr (car fnsr-lst))
       (fnc (access fnsr fnsr :copy))
       (orig (access fnsr fnsr :orig))
       (fnc-recursivep (nth 13 (car tuple-lst)))
       (all-before-vs-after-lemmas
        (append-lst before-vs-after-lemmas-lst))
       (fn-simp-is-fn-lemma-lst-with-hints
        (fn-simp-is-fn-lemmas-with-hints
         fn-simp-is-fn-lemma-lst
         fnsr-lst
         (strip-cadrs all-before-vs-after-lemmas)
         (fn-simp-is-fn-lemmas-fn-subst fnsr-lst)
         (fn-simp-is-fn-lemmas-used-names fnsr-lst not-norm-event-names)))
       (new-def-event-pre (if mut-rec-p
                              (cons 'mutual-recursion new-defun-pre-lst)
                            (car new-defun-pre-lst)))
       (new-def-event-installed ; see comment below, where this is used
        (if mut-rec-p           ; (consp new-defun-installed-lst)
            (cons 'mutual-recursion new-defun-installed-lst)
          (car new-defun-installed-lst)))
       (new-def-event-show

; We could probably bind this to nil if the verbose option is nil.  But that is
; probably rare, so we'll keep it simple; there's very little consing or
; computation involved anyhow.

        (if mut-rec-p ; (consp new-defun-show-lst)
            (cons 'mutual-recursion new-defun-show-lst)
          (car new-defun-show-lst)))
       (hyps-preserved-thm-names
        (hyps-preserved-thm-name-lst fn-hyps-names-alist wrld))
       (fn-hyps-alist (fn-hyps-alist fnsr-lst wrld))
       (hyps-preserved-thm-list
        (if (eq (car clique) fnc)
            (hyps-preserved-thm-list clique fnsr-lst assumptions**
                                     hints-lst
                                     fn-hyps-alist
                                     fn-hyps-def-lst
                                     verbose wrld ctx)
          (and assumptions**
               `((acl2::identity-macro ; avoid "unexpected failure" message
                  (make-event
                   (let ((thms (hyps-preserved-thm-list
                                ',clique ',fnsr-lst ',assumptions**
                                ',hints-lst
                                ',fn-hyps-alist
                                ',fn-hyps-def-lst
                                ',verbose
                                (w state)
                                ',ctx)))
                     (value (cond ((null thms)
                                   '(value-triple :invisible))
                                  ((null (cdr thms))
                                   (car thms))
                                  (t (cons 'progn thms)))))))))))
       (events
        `((logic)
          (set-inhibit-warnings "theory")
          (set-ignore-ok t)
          (set-irrelevant-formals-ok t)
          ,@(and (cdr clique) ; allow any body to simplify to non-recursive
                 '((set-bogus-mutual-recursion-ok t)))
          ,@local-install-not-normalized-lst
          (local
           (progn
             ,@(remove-nils fn-hyps-def-lst)
             ,@runes-def-lst
             (on-failure
              ,new-def-event-pre
              :ctx ,ctx
              :erp :condition-failed
              :val nil
              :msg ,(msg "The following event has failed:~|~%~x0.~|~%The ~
                          reason for the failure may become apparent if you ~
                          call simplify again with the option, :print :info.  ~
                          In general, see :DOC apt::simplify-failure for some ~
                          ways to address failures."
                         new-def-event-pre))
             (encapsulate
               ()
               ,(simplify-defun-heuristics nil)
               (local (set-default-hints nil))
               (local (set-override-hints nil))
               ,@all-before-vs-after-lemmas)
             ,@hyps-preserved-thm-list
             (install-not-normalized$ ,(access fnsr fnsr :simp) :allp t)
             ,(copy-def+-event
               fnc
               (if (cdr clique)
                   fn-hyps-names-alist
                 (cdar fn-hyps-names-alist))
               hyps-preserved-thm-names
               (if (cdr clique)
                   (pairlis$ clique equiv**)
                 (car equiv**))
               fnc-recursivep orig ctx)
             ,@fn-simp-is-fn-lemma-lst-with-hints))

; The events just below are a bit contorted because of the need to lay down
; new-def-event-installed, which includes :hints and :guard-hints even though
; (1) normally there is no reason to include such if they are not needed in
; order to admit functions, but (2) it seems that the transformation
; finite-difference (and perhaps others) picks these up and uses them in
; generated definitions.  Before we added a separate verify-guards, which
; removed :guard-hints from simplify-defun's first definition of the
; new-function, the next three lines were not present and ,new-def-event-pre
; above was not local.  We can probably return to those simpler days in the
; future if other transformations no longer pick up old declare forms.

          ,@(map-local fn-simp-is-fn-lst)
          ,@(map-local (remove-eq nil verify-guards-form?-lst))
          ,new-def-event-installed
          ,@(remove-final-hints-lst fn-simp-is-fn-lst)))
       (state
        (cond (verbose
               (fms "Proposed simplified definition~#0~[~/s~]:~|~x1~%"
                    (list (cons #\0 new-defun-show-lst)
                          (cons #\1 new-def-event-show))
                    (standard-co state) state nil))
              (t state))))
    (value `(encapsulate-report-errors ,ctx () ,@events))))

#!acl2
(defun with-simplify-setup-fn (form)

; See with-simplify-setup.

  `(b* ((wrld (w state))
        (too-many-ifs-pre-rewrite-old
         (cdr (attachment-pair 'too-many-ifs-pre-rewrite wrld)))
        (too-many-ifs-post-rewrite-old
         (cdr (attachment-pair 'too-many-ifs-post-rewrite wrld)))
        (assume-true-false-aggressive-p-old
         (cdr (attachment-pair 'assume-true-false-aggressive-p wrld)))
        (rewrite-if-avoid-swap-old
         (cdr (attachment-pair 'rewrite-if-avoid-swap wrld)))
        ((er -)
         (trans-eval-error-triple (apt::simplify-defun-heuristics nil)
                                  ctx state))
        ((er form)
         (check-vars-not-free (too-many-ifs-pre-rewrite-old
                               too-many-ifs-post-rewrite-old
                               assume-true-false-aggressive-p-old
                               rewrite-if-avoid-swap-old)
                              ,form))
        ((er -)
         (trans-eval-error-triple
          (apt::simplify-defun-heuristics
           `((too-many-ifs-pre-rewrite . ,too-many-ifs-pre-rewrite-old)
             (too-many-ifs-post-rewrite . ,too-many-ifs-post-rewrite-old)
             (assume-true-false-aggressive-p
              . ,assume-true-false-aggressive-p-old)
             (rewrite-if-avoid-swap . ,rewrite-if-avoid-swap-old)))
          ctx state)))
     (value form)))

#!acl2
(defmacro with-simplify-setup (form)

; This macro assumes that CTX and STATE are bound.

  (with-simplify-setup-fn form))

; We move to the "ACL2" package in the following definition because it seems
; awkward to stay in the "APT" package, apparently because bind-** creates
; symbols in the "ACL2" package regardless.
#!acl2
(defun apt::simplify-defun-event (fn assumptions hyp-fn
                                     theory enable disable
                                     equiv expand
                                     hints
                                     thm-name new-name
                                     thm-enable new-enable
                                     simplify-body
                                     simplify-guard guard-hints
                                     verify-guards
                                     simplify-measure
                                     measure-hints measure
                                     untranslate must-simplify non-executable
                                     verbose ctx state)

; Warning: This function executes defattach events that change the world!
; Thus, this function is intended for use only during make-event expansion,
; revert-world, or other suitable protection of the world in case of error.

; Warning: Keep the argument list above in sync with the bind-** call below.

  (with-simplify-setup
   (b* ((wrld (w state))
        ((er clique) ; always non-nil
         (cond ((and (function-namep fn wrld)
                     (definedp fn wrld))
                (value (or (recursivep fn nil wrld)
                           (list fn))))
               (t (er-soft+ ctx :bad-input nil

; Function simplify-event in simplify.lisp already does a check that should
; prevent us from getting here.  So if someone we get here, we'll report a
; failure of simplify-defun, not of simplify.

                    "The first argument to simplify-defun must be a defined ~
                     function symbol, but ~x0 is not."
                    fn))))
        ((er -)
         (let ((bad (and (cdr clique)
                         (append (and (symbolp new-name)
                                      (not (member-eq new-name '(nil :auto)))
                                      (list (cons :new-name new-name)))
                                 (and (symbolp thm-name)
                                      (not (member-eq thm-name '(nil :auto)))
                                      (list (cons :thm-name thm-name)))))))
           (cond (bad
                  (er-soft+ ctx :bad-input nil
                    "The keyword option~#0~[ ~@1 is~/s ~@1 are~] illegal.  ~
                     Since the given function, ~x2, was defined with ~
                     mutual-recursion, ~#0~[this keyword~/each of these ~
                     keywords~] needs to be omitted (or given the default of ~
                     nil or :AUTO) or to be given a :MAP value."
                    (if (cdr bad) 1 0)
                    (if (cdr bad)
                        (msg "~x0 ~x1 and ~x2 ~x3"
                             (car (car bad)) (cdr (car bad))
                             (car (cadr bad)) (cdr (cadr bad)))
                      (msg "~x0 ~x1" (car (car bad)) (cdr (car bad))))
                    fn))
                 (t (value nil))))))
     (bind-**

; Warning: Keep the argument list below in sync with the list of formals above,
; but with verbose, ctx, and state omitted below.

      (assumptions
       hyp-fn
       theory enable disable
       equiv expand
       hints
       thm-name new-name
       thm-enable new-enable
       simplify-body
       simplify-guard guard-hints
       (verify-guards)
       simplify-measure measure-hints measure
       untranslate must-simplify
       (non-executable))
      (b* ((assumptions** (apt::fix-assumptions** hyp-fn** assumptions**))
           ((er form)
            (apt::simplify-defun-form
             clique
             (and (cdr clique)
                  (if assumptions :assumptions t)) ; mut-rec-p
             assumptions** hyp-fn**
             theory** enable** disable**
             equiv** expand**
             hints**
             thm-name** new-name**
             thm-enable** new-enable**
             simplify-body**
             simplify-guard** guard-hints**
             verify-guards ; not legal for :map construct
             simplify-measure**
             measure-hints** measure**
             untranslate** must-simplify**
             non-executable ; not legal for :map construct
             verbose ctx state)))
        (value form))))))
