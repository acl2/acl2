; Copyright (C) 2015, Regents of the University of Texas
; Written by Matt Kaufmann (with inspiration from Alessandro Coglio and Eric Smith)
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; TODO and FIXME items to consider doing:
; - Consider adding missing arguments (:skip-termination, :skip-guard-proof,
;   :rewrite-assumptions, :measure).
; - Perhaps convert this file to guard-verified :logic mode.
; - Add more error checking, e.g.: avoid Lisp error when quoting first
;   argument as in (simplify-defun 'foo) instead of (simplify-defun foo).
; - Provide a general way to specify hints, not just in-theory hints.
; - Probably change defaults for simplify-guard and simplify-measure to 't
;   (after everything is working).
; - If measure is not simplified, perhaps get it, untranslated, from the
;   original definition (so that macros are still present).
; - Add guards to simplify-defun and show-simplify-defun and maybe use
;   set-guard-msg to make nice error messages for guard violations.
; - Search for "TODO" and "FIXME" below.
; - Reconcile handling of :verify-guards with respect to eagerness and default
;   value, with how that's taken into account in simplify-defun-sk.

(in-package "ACL2")

;;; TABLE OF CONTENTS
;;; -----------------
;;; Functions record (fnsr) structures
;;; Dealing with patterns (including @-vars and _-vars)
;;; Generating names and lists containing names
;;; Argument processing
;;; Miscellaneous utilities
;;; Main implementation code

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Included books
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Inclusion of this book can affect the current-theory, because of the
; sub-books included just below, which also introduce congruence runes that can
; have an effect on the simplify-defun process (search for "congruence" in
; simplify-defun-tests.lisp to see an example involving list-equiv).  So far
; I've done nothing about this, because could be tricky to fix without causing
; other problems.  For example, we could insert (deflabel
; start-of-simplify-defun) here and insert (in-theory (current-theory
; start-of-simplify-defun)) at the end of this book.  But then if someone tries
; to get rules from an included book after including simplify-defun, e.g., from
; community book books/std/lists/list-defuns.lisp (included via a sequence of
; included books under transformations/utilities.lisp), that included book
; ("list-defuns") would be redundant and hence its rules would remain disabled.

; (include-book "names") ; for increment-name-suffix-safe
(include-book "kestrel/utilities/system/numbered-names" :dir :system)
; (include-book "../utilities/runes") ; for drop-fake-runes
(include-book "runes") ; for drop-fake-runes
;(include-book "utilities") ; drop?
(include-book "kestrel/utilities/user-interface" :dir :system) ; for control-screen-output
(include-book "kestrel/utilities/defmacroq" :dir :system)
(include-book "misc/expander" :dir :system)
(include-book "misc/install-not-normalized" :dir :system)
(include-book "kestrel/utilities/system/world-queries" :dir :system)
(include-book "directed-untranslate")
(include-book "kestrel/utilities/copy-def" :dir :system) ; includes tools/flag
; (include-book "utilities/process-keyword-args")
; (include-book "utilities/pattern-matching")
(include-book "process-keyword-args")
(include-book "pattern-matching")
(include-book "transformation-table")

(program)
(set-state-ok t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Functions record (fnsr) structures
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrec fnsr ; prounounced "funzer": functions record

; We are given a function symbol, :orig, and we wish to define a new function,
; :simp.  The :copy and :ncopy fields are either :orig and :simp or vice-versa.
; Our approach works requires that if either :orig or :simp is defined
; recursively, then :copy is defined recursively.

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
; on perfect tracking of runesx, which we know is not the case because of
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

(defun fn-hyps-name (fn)
  (intern$ (concatenate 'string (symbol-name fn) "-HYPS")
           (symbol-package-name-non-cl fn)))

(defun hyps-preserved-thm-name (fn hyps-fn)
  (declare (xargs :guard (and (symbolp fn)
                              (symbolp hyps-fn)
                              fn
                              hyps-fn)
                  :mode :logic))
  (intern$ (concatenate 'string
                        (symbol-name hyps-fn)
                        "-PRESERVED-FOR-"
                        (symbol-name fn))
           (symbol-package-name-non-cl hyps-fn)))

(defun hyps-preserved-thm-name-lst (fn-hyps-alist)
  (cond ((endp fn-hyps-alist) nil)
        (t (cons (hyps-preserved-thm-name (caar fn-hyps-alist)
                                          (cdar fn-hyps-alist))
                 (hyps-preserved-thm-name-lst (cdr fn-hyps-alist))))))

(defun fn-simp-name (fn new-name state)

; When I first found increment-name-suffix-safe (which is a rather complicated
; definition), I hoped to avoid it, since I was calling fn-simp-name from
; functions that don't take state.  What's more, new-namep is a good (built-in)
; predicate to use for checking whether a name is used, better perhaps than
; using symbol-has-propsp (which is used by increment-name-suffix-safe); note
; that it's easy to make new-namep guard-verified by adding the obvious guard
; of (and (symbolp name) (plist-worldp wrld)).  I'm also a bit concerned about
; symbols in the Common Lisp package (see symbol-package-name-non-cl aove),
; though maybe I shouldn't be.  HOWEVER, for now I'll just use
; increment-name-suffix-safe in order to keep this file simple and to help with
; compatibility with the old simplify-body.

  (or new-name
      (next-numbered-name fn (w state))))

(defun fn-runes-name (fn)
  (intern$ (concatenate 'string "*" (symbol-name fn) "-RUNES*")
           (symbol-package-name-non-cl fn)))

(defunsr before-vs-after-name (fnsr index)
  (add-suffix fnnc
              (concatenate 'string
                           "-BEFORE-VS-AFTER-"
                           (coerce (explode-nonnegative-integer index 10 nil)
                                   'string))))

(defun fn-simp-is-fn-name (fn fn-simp theorem-name)
  (or theorem-name
      (intern-in-package-of-symbol
       (concatenate 'string (symbol-name fn) "-BECOMES-" (symbol-name fn-simp))
       fn-simp)))

(defun fn-simp-is-fn-lemma-name (fn fn-simp theorem-name)
  (add-suffix (fn-simp-is-fn-name fn fn-simp theorem-name)
              "-LEMMA"))

(defun fn-hyps-alist (fnsr-lst)
  (cond ((endp fnsr-lst) nil)
        (t (let* ((fnsr (car fnsr-lst))
                  (fn (access fnsr fnsr :orig))
                  (fnc (access fnsr fnsr :copy)))
             (acons fnc
                    (fn-hyps-name fn)
                    (fn-hyps-alist (cdr fnsr-lst)))))))

(defun fn-simp-is-fn-lemmas-used-names (fnsr-lst)
  (cond
   ((endp fnsr-lst) nil)
   (t (cons (let* ((fnsr (car fnsr-lst))
                   (fn (access fnsr fnsr :orig))
                   (fnnc (access fnsr fnsr :ncopy)))
              (if (eq fn fnnc)
                  (install-not-normalized-name fn)
                fnnc))
            (fn-simp-is-fn-lemmas-used-names (cdr fnsr-lst))))))

(defun access-fnsr-copy-lst (fnsr-lst)
  (cond ((endp fnsr-lst) nil)
        (t (cons (access fnsr (car fnsr-lst) :copy)
                 (access-fnsr-copy-lst (cdr fnsr-lst))))))

(defun fn-simp-alist (clique new-name** state)
  (cond ((endp clique) nil)
        (t (acons (car clique)
                  (fn-simp-name (car clique) (car new-name**) state)
                  (fn-simp-alist (cdr clique) (cdr new-name**) state)))))

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

  (cond ((and (all-nils assumptions**)
              (all-nils assumptions**))
         assumptions**)
        (t (fix-assumptions**-1 hyp-fn** assumptions**))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Miscellaneous utilities
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun theory+expand-to-hints (theory expand old-fn assumptions-guard-p wrld)
  (let* ((expand-hint
          (and expand ; else there's nothing to expand
               `(:expand (,@expand)))))
    (and (or (not (eq theory :none))
             expand-hint
             assumptions-guard-p)
         `(("Goal"
            ,@(and (not (eq theory :none))
                   `(:in-theory ,theory))
            ,@expand-hint
            ,@(and assumptions-guard-p
                   (eq (symbol-class old-fn wrld)
                       :common-lisp-compliant)
                   `(:use (:guard-theorem ,old-fn))))))))

(defun equiv-from-geneqv-1 (geneqv args)
  (cond ((endp geneqv) nil)
        (t (cons (fcons-term (access congruence-rule (car geneqv) :equiv)
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

(defun fn-ubody (fn fn-body wrld)

; Return a body of fn, preferably an untranslated body, else an unnormalized
; body.  Fn-body may be nil; otherwise it is an unnormalized body of fn in
; wrld, (body fn nil wrld).

  (let* ((ev (get-event fn wrld))
         (def-body
           (and (consp ev)
                (case (car ev)
                  (defun (car (last ev)))
                  (mutual-recursion
                   (car (last (cdr (assoc-eq fn (strip-cdrs (cdr ev)))))))
                  (& nil)))))
    (or def-body
        fn-body
        (body fn nil wrld))))

(defun clique-runic-designators (clique)
  (cond ((endp clique) nil)
        (t (append (let ((fn (car clique)))
                     `(,fn (:e ,fn) (:t ,fn)))
                   (clique-runic-designators (cdr clique))))))

; The following function has been moved here from
; [books]/kestrel/utilities/user-interface.lisp, because it is an obsolete user
; interface utility that is only used in this simplify-defun.lisp file.
(define control-screen-output-and-maybe-replay
  ((verbose "@('t') (or @(''t')) or @('nil') (or @(''nil')), else indicates
             replay on failure.")
   (event-p "Make an event when true.")
   (form (pseudo-event-formp form)))
  :returns (new-form pseudo-event-formp :hyp (pseudo-event-formp form))
  :short "Variant of @(tsee control-screen-output)
          that can replay a failure verbosely."
  :long
  "<p>Usage:</p>

   @({
   (control-screen-output-and-maybe-replay verbose event-p form)
   })

   <p>where @('verbose') is not evaluated.</p>

   <p>If @('verbose') is @('t'), @(''t'), @('nil'), or @(''nil'), this is just
   @(tsee control-screen-output), and @(':event-p') is ignored.  So suppose
   otherwise for the rest of this documentation.</p>

   <p>In that case, @('(control-screen-output nil form)') is evaluated, and
   then if evaluation fails, @('(control-screen-output t form)') is
   subsequently evaluated so that the failure can be seen with more output.
   Moreover, the value of @(':event-p') is relevant, with the following two
   cases.</p>

   <ul>

   <li>For @(':event-p t'), the call of
   @('control-screen-output-and-maybe-replay') can go into a book, but @('form')
   must be a legal event form (see @(see embedded-event-form)).</li>

   <li>For @(':event-p nil'), the call of
   @('control-screen-output-and-maybe-replay') cannot go into a book, but
   @('form') need not be a legal event form.</li>

   </ul>"

  (let ((verbose (maybe-unquote verbose)))
    (cond ((booleanp verbose)
           (control-screen-output verbose form))
          (t
           (let ((form-nil (control-screen-output nil form))
                 (form-t (control-screen-output t form)))
             (cond
              (event-p
               `(make-event
                 '(:or ,form-nil
                       (with-output
                         :off :all
                         :on error
                         :stack :push
                         (progn
                           (value-triple (cw "~%===== VERBOSE REPLAY: =====~|"))
                           (with-output :stack :pop ,form-t))))))
              (t `(mv-let (erp val state)
                    ,form-nil
                    (cond (erp (prog2$ (cw "~%===== VERBOSE REPLAY: =====~|")
                                       ,form-t))
                          (t (value val)))))))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Main implementation code
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun fn-hyps-def (fn fn-hyps hyps wrld)
  (assert$
   (and fn-hyps hyps hyps) ; else don't call this function
   (let ((fn-formals (formals fn wrld)))
     `(defun ,fn-hyps ,fn-formals
        ,(conjoin-untranslated-terms hyps)))))

(defun hyps-preserved-thm-1 (fn-hyps-call tests-and-calls-lst fn-hyps-alist
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
   (t (hyps-preserved-thm-1
       fn-hyps-call (cdr tests-and-calls-lst) fn-hyps-alist wrld
       (let ((tests (access tests-and-calls
                            (car tests-and-calls-lst)
                            :tests))
             (calls (access tests-and-calls
                            (car tests-and-calls-lst)
                            :calls)))
         (if calls
             (cons (make-implication (cons fn-hyps-call tests)
                                     (conjoin (sublis-fn-lst-simple
                                               fn-hyps-alist
                                               calls)))
                   acc)
           acc))))))

(defun hyps-preserved-thm (fn fn-hyps hyps-preserved-theory
                              assumptions-guard-p fn-hyps-alist expand-lst
                              induction-machine wrld)

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
            (hints-from-theory
             (theory+expand-to-hints hyps-preserved-theory
                                     expand-lst
                                     fn
                                     assumptions-guard-p wrld)))
       `(defthm ,(hyps-preserved-thm-name fn fn-hyps)
          ,(hyps-preserved-thm-1
            (fcons-term fn-hyps formals)
            induction-machine
            fn-hyps-alist
            wrld
            nil)
          ,@(and hints-from-theory
                 `(:hints ,hints-from-theory))
          :rule-classes nil))))))

(defun simplify-hyp-list (hyps theory expand ctx state)

; Returns (mv erp _ state) or (mv nil simplified-hyps state).

  (assert$
   hyps ; else don't call this function
   (let ((wrld (w state)))
     (er-let* ((thyps (translate-term-lst hyps
                                          t ; stobjs-out
                                          t ; logic-modep
                                          t ; known-stobjs-lst
                                          ctx wrld state))
               (tmp ; (list* runes (list rewritten-hyp-list) assumptions)
                (with-guard-checking-error-triple
                 nil ; as in prover
                 (simplify-hyps ; defined using tool2-fn in misc/expander.lisp
                  thyps
                  nil ; rewritten-previous-hyps-rev
                  nil ; runes
                  nil ; assns (from forcing, I think)
                  nil ; equiv
                  state
                  (theory+expand-to-hints theory expand nil nil nil)
                  t  ; prove-assumptions
                  t  ; inhibit-output
                  nil ; print-flg
                  nil ; must-rewrite-flg
                  'simplify-hyp-list
                  ))))
       (let ((runes (drop-fake-runes (car tmp)))
             (simplified-hyps (assert$ (null (cdr (cadr tmp))) ; singleton check
                                       (flatten-ands-in-lit-lst (car (cadr tmp)))))
             (assns (cddr tmp)))
         (cond (assns (er soft ctx
                          "Assumptions were generated by forcing (handling ~
                           them is not yet implemented)."))
               (t (value (cons runes simplified-hyps)))))))))

(defconst *must-simplify-keywords*
; Keep this in sync with the default value in (show-)simplify-defun.
  '(:body :measure :guard))

(defun check-must-simplify (x)
  (or (eq x t)
      (eq x nil)
      (and (keyword-value-listp x)
           (null (strip-keyword-list *must-simplify-keywords* x)))))

(defun get-must-simplify (kwd x)
  (declare (xargs :guard (and (check-must-simplify x)
                              (member-eq kwd *must-simplify-keywords*))))
  (cond ((symbolp x) x) ; x is t or nil
        (t (cadr (assoc-keyword kwd x)))))

(defun simplify-defun-term (term hyps g?equiv hints-from-theory+expand must-rewrite
                                 state)

; Warning: A more natural name might be simplify-term, but that name is already
; used in axe/axe.lisp.

; G?equiv is either a geneqv or else a symbol that represents an equivalence
; relation (where nil represents equal).

; Term is a translated term, hyps is a list of translated terms, and
; hints-from-theory+expand is either nil or what you'd expect to find after
; :hints in a defthm, e.g., (("Goal" :use foo)).  This function returns an
; error triple (mv erp val state), where if erp is nil then val is (list
; true-runes rewritten-term).

  (er-let* ((runes/new-term
             (with-guard-checking-error-triple
              nil ; as in prover
              (tool2-fn term
                        hyps
                        g?equiv
                        state
                        hints-from-theory+expand
                        t   ; prove-assumptions
                        t   ; inhibit-output
                        nil ; translate-flg
                        nil ; print-flg
                        must-rewrite
                        'simplify-defun-term
                        ))))
    (value (cons (drop-fake-runes (car runes/new-term))
                 (cadr runes/new-term)))))

(defrec fn-simp-body-result
  ((runes . body)
   (equalities . fnsr)
   . recursivep)
  nil)

(defun fn-simp-body-rec (body simp-hyps theory expand
                              hints-from-theory+expand
                              address-subterm-governors-lst
                              geneqv must-simplify
                              ctx state
                              runes subterm-equalities)

; See fn-simp-body.  Here we recur, simplifying at each indicated subterm.  The
; subterms aren't nested, so it's reasonable to modify body as we recur.

; TODO: Sublis-fn-simple, called below, uses cons-term; but perhaps fcons-term
; would be better.

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
    (let* ((wrld (w state))
           (address-subterm-governors (car address-subterm-governors-lst))
           (subterm (cadr address-subterm-governors))
           (geneqv-subterm
            (geneqv-at-subterm body
                               (car address-subterm-governors)
                               geneqv
                               nil ; pequiv-info
                               (ens state)
                               wrld))
           (equiv-at-subterm (equiv-from-geneqv geneqv-subterm))
           (governors (cddr address-subterm-governors)))
      (er-let* ((runes/simp-governors
                 (if governors

; The following may be a bit heavy-handed, but it makes convenient use of
; existing utilities to do something reasonably powerful.  We have seen an
; example where if we just use governors here, we don't get what we want.
; The example has this

;   :simplify-body
;   (if (or (not expr1)
;           expr2)
;       outputs
;     @)

; and gives us a single hypothesis of the form (not (if ...)), while the
; present code instead gives the expected list of 9 terms (note that expr1
; calls a function that is is defined to be a rather large conjunction),
; implicitly conjoined.

                     (simplify-hyp-list
                      (flatten-ands-in-lit
                       (termify-clause-set
                        (clausify (conjoin governors) nil t (sr-limit wrld))))
                      theory expand ctx state)
                   (value nil)))
                (runes/new-subterm
                 (simplify-defun-term subterm
                                      (append? simp-hyps
                                               (cdr runes/simp-governors))
                                      geneqv-subterm hints-from-theory+expand
                                      (get-must-simplify :body must-simplify)
                                      state)))
        (let* ((runes (union-equal (car runes/simp-governors)
                                   (union-equal (car runes/new-subterm)
                                                runes)))
               (new-subterm (cdr runes/new-subterm))
               (subterm-equality
                (if (equal subterm new-subterm)
                    *t* ; special marker indicating no before-vs-after lemma
                  `(,equiv-at-subterm ,subterm ,new-subterm)))
               (new-body (fdeposit-term body
                                        (car address-subterm-governors)
                                        new-subterm)))
          (fn-simp-body-rec new-body simp-hyps theory expand
                            hints-from-theory+expand
                            (cdr address-subterm-governors-lst)
                            geneqv must-simplify
                            ctx state
                            runes
                            (cons subterm-equality subterm-equalities))))))))

(defun fn-simp-body (fn fn-simp mut-rec-p
                        simplify-body body simp-hyps theory expand
                        hints-from-theory+expand
                        address-subterm-governors-lst
                        geneqv must-simplify fn-simp-alist ctx wrld state)

; We return an error triple such that, in the non-error case, the value is a
; fn-simp-body-result record.  The :equalities field of that record is a list
; of calls of a equivalence relations, where that list is nil if simplify-body
; is nil.

; TODO: Sublis-fn-simple, called below, uses cons-term; but perhaps fcons-term
; would be better.

  (cond
   ((null simplify-body)
    (let ((recursivep (recursivep fn nil wrld)))
      (value (make fn-simp-body-result
                   :runes nil
                   :body (sublis-fn-simple fn-simp-alist body)
                   :equalities nil
                   :fnsr (make-fnsr fn fn-simp
                                    (and (not mut-rec-p) recursivep)
                                    simp-hyps wrld)
                   :recursivep recursivep))))
   (t
    (er-let* ((result (fn-simp-body-rec body simp-hyps theory expand
                                        hints-from-theory+expand
                                        address-subterm-governors-lst geneqv
                                        must-simplify
                                        ctx state
                                        nil nil)))
      (let* ((new-body (sublis-fn-simple fn-simp-alist
                                         (access fn-simp-body-result result
                                                 :body)))
             (recursivep (ffnnamep fn-simp new-body))
             (fnsr (make-fnsr fn fn-simp
                              (and (not mut-rec-p) recursivep)
                              simp-hyps wrld))
             (fnc (access fnsr fnsr :copy))
             (equalities (access fn-simp-body-result result :equalities)))
        (value (change fn-simp-body-result result ; :runes is unchanged
                       :body new-body
                       :equalities (if (eq fn fnc)
                                       (sublis-fn-lst-simple fn-simp-alist
                                                             equalities)
                                     equalities)
                       :fnsr fnsr
                       :recursivep recursivep)))))))

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
                                    index)
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
                            (1+ index)))
   (t
    (let ((s-cmd
           `(:then (:succeed
                    (:s :repeat 3 ; default for (expander-repeat-limit state)
                        :backchain-limit 500 ; from rewrite*
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
        `(defthm ,(before-vs-after-name fnsr index)
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
            :s-prop)
;          :hints (("Goal" :in-theory ,fn-runes :expand ,expand))
           :rule-classes nil)
        (before-vs-after-lemmas fnsr hyps fn-hyps-name
                                formals
                                (cdr governors-lst)
                                (cdr subterm-equalities)
                                fn-runes
                                expand
                                (1+ index))))))))

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

; Modified from simplify-term-with-tool2 as defined in
; kestrel-acl2/transformations/simplify-body.lisp:
(defun fn-simp-defs (fn fn-simp mut-rec-p hyps theory equiv expand
                        function-disabled
                        simplify-body
                        simplify-guard guard-hints guard-hints-p verify-guards
                        simplify-measure measure-hints measure
                        untranslate must-simplify non-executable
                        fn-simp-alist
                        verbose ctx state)

; This function returns an error triple whose value component (in the case of
; error component nil) is (list fnsr defun-form defconst-form hints?), where
; fnsr is a functions record (see make-fnsr), defun-form defines the new
; function, defconst-form defines a constant containing the runes used in the
; simplification, and hints? is either nil or a local in-theory hint based on
; the input theory.

; Note that measure has already gone through a bit of checking in
; simplify-defun-fn.

  (b* ((wrld (w state))
       (formals (formals fn wrld))
       (fn-runes (fn-runes-name fn))
       (guard-verified-p (eq (symbol-class fn wrld)
                             :common-lisp-compliant))
       (old-recursivep (getprop fn 'recursivep nil 'current-acl2-world wrld))
       (hints-from-theory+expand (theory+expand-to-hints theory expand
                                                         nil nil nil))
       (computed-hint-lst (and (not (eq theory :none))
                               `((quote (:in-theory ,theory)))))
       (fn-body (body fn nil wrld))
       (fn-ubody (fn-ubody fn fn-body wrld))
       ((er runes-hyps/simp-hyps)
        (if hyps
            (simplify-hyp-list hyps theory expand ctx state)
          (value nil)))
       (runes-hyps (car runes-hyps/simp-hyps))
       (simp-hyps (cdr runes-hyps/simp-hyps))
       (state (cond ((or (not verbose)
                         (null simplify-body)
                         (null hyps)
                         (equal hyps '(t)))
                     state)
                    (t (fms "Simplified :ASSUMPTIONS~@0:~|~y1"
                            (list (cons #\0 (if mut-rec-p
                                                (msg " for function ~x0"
                                                     fn)
                                              ""))
                                  (cons #\1
                                        (untranslate-lst simp-hyps t wrld)))
                            (standard-co state) state nil))))
       (fn-guard (guard fn nil wrld))
       (fn-ruler-extenders
        (let ((just (getpropc fn 'justification nil wrld)))
          (and just
               (let ((tmp (access justification just
                                  :ruler-extenders)))
                 (and (not (equal tmp (default-ruler-extenders wrld)))
                      tmp)))))
       ((er address-subterm-governors-lst)
        (if (not (booleanp simplify-body)) ; then non-nil value (or, error)
            (address-subterm-governors-lst-state
             simplify-body fn-body ctx state)
          (value (list (list* nil fn-body nil)))))
       (governors-lst (strip-cddrs address-subterm-governors-lst))
       ((er body-result)
        (fn-simp-body fn fn-simp mut-rec-p
                      simplify-body fn-body simp-hyps
                      theory expand hints-from-theory+expand
                      address-subterm-governors-lst
                      (geneqv-from-g?equiv equiv wrld)
                      (get-must-simplify :body must-simplify)
                      fn-simp-alist
                      ctx wrld state))
       (fnsr (access fn-simp-body-result body-result :fnsr))
       (new-body (access fn-simp-body-result body-result :body))
       (new-recursivep (access fn-simp-body-result body-result :recursivep))
       ((er guard-result)
        (if simplify-guard
            (simplify-defun-term
             fn-guard
             nil ; hyps might be guard itself
             'iff hints-from-theory+expand
             (get-must-simplify :guard must-simplify)
             state)
          (value (cons nil fn-guard))))
       ((er measure-result)
        (if (and measure simplify-measure)
            (simplify-defun-term
             measure
             nil ; hyps might be guard itself
             nil hints-from-theory+expand
             (get-must-simplify :measure must-simplify)
             state)
          (value (cons nil measure))))
       (simp-body (cond
                   ((eq untranslate t)
                    (untranslate new-body nil wrld))
                   ((eq untranslate nil)
                    new-body)

; Otherwise untranslate is :nice, but we give special treatment for defun-nx
; (and defund-nx), to eliminate an extra prog2$ (added 6/5/2017 to accommodate
; a change in directed-untranslate).

                   ((and non-executable
                         (eq (car fn-ubody) ; always true?
                             'prog2$)
                         (let ((x (directed-untranslate fn-ubody fn-body
                                                        new-body nil nil
                                                        wrld)))
                           (and (eq (car x) 'prog2$) ; always true?
                                (car (last x))))))
                   (t
                    (directed-untranslate fn-ubody fn-body new-body nil nil
                                          wrld))))
       ((er -)
        (cond ((and simplify-body
                    (equal simp-body fn-ubody))
               (cond ((equal fn-body new-body)

; Probably this case can't happen, because tool2 would cause an error.  But we
; code it up in case that changes.

                      (er soft ctx
                          "No simplification has taken place. ~
                                         Use :simplify-body nil if you want ~
                                         that to be allowed."))
                     (t
                      (er soft ctx
                          "Although simplification has taken ~
                                         place, the resulting definition has ~
                                         the same body after converting to ~
                                         user-level syntax ~
                                         (\"untranslating\").  Use ~
                                         :simplify-body nil to avoid this ~
                                         error."))))
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
        (untranslate (cdr guard-result) nil wrld))
       (simp-measure
        (and measure-result
             (untranslate (cdr measure-result) nil wrld)))
       (runes0 (union$ (access fn-simp-body-result body-result :runes)
                       (car guard-result)         ; possibly nil
                       (car measure-result)       ; possibly nil
                       runes-hyps
                       :test 'equal))
       (runes (if hyps
                  (add-to-set-equal `(:definition ,(fn-hyps-name fn))
                                    runes0)
                runes0))
       (defun? (if non-executable
                   (if function-disabled 'defund-nx 'defun-nx)
                 (if function-disabled 'defund 'defun))))
    (value ; (defun defconst &optional in-theory)
     `(,fnsr
       (,defun? ,fn-simp ,formals
         (declare
          (xargs :normalize nil
                 ,@(and fn-ruler-extenders
                        `(:ruler-extenders ,fn-ruler-extenders))
                 :guard ,simp-guard
                 ,@(and simp-measure

; It is possible that the original definition is recursive but the simplified
; definition is not.

                        new-recursivep
                        `(:measure ,simp-measure))
                 ,@(cond
                    ((and guard-verified-p
                          (not (eq verify-guards nil)))
                     `(:verify-guards
                       t
                       ,@(if guard-hints-p
                             `(:guard-hints ,guard-hints)
                           (let ((compliant-p (eq (symbol-class fn wrld)
                                                  :common-lisp-compliant)))
                             (and (or compliant-p
                                      computed-hint-lst)
                                  `(:guard-hints
                                    (("Goal"
                                      ,@(and compliant-p
                                             `(:use (:guard-theorem ,fn))))
                                     ,@computed-hint-lst)))))))
                    (t
                     `(:verify-guards
                       ,(eq verify-guards t)
                       ,@(and (eq verify-guards t)
                              (if guard-hints-p
                                  `(:guard-hints ,guard-hints)
                                (let ((compliant-p
                                       (eq (symbol-class fn wrld)
                                           :common-lisp-compliant)))
                                  (and (or compliant-p
                                           computed-hint-lst)
                                       `(:guard-hints
                                         (("Goal"
                                           ,@(and compliant-p
                                                  `(:use
                                                    (:guard-theorem ,fn))))
                                          ,@computed-hint-lst)))))))))
                 ,@(and new-recursivep
                        `(:hints
                          ,(if (eq measure-hints :auto)
                               `(("Goal"
                                  ,@(and old-recursivep
                                         `(:use (:termination-theorem ,fn))))
                                 ,@computed-hint-lst)
                             measure-hints)))))
         ,simp-body)
       (make-event (let ((thy (union-equal
                               ',runes
                               (congruence-theory-fn :here (w state)))))
                     (list 'defconst ',fn-runes
                           (list 'quote thy))))
       ,@(and simplify-body

; It is useful to break out this lemma, which is about the subterm that is
; being simplified rather than (in the case that :simplify-body is a pattern)
; the entire body.  For example, the form (simplify-defun outputs$6 ...) in
; MUSE/derivations/bresenham/Experiments/derivation.lisp was failing until we
; added this subterm-level lemma for simplify-defun.

              (before-vs-after-lemmas fnsr hyps (fn-hyps-name fn)
                                      formals governors-lst
                                      subterm-equalities fn-runes expand
                                      0))))))

(defunsr fn-simp-is-fn-lemma (fnsr fn-hyps theorem-name theorem-disabled equiv
                                   wrld)
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
              (fn-simp-is-fn-name fn fn-simp theorem-name)
            (fn-simp-is-fn-lemma-name fn fn-simp theorem-name)))
         (hyps (and fn-hyps
                    (list (cons fn-hyps fn-formals))))
         (defthm? (if theorem-disabled 'defthmd 'defthm)))
    `(,defthm? ,lemma-name
       ,(implicate-untranslated-terms hyps equality))))

(defunsr fn-simp-is-fn (fnsr fn-hyps hyps theorem-name theorem-disabled equiv
                             wrld)
  (cond
   ((and (eq fn fnc) ; else order will be reversed
         (null fn-hyps) ; keep in sync with similar test in fn-simp-is-fn-lemma
         )
    (fn-simp-is-fn-lemma fnsr nil theorem-name theorem-disabled equiv wrld))
   (t (let* ((fn-formals (formals fn wrld))
             (fn-call (cons fn fn-formals))
             (fn-simp-call (cons fn-simp fn-formals))
             (equality `(,equiv ,fn-call ,fn-simp-call))
             (defthm? (if theorem-disabled 'defthmd 'defthm))
             (hyps (remove-equal t (remove-equal *t* hyps))))
        `(,defthm? ,(fn-simp-is-fn-name fn fn-simp theorem-name)
           ,(implicate-untranslated-terms hyps equality)
           :hints (("Goal"
                    :use ,(fn-simp-is-fn-lemma-name fn fn-simp theorem-name)
                    :in-theory ,(and fn-hyps `'(,fn-hyps)))))))))

(defun simplify-defun-theory (clique-runic-designators
                              theory enable disable ctx state)
  (cond
   ((not (or (eq theory :none)
             (and (eq enable :none)
                  (eq disable :none))))
    (er soft ctx
        "It is illegal to supply a value other than :none for both the ~
         :theory (or :hyps-preserved-theory) argument and the corresponding ~
         :enable or :disable argument."))
   (t (cond
       ((not (eq theory :none))
        (value theory))
       (t ; hence (eq theory :none)
        (let* ((enable (if (or (eq enable :none)
                               (consp enable)
                               (null enable))
                           enable ; else expect a non-nil symbol
                         (list enable)))
               (disable (if (eq disable :none)
                            clique-runic-designators
                          (append clique-runic-designators ; !! switch order?
                                  (if (or (consp disable)
                                          (null disable))
                                      disable ; else expect a non-nil symbol
                                    (list disable))))))
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

(defun simplify-defun-tuple (fn mut-rec-p clique-runic-designators
                                assumptions hyp-fn
                                theory enable disable
                                equiv expand
                                theorem-name new-name
                                theorem-disabled function-disabled
                                simplify-body
                                simplify-guard guard-hints guard-hints-p
                                verify-guards
                                simplify-measure
                                measure-hints measure
                                untranslate must-simplify non-executable
                                fn-simp-alist
                                verbose wrld ctx state)

; Actually returns (when not an error) the value (cons full-form defun-form),
; where full-form is the encapsulate to be evaluated and defun-form is the
; defun exported from that encapsulate.

  (b* ((rune (fn-rune-nume fn nil nil wrld))
       (function-disabled
        (if (eq function-disabled :auto)
            (and rune ; true if we've done enough error checking?
                 (not (enabled-runep rune (ens state) wrld)))
          function-disabled))
       (assumptions-guard-p (eq assumptions :guard))
       (hyps (cond (hyp-fn
                    (list (cons hyp-fn
                                (formals fn wrld))))
                   (assumptions-guard-p
                    (list (guard-raw fn wrld)))
                   (t assumptions)))
       (expand (fix-expand-hint expand))
       (fn-hyps (and hyps (fn-hyps-name fn)))
       (fn-hyps-def (and hyps (fn-hyps-def fn fn-hyps hyps wrld)))
       (fn-simp (fn-simp-name fn new-name state))
       ((when (not (member-eq untranslate '(t nil :nice))))
        (er soft ctx
            "The value of keyword :UNTRANSLATE for ~x0 must be ~v1.  The ~
             value ~x2 is thus illegal."
            'simplify-defun '(t nil :nice) untranslate))
       ((when (and hyp-fn assumptions))
        (er soft ctx
            "It is illegal for ~x0 to specify non-nil values for both :HYP-FN ~
             and :ASSUMPTIONS"
            'simplify-defun))
       ((when (not (check-must-simplify must-simplify)))
        (er soft ctx
            "The :MUST-SIMPLIFY argument must be T, NIL, or a ~
             keyword-value-listp for which each key is ~v0."
            *must-simplify-keywords*))
       ((when (not (and (symbolp equiv)
                        (equivalence-relationp equiv wrld))))
        (er soft ctx
            "The :equiv argument must be a known equivalence relation in the ~
             current ACL2 world, but ~x0 is not."
            equiv))
       ((er theory)
        (simplify-defun-theory clique-runic-designators theory enable disable ctx
                               state))
       ((er measure)
        (let ((measure-to-use
               (if (eq measure :auto)
                   (let ((just (getprop fn 'justification nil
                                        'current-acl2-world wrld)))
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
                  ((not (eq measure :auto)) ; user-supplied measure
                   (er soft ctx
                       "It is illegal to simplify a measure that             ~
                        a call of :?, such as ~x0."
                       fn measure-to-use))
                  (t
                   (er soft ctx
                       "It is illegal to simplify the DEFUN for ~x0 because ~
                        its measure, ~x1, is a call of :?."
                       fn measure-to-use))))
                (t (value measure-to-use)))))
       ((er non-executable)
        (case non-executable
          ((t nil) (value non-executable))
          (:auto (value (getpropc fn 'non-executablep nil wrld)))
          (otherwise (er soft ctx
                         "The value of :non-executable must be ~v0; thus ~x1 ~
                          is illegal."
                         '(t nil :auto)
                         non-executable))))
       ((er fn-simp-defs)
        (fn-simp-defs fn fn-simp mut-rec-p hyps theory equiv expand
                      function-disabled simplify-body simplify-guard
                      guard-hints guard-hints-p verify-guards simplify-measure
                      measure-hints measure untranslate must-simplify
                      non-executable fn-simp-alist verbose ctx state))
       (fnsr (car fn-simp-defs))
       (fnc (access fnsr fnsr :copy))
       (new-defun (cadr fn-simp-defs))  ; (defun foo$1 ...)
       (runes-def (caddr fn-simp-defs)) ; (defconst *foo-runes* ...)
       (before-vs-after-lemmas (cdddr fn-simp-defs))
       (fn-simp-is-fn-lemma (fn-simp-is-fn-lemma fnsr fn-hyps theorem-name
                                                 theorem-disabled equiv wrld))
       (fn-simp-is-fn (fn-simp-is-fn fnsr fn-hyps hyps theorem-name
                                     theorem-disabled equiv wrld)))
    (value
     `((local (install-not-normalized ,fn))
       ,new-defun
       ,fn-hyps-def
       ,(and fn-hyps (cons fnc fn-hyps))
       ,runes-def
       ,before-vs-after-lemmas
       ,fn-simp-is-fn-lemma
       ,fn-simp-is-fn
       ,fnsr))))

(defun simplify-defun-tuple-lst (clique mut-rec-p
                                        clique-runic-designators
                                        assumptions** hyp-fn**
                                        theory** enable** disable**
                                        equiv** expand**
                                        theorem-name** new-name**
                                        theorem-disabled** function-disabled**
                                        simplify-body**
                                        simplify-guard** guard-hints**
                                        guard-hints-p**
                                        verify-guards
                                        simplify-measure**
                                        measure-hints**
                                        measure**
                                        untranslate** must-simplify**
                                        non-executable**
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
                (car theorem-name**) (car new-name**)
                (car theorem-disabled**) (car function-disabled**)
                (car simplify-body**)
                (car simplify-guard**)
                (car guard-hints**) (car guard-hints-p**)
                verify-guards
                (car simplify-measure**)
                (car measure-hints**) (car measure**)
                (car untranslate**) (car must-simplify**)
                (car non-executable**)
                fn-simp-alist
                verbose wrld ctx state))
              (tuple-lst
               (simplify-defun-tuple-lst
                (cdr clique) mut-rec-p clique-runic-designators
                (cdr assumptions**) (cdr hyp-fn**)
                (cdr theory**) (cdr enable**) (cdr disable**)
                (cdr equiv**) (cdr expand**)
                (cdr theorem-name**) (cdr new-name**)
                (cdr theorem-disabled**) (cdr function-disabled**)
                (cdr simplify-body**)
                (cdr simplify-guard**)
                (cdr guard-hints**) (cdr guard-hints-p**)
                verify-guards
                (cdr simplify-measure**)
                (cdr measure-hints**) (cdr measure**)
                (cdr untranslate**) (cdr must-simplify**)
                (cdr non-executable**)
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

                 (union-theories (congruence-theory :here)
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
                                           hyps-preserved-theory-lst
                                           fn-hyps-alist expand-lst
                                           induction-machine-lst
                                           wrld acc)
  (cond
   ((endp fnsr-lst) (reverse acc))
   (t (let* ((fnsr (car fnsr-lst))
             (fn (access fnsr fnsr :orig))
             (fnc (access fnsr fnsr :copy))
             (fn-hyps (fn-hyps-name fn))
             (hyps-preserved-theory (car hyps-preserved-theory-lst))
             (assumptions-guard-p (eq (car assumptions**) :guard))
             (thm (hyps-preserved-thm fnc fn-hyps hyps-preserved-theory
                                      assumptions-guard-p fn-hyps-alist expand-lst
                                      (car induction-machine-lst)
                                      wrld)))
        (hyps-preserved-thm-list-1
         (cdr fnsr-lst)
         (cdr assumptions**)
         (cdr hyps-preserved-theory-lst)
         fn-hyps-alist expand-lst
         (cdr induction-machine-lst)
         wrld
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
                                       hyps-preserved-theory-lst wrld)
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
              (fn-hyps-alist (fn-hyps-alist fnsr-lst))
              (expand-lst (hyps-expand-lst fnsr-lst fn-hyps-alist wrld)))
         (hyps-preserved-thm-list-1
          fnsr-lst assumptions** hyps-preserved-theory-lst
          fn-hyps-alist expand-lst induction-machine-lst wrld nil)))))))

(defun simplify-defun-forms (clique mut-rec-p assumptions** hyp-fn**
                                    theory** enable** disable**
                                    equiv** expand**
                                    hyps-preserved-theory**
                                    hyps-preserved-enable**
                                    hyps-preserved-disable**
                                    theorem-name** new-name**
                                    theorem-disabled** function-disabled**
                                    simplify-body**
                                    simplify-guard** guard-hints** guard-hints-p**
                                    verify-guards
                                    simplify-measure**
                                    measure-hints** measure**
                                    untranslate** must-simplify** non-executable**
                                    verbose wrld ctx state)
  (er-let* ((clique-runic-designators
             (value (clique-runic-designators clique)))
            (tuple-lst
             (simplify-defun-tuple-lst
              clique mut-rec-p
              clique-runic-designators
              assumptions** hyp-fn**
              theory** enable** disable**
              equiv** expand**
              theorem-name** new-name**
              theorem-disabled** function-disabled**
              simplify-body**
              simplify-guard** guard-hints** guard-hints-p**
              verify-guards
              simplify-measure**
              measure-hints** measure**
              untranslate** must-simplify** non-executable**
              (fn-simp-alist clique new-name** state)
              verbose wrld ctx state))
            (hyps-preserved-theory-lst
             (simplify-defun-theory-lst clique-runic-designators
                                        hyps-preserved-theory**
                                        hyps-preserved-enable**
                                        hyps-preserved-disable**
                                        ctx state)))
    (let* ((local-install-not-normalized-lst
            (strip-nths 0 tuple-lst))
           (new-defun-lst
            (strip-nths 1 tuple-lst))
           (fn-hyps-def-lst
            (remove-nils (strip-nths 2 tuple-lst)))
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
           (fnsr-lst
            (strip-nths 8 tuple-lst))
           (fnsr (car fnsr-lst))
           (fnc (access fnsr fnsr :copy))
           (all-before-vs-after-lemmas
            (append-lst before-vs-after-lemmas-lst))
           (fn-simp-is-fn-lemma-lst-with-hints
            (fn-simp-is-fn-lemmas-with-hints
             fn-simp-is-fn-lemma-lst
             fnsr-lst
             (strip-cadrs all-before-vs-after-lemmas)
             (fn-simp-is-fn-lemmas-fn-subst fnsr-lst)
             (fn-simp-is-fn-lemmas-used-names fnsr-lst)))
           (new-def-event (if mut-rec-p
                              (cons 'mutual-recursion
                                    new-defun-lst)
                            (car new-defun-lst)))
           (hyps-preserved-thm-names
            (hyps-preserved-thm-name-lst fn-hyps-names-alist)))
      (pprogn
       (cond (verbose
              (fms "Proposed simplified definition~#0~[~/s~]:~|~x1"
                   (list (cons #\0 new-defun-lst)
                         (cons #\1 (cond ((consp (cdr new-defun-lst))
                                          (cons 'mutual-recursion new-defun-lst))
                                         (t (car new-defun-lst)))))
                   (standard-co state) state nil))
             (t state))
       (value
        (cons
         `(encapsulate
            nil
            (set-inhibit-warnings "theory")
            (set-ignore-ok t)
            (set-irrelevant-formals-ok t)
            ,@(and (cdr clique) ; allow some body to simplify to non-recursive
                   '((set-bogus-mutual-recursion-ok t)))
            ,@local-install-not-normalized-lst
            (local (set-default-hints nil))
            (local (set-override-hints nil))
            ,new-def-event
            (local
             (progn
               ,@(remove-nils fn-hyps-def-lst)
               ,@runes-def-lst
               ,@all-before-vs-after-lemmas
               ,@(if (eq (car clique) fnc)
                     (hyps-preserved-thm-list
                      clique fnsr-lst assumptions** hyps-preserved-theory-lst
                      wrld)
                   (and assumptions**
                        `((make-event
                           (let ((thms (hyps-preserved-thm-list
                                        ',clique ',fnsr-lst ',assumptions**
                                        ',hyps-preserved-theory-lst (w state))))
                             (cond ((null thms)
                                    '(value-triple :invisible))
                                   ((null (cdr thms))
                                    (car thms))
                                   (t (cons 'progn thms))))))))
               (copy-def ,fnc
                         :hyps-fn
                         ,(if (cdr clique)
                              fn-hyps-names-alist
                            (cdar fn-hyps-names-alist))
                         :hyps-preserved-thm-names
                         ,hyps-preserved-thm-names
                         :equiv
                         ,(if (cdr clique)
                              (pairlis$ clique equiv**)
                            (car equiv**)))
               ,@fn-simp-is-fn-lemma-lst-with-hints))
            ,@fn-simp-is-fn-lst)
         new-def-event))))))

(defun simplify-defun-fn (fn assumptions hyp-fn
                             theory enable disable
                             equiv expand
                             hyps-preserved-theory
                             hyps-preserved-enable
                             hyps-preserved-disable
                             theorem-name new-name
                             theorem-disabled function-disabled
                             print-def
                             simplify-body
                             simplify-guard guard-hints guard-hints-p
                             verify-guards
                             simplify-measure
                             measure-hints measure
                             untranslate must-simplify non-executable
                             ctx whole-form verbose show-only state)

; Warning: Keep the argument list above in sync with the bind-** call below.

  (let ((prev (previous-transformation-expansion whole-form state)))
    (if prev
        (value prev)
      (er-let* ((wrld (value (w state)))
                (clique ; always non-nil
                 (cond ((and (function-namep fn wrld)
                             (definedp fn wrld))
                        (value (or (recursivep fn nil wrld)
                                   (list fn))))
                       (t (er soft ctx
                              "The first argument to simplify-defun must be a ~
                               defined function symbol, but ~x0 is not."
                              fn)))))
        (bind-**

; Warning: Keep the argument list below in sync with the list of formals above.

         (assumptions
          hyp-fn
          theory enable disable
          equiv expand
          hyps-preserved-theory hyps-preserved-enable hyps-preserved-disable
          theorem-name new-name
          theorem-disabled function-disabled
          (print-def)
          simplify-body
          simplify-guard guard-hints guard-hints-p
          (verify-guards)
          simplify-measure measure-hints measure
          untranslate must-simplify non-executable
          ;; ctx ; not user-supplied
          ;; whole-form ; not user-supplied
          (show-only)
          ;; state ; not user-supplied
          )
         (let ((assumptions** (fix-assumptions** hyp-fn** assumptions**)))
           (er-let* ((forms ; actually (cons full-form defun-form)
                      (simplify-defun-forms
                       clique
                       (and (cdr clique)
                            (if assumptions :assumptions t)) ; mut-rec-p
                       assumptions** hyp-fn**
                       theory** enable** disable**
                       equiv** expand**
                       hyps-preserved-theory**
                       hyps-preserved-enable** hyps-preserved-disable**
                       theorem-name** new-name**
                       theorem-disabled** function-disabled**
                       simplify-body**
                       simplify-guard** guard-hints** guard-hints-p**
                       verify-guards ; not legal for :map construct
                       simplify-measure**
                       measure-hints** measure**
                       untranslate** must-simplify** non-executable**
                       verbose wrld ctx state)))
             (let ((main-form (car forms)))
               (cond
                (show-only (value `(value-triple ',main-form)))
                (t
                 (b* ((defun-form (cdr forms))
                      (full-form
                       `(progn ,main-form
                               (table transformation-table
                                      ',whole-form
                                      ',main-form)
                               ,@(if print-def ; return the form to print
                                     `((value-triple ',defun-form))
                                   `((value-triple t))))))
                   (value full-form))))))))))))

(defmacroq simplify-defun (&whole
                           whole-form
                           fn
                           &key
                           (assumptions 'nil) ; Consider ':guard instead?
                           (hyp-fn 'nil)
                           (theory ':none)
                           (enable ':none)
                           (disable ':none)
                           (equiv 'equal)
                           (expand 'nil)
                           (assumption-theory ':none)
                           (assumption-enable ':none)
                           (assumption-disable ':none)
                           (theorem-name 'nil)
                           (new-name 'nil)
                           (theorem-disabled 'nil)
                           (function-disabled ':auto)
                           (print-def 't)
                           (simplify-body 't)    ; can be t, nil, or pattern
                           (simplify-guard 'nil) ; will likely change to 't
                           (guard-hints 'nil guard-hints-p)
                           (verify-guards ':auto)
                           (simplify-measure 'nil) ; will likely change to 't
                           (measure-hints ':auto)
                           (measure ':auto)
                           (untranslate ':nice)
                           (must-simplify '(:body t :measure nil :guard nil))
                           (non-executable ':auto)
                           (verbose 'nil)
                           (show-only 'nil))

; As with the original simplify-body, no arguments are evaluated except for
; assumptions.

; Note that simplification of the guard is done without assuming the
; :assumptions, since the :assumptions might simplify the guard away.  The
; measure's simplification also does not use the :assumptions; consider for
; example the case that :assumptions is (natp x), which might be the guard, and
; the measure is (nfix x), which must not simplify to x.

; As things currently stand, if :simplify-body is non-nil then the body must
; simplify; but we do not make the analogous requirement for :simplify-guard or
; :simplify-measure.

; Note that :simplify-body may be a pattern.  See :doc simplify-defun.

  (declare (xargs :guard (member-eq verbose '(t nil :replay))))
  (let ((form `(make-event
                (simplify-defun-fn
                 ,fn ,assumptions ,hyp-fn
                 ,theory ,enable ,disable
                 ,equiv ,expand
                 ,assumption-theory ,assumption-enable ,assumption-disable
                 ,theorem-name ,new-name
                 ,theorem-disabled ,function-disabled
                 ,print-def
                 ,simplify-body
                 ,simplify-guard ,guard-hints ,guard-hints-p ,verify-guards
                 ,simplify-measure ,measure-hints ,measure
                 ,untranslate
                 ,must-simplify
                 ,non-executable
                 (cons 'simplify-defun ,fn)
                 ,whole-form
                 ,verbose
                 ,show-only
                 state))))
    (cond (show-only
           (cond ((maybe-unquote verbose) ; quoted by defmacroq
                  (control-screen-output-and-maybe-replay t   nil form))
                 (t
                  (control-screen-output-and-maybe-replay nil nil form))))
          (t
           (cond ((maybe-unquote verbose) ; quoted by defmacroq
                  (control-screen-output-and-maybe-replay t   t form))
                 (t
                  (control-screen-output-and-maybe-replay nil t form)))))))

(defmacro show-simplify-defun (&rest args)
  `(simplify-defun ,@args :show-only t))
