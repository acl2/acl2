; Standard Utilities Library
; Copyright (C) 2008-2014 Centaur Technology
;
; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/
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
; Original authors: Jared Davis <jared@centtech.com>
;                   Sol Swords <sswords@centtech.com>

(in-package "STD")
(include-book "define")
(include-book "tools/flag" :dir :system)
(set-state-ok t)
(program)

(defxdoc defines
  :parents (std/util mutual-recursion)
  :short "A very fine alternative to @(see mutual-recursion)."

  :long "<p>@('Defines') is a sophisticated macro for introducing mutually
recursive functions using @(see define).  It gives you:</p>

<ul>

<li>The usual benefits of @('define')&mdash;@(see extended-formals), concise
@(see xargs) syntax, @(see returns-specifiers), @(see xdoc) integration, easy
inlining, and so on.</li>

<li>Automatic @(see acl2::make-flag) integration, so you can easily prove
inductive theorems about your new definitions.</li>

</ul>

<h3>Examples</h3>

@({
    (defines terms
      :parents (syntax)
      :short \"Example of terms in some simple, numeric language.\"

      (define my-termp (x)
        (if (atom x)
            (natp x)
          (and (symbolp (car x))
               (my-term-listp (cdr x))))
        ///
        (defthm natp-when-my-termp
          (implies (atom x)
                   (equal (my-termp x)
                          (natp x))))
        (defthm my-termp-of-cons
          (equal (my-termp (cons fn args))
                 (and (symbolp fn)
                      (my-term-listp args)))))

      (define my-term-listp (x)
        (if (atom x)
            t
          (and (my-termp (car x))
               (my-term-listp (cdr x))))
        ///
        (deflist my-term-listp (x)
          (my-termp x)
          :already-definedp t)))

  (defines flattening
    :parents (terms)
    :short \"Collect up the arguments of terms.\"

    (define my-flatten-term ((x my-termp))
      :flag term
      :returns (numbers true-listp :rule-classes :type-prescription)
      (if (atom x)
          (list x)
        (my-flatten-term-list (cdr x))))

    (define my-flatten-term-list ((x my-term-listp))
      :flag list
      :returns (numbers true-listp :rule-classes :type-prescription)
      (if (atom x)
          nil
        (append (my-flatten-term (car x))
                (my-flatten-term-list (cdr x)))))
    ///
    (defthm-flattening-flag
      (defthm nat-listp-of-my-flatten-term
        (implies (my-termp x)
                 (nat-listp (my-flatten-term x)))
        :flag term)
      (defthm nat-listp-of-my-flatten-term-list
        (implies (my-term-listp x)
                 (nat-listp (my-flatten-term-list x)))
        :flag list)))
})

<h3>Usage</h3>

<p>The general form of @(see defines) is:</p>

@({
    (defines clique-name
      [global options]
      (define f1 ...)
      ...
      (define fN ...)
      [/// other-events])
})

<p>The @('clique-name') may be any symbol&mdash;we often just use the name of
the first function in the clique, but this is not required.  The name is used
for documentation purposes, and also (by default) is used to name the flag
function that will be introduced by @(see acl2::make-flag).</p>

<p>The global options each have the form @(':name value'), and we describe
these options below.  We usually prefer to put these options at the front of
the @('defines') form, as shown above, but the options can be put anywhere
until the @('///') form.</p>

<p>There must be at least two @('define') forms.  These can use the usual @(see
define) syntax, and mostly this all works out naturally.  The most significant
caveats have to do with how we try to prove the theorems for @(':returns')
specifiers (see below).</p>

<p>The @('other-events') are a structuring device that allow you to associate
any arbitrary events.  These events are submitted after the definitions, flag
function, etc., have been processed.  All of the functions in the clique are
left enabled while processing these events.</p>

<p>Note that individual @('define')s can have their own other-events.  All of
these individual sections are processed (with their own local scopes) before
any global @('other-events').</p>

<h4>Global Options</h4>

<dl>

<dt>:verbosep bool</dt>

<dd>Normally most output is suppressed, but this can make it hard to understand
failures.  You can enable @(':verbosep t') for better debugging.</dd>


<dt>:mode</dt>
<dt>:guard-hints, :guard-debug, :verify-guards</dt>
<dt>:well-founded-relation, :measure-debug, :hints, :otf-flg</dt>
<dt>:ruler-extenders</dt>

<dd>In an ordinary @(see mutual-recursion), each of these @(see xargs) style
options can be attached to any @('defun') in the clique.  But we usually think
of these as global options to the whole clique, so we make them available as
top-level options to the @('defines') form.  In the implementation, we just
attach these options to the first @('defun') form generated, except for
@(':ruler-extenders'), which we apply to all of the defuns.</dd>


<dt>:prepwork</dt>

<dd>Arbitrary events to be submitted before the definitions.  Typically this
might include @(see in-theory) calls, one-off supporting lemmas, etc.  Prepwork
is not automatically @(see local), so lemmas and theory changes should usually
be explicitly made @(see local).</dd>

<dd>Note that each individual @('define') may have its own @(':prepwork')
section.  All of these sections will be appended together in order, with the
global @(':prepwork') coming first, and submitted before the definitions.</dd>


<dt>:returns-hints hints</dt>
<dt>:returns-no-induct bool</dt>

<dd>You can give hints for the inductive @(':returns') theorem.  Alternately,
if you know you don't need to prove the returns theorems inductively, you can
set @(':returns-no-induct t'), which may improve performance.</dd>


<dt>:parents, :short, :long</dt>

<dd>These are global @(see xdoc) options that will be associated with the
@('clique-name') for this @('defines').</dd>

<dd>Note that each individual @('define') may separately have its own
documentation and rest-events.  As a convenience, if global documentation is
provided while individual documentation is not, a basic topic will be created
whose @(':parents') point at the @('clique-name').</dd>

<dd>A corner case is when the @('clique-name') agrees with an individual
function's name.  In this case we try to grab the documentation from
<i>either</i> the named function or the global options.  To prevent confusion,
we cause an error if documentation is provided in both places.</dd>

<dt>:ignore-ok val</dt>
<dt>:irrelevant-formals-ok val</dt>
<dt>:bogus-ok val</dt>

<dd>Submit @(see set-ignore-ok), @(see set-irrelevant-formals-ok), and/or
@(see set-bogus-mutual-recursion-ok) forms before the definitions.  These
options are @(see local) to the definitions; they do not affect the
@('other-events') or any later events.</dd>


<dt>:flag name</dt>

<dd>You can also use @(':flag nil') to suppress the creation of a flag
function.  Alternately, you can use this option to customize the name of the
flag function.  The default is inferred from the @('clique-name'), i.e., it
will look like @('<clique-name>-flag').</dd>

<dt>:flag-var var</dt>
<dt>:flag-defthm-macro name</dt>
<dt>:flag-hints hints</dt>

<dd>Control the flag variable name, flag macro name, and hints for @(see
acl2::make-flag).</dd>


<dt>:flag-local bool</dt>

<dd>By default the flag function is created locally.  This generally improves
performance when later including your book, and is appropriate when all of your
flag-based reasoning about the function is done in @(':returns') specifiers and
in the @('///') section.  If you need the flag function and its macros to exist
beyond the @('defines') form, set @(':flag-local nil').</dd>


<dt>:progn bool</dt>

<dd>By default everything is submitted in an @('(encapsulate nil ...)').  If
you set @(':progn t'), then we will instead submit everything in a @('progn').
This mainly affects what @('local') means within the @('///') section.  This
may slightly improve performance by avoiding the overhead of @(see
encapsulate), and is mainly meant as a tool for macro developers.</dd>


</dl>")




(defconst *defines-xargs-keywords*
  ;; Subset of the *xargs-keywords* that are not individually tailored for
  ;; each function.  We'll stick these into the xargs for the first function.
  ;; ACL2 checks that all the functions agree on these settings.
  '(
    ;; :guard -- no, individual
    ;; :measure -- no, individual
    ;; :non-executable -- no, individual
    ;; :split-types -- no, individual
    ;; :ruler-extenders -- no, individual (actually yes, for flag)
    ;; :normalize -- no, individual
    ;; :stobjs -- no, individual
    :ruler-extenders ;; used for flag
    :guard-hints ;; Appended to guard-hints for all sub-functions.
    :hints       ;; Appended to hints for all sub-functions.
    :guard-debug ;; Must agree with any individual guard-debug settings.
    :measure-debug ;; Must agree with any individual measure-debug settings.
    :well-founded-relation ;; Must agree with any explicit :well-founded-relations
    :otf-flg              ;; Must agree with any explicit otf-flg settings.
    :mode        ;; Must agree with any individual :mode settings.
    :verify-guards ;; Must agree with any individual :verify-guards settings.
    ))

(defconst *defines-keywords*
  (append
   '(:ignore-ok                 ;; you can put this in any define or at the top
     :irrelevant-formals-ok     ;; you can put this in any define or at the top
     :bogus-ok                  ;; shorthand for set-bogus-mutual-recursion-ok

     :parents     ;; Documentation options for CLIQUE-NAME
     :short
     :long

     :prepwork    ;; Global prepwork.  This happens before the prepwork for any
                  ;; individual functions, which are all appended together.

     :flag
     :flag-var
     :flag-local
     :flag-defthm-macro
     :flag-hints

     :returns-no-induct
     :returns-hints

     :verbosep
     :progn
     )
   *defines-xargs-keywords*))

(defun parse-defines (ctx forms extra-keywords world)
  ;; Returns guts list
  (b* (((when (atom forms))
        nil)
       (form1 (car forms))
       ((unless (and (consp form1)
                     (consp (cdr form1))
                     (eq (first form1) 'define)))
        (er hard? ctx "Expected a list of ~s0 forms, but found ~x1."
            'define (car forms)))
       ((cons name args) (cdr form1))
       (guts1 (parse-define name args extra-keywords world)))
    (cons guts1 (parse-defines ctx (cdr forms) extra-keywords world))))

(defun collect-prepworks (gutslist)
  (if (atom gutslist)
      nil
    (append (getarg :prepwork nil (defguts->kwd-alist (car gutslist)))
            (collect-prepworks (cdr gutslist)))))

(defun collect-macros (gutslist)
  (b* (((when (atom gutslist))
        nil)
       (macros1 (defguts->macro (car gutslist)))
       ((unless macros1)
        (collect-macros (cdr gutslist))))
    (cons macros1 (collect-macros (cdr gutslist)))))

(defun collect-ignore-oks (gutslist)
  ;; Collect any explicit :ignore-ok values into a list
  (b* (((when (atom gutslist))
        nil)
       (kwd-alist (defguts->kwd-alist (car gutslist)))
       ((when (assoc :ignore-ok kwd-alist))
        (cons (cdr (assoc :ignore-ok kwd-alist))
              (collect-ignore-oks (cdr gutslist)))))
    (collect-ignore-oks (cdr gutslist))))

(defun collect-irrelevant-formals-oks (gutslist)
  ;; Collect any explicit :irrelevant-formals-ok values into a list
  (b* (((when (atom gutslist))
        nil)
       (kwd-alist (defguts->kwd-alist (car gutslist)))
       ((when (assoc :irrelevant-formals-ok kwd-alist))
        (cons (cdr (assoc :irrelevant-formals-ok kwd-alist))
              (collect-irrelevant-formals-oks (cdr gutslist)))))
    (collect-irrelevant-formals-oks (cdr gutslist))))

(defun make-ignore-events (ctx kwd-alist gutslist)
  (b* ((ignore-oks (collect-ignore-oks gutslist))
       (ignore-oks (if (assoc :ignore-ok kwd-alist)
                       (cons (cdr (assoc :ignore-ok kwd-alist)) ignore-oks)
                     ignore-oks))
       (ignore-oks (remove-duplicates ignore-oks))
       ((unless (or (atom ignore-oks)
                    (atom (cdr ignore-oks))))
        (er hard? ctx "Conflicting :ignore-ok settings."))

       (irrel-oks  (collect-irrelevant-formals-oks gutslist))
       (irrel-oks  (if (assoc :irrel-ok kwd-alist)
                       (cons (cdr (assoc :ignore-ok kwd-alist)) irrel-oks)
                     irrel-oks))
       (irrel-oks  (remove-duplicates irrel-oks))
       ((unless (or (atom irrel-oks)
                    (atom (cdr irrel-oks))))
        (er hard? ctx "Conflicting :irrel-ok settings."))

       (bogus-okp (cdr (assoc :bogus-ok kwd-alist))))
    (append
     (and (car ignore-oks) '((set-ignore-ok t)))
     (and (car irrel-oks)  '((set-irrelevant-formals-ok t)))
     (and bogus-okp        '((set-bogus-mutual-recursion-ok t)))
     )))

(defun collect-main-defs (gutslist)
  (if (atom gutslist)
      nil
    (cons (defguts->main-def (car gutslist))
          (collect-main-defs (cdr gutslist)))))

(defun collect-macro-aliases (gutslist)
  (if (atom gutslist)
      nil
    (append (add-macro-aliases-from-guts (car gutslist))
            (collect-macro-aliases (cdr gutslist)))))

(defun collect-guts-alist-exts (gutslist)
  (if (atom gutslist)
      nil
    (cons (extend-define-guts-alist (car gutslist))
          (collect-guts-alist-exts (cdr gutslist)))))

(defun collect-names-from-guts (gutslist)
  (if (atom gutslist)
      nil
    (cons (defguts->name (car gutslist))
          (collect-names-from-guts (cdr gutslist)))))

(defun collect-defines-to-disable (gutslist)
  (b* (((when (atom gutslist))
        nil)
       ((defguts guts1) (car gutslist))
       (enabled-p (getarg :enabled nil guts1.kwd-alist))
       ((when enabled-p)
        ;; The function is supposed to be ENABLED, so don't collect its name
        (collect-defines-to-disable (cdr gutslist))))
    (cons guts1.name-fn
          (collect-defines-to-disable (cdr gutslist)))))

;; (defun collect-all-returnspec-thms (gutslist world)
;;   (if (atom gutslist)
;;       nil
;;     (append (returnspec-thms (defguts->name-fn (car gutslist))
;;                              (defguts->returnspecs (car gutslist))
;;                              world)
;;             (collect-all-returnspec-thms (cdr gutslist) world))))

;; (defun collect-rest-events-from-guts (gutslist)
;;   (if (atom gutslist)
;;       nil
;;     (append (defguts->rest-events (car gutslist))
;;             (collect-rest-events-from-guts (cdr gutslist)))))

(defun make-fn-defsection (guts cliquename process-returns)
  (b* (((defguts guts) guts)
       (short      (getarg :short          nil guts.kwd-alist))
       (long       (getarg :long           nil guts.kwd-alist))
       (parents    (getarg :parents        nil guts.kwd-alist))
       (parents    (if (assoc :parents guts.kwd-alist)
                       parents
                     (and cliquename
                          (not (eq cliquename guts.name))
                          (list cliquename)))))

    `((defsection ,guts.name
        ,@(and parents `(:parents ,parents))
        ,@(and short   `(:short ,short))
        ,@(and long    `(:long ,long))
        ,@(and process-returns
               `((make-event
                  (let* ((world (w state))
                         (events (returnspec-thms ',guts.name
                                                  ',guts.name-fn
                                                  ',guts.returnspecs
                                                  world)))
                    `(with-output :stack :pop (progn . ,events))))))
        (local (set-define-current-function ,guts.name))
        (with-output :stack :pop (progn . ,guts.rest-events)))
      ;; Make sure the section gets processed first.  Once it's done,
      ;; we can add the signature block.
      (with-output :on (error) ,(add-signature-from-guts guts)))))

(defun collect-fn-defsections (gutslist cliquename process-returns)
  (if (atom gutslist)
      nil
    (append (make-fn-defsection (car gutslist) cliquename process-returns)
            (collect-fn-defsections (cdr gutslist) cliquename process-returns))))

(defun guts->flag (guts)
  (or (cdr (assoc :flag (defguts->kwd-alist guts)))
      (defguts->name guts)))

(defun collect-flag-mapping (gutslist)
  (if (atom gutslist)
      nil
    (cons (list (defguts->name-fn (car gutslist))
                (guts->flag (car gutslist)))
          (collect-flag-mapping (cdr gutslist)))))

(defun returnspec-thm-bodies (fnname binds retspecs world)
  (b* (((when (atom retspecs)) nil)
       (body (returnspec-thm-body fnname binds (car retspecs) world))
       (rest (returnspec-thm-bodies fnname binds (cdr retspecs) world)))
    (if (eq body t)
        rest
      (cons body rest))))

(defun returnspec-thm-ruleclasses-add-corollary (classes body)
  (b* (((when (atom classes)) nil)
       (class (car classes))
       (rest (returnspec-thm-ruleclasses-add-corollary (cdr classes) body))
       ((when (atom class))
        (cons `(,class :corollary ,body) rest))
       ((when (assoc-keyword :corollary (cdr class)))
        (cons class rest)))
    (cons `(,(car class)
            :corollary ,body
            . ,(cdr class))
          rest)))

(defun returnspec-thm-ruleclasses (fnname binds retspecs world)
  (b* (((when (atom retspecs)) nil)
       (body (returnspec-thm-body fnname binds (car retspecs) world))
       (rest (returnspec-thm-ruleclasses fnname binds (cdr retspecs) world))
       (classes (returnspec->rule-classes (car retspecs)))
       ;; :rule-classes :rewrite --> (:rewrite)
       ;; :rule-classes (:rewrite :type-prescription) --> (:rewrite :type-prescription)
       (classes (if (and (atom classes) classes) (list classes) classes))
       (classes-with-corollaries (returnspec-thm-ruleclasses-add-corollary
                                  classes body)))
    (append classes-with-corollaries rest)))

(defun returnspec-thm-hints (retspecs)
  (if (atom retspecs)
      nil
    (append (returnspec->hints (car retspecs))
            (returnspec-thm-hints (cdr retspecs)))))

(defun find-first-string-hint (retspec-hints)
  (if (atom retspec-hints)
      nil
    (if (and (consp (car retspec-hints))
             (stringp (caar retspec-hints)))
        (caar retspec-hints)
      (find-first-string-hint (cdr retspec-hints)))))

(defun returnspecs-flag-entries (retspecs flag fnname fnname-fn binds body-subst hint-subst world)
  (b* (((when (atom retspecs)) nil)
       (formula (returnspec-thm-body fnname-fn binds (car retspecs) world))
       ((when (eq formula t))
        (returnspecs-flag-entries (cdr retspecs) flag fnname fnname-fn binds body-subst hint-subst world))
       ((returnspec x) (car retspecs))
       (subgoal (find-first-string-hint x.hints))
       (strsubst (returnspec-strsubst fnname fnname-fn))
       (- (and subgoal
               (er hard? 'defines
                   "Error in returnspec theorems: unless using ~x0,~
                    subgoal hints should be given using the global ~x1 ~
                    option.  Computed hints may be given on individual ~
                    :returns entries.  Found hint for ~x2."
                   :returns-no-induct :returns-hints subgoal))))
    (cons `(defthm ,(intern-in-package-of-symbol
                     (concatenate 'string "RETURN-TYPE-OF-" (symbol-name fnname)
                                  "." (symbol-name x.name))
                     fnname)
             ,(returnspec-sublis body-subst nil formula)
             :hints ,(returnspec-sublis hint-subst strsubst x.hints)
             :rule-classes ,(returnspec-sublis hint-subst nil x.rule-classes)
             :flag ,flag)
          (returnspecs-flag-entries (cdr retspecs) flag fnname fnname-fn binds body-subst hint-subst world))))

(defun fn-returnspec-flag-entries (guts world)
  (b* (((defguts guts) guts)
       (flag (guts->flag guts))
       (formals (look-up-formals guts.name-fn world))
       (fncall `(,guts.name-fn . ,formals))
       (binds (b* ((names (returnspeclist->names guts.returnspecs))
                   (ignorable-names (make-symbols-ignorable names)))
                (if (consp (cdr ignorable-names))
                    `((mv . ,ignorable-names) ,fncall)
                  `(,(car ignorable-names) ,fncall))))
       ((mv body-subst hint-subst)
        (returnspec-return-value-subst
         guts.name guts.name-fn formals (returnspeclist->names guts.returnspecs))))
    (returnspecs-flag-entries guts.returnspecs flag guts.name guts.name-fn binds body-subst hint-subst world)))

(defun collect-returnspec-flag-thms (gutslist world)
  (if (atom gutslist)
      nil
    (append (fn-returnspec-flag-entries (car gutslist) world)
            (collect-returnspec-flag-thms (cdr gutslist) world))))

(defun returnspec-mrec-default-default-hint (fnname id world)
  (let ((fns (acl2::recursivep fnname t world)))
    (and (eql 0 (acl2::access acl2::clause-id id :forcing-round))
         (equal '(1) (acl2::access acl2::clause-id id :pool-lst))
         `(:computed-hint-replacement
           ((and stable-under-simplificationp
                 (expand-calls . ,fns)))
           :in-theory (disable . ,fns)))))

(defun returnspec-mrec-default-hints (fnname world)
  (let ((entry (cdr (assoc 'returnspec-mrec (table-alist 'std::default-hints-table world)))))
    (subst fnname 'fnname entry)))

(defmacro set-returnspec-mrec-default-hints (hint)
  `(table std::default-hints-table 'returnspec-mrec ',hint))

(set-returnspec-mrec-default-hints
 ((returnspec-mrec-default-default-hint 'fnname acl2::id world)))


(defun returnspec-flag-thm (defthm-macro gutslist returns-hints world)
  (let* ((thms (collect-returnspec-flag-thms gutslist world))
         (hints (if (eq returns-hints :none)
                    (returnspec-mrec-default-hints
                     (defguts->name-fn (car gutslist)) world)
                  returns-hints)))
    (if thms
        `(,defthm-macro
           ,@thms
           :skip-others t
           :hints ,hints)
      `(value-triple :skipped))))

(def-primitive-aggregate defines-guts
  (name             ;; name of the defines section
   gutslist         ;; define guts of functions
   kwd-alist        ;; arguments to defines
   flag-mapping     ;; function names->flag names
   flag-defthm-macro
   ;; other stuff?
   ))

(defun get-defines-alist (world)
  "Look up information about the current defines in the world."
  (cdr (assoc 'defines-alist (table-alist 'define world))))

(defun extend-defines-alist (guts)
  `(table define 'defines-alist
          (cons (cons ',(defines-guts->name guts) ',guts)
                (get-defines-alist world))))

(defun gutslist-find-hints (gutslist)
  (if (atom gutslist)
      nil
    (or (getarg :hints nil (defguts->kwd-alist (car gutslist)))
        (gutslist-find-hints (cdr gutslist)))))

(defun apply-ruler-extenders-to-defs (ruler-extenders defs)
  (if (atom defs)
      nil
    (cons (append (take 3 (car defs))
                  `((declare (xargs :ruler-extenders ,ruler-extenders)))
                  (nthcdr 3 (car defs)))
          (apply-ruler-extenders-to-defs ruler-extenders (cdr defs)))))


; Documentation hack.
;
; Case 1: clique-name doesn't clash with the individual function names.  Then
; everything works out and we'll get reasonable documentation out
;
; Case 2: clique-name is the same as some function name.  We don't want to
; create documentation for "both" the global and local functions.  If we do,
; the local function will win (because its docs come second) and we'll lose
; the global docs.  Worse, this can lead to new top-level topics because we
; can easily end up with topics that are their own parents.
;
; A solution.  If we hit case 2, we'll try to "inject" the global docs into the
; individual function's docs.  (This is better than going the other way around
; and "extracting" the individual docs, because the individual function gets a
; nice "signature" block, etc.)

(defun maybe-inject-global-docs
  (name parentsp parents short long  ;; global clique-name and global docs
   gutslist                 ;; guts for individual defines, which we'll rewrite
   )
  (b* ((__function__ 'maybe-inject-global-docs)
       ((when (atom gutslist))
        nil)
       (rest (maybe-inject-global-docs name parentsp parents short long
                                       (cdr gutslist)))
       (guts1 (car gutslist))
       ((defguts guts1) guts1)
       ((unless (equal guts1.name name))
        (cons (car gutslist) rest))

       (sub-short    (getarg :short   nil guts1.kwd-alist))
       (sub-long     (getarg :long    nil guts1.kwd-alist))
       (sub-parents  (getarg :parents nil guts1.kwd-alist))
       (sub-parentsp (consp (assoc :parents guts1.kwd-alist)))
       ((when (and parentsp sub-parentsp))
        (raise "Can't give :parents in (~x1 ~x0 ...) because there are global ~
                :parents in the (~x2 ~x0 ...) form."
               name 'define 'defines))
       ((when (and short sub-short))
        (raise "Can't give :short in (~x1 ~x0 ...) because there is a global ~
                :short in the (~x2 ~x0 ...) form."
               name 'define 'defines))
       ((when (and long sub-long))
        (raise "Can't give :long in (~x1 ~x0 ...) because there is a global ~
                :long in the (~x2 ~x0 ...) form."
               name 'define 'defines))

       (kwd-alist guts1.kwd-alist)
       (kwd-alist (remove1-assoc :short kwd-alist))
       (kwd-alist (remove1-assoc :long  kwd-alist))
       (kwd-alist (remove1-assoc :parents kwd-alist))
       (kwd-alist (acons :short (or short sub-short) kwd-alist))
       (kwd-alist (acons :long  (or long  sub-long) kwd-alist))
       (kwd-alist (acons :parents (if parentsp parents sub-parents) kwd-alist))
       (new-guts (change-defguts guts1 :kwd-alist kwd-alist)))
    (cons new-guts rest)))

(defun split-///-defines (name args)
  (b* (((mv main-stuff rest-events) (split-/// name args))
       ;; Allow two occurrences of ///.  Up to the first is keywords and
       ;; definitions, up to the second happens after that but before the
       ;; rest-events from each of the define forms, and the rest happen after
       ;; that.
       ((mv rest-events1 rest-events2) (split-/// name rest-events))
       ((mv rest-events1 rest-events2)
        (if rest-events2
            (mv rest-events1 rest-events2)
          (mv nil rest-events1))))
    (mv main-stuff rest-events1 rest-events2)))

(defun defines-fn (name args world)
  (declare (xargs :guard (plist-worldp world)))
  (b* ((__function__ 'defines)
       ((unless (symbolp name))
        (raise "Expected name to be a symbol, but found ~x0." name))

       ((mv main-stuff rest-events1 rest-events2)
        (split-///-defines name args))
       ((mv kwd-alist defs)
        (extract-keywords name *defines-keywords* main-stuff nil))
       (gutslist (parse-defines name defs '(:flag) world))

       ((unless (consp (cdr gutslist)))
        (raise "Error in ~x0: expected more than one function." name))

       (short      (getarg :short   nil kwd-alist))
       (long       (getarg :long    nil kwd-alist))
       (parents    (getarg :parents nil kwd-alist))
       (parents-p  (consp (assoc :parents kwd-alist)))
       (parents    (if parents-p
                       parents
                     (xdoc::get-default-parents world)))
       (fnnames    (collect-names-from-guts gutslist))

       (want-xdoc-p (or short long parents-p))

       ((mv short long parents kwd-alist gutslist)
        (if (and want-xdoc-p (member name fnnames))
            ;; Special case: move the documentation into the function;
            ;; don't produce our own section.
            (mv nil nil nil
                (remove1-assoc :parents
                               (remove1-assoc :short
                                              (remove1-assoc :long kwd-alist)))
                (maybe-inject-global-docs
                 name parents-p parents short long gutslist))
          ;; Normal case: have docs, no function with the same name,
          ;; make our own section
          (mv short long parents kwd-alist gutslist)))

       (prepwork (getarg :prepwork nil kwd-alist))
       ((unless (true-listp prepwork))
        (raise "Error in ~x0: expected :prepwork to be a true-listp, but found ~x1."
               name prepwork))
       (prepwork    (append prepwork (collect-prepworks gutslist)))
       (macros      (collect-macros gutslist))
       (set-ignores (make-ignore-events name kwd-alist gutslist))

       (extra-xargs (get-xargs-from-kwd-alist kwd-alist))
       (ruler-extenders (getarg :ruler-extenders nil kwd-alist))
       (orig-defs   (collect-main-defs gutslist))
       (final-defs  (if extra-xargs
                        ;; Stick them into the first def.
                        (cons (append (take 3 (car orig-defs))
                                      `((declare (xargs . ,extra-xargs)))
                                      (nthcdr 3 (car orig-defs)))
                              (if ruler-extenders
                                  (apply-ruler-extenders-to-defs
                                   ruler-extenders (cdr orig-defs))
                                (cdr orig-defs)))
                      orig-defs))
       (mutual-rec  (cons 'mutual-recursion final-defs))
       (aliases     (collect-macro-aliases gutslist))
       (guts-table-exts (collect-guts-alist-exts gutslist))

       (flag-name (if (assoc :flag kwd-alist)
                      (cdr (assoc :flag kwd-alist))
                    (intern-in-package-of-symbol
                     (concatenate 'string (symbol-name name) "-FLAG")
                     name)))
       (flag-var          (getarg :flag-var nil kwd-alist))
       (flag-local        (getarg :flag-local t kwd-alist))
       (flag-defthm-macro (getarg :flag-defthm-macro nil kwd-alist))
       (flag-hints        (or (getarg :flag-hints nil kwd-alist)
                              (getarg :hints nil kwd-alist)
                              (gutslist-find-hints gutslist)))
       (flag-mapping      (collect-flag-mapping gutslist))

       ((unless (no-duplicatesp-eq (strip-cadrs flag-mapping)))
        (raise "Error: duplicated flag names!"))

       (returns-induct    (and flag-name
                               (not (getarg :returns-no-induct nil kwd-alist))))
       (returns-hints     (getarg :returns-hints :none kwd-alist))

       ((when (and (not returns-induct) (not (eq returns-hints :none))))
        (raise "Error in ~x0: returns-hints only is useful without ~
                :returns-no-induct."
               name))

       (thm-macro      (and flag-name
                            (or flag-defthm-macro (flag::thm-macro-name flag-name))))

       (fn-sections (collect-fn-defsections gutslist
                                            (and want-xdoc-p name)
                                            (not returns-induct)))

       (fns-to-disable (collect-defines-to-disable gutslist))

       (defines-guts
         (make-defines-guts
          :name name
          :gutslist gutslist
          :kwd-alist kwd-alist
          :flag-mapping flag-mapping
          :flag-defthm-macro thm-macro))

       (prognp (getarg :progn nil kwd-alist)))

    `(,@(if prognp '(progn) '(encapsulate nil))
       (with-output :stack :pop (progn . ,prepwork))
       (defsection-progn ,name
         ,@(and parents-p `(:parents ,parents))
         ,@(and short   `(:short ,short))
         ,@(and long    `(:long ,long))
         (with-output :on (error) (progn . ,macros))
         ,@(if set-ignores
               `((encapsulate ()
                   ,@set-ignores
                   (with-output :stack :pop ,mutual-rec)))
             `((with-output :stack :pop ,mutual-rec)))
         (with-output :on (error) (progn . ,aliases))
         (with-output :on (error) (progn . ,guts-table-exts))
         (with-output :on (error)
           ,(extend-defines-alist defines-guts)))

       ;; Introduce a suitable flag function, but only if this is a logic mode function.
       ,@(and flag-name
              `((with-output :on (error)
                  (make-event
                   (if (logic-mode-p ',(defguts->name-fn (car gutslist)) (w state))
                       ;;
                       (value '(flag::make-flag ,flag-name ,(defguts->name-fn (car gutslist))
                                                :flag-mapping ,flag-mapping
                                                ,@(and flag-defthm-macro
                                                       `(:defthm-macro-name ,flag-defthm-macro))
                                                ,@(and flag-var `(:flag-var ,flag-var))
                                                ,@(and flag-local `(:local t))
                                                ,@(and ruler-extenders `(:ruler-extenders ,ruler-extenders))
                                                :hints ,flag-hints))
                     (value '(value-triple :invisible)))))))

       (defsection rest-events-1
         ,@(and want-xdoc-p `(:extension ,name))
         ;; It seems OK to do this even if we're in program mode, because in that
         ;; case you shouldn't be trying to provide return-value theorems, right?
         ,@(and returns-induct
                `((make-event
                   (let ((event (returnspec-flag-thm
                                 ',thm-macro ',gutslist ',returns-hints (w state))))
                     `(with-output :stack :pop ,event)))))
         (with-output :stack :pop (progn . ,rest-events1))
         ,@fn-sections
         (with-output :stack :pop (progn . ,rest-events2)))

       ;; Disable any functions that aren't marked as :enable
       ,@(and (consp fns-to-disable)
              `((make-event
                 (if (logic-mode-p ',(defguts->name-fn (car gutslist)) (w state))
                     '(in-theory (disable . ,fns-to-disable))
                   '(value-triple :invisible)))))

       )))


(defmacro defines (name &rest args)
  (let* ((verbose-tail (member :verbosep args))
         (verbosep (and verbose-tail (cadr verbose-tail))))
    `(with-output
       :stack :push
       ,@(and (not verbosep)
              '(:off :all))
       (make-event (defines-fn ',name ',args (w state))))))






(defxdoc defret-mutual
  :parents (define returns-specifiers)
  :short "Prove additional theorems about a mutual-recursion created using @(see defines), implicitly binding the return variables."

  :long "<p>@('defret-mutual') uses flag-function-based induction to prove
theorems about a mutual recursion created using @(see defines).  See also @(see
acl2::make-flag) for information about the approach.</p>

<p>@('defret-mutual') is mostly just a wrapper around the flag defthm macro
created for the mutual recursion.  It generates the individual theorems within
the mutual induction using @(see defret), so the main features are inherited
from defret, such as automatic binding of return value names and support for
the @(':hyp') keyword.</p>

<h5>Syntax:</h5>
<p>Using the following mutual recursion as an example:</p>
@({
 (defines pseudo-term-vars
   (define pseudo-term-vars ((x pseudo-termp))
     :returns (vars)
     ...)
   (define pseudo-term-list-vars ((x pseudo-term-listp))
     :returns (vars)
     ...))
 })

<p>Then we can use @('defret-mutual') as follows:</p>

@({
 (defret-mutual symbol-listp-of-pseudo-term-vars
   (defret symbol-listp-of-pseudo-term-vars
     (symbol-listp vars)
     :hints ...
     :fn pseudo-term-vars)
   (defret symbol-listp-of-pseudo-term-list-vars
     (symbol-listp vars)
     :hints ...
     :fn pseudo-term-list-vars)
   :mutual-recursion pseudo-term-vars
   ...)
 })

<p>If the @(':mutual-recursion') keyword is omitted, then the last mutual
recursion introduced with @('defines') is assumed to be the subject.</p>

<p>@('defret-mutual') supports all of the top-level options of flag defthm macros such as:</p>
@({
 :hints
 :no-induction-hint
 :skip-others
 :instructions
 :otf-flg })

<p>The individual @('defret') forms inside the mutual recursion support all the
options supported by @(see defret), plus the @(':skip') option from the flag
defthm macro, which if set to nonnil uses the theorem only as an inductive
lemma for the overall mutually recursive proof, and doesn't export it.</p>
 })")

(defun pass-kwd-args (names kwd-alist)
  (if (atom names)
      nil
    (let ((look (assoc (car names) kwd-alist)))
      (if look
          `(,(car names) ,(cdr look) . ,(pass-kwd-args (cdr names) kwd-alist))
        (pass-kwd-args (cdr names) kwd-alist)))))

(defun defgutslist-find (name x)
  (if (atom x)
      nil
    (if (eq name (defguts->name (car x)))
        (car x)
      (defgutslist-find name (cdr x)))))

(defun defret-mutual-process-defret (defret guts name world)
  (b* ((__function__ 'defret-mutual)
       ((defines-guts guts))
       ((unless (and (<= 3 (len defret))
                     (member (car defret) '(defret defretd))
                     (symbolp (cadr defret))))
        (raise "Invaid defret/defretd form in ~x0: ~x1"
               `(defret-mutual ,name) defret))
       (disabledp (eq (car defret) 'defretd))
       (thmname (cadr defret))
       (ctx `(,(car defret) ,thmname))
       (rest (cddr defret))
       ((mv kwd-alist body-lst)
        (extract-keywords ctx
                          '(:hyp :fn :hints :rule-classes :pre-bind :otf-flg :skip)
                          rest nil))
       ((unless (consp body-lst))
        (raise "No body in ~x0" ctx))
       ((unless (atom (cdr body-lst)))
        (raise "Extra args besides the body in ~x0" ctx))
       (body (car body-lst))

       (fn (cdr (assoc :fn kwd-alist)))
       ((unless fn)
        (raise "~x0: The function name must be specified (with :fn)." ctx))
       (fnguts (defgutslist-find fn guts.gutslist))
       ((defguts fnguts))
       (flag (cadr (assoc fnguts.name-fn guts.flag-mapping)))
       ((unless flag)
        (raise "~x0: Invalid function name ~x1 (no flag mapping)." ctx fn))
       (fnguts (defgutslist-find fn guts.gutslist))
       ((unless fnguts)
        (raise "~x0: Invalid function name ~x1 (no define-guts)." ctx fn)))
    (append (defret-core thmname body kwd-alist disabledp fnguts world)
            `(:flag ,flag :skip ,(cdr (assoc :skip kwd-alist))))))


(defun defret-mutual-process-defrets (defrets guts name world)
  (if (atom defrets)
      nil
    (cons (defret-mutual-process-defret (car defrets) guts name world)
          (defret-mutual-process-defrets (cdr defrets) guts name world))))

(defun defret-mutual-fn (name args world)
  (b* ((__function__ 'defret-mutual)
       ((unless (and (symbolp name)
                     (not (keywordp name))))
        (raise "Defret-mutual requires a name as the first argument."))
       ((mv kwd-alist defrets)
        (extract-keywords `(defret-mutual ,name)
                          '(:mutual-recursion
                            :hints
                            :no-induction-hint
                            :skip-others
                            :instructions
                            :otf-flg) args nil))

       ((unless (consp defrets))
        (raise "Defret-mutual needs at least 1 defret/defretd form."))

       (defines-alist (get-defines-alist world))
       (mutual-recursion (let ((look (assoc :mutual-recursion kwd-alist)))
                           (if look
                               (cdr look)
                             (caar defines-alist))))
       ((unless mutual-recursion)
        (raise "Defret-mutual needs a mutual recursion created with defines to work on."))
       (guts (cdr (assoc mutual-recursion defines-alist)))
       ((unless guts)
        (raise "~x0 is not the name of a mutual recursion created with defines." mutual-recursion))
       ((defines-guts guts))
       ((unless guts.flag-defthm-macro)
        (raise "No flag defthm macro for ~x0." mutual-recursion))
       (defthms (defret-mutual-process-defrets defrets guts name world)))
    `(,guts.flag-defthm-macro
      ,name
      ,@defthms
      . ,(pass-kwd-args
          '(:hints :no-induction-hint :skip-others :instructions :otf-flg) kwd-alist))))

(defmacro defret-mutual (name &rest args)
  `(make-event
    (defret-mutual-fn ',name ',args (w state))))
