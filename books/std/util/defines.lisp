; Standard Utilities Library
; Copyright (C) 2008-2014 Centaur Technology
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

<li>Automatic @(see flag::make-flag) integration, so you can easily prove
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
    (defthm-my-flatten-term-flag
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
function that will be introduced by @(see flag::make-flag).</p>

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
enabled before we processing these events.</p>

<p>Note that individual @('define')s can have their own other-events.  All of
these individual sections are processed (with their own local scopes) before
any global @('other-events').</p>

<h4>Global Options</h4>

<dl>

<dt>:mode</dt>
<dt>:guard-hints, :guard-debug, :verify-guards</dt>
<dt>:well-founded-relation, :hints</dt>
<dt>:otf-flg</dt>

<dd>In an ordinary @(see mutual-recursion), each of these @(see xargs) style
options can be attached to any @('defun') in the clique.  But we usually think
of these as global options to the whole clique, so we make them available as
top-level options to the @('defines') form.  In the implementation, we just
attach these options to the first @('defun') form generated.</dd>


<dt>:prepwork</dt>

<dd>Arbitrary events to be submitted before the definitions.  Typically this
might include @(see in-theory) calls, one-off supporting lemmas, etc.  Prepwork
is not automatically @(see local), so lemmas and theory changes should usually
be explicitly made @(see local).</dd>

<dd>Note that each individual @('define') may have its own @(':prepwork')
section.  All of these sections will be appended together in order, with the
global @(':prepwork') coming first, and submitted before the definitions.</dd>


<dt>:parents, :short, :long</dt>

<dd>These are global @(see xdoc) options that will be associated with the
@('clique-name') for this @('defines').</dd>

<dd>Note that each individual @('define') may separately have its own
documentation and rest-events.  As a convenience, if global documentation is
provided while individual documentation is not, a basic topic will be created
whose @(':parents') point at the @('clique-name').</dd>

<dd>BOZO does this make sense?  What if clique-name agrees with a function's
name?  Are we going to accidentally overwrite it?  This is all pretty subtle
and we should go through the various cases and consider whether they make
sense.</dd>


<dt>:ignore-ok val</dt>
<dt>:irrelevant-formals-ok val</dt>
<dt>:bogus-ok val</dt>

<dd>Submit @(see set-ignore-ok), @(see set-irrelevant-formals-ok), and/or
@(see set-bogus-mutual-recursion-ok) forms before the definitions.  These
options are @(see local) to the definitions; they do not affect the
@('other-events') or any later events.</dd>

</dl>



<p>Global Options</p>

@({
     :flag nil   - don't create a flag function
     :flag name  - override the name of the flag function
                   (default is clique-name-flag)
     :flag-var var - use VAR instead of FLAG as the name for the
                     flag variable
     :flag-defthm-macro name - override name of the flag macro
     :flag-hints hints - hints for make-flag
})

<p>Each define can also have a :flag-name option, which governs the name for
its flag in the flag-function.</p>



")

(defmacro defines (name &rest args)
  `(make-event (b* ((world (w state))
                    (event (defines-fn ',name ',args world)))
                 (value event))))


(defconst *defines-xargs-keywords*
  ;; Subset of the *xargs-keywords* that are not individually tailored for
  ;; each function.  We'll stick these into the xargs for the first function.
  ;; ACL2 checks that all the functions agree on these settings.
  '(
    ;; :guard -- no, individual
    ;; :measure -- no, individual
    ;; :non-executable -- no, individual
    ;; :split-types -- no, individual
    ;; :ruler-extenders -- no, individual
    ;; :normalize -- no, individual
    ;; :stobjs -- no, individual
    :guard-hints ;; Appended to guard-hints for all sub-functions.
    :hints       ;; Appended to hints for all sub-functions.
    :guard-debug ;; Must agree with any individual guard-debug settings.
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
     :flag-defthm-macro
     :flag-hints
     )
   *defines-xargs-keywords*))

(defun parse-defines (ctx forms world)
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
       (guts1 (parse-define name args world)))
    (cons guts1 (parse-defines ctx (cdr forms) world))))

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




(defun make-fn-defsection (guts cliquename)
  (b* (((defguts guts) guts)
       (short      (getarg :short          nil guts.kwd-alist))
       (long       (getarg :long           nil guts.kwd-alist))
       (parents    (getarg :parents        nil guts.kwd-alist))
       (parents    (if (assoc :parents guts.kwd-alist)
                       parents
                     (and cliquename (list cliquename)))))

    `((defsection ,guts.name
        ,@(and parents `(:parents ,parents))
        ,@(and short   `(:short ,short))
        ,@(and long    `(:long ,long))
        (make-event
         (let* ((world (w state))
                (events (returnspec-thms ',guts.name-fn
                                         ',guts.returnspecs
                                         world)))
           `(progn . ,events)))
        . ,guts.rest-events)
      ,(add-signature-from-guts guts))))


(defun collect-fn-defsections (gutslist cliquename)
  (if (atom gutslist)
      nil
    (append (make-fn-defsection (car gutslist) cliquename)
            (collect-fn-defsections (cdr gutslist) cliquename))))


(defun collect-flag-mapping (gutslist)
  (if (atom gutslist)
      nil
    (cons (cons (defguts->name-fn (car gutslist))
                (or (cdr (assoc :flag (defguts->kwd-alist (car gutslist))))
                    (defguts->name-fn (car gutslist))))
          (collect-flag-mapping (cdr gutslist)))))


(defun defines-fn (name args world)
  (declare (xargs :guard (plist-worldp world)))
  (b* ((__function__ 'defines)
       ((unless (symbolp name))
        (raise "Expected name to be a symbol, but found ~x0." name))

       ((mv main-stuff rest-events) (split-/// name args))
       ((mv kwd-alist defs)
        (extract-keywords name *defines-keywords* main-stuff nil))
       (gutslist (parse-defines name defs world))

       ((unless (consp (cdr gutslist)))
        (raise "Error in ~x0: expected more than one function." name))

       (short      (getarg :short          nil kwd-alist))
       (long       (getarg :long           nil kwd-alist))
       (parents    (getarg :parents        nil kwd-alist))
       (parents    (if (assoc :parents kwd-alist)
                       parents
                     (xdoc::get-default-parents world)))
       (want-xdoc-p (or short long parents))

       (prepwork (getarg :prepwork nil kwd-alist))
       ((unless (true-listp prepwork))
        (raise "Error in ~x0: expected :prepwork to be a true-listp, but found ~x1."
               name prepwork))
       (prepwork    (append prepwork (collect-prepworks gutslist)))
       (macros      (collect-macros gutslist))
       (set-ignores (make-ignore-events name kwd-alist gutslist))

       (extra-xargs (get-xargs-from-kwd-alist kwd-alist))
       (orig-defs   (collect-main-defs gutslist))
       (final-defs  (if extra-xargs
                        ;; Stick them into the first def.
                        (cons (append (take 3 (car orig-defs))
                                      `((declare (xargs . ,extra-xargs)))
                                      (nthcdr 3 (car orig-defs)))
                              (cdr orig-defs))
                      orig-defs))
       (mutual-rec  (cons 'mutual-recursion final-defs))
       (aliases     (collect-macro-aliases gutslist))
       (guts-table-exts (collect-guts-alist-exts gutslist))

       (fnnames (collect-names-from-guts gutslist))
       (fn-sections (collect-fn-defsections gutslist
                                            (and want-xdoc-p name)))

       (flag-name (if (assoc :flag kwd-alist)
                      (cdr (assoc :flag kwd-alist))
                    (intern-in-package-of-symbol
                     (concatenate 'string (symbol-name name) "-FLAG")
                     name)))
       (flag-var          (getarg :flag-var nil kwd-alist))
       (flag-defthm-macro (getarg :flag-defthm-macro nil kwd-alist))
       (flag-hints        (getarg :flag-hints nil kwd-alist))
       (flag-mapping      (collect-flag-mapping gutslist)))

    `(encapsulate nil
       ,@prepwork
       (defsection ,name
         ,@(and parents `(:parents ,parents))
         ,@(and short   `(:short ,short))
         ,@(and long    `(:long ,long))
         ,@macros
         ,@(if set-ignores
               `((encapsulate ()
                   ,@set-ignores
                   ,mutual-rec))
             `(,mutual-rec))
         ,@aliases
         ,@guts-table-exts)

       ,@(and flag-name
              `((flag::make-flag ,flag-name ,(defguts->name-fn (car gutslist))
                                 :flag-mapping ,flag-mapping
                                 ,@(and flag-defthm-macro
                                        `(:defthm-macro-name ,flag-defthm-macro))
                                 ,@(and flag-var `(:flag-var ,flag-var))
                                 :hints ,flag-hints)))

       (local
        (make-event
         (if (logic-mode-p ',(defguts->name-fn (car gutslist)) (w state))
             '(in-theory (enable . ,fnnames))
           '(value-triple :invisible))))

       (defsection rest-events
         ,@(and want-xdoc-p `(:extension ,name))
         ,@fn-sections
         . ,rest-events))))



