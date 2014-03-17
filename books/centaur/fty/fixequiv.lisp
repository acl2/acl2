; FTY type support library
; Copyright (C) 2014 Centaur Technology
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
; Original author: Sol Swords <sswords@centtech.com>

(in-package "FTY")

(include-book "fixtype")
(include-book "std/util/formals" :dir :system)
(include-book "std/lists/mfc-utils" :dir :system)

;; NOTE: If we want to include this in define, obvs we can't have this
;; include-book, but all we really depend on is the DEFGUTS and
;; define-guts-alist definitions.
(include-book "std/util/defines" :dir :system)


(program)
(set-state-ok t)

(defxdoc deffixequiv
  :parents (fty)
  :short "Generates boilerplate theorems about fixing functions and equivalence relations."

  :long "<p>Part of an attempt to automate the proof discipline described at
@(see fixtype).  See also @(see deffixequiv-mutual) for a version that can be
used on mutually recursive functions created using @(see defines).</p>

<p>Deffixequiv generates theorems about typed arguments of a given function.
There are two ways to invoke it:</p>

@({
 (deffixequiv function-name
              ;; optional:
              :omit (a b)
              :hints (...)) ;; applied to all arguments
 })

<p>This form proves fixing and congruence theorems for each argument not
present in @(':omit').  It tries to derive the type of each argument from the
formal guard given to @(see define).  If the function was not created using
@(see define), then this will fail.</p>

<p>The following form may be used to explicitly specify what to do with each
argument, or to give hints for each argument's proof.  If a type is given
explicitly for each argument, then this can work on a functino not created
using @(see define):</p>

@({
  (deffixequiv function-name
         :args (a                ;; derive type from DEFINE
                (b :hints (...)) ;; derive type from DEFINE
                (c natp ...))     ;; type given explicitly
        :hints (...))   ;; applied to all arguments
 })

<p>This uses the given @(':args') to determine which formals to generate
theorems about.</p>

<p>To summarize the two choices, you may either provide @(':omit'), @(':args'),
or neither (equivalent to @(':omit nil')), but not both; generally, the
argument types are derived from @('define'), but they may instead be given
explicitly in the @(':args') case.</p>

<h3>Theorems generated</h3>

<p>In most cases, three theorems are generated for each argument.  Suppose our
function is @('(foo a b c)'), where @('c') is @('nat-equiv') congruent.</p>

@({
  ;; Prerequisite:
  (deffixtype nat :pred natp :fix nfix :equiv nat-equiv)

  (deffixequiv foo :args ((c nat)))
 })
<p>will generate the following theorems:</p>
@({
 (defthm foo-of-nfix-c
   (equal (foo a b (nfix c))
          (foo a b c)))

 (defthm foo-of-nfix-c-normalize-const
   (implies (syntaxp (and (quotep c)
                          (not (natp (cadr c)))))
            (equal (foo a b c)
                   (foo a b (nfix c)))))

 (defthm foo-nat-equiv-congruence-on-c
   (implies (nat-equiv c c-equiv)
            (equal (foo a b c)
                   (foo a b c-equiv)))
   :rule-classes :congruence)
 })

<p>Some fixtypes may have a predicate and/or fixing function that is either
expensive to execute or not executable.  In this case the second theorem, which
normalizes constant values by fixing them to the correct type, is not a good
one and can be skipped by either:</p>

<ul>
<li>Declaring the fixtype using @(':executablep nil'):
@({
  (deffixtype nat :pred natp :fix nfix :equiv nat-equiv
                  :executablep nil)
 })
</li>
<li>Or using @(':skip-const-thm t') among the keywords for the argument:
@({
  (deffixequiv foo :args ((c nat :skip-const-thm t)))
 })
</li>
</ul>
")

(defxdoc deffixequiv-mutual
  :parents (fty)
  :short "@(see deffixequiv) for mutually-recursive functions."
  :long "<p>Part of an attempt to automate the proof discipline described at
@(see fixtype).  Before reading this, please also read @(see deffixequiv).</p>

<p>Important Note: @('deffixequiv-mutual') will not work if the mutual
recursion in question was not created using @(see defines).</p>

<p>@('deffixequiv-mutual') proves the same theorems as @('deffixequiv'), but
using the mutual induction given by the flag function of some mutual recursion.
A given @('deffixequiv-mutual') event proves one mutually-inductive theorem of
which the individual @('function-of-fix-arg') theorems are corollaries, then
uses these to prove the constant-normalization and congruence theorems.  (These
three theorems are discussed in @(see deffixequiv).</p>

<p>As with @(see deffixequiv), you have the choice of either provinding
@(':omit'), @('args'), or both.  However, for @('deffixequiv-mutual') the
syntax of these parameters is extended, as shown in the following examples:</p>

@({
 ;; Prerequisite: types defined by deffixtype
 (deffixtype nat :pred natp :fix nfix :equiv nat-equiv)
 (deffixtype nat-list :pred nat-listp :fix nat-list-fix :equiv nat-list-equiv)
 (deffixtype int :pred integerp :fix ifix :equiv int-equiv)
 (deffixtype string :pred stringp :fix string-fix :equiv string-equiv)
 
 ;; Prerequisite: functions created using defines
 (defines foo-bar-mutual-rec
   (define foo ((x integerp) y (z natp))
     :flag f
     ...)
   (define bar ((x integerp) y (z nat-listp))
     :flag b
     ...))

 ;; Possible deffixequiv-mutual invocations:

 ;; Derives all argument types from guards and proves them all in one mutual
 ;; induction.
 (deffixequiv-mutual foo-bar-mutual-rec)
 ;; Note: use name of defines form -- foo-bar-mutual-rec
 ;;  -- not name of a function


 ;; Proves only things pertaining to the X argument of both functions
 (deffixequiv-mutual foo-bar-mutual-rec :args (x))
 ;; Same:
 (deffixequiv-mutual foo-bar-mutual-rec :omit (y z))

 ;; Proves string congruence of Y on both functions
 (deffixequiv-mutual foo-bar-mutual-rec :args ((y string)))

 ;; Proves string congruence of y in foo and string-listp in bar
 (deffixequiv-mutual foo-bar-mutual-rec
                     :args ((foo (y stringp))
                            (bar (y string-listp))))

 ;; Omit x in foo and y in bar
 (deffixequiv-mutual foo-bar-mutual-rec
                     :omit ((foo x) (bar y)))

 ;; Various combinations of :args usages
 (deffixequiv-mutual foo-bar-mutual-rec
    :args (x                       ;; all functions, automatic type
           (z natp :hints (...))   ;; all functions, explicit type
           (foo (y stringp :skip-const-thm t :hints (...)))
                                   ;; foo only, explicit type
           (bar (z nat-listp)))    ;; override non-function-specific entry
    :hints (...))  ;; hints for the whole inductive proof
 })

")

(defun fixequivs->events (x)
  (if (atom x)
      nil
    (cons (fixequiv-events (car x))
          (fixequivs->events (cdr x)))))

(defun find-formal-by-name (varname formals)
  (if (atom formals)
      nil
    (if (eq (std::formal->name (car formals)) varname)
        (car formals)
      (find-formal-by-name varname (cdr formals)))))

(defconst *deffixequiv-keywords*
  '(:args :omit :hints :verbosep))

(defun fixequiv-type-from-guard (guard)
  (and (std::tuplep 2 guard)
       (car guard)))
    

(defun fixequiv-from-define-formal (fn formal hints state)
  (b* (((std::formal fm) formal)
       (type (fixequiv-type-from-guard fm.guard))
       ((unless type) nil)
       (formals (fgetprop fn 'acl2::formals :none (w state)))
       (event (deffixequiv-basic-parse (cons fn formals) fm.name type
                `(:skip-ok t :hints ,hints) state)))
    (and event (list event))))

(defun fixequivs-from-define-formals (fn omit formals hints state)
  (if (atom formals)
      nil
    (append (and (not (member (std::formal->name (car formals)) omit))
                 (fixequiv-from-define-formal fn (car formals) hints state))
            (fixequivs-from-define-formals fn omit (cdr formals) hints state))))

(defun remove-key (key kwlist)
  (b* ((look (member key kwlist))
       ((unless look) kwlist)
       (pre (take (- (len kwlist) (len look)) kwlist)))
    (append pre (cddr look))))

(defun fixequiv-from-explicit-arg (fn arg gutsformals formals hints state)
  (b* ((__function__ 'deffixequiv)
       ((mv var type/opts) (if (atom arg) (mv arg nil) (mv (car arg) (cdr arg))))
       ((mv type opts) (if (keywordp (car type/opts))
                           (mv nil type/opts)
                         (mv (car type/opts) (cdr type/opts))))
       (type (or type
                 (b* ((formal (find-formal-by-name var gutsformals))
                      ((unless formal)
                       (if gutsformals
                           (raise "~x0 is not a formal of function ~x1" var fn)
                         (raise "Can't derive argument types from ~x0 because it ~
                        wasn't created with DEFINE." fn)))
                      ((std::formal fm) formal)
                      (type (fixequiv-type-from-guard fm.guard))
                      ((unless type)
                       (raise "Argument ~x0 of function ~x1 wasn't given a ~
                               (unary) type in its DEFINE declaration" var fn)))
                   type)))
       (arg-hints (cadr (member :hints opts)))
       (opts-without-hints (remove-key :hints opts))
       (opts (append `(:hints ,(append arg-hints hints)) opts-without-hints)))
    (deffixequiv-basic-parse (cons fn formals)
      var type opts state)))

(defun fixequivs-from-explicit-args (fn args gutsformals formals hints state)
  (if (atom args)
      nil
    (let ((event (fixequiv-from-explicit-arg fn (car args) gutsformals formals hints state)))
      (if event
          (cons event
                (fixequivs-from-explicit-args fn (cdr args) gutsformals formals hints state))
        (fixequivs-from-explicit-args fn (cdr args) gutsformals formals hints state)))))


(defun deffixequiv-fn (fn kw-args state)
  (b* ((__function__ 'deffixequiv)
       (world (w state))
       ((mv kwd-alist rest)
        (extract-keywords 'deffixequiv *deffixequiv-keywords* kw-args nil))
       ((when rest) (raise "Error: extra arguments: ~x0" rest))
       
       (guts-alist (std::get-define-guts-alist world))
       (guts (cdr (assoc fn guts-alist)))
       ;; It might be an error if there's no define table entry, but it doesn't
       ;; need to be if the arg types are given explicitly.
       (gutsformals (and guts (std::defguts->formals guts)))
       (args (cdr (assoc :args kwd-alist)))
       (hints (cdr (assoc :hints kwd-alist)))
       ((when (and (not args) (not guts)))
        (raise "Deffixequiv requires either explicit types for the arguments ~
                to be considered, or for the function to have DEFINE info, ~
                which ~x0 does not." fn))
       (fn (if guts (std::defguts->name-fn guts) fn))
       (omit (cdr (assoc :omit kwd-alist)))
       ((when (and args omit))
        (raise "Why would you provide both :args and :omit?")))
    (if args
        (fixequivs-from-explicit-args
         fn args gutsformals
         (fgetprop fn 'acl2::formals :none (w state)) hints state)
      (fixequivs-from-define-formals fn omit gutsformals hints state))))

(defmacro deffixequiv (fn &rest keys)
  (b* ((verbosep (let ((lst (member :verbosep keys)))
                   (and lst (cadr lst)))))
    `(with-output ,@(and (not verbosep) '(:off :all)) :stack :push
       (make-event
        (cons 'progn
              (fixequivs->events
               (deffixequiv-fn ',fn ',keys state)))))))


(defconst *deffixequiv-mutual-keywords*
  '(:args :omit :verbosep :hints))


(defun find-define-guts-by-fn/flag-name (fn gutslist)
  (if (atom gutslist)
      nil
    (if (or (eq fn (std::defguts->name (car gutslist)))
            (eq fn (std::defguts->name-fn (car gutslist)))
            (eq fn (cdr (assoc :flag (std::defguts->kwd-alist (car gutslist))))))
        (car gutslist)
      (find-define-guts-by-fn/flag-name fn (cdr gutslist)))))

(defun find-entry-by-fn/flag-name (guts al)
  (b* (((std::defguts guts) guts))
    (or (assoc guts.name al)
        (assoc guts.name-fn al)
        (assoc (cdr (assoc :flag guts.kwd-alist)) al))))

(defun args->varnames (args)
  (if (atom args)
      nil
    (cons (if (atom (car args)) (car args) (caar args))
          (args->varnames (cdr args)))))

(defun keep-args (args keep-names)
  (if (atom args)
      nil
    (if (member (if (atom (car args)) (car args) (caar args)) keep-names)
        (cons (car args) (keep-args (cdr args) keep-names))
      (keep-args (cdr args) keep-names))))


(defun mutual-fixequivs-from-explicit-args (fn-args univ-args gutslist state)
  (b* (((when (atom gutslist)) nil)
       (guts (car gutslist))
       ((std::defguts guts) guts)
       (formal-names (std::formallist->names guts.formals))
       (fn-fn-args (cdr (find-entry-by-fn/flag-name guts fn-args)))
       ;; We include an arg from the univ-args if
       ;; (1) it is among the function's formals and
       ;; (2) it is not overridden in the fn-args.
       (fn-univ-args (keep-args univ-args
                                (set-difference-eq formal-names
                                                   (args->varnames fn-fn-args))))
       (args (append fn-fn-args fn-univ-args))
       (fixequivs (fixequivs-from-explicit-args
                   guts.name-fn args guts.formals formal-names nil state)))
    (cons (cons guts.name fixequivs)
          (mutual-fixequivs-from-explicit-args fn-args univ-args (cdr gutslist) state))))
             
                 
(defun mutual-fixequivs-from-defines (fn-omit univ-omit gutslist state)
  (b* (((when (atom gutslist)) nil)
       ((std::defguts guts) (car gutslist))
       (omit-look (or (assoc guts.name fn-omit)
                      (assoc guts.name-fn fn-omit)
                      (assoc (cdr (assoc :flag guts.kwd-alist)) fn-omit)))
       (fixequivs (fixequivs-from-define-formals
                   guts.name-fn (append univ-omit (cdr omit-look))
                   guts.formals nil state)))
    (cons (cons guts.name fixequivs)
          (mutual-fixequivs-from-defines fn-omit univ-omit (cdr gutslist) state))))

(defun fixequivs->fix-thms-with-flags (flag fixequivs)
  (if (atom fixequivs)
      nil
    (cons (append (fixequiv->fix-thm (car fixequivs)) `(:flag ,flag))
          (fixequivs->fix-thms-with-flags flag (cdr fixequivs)))))
       
(defun fn-mutual-fixequivs->inductive-fix-thms (fn fixequivs gutslist)
  (b* ((guts (find-define-guts-by-fn/flag-name fn gutslist))
       ((unless guts) (er hard? 'deffixequiv-mutual "function name not found?"))
       (flag (std::guts->flag guts)))
    (fixequivs->fix-thms-with-flags flag fixequivs)))


(defun mutual-fixequivs->inductive-fix-thms (fixequiv-al gutslist)
  (if (atom fixequiv-al)
      nil
    (append (fn-mutual-fixequivs->inductive-fix-thms
             (caar fixequiv-al) (cdar fixequiv-al) gutslist)
            (mutual-fixequivs->inductive-fix-thms (cdr fixequiv-al) gutslist))))

(defun mutual-fixequivs->fix-thm (fixequiv-al defines-entry kwd-alist)
  (b* ((thm-macro (std::defines-guts->flag-defthm-macro defines-entry))
       (hints (cdr (assoc :hints kwd-alist))))
    `(with-output :stack :pop
       (,thm-macro
        ,@(mutual-fixequivs->inductive-fix-thms
           fixequiv-al (std::defines-guts->gutslist defines-entry))
        :hints ,hints))))
  
(defun fixequivs->const/cong-thms (fixequivs)
  (if (atom fixequivs)
      nil
    (let* ((rest (fixequivs->const/cong-thms (cdr fixequivs)))
           (cong-thm (fixequiv->cong-thm (car fixequivs)))
           (const-thm (fixequiv->const-thm (car fixequivs)))
           (events (cons cong-thm rest)))
      (if const-thm
          (cons const-thm events)
        events))))

(defun mutual-fixequivs->const/cong-thms (fixequiv-al)
  (if (atom fixequiv-al)
      nil
    (append (fixequivs->const/cong-thms (cdar fixequiv-al))
            (mutual-fixequivs->const/cong-thms (cdr fixequiv-al)))))

(defun get-atoms (x)
  (if (atom x)
      nil
    (if (atom (car x))
        (cons (car x) (get-atoms (cdr x)))
      (get-atoms (cdr x)))))

(defun get-conses (x)
  (if (atom x)
      nil
    (if (atom (car x))
        (get-conses (cdr x))
      (cons (car x) (get-conses (cdr x))))))

(defun get-fn-args (args gutslist)
  (if (atom args)
      nil
    (if (and (consp (car args))
             (find-define-guts-by-fn/flag-name (caar args) gutslist))
        (cons (car args) (get-fn-args (cdr args) gutslist))
      (get-fn-args (cdr args) gutslist))))

(defun get-nonfn-args (args gutslist)
  (if (atom args)
      nil
    (if (and (consp (car args))
             (find-define-guts-by-fn/flag-name (caar args) gutslist))
        (get-nonfn-args (cdr args) gutslist)
      (cons (car args) (get-nonfn-args (cdr args) gutslist)))))

(defun deffixequiv-mutual-fn (name kw-args state)
  (b* ((__function__ 'deffixequiv-mutual)
       (world (w state))
       ((mv kwd-alist rest)
        (extract-keywords 'deffixequiv-mutual *deffixequiv-mutual-keywords* kw-args nil))
       ((when rest) (raise "Error: extra arguments: ~x0" rest))
       (defines-alist (std::get-defines-alist world))
       (defines-entry (cdr (assoc name defines-alist)))
       ((unless (and defines-entry
                     (std::defines-guts->flag-defthm-macro defines-entry)))
        (raise "Deffixequiv-mutual is intended to work on mutual recursions ~
                created using DEFINES with a flag function.  You should give ~
                the name of the defines form, not the name of the function."))
       (args (cdr (assoc :args kwd-alist)))
       (omit (cdr (assoc :omit kwd-alist)))
       (gutslist (std::defines-guts->gutslist defines-entry))
       (univ-args (get-nonfn-args args gutslist))
       (fn-args (get-fn-args args gutslist))
       (univ-omit (get-atoms omit))
       (fn-omit (get-conses omit))
       ((when (and args omit))
        (raise "Why would you provide both :args and :omit?"))
       (fns/fixequivs (if args
                          (mutual-fixequivs-from-explicit-args fn-args univ-args gutslist state)
                        (mutual-fixequivs-from-defines fn-omit univ-omit gutslist state))))
    (cons (mutual-fixequivs->fix-thm fns/fixequivs defines-entry kwd-alist)
          (mutual-fixequivs->const/cong-thms fns/fixequivs))))

(defmacro deffixequiv-mutual (name &rest keys)
  (b* ((verbosep (let ((lst (member :verbosep keys)))
                   (and lst (cadr lst)))))
    `(with-output ,@(and (not verbosep) '(:off :all)) :stack :push
       (make-event
        (cons 'progn
              (deffixequiv-mutual-fn ',name ',keys state))))))
       
