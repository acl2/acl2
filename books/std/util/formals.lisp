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
; Original author: Jared Davis <jared@centtech.com>

(in-package "STD")
(include-book "look-up")
(include-book "da-base")
(program)

(defxdoc extended-formals
  :parents (std/util define)
  :short "Extended syntax for function arguments that allows for built-in
guards, documentation, and macro-like keyword/optional arguments."

  :long "<p>Macros like @(see define) accept an extended formals syntax.  This
syntax properly extends the normal syntax for a function's arguments used by
@(see defun), so you can still use a plain list of variable names if you like.
But there are also some more interesting extensions.</p>

<p>Basic examples of some extended formals in a @('define'):</p>

@({
 (define split-up-string
   ((x stringp \"The string to split\")
    (separators (and (consp separators)
                     (character-listp separators))
     \"Letters to split on -- <b>dropped from the result!</b>\")
    &key
    (limit (or (not limit)
               (natp limit))
     \"Where to stop, @('nil') means @('(length x)')\"))
   ...)
})

<p>The general syntax for extended formals is:</p>

@({
  Formals ::= (Formal*                 ; ordinary formals
               [&optional OptFormal*]  ; optional positional formals
               [&key OptFormal*]       ; optional keyword formals
               )

  OptFormal ::= Formal          ; optional formal w/NIL default
              | (Formal 'val)   ; optional formal w/custom default

  Formal  ::= (varname Item*)

  Item    ::= xdoc       ; documentation string
            | guard      ; guard specifier
            | :key val   ; other additional options
})


<h4>@('&key') and @('&optional') arguments</h4>

<p>You can use @('&key') and @('&optional') as in @(see macro-args).  (Other
lambda-list keywords like @('&rest') aren't supported.)  When macros like
@('define') see these keywords, then instead of just producing a @('defun') we
will generate:</p>

<ul>
<li>A function, @('name-fn'),</li>
<li>A wrapper macro, @('name'),</li>
<li>A <see topic='@(url acl2::macro-aliases-table)'>macro alias</see> associating
@('name-fn') with @('name')</li>
</ul>

<p>The default values for these parameters work just like in ordinary macros.
The explicit quote serves to separate these from Items.</p>


<h4>Inline Documentation</h4>

<p>You can optionally describe your formals with some @(see xdoc)
documentation.  This description will be embedded within some generated
@('<dl>/<dt>/<dd>') tags that describe your function's interface.  You can
freely use @(see xdoc::markup) and @(see xdoc::preprocessor) directives.
Typically your descriptions should be short and should not include
document-structuring tags like @('<p>'), @('<ul>'), @('<h3>'), and so
forth.</p>


<h4>Inline Guards</h4>

<p>As a convenient shorthand, the @('guard') may be a single non-keyword
symbol, e.g., in @('split-up-string') above, the guard for @('x') is
@('(stringp x)').  To be more precise:</p>

<ul>
 <li>@('t') and @('nil') are treated literally, and</li>
 <li>Any other symbol @('g') is treated as short for @('(g var)')</li>
</ul>

<p>For more complex guards, you can also write down arbitrary terms, e.g.,
above @('separators') must be a non-empty character list.  We put a few
sensible restrictions here.  We require that a guard term must be at least a
cons to distinguish it from documentation, symbol guards, and keywords.  We
also require that it is not simply a quoted constant.  This ensures that guards
can be distinguished from default values in macro arguments.  For example,
compare:</p>

@({
     &key (x 'atom)     ;; x has no guard, default value 'atom
 vs. &key (x atom)      ;; x has guard (atom x), default value nil
 vs. &key ((x atom) '3) ;; x has guard (atom x), default value 3
})


<h4>Keyword/Value Options</h4>

<p>To make the formals syntax more flexible, other keyword/value options can be
embedded within the formal.</p>

<p>The valid keywords and their interpretations can vary from macro to macro.
For instance, @(see define) doesn't accept any keyword/value options, but @(see
defaggregate) fields have a @(':rule-classes') option.</p>



<h4>Additional Features</h4>

<p>Some other features of extended formals are not evident in their syntax.</p>

<p>We generally expect macros that take extended formals to automatically
recognize @(see acl2::stobj)s and insert appropriate @('(declare (xargs :stobjs
...))') forms.</p>

<p>Future work (not yet implemented): certain guards like @('stringp') and
@('(unsigned-byte-p 32 x)'), are recognized as @(see acl2::type-spec)s and
result in @(see type) declarations for the Lisp compiler.  This may
occasionally improve efficiency.</p>")

; Internal representation for extended formals

(def-primitive-aggregate formal
  (name    ; a legal-variablep, name of this formal
   guard   ; always a term, t for formals with no guard
   doc     ; always a string, "" for formals with no documentation
   opts    ; alist binding keywords to values
   )
  :tag :formal)

(defun formallist-p (x)
  (declare (xargs :guard t))
  (if (atom x)
      t
    (and (formal-p (car x))
         (formallist-p (cdr x)))))

(defun formallist->names (x)
  (declare (xargs :guard (formallist-p x)))
  (if (atom x)
      nil
    (cons (formal->name (car x))
          (formallist->names (cdr x)))))

(defun formallist->guards (x)
  (declare (xargs :guard (formallist-p x)))
  (if (atom x)
      nil
    (cons (formal->guard (car x))
          (formallist->guards (cdr x)))))

(defun formallist-collect-stobjs (x world)
  ;; Filter formals, returning only those formals that are stobjs
  (declare (xargs :guard (and (formallist-p x)
                              (plist-worldp world))))
  (cond ((atom x)
         nil)
        ((var-is-stobj-p (formal->name (car x)) world)
         (cons (car x) (formallist-collect-stobjs (cdr x) world)))
        (t
         (formallist-collect-stobjs (cdr x) world))))



; User-level syntax for extended formals.
;  (we're going to parse the user-level syntax into formal-p structures.)

(defun parse-formal-name
  ;; basically just recognizes valid formals
  (ctx      ; context for error messages
   varname  ; what the user has given as the variable name
   )
  (declare (xargs :guard t))
  (b* ((__function__ 'parse-formal-name)
       ((when (legal-variablep varname))
        varname)
       (fake-arglist (list varname))
       ((when (acl2::arglistp fake-arglist))
        (raise "~x0: formal ~x1: mysterious problem that Jared thinks should ~
                be impossible, please tell him that he is wrong." ctx varname)
        'default-valid-legal-variablep)
       ((mv & reason)
        (acl2::find-first-bad-arg fake-arglist)))
    (raise (concatenate 'string "~x0: formal ~x1 is invalid; it " reason)
           ctx varname)
    'default-valid-legal-variablep))

(defun check-formal-guard
  (ctx      ; context for error messages
   varname  ; name of this formal (for better error reporting)
   item     ; the symbolp the user wrote as a guard
   world)
  (b* ((__function__ 'check-formal-guard)
       (macro-args (getprop item 'acl2::macro-args :bad 'acl2::current-acl2-world world))
       ((unless (eq macro-args :bad))
        ;; The shorthand guard is a macro.  Can't really check anything.
        nil)
       ;; Not a macro.  It had better be a unary function.
       (formals (getprop item 'acl2::formals :bad 'acl2::current-acl2-world world))
       ((when (eq formals :bad))
        (raise "Error in ~x0: the guard for ~x1 is ~x2, but there is no ~
                function or macro named ~x2." ctx varname item))
       ((when (tuplep 1 formals))
        ;; Okay, seems fine.
        nil))
    (raise "Error in ~x0: the guard for ~x1 should take a single argument, ~
            but ~x2 takes ~x3 arguments."
           ctx varname item (len formals))))

(defun parse-formal-item
  ;; parses guard/doc item inside an extended formal
  ;;   (doesn't deal with keyword/value opts)
  (ctx      ; context for error messages
   varname  ; name of this formal
   item     ; the actual thing we're parsing
   guards   ; accumulator for guards (for this formal only)
   docs     ; accumulator for docs (for this formal only)
   world
   )
  "Returns (mv guards docs)"
  (declare (xargs :guard (legal-variablep varname)))
  (b* ((__function__ 'parse-formal-item)
       ((when (booleanp item))
        (mv (cons item guards) docs))
       ((when (symbolp item))
        (check-formal-guard ctx varname item world)
        (mv (cons `(,item ,varname) guards) docs))
       ((when (and (consp item)
                   (not (eq (car item) 'quote))))
        (mv (cons item guards) docs))
       ((when (stringp item))
        (mv guards (cons item docs))))
    (raise "~x0: formal ~x1: expected guard specifiers or documentation ~
            strings, but found ~x2."
           ctx varname item)
    (mv guards docs)))

(defun parse-formal-items (ctx varname items guards docs world)
  "Returns (mv guards docs)"
  (declare (xargs :guard (legal-variablep varname)))
  (b* ((__function__ 'parse-formal-items)
       ((when (not items))
        (mv guards docs))
       ((when (atom items))
        (raise "~x0: formal ~x1: extended formal items should be ~
                nil-terminated; found ~x2 as the final cdr."
               ctx varname items)
        (mv guards docs))
       ((mv guards docs)
        (parse-formal-item ctx varname (car items) guards docs world)))
    (parse-formal-items ctx varname (cdr items) guards docs world)))

(defun parse-formal
  (ctx        ; context for error messages
   formal     ; thing the user wrote for this formal
   legal-kwds ; what keywords are allowed in the item list
   world
   )
  "Returns a formal-p"
  (declare (xargs :guard t))
  (b* ((__function__ 'parse-formal)
       ((when (atom formal))
        (b* ((varname (parse-formal-name ctx formal)))
          (make-formal :name varname
                       :guard t
                       :doc ""
                       :opts nil)))
       (varname (parse-formal-name ctx (car formal)))
       (items   (cdr formal))
       ((mv opts items)  (extract-keywords (cons ctx varname) legal-kwds items nil))
       ((mv guards docs) (parse-formal-items ctx varname items nil nil world))
       (guard (cond ((atom guards) 't)
                    ((atom (cdr guards)) (car guards))
                    (t (raise "~x0: formal ~x1: expected a single guard term, ~
                               but found ~&2." ctx varname guards))))
       (doc   (cond ((atom docs) "")
                    ((atom (cdr docs)) (car docs))
                    (t (progn$
                        (raise "~x0: formal ~x1: expected a single xdoc ~
                                string, but found ~&2." ctx varname docs)
                        "")))))
    (make-formal :name varname
                 :guard guard
                 :doc doc
                 :opts opts)))

(defun parse-formals (ctx formals legal-kwds world)
  ;; Assumes lambda-list keywords have already been removed from formals.
  (declare (xargs :guard t))
  (b* ((__function__ 'parse-formals)
       ((when (not formals))
        nil)
       ((when (atom formals))
        (raise "~x0: expected formals to be nil-terminated, but found ~x1 as ~
                the final cdr." ctx formals)))
    (cons (parse-formal ctx (car formals) legal-kwds world)
          (parse-formals ctx (cdr formals) legal-kwds world))))



; Support for macro formals

(defun has-macro-args (x)
  (declare (xargs :guard t))
  (if (atom x)
      nil
    (or (acl2::lambda-keywordp (car x))
        (has-macro-args (cdr x)))))

(defun remove-macro-args
  (ctx     ; context for error messages
   formals ; list of unparsed formals
   seenp   ; have we seen &key or &optional yet?
   )
  ;; Generates a new list of (unparsed) formals, with the macro arguments
  ;; removed.  This is going to be the list of formals for the -fn.  We are
  ;; going to remove "&key" and "&optional" from formals, and also fix up
  ;; any keyword/optional formals that have default values.
  ;;
  ;; When an argument has a default value it looks like
  ;;   (foo 'default).
  ;; The quote here distinguishes it from an extended formal that has a guard,
  ;; e.g., (foo 'atom) has a default value of 'atom and no guard, whereas
  ;; (foo atom) is just a plain extended formal with no default value (well, a
  ;; default value of nil) and a guard of (atom foo).
  (declare (xargs :guard t))
  (b* ((__function__ 'remove-macro-args)
       ((when (atom formals))
        formals)
       ((cons arg1 rest) formals)
       ((when (or (eq arg1 '&key)
                  (eq arg1 '&optional)))
        (remove-macro-args ctx rest t))
       ((when (acl2::lambda-keywordp arg1))
        (raise "~x0: only &key and &optional macro-style arguments are ~
                allowed, but found ~x1." ctx arg1))
       ((unless seenp)
        ;; Haven't yet seen &key/&optional, so don't change any args yet.
        (cons arg1 (remove-macro-args ctx rest seenp)))

       ;; Saw &keyword/&optional already and this isn't another keyword.  So,
       ;; this is a real keyword/optional argument.  We need to remove any
       ;; default value.
       ((when (and (consp arg1)
                   (true-listp arg1)
                   (equal (len arg1) 2)
                   (consp (second arg1))
                   (eq (car (second arg1)) 'quote)))
        ;; Arg1 matches (foo 'value), so it has a default value to remove.
        ;; Change it to drop the default value.
        (cons (first arg1) (remove-macro-args ctx rest seenp))))

    ;; Else, it doesn't match (foo 'value), so leave it alone.
    (cons arg1 (remove-macro-args ctx rest seenp))))


(defun formals-for-macro
  ;; Remove extended formal stuff (guards, documentation) and just get down to
  ;; a list of variable names and &key/&optional stuff, which is suitable for
  ;; the formals for the wrapper macro.
  (ctx      ; context for error messages
   formals  ; list of unparsed formals
   seenp    ; have we seen any macro arguments yet
   )
  (declare (xargs :guard t))
  (b* ((__function__ 'formals-for-macro)
       ((when (atom formals))
        formals)
       ((cons arg1 rest) formals)
       ((when (or (eq arg1 '&key)
                  (eq arg1 '&optional)))
        (cons arg1 (formals-for-macro ctx rest t)))
       ((when (acl2::lambda-keywordp arg1))
        (raise "~x0: only &key and &optional macro-style arguments are ~
                allowed, but found ~x1." ctx arg1))
       ((unless seenp)
        ;; Haven't yet seen &key/&optional, so the only args should be ordinary
        ;; symbols and extended formals.  Keep just the name.  If it's a
        ;; extended formal then it has the form (name ...).
        (cons (if (atom arg1) arg1 (car arg1))
              (formals-for-macro ctx rest seenp)))

       ;; Saw &keyword/&optional already and this isn't another keyword.  So,
       ;; this is a real keyword/optional argument.  If there's a default value
       ;; we need to keep it.
       ((when (and (consp arg1)
                   (true-listp arg1)
                   (equal (len arg1) 2)
                   (consp (second arg1))
                   (eq (car (second arg1)) 'quote)))
        ;; Arg1 matches (extended-formal 'value).  We need to keep just
        ;; (name 'value)
        (let* ((eformal     (first arg1))
               (default-val (second arg1)) ;; already quoted
               (name        (if (atom eformal) eformal (car eformal))))
          (cons (list name default-val)
                (formals-for-macro ctx rest seenp)))))

    ;; Else, it doesn't match (foo 'value), so just do the name extraction like
    ;; normal.
    (cons (if (atom arg1) arg1 (car arg1))
          (formals-for-macro ctx rest seenp))))


(defun remove-macro-default-values (args)
  ;; Args might be, e.g., (a b c (d '3) (e '4))
  ;; We just want to remove the values from any args with default values.
  (declare (xargs :guard t))
  (cond ((atom args)
         nil)
        ((atom (car args))
         (cons (car args) (remove-macro-default-values (cdr args))))
        (t
         (cons (caar args) (remove-macro-default-values (cdr args))))))

(defun make-wrapper-macro (fnname fnname-fn formals)
  (declare (xargs :guard (and (symbolp fnname)
                              (symbolp fnname-fn))))
  (b* ((macro-formals  (formals-for-macro fnname formals nil))
       (fn-arg-names   (remove-macro-default-values
                        (set-difference-equal macro-formals '(&key &optional)))))
    `(defmacro ,fnname ,macro-formals
       (list ',fnname-fn . ,fn-arg-names))))
