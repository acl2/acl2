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
; Modified by David Rager <ragerdl@cs.utexas.edu> with minor improvements
; Modified by Sol Swords <sswords@centtech.com> to add untranslate support
; Modified by Shilpi Goel <shilpi@centtech.com> to add config and :after-returns support

(in-package "STD")
(include-book "formals")
(include-book "returnspecs")
(include-book "xdoc/fmt-to-str-orig" :dir :system)
(include-book "tools/mv-nth" :dir :system)
(include-book "kestrel/utilities/make-termination-theorem" :dir :system)
(set-state-ok t)
(program)

(defun bootstrap-revappend-chars-aux (x n xl y)
  (declare (type string x)
           (type unsigned-byte n xl))
  (if (eql n xl)
      y
    (bootstrap-revappend-chars-aux x
                                   (the unsigned-byte (+ 1 n))
                                   xl
                                   (cons (char x n) y))))

(defun bootstrap-revappend-chars (x y)
  (bootstrap-revappend-chars-aux x 0 (length x) y))

(defun bootstrap-html-encode-str (x n xl acc)
  ;; Revappend the HTML encoding of X (e.g., & --> &amp;) onto ACC.
  (declare (type string x)
           (type unsigned-byte n xl))
  (b* (((when (eql n xl))
        acc)
       (char1 (char x n))
       (acc   (case char1
                (#\< (list* #\; #\t #\l #\& acc))         ;; "&lt;" (in reverse)
                (#\> (list* #\; #\t #\g #\& acc))         ;; "&gt;"
                (#\& (list* #\; #\p #\m #\a #\& acc))     ;; "&amp;"
                (#\" (list* #\; #\t #\o #\u #\q #\& acc)) ;; "&quot;"
                (t   (cons char1 acc)))))
    (bootstrap-html-encode-str x (the unsigned-byte (+ 1 n)) xl acc)))

(defxdoc define
  :parents (std/util)
  :short "A very fine alternative to @(see defun)."

  :long "<h3>Introduction</h3>

<p>@('define') is an extension of @('defun')/@('defund') with:</p>

<ul>

<li>Richer @('formals') lists that permit keyword/optional arguments, embedded
guards and documentation, automatically infer @(see acl2::stobj) declarations,
etc.</li>

<li>A more concise @(see xargs) syntax that also adds control over other
settings like @(see set-ignore-ok), @(see set-irrelevant-formals-ok), and
inlining.</li>

<li>A concise syntax for naming return values, documenting them, and proving
basic theorems (e.g., type-like theorems) about them.</li>

<li>Integration with @(see xdoc) with function signatures derived and a @(see
defsection)-like ability to associate related theorems with your function.</li>

<li>Automatic binding of @('__function__') to the name of the function, which
can be useful in error messages (see, e.g., @(see raise)) and, on CCL at least,
appears to produce identical compiled output when @('__function__') isn't used
in the body.</li>

</ul>

<p>The general form of @('define') is:</p>

@({
 (define name formals
   main-stuff
   [/// other-events])     ;; optional, starts with the symbol ///
})

<p>There's nothing special about the @('name'), it's just the name of the new
function to be defined, as in @(see defun).  The other parts all have their own
syntax and features to cover, and we address them in turn.</p>

<p>The formal have many features; see @(see extended-formals).  Besides the
ordinary extended-formals utilities, they can also include @(':type')
declarations; see @(see acl2::type-spec).  For instance:</p>

@({
  (x oddp :type integer)
  (y evenp :type (integer 0 *))
})


<h3>The Main Stuff</h3>

<p>After the formals we get to the main part of the definition.  This section
is a mixed list that may contain:</p>

<ul>
<li><i>Extended options</i> of the form @(':name value')</li>
<li>Declarations of the form @('(declare ...)')</li>
<li>Traditional documentation strings, i.e., @('\"...\"')</li>
<li>The function's body, a term</li>
</ul>

<p>Except for the extended options, this is just like @('defun').</p>

<p>Extended options can go <b>anywhere</b> between the formals and the special
separator @('///') (if any) or the end of the @('define').  Here is a contrived
example:</p>

@({
 (define parse-foo (channel n &optional (state 'state))

   :parents (parser) ;; extended option

   ;; declarations/docstrings must come before body, as in defun
   (declare (type integer n))
   (declare (ignorable channel))
   \"Traditional doc string that the xdoc system ignores.\"
   (declare (xargs :normalize nil))

   :guard (< 17 n) ;; extended option

   (b* ((next (peek-char channel state))  ;; function's body
        ...)
      (mv result state))

   :measure (file-measure channel state)  ;; more extended opts.
   :hints ((\"Goal\" ...))
   :guard-debug t)
})

<p>How does this work, exactly?  Ordinarily, @('defun') distinguishes the
function's body from documentation strings and declarations using a simple
rule: the last item is the function's body, and everything before it must be a
declaration or documentation string.  For @('define'), we simply add a
preprocessing step:</p>

<ul>
<li>First, all of the extended options are extracted.</li>
<li>Then, the remaining parts are handled using the ordinary @('defun') rule.</li>
</ul>

<p>There is one special case where this approach is <b>incompatible</b> with
@('defun'): if your function's body is nothing more than a keyword symbol,
e.g.,</p>

@({
 (defun returns-foo (x)
   (declare (ignore x))
   :foo)
})

<p>then it cannot be converted into a @('define') since the body looks like
a (malformed) extended option.  I considered workarounds to avoid this, but
decided that it is better to just live with not being able to define these
kinds of functions.  They are very weird, anyway.</p>

<h4>Basic Extended Options</h4>

<p>All @(see xargs) are available as extended options (though we provide an
additional option for @(':verify-guards') --- see below).  In practice this
just makes things more concise and better looking, e.g., compare:</p>

@({
 (defun strpos-fast (x y n xl yl)
   (declare (xargs :guard (and ...)
                   :measure (nfix ...)))
   ...)
 vs.
 (define strpos-fast (x y n xl yl)
   :guard (and ...)
   :measure (nfix ...)
   ...)
})

<p>See @(see define-guards) for discussion of the various ways guards can be
given, additionally.</p>

<p>Some additional minor options include:</p>

<dl>

<dt>@(':enabled val')</dt>

<dd>By default the function will be disabled after the @('other-events') are
processed.  If @(':enabled t') is provided, we will leave it enabled,
instead.</dd>

<dt>@(':ignore-ok val')</dt>

<dd>Submits @('(set-ignore-ok val)') before the definition.  This option is
local to the @('define') only and does not affect the @('other-events').</dd>

<dt>@(':irrelevant-formals-ok val')</dt>

<dd>Submits @('(set-irrelevant-formals-ok val)') before the definition; local
to this @('define') only and not to any @('other-events').</dd>

<dt>@(':inline val')</dt>

<dd>By default @('val') is @(':default') and we produce an ordinary function
that is neither inline or notinline.  When @(':inline t') is provided, we
create an <i>inline</i> function as in @(see defun-inline); the function will
have an ugly name like @('foo$inline'), so we'll also set up a @('foo') macro
and appropriate macro aliases.  When @(':inline nil') is provided, we create a
<i>notinline</i> function as in @(see defun-notinline); the function will have
an ugly name like @('foo$notinline'), so we will again set up a macro and
appropriate macro aliases.</dd>

<dt>@(':parents'), @(':short'), @(':long')</dt>

<dd>These are @(see defxdoc)-style options for documenting the function.  They
are passed to a @('defsection') for this definition.</dd>

<dt>@(':prepwork events')</dt>

<dd>These are any arbitrary events you want to put before the definition
itself, for instance it might include @('-aux') functions or local lemmas
needed for termination.</dd>

<dt>@(':t-proof val')</dt>

<dd>By default, the termination proof is lost after admitting a function.
But if @(':t-proof t') is provided, we will create a theorem without
any rule-classes that holds the proof of termination for this function and
measure.</dd>

<dt>@(':verify-guards val')</dt>

<dd>The value @('val') can be one of the following: @('t'), @('nil'), or
@(':after-returns').  The first two correspond to what is described in @(see
xargs), but the third option is specific to @('define').  The keyword
@(':after-returns') indicates that the guards of the function are to be
verified after the @(see returns-specifiers).</dd>

<dt>@(':no-function bool')</dt>

<dd>(Advanced/obscure) By default, @('define') will automatically bind
@('__function__') to the name of your function.  This binding can change how
ACL2 classifies @(':definition') rules by promoting @(':definition') into
@(':abbreviation') rules.  When porting legacy libraries to @('define'), this
difference can sometimes cause problems in later theorems.  Setting
@(':no-function t') will avoid binding @('__function__') for better backwards
compatibility.</dd>

<dt>@(':hooks hooks')</dt>

<dd>(Advanced feature).  Override which @(see post-define-hook)s are to be
executed.  For instance, @(':hooks nil') can be used to disable all such
hooks.</dd>

</dl>

<h5>Configuration Object</h5>

<p>A configuration object can also be defined to specify some extended options;
here's an example.</p>

@({ (make-define-config 
     :inline t 
     :no-function t) })

<p>As of now, the following options can be set through the configuration
object:</p>

@(`(:code *define-config-keywords*)`) <br/>

<p>A configuration object can be used to set these options across multiple
@('define')s.  However, <i>a configuration object's settings are local to a
book.</i> Of course, the object can be changed inside a book as many times as
you want.</p>

<p>Extended options provided in a @('define') will override those set by the
configuration object.  Additionally, the @(':hooks') option in the
configuration object will override any default post-define hook specified using
@('add-default-post-define-hook').</p>

<h4>@('Returns') Specifications</h4>

<p>See @(see returns-specifiers).</p>

<h3>The Other Events</h3>

<p>The final part of a @('define') is an area for any arbitrary events to be
put.  These events will follow the function's definition, but will be submitted
<b>before</b> disabling the function.</p>

<p>Any event can be included here, but this space is generally intended for
theorems that are \"about\" the function that has just been defined.  The
events in this area will be included in the @(see xdoc), if applicable, as if
they were part of the same @(see defsection).</p>

<p>Any strings that appear after the @('///') symbol are appended to the
@(':long') section of the @('define')'s xdoc, in between the events around
it.</p>

<p>To distinguish the @('other-events') from the @('main-stuff'), we use the
special symbol @('///') to separate the two.</p>

<p>Why do we use this goofy symbol?  In Common Lisp, @('///') has a special
meaning and is used by the Lisp read-eval-print loop.  Because of that, ACL2
does not allow you to bind it in @(see let) statements or use it as a formal in
a definition.  Because of <i>that</i>, we can be sure that @('///') is not the
body of any function definition, so it can be reliably used to separate the
rest-events.  As bonus features, @('///') is already imported by any <see
topic='@(url defpkg)'>package</see> that imports
@('*common-lisp-symbols-from-main-lisp-package*'), and even sort of looks like
some kind of separator!</p>


")

(defxdoc define-guards
  :parents (define)
  :short "Discussion of how guards are given in @(see define)."
  :long "<p>@(csee define) allows several different ways to specify the guards
of a function.  The ordering of these in the final guards provided to the
generated defun is sometimes significant (when the guards themselves have
guards) and define's behavior in trying to address this can be quirky.</p>

<p>The following example shows all (?) the ways in which guards can be specified:</p>

@({
  (define foo ((a natp)                   ;; formal guard
               (b :type unsigned-byte)    ;; formal type
               c d$ e f$ g
               state)                     ;; implicit stobj
     :guard (consp c)                     ;; guard keyword
     :stobjs (d$)                         ;; stobjs keyword
     (declare (xargs :guard (stringp e))) ;; guard in declare form
     (declare (xargs :stobjs (f$)))       ;; stobjs in declare form
     (declare (type symbol g))            ;; type in declare form
   ...)
 })

<p>This define generates the following declarations:</p>

@({
  (DECLARE (XARGS :STOBJS (D$ F$ STATE)))         ;; implicit stobjs
  (DECLARE (TYPE UNSIGNED-BYTE B))                ;; formal types
  (DECLARE (XARGS :GUARD (NATP A)))               ;; formal guards
  (DECLARE (XARGS :GUARD (STRINGP E)))            ;; declare forms
  (DECLARE (XARGS :STOBJS (F$)))
  (DECLARE (TYPE SYMBOL G))
  (DECLARE (XARGS :STOBJS (D$) :GUARD (CONSP C))) ;; guard and stobj keywords
 })

<p>The reasons for this ordering are somewhat heuristic: stobj declarations
shouldn't have any dependencies and type declarations are also unlikely to.
Formal guards usually occur first in the define form and are also usually used
for simple unary type constraints, so we put them next.  Declare forms may also
include stobj and type declarations, which the guard keywords might depend on.
Finally, the guards specified by the guard keyword come last.</p>

<p>One further quirk is that we reorder the formal guards, putting those that
only refer to one variable first.  This is because we have encountered
situations where we want to put main formals first and auxiliary parameters
later, but the main formals' guards depend on the auxiliary parameters.  For
example,</p>

@({
 (define fp-add ((x1 (fp-vec-p x1 size))
                 (x2 (fp-vec-p x2 size))
                 (size fp-size-p))
   ...)
 })

<p>Since size has a unary guard @('(fp-size-p size)'), we put that first, which
is good if @('fp-vec-p') has that as a guard on its size argument.</p>

<p>It is possible to construct define forms that look like they should succeed
but actually fail due to the heuristic reordering of guards.  If you encounter
one of these in the wild and have a suggestion to improve the heuristic, please
mention it.  In any case, explicitly stating your guards in order in a declare
form is usually an adequate work-around.</p>")


; -------------- Xargs Extraction ---------------------------------------------

(defun extract-xargs-from-xguts
  (ctx         ; Context for error messages
   xargs-guts  ; Guts from an (xargs ...) form, i.e., (:verify-guards ... :hints ... :guard ...)
   )
  (b* (((when (atom xargs-guts))
        nil)
       ((unless (member (car xargs-guts) acl2::*xargs-keywords*))
        (er hard? ctx "Malformed xargs: expected a valid xargs keyword but found ~x0.~%" (car xargs-guts)))
       ((when (atom (cdr xargs-guts)))
        (er hard? ctx "Malformed xargs: no value for ~x0?~%" (car xargs-guts))))
    (cons (cons (first xargs-guts)
                (second xargs-guts))
          (extract-xargs-from-xguts ctx (cddr xargs-guts)))))

#||
 (extract-xargs-from-xguts 'foo '(:verify-guards t :guard-debug t))
||#

(defun extract-xargs-from-declguts
  (ctx        ; Context for error messages
   declguts   ; Guts from a single (declare ...) form, i.e., ((xargs :verify-guards ...) (ignore ...) ...)
   )
  (b* (((when (atom declguts))
        nil)
       (decl1 (car declguts))
       ((unless (and (consp decl1)
                     (eq (car decl1) 'xargs)))
        (extract-xargs-from-declguts ctx (cdr declguts)))
       (xguts (cdr decl1)))
    (append (extract-xargs-from-xguts ctx xguts)
            (extract-xargs-from-declguts ctx (cdr declguts)))))

#||
 (extract-xargs-from-declguts 'foo
                              '((xargs :verify-guards t)
                                (ignore foo)
                                (type integer foo)
                                (xargs :guard-debug t :measure-debug t)
                                (ignorable bar)))
||#

(defun extract-xargs-from-traditional-decls/docs
  (ctx   ; Context for error messages
   decls ; List of traditional (declare ...) forms or doc strings
   )
  ;; Returns extracted xargs-alist
  (b* (((when (atom decls))
        nil)
       (decl1 (car decls))
       ((unless (and (consp decl1)
                     (eq (car decl1) 'declare)))
        (extract-xargs-from-traditional-decls/docs ctx (cdr decls)))
       (declguts (cdr decl1)))
    (append (extract-xargs-from-declguts ctx declguts)
            (extract-xargs-from-traditional-decls/docs ctx (cdr decls)))))

#||
 (extract-xargs-from-traditional-decls/docs 'foo
                                            '("traditional doc string"
                                              (declare (xargs :guard t :hints 5))
                                              (declare)
                                              (declare (ignore x))
                                              (declare (xargs :verify-guards t)
                                                       (type integer x)
                                                       (xargs :measure-debug t))))
||#


; -------------- Main Stuff Parsing -------------------------------------------


(defun get-xargs-from-kwd-alist (kwd-alist)
  ;; Munges the top-level xargs stuff together into a form suitable for a declare.
  (declare (xargs :guard (alistp kwd-alist)))
  (b* (((when (atom kwd-alist))
        nil)
       ((cons (cons key1 val1) rest) kwd-alist)
       ((when (member key1 acl2::*xargs-keywords*))
        (list* key1 val1
               (get-xargs-from-kwd-alist rest))))
    (get-xargs-from-kwd-alist rest)))

#||
 (get-xargs-from-kwd-alist '((:long . "foo")
                             (:guard-debug . t)
                             (:guard-hints . nil)))
 -->
 (:guard-debug t :guard-hints nil)
||#


(defun get-set-ignores-from-kwd-alist (kwd-alist)
  (declare (xargs :guard (alistp kwd-alist)))
  (b* ((ignore-ok (getarg :ignore-ok nil kwd-alist))
       (irrel-ok  (getarg :irrelevant-formals-ok nil kwd-alist))
       (events    nil)
       (events    (if ignore-ok
                      (cons `(set-ignore-ok ,ignore-ok) events)
                    events))
       (events    (if irrel-ok
                      (cons `(set-irrelevant-formals-ok ,irrel-ok) events)
                    events)))
    events))


(defconst *define-keywords*
  (append '(:ignore-ok
            :irrelevant-formals-ok
            :parents
            :short
            :long
            :inline
            :enabled
            :returns
            :prepwork
            :verbosep
            :progn
            :hooks
            :t-proof
            :no-function
            :local-def)
          acl2::*xargs-keywords*))



; -------------- XDOC Signatures ----------------------------------------------

; The idea here is to write out a signature that shows the names of the formals
; and return values, and then provides the documentation for any documented
; formals/returns.
;
; The formals always have names, but the return values will only have names if
; someone has named them with :returns.  If we don't have return-value names,
; we can at least look up the stobjs-out property and see how many return
; values there are, and if any of them are stobj names they'll have names.
; This will also let us double-check the return value arities.

(defun nils-to-stars (x)
  (declare (xargs :guard t))
  (cond ((atom x)
         nil)
        ((eq (car x) nil)
         (cons '* (nils-to-stars (cdr x))))
        (t
         (cons (car x) (nils-to-stars (cdr x))))))

(defun return-value-names (fnname returnspecs world)
  (declare (xargs :guard (and (symbolp fnname)
                              (returnspeclist-p returnspecs)
                              (plist-worldp world))))
  (b* ((stobjs-out (look-up-return-vals fnname world))
       ((when (atom returnspecs))
        ;; Fine, the user just didn't name/document the return values.  Semi
        ;; bozo: if this is a non-executable function, stobjs-out doesn't
        ;; necessarily say the right thing.  Well, we can't really do any
        ;; better, so whatever.
        (nils-to-stars stobjs-out))
       ((when (and (not (equal (len stobjs-out) (len returnspecs)))
                   ;; See Issue 270.  The stobjs-out is not a reliable
                   ;; indicator of how many values are returned by
                   ;; non-executable functions, so if this function isn't
                   ;; executable we'll just trust that the user knows how
                   ;; many values it returns.
                   (not (getprop fnname 'acl2::non-executablep nil 'acl2::current-acl2-world world))))
        (er hard? 'return-value-names
            "Error in ~x0: ACL2 thinks this function has ~x1 return ~
             values, but :returns has ~x2 entries!"
            fnname
            (len stobjs-out)
            (len returnspecs))))
    ;; Else the user documented things, so everything has a name and we should
    ;; be just fine.
    (returnspeclist->names returnspecs)))

(defun make-xdoc-signature
  ;; Makes the short (foo x y z) -> (mv a b c) line
  (wrapper            ; name of wrapper function, a symbol
   return-value-names ; names of return values, a symbol list
   base-pkg           ; base package for printing
   acc                ; accumulator for chars in reverse order
   state)
  "Returns (mv acc state)"
  (b* ((args (look-up-wrapper-args wrapper (w state)))
       (call-sexpr (cons wrapper args))
       (ret-sexpr (cond ((atom return-value-names)
                         (er hard? 'make-xdoc-signature
                             "Expected at least one return value name."))
                        ((atom (cdr return-value-names))
                         ;; Just one return value, don't do any MV stuff.
                         (car return-value-names))
                        (t
                         (cons 'mv return-value-names))))

       ((mv call-str state) (xdoc::fmt-to-str-orig call-sexpr base-pkg state))
       ((mv ret-str state)  (xdoc::fmt-to-str-orig ret-sexpr base-pkg state))
       (call-len (length call-str)) ;; sensible since not yet encoded
       (ret-len  (length ret-str))  ;; sensible since not yet encoded
       (acc (bootstrap-revappend-chars "  <dt>Signature</dt><dt>" acc))
       (acc (if (< (+ call-len ret-len) 60)
                ;; Short signature, so put it all on the same line.  I'm still
                ;; going to use <code> instead of <tt>, for consistency.
                (b* ((acc (bootstrap-revappend-chars "<code>" acc))
                     (acc (bootstrap-html-encode-str call-str 0 call-len acc))
                     (acc (bootstrap-revappend-chars " &rarr; " acc))
                     (acc (bootstrap-html-encode-str ret-str 0 ret-len acc))
                     (acc (bootstrap-revappend-chars "</code>" acc)))
                  acc)
              ;; Long signature, so split it across lines.  Using <code> here
              ;; means it's basically okay if there are line breaks in call-str
              ;; or ret-str.
              (b* ((acc (bootstrap-revappend-chars "<code>" acc))
                   (acc (bootstrap-html-encode-str call-str 0 call-len acc))
                   (acc (cons #\Newline acc))
                   (acc (bootstrap-revappend-chars "  &rarr;" acc))
                   (acc (cons #\Newline acc))
                   (acc (bootstrap-html-encode-str ret-str 0 ret-len acc))
                   (acc (bootstrap-revappend-chars "</code>" acc)))
                acc)))
       (acc (bootstrap-revappend-chars "</dt>" acc)))
    (mv acc state)))


(defun formal-can-generate-doc-p (x)
  (declare (xargs :guard (formal-p x)))
  (b* (((formal x) x))
    (or (not (equal x.doc ""))
        (not (eq x.guard t)))))

(defun formals-can-generate-doc-p (x)
  (declare (xargs :guard (formallist-p x)))
  (if (atom x)
      nil
    (or (formal-can-generate-doc-p (car x))
        (formals-can-generate-doc-p (cdr x)))))

(defun doc-from-formal (x acc base-pkg state)
  (declare (xargs :guard (formal-p x)))
  (b* (((formal x) x)

       ((unless (formal-can-generate-doc-p x))
        (mv acc state))

       (acc (bootstrap-revappend-chars "  <dd>" acc))
       ((mv name-str state) (xdoc::fmt-to-str-orig x.name base-pkg state))
       (acc (bootstrap-revappend-chars "<tt>" acc))
       (acc (bootstrap-html-encode-str name-str 0 (length name-str) acc))
       (acc (bootstrap-revappend-chars "</tt>" acc))
       (acc (bootstrap-revappend-chars " &mdash; " acc))

       (acc (if (equal x.doc "")
                acc
              (b* ((acc (bootstrap-revappend-chars x.doc acc))
                   (acc (if (ends-with-period-p x.doc)
                            acc
                          (cons #\. acc))))
                acc)))

       ((when (eq x.guard t))
        (b* ((acc (bootstrap-revappend-chars "</dd>" acc))
             (acc (cons #\Newline acc)))
          (mv acc state)))

       (acc (if (equal x.doc "")
                acc
              (bootstrap-revappend-chars "<br/>&nbsp;&nbsp;&nbsp;&nbsp;" acc)))
       (acc (bootstrap-revappend-chars "<color rgb='#606060'>" acc))
       ((mv guard-str state) (xdoc::fmt-to-str-orig x.guard base-pkg state))
       ;; Using @('...') here isn't necessarily correct.  If the sexpr has
       ;; something in it that can lead to '), we are hosed.  BOZO eventually
       ;; check for this and make sure we use <code> tags instead, if it
       ;; happens.
       (acc (bootstrap-revappend-chars "Guard @('" acc))
       (acc (bootstrap-revappend-chars guard-str acc))
       (acc (bootstrap-revappend-chars "').</color></dd>" acc))
       (acc (cons #\Newline acc)))
    (mv acc state)))

(defun doc-from-formals-aux (x acc base-pkg state)
  (declare (xargs :guard (formallist-p x)))
  (b* (((when (atom x))
        (mv acc state))
       ((mv acc state)
        (doc-from-formal (car x) acc base-pkg state)))
    (doc-from-formals-aux (cdr x) acc base-pkg state)))

(defun doc-from-formals (x acc base-pkg state)
  (declare (xargs :guard (formallist-p x)))
  (b* (((unless (formals-can-generate-doc-p x))
        (mv acc state))
       (acc (bootstrap-revappend-chars "  <dt>Arguments</dt>" acc))
       ((mv acc state) (doc-from-formals-aux x acc base-pkg state)))
    (mv acc state)))


(defun returnspec-can-generate-doc-p (x)
  (declare (xargs :guard (returnspec-p x)))
  (b* (((returnspec x) x))
    (or (not (equal x.doc ""))
        (not (eq x.return-type t)))))

(defun returnspecs-can-generate-doc-p (x)
  (declare (xargs :guard (returnspeclist-p x)))
  (if (atom x)
      nil
    (or (returnspec-can-generate-doc-p (car x))
        (returnspecs-can-generate-doc-p (cdr x)))))

(defun doc-from-returnspec (x acc base-pkg state)
  (declare (xargs :guard (returnspec-p x)))
  (b* (((returnspec x) x)

       ((unless (returnspec-can-generate-doc-p x))
        (mv acc state))

       (acc (bootstrap-revappend-chars "<dd>" acc))
       ((mv name-str state) (xdoc::fmt-to-str-orig x.name base-pkg state))
       (acc (bootstrap-revappend-chars "<tt>" acc))
       (acc (bootstrap-html-encode-str name-str 0 (length name-str) acc))
       (acc (bootstrap-revappend-chars "</tt>" acc))
       (acc (bootstrap-revappend-chars " &mdash; " acc))

       (acc (if (equal x.doc "")
                acc
              (b* ((acc (bootstrap-revappend-chars x.doc acc))
                   (acc (if (ends-with-period-p x.doc)
                            acc
                          (cons #\. acc))))
                acc)))

       ((when (eq x.return-type t))
        (b* ((acc (bootstrap-revappend-chars "</dd>" acc))
             (acc (cons #\Newline acc)))
          (mv acc state)))

       (acc (if (equal x.doc "")
                acc
              (bootstrap-revappend-chars "<br/>&nbsp;&nbsp;&nbsp;&nbsp;" acc)))
       (acc      (bootstrap-revappend-chars "<color rgb='#606060'>" acc))
       ((mv type-str state) (xdoc::fmt-to-str-orig x.return-type base-pkg state))
       ;; Using @('...') here isn't necessarily correct.  If the sexpr has
       ;; something in it that can lead to '), we are hosed.  BOZO eventually
       ;; check for this and make sure we use <code> tags instead, if it
       ;; happens.
       (acc (bootstrap-revappend-chars "Type @('" acc))
       (acc (bootstrap-revappend-chars type-str acc))
       (acc (bootstrap-revappend-chars "')" acc))
       ((mv acc state)
        (cond ((eq x.hyp t)
               (mv (cons #\. acc) state))
              ((or (eq x.hyp :guard)
                   (eq x.hyp :fguard))
               (mv (bootstrap-revappend-chars ", given the @(see guard)." acc)
                   state))
              (t
               (b* ((acc (bootstrap-revappend-chars ", given @('" acc))
                    ((mv hyp-str state)
                     (xdoc::fmt-to-str-orig x.hyp base-pkg state))
                    (acc (bootstrap-revappend-chars hyp-str acc))
                    (acc (bootstrap-revappend-chars "')." acc)))
                 (mv acc state)))))
       (acc (bootstrap-revappend-chars "</color>" acc))
       (acc (bootstrap-revappend-chars "</dd>" acc))
       (acc (cons #\Newline acc)))

    (mv acc state)))

(defun doc-from-returnspecs-aux (x acc base-pkg state)
  (declare (xargs :guard (returnspeclist-p x)))
  (b* (((when (atom x))
        (mv acc state))
       ((mv acc state)
        (doc-from-returnspec (car x) acc base-pkg state)))
    (doc-from-returnspecs-aux (cdr x) acc base-pkg state)))

(defun doc-from-returnspecs (x acc base-pkg state)
  (declare (xargs :guard (returnspeclist-p x)))
  (b* (((unless (returnspecs-can-generate-doc-p x))
        (mv acc state))
       (acc (bootstrap-revappend-chars "<dt>Returns</dt>" acc))
       ((mv acc state) (doc-from-returnspecs-aux x acc base-pkg state)))
    (mv acc state)))

(defun make-xdoc-top (wrapper fnname formals returnspecs base-pkg state)
  "Returns (mv str state)"
  (b* ((world (w state))
       (acc nil)
       (acc (bootstrap-revappend-chars "<box><dl>" acc))
       (acc (cons #\Newline acc))
       (return-value-names (return-value-names fnname returnspecs world))
       ((mv acc state) (make-xdoc-signature wrapper return-value-names base-pkg acc state))
       ((mv acc state) (doc-from-formals formals acc base-pkg state))
       ((mv acc state) (doc-from-returnspecs returnspecs acc base-pkg state))
       (acc (cons #\Newline acc))
       (acc (bootstrap-revappend-chars "</dl></box>" acc))
       (acc (cons #\Newline acc))
       (str (reverse (coerce acc 'string))))
    (mv str state)))



; -------------- Top-Level Macro ----------------------------------------------

(defun formallist->types (x)
  (declare (xargs :guard (formallist-p x)))
  (b* (((when (atom x))
        nil)
       ((formal f1) (car x))
       (look (assoc :type f1.opts))
       ((unless look)
        (formallist->types (cdr x)))
       (this-decl
        `(type ,(cdr look) ,f1.name)))
    (cons this-decl
          (formallist->types (cdr x)))))



(def-primitive-aggregate defguts
  (name        ;; user-level name (could be the function, or its wrapper macro)
   name-fn     ;; name of the actual function (might be fn, or fn$inline, fn$notinline, or fn-fn)
   kwd-alist   ;; keyword options passed to define
   returnspecs ;; returns specifiers, already parsed

   t-proof     ;; the full event representing termination for this function
   main-def    ;; the full defun[d] event for the function
   macro       ;; macro wrapper (if necessary), nil or a defmacro event
   raw-formals ;; not parsed, includes any &optional, &key parts
   formals     ;; already parsed, macro parts removed

   rest-events ;; events in the /// part
   pe-entry    ;; raw form to use in the PE-table
   guards-after-returns ;; verify guards after returnspecs
   ))

(table define)
(table define 'guts-alist) ;; An alist binding NAME -> DEFGUTS structures

(defun get-define-guts-alist (world)
  "Look up information about the current defines in the world."
  (cdr (assoc 'guts-alist (table-alist 'define world))))

(defun extend-define-guts-alist (guts)
  `(table define 'guts-alist
          (cons '(,(defguts->name guts) . ,guts) ; minor Matt K. mod
                (get-define-guts-alist world))))

(defun get-define-current-function (world)
  (cdr (assoc 'current-function (table-alist 'define world))))

(defmacro set-define-current-function (fn)
  `(table define 'current-function ',fn))

; -------- Proving termination of some function definition separately -------
(defun make-termination-proof (thmName thmHints defun)
  `((make-event
        (let* ((state (f-put-global 'last-clause '(t) state))
               (oldHint (override-hints (w state))))
          (er-progn
           (set-override-hints
            '((pprogn (f-put-global 'last-clause clause state)
                      (mv 'err nil state))))
           (mv-let (x y state) ,defun
                   (declare (ignore x y))
                   (value `(progn (set-override-hints ,oldHint)
                                  (defthm ,',thmName ,(cons 'or (@ last-clause))
                                    :hints ,',thmHints :rule-classes nil)))))))))

; ----------------- Hooks -----------------------------------------------------

(defxdoc post-define-hook
  :parents (define)
  :short "A way to extend @(see define) to carry out additional behaviors."
  :long "<p>The @(see define) macro can be configured with ``hooks'' to
automatically generate and submit certain additional events.  For instance, the
@(see fty::fixequiv-hook) extends define to automatically prove certain
congruence rules.</p>

<p>This is an advanced and somewhat experimental feature.  To introduce a new
post-define hook, first define a function of the signature:</p>

@({
     (my-hook-fn defguts user-args state) -> (mv er val state)
})

<p>Here:</p>

<ul>

<li>the @('defguts') argument is a structure which will have information from
the @('define') itself, see the comments in @('std/util/define.lisp') for
details</li>

<li>the @('user-args') are any arguments that can be passed to your hook
function at @('define') time via the @(':hooks') argument, or via the default
post-define hook mechanism.</li>

<li>the return value is an ordinary ACL2 error triple, where the @('val')
should be some additional events to submit.</li>

</ul>

<p>Once your function is defined, you can register it as a post-define hook as
follows:</p>

@({
     (add-post-define-hook :myhook my-hook-fn)
})

<p>And subsequently it will be legal to use @(':hooks ((:myhook ...))') or
similar.  Define can also be configured with default post-define hooks, see
@('add-default-post-define-hook') in the @('std/util/define.lisp') source code;
also see the @('std/util/tests/define.lisp') file for some working
examples.</p>")

(defun remove-from-alist (key alist)
  (cond ((atom alist)
         nil)
        ((atom (car alist))
         (remove-from-alist key (cdr alist)))
        ((equal (caar alist) key)
         (remove-from-alist key (cdr alist)))
        (t
         (cons (car alist)
               (remove-from-alist key (cdr alist))))))

(table define 'post-hooks-alist)   ;; Alist of hook keyword -> hook function name
(table define 'default-post-hooks) ;; List of (hook keyword . default-args)

(defun get-post-define-hooks-alist (world)
  (cdr (assoc 'post-hooks-alist (table-alist 'define world))))

(defun get-default-post-define-hooks (world)
  (cdr (assoc 'default-post-hooks (table-alist 'define world))))

(defun add-post-define-hook-fn (kwd fn state)
  (b* ((world   (w state))
       (formals (look-up-formals fn world))
       ((unless (and (tuplep 3 formals)
                     (equal (third formals) 'state)))
        (er soft 'add-post-define-hook
            "~x0 doesn't look like a proper post-define hook function."
            fn))
       (alist (get-post-define-hooks-alist world))
       (look  (cdr (assoc kwd alist)))
       ((unless look)
        (value `(table define 'post-hooks-alist
                       (cons (cons ',kwd ',fn)
                             (get-post-define-hooks-alist world)))))
       ((unless (equal (cdr look) fn))
        (er soft 'add-post-define-hook
            "~x0 is already a post-define hook bound to ~x1." kwd fn)))
    (value '(value-triple :redundant))))

(defmacro add-post-define-hook (kwd fn)
  (declare (xargs :guard (and (keywordp kwd)
                              (symbolp fn))))
  `(make-event (add-post-define-hook-fn ',kwd ',fn state)))

(defmacro remove-post-define-hook (kwd)
  (declare (xargs :guard (keywordp kwd)))
  `(table define 'post-hooks-alist
          (remove-from-alist ',kwd (get-post-define-hooks-alist world))))

(defun add-default-post-define-hook-fn (kwd default-args state)
  (b* ((world (w state))
       ((unless (assoc kwd (get-post-define-hooks-alist world)))
        (er soft 'add-default-post-define-hook
            "~x0 is not the name of a post-define hook." kwd))
       (current-hooks (get-default-post-define-hooks world))
       (look (assoc kwd current-hooks))
       ((unless look)
        (value `(table define 'default-post-hooks
                       (cons (cons ',kwd ',default-args)
                             (get-default-post-define-hooks world)))))
       ((unless (equal (cdr look) default-args))
        (er soft 'add-post-define-hook
            "~x0 is already in use as a default post-define hook." kwd)))
    (value `(value-triple :redundant))))

(defmacro add-default-post-define-hook (kwd &rest default-args)
  (declare (xargs :guard (keywordp kwd)))
  `(make-event (add-default-post-define-hook-fn ',kwd ',default-args state)))

(defmacro remove-default-post-define-hook (kwd)
  (declare (xargs :guard (keywordp kwd)))
  `(table define 'default-post-hooks
          (remove-from-alist ',kwd (get-default-post-define-hooks world))))

(defun post-hook-make-events
  (hook-specs  ;; a list of either: plain keywords (naming hooks), or (keyword . user-args) pairs
   hooks-alist ;; the post-define-hooks alist, binds hook keywords to function names
   guts        ;; the defguts object for the function that has just been defined
   )
  ;; Returns a list of make-event forms
  (b* (((when (atom hook-specs))
        nil)
       (spec1 (car hook-specs))
       ((mv hook-kwd user-args)
        (if (consp spec1)
            (mv (car spec1) (cdr spec1))
          ;; Plain keyword like :hook1
          (mv spec1 nil)))
       ((unless (keywordp hook-kwd))
        (er hard? 'post-hook-make-events "Invalid post-define hook specifier: ~x0" spec1))
       (look (assoc hook-kwd hooks-alist))
       ((unless look)
        (er hard? 'post-hook-make-events "Post-define hook not found: ~x0.  Known hooks: ~&1."
            hook-kwd (strip-cars hooks-alist)))
       (hook-fn (cdr look))
       (event1 `(make-event (,hook-fn ',guts ',user-args state))))
    (cons event1
          (post-hook-make-events (cdr hook-specs) hooks-alist guts))))

(defun sort-formal-guards-aux (guards wrld state-vars)
  ;; Returns two lists: simple and complex.  Simple is any guards that we can
  ;; translate and that have at most 1 variable.  Complex is everything else.
  ;; Both simple and complex are in the order they were encountered.
  (b* (((when (atom guards))
        (mv nil nil))
       (guard1 (car guards))
       ((mv err transguard)
        (acl2::translate-cmp guard1
                             '(nil) ;; returns single non-stobj
                             nil    ;; execution, not logic-modep
                             t    ;; known-stobjs -- probably don't need them?
                             'sort-formal-guards
                             wrld state-vars))
       ((mv rest-simple rest-complex)
        (sort-formal-guards-aux (cdr guards) wrld state-vars))
       ((when (or err
                  (consp (cdr (all-vars transguard)))))
        (mv rest-simple
            (cons guard1 rest-complex))))
    (mv (cons guard1 rest-simple)
        rest-complex)))

(defun sort-formal-guards (guards wrld)
  (b* (((mv simple complex)
        (sort-formal-guards-aux guards wrld (acl2::default-state-vars nil))))
    (append simple complex)))

(defun keep-assocs (keys-to-keep alist)
  (cond ((atom alist)
         nil)
        ((member (caar alist) keys-to-keep)
         (cons (car alist)
               (keep-assocs keys-to-keep (cdr alist))))
        (t
         (keep-assocs keys-to-keep (cdr alist)))))


(defun prettify-returnspec-for-pe (returnspec)
  ;; For the :pe display, we don't want to include things like :hints for the
  ;; returns specifiers, but it's definitely nice to include a simplified
  ;; :returns information.
  (b* (((returnspec x) returnspec)
       ((when (and (eq x.return-type t)
                   (equal x.doc "")))
        x.name))
    (append (list x.name)
            (cond ((eq x.return-type t)
                   nil)
                  ((and (tuplep 2 x.return-type)
                        (equal (second x.return-type) x.name))
                   ;; Simple return type, use concise syntax
                   (list (first x.return-type)))
                  (t
                   ;; Complex return type, use full syntax
                   (list x.return-type)))
            (if (eq x.hyp t)
                nil
              `(:hyp ,x.hyp))
            (if (eq x.rule-classes :rewrite)
                nil
              `(:rule-classes ,x.rule-classes))
            (if (equal x.doc "") nil (list x.doc)))))

(defun prettify-returnspecs-for-pe-aux (returnspecs)
  (if (atom returnspecs)
      nil
    (cons (prettify-returnspec-for-pe (car returnspecs))
          (prettify-returnspecs-for-pe-aux (cdr returnspecs)))))

(defun prettify-returnspecs-for-pe (returnspecs)
  (cond ((atom returnspecs)
         nil)
        ((atom (cdr returnspecs))
         (prettify-returnspec-for-pe (car returnspecs)))
        (t
         (cons 'mv (prettify-returnspecs-for-pe-aux returnspecs)))))

(defun convert-kwd-alist-back-into-plist (kwd-alist)
  (if (atom kwd-alist)
      nil
    (list* (caar kwd-alist)
           (cdar kwd-alist)
           (convert-kwd-alist-back-into-plist (cdr kwd-alist)))))

(defun pe-entry-args (args returnspecs)
  (declare (xargs :guard (true-listp args)))
  (cond ((endp args) nil)
        ((and (eq (car args) :long)
              (cdr args))
         (list* :long "Documentation is available via :doc."
                (pe-entry-args (cddr args) returnspecs)))
        ((and (eq (car args) :prepwork)
              (cdr args))
         (list* :prepwork "<event list elided>"
                (pe-entry-args (cddr args) returnspecs)))
        ((and (eq (car args) :returns)
              (cdr args)
              (consp returnspecs))
         (list* :returns
                (prettify-returnspecs-for-pe returnspecs)
                (pe-entry-args (cddr args) returnspecs)))
        ((eq (car args) '///)
         (list '/// "<events elided>"))
        (t (cons (car args)
                 (pe-entry-args (cdr args) returnspecs)))))

(defun append-and-remove-clashes (alst1 alst2)
  ;; [Shilpi] Added in support for a simple config object.
  ;; Append two alists alst1 and alst2 --- but if there any overlapping keys in
  ;; alst1 and alst2, then the keys in alst1 are retained and those in alst2
  ;; are discarded.
  (declare (xargs :guard (and (alistp alst1)
                              (alistp alst2))))
  (cond ((endp alst2) alst1)
        ((endp alst1) alst2)
        ((member-equal (caar alst1) (strip-cars alst2))
         ;; Overlapping key: keep the pair in alst1 and discard all pairs with
         ;; the matching key in alst2.
         (cons (car alst1)
               (append-and-remove-clashes
                (cdr alst1)
                (remove-assoc-equal (caar alst1) alst2))))
        (t
         (cons (car alst1)
               (append-and-remove-clashes (cdr alst1) alst2)))))

(defun get-define-config-alist (world)
  ;; [Shilpi] Added in support for a simple config object.
  (cdr (assoc 'define-config (table-alist 'define world))))

(defun parse-define
  (name            ; User-level name, e.g., FOO
   args            ; Everything that comes after the name
   extra-keywords  ; Any additional keywords to allow (useful for
                   ; building tools atop define).
   world)
  ;; Returns GUTS
  (declare (xargs :guard (plist-worldp world)))
  (b* ((__function__ 'define)
       ((unless (symbolp name))
        (raise "Expected function names to be symbols, but found ~x0." name))

       ((mv main-stuff rest-events) (split-/// name args))
       ((mv kwd-alist normal-defun-stuff)
        (extract-keywords name (append extra-keywords *define-keywords*)
                          main-stuff nil))
       ;; [Shilpi] Added support for a simple config object.
       (config-alist     (get-define-config-alist world))
       ;; Append config-alist to kwd-alist --- if there are keywords common to
       ;; both alists, those in kwd-alist override those in config-alist.
       (kwd-alist        (append-and-remove-clashes kwd-alist config-alist))
       (raw-formals            (car normal-defun-stuff))
       (traditional-decls/docs (butlast (cdr normal-defun-stuff) 1))
       (body                   (car (last normal-defun-stuff)))

       (non-exec   (getarg :non-executable nil      kwd-alist))
       (returns    (getarg :returns        nil      kwd-alist))
       (inline     (getarg :inline         :default kwd-alist))
       (prepwork   (getarg :prepwork       nil      kwd-alist))

       ((unless (true-listp prepwork))
        (raise "Error in ~x0: expected :prepwork to be a true-listp, but found ~x1."
               name prepwork))

       (t-proof (getarg :t-proof nil kwd-alist))
       ((unless (booleanp t-proof))
        (raise "Error in ~x0: expected :t-proof to be a booleanp, but found ~x1."
               name prepwork))
       ((unless (member inline '(:default t nil)))
        (raise "Error in ~x0: expected :inline to be T, NIL, or :DEFAULT, but found ~x1."
               name inline))

       (embedded-xargs-alist (extract-xargs-from-traditional-decls/docs (list 'define name)
                                                                        traditional-decls/docs))

       (need-macrop (or (not (eq inline :default))
                        (has-macro-args raw-formals)))
       (name-fn     (cond ((eq inline t)
                           (intern-in-package-of-symbol
                            (concatenate 'string (symbol-name name) "$INLINE")
                            name))
                          ((eq inline nil)
                           (intern-in-package-of-symbol
                            (concatenate 'string (symbol-name name) "$NOTINLINE")
                            name))
                          (need-macrop
                           (intern-in-package-of-symbol
                            (concatenate 'string (symbol-name name) "-FN")
                            name))
                          (t
                           name)))

       (macro         (and need-macrop
                           (make-wrapper-macro name name-fn raw-formals)))
       (formals       (remove-macro-args name raw-formals nil))
       (formals       (parse-formals name formals '(:type) world))

       (formal-names  (formallist->names formals))
       (formal-guards (remove t (formallist->guards formals)))
       (formal-types  (formallist->types formals))
       (stobj-names   (formallist->names (formallist-collect-stobjs formals world)))

       (no-function   (getarg :no-function nil kwd-alist))
       (extended-body (if no-function
                          body
                        `(let ((__function__ ',name))
                           ;; CCL's compiler seems to be smart enough to not
                           ;; generate code for this binding when it's not
                           ;; needed.
                           (declare (ignorable __function__))
                           ,body)))
       (final-body    (if non-exec
                          ;; support the :non-executable xarg by wrapping the
                          ;; body in the required throw form
                          `(prog2$ (acl2::throw-nonexec-error
                                    ',name (list . ,formal-names))
                                   ,extended-body)
                        extended-body))
       ;; [Shilpi] Added to support :verify-guards :after-returns.
       (verify-guards-after-returns
        (eq (cdr (assoc :verify-guards kwd-alist)) :after-returns))
       ;; Modify kwd-alist so that 'nil is paired with :verify-guards in the
       ;; main-def.
       (kwd-alist     (if verify-guards-after-returns
                          (put-assoc :verify-guards 'nil kwd-alist)
                        kwd-alist))
       (xargs         (get-xargs-from-kwd-alist kwd-alist))

       ;; BOZO packn??  Probably should use the function's package instead.
       (t-proof-name  (if t-proof (ACL2::packn (LIST name-fn '|-| t-proof)) nil))

       (returnspecs   (parse-returnspecs name returns world))

       (pe-entry (list* 'define name (pe-entry-args args returnspecs)))

       (guard-verification-will-happen-anyway-p
        ;; Design decision: define will ignore set-verify-guards-eagerness 1
        ;; and always try to verify guards.  (I think I much more frequently
        ;; have guards of T than want to not verify guards.)  We could do this
        ;; by always adding an explicit (declare (xargs :guard t)).  But that's
        ;; a bit ugly, so work harder and only add it if there are no guards
        ;; coming from other places like extended formals, type declarations,
        ;; etc.
        (or (consp formal-types)
            (consp formal-guards)
            (assoc :guard kwd-alist)
            (assoc :guard embedded-xargs-alist)
            ;; BOZO eventually could also look for type declarations in
            ;; the traditional decls/docs
            ))

       (main-def
        `(;; Historically we used defund unless the function was enabled-p.
          ;; But this ran afoul of Issue 464 for DEFINE forms that were
          ;; embedded in DEFINES.  It seems simpler and easier to just handle
          ;; the enabling or disabling later, since DEFUND isn't really
          ;; anything special.  So, we now just always use DEFUN instead.
          defun
          ,name-fn ,formal-names

; Subtle: this order isn't what we always used, but Sol ran into some problems
; where, e.g., traditional type declarations weren't coming before the guards
; from formals, and therefore the guards wouldn't verify.  We now try to use an
; order that seems like it is most probably the one you want.

; 1. Stobj names, since they give us stobj-p guards, which may be useful and
; probably can't depend on anything else
           ,@(and stobj-names
                  `((declare (xargs :stobjs ,stobj-names))))

; 2. Formal types, since they shouldn't have dependencies and may give us
; useful guards.

           ,@(and formal-types
                  `((declare . ,formal-types)))

; 3. Formal guards, since these should often be "simple types" that probably
; don't have further dependencies, e.g., don't rely on the top-level :guard

           ,@(cond ((atom formal-guards)
                    nil)
                   ((atom (cdr formal-guards))
                    `((declare (xargs :guard ,(car formal-guards)))))
                   (t
                    ;; Sort the guards by putting those that we can determine
                    ;; to be dependent on only 1 variable first.
                    (b* ((sorted-formal-guards (sort-formal-guards formal-guards world)))
                      `((declare (xargs :guard (and . ,sorted-formal-guards)))))))

; 4. This is kind of arbitrary.  We put the traditional decls before the top-level
; xargs because it seems rather unlikely that someone would write
;     :guard ...
;     (declare (xargs :guard ...))
;
; But it seems more likely that they would write:
;     :guard ...
;     (declare (type integer x))
; And so in this case, we'll get the type declarations before the "complex" guard,
; which can't hurt.

           ,@traditional-decls/docs

; 5. Finally the top-level :guards and other xargs, since they might be for
; more dependent-typey kinds of things that may depend on type declarations and
; formal guards and stobjs from above.

           ,@(and xargs
                  `((declare (xargs . ,xargs))))

           ;; Just in case there is nothing else to provoke guard verification:
           ,@(and (not guard-verification-will-happen-anyway-p)
                  `((declare (xargs :guard t))))

           ,final-body
           )))

    (make-defguts :name        name
                  :name-fn     name-fn
                  :kwd-alist   kwd-alist
                  :returnspecs returnspecs
                  :main-def    main-def
                  :macro       macro
                  :raw-formals raw-formals
                  :formals     formals
                  :rest-events (xdoc::make-xdoc-fragments rest-events)
                  :t-proof     (if t-proof (cons t-proof-name nil) nil)
                  :pe-entry    pe-entry
                  :guards-after-returns verify-guards-after-returns
                  )))

(defun add-signature-from-guts (guts)
  (b* (((defguts guts) guts))
    ;; Now that the section has been submitted, we can compute its signature
    ;; block and prepend it to the topic (if any docs were generated)
    `(make-event
      (b* ((current-pkg (acl2::f-get-global 'acl2::current-package state))
           (base-pkg    (pkg-witness current-pkg))
           (name        ',guts.name)
           (all-topics  (xdoc::get-xdoc-table (w state)))
           (old-topic   (xdoc::find-topic name all-topics))
           ((unless old-topic)
            ;; Fine, it isn't documented.
            (value '(value-triple :invisible)))
           ((mv str state)
            (make-xdoc-top name ',guts.name-fn ',guts.formals
                           ',guts.returnspecs base-pkg state))
           (event (list 'xdoc::xdoc-prepend name str)))
        (value event)))))

(defun add-macro-aliases-from-guts (guts)
  (b* (((defguts guts) guts))
    (and guts.macro
         `((add-macro-alias ,guts.name ,guts.name-fn)
           (table define-macro-fns ',guts.name-fn ',guts.name)))))

(defun events-from-guts (guts world)
  (b* (((defguts guts) guts)
       (enabled-p  (getarg :enabled        nil guts.kwd-alist))
       (prepwork   (getarg :prepwork       nil guts.kwd-alist))
       (short      (getarg :short          nil guts.kwd-alist))
       (long       (getarg :long           nil guts.kwd-alist))
       (parents    (getarg :parents        nil guts.kwd-alist))
       (parents    (if (assoc :parents guts.kwd-alist)
                       parents
                     (xdoc::get-default-parents world)))

       (hooks-alist (get-post-define-hooks-alist world))
       (hook-specs  (getarg :hooks
                            (get-default-post-define-hooks world)
                            guts.kwd-alist))

       (set-ignores (get-set-ignores-from-kwd-alist guts.kwd-alist))
       (prognp      (getarg :progn         nil guts.kwd-alist))
       (start-max-absolute-event-number
        (acl2::max-absolute-event-number world))
       )

    `(progn
       (,(if prognp 'defsection-progn 'defsection) ,guts.name
         ,@(and parents `(:parents ,parents))
         ,@(and short   `(:short ,short))
         ,@(and long    `(:long ,long))

         ,@(and prepwork
                `((with-output :stack :pop
                    (progn . ,prepwork))))

         ;; Define the macro first, so that it can be used in recursive calls,
         ;; e.g., to take advantage of nicer optional/keyword args.
         ,@(and guts.macro `((with-output :stack :pop ,guts.macro)))

         ,(let ((def (if set-ignores
                         `(encapsulate ()
                            ,@set-ignores
                            (with-output :stack :pop ,guts.main-def))
                       `(with-output :stack :pop ,guts.main-def))))
            (if (cdr (assoc :local-def guts.kwd-alist))
                `(local ,def)
              def))

         ,@(add-macro-aliases-from-guts guts)

         ;; Extend the define table right away, in case anything during
         ;; the rest-events needs to make use of it.
         ,(extend-define-guts-alist guts)
         (set-define-current-function ,guts.name)

         ,@(and guts.returnspecs
                `((make-event
                   (make-define-ret-patbinder ',guts (w state)))))

         (local
          ;; [Jared] Previously, when we sometimes used DEFUND and DEFUN, this
          ;; was a sensible way to ensure that the function was always enabled
          ;; during the processing of the /// section.  You might think (and I
          ;; originally DID think) that, now that we always use DEFUN, that
          ;; this would be unnecessary.  However, in rare cases, for instance,
          ;; if we are redundantly DEFINEing a function that was originally
          ;; DEFINEd before now, the function may NOT be enabled even though we
          ;; have introduced it with DEFUN, because you can do something like
          ;;
          ;;    (defun foo ...)
          ;;    (in-theory (disable foo))
          ;;    (defun foo ...) ;; redundantly
          ;;
          ;; And at this point FOO is still disabled.  So, this is a bummer
          ;; because enabling/disabling is expensive, but at least we can keep
          ;; this local...
          (make-event
           (if (logic-mode-p ',guts.name-fn (w state))
               '(in-theory (enable ,guts.name))
             '(value-triple :invisible))))

         (make-event
          (let* ((world (w state))
                 (events (returnspec-thms ',guts.name ',guts.name-fn ',guts.returnspecs world)))
            (value (if events
                       `(with-output :stack :pop (progn . ,events))
                     '(value-triple :invisible)))))

         ;; [Shilpi] Added to support :verify-guards :after-returns.  Note that
         ;; the following verify-guards form will be generated whenever
         ;; :after-returns is used, irrespective of whether returns are
         ;; specified or not.
         ,@(and guts.guards-after-returns
                `((verify-guards ,guts.name-fn)))

         ;; BOZO using name-fn here is kind of weird, but otherwise we see ugly
         ;; output when there are macro arguments involved because ACL2 shows us
         ;; our nice output and then says, "oh but this is really a macro" and
         ;; then shows us the ugly macro.  But targeting name-fn instead seems
         ;; to do the right thing.
         ,(let ((pe-table `(acl2::extend-pe-table ,guts.name-fn ,guts.pe-entry)))
            (if (cdr (assoc :local-def guts.kwd-alist))
                `(local ,pe-table)
              pe-table))

         ,@(and guts.rest-events
                `((with-output :stack :pop
                    (progn
                      . ,guts.rest-events))))

         ,@(and hook-specs
                `((value-triple (cw "; Running post-define hooks.~%"))
                  .
                  ,(post-hook-make-events hook-specs hooks-alist guts)))

         ,@(if prognp
               `((set-define-current-function nil))
             nil)

         ,@(if enabled-p
               nil
             (let ((disable
                    `(make-event
                      (if (logic-mode-p ',guts.name-fn (w state))
                          '(in-theory (disable ,guts.name))
                        '(value-triple :invisible)))))
               (if (cdr (assoc :local-def guts.kwd-alist))
                   `((local ,disable))
                 `(,disable)))))


       ;; Now that the section has been submitted, its xdoc exists, so we can
       ;; do the doc generation and prepend it to the xdoc.
       ,(add-signature-from-guts guts)

       ,@(and guts.t-proof
              `((make-event
                 (if (and (logic-mode-p ',guts.name-fn (w state))
                          (acl2::recursivep ',guts.name-fn nil (w state)))
                     '(acl2::make-termination-theorem ,guts.name
                                                      :thm-name
                                                      ,(car guts.t-proof))
                   '(defthm ,(car guts.t-proof) t :rule-classes nil)))))

       (make-event (list 'value-triple
                         (if (eql ,start-max-absolute-event-number
                                  (acl2::max-absolute-event-number
                                   (acl2::w acl2::state)))
                             :redundant
                           (quote ',guts.name))))
       )))

(defun define-fn (name args world)
  (declare (xargs :guard (plist-worldp world)))
  (b* ((guts (parse-define name args nil world)))
    (events-from-guts guts world)))

(defmacro define (name &rest args)
  (let* ((verbose-tail (member :verbosep args))
         (verbosep (and verbose-tail (cadr verbose-tail))))
    `(with-output
       :stack :push
       ,@(and (not verbosep)
              '(:on (acl2::error) :off :all))
       (make-event
        (define-fn ',name ',args (w state))))))

#!ACL2
(progn
  ;; Returns (mv successp arglist).
  ;; If DEFINE has created a macro wrapper for a function, which may have
  ;; optional or keyword args, we'd like terms involving the function to
  ;; untranslate to a correct call of the macro.  This tries to do that.  Args
  ;; are the arguments provided to the function, macro-args is the lambda-list
  ;; of the macro.
  (defun untrans-macro-args (args macro-args opt/key)
    (cond ((endp macro-args)
           (mv (endp args) nil))
          ((endp args) (mv nil nil))
          ((member-eq (car args) '(&whole &body &rest &allow-other-keys))
           ;; unsupported macro arg type
           (mv nil nil))
          ((member (car macro-args) '(&key &optional))
           (untrans-macro-args args (cdr macro-args) (car macro-args)))
          ((not opt/key)
           ;; just variables, no default
           (mv-let (ok rest)
             (untrans-macro-args (cdr args) (cdr macro-args) opt/key)
             (if ok
                 (mv t (cons (car args) rest))
               (mv nil nil))))
          (t (let* ((default (and (< 1 (len (car macro-args)))
                                  ;; unquote of the second element
                                  (cadr (cadr (car macro-args)))))
                    (key (and (eq opt/key '&key)
                              (cond ((symbolp (car macro-args))
                                     (intern (symbol-name (car macro-args)) "KEYWORD"))
                                    ((symbolp (caar macro-args))
                                     (intern (symbol-name (caar macro-args)) "KEYWORD"))
                                    (t (caaar macro-args)))))
                    (presentp (< 2 (len (car macro-args)))))
               (if (and (not (equal (car args) default))
                        presentp
                        (not (cadr args)))
                   ;; Looks like presentp is nil but the value is not the
                   ;; default, so things must not be of the expected form.
                   (mv nil nil)
                 (mv-let (ok rest)
                   (untrans-macro-args
                    (if presentp (cddr args) (cdr args))
                    (cdr macro-args) opt/key)
                   (if (not ok)
                       (mv nil nil)
                     (let ((args-out
                            (cond ((and (or (eq opt/key '&key) (not rest))
                                        (equal default (car args))
                                        (or (not presentp)
                                            (not (cadr args))))
                                   ;; default value and not supposed to be present, leave out
                                   rest)
                                  (key (list* key (car args) rest))
                                  (t (cons (car args) rest)))))
                       (mv t args-out)))))))))


  (defun untranslate-preproc-for-define (term world)
    (and (consp term)
         (not (eq (car term) 'quote))
         (symbolp (car term))
         (let* ((macro (cdr (assoc (car term) (table-alist 'std::define-macro-fns world)))))
           (and macro
                (let ((macro-args
                       (getprop macro 'macro-args nil
                                'current-acl2-world world)))
                  (and macro-args
                       (mv-let (ok newargs)
                         (untrans-macro-args (cdr term) macro-args nil)
                         (and ok
                              (cons macro newargs)))))))))


  (table user-defined-functions-table
         'untranslate-preprocess
         'untranslate-preproc-for-define))





; ------------------------------------------------------------------------
;
;  More Returns!!!
;
; ------------------------------------------------------------------------

(defxdoc more-returns
  :parents (define returns-specifiers)
  :short "Prove additional return-value theorems about a @(see define)d
function."

  :long "<p>@('more-returns') is a concise syntax for proving additional
theorems about the return-values of your functions, using @(see define)'s
@(':returns')-like syntax.</p>

<p>Example <i>within a define</i>:</p>

@({
    (define my-make-alist (keys)
     :returns (alist alistp)
     (if (atom keys)
         nil
       (cons (cons (car keys) nil)
             (my-make-alist (cdr keys))))
     ///
     (more-returns   ;; no name needed since we're in a define
      (alist true-listp :rule-classes :type-prescription)
      (alist (equal (len alist) (len keys))
             :name len-of-my-make-alist)))
})

<p>Example outside a define:</p>

@({
    (local (in-theory (enable my-make-alist)))
    (more-returns my-make-alist
      (alist (equal (strip-cars alist) (list-fix keys))
             :name strip-cars-of-my-make-alist))
})

<p>General form:</p>

@({
     (more-returns [name] ;; defaults to the current define
       <return-spec-1>
       <return-spec-2>
       ...)
})

<p>Where each @('return-spec') is as described in @(see returns-specifiers) and
shares a name with one of the @(':returns') from the @('define').</p>

<p>Note that any @(see xdoc) documentation strings within these return
specifiers is ignored.  You should usually put such documentation into the
@(':returns') specifier for the @(see define), instead.</p>")

(defun returnspec-additional-single-thm (guts newspec world)
  ;; Only dealing with the single-return-value case.
  ;; Guts is the define we're dealing with.  We assume it has a single return spec.
  ;; Newspec is the new returnspec-p that we want to prove
  (b* ((__function__ 'returnspec-additional-single-thm)
       ((defguts guts) guts)
       (origspec (car guts.returnspecs))
       ((unless (equal (returnspec->name origspec)
                       (returnspec->name newspec)))
        (raise "Expected return value for ~x0 to be named ~x1, found ~x2."
               guts.name
               (returnspec->name origspec)
               (returnspec->name newspec)))
       (badname-okp
        ;; This is meant to avoid name clashes.
        nil)
       ((mv body-subst hint-subst)
        (returnspec-return-value-subst guts.name guts.name-fn
                                       (look-up-formals guts.name-fn world)
                                       (list (returnspec->name origspec)))))
    (returnspec-single-thm guts.name guts.name-fn newspec body-subst hint-subst badname-okp world)))

(defun returnspec-additional-single-thms (guts newspecs world)
  (if (atom newspecs)
      nil
    (append (returnspec-additional-single-thm guts (car newspecs) world)
            (returnspec-additional-single-thms guts (cdr newspecs) world))))

(defun returnspec-additional-multi-thms (guts newspecs world)
  (b* ((__function__ 'returnspec-additional-multi-thms)
       ((defguts guts) guts)
       (fn-formals      (formallist->names guts.formals))
       (fn-return-names (returnspeclist->names guts.returnspecs))
       (ignorable-names (make-symbols-ignorable fn-return-names))
       (binds           `((mv . ,ignorable-names) (,guts.name-fn . ,fn-formals)))
       (new-return-names (returnspeclist->names newspecs))
       ((unless (subsetp new-return-names fn-return-names))
        (raise "No return value named ~x0 for function ~x1."
               (car (set-difference-equal new-return-names fn-return-names))
               guts.name))
       (badname-okp nil)
       ((mv body-subst hint-subst)
        (returnspec-return-value-subst guts.name guts.name-fn fn-formals fn-return-names)))
    (returnspec-multi-thms guts.name guts.name-fn binds newspecs body-subst hint-subst badname-okp world)))

(defun returnspec-additional-thms (guts newspecs world)
  ;; This deals with either the single- or multi-valued return case.
  (b* ((__function__ 'returnspec-additional-thms)
       ((defguts guts) guts)
       ((unless guts.returnspecs)
        (raise "Can't prove additional return-value theorems for ~x0 because ~
                it doesn't have a :returns, so we don't know the names of its ~
                return values.  Consider adding a :returns section."  guts.name))
       ((when (eql (len guts.returnspecs) 1))
        (returnspec-additional-single-thms guts newspecs world)))
    (returnspec-additional-multi-thms guts newspecs world)))

(defun more-returns-fn (args world)
  (b* ((__function__ 'more-returns)
       ((unless (consp args))
        (raise "No arguments?"))
       ((mv name rets)
        (if (symbolp (car args))
            (mv (car args) (cdr args))
          (mv (or (get-define-current-function world)
                  (raise "No function given and not in a /// section?"))
              args)))
       (guts (cdr (assoc name (get-define-guts-alist world))))
       ((unless guts)
        (raise "No define-guts entry for ~x0." name))
       ((defguts guts) guts)
       (returnspecs (parse-returnspecs-aux guts.name rets world))
       (events      (returnspec-additional-thms guts returnspecs world)))
    `(progn . ,events)))

(defmacro more-returns (&rest args)
  `(make-event (more-returns-fn ',args (w state))))




; ------------------------------------------------------------------------
;
;  Defret -- looks like a defthm, but shares some features with :returns/more-returns
;
; ------------------------------------------------------------------------

(defxdoc defret
  :parents (define returns-specifiers)
  :short "Prove additional theorems about a @(see define)d
function, implicitly binding the return variables."

  :long "<p>@('defret') is basically defthm, but has a few extra features.</p>

<p>The main feature is that it automatically binds the declared return values
for a function, which defaults to the most recent function created using @(see
define).</p>

<p>It also supports the @(':hyp') keyword similar to define's @(see
returns-specifiers).</p>

<p>Syntax:</p>

<p>Suppose we have a function created using define with the following
signature:</p>

@({
 (define my-function ((a natp)
                      (b stringp)
                      (c true-listp))
   :returns (mv (d pseudo-termp)
                (e booleanp)
                (f (tuplep 3 f)))
   ...)
})

<p>(The guards and return types aren't important for our purposes, just the
names.)</p>

<p>A @('defret') form like this:</p>

@({
  (defret a-theorem-about-\<fn\>
     :hyp (something-about a b c)
     :pre-bind ((q (foo a b c)))
     (implies (not e)
              (and (consp d)
                   (symbolp (car d))
                   (equal (second d) q)))
     :fn my-function   ;; defaults to the most recent define
     :hints ...
     :rule-classes ...)
 })

<p>will then expand to this:</p>

@({
 (defthm a-theorem-about-my-function
   (implies (something-about a b c)
      (b* ((q (foo a b c))
           ((mv ?d ?e ?f) (my-function a b c)))
        (implies (not e)
                 (and (consp d)
                      (symbolp (car d))
                      (equal (second d) q)))))
   :hints ...
   :rule-classes ...)
})

<p>The @(':hyp :guard') and @(':hyp :fguard') features of @(see
returns-specifiers) are also supported.</p>

<p>@('Defret') does <i>not</i> support the feature where a single function name
specifies a type of a return value.  Perhaps we could support it for functions
with a single return value.</p>

<p>One limitation of @('defret') is that the conclusion term can't refer to a
formal if there is a return value that has the same name.  To work around this,
the @(':pre-bind') argument accepts a list of @(see b*) bindings that occur
before the binding of the return values.  You may also just want to not share
names between your formals and returns.</p>

<h3>Features</h3>

<ul>

<li>The return value names specified by @(':returns') for the function are
bound in the body of the theorem.  This way if the function is changed to
e.g. return an additional value, @('defret') forms don't necessarily need to
change as long as the @(':returns') specifiers are kept up to date.</li>

<li>The return value names are substituted for appropriate expressions in the
hints and rule-classes.  E.g., in the above example, an occurrence of @('d') in
the hints or rule-classes would be replaced by @('(mv-nth 0 (my-function a b
c))').</li>

<li>Any symbol named @('<CALL>') (in any package) is replaced by the call of
the function in the body, hints, and rule-classes.  Similarly any symbol named
@('<FN>') is replaced by the function name or macro alias; additionally, any
symbol named @('<FN!>') is replaced by strictly the function name (not the
macro alias).</li>

<li>The substrings @('\"<FN>\"') and @('\"<FN!>\"') are replaced in the theorem name by
the names of the function/macro alias and function (respectively), so that
similar theorems for different functions can be copied/pasted without editing
the names.</li>

</ul>

")
    

(defun defret-core (name concl-term kwd-alist disablep guts world)
  (b* ((__function__ 'defret)
       ((defguts guts) guts)
       (fn guts.name)
       ((unless guts.returnspecs)
        (raise "No return names provided for ~x0" fn))
       (names (returnspeclist->names guts.returnspecs))
       (ign-names (make-symbols-ignorable names))
       (formals (look-up-formals guts.name-fn world))
       ((mv body-subst hint-subst) (returnspec-return-value-subst fn guts.name-fn formals names))
       (strsubst (returnspec-strsubst fn guts.name-fn))
       (binding `((,(if (consp (cdr ign-names))
                        `(mv . ,ign-names)
                      (car ign-names))
                   (,guts.name-fn . ,formals))))
       (hyp? (assoc :hyp kwd-alist))
       (hyp (cond ((eq (cdr hyp?) :guard) (fancy-hyp (look-up-guard guts.name-fn world)))
                  ((eq (cdr hyp?) :fguard) (fancy-force-hyp (look-up-guard guts.name-fn world)))
                  (t (cdr hyp?))))
       (rule-classes? (assoc :rule-classes kwd-alist))
       (hints? (assoc :hints kwd-alist))
       (otf-flg? (assoc :otf-flg kwd-alist))
       (pre-bind (returnspec-sublis body-subst nil (cdr (assoc :pre-bind kwd-alist))))
       (concl-subst (returnspec-sublis body-subst nil concl-term))
       ((mv ?err concl-trans) (acl2::translate-cmp concl-subst t nil nil 'defret world
                                                   (acl2::default-state-vars nil)))
       ;; Ignore any error from translate, just want to find out if any of the bindings are needed.
       ;; Omit the binding if none of the bound variables are used.
       (binding (and (not err)
                     (intersectp-eq names (acl2::all-vars concl-trans))
                     binding))
       (concl `(b* (,@pre-bind ,@binding) ,concl-subst))
       (thm (if hyp?
                `(implies ,(returnspec-sublis body-subst nil hyp)
                          ,concl)
              concl))
       (thmname (intern-in-package-of-symbol
                 (dumb-str-sublis strsubst (symbol-name name))
                 name)))
    `(,(if disablep 'defthmd 'defthm) ,thmname
      ,thm
      ,@(and hints?        `(:hints ,(returnspec-sublis hint-subst strsubst (cdr hints?))))
      ,@(and otf-flg?      `(:otf-flg ,(cdr otf-flg?)))
      ,@(and rule-classes? `(:rule-classes ,(returnspec-sublis hint-subst nil (cdr rule-classes?)))))))


(defun defret-fn (name args disablep world)
  (b* ((__function__ 'defret)
       ((mv kwd-alist args)
        (extract-keywords `(defret ,name) '(:hyp :fn :hints :rule-classes :pre-bind
                                            :otf-flg)
                          args nil))
       ((unless (consp args))
        (raise "No body"))
       ((when (cdr args))
        (raise "Extra junk: ~x0" (cdr args)))
       (concl-term (car args))
       (fn (let ((look (assoc :fn kwd-alist)))
             (if look (cdr look) (get-define-current-function world))))
       (guts (cdr (assoc fn (get-define-guts-alist world))))
       ((unless guts)
        (raise "No define-guts for ~x0" fn)))
    (defret-core name concl-term kwd-alist disablep guts world)))


(defmacro defret (name &rest args)
  `(make-event (defret-fn ',name ',args nil (w state))))

(defmacro defretd (name &rest args)
  `(make-event (defret-fn ',name ',args t (w state))))



#!acl2
(def-b*-binder ret
  :parents (b*-binders std::returns-specifiers)
  :short "@(see b*) binder for named return values from functions."

  :long "<box><p>BETA.  Interface may change.</p></box>

<p>@('ret') is a very fancy @(see b*) that can be used to treat the return
values from a function as a single bundle which you can then access by their
names.</p>


<h3>Introductory Example</h3>

<p>Here is a function, written with @(see define), that returns two values.</p>

@({
    (define mathstuff ((a natp)
                       (b natp))
      :returns (mv (sum natp)
                   (prod natp))
      (b* ((a (nfix a))
           (b (nfix b)))
        (mv (+ a b)
            (* a b))))
})

<p>Normally, to call this function from @(see b*), you might use an @(see mv)
form like this:</p>

@({
     (b* (((mv mysum myprod) (mathstuff 3 4)))      ;; (:sum 7 :prod 12)
       (list :sum  mysum
             :prod myprod))
})

<p>Using the @('ret') binder, you might instead write:</p>

@({
     (b* (((ret mystuff) (mathstuff 3 4)))          ;; (:sum 7 :prod 12)
       (list :sum  mystuff.sum
             :prod mystuff.prod))
})

<p>In other words, the @('ret') binder lets you to treat all of the return
values for a function as if they were a single aggregate and then refer to the
individually returned values using a @(see defaggregate)- or C-like
@('foo.bar') style syntax.</p>


<h3>Mechanics</h3>

<p>To a first approximation, the @('ret') binder just expands into an
equivalent @(see mv) binder that sets up names like @('mystuff.sum') and
@('mystuff.prod').  However, there are (unfortunately) many subtleties that you
should be aware of.</p>


<h4>Finding the function</h4>

<p>To be able to know the names of the function's return values, the @('ret')
binder obviously needs to \"know\" what function is being invoked.</p>

<p>It does this, completely barbarically, by just looking at the form on the
right hand side of the binder, even before any macro expansion.  For instance,
if we write a binding form like this:</p>

@({
      ((ret myreturn) (myfn ...))
})

<p>Then the @('ret') binder will look at the right-hand side and sees that it
is a call of @('myfn').</p>

<p>Note that it is easy to write right-hand sides that @('ret') <b>does not
understand</b>.  For instance, if you just put a simple identity functions or
macro like @(see time$) around your function call, e.g.,</p>

@({
      ((ret myreturn) (time$ (myfn ...)))
})

<p>then the @('ret') binder will not understand that you are calling @('myfn')
and macroexpansion will fail.  Similarly, you can't use @(see let)-bindings or
similar on the right-hand side.</p>


<h4>Introducing the bindings</h4>

<p>Once we know that the function being invoked is @('myfn'), the @('ret')
binder itself expands into a call of @('patbind-myfn-ret').  Normally, this
should be a function that is introduced for you automatically at @(see define)
time.</p>

<p>Because the @('patbind') function is constructed at @('define') time, it
implicitly \"knows\" the names of the return values for your functions.  It
also \"knows\" which of your function's return values are @(see acl2::stobj)s
and how any such stobjs correspond to the arguments of your function.</p>

<p>Given all of this information, it is possible to construct a suitable @(see
mv) binding that will bind:</p>

<ul>

<li>Each non-stobj return value to a new symbol with a dotted name like
@('myreturn.foo'), @('myreturn.bar'), or similar; and</li>

<li>Each output stobj to the correct stobj name.</li>

</ul>

<p>Aside from some technical details regarding congruent stobjs (see @(see
acl2::stobj)) this is almost straightforward.  However, in purely logical
contexts such as theorem bodies and non-executable functions, it might be
desirable to ignore stobjs and name the stobj outputs just like all the rest.
You can use @(':ignore-stobjs t') as an optional argument to the @('ret')
binder, occurring after the name (if any), to get this behavior.</p>


<h5>Ignorability</h5>

<p>Consider our @('mathstuff') example.  We might imagine that a binding such
as:</p>

@({
     ((ret mystuff) (mathstuff 3 4))
})

<p>would be expanded into:</p>

@({
     ((mv mystuff.sum mystuff.prod) (mathstuff 3 4))
})

<p>This works fine if we use all of the return values, but if we (say) don't
need @('mystuff.prod'), then we'd get errors unless we went out of our way to
use something like @(see set-ignore-ok).  To avoid this, the @('ret') binders
will currently declare <b>all return values as ignorable.</b> We may eventually
revisit this decision and require some kind of more strict checking here.</p>


<h5>Package Naming</h5>

<p>What @(see package) does @('mystuff.sum') belong in?  The most obvious
candidate is to @(see intern) it into the package of the new variable, i.e.,
@('mystuff').  Unfortunately this can sometimes be very confusing.  For
instance, consider a code fragment like this:</p>

@({
     (b* ((fn         (get-function ...))
          ((ret args) (extend-args initial-args ...)))
       (make-answer :fn       fn
                    :args     args.extensions
                    :size     args.size
                    :warnings args.warnings))
})

<p>The problem here is that @('args') is a symbol in the @(see *acl2-exports*)
list.  So, if you submit the above code in a typical package, @('foo'), where
you have imported the symbols from @('*acl2-exports*'), then @('args') is in
the @('acl2') package, but symbols like @('args.extensions'), which are
presumably not imported, will instead be in the @('foo') package.</p>

<p>To avoid this confusion, we scan the form for a symbol with the right name,
regardless of its package.  This scan is done before macros are expanded, so it
may not work with macros that generate names like @('args.extensions').</p>"
  :decls
  ((declare (xargs :guard (and (eql (len forms) 1)
                               (consp (car forms))
                               (symbolp (caar forms))))))
  :body
  (b* ((fncall (car forms))
       (fnname (car fncall)))
    `(,(intern-in-package-of-symbol
        (concatenate 'string "PATBIND-" (symbol-name fnname) "-RET")
        fnname)
      ,args ,forms ,rest-expr)))

(defun find-symbols-with-name (name x acc)
  (if (atom x)
      (if (and (symbolp x)
               (equal (symbol-name x) name))
          (cons x acc)
        acc)
    (find-symbols-with-name
     name (car x) (find-symbols-with-name name (cdr x) acc))))

(defun find-symbol-of-name-in-expr (name rest-expr)
  (let* ((matches (find-symbols-with-name name rest-expr nil))
         (matches (remove-duplicates matches)))
    (cond ((atom matches)
           ;; Found no symbols with this name.  Warn?
           (intern$ name "ACL2"))
          ((consp (cdr matches))
           (er hard? 'patbind-ret
               "Found multiple different symbols with the same name: ~x0" matches))
          (t
           ;; OK good, found just one symbol with this name, use it.
           (car matches)))))



(defun match-define-keyword-formals-with-actuals
  (formals ;; macro formals without any leading &key stuff, ex: (foo (bar 't) baz)
   actuals ;; corresponding actuals, ex: '(:foo 1 :baz 3)
   )
  (b* (((when (atom formals)) nil)
       (formal1 (car formals))
       ((mv name default name-p)
        (cond ((atom formal1) (mv formal1 nil nil))
              ((atom (cdr formal1)) (mv (car formal1) nil nil))
              (t (mv (first formal1)
                     (acl2::unquote (second formal1))
                     (third formal1)))))
       (key (intern$ (symbol-name name) "KEYWORD"))
       (lookup (assoc-keyword key actuals))
       (val (if lookup (cadr lookup) default))
       (rest (match-define-keyword-formals-with-actuals (cdr formals) actuals)))
    (cons (cons name val)
          (if name-p
              (cons (cons name-p (consp lookup)) rest)
            rest))))

(defun match-define-optional-formals-with-actuals
  (formals ;; macro formals without any leading &optional stuff, ex: (foo (bar 't) baz)
   actuals ;; corresponding actuals, ex: '(:foo 1 :baz 3)
   )
  (b* (((when (atom formals)) nil)
       (formal1 (car formals))
       ((when (eq formal1 '&key))
        (match-define-keyword-formals-with-actuals (cdr formals) actuals))
       ((mv name default name-p)
        (cond ((atom formal1) (mv formal1 nil nil))
              ((atom (cdr formal1)) (mv (car formal1) nil nil))
              (t (mv (first formal1)
                     (acl2::unquote (second formal1))
                     (third formal1)))))
       (val (if (consp actuals) (car actuals) default))
       (rest (match-define-optional-formals-with-actuals (cdr formals) (cdr actuals))))
    (cons (cons name val)
          (if name-p
              (cons (cons name-p (consp actuals)) rest)
            rest))))

(defun match-define-formals-with-actuals
  (formals ;; macro formals
   actuals ;; corresponding actuals
   ctx)
  (b* (((when (atom formals)) nil)
       (name (car formals))
       ((when (eq name '&key))
        (match-define-keyword-formals-with-actuals (cdr formals) actuals))
       ((when (eq name '&optional))
        (match-define-optional-formals-with-actuals (cdr formals) actuals))
       ((when (atom actuals))
        (er hard? 'match-define-optional-formals-with-actuals
            "~x0: Not enough arguments" ctx))
       (val (car actuals))
       (rest (match-define-formals-with-actuals (cdr formals) (cdr actuals) ctx)))
    (cons (cons name val) rest)))


(defun patbind-ret-mv-names
  (rets            ;; (return-name . corresponding stobjs-out entry) list
   varname         ;; NIL for ((ret) ...), or varname for ((ret varname) ...)
   formals/actuals ;; see below
   rest-expr       ;; rest-expr from the b*
   ignore-stobjs
   )
  (b* (((when (atom rets)) nil)
       ((cons retname stobj) (car rets))
       ((when (and stobj (not ignore-stobjs)))
        ;; The return name might not be the stobj name, and the stobj name
        ;; might not be the one in use due to congruent stobjs.  So we parse
        ;; the function call (elsewhere) and pair up the formals with actual
        ;; actuals so that we can look up what stobj was passed in and bind
        ;; that.
        (cons (cdr (assoc stobj formals/actuals))
              (patbind-ret-mv-names (cdr rets) varname formals/actuals rest-expr ignore-stobjs)))
       (name (if varname
                 (concatenate 'string (symbol-name varname) "." (symbol-name retname))
               (symbol-name retname)))
       (symbol (find-symbol-of-name-in-expr name rest-expr)))
    (cons symbol
          (patbind-ret-mv-names (cdr rets) varname formals/actuals rest-expr ignore-stobjs))))


(defun patbind-ret-fn (rets macro-formals args forms rest-expr)
  (b* (((mv varname ignore-stobjs)
        (if (eq (car args) :ignore-stobjs)
            (mv nil (cadr args))
          (mv (car args) (cadr (assoc-keyword :ignore-stobjs (cdr args))))))
       (call (car forms))
       (formals/actuals
        (match-define-formals-with-actuals macro-formals (cdr call) (car forms)))
       (mv-names (patbind-ret-mv-names rets varname formals/actuals rest-expr ignore-stobjs)))
    (if (< 1 (len mv-names))
        `(mv-let ,mv-names ,(car forms)
           (declare (ignorable . ,mv-names))
           ,rest-expr)
      `(let ((,(car mv-names) ,(car forms)))
         (declare (ignorable . ,mv-names))
         ,rest-expr))))

(defun make-define-ret-patbinder (guts world)
  (declare (xargs :mode :program))
  (b* (((defguts guts))
       (name (intern-in-package-of-symbol
              (concatenate 'string (symbol-name guts.name) "-RET")
              guts.name)))
    `(def-b*-binder ,name
       :parents nil
       :short nil
       :long nil
       :body
       (patbind-ret-fn ',(pairlis$ (returnspeclist->names guts.returnspecs)
                                   (fgetprop guts.name-fn 'acl2::stobjs-out
                                             nil world))
                       ',(or (fgetprop guts.name 'acl2::macro-args
                                       nil world)
                             (fgetprop guts.name-fn 'acl2::formals
                                       nil world))

                       acl2::args acl2::forms acl2::rest-expr))))



; ----------------- Config ----------------------------------------------------

(logic)

(defconst *define-config-keywords*
  '(:inline
    :t-proof
    :no-function
    :non-executable
    :enabled
    :verbosep
    :progn
    :ignore-ok
    :irrelevant-formals-ok
    :mode
    :normalize
    :split-types
    :well-founded-relation
    :hooks ;; precedence: local to define > config > hooks table
    :ruler-extenders
    :verify-guards))

(local
 (defthm define-config-keywords-okp
   (subsetp-equal *define-config-keywords*
                  *define-keywords*)))

(defun define-config-keyword-value-listp (l)
  (declare (xargs :guard t))
  (cond ((atom l) (null l))
        (t (and (keywordp (car l))
                (member (car l) *define-config-keywords*)
                (consp (cdr l))
                (define-config-keyword-value-listp (cddr l))))))

(defun make-define-config-fn (args)
  (if (atom args)
      nil
    (cons (cons (first args) (second args))
          (make-define-config-fn (cddr args)))))

(defmacro make-define-config (&rest args)
  (declare (xargs :guard (define-config-keyword-value-listp args)))
  `(local
    (table define 'define-config
           (make-define-config-fn (quote ,args)))))

;; ----------------------------------------------------------------------
