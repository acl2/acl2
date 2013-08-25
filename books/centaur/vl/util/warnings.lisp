; VL Verilog Toolkit
; Copyright (C) 2008-2011 Centaur Technology
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
; Original author: Jared Davis <jared@centtech.com>

(in-package "VL")
(include-book "defs")
(include-book "defsort/remove-dups" :dir :system)
(local (include-book "arithmetic"))


(defxdoc warnings
  :parents (vl)
  :short "Support for handling warnings and errors."

  :long "<p>During the course lexing, parsing, and translation, we sometimes
want to issue a variety of warnings.</p>

<p>Our original approach to handling warnings was quite ad-hoc.  We sometimes
printed messages to standard output using the @('cw') function, and we
sometimes caused errors using @('er').  But this approach had a number of
problems.  In particular,</p>

<ul>

<li>It led us to see many of the same warnings repeatedly because our various
well-formedness checks were run many times on the same modules in different
stages of the translation.</li>

<li>For some warnings, we did not particularly care about the individual
instances of the warning.  For instance, unless we're interested in fixing the
\"if\" statements to be ?: instead, we don't want to be told about each
occurrence of an if statement.  We just want a higher-level note that hey,
there are 30 if-statements to clean up.</li>

<li>It separated the warnings from the modules they were about, so that some
users might not even see the warnings that had been generated for the modules
they are working on.</li>

<li>There is no way to recover form an error created with @('er'), so if we ran
into some bad problem with a particular module, it could actually prevent us
from translating <i>any</i> of the modules.</li>

</ul>

<p>Our new approach is to create warnings as explicit @(see vl-warning-p)
objects, and to associate these warnings with the modules they are about.  This
allows us to do many things, such as grouping warnings by type, removing
duplicates, and otherwise develop a better way to display and handle these
warnings.</p>

<h3>Accumulating Warnings</h3>

<p>During some transformation or well-formedness check, we might notice that
something is wrong and decide to issue a warning.  In a typical object-oriented
programming language, this would be entirely straightforward: our module class
would have some kind of @('add-warning') method, which would allow us to change
the module by adding an extra warning.</p>

<p>Since our programming language is truly functional, so we cannot modify
existing modules.  Instead, whenever some subsidiary function wants to produce
a warning, its caller must take measures to ensure that the warning is
eventually added to the appropriate module.</p>

<p>Our usual approach is to add a <b>warnings accumulator</b> as an argument to
our functions.  Typically this argument is named @('warnings'), and functions
that take a warnings accumulator return the (possibly extended) accumulator as
one of their return values.</p>

<p>At a high level, then, a high-level module transforming function begins by
obtaining the current warnings for the module, and using these warnings as the
initial accumulator.  The function calls its subsidiary helpers to carry out
its work, and in the process this list of warnings is perhaps extended.
Finally, the function returns a new @(see vl-module-p) which is updated with
the extended list of warnings.</p>

<h3>Fatal Warnings</h3>

<p>One can imagine issuing some warnings on stylistic grounds.  For instance,
we might notice that the width of an expression is implementation dependent, or
that a wire is never used.  Such cases do not pose a problem for our
translation, but we still may wish to issue warnings about these
observations.</p>

<p>On the other hand, many errors are severe enough that they would impact the
veracity of our translation.  For instance, perhaps the module makes use of
unsupported constructs such as inout ports.  In such cases, we wish to abandon
our attempt to translate the module.</p>

<p>In a typical object-oriented programming language, we might have some global
list of modules we are transforming, so that to \"abandon\" a module we would
simply delete it from this list.  But as with the accumulation of warnings, the
functional nature of our programming language complicates this.  If some
subsidiary function wants to throw away a module, then we need to somehow
communicate that to the caller, etc.</p>

<p>Since we are already accumulating warnings, it is convenient to simply
extend our warning objects with a @('fatalp') field that indicates whether the
warning is severe.  Using this approach, most subsidiary functions can simply
add a fatal warning to their warnings accumulator when a true problem is
encountered.</p>

<p>After carrying out some transformation, we can scan the list of modules for
any fatal warnings, and these modules (and their dependents) can be easily
thrown out using @(see vl-propagate-errors).</p>

<h3>Printing Warnings</h3>

See @(see vl::printer) for information on printing warnings.")


(defaggregate vl-warning
  (type msg args fatalp fn)
  :require ((symbolp-of-vl-warning->type
             (symbolp type)
             :rule-classes :type-prescription)
            (stringp-of-vl-warning->msg
             (stringp msg)
             :rule-classes :type-prescription)
            (true-listp-of-vl-warning->args
             (true-listp args)
             :rule-classes :type-prescription)
            (booleanp-of-vl-warning->fatalp
             (booleanp fatalp)
             :rule-classes :type-prescription)
            (symbolp-of-vl-warning->fn
             (symbolp fn)
             :rule-classes :type-prescription))
  :tag :vl-warning
  :parents (warnings)

  :short "Fundamental warning object used throughout VL."

  :long "<p>The @('type') of each warning is a symbol (typically a keyword
symbol) that describes very broadly what kind of warning this is.  There is not
currently any particular discipline or strategy for assigning types to
warnings, but the goal is to be able to use types to filter out or group
warnings.</p>

<p>The @('msg') of each warning is a more detailed message describing what went
wrong.  This string should be acceptable to @(see vl-fmt); it is similar to the
\"format strings\" used by ACL2's @('cw') function, but there are some
important differences.  In particular, we do <b>NOT</b> support all of the
directives that ACL2's printer can use, and we have certain extra support for
printing locations, module names, and so on.</p>

<p>The @('args') are composed with the tilde directives in @('msg') when the
warning is displayed to the user.  That is, a directive like @('~x0') refers to
the first argument, @('~x1') to the second, etc.</p>

<p>The @('fatalp') flag indicates whether this error is so severe that the
module ought to be thrown away and not subjected to further translation.  See
the general discussion in @(see warning) for more information on how this is
used.</p>

<p>The @('fn') is supposed to be the name of the function that caused the
warning.  We added this later, so some warnings might not have this field set
at the moment.</p>")

(deflist vl-warninglist-p (x)
  (vl-warning-p x)
  :elementp-of-nil nil
  :parents (warnings)
  :rest
  ((defthm vl-warninglist-p-of-remove-adjacent-duplicates
     (implies (force (vl-warninglist-p x))
              (vl-warninglist-p (acl2::remove-adjacent-duplicates x)))
     :hints(("Goal" :in-theory (enable acl2::remove-adjacent-duplicates))))))

(defprojection vl-warninglist->types (x)
  (vl-warning->type x)
  :guard (vl-warninglist-p x)
  :nil-preservingp t
  :parents (warnings))


(defsection warn
  :parents (warnings)
  :short "Extend a @(see warnings) accumulator with a non-fatal warning."

  :long "@(ccall warn)

<p>This macro builds a new warning @('w') from the given @('type'), @('msg'),
@('args'), and @('fn'), then conses @('w') onto the @(see warnings) accumulator
@('acc')</p>

<p>Note that @('warn') always builds non-fatal warnings.  If you want to build
a fatal warning instead, use the macro @(see fatal), which has an identical
interface.</p>

<p>There are a couple of interfacing tricks:</p>

<p>Note that @('acc') defaults to @('warnings') because we often use
@('warnings') as the name of the warnings accumulator we are working with.
That is, as long as your warnings accumulator is named @('warnings'), you don't
have to give an @('acc') argument.</p>

<p>Note that @('fn') defaults to @('__function__').  Macros like @(see define)
often bind this symbol to the name of the current function, so if you are using
a macro like this you don't have to give a @('fn') argument.  But you will need
to explicitly give a function name when using raw @(see defun).</p>"

  (defmacro warn (&key type msg args
                       (fn '__function__)
                       (acc 'warnings))
    `(cons (make-vl-warning :type ,type
                            :msg ,msg
                            :args ,args
                            :fatalp nil
                            :fn ,fn)
           ,acc)))

(defsection fatal
  :parents (warnings)
  :short "Extend a @(see warnings) accumulator with a fatal warning."
  :long "@(ccall fatal)

<p>This is identical to @(see warn), except that it produces fatal warnings
instead of non-fatal warnings.</p>"

  (defmacro fatal (&key type msg args
                        (fn '__function__)
                        (acc 'warnings))
    `(cons (make-vl-warning :type ,type
                            :msg ,msg
                            :args ,args
                            :fatalp t
                            :fn ,fn)
           ,acc)))


(define vl-warning-< ((x vl-warning-p)
                      (y vl-warning-p))
  :parents (warnings)
  :short "Basic ordering for warnings."
  :long "<p>This is mainly useful for @(see vl-warning-sort).</p>"

  (b* (((vl-warning x) x)
       ((vl-warning y) y)

       ((when (symbol-< x.type y.type)) t)
       ((unless (eq x.type y.type)) nil)

       ((when (<< x.fn y.fn)) t)
       ((unless (eq x.fn y.fn)) nil)

       ((when (string< x.msg y.msg)) t)
       ((unless (equal x.msg y.msg)) nil)

       ((when (<< x.args y.args)) t)
       ((unless (equal x.args y.args)) nil))

    (<< x.fatalp y.fatalp))

  ///

  (defthm vl-warning-<-transitive
    (implies (and (vl-warning-< x y)
                  (vl-warning-< y z)
                  (force (vl-warning-p x))
                  (force (vl-warning-p y))
                  (force (vl-warning-p z)))
             (vl-warning-< x z))
    :hints(("Goal" :in-theory (enable string<)))))


(defsection vl-warning-sort
  :parents (warnings)
  :short "Mergesort warnings using @(see vl-warning-<)"

  (ACL2::defsort :comparablep vl-warning-p
                 :compare< vl-warning-<
                 :prefix vl-warning)

  ;; Ugh, stupid defsort.  I should be able to rename these functions.
  (defthm vl-warning-list-p-is-vl-warninglist-p
    (equal (vl-warning-list-p x)
           (vl-warninglist-p x))
    :hints(("Goal" :in-theory (enable vl-warning-list-p))))

  (defthm vl-warninglist-p-of-vl-warning-sort
    (implies (force (vl-warninglist-p x))
             (vl-warninglist-p (vl-warning-sort x)))
    :hints(("Goal"
            :in-theory (disable vl-warning-sort-creates-comparable-listp)
            :use ((:instance vl-warning-sort-creates-comparable-listp (ACL2::x x)))))))


(define vl-clean-warnings ((x vl-warninglist-p))
  :returns (ans vl-warninglist-p :hyp :fguard)
  :parents (warnings)
  :short "Sort warnings and remove duplicates."

  (ACL2::remove-adjacent-duplicates
   (vl-warning-sort
    (redundant-list-fix x))))


(define vl-remove-warnings ((types symbol-listp)
                            (x vl-warninglist-p))
  :returns (ans vl-warninglist-p :hyp :guard)
  :parents (warnings)
  :short "Remove warnings of certain types."
  :long "<p>This can be useful to filter out mundane warnings that you do not
want to bother the user with.</p>"

  (cond ((atom x)
         nil)
        ((member (vl-warning->type (car x)) types)
         (vl-remove-warnings types (cdr x)))
        (t
         (cons (car x) (vl-remove-warnings types (cdr x))))))


(define vl-keep-warnings ((types symbol-listp)
                          (x vl-warninglist-p))
  :returns (ans vl-warninglist-p :hyp :guard)
  :parents (warnings)
  :short "Keep only warnings of certain types."
  :long "<p>This can be useful to highlight certain warnings that are of
particular interest.</p>"

  (cond ((atom x)
         nil)
        ((member (vl-warning->type (car x)) types)
         (cons (car x) (vl-keep-warnings types (cdr x))))
        (t
         (vl-keep-warnings types (cdr x)))))


(define vl-some-warning-fatalp ((x vl-warninglist-p))
  :parents (warnings)
  :short "Check if any warning is marked as fatal."

  (if (atom x)
      nil
    (or
     ;; MBE gives us an always-boolean result.
     (mbe :logic (if (vl-warning->fatalp (car x)) t nil)
          :exec (vl-warning->fatalp (car x)))
     (vl-some-warning-fatalp (cdr x))))

  ///

  (defthm vl-some-warning-fatalp-when-not-consp
    (implies (not (consp x))
             (equal (vl-some-warning-fatalp x)
                    nil)))

  (defthm vl-some-warning-fatalp-of-cons
    (equal (vl-some-warning-fatalp (cons a x))
           (or (if (vl-warning->fatalp a) t nil)
               (vl-some-warning-fatalp x))))

  (defthm vl-some-warning-fatalp-of-append
    (equal (vl-some-warning-fatalp (append x y))
           (or (vl-some-warning-fatalp x)
               (vl-some-warning-fatalp y))))

  (defthm vl-some-warning-fatalp-of-list-fix
    (equal (vl-some-warning-fatalp (list-fix x))
           (vl-some-warning-fatalp x)))

  (defthm vl-some-warning-fatalp-of-rev
    (equal (vl-some-warning-fatalp (rev x))
           (vl-some-warning-fatalp x)))

  (defthm vl-some-warning-fatalp-of-revappend
    (equal (vl-some-warning-fatalp (revappend x y))
           (or (vl-some-warning-fatalp x)
               (vl-some-warning-fatalp y)))))


(define vl-some-warning-of-type-p ((types symbol-listp)
                                   (x vl-warninglist-p))
  :parents (warnings)
  :short "Check if there are any warnings of certain types."
  :long "<p>Note that we leave this function enabled.</p>"

  (mbe :logic
       (intersectp-equal types (vl-warninglist->types x))
       :exec
       (cond ((atom x)
              nil)
             ((member (vl-warning->type (car x)) types)
              t)
             (t
              (vl-some-warning-of-type-p types (cdr x))))))



