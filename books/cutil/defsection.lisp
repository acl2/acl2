; CUTIL - Centaur Basic Utilities
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

(in-package "CUTIL")
(include-book "xdoc/top" :dir :system)

(defxdoc extract-keyword-from-args
  :parents (cutil)
  :short "Get the value for a keyword argument like <tt>:foo value</tt>."

  :long "<p>@(call extract-keyword-from-args) is given <tt>kwd</tt>, which
should be a keyword symbol, and a list of <tt>args</tt> which are typically the
<tt>&amp;rest args</tt> given to a macro.  It scans the list of <tt>args</tt>,
looking for the indicated keyword, and returns <tt>(kwd . value)</tt>, or
<tt>nil</tt> if no such keyword is found.</p>

<code>
 (extract-keyword-from-args :bar '(:foo 3 :bar 5 :baz 7))
   ;; returns (:bar . 5)
</code>

<p>This function is mainly useful for writing macros that mix <tt>&amp;rest</tt>
parts with keyword arguments.  See also @(see throw-away-keyword-parts).</p>

@(def extract-keyword-from-args)")

(defund extract-keyword-from-args (kwd args)
  (declare (xargs :guard (keywordp kwd)))
  (cond ((atom args)
         nil)
        ((eq (car args) kwd)
         (if (consp (cdr args))
             (cons (car args)
                   (cadr args))
           (er hard? 'extract-keyword-from-args
               "Expected something to follow ~s0." kwd)))
        (t
         (extract-keyword-from-args kwd (cdr args)))))

(defxdoc throw-away-keyword-parts
  :parents (cutil)
  :short "Throw away any keyword arguments and their values from a macro
argument list."

  :long "<p>@(call throw-away-keyword-parts) is given a list of arguments that
are typically the <tt>&amp;rest args</tt> given to a macro.  It scans the
arguments for any keyword symbols such as <tt>:foo</tt>, and throws away both
the keyword and the argument that follows it.  For instance,</p>

<code>
 (throw-away-keyword-parts '(x y z :foo 3 :bar 5 blah blah blah))
   --&gt;
 '(x y z blah blah blah)
</code>

<p>This function is mainly useful for writing macros that mix
<tt>&amp;rest</tt> parts with keyword arguments.  See also @(see
extract-keyword-from-args).</p>

@(def throw-away-keyword-parts)")

(defund throw-away-keyword-parts (args)
  (declare (xargs :guard t))
  (cond ((atom args)
         nil)
        ((keywordp (car args))
         (throw-away-keyword-parts (if (consp (cdr args))
                                       (cddr args)
                                     (er hard? 'throw-away-keyword-parts
                                         "Expected something to follow ~s0."
                                         (car args)))))
        (t
         (cons (car args)
               (throw-away-keyword-parts (cdr args))))))



(defxdoc defsection
  :parents (cutil)
  :short "Fancy <tt>(encapsulate nil ...)</tt> with a name and @(see xdoc)
support."

  :long "<p>General form:</p>

<code>
 (defsection name
    [:parents parents]
    [:short short]
    [:long long]
    ... events ...)
</code>

<p>The <tt>parents</tt>, <tt>short</tt>, and <tt>long</tt> keyword are
optional.  If any of these are supplied, they are used to introduce a @(see
defxdoc) command.  Otherwise, no documentation is generated.</p>

<p>The main reasons to use <tt>defsection</tt> are:</p>

<ul>
 <li>It is easier to identify in the <tt>:pbt</tt> history,</li>
 <li>It indents more nicely than <tt>encapsulate</tt> in a vanilla emacs,</li>
 <li>It settles the question of where to put the <tt>defxdoc</tt> command.</li>
</ul>

<p>I often find myself using the following style:</p>

<code>
 (defsection foo
   ... documentation, if applicable ...
   (defund foo (x) ...)
   (local (in-theory (enable foo)))
   (defthm foo-prop1 ...)
   (defthm foo-prop2 ...))
</code>

<p>A nice feature of this is that if you add a new theorem, say
<tt>foo-prop3</tt>, and re-submit the defsection without undoing the previous
one, all of the enabling/disabling still happens correctly.</p>

<p>I may eventually investigate automatically having @(see xdoc) infer that the
events within a section should be included in the manual.</p>")

(defund defsection-fn (name args)
  (declare (xargs :guard t))
  (let ((parents  (cdr (extract-keyword-from-args :parents args)))
        (short    (cdr (extract-keyword-from-args :short args)))
        (long     (cdr (extract-keyword-from-args :long args)))
        (new-args (throw-away-keyword-parts args)))
    `(encapsulate
      ()
      ,@(and (or parents short long)
             `((defxdoc ,name
                 :parents ,parents
                 :short ,short
                 :long ,long)))
      . ,new-args)))

(defmacro defsection (name &rest args)
  (declare (xargs :guard (symbolp name)))
  (defsection-fn name args))

