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
(include-book "tools/bstar" :dir :system)
(include-book "xdoc/top" :dir :system)
(include-book "misc/book-thms" :dir :system)


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

  :long "<p>The main reasons to use <tt>defsection</tt> are:</p>

<ul>
 <li>It is easier to identify in the <tt>:pbt</tt> history,</li>
 <li>It indents more nicely than <tt>encapsulate</tt> in a vanilla emacs,</li>
 <li>It settles the question of where to put the <tt>defxdoc</tt> command, and</li>
 <li>It can automatically add the definitions/theorems you supply into the
     documentation for your section.</li>
</ul>

<p>General form:</p>

<code>
 (defsection name
    [:parents   parents]
    [:short     short]
    [:long      long]
    [:autodoc   autodoc]
    [:extension topic]
    ... events ...)
</code>

<p>For example,</p>

<code>
 (defsection foo
   :parents (parent1 parent2 ...)
   :short \"@@(call foo) is like @@(see bar), but better when...\"
   :long \"The main difference is ...\"

   (defund foo (x) ...)
   (local (in-theory (enable foo)))
   (defthm foo-thm1 ...)
   (defthm foo-thm2 ...))
</code>

<h3>Ordinary Sections</h3>

<p>The <tt>:parents</tt>, <tt>:short</tt>, and <tt>:long</tt> keywords are
optional.  If any of these keywords are provided, they will be used to
introduce a @(see defxdoc) command; otherwise no documentation will be
generated.</p>

<p>By default, the <tt>:long</tt> string you give will be automatically
extended with a \"Definitions and Theorems\" part that lists all
the (non-local) definitions and theorems introduced in the section.  This makes
it easy to keep the documentation up-to-date as you add and remove theorems to
the section.  In the above example, the <tt>:long</tt> field would be extended
with:</p>

<code>
 &lt;h3&gt;Definition and Theorems&lt;/h3&gt;
 @@(def foo)
 @@(thm foo-thm1)
 @@(thm foo-thm2)
</code>

<p>If you do not want this automatic documentation, you can turn it off with
<tt>:autodoc nil</tt>.</p>

<p>By the way, I particularly like to use the above style, where a
<tt>defund</tt> is immediately followed by a local <tt>enable</tt>, because if
I want to add a new theorem, say <tt>foo-thm3</tt>, then I can just re-submit
the defsection without undoing the previous one, and all of the enabling and
disabling still happens correctly.</p>

<h3>Extended Sections</h3>

<p>The <tt>:extension</tt> keyword allows you to say that this section is a
continuation of a previously introduced concept.  When <tt>:extension
topic</tt> is provided, then <tt>topic</tt> must be the name of a previously
documented @(see xdoc) section, and you are not allowed to use
<tt>:parents</tt> or <tt>:short</tt> since the topic already exists.</p>

<p>The main purpose of an <tt>:extension</tt> section is to add additional
documentation, either via the <tt>:long</tt> string or via the automatic
documentation generation features of <tt>defsection</tt>.  The documentation
obtained this way is just appended onto the existing <tt>:long</tt> for the
topic.</p>

<p>For example, if we have already given the section <tt>foo</tt> with basic
theorems, above we now want to add a bunch of additional theorems about it,
we might write something like this:</p>

<code>
 (defsection advanced-theorems-about-foo
   :extension foo
   (defthm foo-thm3 ...)
   (defthm foo-thm4 ...))
</code>

<p>This will then append the definitions of <tt>foo-thm3</tt> and
<tt>foo-thm4</tt> onto the end of the documentation for <tt>foo</tt>.</p>")

(defun bar-escape-chars (x)
  (declare (xargs :mode :program))
  (cond ((atom x)
         nil)
        ((eql (car x) #\|)
         (list* #\\ #\| (bar-escape-chars (cdr x))))
        (t
         (cons (car x) (bar-escape-chars (cdr x))))))

(defun bar-escape-string (x)
  (declare (xargs :mode :program))
  (coerce (bar-escape-chars (coerce x 'list)) 'string))

(defun full-escape-symbol (x)
  (declare (xargs :mode :program))
  (concatenate 'string "|" (bar-escape-string (symbol-package-name x)) "|::|"
               (bar-escape-string (symbol-name x)) "|"))

(defun formula-info-to-defs1 (entries)
  ;; See misc/book-thms.lisp.  Entries should be the kind of structure that
  ;; new-formula-info produces.  We turn it into a list of "@(def fn)" entries.
  ;; This is a hack.  We probably want something smarter.
  (declare (xargs :mode :program))
  (cond ((atom entries)
         nil)
        ((and (consp (car entries))
              (symbolp (caar entries)))
         (cons (concatenate 'string "@(def " (full-escape-symbol (caar entries)) ")")
               (formula-info-to-defs1 (cdr entries))))
        (t
         (formula-info-to-defs1 (cdr entries)))))

(defun join-strings (strs sep)
  (declare (xargs :mode :program))
  (cond ((atom strs)
         "")
        ((atom (cdr strs))
         (car strs))
        (t
         (concatenate 'string (car strs) sep (join-strings (cdr strs) sep)))))

(defun formula-info-to-defs (headerp entries)
  ;; BOZO make this nicer
  (declare (xargs :mode :program))
  (let ((strs (formula-info-to-defs1 entries)))
    (if strs
        (concatenate 'string
                     (if headerp "<h3>Definitions and Theorems</h3>" "")
                     (join-strings strs (coerce (list #\Newline) 'string)))
      "")))

(defun defsection-fn (wrapper ; (encapsulate nil) or (progn)
                      name args)
  (declare (xargs :mode :program))
  (b* ((parents     (cdr (extract-keyword-from-args :parents args)))
       (short       (cdr (extract-keyword-from-args :short args)))
       (long        (cdr (extract-keyword-from-args :long args)))
       (extension   (cdr (extract-keyword-from-args :extension args)))
       (defxdoc-p   (and (not extension)
                         (or parents short long)))

       (- (or (not extension)
              (and (not parents)
                   (not short))
              (er hard? 'defsection-fn "When using :extension, you cannot ~
                  give a :parents or :short field.")))

       (autodoc-arg (extract-keyword-from-args :autodoc args))
       (autodoc-p   (and (or defxdoc-p extension)
                         (or (not autodoc-arg)
                             (cdr autodoc-arg))))

       (new-args (throw-away-keyword-parts args)))

    (if (not autodoc-p)
        `(with-output
           :stack :push
           :off :all
           :on error  ;; leave errors on, or you can think forms succeeded when they didn't.
           (progn
             ,@(and defxdoc-p
                    `((defxdoc ,name
                        :parents ,parents
                        :short ,short
                        :long ,long)))
             (with-output :stack :pop
               (,@wrapper
                 ;; A silly value-triple so that an empty defsection is okay.
                 (value-triple :invisible)
                 . ,new-args))
             ,@(and extension
                    long
                    `(xdoc-extend ,extension ,long))))

      ;; Fancy autodoc stuff.
      (let ((marker `(table acl2::intro-table :mark ',name)))
        `(with-output
           :stack :push
           :off :all
           :on error
           (progn
             ,marker
             (with-output :stack :pop
               (,@wrapper
                 ;; A silly value-triple so that an empty defsection is okay.
                 (value-triple :invisible)
                 . ,new-args))
             (make-event
              (let* ((name      ',name)
                     (parents   ',parents)
                     (short     ',short)
                     (extension ',extension)
                     (wrld      (w state))
                     (trips     (acl2::reversed-world-since-event wrld ',marker nil))
                     (info      (reverse (acl2::new-formula-info trips wrld nil)))
                     (autodoc   (formula-info-to-defs (not extension) info))
                     (long      (concatenate 'string
                                             ',(or long "")
                                             (coerce (list #\Newline #\Newline) 'string)
                                             autodoc)))
                (if extension
                    `(xdoc-extend ,extension ,long)
                  `(defxdoc ,name
                     :parents ,parents
                     :short ,short
                     :long ,long))))
             (value-triple ',name)))))))

(defmacro defsection (name &rest args)
  (declare (xargs :guard (symbolp name)))
  (defsection-fn '(encapsulate nil) name args))



(defxdoc defsection-progn
  :parents (cutil)
  :short "Fancy <tt>(progn ...)</tt> with a name and @(see xdoc) support."
  :long "<p>The <tt>defsection-progn</tt> macro is like @(see defsection)
except that it generates a <tt>(progn ...)</tt> instead of an <tt>(encapsulate
nil ...)</tt>.</p>

<p>This has a number of consequences, mostly having to do with the scope of
<tt>local</tt> events within the section.  A <tt>defsection-progn</tt>
basically does not introduce a new scope, whereas a <tt>defsection</tt>
does.</p>")

(defmacro defsection-progn (name &rest args)
  (declare (xargs :guard (symbolp name)))
  (defsection-fn '(progn) name args))


#||

(defxdoc test :short "Test of defsection")

(defsection foo1
  :parents (test)
  :autodoc nil
  (defun foo1 (x) x))

(defsection foo2
  :parents (test)
  (defun foo2 (x) x))

(defsection foo3
  :parents (test)
  :short "Section for foo3"
  :long "<p>Foo3 is wonderful.</p>"

  (defund foo3 (x) (+ 1 x))

  (local (in-theory (enable foo3)))

  (defthm natp-of-foo3
    (implies (natp x)
             (natp (foo3 x))))

  (local (defthm foo3-lemma
           (implies (equal x 3)
                    (equal (foo3 x) 4))))

  (defmacro foo3-alias (x)
    `(foo3 ,x))

  (defsection bar
    :parents (test)
    :short "Section for bar"
    :long "<p>Bar is wonderful.</p>"
    (defund bar (x) (+ 2 x))))

;; BOZO the theorems in the nested section are leaking out into the superior
;; section... ugh.


(defsection foo3-advanced
  :extension foo3

  (local (in-theory (enable foo3)))

  (defthm posp-of-foo3
    (implies (natp x)
             (posp (foo3 x))))

  (defthm oddp-of-foo3
    (implies (evenp x)
             (oddp (foo3 x)))))


(defsection foo3-advanced-more
  :extension foo3
  :long "<h3>Even more theorems!</h3>"

  (local (in-theory (enable foo3)))

  (defthm integerp-of-foo3
    (implies (integerp x)
             (integerp (foo3 x)))))




||#

