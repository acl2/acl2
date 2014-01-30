; Best Practices Documentation
; Copyright (C) 2013-2014 Centaur Technology
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

(in-package "ACL2")
(include-book "xdoc/top" :dir :system)

(defxdoc best-practices
  :parents (books)
  :short "Recommended best practices for ACL2 books."

  :long "<h2>DRAFT</h2>

<p>This is a preliminary document.  Feedback is very much welcome and
appreciated.  Please direct feedback to the acl2-books list or to Jared
Davis.</p>")

(local (xdoc::set-default-parents best-practices))


(defxdoc file-extensions
  :short "Conventions to follow for choosing file extensions like @('.lisp'),
@('.lsp'), and @('.acl2') files."

  :long "<h4>Recommendations</h4>

<ol>

<li>Certifiable books should use the extension @('.lisp')</li>

<li>Certification commands (\"portcullis\" stuff) should use the extension
@('.acl2')</li>

<li>Other Lisp files (package definitions, raw lisp code) should that are not
certifiable books should use @('.lsp')</li>

</ol>

<h4>Rationale</h4>

<p>These conventions allow build systems like @(see cert.pl) to automatically
distinguish between what should be certified and what should not.</p>

<p>Once a user is familiar with these conventions, they act as a signal about
what files are likely to be of interest.</p>")

(defxdoc file-names
  :short "Restrictions to follow for naming books, directories, and other
files."

  :long "<h4>Recommendations</h4>

<ol>

<li>All file names and directory should use strictly lower-case, printable
ASCII letters.</li>

<li>Spaces and odd punctuation characters (e.g., beyond dash, underscore, and
period) should not be used.</li>

<li>Dashes should generally be preferred over underscores.</li>

</ol>

<h4>Rationale</h4>

<p>These name restrictions encourage portability across different operating
systems, file systems, etc.  (Some file systems restrict certain characters, or
differ from one another with respect to case sensitivity.)</p>

<p>Avoiding file names with spaces and special characters helps to makes it
easier to write scripts or to write quick, one-off shell commands to process
the books without worrying overly much about escaping.</p>")


(defxdoc working-with-packages
  :short "How to set up new package and portcullis files."

  :long "<h4>Recommendations</h4>

<p>Here is a basic recipe to follow for creating new directories that make use
of packages:</p>

<dl>

<dt>@('foo/package.lsp') &mdash; main package definitions</dt>

<dd>
@({
    ;; load other packages needed to define our new packages...
    (include-book \"lib1/portcullis\" :dir :system)
    (include-book \"lib2/portcullis\" :dir :system)

    ;; define our new packages
    (defpkg \"PKG1\" ...)
    (defpkg \"PKG2\" ...)

    ;; optionally set up useful exports lists
    (defconst PKG1::*pkg1-exports* ...)
    (defconst PKG2::*pkg2-exports* ...)
})</dd>

<dt>@('foo/portcullis.lisp') &mdash; a nearly empty book</dt>

<dd>
@({
     (in-package \"FOO\")
})
</dd>

<dt>@('(foo/portcullis.acl2') &mdash; certification instructions for the portcullis book</dt>

<dd>
@({
     (ld \"package.lsp\")
})
</dd>


<dt>@('foo/cert.acl2') &mdash; certification instructions for the other books</dt>

<dd>
@({
     (include-book \"portcullis\")
     ;; cert-flags: ? t [:ttags :all ...]
})
</dd>


<dt>@('foo/acl2-customization.lsp') &mdash; merely for convenience</dt>

<dd>
@({
     (ld \"~/acl2-customization.lsp\" :ld-missing-input-ok t)
     (ld \"package.lsp\")
     (in-package \"FOO\")
})
</dd>
</dl>

<h4>Rationale</h4>

<p>Using the same names for @('package.lsp') and @('portcullis.lisp') is a nice
convention that improves consistency and discoverability.</p>

<ul>
<li>The @('.lsp') extension helps Emacs realize the package file is a Lisp file</li>
<li>It also helps @(see cert.pl) know it is not a certifiable book.</li>
</ul>

<p>The empty portcullis book is a useful trick.  Including this book, rather
than directly @(see ld)'ing the package from @('cert.acl2'), means that when
several books from the same directory are loaded into the same session, each of
their individual @('.cert') files contain commands like:</p>

@({
   (include-book \"portcullis\")
})

<p>instead of:</p>

@({
    (defpkg \"FOO\" (union-eq ...))
})

<p>This is good because ACL2 can quickly realize that the @(see include-book)
form is redundant and not do any work, instead of having to re-evaluate the
package commands to see if it is indeed the same.</p>

<p>Having a customization file that starts ACL2 up in \"the right package\" is
often very convenient while developing.  Loading the user's customization file
first, if one exists, is nice for users who have their own macros.</p>")


(defxdoc theory-management
  :short "Recommendations related to enabling and disabling functions and
theorems."

  :long "<p>The best practices depend somewhat on the kind of book you are
writing.  We distinguish between <i>Widget Libraries</i> and <i>Core
Libraries</i>.</p>

<h3>Widget Libraries</h3>

<p>Scenario: your library describes a particular kind of \"Widget:\" it defines
what Widgets are, provides some useful algorithms for operating on Widgets, and
proves some theorems about the properties of Widgets and these algorithms.</p>

<h4>Recommendations</h4>

<ol>

<li>Avoid any non-local inclusion of arithmetic libraries</li>

<li>Avoid any non-local @('(in-theory ...)') events that involve built-in ACL2
functions.  For instance, do not do: @('(in-theory (enable append))').</li>

<li>Try to respect the ACL2 namespace, e.g., do not define new functions in the
ACL2 package, especially with short or generic names, etc.</li>

</ol>

<h4>Rationale</h4>

<ul>

<li>You would expect that loading a Widget library should generally just give
you definitions and lemmas that are about Widgets.</li>

<li>You would not expect a Widget library to change how you reason about other
concepts that are unrelated to Widgets.</li>

<li>Non-local arithmetic includes may make your Widget library incompatible
with other arithmetic libraries.</li>

</ul>

<h3>Core Libraries</h3>

<p>Scenario: your library is meant to assist with reasoning about built-in ACL2
functions, for instance:</p>

<ul>
<li>arithmetic functions like +, -, *, /, floor, mod, logand;</li>
<li>list functions like append, len, nth, member, subsetp;</li>
<li>string functions like coerce, concatenate, subseq;</li>
<li>system functions like io routines and state updates;</li>
<li>meta functions like pseudo-termp, disjoin, conjoin-clauses;</li>
</ul>

<p>Since your library is inherently about existing ACL2 functions rather than
new definitions, the Widget-library recommendations do not necessarily
apply.</p>")



(defxdoc conventional-normal-forms
  :short "Recommendations for respecting global conventions that the ACL2 books
authors have agreed to."

  :long "<p>In many cases there are alternate normal forms that you can use for
the same concept.  For greater compatibility between libraries, we prefer to
use various forms as described below.</p>

<h4>Disable @(see mv-nth)</h4>

<p>Recommendations:</p>

<ol>
<li>Write lemmas in terms of @('(mv-nth n ...)') instead of @('(caddr ...)')</li>
<li>Include the @('tools/mv-nth') book</li>
</ol>

<p>Rationale</p>

<ul>

<li>It's important to have a standard here since multiply-valued functions
are needed in many libraries.</li>

<li>Leaving @('mv-nth') enabled is worse because it leads to different normal
forms for slot 0 versus other slots.  That is, ACL2 will rewrite @('(mv-nth 0
...)')  to @('(car ...)') but will not rewrite @('(mv-nth 1 ...)') unless
additional rewrite rules are added.</li>

<li>Writing theorems in terms of @('mv-nth') is compatible with using @(see b*)
bindings in theorems, which is particularly nice.</li>

</ul>

<h4>BOZO Other important normal forms we should all agree on?</h4>

<p>Member versus Memberp?</p>")



(defsection naming-rewrite-rules
  :short "Recommendations for writing understandable rule names."
  :long "

<h4>Strong Recommendations</h4>

<p>Do not non-locally use common names for local lemmas, such as:</p>

@({
lemma*   crock*    crux*        a0 b0 c0 ...
temp*    goal*     main-goal*   a1 b1 c1
stupid*  wtf*      corollary*   ...
})

<h4>Rationale</h4>

<p>Using these names may make your book hard to include for people
who (perhaps via macros) are already using these names or who may want to use
them.</p>

<h4>Weak Recommendations</h4>

<ol>

<li>For unconditional, equality-based rules, we base the rule name on a reading
of the left-hand side, using @('of') as a separator.  This is meant to boost
readability when the function names involved have their own hyphens.</li>

<li>For rules with simple hypotheses, we add @('-when-hyp') to the name.</li>

<li>For rules about other equivalence relations, we add @('-under-equiv') to the
name.</li>

</ol>

<h5>Examples</h5>

@({
    (defthm append-of-cons
      (equal (append (cons a x) y)
             (cons a (append x y))))

    (defthm true-listp-of-append
      (equal (true-listp (append x y))
             (true-listp y)))

    (defthm member-when-atom         ;; lhs is (member a x)
      (implies (atom x)
               (not (member a x))))

    (defthm logbitp-of-0-when-bitp
      (implies (bitp b)
               (equal (logbitp 0 b)
                      (equal b 1))))

    (defthm append-under-iff         ;; lhs is (append x y)
      (iff (append x y)
           (or (consp x)
               y)))

   (defthm union-equal-under-set-equiv  ;; lhs is (union-equal a b)
     (set-equiv (union-equal a b)
                (append a b)))
})

<p>Obviously you can take this too far.  For complex theorems, these
recommendations would lead to names that are far too long.  Think of them as a
starting point, not a mandate.</p>

<h4>Rationale</h4>

<p>Following these conventions can help lead to more consistently named rules
whose effect may be more easy to guess.</p>")
