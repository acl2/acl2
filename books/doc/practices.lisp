; Best Practices Documentation
; Copyright (C) 2013-2014 Centaur Technology
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
; Contributing author: Grant Jurgensen <grant@kestrel.edu>

(in-package "ACL2")
(include-book "xdoc/constructors" :dir :system)
(include-book "xdoc/top" :dir :system)

(defxdoc best-practices
  :parents (books)
  :short "Recommended best practices for ACL2 books."

  :long
  (xdoc::topstring
   (xdoc::p "Here we summarize various style and formatting principles commonly
             accepted and employed across the ACL2 repository. The goal is to
             avoid opinionated rules and only highlight conventions which are
             widely agreed upon. The advice included here is intended to apply
             to the majority of cases. There may be exceptions in which a given
             rule ought be ignored. Use your best judgment.")
   (xdoc::p "See the @(see developers-guide-style) for a more specific style
             guide for changes to the core ACL2 system (not necessary if you
             are just developing books).")
   (xdoc::h3 "Whitespace and Special Characters")
   (xdoc::ul
    (xdoc::li "Avoid using tabs, as they may render inconsistently across
               machines and editors. Use spaces instead.")
    (xdoc::li "Do not leave ``trailing whitespace'' at the end of your lines
               (see @(see remove-whitespace)). Trailing whitespace can add
               noise to Git commits and disrupt navigation in the editor.")
    (xdoc::li "Unicode characters should be avoided in identifiers, but are
               permissible in comments and strings. (Keep in mind that some
               string utilities may not behave as expected, for instance @(tsee
               length) may return the number of bytes instead of the number of
               unicode code points.)")
    (xdoc::li "Avoid consecutive blank lines.")
    (xdoc::li "Line breaks should use the posix-style newline
               (i.e. @('\"\\n\"'), not @('\"\\r\\n\"')). Linux and Mac
               developers should not need to worry about this. Windows
               developers may need to be more careful that their editor or
               other tools uses posix-style newlines.")
    (xdoc::li "Files should end with a newline. (Note, we mean a newline, not a
               blank line.) This is a posix-standard. Most editors should
               handle this automatically."))
   (xdoc::h3 "Comments")
   (xdoc::ul
    (xdoc::li "Comments should begin with a single space. E.g.:"
              (xdoc::codeblock "; This is a comment.")
              (xdoc::i "not")
              (xdoc::codeblock ";This is a comment."))
    (xdoc::li "Books should begin with a copyright and licensing header (which
               may just point to the repository's top-level LICENSE file).")
    (xdoc::li "Use two semicolons for inline comments which should be indented
               as a form would be. This is a standard practice in Common Lisp,
               and editors like Emacs will indent such comments
               appropriately.")
    (xdoc::li "Avoid commented code which would disrupt the s-expression
               balance if uncommented. For instance, instead of this:"
              (xdoc::codeblock
               "(let ((x foo)"
               "      ;; (y bar))"
               "      )"
               "  baz"
               "  )")
              "do this:"
              (xdoc::codeblock
               "(let ((x foo)"
               "      ;; (y bar)"
               "      )"
               "  baz"
               "  )"))
    (xdoc::li "Consider whether comments would be more appropriate as "
              (xdoc::seetopic "xdoc" "XDOC")
              " documentation."))
   (xdoc::h3 "Documentation")
   (xdoc::ul
    (xdoc::li (xdoc::seetopic "xdoc" "XDOC")
              " short forms should be in ``sentence case,'' not ``title case.''
               They should end with a period, even if they are not a full
               sentence.")
    (xdoc::li (xdoc::seetopic "xdoc" "XDOC")
              " short forms should not span multiple paragraphs, or include
               code blocks, tables, headers, etc.")
    (xdoc::li "When making changes to "
              (xdoc::seetopic "xdoc" "XDOC")
              ", make sure the manual still builds successfully by invoking
               @('make manual'). After building, open your local manual and
               check that your topics don't appear under @(see
               xdoc::missing-parents).")
    (xdoc::li "Avoid traditional Common Lisp documentation strings (AKA
               ``docstrings''). Use "
              (xdoc::seetopic "xdoc" "XDOC")
              " instead."))
   (xdoc::h3 "Naming Conventions")
   (xdoc::ul
    (xdoc::li "Consider ending predicates with ``p'' (or ``-p,'' especially if
               needed for clarity). This is a convention inherited from Common
               Lisp.")
    (xdoc::li "For ordinary identifiers, avoid uppercase and use hyphens to
               delimit words (a style sometimes called ``dash-case'',
               ``kebab-case'', or ``lisp-case''). E.g., ``my cool function''
               would be rendered @('my-cool-function').")
    (xdoc::li "See @(see naming-rewrite-rules) for recommendations regarding
               the naming of rewrite rules."))
   (xdoc::h3 "Formatting")
   (xdoc::ul
    (xdoc::li "Multiline @('if') forms should be formatted as follows:"
              (xdoc::codeblock
               "(if x"
               "    y"
               "  z)")
              "That is, 4 spaces for the ``then'' term, and 2 spaces for the
               ``else'' term. If your Emacs auto-indents such forms
               incorrectly, consider adding the following to your Emacs
               configuration:"
              (xdoc::codeblock
               "(eval-after-load 'cl-indent"
               "  '(put 'if 'common-lisp-indent-function 2))"))
    (xdoc::li "Ensure that parentheses are balanced. Usually, books will fail
               to certify if the are imbalanced, but some Lisps may be overly
               forgiving in this respect. If you have the @(csee emacs) plugin
               loaded, you can use @('M-x find-unbalanced-parentheses') to look
               for such issues."))
   (xdoc::h3 "Packages")
   (xdoc::ul
    (xdoc::li "The use of packages is highly encouraged. This helps to avoid
               name clashes and polluting the default namespace. See @(see
               working-with-packages) for further guidance.")
    (xdoc::li "If you are defining a new package name, check to see that the
               name is not already in use. You can list all packages defined
               across the repository using the following @('grep') command:"
              (xdoc::codeblock
                "grep -hr --include='*.lsp' --include='*.acl2' -E '\\(defpkg \"[^\"]*\"' . \\"
                "  | sed -n 's/[^\"]*\"\\([^\"]*\\)\".*/\\1/p' \\"
                "  | sort | uniq")))
   (xdoc::h3 "Theory Events")
   (xdoc::ul
    (xdoc::li "Top-level @('include-book') and @('in-theory') events should be
               at the top of the book. Intermixing @('include-book') and
               @('in-theory') events with function definitions and theorems can
               make it more difficult for the maintainer to understand the
               state of the current theory.")
    (xdoc::li "@('include-book') and @('in-theory') events should be @(see
               local) where possible, unless they support the main purpose of
               the book and are intended to be ``exported.'' This allows
               libraries to be more modular and avoids cluttering the
               end-user's world.")
    (xdoc::li "Use relative paths in @('include-book') events only when
               including books contained within the same library. Otherwise,
               use @(':dir :system'). Never use absolute paths.")
    (xdoc::li "Most functions (especially non-recursive function) should be
               disabled by default, unless they are best understood as simple
               aliases/wrappers.")
    (xdoc::li "Sets of rules which are known to cause rewrite loops should be
               declared @(see incompatible) as a @(see theory-invariant).")
    (xdoc::li "See also @(see theory-management)."))
   (xdoc::h3 "Proofs")
   (xdoc::ul
    (xdoc::li "Try to avoid subgoal hints. These can make proofs brittle and
               difficult to maintain. If it is not sufficient to apply hints to
               the top-level goal, consider factoring out a subgoal into an
               auxiliary lemma.")
    (xdoc::li "Generally speaking, the less hints for a proof, the
               better. Consider whether @(':use') or @(':expand') hints may
               suggest good general-purpose rules (this is not always the
               case).")
    (xdoc::li "Try to avoid brittle @(see proof-builder) instructions (given as
               an argument to the @(':instructions') keyword argument of either
               @(tsee defthm) or a goal "
              (xdoc::seetopic "hints" "hint")
              ") which may be difficult to maintain.")
    (xdoc::li "Avoid short proof timeout windows which could fail on slower
               machines (e.g. via @(tsee with-prover-time-limit), @(tsee
               acl2s::set-defunc-timeout), etc.). If possible, avoid timeout
               windows altogether, or use step limits instead (e.g. @(tsee
               with-prover-step-limit))."))
   (xdoc::h3 "The Build")
   (xdoc::ul
    (xdoc::li "Avoid introducing new Makefiles when possible, relying instead
               on the existing top-level GNUMakefile. (See also @(see
               books-certification).)"))
   (xdoc::h3 "Book Style Consistency")
   (xdoc::ul
    (xdoc::li "There are certain styles which are not universal across the
               repository, but which should be consistent within a given book
               or library. Book style should be respected when making edits.")
    (xdoc::li "Try to match the line width of a file. Common line widths are 79
               or 80.")
    (xdoc::li "A book should use either @(tsee defun) or @(tsee define), not
               both.")
    (xdoc::li "A book should use either @(tsee defthm) or @(tsee defrule), not
               both."))))

(local (xdoc::set-default-parents best-practices))

(defxdoc finite-reasoning
  :short "Use @(see gl) to reason about finitely bounded values."
  :long "It is often convenient to use as much automation as possible when
  performing proofs.  @(csee gl) provides the ability to automatically reason
  about finite values, such as 32-bit integers.  As examples, this can be quite
  useful when reasoning about cryptography algorithms or verifying hardware.")

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

<p>These conventions allow build systems like @(see build::cert.pl) to
automatically distinguish between what should be certified and what should
not.</p>

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
  :parents (best-practices packages)
  :short "How to set up new package and portcullis files."

  :long "<h4>Recommendations</h4>

<p>Here is a basic recipe to follow for creating new directories that make use
of packages:</p>

<dl>

<dt>@('foo/package.lsp') &mdash; main package definitions</dt>

<dd>
@({
    ;; load other packages needed to define our new packages...
    ;; note that we only include portcullis files, that define
    ;; the packages, not the libraries which those files support
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
     ;; We need an \"in-package\" line to make this a valid book, but
     ;; which package doesn't matter since the rest of the book is empty.
     (in-package \"FOO\")
})
</dd>

<dt>@('foo/portcullis.acl2') &mdash; certification instructions for the portcullis book</dt>

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
<li>It also helps @(see build::cert.pl) know it is not a certifiable book.</li>
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
first, if one exists, is nice for users who have their own macros.</p>

<p>It can also be good to pre-load packages like @('std') when your session
starts.  See @('books/std/std-customization.lsp') for an @(see
acl2-customization) file that does this.</p>")


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

<p>Using the above names may make your book hard to include for people
who (perhaps via macros) are already using these names or who may want to use
them.</p>

<h4>Weak Recommendations</h4>

<ol>

<li>For unconditional, equality-based rules, we base the rule name on a reading
of the left-hand side, using @('of') as a separator.  This is meant to boost
readability when the function names involved have their own hyphens.  Examples:

 @({
    (defthm append-of-cons
      (equal (append (cons a x) y)
             (cons a (append x y))))

    (defthm true-listp-of-append
      (equal (true-listp (append x y))
             (true-listp y)))
 })
</li>

<li>For rules describing the return-type of a function, we use a similar naming
convention, using @('of') as a separator.  Example:

 @({
    (defthm consp-of-cons
      (consp (cons x y)))
 })
</li>

<li>For rules with one simple hypothesis, we add @('-when-hyp') to the
name.  Examples:
 @({
    (defthm member-when-atom         ;; lhs is (member a x)
      (implies (atom x)
               (not (member a x))))

    (defthm logbitp-of-0-when-bitp
      (implies (bitp b)
               (equal (logbitp 0 b)
                      (equal b 1))))
 })
</li>

<li>For rules about other equivalence relations, we add @('-under-equiv') to the
name.  Examples:
 @({
    (defthm append-under-iff         ;; lhs is (append x y)
      (iff (append x y)
           (or (consp x)
               y)))
    (defthm union-equal-under-set-equiv  ;; lhs is (union-equal a b)
      (set-equiv (union-equal a b)
                 (append a b)))

 })
</li>

<li>For rules that specify the upper limit of a function's numerical return
value, we often add @('-limit'). </li>

<li>For rules that specify both the lower and upper limit of a function's
numerical return value, we often add @('-bounds').</li>

</ol>

<p>Obviously you can take this too far.  For complex theorems, these
recommendations would lead to names that are far too long.  Think of them as a
starting point, not a mandate.</p>

<h4>Rationale</h4>

<p>Following these conventions can help lead to more consistently named rules
whose effect may be more easy to guess.</p>")

(defxdoc where-do-i-place-my-book
  :parents (best-practices projects books)
  :short "How to decide where in the books directory structure to place your book"
  :long "<p>Here is our loose view of the books organization:</p>

  <ol>
    <li>project-specific stuff</li>
    <li>useful libraries not yet vetted by the 'std' maintainers</li>
    <li>libraries 'approved' for the standard approach</li>
  </ol>

  <p>Books in category (1) easily belong in @('books/projects').</p>

  <p>Books in category (2) can go in the top-level @('books') directory or in
  projects.  There's so much stuff in the top-level directory, that we suggest
  @('books/projects') -- especially for people that are new to the ACL2
  community.</p>

  <p>Once general-use books are vetted by the ACL2 book Czars, they go in the
  @('std') directory.  Some of the criteria the book czars use to decide
  whether a book should be in @('std') follow below:</p>

  <ul>
    <li>Design is consistent with other @('std') books</li>
    <li>Has some general purpose use -- e.g., data structure books are very
    much something that you would expect to see in a general framework for a
    language like Java</li>
    <li>Has good documentation that explains how to use it</li>
  </ul>")

(defxdoc remove-whitespace
  :short "How to find and remove whitespace from .lisp files"
  :long "<p>Some of us are of the opinion that it's good hygiene to not allow
  trailing whitespaces.  To see trailing-whitespaces in Emacs enable:</p>

  @({(setq-default show-trailing-whitespace t)})

  <p>To remove trailing-whitespaces from a file you have open in emacs do:</p>

  @({M-x delete-trailing-whitespace})

  <p>To find trailing whitespaces in @('.lisp') files within your current
  directory, in your shell do:</p>

  @({find . -name '*.lisp' -exec egrep -l \" +$\" {} \;})")
