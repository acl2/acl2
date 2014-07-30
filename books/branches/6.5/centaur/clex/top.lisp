; Centaur Lexer Library
; Copyright (C) 2013 Centaur Technology
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

(in-package "CLEX")
(include-book "sin")
(include-book "matchers")
(include-book "std/strings/decimal" :dir :system)

(defsection clex
  :parents (acl2::interfacing-tools)
  :short "<b>C</b>entaur <b>Lex</b>er Library."

  :long "<p>This is a rudimentary library for creating lexers for character
data in ACL2.  It is an outgrowth and revision of lexer support routines that
were originally developed as part of the @(see vl::vl) library.</p>

<p>These routines are based on ACL2 @(see acl2::characters).  They are,
accordingly, suitable for processing text in ASCII or ISO-8859-1 or some other
8-bit character set, but <b>not Unicode</b> or other wide character sets.  It
would generally be a bad idea to use CLEX to write a lexer for a language like
Java or XML that needs Unicode support.</p>

<p>Many lexical analyzers like <a href='http://flex.sourceforge.net/'>Flex</a>
are rather sophisticated and allow you to declare the syntax of your tokens at
a relatively high level (e.g., via regular expressions); this description is
then compiled into a full-blown scanner function.</p>

<p>In comparison, CLEX is quite primitive.  Really, it is nothing more than
some functions that tend to be useful when writing lexers \"by hand.\" Even so,
this is not so bad.  Here are the things that CLEX provides:</p>

<ul>

<li>A <see topic='@(url sin)'>stream input</see> mechanism that is somewhat
efficient and conveniently tracks your position (for good error messages).</li>

<li>A @(see defcharset) macro for describing basic character types (e.g.,
whitespace, digits, letters, etc).</li>

<li>Basic @(see matching-functions) for tokenizing input.</li>

<li>Macros like @(see def-sin-progress) for proving that your lexers make
progress.</li>

<li>Lemmas about matching functions for proving basic \"reconstruction\"
theorems.</li>

</ul>


<h3>Getting Started</h3>

<p>Most users should simply load the top book in the library as follows:</p>

@({
 (include-book \"centaur/clex/top\" :dir :system)
})

<p>Besides this documentation, you may find it useful to see the @(see
example-lexer), located in @('centaur/clex/example.lisp'); note that this
example is not included in @('clex/top').</p>")


(defsection def-sin-progress
  :parents (clex)
  :short "Prove basic progress properties of a lexing function."
  :long "<p>The macro @('def-sin-progress') can be used to prove basic progress
properties about a function that updates @(see sin).</p>

<p>Typically for any function @('(f ... sin) --> (mv ... sin)') you will want
to prove:</p>

@({
     (defthm f-progress-weak
       (<= (len (strin-left (mv-nth ... (f ... sin))))
           (len (strin-left sin)))
       :rule-classes ((:rewrite) (:linear)))

     (defthm f-progress-strong
       (implies hyp
                (< (len (strin-left (mv-nth ... (f ... sin))))
                   (len (strin-left sin))))
       :rule-classes ((:rewrite) (:linear)))
})

<p>Where @('hyp') is some suitable hypothesis involving the inputs and/or other
values returned by the function, e.g., frequently, that F produced a token
instead of failing.</p>

<p>@(call def-sin-progress) just tries to prove these theorems automatically
about the function named @('name'), with the given @('hyp').  See the @(see
example-lexer) for some examples of using it.</p>"
  :autodoc nil

  (defun generate-awful-names-for-return-values (x n)
    ;; X is like a :stobjs-out list, e.g., (nil nil sin)
    ;; Replace all NILs with generated variable names.
    (declare (xargs :mode :program))
    (cond ((atom x)
           nil)
          ((eq (car x) nil)
           (cons (intern-in-package-of-symbol (cat "VAL" (natstr n))
                                              'foo)
                 (generate-awful-names-for-return-values (cdr x) (+ 1 n))))
          (t
           (cons (car x)
                 (generate-awful-names-for-return-values (cdr x) n)))))

  (defun def-sin-progress-fn (name hyp world)
    (declare (xargs :mode :program))
    (b* ((__function__ 'def-sin-progress)
         (name-s  (symbol-name name))
         (formals (std::look-up-formals name world))
         (returns (std::look-up-return-vals name world))
         ((unless (member 'sin formals))
          (raise "~x0 does not take ~x1 as an argument." name 'sin))
         ((unless (member 'sin returns))
          (raise "~x0 does not return ~x1." name 'sin))
         ;; Try to pick good return-value names.  This works if the user
         ;; introduced their function with DEFINE and named their return
         ;; values.  Otherwise, just generate crappy names.
         (info (cdr (assoc name (std::get-define-guts-alist world))))
         (return-names
          (if info
              (std::returnspeclist->names (std::defguts->returnspecs info))
            (generate-awful-names-for-return-values returns 0)))
         (return-names
          ;; Rename the output SIN to NEW-SIN, so we can target it.
          (update-nth (position 'sin returns) 'new-sin return-names)))
      `(encapsulate ()
         (local (in-theory (enable ,name)))
         (defthm ,(intern-in-package-of-symbol (cat name-s "-PROGRESS-WEAK")
                                               name)
           (mv-let ,return-names
             (,name . ,formals)
             (declare (ignorable . ,return-names))
             (<= (len (strin-left new-sin))
                 (len (strin-left sin))))
           :rule-classes ((:rewrite) (:linear)))
         (defthm ,(intern-in-package-of-symbol (cat name-s "-PROGRESS-STRONG")
                                               name)
           (mv-let ,return-names
             (,name . ,formals)
             (declare (ignorable . ,return-names))
             (implies ,hyp
                      (< (len (strin-left new-sin))
                         (len (strin-left sin)))))
           :rule-classes ((:rewrite) (:linear))))))

  (defmacro def-sin-progress (name &key (hyp 't))
    `(make-event
      (b* ((world (w state))
           (event (def-sin-progress-fn ',name ',hyp world)))
        (acl2::value event)))))


