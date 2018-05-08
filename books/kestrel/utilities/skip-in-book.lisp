; Copyright (C) 2018, Regents of the University of Texas
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

(in-package "ACL2")

(include-book "xdoc/top" :dir :system)

(defxdoc skip-in-book
  :parents (kestrel-utilities)
  :short "Skip a form when executing @(tsee certify-book) or @(tsee
 include-book)"
  :long "<p>The utility @('skip-in-book') takes a single argument, which is a
 form to be evaluated except during a call of @(tsee certify-book) or @(tsee
 include-book).  Thus, by placing an expression @('(skip-in-book <form>)') in a
 book, say @('foo.lisp'), you are arranging that evaluation of @('<form>') is
 skipped when certifying or including @('foo.lisp').  However, @('<form>') will
 be evaluated if you submit @('(skip-in-book <form>)') to the top-level loop,
 for example by evaluating @('(ld \"foo.lisp\")').</p>

 <p>(Technically, the criterion for skipping the form is that either some book
 is being certified or @('(ld-skip-proofsp state)') is @(''include-book').  The
 latter holds when including a book, whether certified or not.)</p>

 <p>To use this utility, you must both include the book in which it is defined
 and then <i>install</i> it, as follows.</p>

 @({
 (include-book \"kestrel/utilities/skip-in-book\" :dir :system)
 (install-skip-in-book)
 })

 <p>Let us consider an example in which the contents of the book @('foo.lisp')
 are as follows.</p>

 @({
 (in-package \"ACL2\")

 (include-book \"kestrel/utilities/skip-in-book\" :dir :system)
 (install-skip-in-book)

 (defun good-fn (x)
   (cons x x))

 (skip-in-book
  (defun bad-fn (x)
    (cons x x)))

 (skip-in-book
  (set-guard-checking nil))
 })

 <p>When you certify or include this book, the last two forms will be skipped,
 and thus @('bad-fn') will not be defined and guard-checking will be unchanged.
 But when you execute @('(ld \"foo.lisp\")'), you will be defining @('bad-fn')
 and also you will see that guard-checking has transitioned to @('nil').</p>")

(defpointer install-skip-in-book skip-in-book)

(defmacro install-skip-in-book ()
  '(make-event
    (if (or (f-get-global 'certify-book-info state)
            (eq (ld-skip-proofsp state) 'include-book))
        '(defmacro skip-in-book (form)
           (declare (ignore form))
           '(value-triple :skipped))
      '(defmacro skip-in-book (form)
         form))))
