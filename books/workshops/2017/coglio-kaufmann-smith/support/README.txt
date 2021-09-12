NOTE: As discussed in ../README, support for the current version of
the simplify tool (which supersedes simplify-defun) may be found in
community books directory books/kestrel/apt/.

Supporting file for Section 2.1:

  example-producer-consumer.lisp

Supporting file for Section 2.2:

  example-integers.lisp

The remaining files support the definition of simplify-defun.  To play
with simplify-defun, evaluate the forms in simplify-defun-tests.lisp.

Update, September 2021.  Before now, community book
kestrel/utilities/directed-untranslate.lisp supported the present
directory's version of simplify-defun.  But with this update, we have
copied that version of directed-untranslate.lisp to the present
directory and make simplify-defun.lisp depend on it, which allows
future changes to kestrel/utilities/directed-untranslate.lisp without
affecting the present directory.  Because directed-untranslate.lisp
includes make-executable.lisp, that was copied here as well.
