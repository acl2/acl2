#|

In order to learn about make-event, it may be useful to look at the files below
in the order shown, probably just those marked with + (or referred to in
comments in those files).  Typically, we add "-check" to indicate a variant
that uses :check-expansion t, and we add "-include" to suggest a book that
includes a previous book.

  acl2x-help.lisp
    Support for avoiding needless proofs when generating .acl2x files (see :DOC
    set-write-acl2x); demonstrated with acl2x-help-test.lisp
+ basic.lisp
    Simple examples; make-event-debug.  Suggestion: Look at the output.
+ basic-check.lisp
    Interesting experiment:
    (assign make-event-debug t)
    (include-book "basic-check") ; see checking of expansions
    :u
    (include-book "basic") ; no checking of expansions
  basic-pkg.lisp
  basic-pkg-check.lisp
+ double-cert-test-1.lisp, double-cert-test.lisp
    Certification that ultimately avoids need for trust tags; see
    :DOC set-write-acl2x.
+ read-from-file.lisp
    Create events by reading a file.  Includes remark explaining why we enable
    proofs during evaluation of the expansion result when :check-expansion is
    not nil.
+ proof-by-arith.lisp
    Search among different proof strategies.
+ defrule.lisp
    Expand macros before generating a rewrite rule
+ gen-defun.lisp
    Generate events and event names based on the current logical world.
  gen-defun-check.lisp
  local-elided.lisp
  local-elided-include.lisp
  local-requires-skip-check.lisp
  local-requires-skip-check-include.lisp
+ defconst-fast.lisp
+ defconst-fast-examples.lisp
+ macros.lisp
    Some tests that give a deeper understand of the interaction of make-event
    with macros, local, and redundancy.
+ macros-include.lisp
    Gives deeper understanding of the expansions stored, which are checked by
    reading a .cert file inside a make-event.
  macros-skip-proofs-include.lisp
  macros-skip-proofs.lisp
+ gen-defthm.lisp
    Generate theorems using state modification during expansion.
  gen-defthm-check.lisp
+ eval.lisp
    Useful macros must-succeed and must-fail.
+ eval-tests.lisp
    Tests illustrating the use of macros must-succeed and must-fail.
  eval-check.lisp
+ eval-check-tests.lisp
    Like eval-tests.lisp, but illustrates why state global 'ld-skip-proofsp is
    set to t at the start of expansion.
+ assert.lisp
    Assertions that can be put into a book.
+ assert-include.lisp
    Check that expansion blows away the make-event if :check-expansion is nil.
+ assert-check.lisp
    Check that expansion does NOT blow away the make-event if :check-expansion
    is t (using the two books just below).
  assert-check-include-1.lisp
  assert-check-include.lisp
+ test-case.lisp
    Variant of assert.
  test-case-check.lisp
  nested.lisp
  nested-check.lisp
+ embeddable-event-forms.lisp
    Simple constructors to make forms you can put in a book.
  portcullis-expansion.lisp
  portcullis-expansion-include.lisp
+ stobj-test.lisp
    Illustrates the use of stobjs during make-event expansion.
+ dotimes.lisp
    Defines a dotimes$ macro and provides an example.
+ logical-tangent.lisp
    Provides a wormhole-like capability, where you can experiment for awhile
    and then the built-in part of the state, including the logical world, will
    be reverted.
+ defrefine.lisp
    Provides a collection of macros to aid in reasoning about ACL2 functions
    via refinement.
+ inline-book.lisp
    Provides a couple rough replacements for include-book that do not require
    separate certification of the included book.
+ require-book.lisp
    Provides a way of specifying that a book should be included when using
    a book but is not needed for certification.

The rest of this file is metadata for the ACL2 system.

|#

((:FILES ; non-empty list of filenames, generated from Unix command "ls -1R"
"
.:
Makefile
Readme.lsp
assert-check-include-1.acl2
assert-check-include-1.lisp
assert-check-include.lisp
assert-check.lisp
assert-include.acl2
assert-include.lisp
assert.lisp
basic-check.lisp
basic-pkg-check.acl2
basic-pkg-check.lisp
basic-pkg.acl2
basic-pkg.lisp
basic.lisp
defconst-fast-examples.lisp
defconst-fast.lisp
defrefine.lisp
dotimes.lisp
double-cert-test-1.acl2
double-cert-test-1.lisp
double-cert-test.lisp
embeddable-event-forms.lisp
eval-check-tests.lisp
eval-check.lisp
eval-tests.lisp
eval.lisp
gen-defthm-check.lisp
gen-defthm.lisp
gen-defun-check.lisp
gen-defun.lisp
inline-book.lisp
local-requires-skip-check-include.lisp
local-requires-skip-check.lisp
logical-tangent.lisp
macros-include.lisp
macros-skip-proofs-include.acl2
macros-skip-proofs-include.lisp
macros-skip-proofs.acl2
macros-skip-proofs.lisp
macros.lisp
make-redundant.lisp
nested-check.lisp
nested.lisp
portcullis-expansion-include.acl2
portcullis-expansion-include.lisp
portcullis-expansion.acl2
portcullis-expansion.lisp
proof-by-arith.lisp
read-from-file-data-mod.lsp
read-from-file-data.lsp
read-from-file.lisp
require-book.lisp
stobj-test.lisp
test-case-check.lisp
test-case.lisp
")
 (:TITLE    "Examples illustrating the use of make-event")
 (:AUTHOR/S "M. Kaufmann" "J Moore" "David Rager" "Peter Dillinger")
 (:KEYWORDS ; non-empty list of keywords, case-insensitive
   "make-event" "assert!" "assert!!" "must-fail" "must-succeed" "must-eval-to"
   "must-eval-to-t" "test-case" "dotimes$" "logical-tangent" "inline-book"
   "program refinement")
 (:ABSTRACT "
The .lisp files in this directory illustrate a number of potential
uses of make-event.  In particular, eval.lisp defines some macros
that allow one to put tests into one's certifiable books; but there
are many other examples as well."))

