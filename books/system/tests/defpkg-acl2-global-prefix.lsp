; This file was produced by Claude and passed along by Eric Smith.  It
; illustrates a bug in ACL2 Version 8.7 fixed before ACL2 Version 8.8.  It is
; not a certifiable book, because of the defpkg forms.  To test it, evaluate
; (ld "defpkg-acl2-global-prefix.lsp").  Anyone is welcome to use run-script to
; create a book for this test.

; Finding 66: chk-acceptable-defpkg checks the "ACL2_*1*_" package prefix but
; NOT "ACL2_GLOBAL_".
;
; THE TWO PREFIXES ARE CREATED BY THE SAME CODE.  acl2.lisp:1361-1363:
;
;    (defparameter *global-package-prefix* "ACL2_GLOBAL_")
;    (defparameter *1*-package-prefix*     "ACL2_*1*_")
;
; and maybe-make-three-packages (acl2-fns.lisp:1158-1168) creates
; ACL2_GLOBAL_<P> and ACL2_*1*_<P> side by side for every known package P.
;
; ONLY ONE OF THEM IS DEFENDED.  The name-legality cond in
; chk-acceptable-defpkg (other-events.lisp:1468-1522) has clauses for
; non-string (:1472), "" (:1477), lower case (:1496), "LISP" (:1501) and
; *1*-pkg-prefix* (:1507-1520) -- and nothing for *global-package-prefix*.
; The asymmetry is stark: the *1* prefix even got its own loop-side constant
; (*1*-pkg-prefix*, other-events.lisp:1404) with an "Implementation error"
; check keeping it in sync with the raw one.  There is no *global-pkg-prefix*.
;
; WHY IT IS UNSOUND.  global-symbol (acl2-fns.lisp:75-82) maps state global
; FOO::*C* to the symbol ACL2_GLOBAL_FOO::*C*, and raw f-put-global
; (axioms.lisp:15889) setfs that symbol's SYMBOL-VALUE.  That is the same cell
; add-trip's defconst case uses, via ifat-defparameter
; (interface-raw.lisp:6789, :6874-6879).  add-trip installs the UNTRANSLATED
; body as the raw definition, so a function whose body is that defconst reads
; it through symbol-value at run time while its definitional axiom carries the
; substituted literal.  Measured, with a fresh pair ACL2_GLOBAL_BAR / BAR:
;
;    (gg 3)                                    => 17
;    (getpropc 'gg 'unnormalized-body ...)     => '17
;    (f-put-global 'bar::*k* 42 state)
;    (gg 3)                                    => 42        <<< raw
;    (getpropc 'gg 'unnormalized-body ...)     => '17        <<< logic
;
; NO BYPASS IS NEEDED.  Unlike Finding 45, this needs no
; (set-ld-skip-proofsp 'include-book state): both defpkgs are ordinary,
; accepted events.  The ordering matters -- ACL2_GLOBAL_FOO must be introduced
; BEFORE FOO, since otherwise the raw package already exists and defpkg-raw1's
; *defpkg-virgins* test (axioms.lisp:12636-12645) refuses it.
;
; The end-to-end portcullis witness is in the report bundle; it certifies with
; five * Step lines and all four oracles clean.
;
; POLARITY: RED while present -- the first MUST-FAIL fails because the illegal
; name is accepted.  GREEN once the cond gets its *global-package-prefix*
; clause.

(in-package "ACL2")
(include-book "std/testing/must-fail" :dir :system)

; THE DEFECT: defpkg accepts a name in the reserved ACL2_GLOBAL_ space, with
; no flag of any kind set.
(must-fail (defpkg "ACL2_GLOBAL_N90A" nil))

; The same, with lower case in the suffix only, so the upper-case clause at
; :1496 is not what refuses it.
(must-fail (defpkg "ACL2_GLOBAL_N90B" '(car)))

; CONTROL 1: the *1* prefix IS refused, with no flag set.  This is the sibling
; check that exists, and the whole point of the finding is that these two
; lines behave differently.
(must-fail (defpkg "ACL2_*1*_N90C" nil))

; CONTROL 2: the other three name-legality clauses still fire, so this book
; measures the ACL2_GLOBAL_ gap and not a general collapse of the cond.
(must-fail (defpkg "" nil))
(must-fail (defpkg "lowern90" nil))
(must-fail (defpkg "LISP" nil))

; CONTROL 3: an ordinary package name must still be accepted, so the fix
; cannot be to reject more than the reserved prefix.  A name that merely
; CONTAINS the prefix away from position 0 is also legal and must stay so.
(defpkg "N90-OK" nil)
(defpkg "N90-ACL2_GLOBAL_X" nil)
