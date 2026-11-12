; This book, modified only as noted below by Matt Kaufmann, was produced by
; Claude and passed along by Eric Smith.  It illustrates a bug fixed before
; ACL2 Version 8.8.

; S-36 (consequence for ordinary recursive functions; not a proof of nil): the double substitution adds a false measure conjunct, so
; the terminating G is rejected while G2 (outer LET variable named Z) is admitted. Run with :ld-error-action :continue.
;
; G294 (other: a valid definition is rejected; same root as S-36): for an
; ORDINARY recursive function (no :loop$-recursion), termination-machine-rec
; (induct.lisp) collects the loop$ scion calls in the actuals of a LET with
; (all-loop$-scion-quote-lambdas-lst (fargs body) alist), which already applies
; the enclosing LET bindings, and then explores each of them with the same
; alist again, so the recursive calls in the loop$ target are instantiated
; twice.  The real calls are also collected (correctly) by all-calls-lst, so the
; extra, doubly instantiated calls only ADD measure conjectures: no unsoundness,
; but a terminating function can be rejected.
;
; Below, the only recursive call is (g (cdr (cdr x))) with x bound by the outer
; LET to (cons 'a x), i.e. (g (cdr x)): G terminates.  The measure conjecture
; nevertheless contains the false conjunct
;   (O< (ACL2-COUNT (CDDR (LIST* 'A 'A X))) (ACL2-COUNT X))
; and the DEFUN fails.  G2, identical except that the outer LET variable is
; named Z (so a second substitution changes nothing), is admitted.
;
; Master dc0f042c42 SBCL and CCL, and 21aaad6 (acl2-sbcl): G rejected, G2
; admitted.  S-36's suggested fix (pass nil instead of alist at the remaining
; call sites of termination-machine-rec) removes the spurious conjunct.
; (With the default ruler-extenders the IF-test site is not reached, because IF
; is a ruler-extender; the LET-actuals site is.)
(in-package "ACL2")

(defun g (x)
  (if (consp x)
      (let ((x (cons 'a x)))
        (let ((y (loop$ for e in (list (g (cdr (cdr x)))) always (natp e))))
          (if y 1 2)))
    0))

; control
(defun g2 (x)
  (if (consp x)
      (let ((z (cons 'a x)))
        (let ((y (loop$ for e in (list (g2 (cdr (cdr z)))) always (natp e))))
          (if y 1 2)))
    0))
