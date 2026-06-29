; Copyright (C) 2026, ForrestHunt, Inc.
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; For output, see the file encap-defs-ht-log.txt in this directory.

(in-package "ACL2")

(set-raw-mode-on!)
(setq *debug-on* t)
(set-raw-mode nil)
(u) ; undo ttag

(set-debugger-enable nil) ; avoid Lisp-dependent backtraces

; Simple test that local and redundancy work as expected with hash tables:
(encapsulate
  ()
  (local (defun foo (x)
           (declare (xargs :mode :program))
           (cons x x)))
  ;; redundant:
  (defun foo (x)
    (declare (xargs :mode :program))
    (cons x x)))

(u)

; As just above, but nested inside an encapsulate:
(encapsulate
  ()
  (encapsulate
    ()
    (local (defun foo (x)
             (declare (xargs :mode :program))
             (cons x x)))
    ;; redundant:
    (defun foo (x)
      (declare (xargs :mode :program))
      (cons x x))))

(u)

; Lots of nesting of encapsulates:
(encapsulate ()         ; [a]
  (encapsulate ()       ; [b]
    (encapsulate ()     ; [c]
      (defun g (x)
        (declare (xargs :mode :program))
        (cons x x)))))

(u)

(encapsulate
  ()
  (local (defun f (x)
           (declare (xargs :guard t))
           ;; (prog2$ (cw "@@@HI@@@~%") (cons x x))
           (with-debug (cons x x)
                       "@@@HI@@@~%")
           ))
  (local (memoize 'f))
; Redundant, but only saved *1* function in hash-table, since f is memoized:
  (defun f (x)
    (declare (xargs :guard t))
    ;; (prog2$ (cw "@@@HI@@@~%") (cons x x))
    (with-debug (cons x x)
                "@@@HI@@@~%")
    ))

; Printing:
(f 3)

; Should still print (ACL2 8.7 bug is illustrated if we use cw instead above),
; since memoization of f is local:
(f 3)

(u)

(encapsulate
  ()
  (local (defun f (x)
           (declare (xargs :guard t))
           (with-debug (cons x x) "@@@HI@@@~%")))
; Redundant; saved both f and *1*f into hash table, since f is not yet
; memoized:
  (defun f (x)
    (declare (xargs :guard t))
    (with-debug (cons x x) "@@@HI@@@~%"))
  (memoize 'f))

(f 3) ; printing
(f 3) ; no printing (due to memoization)

(u)

; Inlined function, related to a preceding test:
#|
; This is a fine test, but the output differs in SBCL from other Lisps because
; source code is necessary for support of inlining.  See the #+sbcl code in
; install-defs-for-add-trip.  So we comment out this test.
(encapsulate
  ()
  (defun f$inline (x)
    (declare (xargs :guard t))
    (with-debug x "@@@ HI! @@@~%"))
  (local (memoize 'f$inline))
  (defun g (x)
    (f$inline x)))

(g 3) ; Printing
(g 3) ; Still printing, presumably as memoization is ignored for inline fn

(u)
|#

(encapsulate
  ()
  (local (defun foo (x)
           (declare (xargs :mode :logic))
           (car x)))
  ;; The following is redundant on the first pass, at which time it adds a fake
  ;; hash table entry for *1*foo since the symbol-class has changed:
  (defun foo (x)
    (declare (xargs :mode :program))
    (car x)))

; Raw Lisp error (in .cert.out file) rather than guard violation (in -log.txt
; file) due to use of :program mode *1*foo (ACL2 8.7 bug):
(foo 3)

(u)

(encapsulate
  ()
  (local (defun foo (x)
           (declare (xargs :mode :program))
           (car x)))
  (local (defun foo (x)
           (declare (xargs :mode :logic))
           (car x)))
  ;; Redundant on first pass with :logic mode def, so *1*foo is saved:
  (defun foo (x)
    (declare (xargs :mode :logic))
    (car x)))

(foo 3) ; guard violation, showing call of :logic version of *1*foo

(u)

(set-guard-checking :all)

(defun my-true-listp (x)
  (declare (xargs :guard t))
  (with-debug (true-listp x) "@~%"))

(encapsulate
  ()
  (local (defun foo (x)
           (declare (xargs :guard
                           ;; (prog2$ (cw "@") (true-listp x))
                           (my-true-listp x)))
           (if (consp x) (foo (cdr x)) x)))
  (defun foo (x)
    (declare (xargs :guard
                    ;; (prog2$ (cw "@") (true-listp x))
                    (my-true-listp x)
                    :verify-guards nil))
    (if (consp x) (foo (cdr x)) x)))

; Should get 5 atsigns, not 1, from :ideal version of *1*foo (as was exhibited
; by an ACL2 8.7 bug when using the cw version instead)
(foo '(1 2 3 4))

(set-guard-checking t)

(u)
(u)

(encapsulate ()
  (encapsulate ()
    (local (defun g (x)
             (declare (xargs :mode :program))
             x)))
  ;; This is a different definition for g than the local one above:
  (defun g (x)
    (declare (xargs :mode :program))
    (cons x x)))

(g 3) ; Should be (3 . 3), not 3

(u)

; Reclassifying value inside (outer) encapsulate; also involves non-trivial
; encapsulate.
(encapsulate
  ()
  (encapsulate
    ((h (x) t))
    (local (defun h (x) x))
    (defun foo (x) (declare (xargs :mode :program)) (car x)))
  (defun foo (x) (car x)))

(foo 3) ; guard violation

(u)

(set-ld-skip-proofsp t state)
(encapsulate
  ()
  (local (defun foo (x) (declare (xargs :guard t)) (car x)))
  (defun foo (x) (car x)))
(foo 3) ; guard violation, not error (ACL2 8.7 bug)
(set-ld-skip-proofsp nil state)

(u)

(encapsulate ()
; Debug output should confirm that hash tables are ignored during make-event
; expansion.
  (make-event (progn (defun foo (x) (declare (xargs :guard t :mode :program)) x)
                     (assert-event (equal (foo 3) 3))
                     (value-triple '(value-triple 17)))
              :check-expansion t)
  (defun foo (x) (declare (xargs :guard t :mode :program)) (cons x x)))

(u)

; The following should cause a raw Lisp error (ACL2 8.7 bug avoids raw Lisp
; error).  Of possible interest: Just before the error, we see
;   [IFATIB-2] Update hash table entry for ACL2_*1*_ACL2::FOO with fixed-val.
; and then
;   [IDFAT-9] Eval def for ACL2_*1*_ACL2::FOO.
; indicating that the reclassifying value placed in the hash table by the
; logic-mode defun of foo is not used on the program-mode defun, but instead,
; is made ready for the later logic-mode defun and then ignored as we evaluate
; the program-mode *1* definition.
(encapsulate
  ()
  (encapsulate
    ((h (x) t))
    (local (defun h (x) x))
    (defun foo (x) (declare (xargs :mode :program)) (car x)))
  (local (defun loc (x) x))
  (make-event (let ((val (if (function-symbolp 'loc (w state))
                             nil
; The following should cause an error because the *1*foo with symbol-class
; :program should be the one that is called.  In Version 8.7, and after that
; through 5/2026, the saved :ideal version of *1* foo was erroneously called.
                           (with-guard-checking nil
                                                (foo 3)))))
                (value (list 'value-triple val)))
              :check-expansion t)
  (defun foo (x) (car x)))

; (u) ; Nothing to undo after raw Lisp error above

; Simple test of defmacro:
(encapsulate
  ()
  (defmacro mac (x) `(expt 2 ,x)))

(u)

; Simple test for defmacro redundancy:
(encapsulate
  ()
  (local (defmacro mac (x) `(expt 2 ,x)))
  (defmacro mac (x) `(expt 2 ,x)))

(u)

; Second simple test for defmacro redundancy:
(encapsulate
  ()
  (encapsulate
    ()
    (local (defmacro mac (x) `(expt 2 ,x)))
    (defmacro mac (x) `(expt 2 ,x)))
  (defmacro mac (x) `(expt 2 ,x)))

(u)

; Here is the third simple test for defmacro redundancy.  Because of the
; initial local event, we put the macro-function for the (redundant) definition
; of mac from the encapsulate into the hash table.  But it is never used on the
; second pass, simply because that defmacro from the encapsulate is redundant.
; We could presumably avoid this needless setting of the hash table by checking
; that the existing local definition is inside the encapsulate, but that
; doesn't seem worth the trouble -- the cost of the hash-table addition is
; presumably negligible.

(local (defmacro mac (x) `(expt 2 ,x)))

(encapsulate
  ()
  (defun h (x) x)
  (defmacro mac (x) `(expt 2 ,x)))

(u)
(u)

; Simple test of defconst:
(encapsulate
  ()
  (defconst *c* (expt 2 3)))

(u)

; Simple test for defconst redundancy:
(encapsulate
  ()
  (local (defconst *c* (expt 2 3)))
  (defconst *c* (expt 2 3)))

(u)

; Second simple test for defconst redundancy:
(encapsulate
  ()
  (encapsulate
    ()
    (local (defconst *c* (expt 2 3)))
    (defconst *c* (expt 2 3)))
  (defconst *c* (expt 2 3)))

; Third simple test for defconst redundancy; see discussion of "the third
; simple test for defmacro redundancy" above, as this situation is similar.

(local (defconst *c* (expt 2 3)))

(encapsulate
  ()
  (defun h (x) x)
  (defconst *c* (expt 2 3)))

(u)
(u)

; The following gets the symbol-functions for foo and *1* foo from sub, then
; installs those into hash tables when processing the defun below on pass 1 of
; the encapsulate, and finally retrieves those in pass 2 of the encapsulate.
(encapsulate
  ()
  (local (include-book "encap-defs-ht-sub"))
  (defun foo (x) (cons x x)))

(u)

; The following example occurs in the comment about "Storing
; *hcomp-fake-value*" in the defun for
; update-hcomp-fn-ht-redundant-in-encapsulate.  See that comment for an
; explanation.
(encapsulate
  ()
  (local (defun g (x) x))
  (local (defun foo (x)
           (declare (xargs :mode :logic))
           (car x)))
  (defun foo (x)
    (declare (xargs :mode :program))
    (car x))
  (make-event (prog2$ (or (function-symbolp 'g (w state))
                          (foo 3))
                      (value '(defun h (x) x)))
	      :check-expansion t)
  (defun foo (x)
    (declare (xargs :mode :logic))
    (car x)))
