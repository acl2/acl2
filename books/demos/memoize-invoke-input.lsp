; Copyright (C) 2020, ForrestHunt, Inc.
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; This book includes a few simple tests that illustrate the :invoke keyword of
; memoize.

; You can run this at the terminal with:
; (ld "memoize-invoke-input.lsp" :ld-error-action :continue :ld-pre-eval-print t)

; Redirect trace output to where the rest of the output is going:
(f-put-global 'trace-co (@ standard-co) state)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; A simple test
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defn f1 (x) (list (car (cons x x))))
(defn g1 (x) (list x))
; The following memoize event fails.
(memoize 'f1 :invoke 'g1)
; The output from the failure above suggests proving the following.
(DEFTHM |F1-is-G1| (EQUAL (F1 X) (G1 X)) :RULE-CLASSES NIL)
; This now succeeds.
(memoize 'f1 :invoke 'g1)
(trace$ g1)
(f1 3)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; A test using a recursively defined function,
; doing directly with memoize what can be
; accomplished using use-io-pairs.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Define the Finonacci function.
(defun fib (n)
  (declare (xargs :guard (natp n)))
  (if (zp n)
      0 (if (eql n 1)
            1
          (+ (fib (- n 1)) (fib (- n 2))))))
(with-output
  :off summary ; With progn, avoid comp return value differences per Lisp.
  (progn
    (comp 'fib) ; for major speed-up in other than CCL or SBCL
    (value-triple t)))
; Provide an immediate result for a specific value.
(defun fib2 (n)
  (declare (xargs :guard (natp n)))
  (if (= n 40) 102334155 (fib n)))
; The following fails because the necessary equality must be proved first.
(memoize 'fib :invoke 'fib2)
; Prove the necessary equality.
(DEFTHM |FIB-is-FIB2| (EQUAL (FIB N) (FIB2 N)) :RULE-CLASSES NIL)
; Succeeds now:
(memoize 'fib :invoke 'fib2)
(fib 40) ; fast
(fib 41) ; slow

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; A test involving guard implication
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun f2 (x)
  (declare (xargs :guard (consp x)))
  (car x))
; Fails with guard violation:
(f2 3)
(defun g2 (x)
  (declare (xargs :guard (listp x)))
  (car x))
(DEFTHM |F-is-G| (EQUAL (F2 X) (G2 X)) :RULE-CLASSES NIL)
(memoize 'f2 :invoke 'g2)
(verify-guard-implication f2 g2)
(memoize 'f2 :invoke 'g2)
(trace$ g2)
; Still fails with guard violation:
(f2 3)
(f2 '(a b c))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; The commutative argument is tolerated.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defn f3 (x y) (declare (type rational x y)) (+ x y))
(defn g3 (x y) (declare (type rational x y)) (+ 1 -1 x y))
(DEFTHM |F3-is-G3| (EQUAL (F3 X Y) (G3 X Y)) :RULE-CLASSES NIL)
(with-output :off :all
; This use of with-output avoids the need to update memoize-invoke-log.txt
; whenever a change to the absolute-event-number causes a different
; value-triple to be generated.
  (memoize 'f3 :invoke 'g3 :commutative t))
(trace$ g3)
(f3 3 4)
