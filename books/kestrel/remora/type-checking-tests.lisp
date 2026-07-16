; Remora Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)
; Contributions by; Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "REMORA")

(include-book "parser-interface")
(include-book "type-checking")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Test that a standalone Remora expression
; parses and type-checks without error.
; The argument is a string of Remora source for a standalone expression.
; The macro expands to an assert-event that runs
; parse-top-exp-from-string followed by check-top-expr,
; and passes when the result is not an error.
; The type of the expression is printed to the comment window
; for manual inspection; the expected type is not checked.

(defmacro test-check-top-expr (code)
  `(assert-event
    (b* ((code ,code)
         (ast (parse-top-exp-from-string code))
         (tast (check-top-expr ast)))
      (and (not (reserrp tast))
           (not (cw "~x0~%" (type+expr->type tast)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Test that a standalone Remora expression
; parses but does not type-check.
; The argument is a string of Remora source for a standalone expression.
; The macro expands to an assert-event that runs
; parse-top-exp-from-string followed by check-top-expr,
; and passes when type checking returns an error.
; The error is printed to the comment window for manual inspection.

(defmacro test-check-top-expr-fail (code)
  `(assert-event
    (b* ((code ,code)
         (ast (parse-top-exp-from-string code))
         (tast (check-top-expr ast)))
      (and (not (cw "~x0~%" tast))
           (reserrp tast)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The variable $d escapes.
(test-check-top-expr-fail
 "(unbox ($d v (box (3) [1 2 3] (Sigma ($e) (A Int $e)))) v)")

; The inner variable $d escapes, and the outer variable $d does not interfere.
(test-check-top-expr-fail
 "(let ((i-fun (f ($d))
        (unbox ($d v (box (3) [1 2 3] (Sigma ($e) (A Int $e)))) v)))
  (@length (Int) (5 []) (i-app f 5)))")

; As above but without the consumer:
; the escaped witness $d would be captured by the i-fun's $d,
; making the expression appear to have type [Int 5]
; while evaluating to a vector of length 3.
(test-check-top-expr-fail
 "(let ((i-fun (f ($d))
        (unbox ($d v (box (3) [1 2 3] (Sigma ($e) (A Int $e)))) v)))
  (i-app f 5))")

; As above with the length instantiation matching the run-time value:
; also rejected, since the escape is the problem,
; not which length is demanded.
(test-check-top-expr-fail
 "(let ((i-fun (f ($d))
        (unbox ($d v (box (3) [1 2 3] (Sigma ($e) (A Int $e)))) v)))
  (@length (Int) (3 []) (i-app f 5)))")

; The witness $w escapes; the unrelated outer variable $z does not mask it.
(test-check-top-expr-fail
 "(let ((i-fun (f ($z))
        (unbox ($w v (box (3) [1 2 3] (Sigma ($e) (A Int $e)))) v)))
  (i-app f 5))")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Nothing escapes when the body's type does not mention the witness,
; even when the witness shadows an outer ispace variable.
(test-check-top-expr
 "(let ((i-fun (f ($d))
        (unbox ($d v (box (3) [1 2 3] (Sigma ($e) (A Int $e)))) 0)))
  (i-app f 5))")

; The idiomatic use of a witness:
; consume the payload inside the unbox,
; instantiating with the witness itself; the body's type is closed.
(test-check-top-expr
 "(unbox ($d v (box (3) [1 2 3] (Sigma ($e) (A Int $e))))
   (@length (Int) ($d []) v))")

; The witness name appears in the body's type only under a binder
; (the Pi introduced by the i-fn), so it does not escape:
; the escape check must be aware of binders within types.
(test-check-top-expr
 "(unbox ($d v (box (3) [1 2 3] (Sigma ($e) (A Int $e))))
   (i-fn ($d) 7))")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The tests below are commented out because they currently fail:
; the type checker accepts these expressions,
; but each one gets stuck (a dynamic shape error) when evaluated,
; so each should be rejected.
; They exploit shadowing of ispace variables rather than escaping witnesses:
; a type recorded in the environment mentions an ispace variable
; that a later homonymous binder silently reinterprets (captures).
; The escape check in the unbox case of check-expr cannot see them,
; because the escaping type is closed in each case;
; rejecting them requires binder freshness,
; e.g. uniquification of bound variables before type checking
; (see unique-names.lisp)
; or freshness checks at every ispace binder.
; If freshness is enforced, these should become passing tests.

; The type of u refers to the outer $d
; but is reinterpreted at the witness $d inside the unbox:
; length is instantiated at the witness (3 at run time)
; and applied to u (of length 5 at run time).
; (test-check-top-expr-fail
;  "(let ((i-fun (f ($d))
;         (fn ((u [Int $d]))
;           (unbox ($d v (box (3) [1 2 3] (Sigma ($e) (A Int $e))))
;             (@length (Int) ($d []) u)))))
;   ((i-app f 5) [1 2 3 4 5]))")

; The Sigma body type (A Int $d) mentions the outer $d free;
; renaming the Sigma variable $e to the witness $d
; rebinds (captures) that occurrence,
; so the type of v is misread at the witness.
; (test-check-top-expr-fail
;  "(let ((i-fun (f ($d))
;         (fn ((u [Int $d]))
;           (unbox ($d v (box (3) u (Sigma ($e) (A Int $d))))
;             (@length (Int) ($d []) v)))))
;   ((i-app f 5) [1 2 3 4 5]))")

; The same reinterpretation with no unbox involved:
; the inner i-fn's $d shadows the outer $d in the type of u.
; (test-check-top-expr-fail
;  "(let ((i-fun (f ($d))
;         (fn ((u [Int $d]))
;           (i-fn ($d) (@length (Int) ($d []) u)))))
;   (i-app ((i-app f 5) [1 2 3 4 5]) 3))")
