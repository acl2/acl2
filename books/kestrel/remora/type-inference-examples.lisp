; Remora Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "REMORA")

(include-book "parser-interface")
(include-book "type-checker")
(include-book "evaluation")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The function 'vec-length' specializes the primitive 'length' to vectors:
; it is parameterized only on a dimension, without a subsequent shape.
; The following examples bind 'vec-length' and then do something with it.

; Long form of applying 'vec-length' to an integer vector (no type inference).
(defconst *long-int*
  "(let ((fun (@vec-length (&t) ($d) (vec (A &t (dims $d))) : Int)
              ((i-app (i-app (t-app length &t) $d) (++)) vec)))
     ((i-app (t-app vec-length Int) 3) (array [3] 1 2 3)))")

; Long form of applying 'vec-length' to a boolean vector (no type inference).
(defconst *long-bool*
  "(let ((fun (@vec-length (&t) ($d) (vec (A &t (dims $d))) : Int)
              ((i-app (i-app (t-app length &t) $d) (++)) vec)))
     ((i-app (t-app vec-length Bool) 2) (array [2] #t #f)))")

; Short form of applying 'vec-length' to an integer vector (type inference).
(defconst *short-int*
  "(let ((fun (@vec-length (&t) ($d) (vec (A &t (dims $d))) : Int)
              ((i-app (i-app (t-app length &t) $d) (++)) vec)))
     (vec-length (array [3] 1 2 3)))")

; Short form of applying 'vec-length' to a boolean vector (type inference).
(defconst *short-bool*
  "(let ((fun (@vec-length (&t) ($d) (vec (A &t (dims $d))) : Int)
              ((i-app (i-app (t-app length &t) $d) (++)) vec)))
     (vec-length (array [2] #t #f)))")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The Remora compiler accepts the first two but rejects the other two.

#|

remora interpret -e '(let ((fun (@vec-length (&t) ($d) (vec (A &t (dims $d))) : Int)
              ((i-app (i-app (t-app length &t) $d) (++)) vec)))
     ((i-app (t-app vec-length Int) 3) [1 2 3]))'

remora interpret -e '(let ((fun (@vec-length (&t) ($d) (vec (A &t (dims $d))) : Int)
              ((i-app (i-app (t-app length &t) $d) (++)) vec)))
     ((i-app (t-app vec-length Bool) 2) [#t #f]))'

remora interpret -e '(let ((fun (@vec-length (&t) ($d) (vec (A &t (dims $d))) : Int)
              ((i-app (i-app (t-app length &t) $d) (++)) vec)))
     (vec-length [1 2 3]))'

remora interpret -e '(let ((fun (@vec-length (&t) ($d) (vec (A &t (dims $d))) : Int)
              ((i-app (i-app (t-app length &t) $d) (++)) vec)))
     (vec-length [#t #f]))'

|#

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Get the ASTs for the examples.

(defconst *long-int-ast*
  (parse-top-exp-from-string *long-int*))

(defconst *long-bool-ast*
  (parse-top-exp-from-string *long-bool*))

(defconst *short-int-ast*
  (parse-top-exp-from-string *short-int*))

(defconst *short-bool-ast*
  (parse-top-exp-from-string *short-bool*))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Type-check the examples.

(defconst *long-int-type+expr*
  (check-top-expr *long-int-ast*))

(defconst *long-bool-type+expr*
  (check-top-expr *long-bool-ast*))

(defconst *short-int-type+expr*
  (check-top-expr *short-int-ast*))

(defconst *short-bool-type+expr*
  (check-top-expr *short-bool-ast*))

(assert-event (and (not (reserrp *long-int-type+expr*))
                   (not (reserrp *long-bool-type+expr*))
                   (not (reserrp *short-bool-type+expr*))
                   (not (reserrp *short-bool-type+expr*))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Evaluate the examples.

(defconst *long-int-result*
  (eval-top-expr (type+expr->expr *long-int-type+expr*) 1000000))

(defconst *long-bool-result*
  (eval-top-expr (type+expr->expr *long-bool-type+expr*) 1000000))

(defconst *short-int-result*
  (eval-top-expr (type+expr->expr *short-int-type+expr*) 1000000))

(defconst *short-bool-result*
  (eval-top-expr (type+expr->expr *short-bool-type+expr*) 1000000))

(assert-event (equal *long-int-result*
                     (expr-value-base (base-value-int (int-value 3)))))

(assert-event (equal *long-bool-result*
                     (expr-value-base (base-value-int (int-value 2)))))

(assert-event (equal *short-int-result*
                     (expr-value-base (base-value-int (int-value 3)))))

(assert-event (equal *short-bool-result*
                     (expr-value-base (base-value-int (int-value 2)))))
