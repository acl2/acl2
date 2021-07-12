; APT (Automated Program Transformations) Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/apt/tailrec" :dir :system)

(include-book "std/testing/assert-equal" :dir :system)
(include-book "std/testing/must-be-redundant" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The factorial function is a typical example.
; Its mathematical definition is recursive but not tail-recursive.
; TAILREC turns it into a tail-recursive version without any help from the user
; (i.e. no additional inputs other than the name of the target function).

; The default :MONOID variant of TAILREC is adequate for this function:
; the binary operation is *, with identity 1.
; Note that TAILREC automatically infers ACL2-NUMBERP
; as the domain of the binary operation (i.e. * here);
; this is used as the guard of the accumulator argument R.
; Running TAILREC with :PRINT :INFO shows these and other details.
; All the applicability conditions are proved automatically.

; If instead of using TAILREC we wrote directly the tail-recursive version,
; proving the correctness theorem asserting
; (EQUAL (FACTORIAL N) (FACTORIAL{1} N 1))
; would require first to prove the lemma asserting
; (EQUAL (FACTORIAL{1} N R) (* R (FACTORIAL N))),
; from which the correctness theorem then follows.
; Compare writing all of this
; (the tail-recursive function, the lemma, the theorem)
; with just the short line to call TAILREC.

(defun factorial (n)
  (declare (xargs :guard (natp n)))
  (if (zp n)
      1
    (* n (factorial (1- n)))))

(apt::tailrec factorial)

(must-be-redundant
 (defun factorial{1} (n r)
   (declare (xargs :guard (and (natp n) (acl2-numberp r))
                   :measure (acl2-count n)))
   (if (zp n)
       r
     (factorial{1} (+ -1 n) (* r n)))))

(must-be-redundant
 (defthmd factorial-to-factorial{1}
   (equal (factorial n)
          (factorial{1} n 1))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Triangular numbers have the form 1 + 2 + 3 + ... + n:
; each can be visualized as a right triangle whose catheti have length n.
; They can be recursively defined in the same way as factorial,
; but with + instead of *, and with 0 instead of 1 as identity.

; Unsurprisingly, TAILREC generates a tail-recursive version
; in the same way as done for factorial.
; Here we specify a name for the accumulator argument,
; just to showcase this feature
; (which is not necessary for this example to work).

(defun triangular (n)
  (declare (xargs :guard (natp n)))
  (if (zp n)
      0
    (+ n (triangular (1- n)))))

(apt::tailrec triangular :accumulator a)

(must-be-redundant
 (defun triangular{1} (n a)
   (declare (xargs :guard (and (natp n) (acl2-numberp a))
                   :measure (acl2-count n)))
   (if (zp n)
       a
     (triangular{1} (+ -1 n) (+ a n)))))

(must-be-redundant
 (defthmd triangular-to-triangular{1}
   (equal (triangular n)
          (triangular{1} n 0))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Pyramidal numbers have the form 1*1 + 2*2 + 3*3 + ... + n*n:
; each can be visualized as a square pyramid with base n*n
; stacked with decreasing layers (n-1)*(n-1), ..., 2*2, 1*1.
; This function is perhaps more commonly describes as sum of squares.

; The only difference with triangular numbers is that
; it is the square of N that is added at each recursion instead of just N.
; But the binary operation is still + and the identity still 0,
; so again the default variant, :MONOID, works.
; TAILREC again infers ACL2-NUMBERP as the domain of the monoid.

; Here we specify the generation of a wrapper function.
; The names of the new (tail-recursive) and wrapper functions
; are in accordance with :DOC APT::FUNCTION-NAME-GENERATION.

(defun pyramidal (n)
  (declare (xargs :guard (natp n)))
  (if (zp n)
      0
    (+ (* n n) (pyramidal (1- n)))))

(apt::tailrec pyramidal :wrapper t)

(must-be-redundant
 (defun pyramidal-aux{1} (n r)
   (declare (xargs :guard (and (natp n) (acl2-numberp r))
                   :measure (acl2-count n)))
   (if (zp n)
       r
     (pyramidal-aux{1} (+ -1 n) (+ r (* n n))))))

(must-be-redundant
 (defund pyramidal{1} (n)
   (declare (xargs :guard (natp n)))
   (pyramidal-aux{1} n 0)))

(must-be-redundant
 (defthmd pyramidal-to-pyramidal-aux{1}
   (equal (pyramidal n)
          (pyramidal-aux{1} n 0))))

(must-be-redundant
 (defthmd pyramidal-to-pyramidal{1}
   (equal (pyramidal n)
          (pyramidal{1} n))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; We can also transform built-in functions, such as LEN,
; which returns the length of a list,
; but really operates on any value, treating any atom as the empty list.

; Unlike the above examples, LEN does not operate specifically on numbers.
; But the monoid is still the same as some of the above examples:
; ACL2-NUMBERP as domain, + as binary operation, and 1 as identity.
; The monoidal algebraic structure refers
; not to the inputs of the target function, but to its outputs.

; Note also that LEN has the base and recursive branches
; swapped compared to the previous examples.
; But it is easy for TAILREC to handle both cases
; (namely, the case in which the base branch comes first,
; and the case in which the base branch comes second).

(assert-equal (logical-defun 'len (w state))
              '(defun len (x)
                 (declare (xargs :mode :logic))
                 (declare (xargs :guard t))
                 (if (consp x)
                     (+ 1 (len (cdr x)))
                   0)))

(apt::tailrec len)

(must-be-redundant
 (defun len{1} (x r)
   (declare (xargs :guard (acl2-numberp r) :measure (acl2-count x)))
   (if (not (consp x))
       r
     (len{1} (cdr x) (+ r 1)))))

(must-be-redundant
 (defthmd len-to-len{1}
   (equal (len x)
          (len{1} x 0))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; This function adds up all the elements of a list of numbers,
; starting with 0 (i.e. it return 0 on the empty list).

; Here the default :MONOID variant does not work,
; as can be easily seen by calling the transformation without :VARIANT.
; We get an unprovable applicability condition
; requiring the first element of any non-empty list to be an ACL2-NUMBERP:
; note that the guard is not considered by that applicability condition.
; However, the :MONOID-ALT variant works,
; as should be clear by examining, in :DOC TAILREC,
; the different applicability conditions generated for the two variants.
; The binary operation is + here.

(defun list-sum (l)
  (declare (xargs :guard (acl2-number-listp l)))
  (if (endp l)
      0
    (+ (car l) (list-sum (cdr l)))))

(apt::tailrec list-sum :variant :monoid-alt)

(must-be-redundant
 (defun list-sum{1} (l r)
   (declare (xargs :guard (and (acl2-number-listp l) (acl2-numberp r))
                   :measure (acl2-count l)))
   (if (endp l)
       r
     (list-sum{1} (cdr l) (+ r (car l))))))

(must-be-redundant
 (defthmd list-sum-to-list-sum{1}
   (equal (list-sum l)
          (list-sum{1} l 0))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Raising to a power involves more than one argument (base and exponent).
; Here we restrict the exponent to be a natural number,
; which is the argument that decreases in the recursive call.

; Here the default :MONOID variant does not work:
; we get an unprovable applicability condition
; requiring x to be an ACL2-NUMBERP (which is the domain inferred by TAILREC).
; But the :MONOID-ALT variant works.
; The binary operation is * here.

(defun power (x n)
  (declare (xargs :guard (and (acl2-numberp x) (natp n))))
  (if (zp n)
      1
    (* x (power x (1- n)))))

(apt::tailrec power :variant :monoid-alt)

(must-be-redundant
 (defun power{1} (x n r)
   (declare (xargs :guard (and (and (acl2-numberp x) (natp n))
                               (acl2-numberp r))
                   :measure (acl2-count n)))
   (if (zp n)
       r
     (power{1} x (+ -1 n) (* r x)))))

(must-be-redundant
 (defthmd power-to-power{1}
   (equal (power x n)
          (power{1} x n 1))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The following example, list reversal, does not involve numbers at all:
; it involves lists instead.

; Here the :MONOID variant works.
; The binary operator is APPEND (more precisely, BINARY-APPEND),
; for which TAILREC automatically infers TRUE-LISTP as domain.
; The identity is NIL, of course.

(defun list-reverse (l)
  (declare (xargs :guard (true-listp l)))
  (if (atom l)
      nil
    (append (list-reverse (cdr l)) (list (car l)))))

(apt::tailrec list-reverse)

(must-be-redundant
 (defun list-reverse{1} (l r)
   (declare (xargs :guard (and (true-listp l) (true-listp r))
                   :measure (acl2-count l)))
   (if (atom l)
       r
     (list-reverse{1} (cdr l) (append (list (car l)) r)))))

(must-be-redundant
 (defthmd list-reverse-to-list-reverse{1}
   (equal (list-reverse l)
          (list-reverse{1} l nil))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The following example finds the minimum number in a list of rationals.

; Here we must use the :ASSOC-ALT variant;
; none of the other variants would work.
; We must also explicitly supply the domain:
; currently TAILREC only attempts to infer the (right) domain
; in the :MONOID and :MONOID-ALT variants.
; The binary operation is MIN here,
; which is associative but has no identity elements.

(defun list-min (l)
  (declare (xargs :guard (and (rational-listp l)
                              (consp l))))
  (if (endp (cdr l))
      (car l)
    (min (car l) (list-min (cdr l)))))

(apt::tailrec list-min :variant :assoc-alt :domain rationalp)

(must-be-redundant
 (defun list-min{1} (l r)
   (declare (xargs :guard (and (and (rational-listp l) (consp l))
                               (rationalp r))
                   :measure (acl2-count l)))
   (if (endp (cdr l))
       (min r (car l))
     (list-min{1} (cdr l) (min r (car l))))))

(must-be-redundant
 (defthmd list-min-to-list-min{1}
   (equal (list-min l)
          (if (endp (cdr l))
              (car l)
            (list-min{1} (cdr l) (car l))))))
