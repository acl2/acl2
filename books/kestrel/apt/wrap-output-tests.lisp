; Tests of the wrap-output transformation
;
; Copyright (C) 2014-2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)
; Supporting Author: Nathan Guermond
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "wrap-output")
(include-book "kestrel/utilities/deftest" :dir :system)

(deftest
  (defun bool-to-bit (x) (if x 1 0))
  (defun contains-3 (lst)
    (if (endp lst)
        nil
      (if (equal 3 (first lst))
          t
        (contains-3 (rest lst)))))
  ;; Build a version of contains-3 that returns 1 or 0 rather than true/false:
  (wrap-output contains-3 (lambda (x) (bool-to-bit x)))
  (must-be-redundant
    ;; new function (always returns 0 or 1)
    (defun contains-3$1 (lst)
;      (declare (xargs :measure (acl2-count lst)))
      (if (endp lst)
          (bool-to-bit nil) ;base case got wrapped (this could be simplified to 0)
        (if (equal 3 (first lst))
            (bool-to-bit t) ;also got wrapped, could be simplified to 1
          (contains-3$1 (rest lst))))) ;tail-call changed to call new function but not wrapped in bool-to-bit (new function already does the wrapping)
    (defthm contains-3-contains-3$1-connection
      (equal (bool-to-bit (contains-3 lst))
             (contains-3$1 lst))))
  ;;just to check (the transformation doesn't produce this):
  (defthm contains-3$1-type
   (or (equal 0 (contains-3$1 lst))
       (equal 1 (contains-3$1 lst)))
   :rule-classes nil))

(deftest
  ;; a weird identity function on nats
  (defun copy (n)
    (if (zp n)
        0
      (+ 1 (copy (+ -1 n)))))

  ;; Build a function of n equivalent to (* 2 (copy n)) by pushing the doubling
  ;; into the IF-branches of COPY.
  (wrap-output copy (lambda (x) (binary-* '2 x))) ;todo: can this be an untranslated term too?

  (must-be-redundant
    (defun copy$1 (n)
      (declare (xargs :measure (acl2-count n)))
      (if (zp n)
          (binary-* '2 0)
        (binary-* '2
                  (+ 1 (copy (+ -1 n)))))) ;;whoa!  This call didn't get fixed up...   May not be a way to do this in general

    (defthm copy-copy$1-connection
      (equal (binary-* 2 (copy n))
             (copy$1 n)))

    ;; Now we would apply distibutivity laws and simplify-body to make the function recursive again (after bringing the doubling inward so that it applies to the recursive call).
    ))


;TODO: Add an example of a list or tree (?)

;; Test :function-disabled and :theorem-disabled:
(deftest
  (defun copy (n)
    (if (zp n)
        0
      (+ 1 (copy (+ -1 n)))))

  ;; Build a function of n equivalent to (* 2 (copy n)) by pushing the doubling
  ;; into the IF-branches of COPY.
  (wrap-output copy (lambda (x) (binary-* '2 x)) :theorem-disabled t :function-disabled t))

;; Test the case where we supply the name of a unary function as the wrapper:
(deftest
  (defun double (x) (* 2 x))
  (defun copy (n)
    (if (zp n)
        0
      (+ 1 (copy (+ -1 n)))))

  ;; Build a function of n equivalent to (* 2 (copy n)) by pushing the doubling
  ;; into the IF-branches of COPY.
  (wrap-output copy double :theorem-disabled t :function-disabled t))

;Try some tests like deforestation (map, filter, etc.)

;; Test the :new-name
(deftest
  (defun double (x) (* 2 x))
  (defun copy (n)
    (if (zp n)
        0
      (+ 1 (copy (+ -1 n)))))

  ;; Build a function of n equivalent to (* 2 (copy n)) by pushing the doubling
  ;; into the IF-branches of COPY.
  (wrap-output copy double :theorem-disabled t :function-disabled t :new-name bar)
  (must-be-redundant
   (DEFUND BAR (N)
     (DECLARE (XARGS :VERIFY-GUARDS NIL))
     (IF (ZP N)
         (DOUBLE 0)
         (DOUBLE (+ 1 (COPY (+ -1 N)))))) ;note that this is not a recursive call
   (DEFTHMD COPY-BAR-CONNECTION
     (EQUAL (DOUBLE (COPY N))
            (BAR N))
     :HINTS (("Goal" :INDUCT T
              :IN-THEORY '(COPY BAR))))))

;; Test of wrapping a non-recursive function:
(deftest
  (defun double (x) (* 2 x))
  (defun triple (x)
    (if (zp x)
        0
      (* 3 x)))

  (wrap-output triple double)

  (must-be-redundant
   (DEFUN TRIPLE$1 (X)
     (DECLARE (XARGS :VERIFY-GUARDS NIL))
     (IF (ZP X)
         (DOUBLE 0)
         (DOUBLE (* 3 X))))

   (DEFTHM TRIPLE-TRIPLE$1-CONNECTION
     (EQUAL (DOUBLE (TRIPLE X))
            (TRIPLE$1 X))
     :HINTS (("Goal" :IN-THEORY '(TRIPLE TRIPLE$1))))))


;; An example where the wrapper has an extra param
(deftest
  (defun copy-elems (lst)
    (if (endp lst)
        nil
      (cons (first lst)
            (copy-elems (rest lst)))))
  (defun copy-and-filter (x y)
    (intersection-equal (copy-elems x) y))
  ;; ;; we want to push the intersection into the loop
  ;; ;; we want something like this:
  ;; (defun copy-elems.2 (lst y)
  ;;   (if (endp lst)
  ;;       nil
  ;;     (if (member-equal (first lst) y)
  ;;         (cons (first lst)
  ;;               (copy-elems.2 (rest lst) y))
  ;;       (copy-elems.2 (rest lst) y))))
  ;; (defthm copy-elems.2-correct
  ;;   (equal (intersection-equal (copy-elems x) y)
  ;;          (copy-elems.2 x y)))
  (wrap-output copy-elems (lambda (x) (intersection-equal x y)))
  (must-be-redundant
   ;; Not yet recursive but could be made recursive again by applying
   ;; distributivity rules and copy-elems-copy-elems$1-connection.
   (defun copy-elems$1 (lst y)
     (declare (xargs :verify-guards nil))
     (if (endp lst)
         (intersection-equal nil y)
       (intersection-equal (cons (first lst)
                                 (copy-elems (rest lst)))
                           y)))
   (defthm copy-elems-copy-elems$1-connection
     (equal (intersection-equal (copy-elems lst) y)
            (copy-elems$1 lst y)))))

;; An example where the wrapper has an extra param and there is a tail call to fix up
(deftest
  (defun first-nat (lst)
    (if (endp lst)
        0
      (if (natp (first lst))
          (first lst)
        (first-nat (rest lst)))))
  (wrap-output first-nat (lambda (x) (< x bound)))
  (must-be-redundant
   (DEFUN FIRST-NAT$1 (LST BOUND)
     (DECLARE (XARGS :VERIFY-GUARDS NIL))
     (IF (ENDP LST)
         (< 0 BOUND)
         (IF (NATP (FIRST LST))
             (< (FIRST LST) BOUND)
             ;; this has the new formal BOUND added in:
             (FIRST-NAT$1 (REST LST) BOUND))))))


;TODO: Can we do firstn of sort ?


;; TESTS ON MACROS, INCLUDING OR, AND, LET, etc.
;; wrap-output only works on the untranslated body, so that macros are not expanded
(deftest
  (defmacro foo-body ()
    `(if (zp n) x
       (foo x (1- n))))
  (defun foo (x n)
    (foo-body))
  (wrap-output foo identity)
  (must-be-redundant
   (DEFUN FOO$1 (X N)
     (DECLARE (XARGS :VERIFY-GUARDS NIL))
     (IDENTITY (FOO-BODY)))
   (DEFTHM FOO-FOO$1-CONNECTION
     (EQUAL (IDENTITY (FOO X N)) (FOO$1 X N)))))

;; Test nary and:
(deftest
  (defun foo (x y z w)
    (and x y z w))
  (defstub f (x) t)
  (wrap-output foo (lambda (x) (f x)))
  (must-be-redundant
   (DEFUN FOO$1 (X Y Z W)
     (DECLARE (XARGS :VERIFY-GUARDS NIL))
     (IF (AND X Y Z) (F W) (F NIL)))
   (DEFTHM FOO-FOO$1-CONNECTION
     (EQUAL (F (FOO X Y Z W)) (FOO$1 X Y Z W))))
  )

;; Test 0-ary and:
(deftest
  (defun foo ()
    (and))
  (defstub f (x) t)
  (wrap-output foo (lambda (x) (f x)))
  (must-be-redundant
   (DEFUN FOO$1 NIL (DECLARE (XARGS :VERIFY-GUARDS NIL)) (F T))
   (DEFTHM FOO-FOO$1-CONNECTION
     (EQUAL (F (FOO)) (FOO$1))))
  )

;; Test unary and:
(deftest
  (defun foo (x)
    (and x))
  (defstub f (x) t)
  (wrap-output foo (lambda (x) (f x)))
  (must-be-redundant
   (DEFUN FOO$1 (X) (DECLARE (XARGS :VERIFY-GUARDS NIL)) (F X))
   (DEFTHM FOO-FOO$1-CONNECTION
     (EQUAL (F (FOO X)) (FOO$1 X))))
  )

;; Test binary and:
(deftest
  (defun foo (x y)
    (and x y))
  (defstub f (x) t)
  (wrap-output foo (lambda (x) (f x)))
  (must-be-redundant
   (DEFUN FOO$1 (X Y)
     (DECLARE (XARGS :VERIFY-GUARDS NIL))
     (IF X (F Y) (F NIL)))
   (DEFTHM FOO-FOO$1-CONNECTION
     (EQUAL (F (FOO X Y)) (FOO$1 X Y))))
  )


;; 'or' is not fully implemented, each of these tests fail!
#|
;; Test nary or:
(deftest
  (defun foo (x y z w)
    (or x y z w))
  (defstub f (x) t)
  (wrap-output foo (lambda (x) (f x)) :print :all))

;; Test 0-ary or:
(deftest
  (defun foo ()
    (or))
  (defstub f (x) t)
  (wrap-output foo (lambda (x) (f x)) :print :all))

;; Test unary or:
(deftest
  (defun foo (x)
    (or x))
  (defstub f (x) t)
  (wrap-output foo (lambda (x) (f x)) :print :all))

;; Test binary or:
(deftest
  (defun foo (x y)
    (or x y))
  (defstub f (x) t)
  (wrap-output foo (lambda (x) (f x)) :print :all))
|#


;; test let
(deftest
  (defun foo (x n)
    (if (zp n) x
      (let ((y x) (z x))
        (declare (ignore z))
        (foo y (1- n)))))
  (defstub f (x) t)
  (wrap-output foo (lambda (x) (f x)))
  (must-be-redundant
   (DEFUN FOO$1 (X N)
     (IF (ZP N)
         (F X)
         (LET ((Y X) (Z X))
              (DECLARE (IGNORE Z))
              (FOO$1 Y (1- N)))))
   (DEFTHM FOO-FOO$1-CONNECTION
     (EQUAL (F (FOO X N)) (FOO$1 X N)))
   ))

;; test let*
(deftest
  (defun foo (x n)
    (if (zp n) x
      (let* ((y x)
             (z x)
             (w x))
        (declare (ignore w))
        (* z (foo y (1- n))))))
  (defstub f (x) t)
  (wrap-output foo (lambda (x) (f x)))
  (must-be-redundant
   (DEFUN FOO$1 (X N)
     (IF (ZP N)
         (F X)
         (LET* ((Y X) (Z X) (W X))
               (DECLARE (IGNORE W))
               (F (* Z (FOO Y (1- N)))))))
   (DEFTHM FOO-FOO$1-CONNECTION
     (EQUAL (F (FOO X N)) (FOO$1 X N))))
  )

;; test b*
(deftest
  (defun foo (x n)
    (if (zp n) x
      (b* ((y x)
             (z x))
        (* z (foo y (1- n))))))
  (defstub f (x) t)
  (wrap-output foo (lambda (x) (f x)))
  (must-be-redundant
   (DEFUN FOO$1 (X N)
     (IF (ZP N)
         (F X)
         (B* ((Y X) (Z X))
           (F (* Z (FOO Y (1- N)))))))
   (DEFTHM FOO-FOO$1-CONNECTION
     (EQUAL (F (FOO X N)) (FOO$1 X N))))
  )


;; VARIABLE BINDING TESTS

;; wrapper applied to tail-recursive function
(deftest
  (defun fac (n acc)
    (if (zp n)
        acc
      (fac (1- n) (* n acc))))
  (wrap-output fac (lambda (n) (* 2 n)))
  (must-be-redundant
   (DEFUN FAC$1 (N ACC)
     (IF (ZP N)
         (* 2 ACC)
         (FAC$1 (1- N) (* N ACC))))
   (DEFTHM FAC-FAC$1-CONNECTION
     (EQUAL (* 2 (FAC N ACC)) (FAC$1 N ACC))))
  )

;; add a free variable in wrapper
(deftest
  (defun fac (n)
    (if (zp n)
        1
      (* n (fac (1- n)))))
  (wrap-output fac (lambda (n) (* m n)))
  (must-be-redundant
   (DEFUN FAC$1 (N M)
     (DECLARE (XARGS :VERIFY-GUARDS NIL))
     (IF (ZP N)
         (* M 1)
         (* M (* N (FAC (1- N))))))
   (DEFTHM FAC-FAC$1-CONNECTION
     (EQUAL (* M (FAC N)) (FAC$1 N M)))
   ))

;; add function parameter as free variable in wrapper
(deftest
  (defun fac (n)
    (if (zp n)
        1
      (* n (fac (1- n)))))
  (wrap-output fac (lambda (m) (* n m)))
  (must-be-redundant
   (DEFUN FAC$1 (N)
     (DECLARE (XARGS :VERIFY-GUARDS NIL))
     (IF (ZP N)
         (* N 1)
         (* N (* N (FAC (1- N))))))
   (DEFTHM FAC-FAC$1-CONNECTION
     (EQUAL (* N (FAC N)) (FAC$1 N)))
   ))


;; add function parameter as free variable in wrapper, but with tail recursive function
;; this gives example in which equivalence between (wrapper . fac) and fac$1 fails
(deftest
  (defun fac (n acc)
    (if (zp n)
        acc
      (fac (1- n) (* n acc))))
  ;; this fails
  ;; (wrap-output fac (lambda (m) (* n m)) :print :all)
  ;; this defines
  (DEFUN FAC$1 (N ACC)
    (IF (ZP N)
        (* N ACC)
        (FAC$1 (1- N) (* N ACC))))
  ;; and tries to prove
  ;; (DEFTHM FAC-FAC$1-CONNECTION
  ;;   (EQUAL (* N (FAC N ACC)) (FAC$1 N ACC))))
  ;; but this fails because
  (defthm fac$1-is-zero
    (implies (natp n)
             (equal (fac$1 n acc) 0))))

;; example of why free variables in wrapper cannot become bound in a lambda term!
(deftest
  (defun test-lambda (x n)
    (if (zp n) x
      ((lambda (y)
         ;(* y (test-lambda y (1- n))))
         (test-lambda y (1- n)))
       x)))
  ;; this fails
  ;; (wrap-output test-lambda (lambda (x) (* y x)) :print :all)
  ;; and defines
  (DEFUN TEST-LAMBDA$1 (X N Y)
    (IF (ZP N)
        (* Y X)
        ((LAMBDA (Y)
                 (TEST-LAMBDA$1 Y (1- N) Y))
         X)))
  ;; and produces
  ;; (DEFTHM TEST-LAMBDA-TEST-LAMBDA$1-CONNECTION
  ;;   (EQUAL (* Y (TEST-LAMBDA X N))
  ;;          (TEST-LAMBDA$1 X N Y)))
  ;; but this fails because test-lambda$1 does not depend on y
  (defthm test-lambda$1-is-x^2
    (implies (not (zp n))
             (equal (test-lambda$1 x n y) (* x x)))))

;; test that variable clashes are ok when not free
(deftest
  (defun test-lambda (x n)
    (if (zp n) x
      ((lambda (x) (* x (test-lambda x (1- n)))) x)))
  (wrap-output test-lambda (lambda (x) (* x x)) :print :all)
  (must-be-redundant
   (DEFUN TEST-LAMBDA$1 (X N)
     (IF (ZP N)
         (* X X)
         ((LAMBDA (X)
                  (* (* X (TEST-LAMBDA X (1- N)))
                     (* X (TEST-LAMBDA X (1- N)))))
          X)))
   (DEFTHM TEST-LAMBDA-TEST-LAMBDA$1-CONNECTION
     (EQUAL (* (TEST-LAMBDA X N) (TEST-LAMBDA X N))
            (TEST-LAMBDA$1 X N))))
  )

;; proving the equivalence of foo and foo$1 actually fails here,
;; this example suggests there should be an option for adding hints to the
;; equivalence theorem?
(deftest
  (defun foo (x)
    (if (equal x 1)
        (foo (1- x))
      0))
  ;; this fails
  ;; (wrap-output foo (lambda (x) (1+ x)) :print :all)
  )

;; test wrapping in lambdas
(deftest
  (defun test-lambdas (x n)
    (cond ((zp n) 0)
          ((equal x 1)
           ((lambda (x) (test-lambdas x (1- n))) x))
          ((equal x 2)
           ((lambda (y) (test-lambdas y (1- n))) x))
          ((equal x 3)
           ((lambda (y) (* y (test-lambdas x (1- n)))) x))
          ((equal x 4)
           (* x ((lambda (y) (test-lambdas y (1- n))) x)))
          ((equal x 5)
           ((lambda (y) y) (test-lambdas x (1- n))))
          ((equal x 6)
           ((lambda (y) y) (* x (test-lambdas x (1- n)))))
          ((equal x 7)
           (* x ((lambda (y) y) (test-lambdas x (1- n)))))
          (t 0)))
  ;; show-only because hints for equivalence are otherwise needed (see example above)
  (wrap-output test-lambdas identity :show-only t)
  ;; this produces (not redundant because show-only)
   (DEFUN TEST-LAMBDAS$1 (X N)
     (COND ((ZP N) (IDENTITY 0))
           ((EQUAL X 1)
            ((LAMBDA (X) (TEST-LAMBDAS$1 X (1- N))) X))
           ((EQUAL X 2)
            ((LAMBDA (Y) (TEST-LAMBDAS$1 Y (1- N))) X))
           ((EQUAL X 3)
            ((LAMBDA (Y) (IDENTITY (* Y (TEST-LAMBDAS X (1- N))))) X))
           ((EQUAL X 4)
            (IDENTITY (* X ((LAMBDA (Y) (TEST-LAMBDAS Y (1- N))) X))))
           ((EQUAL X 5)
            ((LAMBDA (Y) (IDENTITY Y)) (TEST-LAMBDAS X (1- N))))
           ((EQUAL X 6)
            ((LAMBDA (Y) (IDENTITY Y)) (* X (TEST-LAMBDAS X (1- N)))))
           ((EQUAL X 7)
            (IDENTITY (* X ((LAMBDA (Y) Y) (TEST-LAMBDAS X (1- N))))))
           (T (IDENTITY 0)))))


;; this gives a hard error because bar takes two arguments
(deftest
  (defun foo (x)
    x)
  (defun bar (x y) (list x y))
  ;(wrap-output foo bar)
  )


;; Test involving normalizaion:  TODO: Get this to work

;; (deftest
;;   (defstub stub (x) t)

;;   (defun foo (params)
;;     (declare (xargs :measure (acl2-count (car params))))
;;     (if (zp (car params))
;;         params
;;       (foo (list (+ -1 (car params))
;;                  ;; The not here (really an IF) gets lifted by normalization
;;                  (stub (not (cadr params)))))))

;;   (wrap-output foo (lambda (x) (nth 0 x))))


;; MUTUAL-RECURSION TESTS

;; Test with a mutual-recursion
(deftest
  (set-bogus-mutual-recursion-ok t) ;fixme
  (wrap-output pseudo-termp ;defined in a mutual-recursion
               (lambda (x) (not x))))

;; Test with a mutual-recursion and an extra param
(deftest
  (set-bogus-mutual-recursion-ok t) ;fixme
  (wrap-output pseudo-termp ;defined in a mutual-recursion
               (lambda (x) (and x y)))) ;y is an extra param

;; Test :new-name option with :map for mutual-recursion
(deftest
  (set-bogus-mutual-recursion-ok t) ;fixme
  (wrap-output pseudo-termp ;defined in a mutual-recursion
               (lambda (x) (not x))
               :new-name (:map (pseudo-termp foo) (pseudo-term-listp bar))))


;; Test :guard option with :map for mutual-recursion
(deftest
  (set-bogus-mutual-recursion-ok t) ;fixme
  (wrap-output pseudo-termp ;defined in a mutual-recursion
               (lambda (x) (not x))
               :guard (:map (pseudo-termp (eql 2 2))
                            (pseudo-term-listp (eql 3 3)))))


;; test guards
(deftest
  (encapsulate nil
    (local (include-book "arithmetic/top-with-meta" :dir :system))
    (local (include-book "arithmetic-5/top" :dir :system))
    (defun dec-x<y (x y)
      (declare (xargs :guard (and (natp x) (posp y) (< (/ x y) 1))))
      (if (zp x)
          (cons x y)
        (dec-x<y (1- x) (1- y))))

    (defun out (|(cons x y)|)
      (declare (xargs :guard (and (consp |(cons x y)|)
                                  (rationalp (car |(cons x y)|))
                                  (rationalp (cdr |(cons x y)|))
                                  (< (* (car |(cons x y)|) (cdr |(cons x y)|)) (/ 1 2)))))
      |(cons x y)|))

  (wrap-output dec-x<y out)
  (must-be-redundant
   (DEFUN DEC-X<Y$1 (X Y)
     (DECLARE (XARGS :VERIFY-GUARDS T
                     :GUARD (AND (NATP X) (POSP Y) (< (/ X Y) 1))))
     (IF (ZP X)
         (OUT (CONS X Y))
         (DEC-X<Y$1 (1- X) (1- Y))))
   (DEFTHM DEC-X<Y-DEC-X<Y$1-CONNECTION
     (EQUAL (OUT (DEC-X<Y X Y))
            (DEC-X<Y$1 X Y))))
  )

;; ;; test guard-hints for mutual-rec

;; This is introduced here because I couldn't think of a mutual-recursion guard
;; which could not be proved without additional hints in wrap-output
;; we leave this commented for obvious reasons.
;; if this is even needed, think of safer replacement?

;; (defaxiom omnipotent-axiom
;;   nil
;;   :rule-classes nil)

;; (deftest
;;   (mutual-recursion
;;    (defun foo-1 (x)
;;      (declare (xargs :measure (acl2-count x)
;;                      :guard (natp x)))
;;      (if (zp x) 0
;;        (foo-2 (1- x))))
;;    (defun foo-2 (x)
;;      (declare (xargs :measure (acl2-count x)
;;                      :guard (natp x)))
;;      (if (zp x) 0
;;        (foo-1 (1- x)))))

;;   (defun bar (x)
;;     (declare (xargs :guard nil))
;;     x)

;;   ;; this fails
;;   ;; (wrap-output foo-1 bar)
;;   (wrap-output foo-1 bar :guard-hints (("Goal" :use (:instance omnipotent-axiom))))
;;   )

;; Test that previously faile because of the handling of not-normalized.
(deftest
  (defun empty-clause () (declare (xargs :guard t)) nil)

  (defun foo99 (pairs)
    (declare (xargs :guard (true-listp pairs)))
    (if (endp pairs)
        nil
      (cons '(xxx)
            (foo99 (rest pairs)))))

  (wrap-output foo99
               (lambda (result)
                 (if (member-equal (empty-clause) result)
                     (list (empty-clause))
                   result))))
