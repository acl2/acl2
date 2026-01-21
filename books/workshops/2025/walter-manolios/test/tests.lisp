(in-package #:cl-z3/tests)

(defmacro is-sat-assignment (expr)
  `(progn
     (is eq (check-sat) :sat)
     (true (eval-under-model ,expr))))

(defmacro with-reset-z3 (&body body)
  `(unwind-protect
        (progn ,@body)
     (solver-reset)))

(defmacro has-assignments (bindings)
  `(progn
     (is eq (check-sat) :sat)
     ,@(loop for binding in bindings
             collect `(is equal (eval-under-model ,(car binding)) ,(second binding)))))

(define-test basic
    (solver-init)
  (with-reset-z3
      (z3-assert (x :bool y :int)
                 (and x (>= y 5)))
    (is-sat-assignment (and x (>= y 5))))
  (with-reset-z3
      (z3-assert (x :bool)
                 (and x (not x)))
    (is eq (check-sat) :unsat))
  (with-reset-z3
      (declare-const x :int)
    (declare-const y :int)
    (z3-assert (= (+ x y) 10))
    (is-sat-assignment (= (+ x y) 10)))
  (with-reset-z3
      (fail (z3-assert (z :int z :bool)
                       (and z (> z 3)))))
  (with-reset-z3
      (z3-assert (x :bool)
                 (and x (not x)))
    (is eq (check-sat) :unsat)
    (fail (get-model))))

(define-test bitvectors
    (solver-init)
  (with-reset-z3
      (z3-assert (v (_ :bitvec 5))
                 (= (bv2int v nil) 20))
    (has-assignments ((v 20)))))

(define-test optimize
    (solver-init)
  (setf *default-solver* (make-optimizer))
  (z3-assert (aapl msft googl :int)
             (and (= (+ aapl msft googl) 200000)
                  (<= (+ aapl msft) 100000)
                  (<= googl 100000)))
  (optimize-maximize ()
                     (+ (* 6 aapl) (* 14 msft) (* 15 googl)))
  (has-assignments ((aapl 100000) (googl 100000) (msft 0))))

(define-test quantifiers
    (solver-init)
  (with-reset-z3
      (z3-assert (x :int)
                 (forall (y :int) (== (* x y) y)))
    (has-assignments ((x 1))))
  (with-reset-z3
      (z3-assert (x :bool)
                 (exists (y :bool) (== x y)))
    (is eq (check-sat) :sat))
  (with-reset-z3
      (z3-assert (x :bool)
                 (forall (y :bool) (== x y)))
    (is eq (check-sat) :unsat))
  (with-reset-z3
      (z3-assert (x :int)
                 (and (== x 0)
                      (exists (x :int) (forall (y :int) (== (* x y) y)))))
    (is eq (check-sat) :sat)))

(define-test sequences
    (solver-init)
  (with-reset-z3
      (z3-assert (x y (:seq :int))
                 (= (seq.++ x y) (seq 1 2 3 4 5)))
    (is eq (check-sat) :sat)
    (is equal (append (eval-under-model x) (eval-under-model y))
        '(1 2 3 4 5))))

(define-test strings
    (solver-init)
  (with-reset-z3
      (z3-assert (x :string y :string)
                 (= (str.++ x y) "Hello, World!"))
    (is eq (check-sat) :sat)
    (is equal (concatenate 'string (eval-under-model x) (eval-under-model y))
        "Hello, World!"))
  (with-reset-z3
      (z3-assert (x :string y :int)
                 (and (= x (int.to.str 5))
                      (= y (str.to.int "3"))))
    (has-assignments ((x "5") (y 3)))))

(define-test tuples
    (solver-init)
  (with-reset-z3
      (register-tuple-sort :blah ((a . :int) (b . :bool)))
    (z3-assert (r :blah)
               (and (= (tuple-get :blah a r) 5)
                    (tuple-get :blah b r)))
    (is eq (check-sat) :sat)
    (is equal (eval-under-model (tuple-get :blah a r)) 5)
    (is equal (eval-under-model (tuple-get :blah b r)) t)))
