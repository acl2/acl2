(in-package "STD")

(include-book "define")

(define foo ()
  :returns (ans integerp)
  3)

(define foo2 ()
  (mv 3 "hi"))

(define foo3 ()
  (mv 3 "hi"))

(define foo4 ()
  :returns (ans integerp)
  44)

(define foo5 ((x oddp :type integer))
  :returns (ans integerp :hyp :guard)
  (- x 1))

(define foo6 ((x oddp :type (integer 0 *)))
  :returns (ans natp :hyp :guard)
  (- x 1))

(define foo7
  :parents (|look ma, parents before formals, even!|)
  (x)
  (consp x))

(encapsulate
  ()
  (logic)
  (define foo8 (x)
    :mode :program
    (+ 1 x)))

(encapsulate
  ()
  (logic)
  (define foo9 (x)
    (declare (xargs :mode :program))
    (+ 2 x)))

(encapsulate
  ()
  (program)
  (define foo10 ((x natp))
    (declare (xargs :mode :logic))
    (+ 2 x)))

(encapsulate
  ()
  (program)
  (define foo11 (x)
    (declare (xargs :mode :program))
    (+ 3 x)))

(encapsulate
  ()
  (program)
  (define foo12 (x)
    :mode :program
    (+ 3 x)))




(encapsulate
  ()
  (logic)
  (define bar8 (x &optional y)
    :mode :program
    (+ 1 x y)))

(encapsulate
  ()
  (logic)
  (define bar9 (x &optional y)
    (declare (xargs :mode :program))
    (+ 2 x y)))

(encapsulate
  ()
  (program)
  (define bar10 ((x natp) &optional (y natp))
    (declare (xargs :mode :logic))
    (+ 2 x y)))

(encapsulate
  ()
  (program)
  (define bar11 (x &optional y)
    (declare (xargs :mode :program))
    (+ 3 x y)))

(encapsulate
  ()
  (program)
  (define bar12 (x &optional y)
    :mode :program
    (+ 3 x y)))




(define m0 (x)
  (consp x))

(assert! (let ((topic (xdoc::find-topic 'm0 (xdoc::get-xdoc-table (w state)))))
           (and topic
                (equal (cdr (assoc :parents topic))
                       '(acl2::undocumented)))))

(xdoc::set-default-parents foo bar)

(define m1 (x)
  (consp x))

(assert! (let ((topic (xdoc::find-topic 'm1 (xdoc::get-xdoc-table (w state)))))
           (and topic
                (equal (cdr (assoc :parents topic))
                       '(foo bar)))))

(define m2 (x)
  (consp x)
  :parents (bar))

(assert! (let ((topic (xdoc::find-topic 'm2 (xdoc::get-xdoc-table (w state)))))
           (and topic
                (equal (cdr (assoc :parents topic))
                       '(bar)))))

(define m3 (x)
  (consp x)
  :parents nil)

(assert! (let ((topic (xdoc::find-topic 'm3 (xdoc::get-xdoc-table (w state)))))
           (not topic)))




