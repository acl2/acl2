; Copyright (C) 2013, ForrestHunt, Inc.
; Written by J Strother Moore (some years before that)
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

(in-package "ACL2")

(include-book "huet-lang-algorithm")

(defstub h (x) t)

(defun generic-run (s n)
  (if (zp n)
      s
    (generic-run (h s) (- n 1))))

(defun m5-run (s n)
  (if (zp n)
      s
    (m5-run (cons 3 s) (- n 1))))

(set-state-ok t)

(defun hld-test-fn (generic concrete ans state)
  (declare (xargs :mode :program))
  (if (equal (hld generic
                  concrete
                  '(-1 . nil) ; psubst0
                  nil ; restrictions
                  nil ; toxic-fnname
                  1   ; eriapw repetition max
                  (w state))
             ans)
      (value t)
    (er soft 'hld-test "HLD Test failed ~x0 versus ~x1" generic concrete)))

(defmacro hld-test (generic concrete ans)
  `(make-event (er-progn (hld-test-fn ,generic ,concrete ,ans state)
                         (value '(value-triple t)))))

(hld-test
 '(generic-run s n)
 '(m5-run s n)
 '((15/4 (H LAMBDA (X) (CONS '3 X))
         (N . N)
         (S . S)
         (GENERIC-RUN LAMBDA (S N)
                      (M5-RUN S N)))))

(defun map-h (x)
  (if (endp x)
      nil
    (cons (h (car x)) (map-h (cdr x)))))

(defthm map-h-append
  (equal (map-h (append y z))
         (append (map-h y) (map-h z)))
  :rule-classes nil)

(defun bumper1 (u v w)
  (if (endp u)
      nil
    (cons (+ (* w (car u)) v)
          (bumper1 (cdr u) v w))))

(hld-test '(map-h x)
          '(bumper1 a c d)
          '((23/7 (H LAMBDA (X)
                     (BINARY-+ (BINARY-* D X) C))
                  (X . A)
                  (MAP-H LAMBDA (X) (BUMPER1 X C D)))))

(defun bumper2 (u v w)
  (if (consp u)
      (cons (+ (* w (car u)) v)
            (bumper2 (cdr u) v w))
    nil))

(hld-test '(map-h x)
          '(bumper2 a c d)
          '((23/7 (H LAMBDA (X)
                     (BINARY-+ (BINARY-* D X) C))
                  (X . A)
                  (MAP-H LAMBDA (X) (BUMPER2 X C D)))))

(defun bumper3 (u v w)
  (if (consp u)
      (if (zp (car u))
          (cons 0 (bumper3 (cdr u) v w))
          (cons (+ (* w (car u)) v)
                (bumper3 (cdr u) v w)))
    nil))

(hld-test '(map-h x)
          '(bumper3 a c d)
          '((23/7 (H LAMBDA (X)
                     (IF (ZP X)
                         '0
                         (BINARY-+ (BINARY-* D X) C)))
                  (X . A)
                  (MAP-H LAMBDA (X) (BUMPER3 X C D)))))

(defun generic-exists (x)
  (if (endp x)
      nil
    (or (h x)
        (generic-exists (cdr x)))))

; This next one takes less than 1 second if you use a rewrite max of 4
; or less, but takes 90 seconds if you use 5.

(hld-test '(generic-exists x)
          '(member-equal e lst)
          '((17/5 (H LAMBDA (X)
                    (IF (EQUAL E (CAR X)) X 'NIL))
                 (X . LST)
                 (GENERIC-EXISTS LAMBDA (X)
                                 (MEMBER-EQUAL E X)))))

(defstub g (x y) t)

(defun generic-list-iterator (x ans)
  (cond ((endp x) ans)
        (t (generic-list-iterator (cdr x) (g (car x) ans)))))

(hld-test '(generic-list-iterator x ans)
          '(revappend a b)
          '((19/5 (G LAMBDA (X Y) (CONS X Y))
               (ANS . B)
               (X . A)
               (GENERIC-LIST-ITERATOR LAMBDA (X ANS)
                                      (REVAPPEND X ANS)))))

(defun get-integers (x a)
  (cond ((consp x)
         (cond ((integerp (car x))
                (get-integers (cdr x) (cons (car x) a)))
               (t (get-integers (cdr x) a))))
        (t a)))

(hld-test '(generic-list-iterator x ans)
          '(get-integers a b)
          '((19/5 (G LAMBDA (X Y)
                  (IF (INTEGERP X) (CONS X Y) Y))
               (ANS . B)
               (X . A)
               (GENERIC-LIST-ITERATOR LAMBDA (X ANS)
                                      (GET-INTEGERS X ANS)))))

(include-book "std/testing/must-fail" :dir :system)
(include-book "std/testing/must-succeed" :dir :system)

(must-succeed
 (cond
  ((and
    (equal (hld '(h x) '(car (cdr a)) '(-1 . nil) nil nil 1 (w state))
           '((7/2 (X . A) (H LAMBDA (X) (CAR (CDR X))))
             (7/2 (X CDR A) (H LAMBDA (X) (CAR X)))
             (3 (X CAR (CDR A)) (H LAMBDA (X) X))
             (5/2 (H LAMBDA (X) (CAR (CDR A))))))
    (equal (hld '(h x) '(car (cdr a))
                (convert-var-and-fn-alists-to-psubst '((x . a))
                                                     nil
                                                     (w state))
                nil nil 1 (w state))
           '((7/2 (H LAMBDA (X) (CAR (CDR X))) (X . A))
             (5/2 (H LAMBDA (X) (CAR (CDR A))) (X . A))))
    (equal (hld '(h x) '(car (cdr a))
                (convert-var-and-fn-alists-to-psubst nil
                                                     '((h . car))
                                                     (w state))
                nil nil 1 (w state))
           '((7/2 (X CDR A) (H LAMBDA (X) (CAR X)))))
    (equal (hld '(h x) '(car (cdr a))
                (convert-var-and-fn-alists-to-psubst nil
                                                     '((h . (lambda (x) x)))
                                                     (w state))
                nil nil 1 (w state))
           '((3 (X CAR (CDR A)) (H LAMBDA (X) X)))))
   (value t))
  (t (er soft 'special "HLD failed the extension test!"))))

(definst map-h-append bumper1)

(definst map-h-append bumper2)

(definst map-h-append bumper3)

(defthm generic-run-sum
  (implies (and (integerp i)
                (<= 0 i)
                (integerp j)
                (<= 0 j))
           (equal (generic-run s (+ i j))
                  (generic-run (generic-run s i) j))))

(definst generic-run-sum m5-run)

(defthm generic-list-iterator-append
  (equal (generic-list-iterator (append u v) a)
         (generic-list-iterator v (generic-list-iterator u a))))


; This one should fail to find an instantiation.

(must-fail
 (definst generic-list-iterator-append true-listp)) ; <--- expected to fail!
