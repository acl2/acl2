; Low-Seven:  An Exploration of a Ghostly Defsys
; J Strother Moore
; March, 2012

; (include-book "defsys")
; (certify-book "low-seven" 1)

(in-package "M1")

; Low-seven looks for the digit 7 in the decimal representation of x, stopping
; after it has inspected n digits.  If it finds it, it returns its position.
; For example, (low-seven 9753 0 5) returns 2 because the lowest-order 7 occurs
; at 10^2.  If there is no 7 among the low order n digits, low-seven returns
; nil.

; We will implement low-seven with an M1 program that does not halt unless it
; finds a seven.

; Note: This is just a warm-up for more interesting proofs about
; non-terminating programs.  Obviously, low-seven could look through all the
; digits of x by stopping when x becomes 0, but we're not doing that, on
; purpose!

(defun low-seven! (x a n)
  (declare (xargs :measure (acl2-count n)))
  (if (zp n)
      (mv 0 x a)
      (if (equal (mod x 10) 7)
          (mv 1 x a)
          (low-seven! (floor x 10) (+ 1 a) (- n 1)))))

(defsys
  :ld-flg nil
  :modules
  ((lessp :formals (x y)
          :input (and (natp x)
                      (natp y))
          :output (if (< x y) 1 0)
          :code (ifeq y
                      0
                      (ifeq x
                            1
                            (lessp (- x 1) (- y 1)))))
   (mod :formals (x y)
        :input (and (natp x)
                    (natp y)
                    (not (equal y 0)))
        :output (mod x y)
        :code (ifeq (lessp x y)
                    (mod (- x y) y)
                    x))
   (floor :formals (x y a)
          :input (and (natp x)
                      (natp y)
                      (not (equal y 0))
                      (natp a))
          :output (+ a (floor x y))
          :code (ifeq (lessp x y)
                      (floor (- x y) y (+ a 1))
                      a))

   (low-seven :formals (x a)
              :dcls   ((declare (xargs :measure (acl2-count n))))
              :input (and (natp x)
                          (natp a))
              :output (low-seven! x a n)
              :output-arity 3
              :code (ifeq (- (mod x 10) 7)
                          (mv 1 x a)
                          (low-seven (floor x 10 0)
                                     (+ 1 a)))
              :ghost-formals (n)
              :ghost-base-test (zp n)
              :ghost-base-value (mv 0 x a)
              :ghost-decr ((- n 1)))

   (main :formals (x)
         :input (natp x)
         :output (low-seven! x 0 n)
         :output-arity 3
         :code (low-seven x 0)
         :ghost-formals (n)
         :ghost-base-value (mv 0 -1 -1))))

