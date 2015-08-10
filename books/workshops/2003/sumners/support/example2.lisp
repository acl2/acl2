(in-package "ACL2")
(set-match-free-default :all)

#| example2.lisp

We present a simple example to demonstrate the use of the fair environment in
fair2.lisp in proving a liveness property using the fair environment assumption
provided in fair2.lisp. The example in this file is a trivial "system", but
demonstrates the key concepts in using the fair input assumption environment in
fair.lisp to prove a simple liveness property. The key idea is to use the
fair-measure to define a terminating measure for a function which is the
witness to proving the liveness property. It is the author's belief (with some
applications supporting this belief) that for most systems, the forms from the
defun of good-time on could be re-used for any liveness proof with little or no
modification and that the only item needed to be changed for a particular
system would be the measure for the function good-time.

A more thorough (but complicated) demonstration of this is found in
example3.lisp.

|#

(include-book "fair2")

;; the following macro defines the functions env and env-measure

(define-env)

(encapsulate (((upper-bound) => *))
  (local (defun upper-bound () 1))
  (defthm upper-bound-positive-natural
    (and (integerp (upper-bound))
         (> (upper-bound) 0))
    :rule-classes :type-prescription))

(defun sys-step (s i)
  (let ((s (if (= s i) (1+ s) s)))
    (if (<= s (upper-bound)) s 0)))

(defun sys-init () 0)

(defun run (n)
  (if (zp n) (sys-init)
    (let ((n (1- n)))
      (sys-step (run n) (env n)))))

(defthm run-n-is-natural
  (natp (run n))
  :rule-classes :type-prescription)

(defthm run-n-is-bounded
  (<= (run n) (upper-bound))
  :rule-classes :linear)

(defun good (s)
  (= s (upper-bound)))

(defmacro lexprod (&rest r)
  (cond ((endp r) 0)
        ((endp (rest r)) (first r))
        (t `(cons (lexprod ,@(butlast r 1))
                  ,(car (last r))))))

(defun good-measure (n)
  (lexprod
   (if (natp n) 1 2)
   (1+ (nfix (- (upper-bound) (run n))))
   (env-measure (run n) n)))

(in-theory (disable (good-measure)))

;; the following is just a rewrite rule we need from linear arithmetic (which
;; does not "rewrite")
(local
 (defthm linear-factoid3
   (implies (and (integerp x)
                 (integerp y))
            (equal (+ (- y) y x) x))))

(defun good-time (n)
  (declare (xargs :measure (good-measure n)))
  (cond ((not (natp n)) (good-time 0))
        ((good (run n)) n)
        (t (good-time (1+ n)))))

(in-theory (disable good (good-time)))

(defthm good-of-good-time
  (good (run (good-time n))))

(defthm good-time->=
  (implies (integerp n)
           (>= (good-time n) n))
  :rule-classes :linear)

(defthm good-time-is-natp
  (natp (good-time n))
  :rule-classes :type-prescription)

(defun time>= (y x)
  (and (natp y) (implies (natp x) (>= y x))))

(defun-sk eventually-good (x)
  (exists (y) (and (time>= y x) (good (run y)))))

(defthm progress-or-liveness
  (eventually-good n)
  :hints (("Goal" :use (:instance eventually-good-suff
                                  (x n)
                                  (y (good-time n))))))



