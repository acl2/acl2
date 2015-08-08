(in-package "ACL2")
(set-match-free-default :all)

#| example1.lisp

We present a simple example to demonstrate the use of the fair environment in
fair1.lisp in proving a liveness property using the fair environment assumption
provided in fair1.lisp. The example in this file is a trivial "system", but
demonstrates the key concepts in using the fair input assumption environment in
fair1.lisp to prove a simple liveness property. The key idea is to use the
fair-measure to define a terminating measure for a function which is the
witness to proving the liveness property. This approach requires the addition
of the (fair-selection) assumption which is an unfortunate need. Since usage
of the fair2.lisp file does not require this assumption, we generally believe
the user should use the fair2.lisp book instead (as in example2.lisp).

|#

(include-book "fair1")

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
  (cond ((not (fair-selection)) 0)
        ((not (natp n)) (good-time 0))
        ((good (run n)) n)
        (t (good-time (1+ n)))))

(in-theory (disable good (good-time)))

(defthm good-of-good-time
  (implies (fair-selection)
           (good (run (good-time n)))))

(defthm good-time->=
  (implies (and (integerp n)
                (fair-selection))
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
  (implies (fair-selection)
           (eventually-good n))
  :hints (("Goal" :use (:instance eventually-good-suff
                                  (x n)
                                  (y (good-time n))))))



