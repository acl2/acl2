(in-package "ACL2")

#|

 measures.lisp
 ~~~~~~~~~~~~~

In this book, I prove an alternative theorem for fast symbolic simulation to
prove total correctness. This set of constraint guanrantees that the theorem
|some cutpoint is reachable| that I wrote for the total correctness theorem can
be proved via symbolic simulation based on next-cutpoint. I keep it here as
opposed to the original book since I treat the original book as specifying the
actual total correctness theorem and this book is merely a subsidiary for fast
symbolic simulation. This book will be made use of in the defsimulate macro.

|#

(include-book "misc/defpun" :dir :system)
(include-book "ordinals/ordinals" :dir :system)

(defstub nextt (*) => *)
(defun run (s n) (if (zp n) s (run (nextt s) (1- n))))

(encapsulate
 (((default-state) => *)
  ((cutpoint *) => *)
  ((assertion *) => *)
  ((exitpoint *) => *))

 (local (defun default-state () nil))
 (local (defun cutpoint (s) (not (equal s nil))))
 (local (defun assertion (s) (declare (ignore s)) t))
 (local (defun exitpoint (s) (declare (ignore s)) t))

 (defpun steps-to-cutpoint-tail (s i)
  (if (cutpoint s)
      i
    (steps-to-cutpoint-tail (nextt s) (1+ i))))

 (defun steps-to-cutpoint (s)
   (let ((steps (steps-to-cutpoint-tail s 0)))
     (if (cutpoint (run s steps))
         steps
       (omega))))

  (defun nextt-cutpoint (s)
   (let ((steps (steps-to-cutpoint s)))
     (if (natp steps)
         (run s steps)
       (default-state))))



  ;; Notice that I specify the constraint that some cutpoint is reachable, but
  ;; do it via the nextt-cutpoint expressions.

  (defthm |default state is not cutpoint|
    (equal (cutpoint (default-state)) nil))

    (defthm |some cutpoint reachable via nextt|
      (implies (and (cutpoint s)
                    (assertion s)
                 (not (exitpoint s)))
            (cutpoint (nextt-cutpoint (nextt s))))))


(local
 (defun cutpoint-induction (k steps s)
   (if (zp k) (list k steps s)
     (cutpoint-induction (1- k) (1+ steps) (nextt s)))))

(local
 ;; [Jared] changed this to use arithmetic-3 instead of 2
 (include-book "arithmetic-3/bind-free/top" :dir :system))

;; The following theorem is proven by induction and is about everything that we
;; need to know about steps-to-cutpoint-tail.

(local
 (defthmd steps-to-cutpoint-tail-inv
   (implies (and (cutpoint (run s k))
                 (natp steps))
            (let* ((result  (steps-to-cutpoint-tail s steps))
                   (cutpoint-steps (- result steps)))
              (and (natp result)
                   (natp cutpoint-steps)
                   (implies (natp k)
                            (<= cutpoint-steps k))
                   (cutpoint (run s cutpoint-steps)))))
   :hints (("Goal"
            :in-theory (enable natp)
            :induct (cutpoint-induction k steps s)))))


;; Now I know that if some cutpoint is reachable then steps-to-cutpoint is a
;; natp.

(local
 (defthm steps-to-cutpoint-is-natp
   (implies (cutpoint (run s k))
            (natp (steps-to-cutpoint s)))
   :hints (("Goal"
            :use ((:instance steps-to-cutpoint-tail-inv
                             (steps 0)))))))

;; This theorem basically rewrites (steps-to-cutpoint s) to (omega) when it is
;; not a natp. And I know that when it is (omega) nextt-cutpoint is going to
;; give me default state which is of course not a cutpoint. Thus the theorem
;; will be proved.

(local
 (defthm steps-to-cutpoint-natp-or-ordinal
   (implies (not (natp (steps-to-cutpoint s)))
            (equal (steps-to-cutpoint s) (omega)))))

(local
 (in-theory (disable steps-to-cutpoint)))

(defthm |some cutpoint is reachable|
  (implies (and (cutpoint s)
                (assertion s)
                (not (exitpoint s)))
           (natp (steps-to-cutpoint (nextt s))))
  :otf-flg t
  :hints (("Goal"
           :in-theory (disable |some cutpoint reachable via nextt|
                               steps-to-cutpoint-is-natp)
           :use ((:instance steps-to-cutpoint-is-natp
                            (s (nextt s))
                            (k (1- (steps-to-cutpoint s))))
                 (:instance |some cutpoint reachable via nextt|)))))
