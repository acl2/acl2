(in-package "ACL2")

#||

  memory-clearning.lisp
  ~~~~~~~~~~~~~~~~~~~~~

  Author: Sandip Ray

In this book, we show that a machine that looks somewhat more
reasonable also satisfies the spurious notion of correctness for any
definition of modify.

||#

(defun factorial (n)
  (if (zp n) 1 (* n (factorial (1- n)))))

(defun program-component (s) (first s))
(defun pcnt (s) (second s))
(defun mem (s) (third s))

(defun update-mem (s val)
  (update-nth 2 val s))

(defun next (s)
  (update-mem s nil))

(defun halted (s)
  (equal s (next s)))

;; the precondition says that memory location 3 contains a natural number.

(defun pre (s)
  (natp (nth 3 (mem s))))

;; The modify says that we modify memory location 4 with factorial of
;; memory location 3.

(defun modify (s)
  (update-mem
   s
   (update-nth 4 (factorial (nth 3 (mem s))) (mem s))))


(include-book "misc/defpun" :dir :system)

(defpun stepw (s)
  (if (halted s) s
    (stepw (next s))))

(defun == (x y)
  (equal (stepw x) (stepw y)))

(local
 (defthm update-nth-update-nth
   (equal (update-nth i u (update-nth i v s))
          (update-nth i u s))))

(local
 (defthm next-is-halted
   (halted (next s))))

(local
 (defthm pre-is-not-halted
   (implies (pre s) (not (halted s)))))

(local
 (defthm next-of-modify
   (equal (next (modify s))
          (next s))))

(local
 (in-theory (disable next modify)))

(defthm partial-correctness
  (implies (pre s)
           (== s (modify s)))
  :hints (("Goal"
           :use ((:instance stepw-def)))))


