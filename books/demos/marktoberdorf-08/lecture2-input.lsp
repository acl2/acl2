; This is the demo given in Lecture 2.

; cd to the marktoberdorf-08/scripts/ directory and then fire up ACL2

(set-guard-checking nil)

(set-gag-mode nil) ; to get full proof output, as in the original demo

(include-book "m1")

(in-package "M1")

(quote (end of setup))

(defun g (n a)
         (if (zp n)
             a
           (g (- n 1) (* n a))))

(defconst *g*
       '((PUSH 1)
         (STORE 1)
         (LOAD 0)
         (IFLE 10)
         (LOAD 0)
         (LOAD 1)
         (MUL)
         (STORE 1)
         (LOAD 0)
         (PUSH 1)
         (SUB)
         (STORE 0)
         (GOTO -10)
         (LOAD 1)
         (HALT)))

(defun g-sched-loop (n)
         (if (zp n)
             (repeat 0 4)
           (append (repeat 0 11)
                   (g-sched-loop (- n 1)))))

(defun g-sched (n)
         (append (repeat 0 2)
                 (g-sched-loop n)))

(defun run-g (n)
         (top
          (stack
           (run (g-sched n)
                (make-state 0
                            (list n 0)
                            nil
                            *g*)))))

(run-g 5)

(run-g 1000)

(len (g-sched 1000))

(quote (End of Demo 1))

(include-book "compile")

(compile '(n)               ; Factorial
             '((a = 1)
               (while (n > 0)
                 (a = (n * a))
                 (n = (n - 1)))
               (return a)))

(quote (End of Demo 2))

(quote (the end))
