; This is the demo given in Lecture 3.

; cd to the marktoberdorf-08/scripts/ directory and then fire up ACL2

(set-guard-checking nil)

(set-gag-mode nil) ; to get full proof output, as in the original demo

(include-book "m1")
(include-book "compile")

(in-package "M1")

(defun f (n)
         (if (zp n)
             1
           (* n (f (- n 1)))))

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
         (RETURN)))

(defun g-sched-loop (n)
  (if (zp n)
      (repeat 0 4)
    (append (repeat 0 11)
            (g-sched-loop (- n 1)))))

(defun g-sched (n)
  (append (repeat 0 2)
          (g-sched-loop n)))


(quote (end of setup))

; Fails but checkpoint is the whole point:
(thm
       (equal (run (repeat 0 9)
                   (make-state 4
                               (list n a)
                               stk
                               *g*))
              ???))

(quote (End of Demo 1))

(thm (equal (run (append a b) s)
                 (run b (run a s)))

        :hints (("Goal" :in-theory (disable run-append))))



(quote (End of Demo 2))

(defthm step-1-[loop]
         (implies (and (natp n)
                       (natp a))
                  (equal (run (g-sched-loop n)
                              (make-state 2
                                          (list n a)
                                          stk
                                          *g*))
                         (make-state 14
                                     (list 0 (g n a))
                                     (push (g n a) stk)
                                     *g*))))

(quote (End of Demo 3))

(defthm step-1
         (implies (natp n)
                  (equal (run (g-sched n)
                              (make-state 0
                                          (list n a)
                                          stk
                                          *g*))
                         (make-state 14
                                     (list 0 (g n 1))
                                     (push (g n 1) stk)
                                     *g*))))

(in-theory (disable g-sched))

(quote (End of Demo 4))

(defthm step-2
         (implies (natp a)
                  (equal (g n a)
                         (* a (f n)))))

(defthm main
  (implies (natp n)
           (equal (run (g-sched n)
                       (make-state 0
                                   (list n a)
                                   stk
                                   *g*))
                  (make-state 14
                              (list 0 (f n))
                              (push (f n) stk)
                              *g*))))


(defthm corollary1
         (let ((s_fin (run (g-sched n)
                           (make-state 0
                                       (list n a)
                                       stk
                                       *g*))))
           (implies (natp n)
                    (and (equal (top (stack s_fin))
                                (f n))
                         (haltedp s_fin)))))

(defthm corollary2
         (let ((s_fin (run (g-sched n)
                           (make-state 0
                                       (list n a)
                                       stk
                                       (compile
                                        '(n)
                                        '((a = 1)
                                          (while (n > 0)
                                            (a = (n * a))
                                            (n = (n - 1)))
                                          (return a)))))))
           (implies (natp n)
                    (and (equal (top (stack s_fin))
                                (f n))
                         (haltedp s_fin)))))

(quote (End of Demo 5))

(quote (The End))
