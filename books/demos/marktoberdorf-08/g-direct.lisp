; (include-book "m1")
; (certify-book "g-direct" 1)

(in-package "M1")

(defun f (n)
         (if (zp n)
             1
           (* n (f (- n 1)))))

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

(defun g (n a)
         (if (zp n)
             a
           (g (- n 1) (* n a))))

(defun run-g (n)
         (top
          (stack
           (run (g-sched n)
                (make-state 0
                            (list n 0)
                            nil
                            *g*)))))

; (run-g 5)
; (run-g 1000)

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

(defthm corollary
         (let ((s_fin (run (g-sched n)
                           (make-state 0
                                       (list n a)
                                       stk
                                       *g*))))
           (implies (natp n)
                    (and (equal (top (stack s_fin))
                                (f n))
                         (haltedp s_fin)))))
