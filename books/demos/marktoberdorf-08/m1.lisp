; (ld "m1-package.lsp")
; (ld "m1.lisp" :ld-pre-eval-print t)
; (certify-book "m1" 1)
; jsm

(in-package "M1")

(defun push (obj stack) (cons obj stack))
(defun top (stack) (car stack))
(defun pop (stack) (cdr stack))

(defun opcode (inst) (nth 0 inst))
(defun arg1 (inst) (nth 1 inst))
(defun arg2 (inst) (nth 2 inst))
(defun arg3 (inst) (nth 3 inst))

(defun make-state (pc locals stack program)
     (cons pc
           (cons locals
                 (cons stack
                       (cons program
                             nil)))))

(defun pc (s) (nth 0 s))
(defun locals (s) (nth 1 s))
(defun stack (s) (nth 2 s))
(defun program (s) (nth 3 s))

(defun next-inst (s) (nth (pc s) (program s)))

(defun execute-PUSH (inst s)
  (make-state (+ 1 (pc s))
              (locals s)
              (push (arg1 inst) (stack s))
              (program s)))

(defun execute-LOAD (inst s)
  (make-state (+ 1 (pc s))
              (locals s)
              (push (nth (arg1 inst)
                         (locals s))
                    (stack s))
              (program s)))

(defun execute-ADD (inst s)
  (declare (ignore inst))
  (make-state (+ 1 (pc s))
              (locals s)
              (push (+ (top (pop (stack s)))
                       (top (stack s)))
                    (pop (pop (stack s))))
              (program s)))

(defun execute-STORE (inst s)
  (make-state (+ 1 (pc s))
              (update-nth (arg1 inst) (top (stack s)) (locals s))
              (pop (stack s))
              (program s)))

(defun execute-SUB (inst s)
  (declare (ignore inst))
  (make-state (+ 1 (pc s))
              (locals s)
              (push (- (top (pop (stack s)))
                       (top (stack s)))
                    (pop (pop (stack s))))
              (program s)))

(defun execute-MUL (inst s)
  (declare (ignore inst))
  (make-state (+ 1 (pc s))
              (locals s)
              (push (* (top (pop (stack s)))
                       (top (stack s)))
                    (pop (pop (stack s))))
              (program s)))

(defun execute-GOTO (inst s)
  (make-state (+ (arg1 inst) (pc s))
              (locals s)
              (stack s)
              (program s)))

(defun execute-IFLE (inst s)
  (make-state (if (<= (top (stack s)) 0)
                  (+ (arg1 inst) (pc s))
                (+ 1 (pc s)))
              (locals s)
              (pop (stack s))
              (program s)))

; Boyer-Moore instructions

(defun execute-IFLT (inst s)
  (make-state (if (< (top (stack s)) 0)
                  (+ (arg1 inst) (pc s))
                (+ 1 (pc s)))
              (locals s)
              (pop (stack s))
              (program s)))

(defun execute-IFNE (inst s)
  (make-state (if (not (equal (top (stack s)) 0))
                  (+ (arg1 inst) (pc s))
                (+ 1 (pc s)))
              (locals s)
              (pop (stack s))
              (program s)))

(defun execute-IFANE (inst s)
  (make-state (if (not (equal (top (pop (stack s)))
                              (top (stack s))))
                  (+ (arg1 inst) (pc s))
                (+ 1 (pc s)))
              (locals s)
              (pop (pop (stack s)))
              (program s)))

(defun execute-ALOAD (inst s)
  (declare (ignore inst))
  (make-state (+ 1 (pc s))
              (locals s)
              (push (if (stringp (top (pop (stack s))))
                        (char-code (char (top (pop (stack s)))
                                         (top (stack s))))
                      (nth (top (stack s))
                           (top (pop (stack s)))))
                    (pop (pop (stack s))))
              (program s)))

(defun do-inst (inst s)
  (if (equal (opcode inst) 'PUSH)
      (execute-PUSH  inst s)
    (if (equal (opcode inst) 'LOAD)
        (execute-LOAD  inst s)
      (if (equal (opcode inst) 'STORE)
          (execute-STORE  inst s)
        (if (equal (opcode inst) 'ADD)
            (execute-ADD   inst s)
          (if (equal (opcode inst) 'SUB)
              (execute-SUB   inst s)
            (if (equal (opcode inst) 'MUL)
                (execute-MUL   inst s)
              (if (equal (opcode inst) 'GOTO)
                  (execute-GOTO   inst s)
                (if (equal (opcode inst) 'IFLE)
                    (execute-IFLE   inst s)
                  (if (equal (opcode inst) 'IFLT)
                      (execute-IFLT   inst s)
                    (if (equal (opcode inst) 'IFNE)
                        (execute-IFNE   inst s)
                      (if (equal (opcode inst) 'IFANE)
                          (execute-IFANE  inst s)
                        (if (equal (opcode inst) 'ALOAD)
                            (execute-ALOAD   inst s)
                          s)))))))))))))

(defun step (s)
  (do-inst (next-inst s) s))

(defun haltedp (s)
  (equal s (step s)))

(defun run (sched s)
  (if (endp sched)
      s
    (run (cdr sched) (step s))))

(defun repeat (th n)
     (if (zp n)
         nil
       (cons th (repeat th (- n 1)))))

(include-book "arithmetic/top-with-meta" :dir :system)

(defthm stacks
  (and (equal (top (push x s)) x)
       (equal (pop (push x s)) s)

       (equal (top (cons x s)) x)
       (equal (pop (cons x s)) s)))

(in-theory (disable push top pop))

(defthm states
  (and (equal (pc (make-state pc locals stack program)) pc)
       (equal (locals
               (make-state pc locals stack program))
              locals)
       (equal (stack
               (make-state pc locals stack program))
              stack)
       (equal (program
               (make-state pc locals stack program))
              program)

       (equal (pc (cons pc x)) pc)
       (equal (locals (cons pc (cons locals x))) locals)
       (equal (stack
               (cons pc (cons locals (cons stack x))))
              stack)
       (equal (program
               (cons pc 
                (cons locals (cons stack (cons program x)))))
              program)))

(in-theory (disable make-state pc locals stack program))

(defthm step-opener
  (implies (consp (next-inst s))
           (equal (step s)
                  (do-inst (next-inst s) s))))

(in-theory (disable step))

(defthm run-opener
  (and (equal (run nil s) s)
       (equal (run (cons th sched) s)
              (run sched (step s)))))

(defthm run-append
  (equal (run (append a b) s)
         (run b (run a s))))

(defthm nth-add1!
  (implies (natp n)
           (equal (nth (+ 1 n) list)
                  (nth n (cdr list)))))

(defthm update-nth-add1!
  (implies (natp n)
           (equal (update-nth (+ 1 n) v x)
                  (cons (car x) (update-nth n v (cdr x))))))

