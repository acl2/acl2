; This file contains all the material prepared for the preliminary paper,
; main.pdf

#|
(defpkg  "M1"
  (set-difference-equal
   (union-eq '(defp measure l< delta preprocess fast-loop fast correct-loop correct
                pairlis-x2)
         (union-eq *common-lisp-symbols-from-main-lisp-package*
                   *acl2-exports*))
   '(PC PROGRAM ID PUSH POP STEP COMPILE)))

(certify-book "preliminary-material" 1)
jsm
|#

(in-package "M1")

(defun fact (n)
  (if (zp n)
      1
      (* n (fact (- n 1)))))

(defthm nth-nil
  (equal (nth n nil) nil))

(defthm acl2-count-nth
  (implies (consp x)
           (< (acl2-count (nth n x))
              (acl2-count x)))
  :rule-classes :linear)

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

(defconst *ifact-program*

;    M1              M1      JVM    JVM            Java
;    code            pc       pc   bytecode

 '((PUSH 1)     ;   0         0   bipush_1 
   (STORE 1)    ;   1         1   istore_1      a = 1;
   (LOAD 0)     ;   2         2   iload_0       while (n>0){
   (IFLE 10)    ;   3         3   ifle    17
   (LOAD 0)     ;   4         6   iload_0
   (LOAD 1)     ;   5         7   iload_1  
   (MUL)        ;   6         8   imul      
   (STORE 1)    ;   7         9   istore_1        a = n*a;
   (LOAD 0)     ;   8        10   iload_0  
   (PUSH 1)     ;   9        11   bipush_1 
   (SUB)        ;  10        12   isub      
   (STORE 0)    ;  11        13   istore_0        n = n-1;
   (GOTO -10)   ;  12        14   goto    2       }
   (LOAD 1)     ;  13        17   iload_1
   (RETURN)     ;  14        18   ireturn        return a;  
   ))

(defun repeat (th n)
     (if (zp n)
         nil
       (cons th (repeat th (- n 1)))))

(defun ifact-loop-sched (n)
  (if (zp n)
      (repeat 0 4)
    (append (repeat 0 11)
            (ifact-loop-sched (- n 1)))))

(defun ifact-sched (n)
  (append (repeat 0 2)
          (ifact-loop-sched n)))

(defthm factorial-5-example
  (equal (top
          (stack
           (run
            (ifact-sched 5)
            (make-state
             0
             '(5 0)
             nil
             *ifact-program*))))
         (fact 5))
  :rule-classes nil)

(defun collect-at-end (x e)
  (if (member e x)
      x
    (append x (cons e nil))))

(defun collect-vars-in-expr (vars expr)
  (if (atom expr)
      (if (symbolp expr)
          (collect-at-end vars expr)
        vars)
    (collect-vars-in-expr
     (collect-vars-in-expr vars
                           (nth 0 expr))
     (nth 2 expr))))

(mutual-recursion

 (defun collect-vars-in-stmt* (vars stmt-list)
   (if (endp stmt-list)
       vars
     (collect-vars-in-stmt*
      (collect-vars-in-stmt vars (car stmt-list))
      (cdr stmt-list))))

 (defun collect-vars-in-stmt (vars stmt)
   (if (equal (nth 1 stmt) '=)
       (collect-vars-in-expr
        (collect-at-end vars (nth 0 stmt))
        (nth 2 stmt))
     (if (equal (nth 0 stmt) 'WHILE)
         (collect-vars-in-stmt*
          (collect-vars-in-expr vars (nth 1 stmt))
          (cdr (cdr stmt)))
       (if (equal (nth 0 stmt) 'RETURN)
           (collect-vars-in-expr vars (nth 1 stmt))
         vars))))
)

(defun index (vars var)
  (if (endp vars)
      0
    (if (equal var (car vars))
        0
      (+ 1 (index (cdr vars) var)))))

(defun OP! (op)
  (if (equal op '+)
      '((ADD))
    (if (equal op '-)
        '((SUB))
      (if (equal op '*)
          '((MUL))
        '((ILLEGAL))))))

(defun LOAD! (vars var)
  (cons (cons 'LOAD (cons (index vars var) nil))
        nil))

(defun PUSH! (n)
  (cons (cons 'PUSH (cons n nil))
        nil))

(defun expr! (vars expr)
  (if (atom expr)
      (if (symbolp expr)
          (LOAD! vars expr)
        (PUSH! expr))
    (append (expr! vars (nth 0 expr))
            (append (expr! vars (nth 2 expr))
                    (OP! (nth 1 expr))))))

(defun IFLE! (offset)
  (cons (cons 'IFLE (cons offset nil))
        nil))

(defun GOTO! (offset)
  (cons (cons 'GOTO (cons offset nil))
        nil))

(defun while! (test-code body-code)
  (append test-code
          (append (IFLE! (+ 2 (len body-code)))
                  (append body-code
                          (GOTO! (- (+ (len test-code)
                                       1
                                       (len body-code))))))))

(defun test! (vars test)
  (if (equal (nth 1 test) '>)
      (if (equal (nth 2 test) 0)
          (expr! vars (nth 0 test))
        (append (expr! vars (nth 0 test))
                (append (expr! vars (nth 2 test))
                        '((SUB)))))
    '((ILLEGAL))))

(defun STORE! (vars var)
  (cons (cons 'STORE (cons (index vars var) nil))
        nil))

(mutual-recursion

 (defun stmt*! (vars stmt-list)
   (if (endp stmt-list)
       nil
     (append (stmt! vars (car stmt-list))
             (stmt*! vars (cdr stmt-list)))))

 (defun stmt! (vars stmt)
   (if (equal (nth 1 stmt) '=)
       (append (expr! vars (nth 2 stmt))
               (STORE! vars (nth 0 stmt)))
     (if (equal (nth 0 stmt) 'WHILE)
         (while!
          (test! vars (nth 1 stmt))
          (stmt*! vars (cdr (cdr stmt))))
       (if (equal (nth 0 stmt) 'RETURN)
           (append (expr! vars (nth 1 stmt))
                   '((RETURN)))
         '((ILLEGAL))))))
 )

(defun compile (formals stmt-list)
  (stmt*! (collect-vars-in-stmt* formals stmt-list)
          stmt-list))

(defthm example-compilation-1
  (equal (compile '(n)
                  '((a = 1)
                    (while (n > 0)
                      (a = (n * a))
                      (n = (n - 1)))
                    (return a)))
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
  :rule-classes nil)

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

(defun ifact (n a)
  (if (zp n)
      a
    (ifact (- n 1) (* n a))))

(defthm ifact-loop-lemma
  (implies (and (natp n)
                (natp a))
           (equal (run (ifact-loop-sched n)
                       (make-state 2
                                   (cons n (cons a nil))
                                   stack
                                   *ifact-program*))
                  (make-state 14
                              (cons 0 (cons (ifact n a) nil))
                              (push (ifact n a) stack)
                              *ifact-program*))))

(defthm ifact-lemma
  (implies (natp n)
           (equal (run (ifact-sched n)
                       (make-state 0
                                   (cons n (cons a nil))
                                   stack
                                   *ifact-program*))
                  (make-state 14
                              (cons 0 (cons (ifact n 1) nil))
                              (push (ifact n 1) stack)
                              *ifact-program*))))

(in-theory (disable ifact-sched))

(defthm ifact-is-factorial
  (implies (and (natp n)
                (natp a))
           (equal (ifact n a)
                  (* (fact n) a))))

(defthm ifact-correct
  (implies (natp n)
           (equal (run (ifact-sched n)
                       (make-state 0
                                   (cons n (cons a nil)) 
                                   stack
                                   *ifact-program*))
                  (make-state 14
                              (cons 0 (cons (fact n) nil))
                              (push (fact n) stack)
                              *ifact-program*))))

(defthm ifact-correct-corollary-1
  (implies (natp n)
           (haltedp (run (ifact-sched n)
                         (make-state 0
                                     (cons n (cons a nil))
                                     stack
                                     *ifact-program*)))))

(defthm ifact-correct-corollary-2
  (implies (natp n)
           (equal (top
                   (stack
                    (run (ifact-sched n)
                         (make-state 0
                                     (cons n (cons a nil))
                                     stack
                                     *ifact-program*))))
                  (fact n))))

(defthm ifact-correct-corollary-3
  (implies (natp n)
           (equal (top
                   (stack
                    (run (ifact-sched n)
                         (make-state 0
                                     (cons n (cons a nil))
                                     stack
                                     (compile
                                      '(n)
                                      '((a = 1)
                                        (while (n > 0)
                                          (a = (n * a))
                                          (n = (n - 1)))
                                        (return a)))))))
                  (fact n))))

(include-book "misc/defp" :dir :system)

(defmacro defspec (name prog inputs pre-pc post-pc annotation-alist)
  (let ((Inv
         (intern-in-package-of-symbol
          (concatenate 'string (symbol-name name) "-INV")
          'run))
        (Inv-def
         (intern-in-package-of-symbol
          (concatenate 'string (symbol-name name) "-INV$DEF")
          'run))
        (Inv-opener
         (intern-in-package-of-symbol
          (concatenate 'string (symbol-name name) "-INV-OPENER")
          'run))
        (Inv-step
         (intern-in-package-of-symbol
          (concatenate 'string (symbol-name name) "-INV-STEP")
          'run))
        (Inv-run
         (intern-in-package-of-symbol
          (concatenate 'string (symbol-name name) "-INV-RUN")
          'run))
        (Correctness
         (intern-in-package-of-symbol
          (concatenate 'string "PARTIAL-CORRECTNESS-OF-PROGRAM-"
                       (symbol-name name))
          'run)))
    `(progn
       (defp ,Inv (,@inputs s)
         (if (member (pc s)
                     ',(strip-cars annotation-alist))
             (and (equal (program s)
                         ,prog)
                  (case (pc s)
                    ,@annotation-alist))
           (,Inv ,@inputs (step s))))
       (defthm ,Inv-opener
         (implies (and (equal pc (pc s))
                       (syntaxp (quotep pc))
                       (not
                        (member pc
                                ',(strip-cars annotation-alist))))
                  (equal (,Inv ,@inputs s)
                         (,Inv ,@inputs (step s)))))
       (defthm ,Inv-step
         (implies (,Inv ,@inputs s)
                  (,Inv ,@inputs (step s))))
       (defthm ,Inv-run
         (implies (,Inv ,@inputs s)
                  (,Inv ,@inputs (run sched s)))
         :rule-classes nil
         :hints (("Goal" :in-theory (e/d (run)(,Inv-def)))))
       (defthm ,Correctness
         (let* ((sk (run sched s0)))
           (implies
            (and (let ((s s0)) ,(cadr (assoc pre-pc annotation-alist)))
                 (equal (pc s0) ,pre-pc)
                 (equal (locals s0) (list* ,@inputs any))
                 (equal (program s0) ,prog)
                 (equal (pc sk) ,post-pc))
            (let ((s sk)) ,(cadr (assoc post-pc annotation-alist)))))

         :hints (("Goal" :use
                  (:instance ,Inv-run
                             ,@(pairlis$ inputs (pairlis-x2 inputs nil))
                             (s s0)
                             (sched sched))))
         :rule-classes nil))))

(defun n (s) (nth 0 (locals s)))
(defun a (s) (nth 1 (locals s)))

(defspec ifact *ifact-program* (n0 a0) 0 14
  ((0 (and (equal n0 (n s))
           (natp n0)))
   (2 (and (natp n0)
           (natp (n s))
           (natp (a s))
           (<= (n s) n0)
           (equal (fact n0) (* (fact (n s)) (a s)))))
   (14 (equal (top (stack s)) (fact n0)))))

(defthm partial-correctness-of-program-ifact-corrollary
  (implies (and (natp n0)
                (equal (pc s0) 0)
                (equal (locals s0)
                       (cons n0 (cons a0 nil)))
                (equal (program s0) *ifact-program*)
                (equal sk (run sched s0))
                (equal (pc sk) 14))
           (equal (top (stack sk))
                  (fact n0)))

  :hints (("goal" :use (:instance partial-correctness-of-program-ifact
                                  (n0 n0)
                                  (a0 a0)
                                  (sched sched)
                                  (any nil))))
  :rule-classes nil)


(include-book "fast")

(defconst *m1-boyer-moore-program*

; Allocation of locals

; pat   0 
; j     1
; txt   2
; i     3
; pmax  4 = (length pat)
; tmax  5 = (length txt)
; array 6 = (preprocess pat)
; c     7 = temp - last char read from txt

  '(

    (load 0)        ;  0    (load pat)
    (push "")       ;  1    (push "")
    (ifane 5)       ;  2    (ifane loop)        ; if pat/="", goto loop
    (load 2)        ;  3    (load txt)
    (push "")       ;  4    (push "")
    (ifane 40)      ;  5    (ifane win)         ; if txt/="", goto win
    (goto 43)       ;  6    (goto lose)         
; loop:             
    (load 1)        ;  7    (load j)     
    (iflt 37)       ;  8    (iflt win))         ; if j<0, goto win
    (load 5)        ;  9    (load tmax)  
    (load 3)        ; 10    (load i)     
    (sub)           ; 11    (sub)        
    (ifle 37)       ; 12    (ifle lose)         ; if (length txt)-i <= 0, goto lose
    (load 0)        ; 13    (load pat)   
    (load 1)        ; 14    (load j)     
    (aload)         ; 15    (aload)             ; pat[j]
    (load 2)        ; 16    (load txt)   
    (load 3)        ; 17    (load i)     
    (aload)         ; 18    (aload)             ; txt[i]
    (store 7)       ; 19    (store v)           ; (store into v)
    (load 7)        ; 20    (load v)     
    (sub)           ; 21    (sub)        
    (ifne 10)       ; 22    (ifne skip)         ; if pat[j] /= txt[i], goto skip
    (load 1)        ; 23    (load j)     
    (push 1)        ; 24    (push 1)    
    (sub)           ; 25    (sub)        
    (store 1)       ; 26    (store j)           ; j=j-1
    (load 3)        ; 27    (load i)     
    (push 1)        ; 28    (push 1)    
    (sub)           ; 29    (sub)        
    (store 3)       ; 30    (store i)           ; i=i-1
    (goto -24)      ; 31    (goto loop)         ; goto loop
; skip:
    (load 3)        ; 32    (load i)     
    (load 6)        ; 33    (load array)       
    (load 7)        ; 34    (load v)     
    (aload)         ; 35    (aload)      
    (load 1)        ; 36    (load j)     
    (aload)         ; 37    (aload)      
    (add)           ; 38    (add)
    (store 3)       ; 39    (store i)           ; i := i+array[c][j]
    (load 4)        ; 40    (load pmax)  
    (push 1)        ; 41    (push 1)    
    (sub)           ; 42    (sub)
    (store 1)       ; 43    (store j)           ; j := (length pat)-1
    (goto -37)      ; 44    (goto loop)   
; win:
    (load 3)        ; 45    (load i)     
    (push 1)        ; 46    (push 1)    
    (add)           ; 47    (add)        
    (return)        ; 48    (return)     
; lose:
    (push nil)      ; 49    (push nil) 
    (return) )      ; 50    (return))
  )

(in-theory (enable char length))

(defun m1-boyer-moore-loop-sched (pat j txt i)
  (declare (xargs :measure (measure pat j txt i)
                  :well-founded-relation l<))
  (cond
   ((not (and (stringp pat) (integerp j)
              (stringp txt) (integerp i)
              (<= -1 j) (< j (length pat))
              (<= j i)))
    nil)
   ((< j 0)
    (repeat 0 6))
   ((<= (length txt) i)
    (repeat 0 8))
   ((equal (char-code (char pat j)) (char-code (char txt i)))
    (append (repeat 0 25)
            (m1-boyer-moore-loop-sched pat (- j 1) txt (- i 1))))
   (t (append (repeat 0 29)
              (m1-boyer-moore-loop-sched pat
                                         (- (length pat) 1)
                                         txt
                                         (+ i (delta (char txt i)
                                                     j
                                                     pat)))))))

(defun m1-boyer-moore-sched (pat txt)
  (if (equal pat "")
      (if (equal txt "")
          (repeat 0 9)
        (repeat 0 10))
    (append (repeat 0 3)
            (m1-boyer-moore-loop-sched pat 
                                       (- (length pat) 1)
                                       txt
                                       (- (length pat) 1)))))
(defun m1-boyer-moore-loop-vars (pat j txt i v)
  (declare (xargs :measure (measure pat j txt i)
                  :well-founded-relation l<))
  (cond
   ((not (and (stringp pat) (integerp j)
              (stringp txt) (integerp i)
              (<= -1 j) (< j (length pat))
              (<= j i)))
    (list j i v))
   ((< j 0)
    (list j i v))
   ((<= (length txt) i)
    (list j i v))
   ((equal (char-code (char pat j)) (char-code (char txt i)))
    (m1-boyer-moore-loop-vars
     pat
     (- j 1)
     txt
     (- i 1)
     (char-code (char txt i))))
   (t (m1-boyer-moore-loop-vars
       pat
       (- (length pat) 1)
       txt
       (+ i (delta (char txt i)
                   j
                   pat))
       (char-code (char txt i))))))

(defthm m1-boyer-moore-loop-is-fast-loop
  (implies (and (stringp pat)
                (stringp txt)
                (integerp j)
                (<= -1 j)
                (< j (length pat))
                (integerp i)
                (<= j i))
           (equal (run (m1-boyer-moore-loop-sched pat j txt i)
                       (make-state 7
                                   (list pat
                                         j
                                         txt
                                         i
                                         (length pat)
                                         (length txt)
                                         (preprocess pat)
                                         v)
                                   nil
                                   *m1-boyer-moore-program*))
                  (if (fast-loop pat j txt i)
                      (make-state 48
                                  (list pat
                                        (nth 0 (m1-boyer-moore-loop-vars pat j txt i v))
                                        txt
                                        (nth 1 (m1-boyer-moore-loop-vars pat j txt i v))
                                        (length pat)
                                        (length txt)
                                        (preprocess pat)
                                        (nth 2 (m1-boyer-moore-loop-vars pat j txt i v)))
                                  (push (fast-loop pat j txt i) nil)
                                  *m1-boyer-moore-program*)
                    (make-state 50
                                (list pat
                                      (nth 0 (m1-boyer-moore-loop-vars pat j txt i v))
                                      txt
                                      (nth 1 (m1-boyer-moore-loop-vars pat j txt i v))
                                      (length pat)
                                      (length txt)
                                      (preprocess pat)
                                      (nth 2 (m1-boyer-moore-loop-vars pat j txt i v)))
                                (push nil nil)
                                *m1-boyer-moore-program*))))
  :hints (("Goal" :in-theory (enable preprocess))))

(in-theory (disable length))

(defthm m1-boyer-moore-is-fast
  (implies (and (stringp pat)
                (stringp txt))
           (equal (top
                   (stack
                    (run (m1-boyer-moore-sched pat txt)
                         (make-state 0
                                     (list pat
                                           (- (length pat) 1)
                                           txt
                                           (- (length pat) 1)
                                           (length pat)
                                           (length txt)
                                           (preprocess pat)
                                           0)
                                     nil
                                     *m1-boyer-moore-program*))))
                  (fast pat txt))))

(defthm m1-boyer-moore-halts
  (implies (and (stringp pat)
                (stringp txt))
           (haltedp
            (run (m1-boyer-moore-sched pat txt)
                 (make-state 0
                             (list pat
                                   (- (length pat) 1)
                                   txt
                                   (- (length pat) 1)
                                   (length pat)
                                   (length txt)
                                   (preprocess pat)
                                   0)
                             nil
                             *m1-boyer-moore-program*)))))

(defthm m1-boyer-moore-is-correct
  (implies (and (stringp pat)
                (stringp txt))
           (equal (top
                   (stack
                    (run (m1-boyer-moore-sched pat txt)
                         (make-state 0
                                     (list pat
                                           (- (length pat) 1)
                                           txt
                                           (- (length pat) 1)
                                           (length pat)
                                           (length txt)
                                           (preprocess pat)
                                           0)
                                     nil
                                     *m1-boyer-moore-program*))))
                  (correct pat txt))))




; Appendix:  A Universal Program?

(defconst *universal-program*
  '((PUSH 0)
    (PUSH 1)
    (ADD)
    (GOTO -2)))

(defun universal-sched-loop (k)
  (if (zp k)
      nil
    (append (repeat 0 3)
            (universal-sched-loop (- k 1)))))

(defun universal-sched (k)
  (append (repeat 0 1)
          (universal-sched-loop k)))

(defun induct-hint (k stack)
  (if (zp k)
      stack
    (induct-hint (- k 1)
                 (push (+ 1 (top stack))
                       (pop stack)))))

(defun universal-algorithm (k n)
  (if (zp k)
      n
    (universal-algorithm (- k 1) (+ 1 n))))

(defthm step-a-run-universal-loop
  (implies (and (natp k)
                (natp n))
           (equal (run (universal-sched-loop k)
                       (make-state 1
                                   locals
                                   (push n stack)
                                   *universal-program*))
                  (make-state 1
                              locals
                              (push (universal-algorithm k n)
                                    stack)
                              *universal-program*))))

(defthm step-a-run-universal
  (implies (natp k)
           (equal (run (universal-sched k)
                       (make-state 0
                                   locals
                                   stack
                                   *universal-program*))
                  (make-state 1
                              locals
                              (push (universal-algorithm k 0)
                                    stack)
                              *universal-program*))))

(defthm step-b
  (implies (and (natp k)
                (natp n))
           (equal (universal-algorithm k n) (+ k n))))

(defun new-fact-sched (n)
  (universal-sched (fact n)))

(defthm universal-computes-fact
  (equal (top
          (stack
           (run (new-fact-sched n)
                (make-state 0
                            locals
                            stack
                            *universal-program*))))
         (fact n)))


(defthm universal-never-halts-lemma
  (implies (and (member (pc s) '(0 1 2 3))
                (equal (program s) *universal-program*))
           (not (haltedp (run sched s)))))


(defthm universal-never-halts
  (not
   (haltedp
    (run sched
         (make-state 0
                     locals
                     stack
                     *universal-program*)))))

