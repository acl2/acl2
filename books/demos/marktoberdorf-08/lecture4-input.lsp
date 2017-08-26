; This is the demo given in Lecture 4.

; cd to the marktoberdorf-08/scripts/ directory and then fire up ACL2

(set-guard-checking nil)

(set-gag-mode nil) ; to get full proof output, as in the original demo

(include-book "m1")

(include-book "misc/defpun" :dir :system)

(in-package "M1")

(defmacro defpun (g args &rest tail)
  `(acl2::defpun ,g ,args ,@tail))

(defmacro defspec (name prog inputs pre-pc post-pc annotation-alist)
  (let ((Inv
         (intern-in-package-of-symbol
          (concatenate 'string (symbol-name name) "-INV")
          'run))
        (Inv-def
         (intern-in-package-of-symbol
          (concatenate 'string (symbol-name name) "-INV-DEF")
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
       (defpun ,Inv (,@inputs s)
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
                             ,@(pairlis$ inputs (acl2::pairlis-x2 inputs nil))
                             (s s0)
                             (sched sched))))
         :rule-classes nil))))


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

(quote (end of setup))

(defun n (s) (nth 0 (locals s)))

(defun a (s) (nth 1 (locals s)))

(defspec g *g* (n0 a0) 0 14
     ((0                             ; Pre-condition
         (and (equal n0 (n s))
              (natp n0)))

      (2                             ; Loop Invariant
         (and (natp n0)
              (natp (n s))
              (natp (nth 1 (locals s)))
              (<= (n s) n0)
              (equal (f n0) (* (f (n s)) (a s)))))

      (14                            ; Post-condition
          (equal (top (stack s)) (f n0)))))

(defthm corollary
       (let ((sk (run sched s0)))
         (implies (and (equal n0 (n s0))
                       (natp n0)
                       (equal (pc s0) 0)
                       (equal (locals s0) (list* n0 a0 any))
                       (equal (program s0) *g*)
                       (equal (pc sk) 14))
                  (equal (top (stack sk))
                         (f n0))))

       :hints (("Goal" :use PARTIAL-CORRECTNESS-OF-PROGRAM-G)))

(quote (End of Demo 1))

(defconst *h*

;    public static int half(int n){
;	int a = 0;
;	while (n!=0){a=a+1;n=n-2;};
;	return a;
;    }

  '((push 0)    ;  0
    (store 1)   ;  1
    (goto 9)    ;  2
    (load 1)    ;  3
    (push 1)    ;  4
    (add)       ;  5
    (store 1)   ;  6
    (load 0)    ;  7
    (push 2)    ;  8
    (sub)       ;  9
    (store 0)   ; 10
    (load 0)    ; 11
    (ifne -9)   ; 12
    (load 1)    ; 13
    (return))   ; 14
  )

(defun run-h (n)
  (run (repeat 0 10000)
       (make-state 0
                   (list n 0)
                   nil
                   *h*)))

(run-h 216)
(run-h 215)

(defspec h *h*  (n0) 0 14
       (; Pre-Condition:
        (0 (and (equal (n s) n0)
                (natp n0)))

        ; Loop Invariant:
        (11 (and (natp n0)
                 (integerp (n s))
                 (if (and (natp (a s))
                          (evenp (n s)))
                     (equal (+ (a s) (/ (n s) 2))
                            (/ n0 2))
                   (not (evenp (n s))))
                 (iff (evenp n0) (evenp (n s)))))

        ; Post-condition:
        (14 (and (evenp n0)
                 (equal (top (stack s)) (/ n0 2))))))

(defthm h-corollary
     (implies (and (natp (n s0))
                   (equal (pc s0) 0)
                   (equal (program s0) *h*)
                   (equal sk (run sched s0))
                   (equal (pc sk) 14))
              (and (evenp (n s0))
                   (equal (top (stack sk)) (/ (n s0) 2))))

     :hints
     (("Goal"
       :use (:instance PARTIAL-CORRECTNESS-OF-PROGRAM-H
                       (n0 (n s0))
                       (any (cdr (locals s0)))
                       ))))

(quote (End of Demo 2))
(quote (The End))


