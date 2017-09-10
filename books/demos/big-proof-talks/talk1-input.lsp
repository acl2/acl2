; Formalizing Machine Semantics and Proving Code Correct
; (with ACL2)
; J Strother Moore

; Start up ACL2 and do:

(set-gag-mode nil)

(set-irrelevant-formals-ok t)

; --- cut here ---

(+ 2 3)

(cons 'monday (cons 'tuesday (cons 'wednesday nil)))

(include-book "models/jvm/m1/m1" :dir :system)

(in-package "M1")

(defun sq (x) (* x x))

(sq 7)

(defun ^ (i j)
       (if (zp j)
           1
           (* i (^ i (- j 1)))))

(^ 2 5)

(thm (implies (and (natp i) (natp j) (natp k))
                   (equal (^ i (+ j k))
			  (* (^ i j) (^ i k)))))

(quote (end of demo 1))

(defconst *p*

; Register numbers: 0, 1, 2
; My names:         i, j, k

       '((ILOAD 1)   ; 0
         (IFEQ 10)   ; 1  if j=0, goto 1+10
         (ILOAD 0)   ; 2
         (ILOAD 2)   ; 3
         (IMUL)      ; 4
         (ISTORE 2)  ; 5  k := i*k;
         (ILOAD 1)   ; 6
         (ICONST -1) ; 7
         (IADD)      ; 8
         (ISTORE 1)  ; 9  j := j-1
         (GOTO -10)  ;10  goto 10-10
         (ILOAD 2)   ;11
         (HALT))     ;12  ``return'' k
       )

(defun ms (i j k)
       (make-state 0            ; program counter
		   (list i j k) ; registers
		   nil          ; stack
		   *p*          ; program
		   ))

(top (stack (m1 (ms 2 5 1) 1000)))

(top (stack (m1 (ms 2 64 1) 1000)))

(^ 2 64)

(defun clk (i j k)
       (if (zp j)
           3
           (clk+ 11
                 (clk i (- j 1) (* i k)))))

(clk 2 5 1)
(clk 2 1000 1)

(top (stack (m1 (ms 2 1000 1) (clk 2 1000 1))))

(defthm code-is-correct
       (implies (and (natp i)
                     (natp j)
                     (natp k))
                (equal (m1 (ms i j k) (clk i j k))
                       (make-state 12
                                   (list i 0 (* k (^ i j)))
                                   (push (* k (^ i j)) nil)
                                   *p*))))

(defthm corr
       (implies (and (natp i)
                     (natp j)
                     (natp k))
                (let ((fin-st (m1 (ms i j k) (clk i j k))))
                  (and (haltedp fin-st)
                       (equal (top (stack fin-st))
                              (* k (^ i j)))))))


(quote (demo of symbolic execuation))

(defthm this-is-not-a-theorem
      (implies (and (natp i)
                    (natp j)
                    (natp k))
               (equal (m1 (ms i j k) 11) xxx)))

(quote (end of demo 2))

