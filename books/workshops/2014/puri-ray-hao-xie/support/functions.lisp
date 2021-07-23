(in-package "ACL2")
(include-book "ordinals/ordinals" :dir :system)

#||

functions.lisp
~~~~~~~~~~~~~~
Author: Disha Puri
Last Updated: 12th April 2014

This file provides the syntax of a CCDFG.  The syntax is
(now) based essentially on LLVM parse tree.  In particular, a
syntactically correct CCDFG is something that can be transformed
(after suitable translation) by an LLVM optimization.

||#

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Section 1: Auxillary Functions
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; printing to comment window
(defun eval-print (str val)
  (prog2$ (cw (string-append str " ~x0~%") val) val))

;; macro to skip proofs of theorems if needed
(defmacro defthms (&rest args)
  `(skip-proofs (defthm ,@args)))

(defun evaluate-val (val bindings)
  (if (symbolp val)
      (cdr (assoc-equal val bindings))
    val))

(defun mem (e x)
  (if (consp x)
      (if (equal e (car x))
          t
        (mem e (cdr x)))
    nil))

(defun not-in (a b)
  (if (endp a) t
    (if (not (mem (car a) b)) (not-in (cdr a) b)
      nil)))

;; get first n members of a list
(defun take-n (n l)
  (if (or (endp l)
          (zp n)) '()
    (append (list (car l))
            (take-n (- n 1) (cdr l)))))

;; get last n members of a list
(defun remove-n (n l)
  (if (or (endp l)
          (zp n)) l
    (remove-n (- n 1) (cdr l))))

(defun replace-var (var val lst)
  (if (endp lst) (acons var val lst)
    (if (not var) lst
      (if (equal var (caar lst))
          (acons var val (cdr lst))
        (if (symbol< (caar lst) var)
            (cons (car lst)
                  (replace-var var val (cdr lst)))
          (acons var val lst))))))

(defun substring (sub str start)
  (declare (xargs :measure (nfix (- (1+ (- (length str) (length sub))) start))))
  (if (or (not (natp start))
          (< (length str) (length sub))
          (> start (- (length str) (length sub))))
      nil
    (if (equal (subseq str start (+ start (length sub)))
               sub)
        start
      (substring sub str (1+ start)))))

;; to find if sub is a substring of str
(defun is-substring (sub str)
  (if (not (equal (substring sub str 0) nil))
      t
    nil))

(defun prefix-before-substring (sub str)
  (let ((pos (substring sub str 0)))
    (if (not pos)
        nil
      (subseq str 0 pos))))

(defun prefix (mstep)
  (prefix-before-substring "_" (symbol-name (car mstep))))

(defun variable-or-numberp (x)
  (or (symbolp x)
      (integerp x)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Section 2: Syntax of statements
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; We start with the definition of the grammar of a statement.  A
;; statement is a (1) branch statement, (2) return statement, (3)
;; store statement, or (4) assignment statement (5) phi-statements.  We assume
;; implicitly that the statements are in Single-Static-Assignment
;; (SSA) form.  But our grammar does not fully enforce SSA, only
;; exploits that understanding.

;; unconditional branch statement
;; (br  bb1  [from entry]))
(defun unconditional-branch-statement-p (x)
  (or (and (equal (len x) 4)
           (equal (first x) 'br)
           (variable-or-numberp (second x))
           (equal (third x) '[from)
           (symbolp (fourth x)))
      (and (equal (len x) 3)
           (equal (first x) 'br)
           (equal (second x) 'label)
           (variable-or-numberp (third x)))))

;; conditional branch statement
;; (br |%exitcond1| bb2 bb [from bb1])
(defun conditional-branch-statement-p (x)
  (and (equal (len x) 6)
       (equal (first x) 'br)
       (variable-or-numberp (second x))
       (symbolp (third x))
       (symbolp (fourth x))
       (equal (fifth x) '[from)
       (symbolp (sixth x))))

(defun branch-statement-p (x)
  (and (equal (len x) 1)
       (or (unconditional-branch-statement-p (car x))
           (conditional-branch-statement-p (car x)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; return statement
;; (ret void) or (ret a)
(defun return-statement-p (x)
  (and (equal (len x) 1)
       (and (equal (len (car x)) 2)
            (equal (first (car x)) 'ret)
            (or (equal (second (car x)) 'void)
                (and (second (car x))
                     (symbolp (second (car x))))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; store statement
;; store (store |%v0_1| |%v_addr| v)
(defun store-statement-p (x)
  (and (equal (len x) 1)
       (let ((a (car x)))
         (and (equal (len a) 4)
              (equal (first a) 'store)
              (variable-or-numberp (second a))
              (variable-or-numberp (third a))
              (symbolp (fourth a))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; An assignment statement is a bit more complex.  It has two parts.
;; The first part is a variable to be assigned.  The second part is an
;; expression.  Now what is an expression?  It can be an arithmetic
;; expression such as sub, icmp, igt, etc.  It can also be a load
;; expression.  We characterize each expression below.

;; load expression
;; (load |%v_addr|)
(defun load-expression-p (x)
  (and (consp x)
       (equal (len x) 2)
       (equal (first x) 'load)
       (variable-or-numberp (second x))))

;; (load_2 |%v_addr|)
(defun load2-expression-p (x)
  (and (consp x)
       (equal (len x) 2)
       (equal (first x) 'load_2)
       (variable-or-numberp (second x))))

;; (xor |%tmp6| |%tmp_9|)
(defun xor-expression-p (x)
  (and (equal (len x) 3)
       (equal (first x) 'xor)
       (variable-or-numberp (second x))
       (variable-or-numberp (third x))))

;; (lshr |%v0_2| 5)
(defun lshr-expression-p (x)
  (and (equal (len x) 3)
       (equal (first x) 'lshr)
       (variable-or-numberp (second x))
       (variable-or-numberp (third x))))


;; (add |%tmp| |%k0_read|)
(defun add-expression-p (x)
  (and (equal (len x) 3)
       (equal (first x) 'add)
       (variable-or-numberp (second x))
       (variable-or-numberp (third x))))


;; (shl |%tmp| 2)
(defun shl-expression-p (x)
  (and (equal (len x) 3)
       (equal (first x) 'shl)
       (variable-or-numberp (second x))
       (variable-or-numberp (third x))))

;; (eq |%tmp| |%k0_read|)
(defun eq-expression-p (x)
  (and (equal (len x) 3)
       (equal (first x) 'eq)
       (variable-or-numberp (second x))
       (variable-or-numberp (third x))))

;; added for simple assignment of symbols
;; (|%k0_read|)
(defun symbol-expression-p (x)
  (and (equal (len x) 1)
       (variable-or-numberp (first x))))

;; (getelementptr |%k0_read|)
(defun getelementptr-expression-p (x)
  (and (consp x)
       (equal (len x) 2)
       (equal (first x) 'getelementptr)
       (symbolp (second x))))

(defun expression-p (x)
  (and (consp x)
       (or (load-expression-p x)
           (load2-expression-p x)
           (add-expression-p x)
           (xor-expression-p x)
           (lshr-expression-p x)
           (shl-expression-p x)
           (eq-expression-p x)
           (symbol-expression-p x)
           (getelementptr-expression-p x))))

;; And an assignment statement has a variable on the left
;; and an expression on the right.
;; It is actually of the form ((a expr))
(defun assignment-statement-p (x)
  (and (equal (len x) 1)
       (and (equal (len (car x)) 2)
            (first (car x))
            (symbolp (first (car x)))
            (expression-p (second (car x))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; defining phi-expression

;; (|v0_1| bb)
(defun phi-a (x)
  (and (consp x)
       (equal (len x) 2)
       (variable-or-numberp (first x))
       (symbolp (second x))))

;; ((|v0_1| 'bb)(|v0_2| 'entry))
(defun phi-l (x)
  (if (endp x) t
    (and (phi-a (first x))
         (phi-l (rest x)))))

;; (phi ((|v0_1| 'bb)(|v0_2| 'entry)))
(defun phi-expression-p (x)
  (and (consp x)
       (= (len x) 1)
       (consp (car x))
       (> (len (car x)) 2)
       (equal (caar x) 'phi)
       (phi-l (cdr (car x)))))

;; phi-statement
(defun phi-statement-p (x)
  (and (consp x)
       (equal (len x) 2)
       (symbolp (first x))
       (first x)
       (phi-expression-p (cdr x))))

(defun phi-statements-aux-p (x)
  (if (endp x) t
    (and (consp x)
         (phi-statement-p (first x))
         (phi-statements-aux-p (rest x)))))

;; phi-construct
;((|%i| (phi  (|%i_1| bb) (0 entry)))
; (|%y| (phi  (|%x| bb) (0 entry)))))
(defun phi-statements-p (x)
  (and (consp x)
       (phi-statements-aux-p x)))

;; Now we can formalize what a statement is.
(defun statement-p (x)
  (or (branch-statement-p x)
      (return-statement-p x)
      (store-statement-p x)
      (phi-statements-p x)
      (assignment-statement-p x)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Section 3: Syntax of CCDFG
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun mstep-p (x)
  (and (symbolp (first x))
       (statement-p (cdr x))))

(defun msteps-list-p (x)
  (if (endp x)
      t
    (and (mstep-p (first x))
         (msteps-list-p (rest x)))))

(defun msteps-lists-list-p (x)
  (if (endp x)
      t
    (and (msteps-list-p (first x))
         (msteps-lists-list-p (rest x)))))

;; a basic block consists of a name and lists of (list of msteps)
(defun basic-block-p (x)
  (and (equal (len x) 2)
       (natp (first x))
       (msteps-lists-list-p (second x))))

(defun basic-block-list-p (x)
  (if (endp x)
      t
    (and (basic-block-p (first x))
         (basic-block-list-p (rest x)))))

;; a ccdfg is a list of three elements:  a prologue, loop and epilogue
(defun ccdfg-p (x)
  (and (basic-block-list-p (first x))
       (basic-block-list-p (second x))
       (basic-block-list-p (third x))))

;; when we only have the sequential CCDFG, prologue and epilogue are nil

;; after unrolling the loop once and replacing the phi statement, we have prologue
;; and loop, while epilogue is still nil
;; it is only after superstep construction step, we get the pipelined CCDFG with
;; three elements: prologue, loop and epilogue
(defun seq-ccdfg-p (x)
  (and (ccdfg-p x)
       (not (third x))
       (equal (cdr (first x))
              (cdr (second x)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Sections 4: Functions related to CCDFG
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun phi-restriction-list (x)
  (if (endp x) t
    (and (not (phi-statements-p (cdr (car x))))
         (phi-restriction-list (cdr x)))))

(defun phi-restriction-block (x)
  (if (endp x) t
    (and (phi-restriction-list (car x))
         (phi-restriction-block (cdr x)))))

;; block here is (()())
(defun phi-restriction-ccdfg (x)
  (if (endp x) t
    (and (phi-restriction-block (cadr (car x)))
         (phi-restriction-ccdfg (cdr x)))))

;; a CCDFG with no phi-construct
(defun phi-restriction (x)
  (and (phi-restriction-ccdfg (first x))
       (phi-restriction-ccdfg (second x))
       (phi-restriction-ccdfg (third x))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun branch-restriction-list (x)
  (if (endp x) t
    (and (not (branch-statement-p (cdr (car x))))
         (branch-restriction-list (cdr x)))))

(defun branch-restriction-block (x)
  (if (endp x) t
    (and (branch-restriction-list (car x))
         (branch-restriction-block (cdr x)))))

(defun branch-restriction-ccdfg (x)
  (if (endp x) t
    (and (branch-restriction-block (cadr (car x)))
         (branch-restriction-ccdfg (cdr x)))))

;; a CCDFG with no branch-statements
(defun branch-restriction (x)
  (and (branch-restriction-ccdfg (first x))
       (branch-restriction-ccdfg (second x))
       (branch-restriction-ccdfg (third x))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Section 5: variable read and written in msteps
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; functions to find write-list of mstep
(defun remove-nils (lst)
  (if (endp lst) lst
    (if (equal (car lst) nil) (remove-nils (cdr lst))
      (append (list (car lst))
              (remove-nils (cdr lst))))))

(defun get-write-phi (stmts)
  (if (endp stmts) '()
    (append (list (caar stmts))
            (get-write-phi (cdr stmts)))))

;; state consists of
;; bindings (list of tuples of variables with their values
;; mem (mem with values at particular addresses)
;; ptrs (lists of tuples of ptr name with its value

(defun write-list-stmt (stmt)
  (if (endp stmt) '()
    (cond ((branch-statement-p stmt) '())
          ((return-statement-p stmt) '())
          ((store-statement-p stmt) '())
          ((assignment-statement-p stmt) (list (caar stmt)))
          ((phi-statements-p stmt) (get-write-phi stmt))
          (t nil))))

(defun write-from-bindings (mstep)
  (remove-nils (write-list-stmt (cdr mstep))))

(defun write-list-msteps (msteps)
  (if (endp msteps) '()
    (append (write-from-bindings (car msteps))
            (write-list-msteps (cdr msteps)))))

(defun write-from-ptrs (mstep)
  (if (store-statement-p (cdr mstep))
      (list (fourth (cadr mstep)))
    nil))

(defun writel (mstep)
  (append (write-from-bindings mstep)
          (write-from-ptrs mstep)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; functions to find read-list of mstep
(defun eval-symbol (val)
  (if (symbolp val) val
    nil))

(defun find-read-phi (expr)
  (if (endp expr) nil
    (append (list (eval-symbol (car (car expr))))
            (find-read-phi (cdr expr)))))

(defun find-read-phi-s (stmt)
  (if (endp stmt) '()
    (append (find-read-phi (cdr (second (car stmt))))
            (find-read-phi-s (cdr stmt)))))

(defun find-read (expr)
  (if (endp expr) nil
    (cond ((load-expression-p expr) (list (cadr expr)))
          ((load2-expression-p expr)  (list (cadr expr)))
          ((add-expression-p expr) (list (eval-symbol (cadr expr))
                                         (eval-symbol (caddr expr))))
          ((xor-expression-p expr) (list (eval-symbol (cadr expr))
                                         (eval-symbol (caddr expr))))
          ((lshr-expression-p expr) (list (eval-symbol (cadr expr))
                                          (eval-symbol (caddr expr))))
          ((shl-expression-p expr) (list (eval-symbol (cadr expr))
                                         (eval-symbol (caddr expr))))
          ((eq-expression-p expr) (list (eval-symbol (cadr expr))
                                        (eval-symbol (caddr expr))))
          ((symbol-expression-p expr) (list (eval-symbol (car expr))))
          ((getelementptr-expression-p expr) '())
          (t nil))))

(defun read-list-stmt (stmt)
  (cond ((return-statement-p stmt)
         (list (nth 1 (car stmt))))
        ((assignment-statement-p stmt)
         (find-read (nth 1 (car stmt))))
        ((store-statement-p stmt)
         (list (nth 1 (car stmt)) (nth 2 (car stmt))))
        ((conditional-branch-statement-p (car stmt))
         (list (nth 1 (car stmt))))
        ((phi-statements-p stmt)
         (find-read-phi-s stmt))
        (t nil)))

(defun read-from-bindings (mstep)
  (remove-nils (read-list-stmt (cdr mstep))))

(defun read-from-ptrs (mstep)
  (cond ((and (assignment-statement-p (cdr mstep))
              (getelementptr-expression-p (cadadr mstep)))
         (list (eval-symbol (cadr (cadadr mstep)))))
        ((store-statement-p (cdr mstep))
         (list (fourth (cadr mstep))))
        (t nil)))

(defun readl (mstep)
  (append (read-from-bindings mstep)
          (read-from-ptrs mstep)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Section 6: combining iterations in parallel
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun get-msteps-block (block)
  (if (endp block) '()
    (append (list (car block))
            (get-msteps-block (cdr block)))))

(defun get-msteps-blocks (blocks)
  (if (endp blocks) '()
    (append (get-msteps-block (car blocks))
            (get-msteps-blocks (cdr blocks)))))

(defun get-msteps (ccdfg)
  (if (endp ccdfg) '()
    (append (get-msteps-blocks (cadr (car ccdfg)))
            (get-msteps (cdr ccdfg)))))

(defun all-read (msteps)
  (if (endp msteps) '()
    (append (readl (car msteps))
            (all-read (cdr msteps)))))

(defun all-write (msteps)
  (if (endp msteps) '()
    (append (writel (car msteps))
            (all-write (cdr msteps)))))

(defun no-conflict (c1 c2)
  (if (and (not-in (all-read (get-msteps c1))
                   (all-write (get-msteps c2)))
           (not-in (all-write (get-msteps c1))
                   (all-read (get-msteps c2)))
           (not-in (all-write (get-msteps c1))
                   (all-write (get-msteps c2))))
      t
    nil))

;; here block is a ccdfg in itself, just it has one block
;; (combine-blocks (x ((a) (b) (c))) (y ((a) (b) (C))) 1)
(defun combine-blocks (new-ccdfg block pos)
  (if (equal new-ccdfg nil) block
    (if (no-conflict block (remove-n (+ pos 1) new-ccdfg))
        (append (take-n pos new-ccdfg)
                (list (list (car (nth pos new-ccdfg))
                            (append (cadr (nth pos new-ccdfg))
                                    (cadr (car block)))))
                (remove-n (+ 1 pos) new-ccdfg))
      "error")))

(defun combine-iters (new-ccdfg new-iter pos)
  (declare (xargs :measure (acl2-count new-iter)))
  (if (or (endp new-iter)
          (equal new-ccdfg "error")) new-ccdfg
    (combine-iters (combine-blocks new-ccdfg
                                   (list (car new-iter))
                                   pos)
                   (cdr new-iter)
                   (+ pos 1))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Example for testing
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defconst *seq-ccdfg*
  '(
    ((1(((bb1_@@_4       (|%exitcond1| (eq |%i| 10000)))
         (bb1_@@_5       (|%i_1| (add |%i| 00001)))
         (bb_@@_0        (|%exitcond1| (true))))))
     (2(((bb_@@_1        (|%tmp| (shl |%v1_1| 4)))
         (bb_@@_2        (|%tmp_1| (add |%tmp| |%k0_read|)))
         (bb_@@_3        (|%tmp_2| (lshr |%v1_1| 5)))
         (bb_@@_4        (|%tmp_3| (add |%tmp_2| |%k1_read|)))
         (bb_@@_5        (|%tmp4| (add |%v1_1| |%next_mul|))))))
     (3(((bb_@@_6        (|%tmp5| (xor |%tmp_3| |%tmp4|)))
         (bb_@@_7        (|%tmp_5| (xor |%tmp5| |%tmp_1|)))
         (bb_@@_8       (|%v0_2| (add |%tmp_5| |%v0_1|)))
         (bb_@@_9       (|%tmp_6| (shl |%v0_2| 4)))
         (bb_@@_10       (|%tmp_7| (add |%tmp_6| |%k2_read|)))
         (bb_@@_11       (|%tmp_8| (lshr |%v0_2| 5)))))))
    ((1(((bb1_@@_4       (|%exitcond1| (eq |%i| 10000)))
         (bb1_@@_5       (|%i_1| (add |%i| 00001)))
         (bb_@@_0        (|%exitcond1| (true))))))
     (2(((bb_@@_1        (|%tmp| (shl |%v1_1| 4)))
         (bb_@@_2        (|%tmp_1| (add |%tmp| |%k0_read|)))
         (bb_@@_3        (|%tmp_2| (lshr |%v1_1| 5)))
         (bb_@@_4        (|%tmp_3| (add |%tmp_2| |%k1_read|)))
         (bb_@@_5        (|%tmp4| (add |%v1_1| |%next_mul|))))))
     (3(((bb_@@_6        (|%tmp5| (xor |%tmp_3| |%tmp4|)))
         (bb_@@_7        (|%tmp_5| (xor |%tmp5| |%tmp_1|)))
         (bb_@@_8       (|%v0_2| (add |%tmp_5| |%v0_1|)))
         (bb_@@_9       (|%tmp_6| (shl |%v0_2| 4)))
         (bb_@@_10       (|%tmp_7| (add |%tmp_6| |%k2_read|)))
         (bb_@@_11       (|%tmp_8| (lshr |%v0_2| 5)))))))
    ))
;;;;;;;;;;;;;;;;;; End of File "functions.lisp" ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
