#||

semantics.lisp
~~~~~~~~~~~~~~
Author: Disha Puri
Last Updated: 12th April 2014

This file provides the semantics of CCDFG. It specifies what it
means to execute a CCDFG. This can be viewed as providing an
interpreter semantics to a parse tree.

The syntax and semantics together provide a way to write a program in
terms of a graph and allow classical logic to manipulate and reason
about that graph-based program.

||#

(in-package "ACL2")
(include-book "functions")


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Section 1: Execute a statement in a CCDFG
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; execute-store statement
(defun append-pos (val pos heap)
  (if (or (not (integerp val))
          (< val 0)
          (not (integerp pos))
          (< pos 0)) heap
    (if (equal pos 0) (append (list val) (cdr heap))
      (append (list (car heap))
              (append-pos val (1- pos) (cdr heap))))))

;; stmt is  store value address v
(defun execute-store (stmt init-state)
  (let* ((val (evaluate-val (second stmt) (car init-state)))
         (addr (evaluate-val (third stmt) (car init-state)))
         (heap (evaluate-val (fourth stmt) (third init-state))))
    (if (or (not (integerp addr))
            (< addr 0)
            (not (integerp val))
            (< val 0))
        init-state
      (list (car init-state) (second init-state)
            (replace-var (fourth stmt)
                         (append-pos val addr heap)
                         (third init-state))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Now execution of assignment statement.
;; This really is in two parts.  First we will need to evaluate the
;; expression and then we will do an assignment of the appropriate
;; variable to extend the mapping.

(defun evaluate-load (expr mem bindings)
  (let* ((addr (evaluate-val (second expr) bindings)))
    (if (or (not (integerp addr))
            (< addr 0)
            (>= addr (- (len mem) 2))) nil
      (nth addr (cdr mem)))))

(defun evaluate-load2 (expr mem bindings)
  (let* ((addr (evaluate-val (second expr) bindings)))
    (if (or (not (integerp addr))
            (< addr 0)
            (>= addr (- (len mem) 2))) nil
      (nth addr (cdr mem)))))

(defun evaluate-add (expr bindings)
  (let ((op1 (evaluate-val (second expr) bindings))
        (op2 (evaluate-val (third expr) bindings)))
    (if (and (acl2-numberp op1)
             (acl2-numberp op2))
        (+ op1 op2)
      nil)))

(defun evaluate-xor (expr bindings)
  (let* ((op1 (evaluate-val (second expr) bindings))
         (op2 (evaluate-val (third expr) bindings)))
    (let ((res (xor (if (equal op1 0) nil  t)
                    (if (equal op2 0) nil t))))
      (if (equal (or op1 op2) nil) nil
        (if res 1 0)))))

(defun evaluate-lshr (expr bindings)
  (let ((op1 (evaluate-val (second expr) bindings))
        (op2 (evaluate-val (third expr) bindings)))
    (if (and (integerp op1)
             (integerp op2))
        (ash op1 op2)
      nil)))

(defun evaluate-shl (expr bindings)
  (let* ((op1 (evaluate-val (second expr) bindings))
         (op2 (evaluate-val (third expr) bindings)))
    (if (and (integerp op1)
             (integerp op2))
        (ash op1 (- 0 op2))
      nil)))

(defun evaluate-symbol (expr bindings)
  (let ((op (evaluate-val (first expr) bindings)))
    op))

(defun evaluate-eq (expr bindings)
  (let ((op1 (evaluate-val (second expr) bindings))
        (op2 (evaluate-val (third expr) bindings)))
    (if (equal op1 op2) 1
      0)))

(defun evaluate-ptr (expr ptrs)
  (let ((op (nth 0 (evaluate-val (second expr) ptrs))))
    op))

(defun execute-assignment (stmt init-state)
  (let*
      ((expr (second stmt))
       (var (first stmt))
       (val
        (cond
         ((load-expression-p expr) (evaluate-load expr (second init-state) (car init-state)))
         ((load2-expression-p expr) (evaluate-load2 expr (second init-state) (car init-state)))
         ((add-expression-p expr) (evaluate-add expr (car init-state)))
         ((xor-expression-p expr) (evaluate-xor expr (car init-state)))
         ((shl-expression-p expr) (evaluate-shl expr (car init-state)))
         ((lshr-expression-p expr) (evaluate-lshr expr (car init-state)))
         ((eq-expression-p expr) (evaluate-eq expr (car init-state)))
         ((getelementptr-expression-p expr) (evaluate-ptr expr (third init-state)))
         ((symbol-expression-p expr) (evaluate-symbol expr (car init-state)))
         (t (er hard 'evaluate-assignment "wrong expression ~p0~%" expr)))))
    (list (replace-var var val (car init-state)) (second init-state) (third init-state))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; phi-construct

(defun choose (choices prev-bb)
  (if (or (equal (nth 1 (first choices)) prev-bb)
          (equal (symbol-name (nth 1 (first choices))) prev-bb))
      (nth 0 (first choices))
    (nth 0 (second choices))))

;;one stmt is (|%v0_1| (phi  (|%v0_2| bb) (|%v0| entry)))
(defun execute-phi (stmt init-state prev-bb)
  (let*
      ((expr (cdr stmt))
       (var (first stmt))
       (val
        (cond
         ((phi-expression-p expr) (evaluate-val (choose (cdr (car expr)) prev-bb) (car init-state)))
         (t (er hard 'evaluate-phi "wrong expression ~p0~%" expr)))))
    (list (replace-var var val (car init-state)) (second init-state) (third init-state))))

(defun execute-phi-s (stmts init-state prev-bb)
  (if (or (endp stmts)
          (not (consp stmts))) init-state
    (execute-phi-s (cdr stmts)
                   (execute-phi (car stmts)
                                init-state
                                prev-bb)
                   prev-bb)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; while executing a CCDFG, we give special treatement to phi and branch statements,
;; for others we do execute-statement
;; so we have branch, assignment and store
;; we keep phi separate as it is not used once phi-construct is removed
;; we keep branch separate as it changes the control flow
(defun execute-statement (stmt init-state)
  (cond ((branch-statement-p stmt) init-state)
        ((store-statement-p stmt) (execute-store (car stmt) init-state))
        ((assignment-statement-p stmt) (execute-assignment (car stmt) init-state))
        (t init-state)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; br bb1 [from entry]
(defun get-next-block-uncond (stmt init-state)
  (declare (ignore init-state))
  (second stmt))

;; A conditional branch statement has a condition label and two
;; targets (based on the value of the source).
;; condition is either true or false
(defun get-next-block-cond (stmt init-state)
  (let* ((condition (evaluate-val (second stmt) (car init-state)))
         (tgt (third stmt))
         (ft (fourth stmt)))
    (if (equal condition 1)
        tgt
      ft)))

;; gives the name of the next basic block by evaluating the branch statement
(defun get-next-bb (stmt init-state)
  (if (unconditional-branch-statement-p stmt)
      (get-next-block-uncond stmt init-state)
    (get-next-block-cond stmt init-state)))

;; finds the next steps in same list of msteps from where to start executing if encounter a branch
(defun next-to-execute (msteps bb)
  (if (endp msteps) nil
    (if (equal (prefix (car msteps))
               (prefix bb))
        msteps
      (next-to-execute (cdr msteps) bb))))

;; if there is no branch statement in the block, next block is the one in order
;; if there is a branch which has been used within the block, then too
;; else next block is found by get-next-bb
(defun get-next-lists (l init-state)
  (if (endp l) nil
    (if (not (branch-statement-p (cdr (car l))))
        (get-next-lists (cdr l) init-state)
      (if (equal (next-to-execute (cdr l) (get-next-bb (cadr (car l)) init-state)) nil)
          (get-next-bb (cadr (car l)) init-state)
        nil))))

(defun get-next-block (block init-state)
  (if (endp block) nil
    (if (equal (get-next-block (cdr block) (get-next-lists (car block) init-state)) nil)
        (get-next-lists (car block) init-state)
      nil)))

;; if branch-statement, go to next stmt with the next bb if in the same block
;; for everything else, execute-statement and go to next one
;; when you run a block, we go in order unless there is a branch
;; a block is a list of msteps

;; b = (x y z)
(defun run-lists (msteps init-state next prev)
  (if (endp msteps) init-state
    (if (or (equal next nil)
            (equal next (prefix (car msteps))))
        (if (branch-statement-p (cdr (car msteps)))
            (run-lists (next-to-execute (cdr msteps) (get-next-bb (cadr (car msteps)) init-state))
                       init-state
                       nil
                       prev)
          (if (phi-statements-p (cdar msteps))
              (run-lists (cdr msteps) (execute-phi-s (cdar msteps) init-state prev) nil prev)
            (run-lists (cdr msteps) (execute-statement (cdar msteps) init-state) nil prev)))
      (run-lists (cdr msteps) init-state next prev))))

;; b = (()()())
(defun run-block (b init-state next prev)
  (if (endp b) init-state
    (run-block (cdr b) (run-lists (car b) init-state next
                                  prev)
               (get-next-block b init-state)
               prev)))

;; run a set of blocks, c here is equivalent to a list of basic blocks
;; (cadar c) = ((a) (b) (c))
;; first statement is (caar (cadar c))
;; if next is nil or next is equal to prefix of first statement, then execute the first statement
(defun run-block-set (c init-state next-bb prev)
  (if (endp c) init-state
    (run-block-set (cdr c) (run-block (cadar c) init-state next-bb prev)
                   (get-next-block (cadar c) init-state)
                   prev)))

;; run the entire loop block set for certian number of iterations
;; c = ((name1 ((a)(b)(c))) (name2 (()()())))
(defun run-blocks-iters (c init-state iter prev)
  (if (zp iter) init-state
    (run-blocks-iters c (run-block-set c init-state nil prev) (- iter 1) prev)))

;; Because we want loop to be iterated a certain number of types,
;; I have divided run a ccdfg into run-pre, run-loop and run-post
;; run-ccdfg-k means run-pre, then run-loop for k iterations
(defun run-ccdfg-k (pre loop iterations init-state prev)
  (let* ((state1 (run-block-set pre init-state nil prev))
         (state2 (run-blocks-iters loop state1 iterations
                                   (prefix (car (last (cadar (last loop))))))))
    state2))

;; run-pre, then run-loop for k iterations, then run-post
(defun run-ccdfg (pre loop post iterations init-state prev)
  (let* ((state1 (run-block-set pre init-state nil prev))
         (state2 (run-blocks-iters loop state1 iterations
                                   (prefix (car (last (cadar (last loop)))))))
         (state3 (run-block-set post state2 nil
                                (prefix (car (last (cadar (last post))))))))
    state3))
