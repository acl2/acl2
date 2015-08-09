(in-package "ACL2")

;; This book is an initial (incomplete) attempt to define a simulator generator
;; which uses the records and inline books to achieve through mbe, a fast
;; (local-stobj-based) run function under-the-hood, while having a much nicer
;; function composition in the logic.

;; This is *NOT* intended to be an efficient simulator, but instead a
;; demonstration of how to compose efficient uses of mbe to get something even
;; faster. I do think an appropriate extension of this simulator generator could
;; be done and the code here should be viewed as an oversimplified sketch of how
;; it could be done.

(defun symbol-binary-append (x y)
  (declare (xargs :guard (and (symbolp x) (symbolp y))))
  (intern (string-append (symbol-name x) (symbol-name y)) "ACL2"))

(defmacro symbol-append (symb &rest symbs)
  (if (endp symbs) symb
    `(symbol-binary-append ,symb (symbol-append ,@symbs))))

(defun get-fn (var) (symbol-append 'r- var))
(defun set-fn (var) (symbol-append 'update-r- var))
(defun next-var (var) (symbol-append 'next-val- var))

(defun get-fns (vars)
  (if (endp vars) () (cons (get-fn (first vars)) (get-fns (rest vars)))))

(defun reg-vars (regs)
  (if (endp regs) () (cons (first (first regs)) (reg-vars (rest regs)))))

(defun var-binds (vars)
  (if (endp vars) ()
    (let ((var (first vars)))
      (cons `(,var (,var (1- n))) (var-binds (rest vars))))))

(defun logic-fn (reg init nxt vars)
  `(defun ,reg (n) (if (zp n) ,init (let ,(var-binds vars) ,nxt))))

(defun logic-fns (regs vars)
  (if (endp regs) ()
    (cons (logic-fn (first (first regs))
                    (second (first regs))
                    (third (first regs))
                    vars)
          (logic-fns (rest regs) vars))))

(defun sv-binds (vars)
  (if (endp vars) ()
    (cons (list (first vars)
                (list (get-fn (first vars)) 'sv))
          (sv-binds (rest vars)))))

(defun sv-nexts (regs)
  (if (endp regs) ()
    (cons (list (next-var (first (first regs)))
                (third (first regs)))
          (sv-nexts (rest regs)))))

(defun sv-updates (vars)
  (if (endp vars) ()
    (cons (list 'sv
                (list (set-fn (first vars))
                      (next-var (first vars))
                      'sv))
          (sv-updates (rest vars)))))

(defun inv-unr (vars)
  (if (endp vars) ()
    (cons `(equal (,(get-fn (first vars)) sv) (,(first vars) n))
          (inv-unr (rest vars)))))

(defun lgc-fncls (vars)
  (if (endp vars) ()
    (cons (list (first vars) 'n) (lgc-fncls (rest vars)))))

(defun var-nils (vars)
  (if (endp vars) () (cons nil (var-nils (rest vars)))))

(defun get-fncls (vars)
  (if (endp vars) ()
    (cons (list (get-fn (first vars)) 'sv)
          (get-fncls (rest vars)))))

(defun init-upds (regs)
  (if (endp regs) ()
    (cons (list 'sv (list (set-fn (first (first regs)))
                          (second (first regs))
                          'sv))
          (init-upds (rest regs)))))

(defun open-init-thms (regs)
  (if (endp regs) ()
    (cons `(defthm ,(symbol-append 'open-init- (first (first regs)))
             (implies (zp n) (equal (,(first (first regs)) n)
                                    ,(second (first regs)))))
          (open-init-thms (rest regs)))))

(defun open-step-thms (regs vars)
  (if (endp regs) ()
    (cons `(defthm ,(symbol-append 'open-step- (first (first regs)))
             (implies (not (zp n))
                      (equal (,(first (first regs)) n)
                             (let ,(var-binds vars) ,(third (first regs))))))
          (open-step-thms (rest regs) vars))))

(defmacro defsimulator (&rest regs)
  (let ((vars (reg-vars regs)))
    (append
     `(encapsulate
       ()
       (mutual-recursion ,@(logic-fns regs vars))
       (defstobj sv ,@(get-fns vars))
       (defun step-sv (sv)
         (declare (xargs :stobjs sv))
         (let* ,(append (sv-binds vars)
                        (sv-nexts regs)
                        (sv-updates vars))
           sv))
       (defun init-sv (sv)
         (declare (xargs :stobjs sv))
         (let* ,(init-upds regs) sv))
       (defun run-sv (n sv)
         (declare (xargs :stobjs sv :guard (natp n)))
         (if (zp n) sv (let ((sv (step-sv sv))) (run-sv (1- n) sv))))
       (defun run-state (n sv)
         (declare (xargs :stobjs sv :guard (natp n)))
         (let ((sv (init-sv sv))) (run-sv n sv)))
       (defun inv (n sv)
         (declare (xargs :stobjs sv :verify-guards nil))
         (and ,@(inv-unr vars))))
     (open-init-thms regs)
     (open-step-thms regs vars)
     `((defthm inv-over-step-sv
         (implies (and (not (zp n)) (inv (1- n) sv))
                  (inv n (step-sv sv))))
       (defthm inv-of-init-sv
         (inv 0 (init-sv sv)))
       (defthm run-sv-commute
         (equal (run-sv n (step-sv sv))
                (step-sv (run-sv n sv)))
         :hints (("Goal" :in-theory (disable step-sv))))
       (defun induct-scheme (n m sv)
         (if (zp n) (list n m sv) (induct-scheme (1- n) m sv)))
       (defthm inv-over-run-sv
         (implies (and (natp n) (natp m) (inv m sv))
                  (inv (+ n m) (run-sv n sv)))
         :hints (("Goal" :induct (induct-scheme n m sv)
                  :in-theory (disable inv step-sv)))
         :rule-classes nil)
       (defthm inv-over-run-state
         (implies (natp n)
                  (inv n (run-state n sv)))
         :hints (("Goal" :in-theory (disable inv init-sv)
                  :use ((:instance inv-over-run-sv (m 0)
                                   (sv (init-sv sv)))))))
       (defthm inv-unroll
         (implies (inv n sv) (and ,@(inv-unr vars)))
         :rule-classes nil)
       (defexec machine-state (n)
         (declare (xargs :guard (natp n)
                         :guard-hints
                         (("Goal" :in-theory (disable inv run-state ,@(get-fns vars))
                           :use ((:instance inv-unroll
                                            (sv (run-state n (list ,@(var-nils vars))))))))))
         (mbe :logic (list ,@(lgc-fncls vars))
              :exec (with-local-stobj sv
                        (mv-let (rslt sv)
                            (let ((sv (run-state n sv)))
                              (mv (list ,@(get-fncls vars)) sv))
                          rslt))))))))

;; example use from the paper:

(defun initial-pc ()
  (declare (xargs :guard t))
  0)
(defun initial-ra ()
  (declare (xargs :guard t))
  0)
(defun initial-rb ()
  (declare (xargs :guard t))
  0)

(defun instr (pc)
  (declare (xargs :guard t))
  ;; defines the program. we will encapsulate it here
  ;; by defining a simple function and the disabling the body
  ;; and executable counterpart
  (if (> (nfix pc) 0) 'bra 'mov))

(in-theory (disable instr (instr)
                    initial-pc (initial-pc)
                    initial-ra (initial-ra)
                    initial-rb (initial-rb)))

(defun >n (x y)
  (declare (xargs :guard t))
  (> (nfix x) (nfix y)))
(defun +n (x y)
  (declare (xargs :guard t))
  (+ (nfix x) (nfix y)))

(in-theory (disable >n +n))

(defsimulator
  (rpc (initial-pc)
       (cond ((and (eq (instr rpc) 'bra) (equal rrb 0)) rra)
             (t (+n rpc 1))))
  (rra (initial-ra)
       (cond ((eq (instr rpc) 'add) (+n rra rrb))
             ((integerp (instr rpc)) (instr rpc))
             (t rra)))
  (rrb (initial-rb)
       (cond ((eq (instr rpc) 'mov) rra)
             ((eq (instr rpc) 'cmp) (if (>n rra rrb) 1 0))
             (t rrb))))
