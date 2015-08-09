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

(include-book "records")
(include-book "inline")

(defmacro g (a r) `(mget ,a ,r))
(defmacro s (a v r) `(mset ,a ,v ,r))
(defun wf-rcdp (r)
  (declare (xargs :guard t))
  (good-map r))

(defun next-fn (name)
  (declare (xargs :guard (symbolp name)))
  (symbol-append name '$next))

(defmacro defunc (name args &rest aux)
  (declare (xargs :guard (and (symbolp name) (symbol-listp args))))
  `(defun* ,name ,args :inline (declare (xargs :guard t)) ,@aux))

(defun mk-signal-guard (args)
  (declare (xargs :guard (symbol-listp args)))
  (if (endp args) ''t
   `(and (wf-rcdp ,(first args))
         ,(mk-signal-guard (rest args)))))

(defmacro defwire (name args &rest aux)
  (declare (xargs :guard (and (symbolp name) (symbol-listp args))))
  `(defun* ,(next-fn name) ,args :inline
     (declare (xargs :guard ,(mk-signal-guard args)))
     ,@aux))

(defmacro defreg (name args &rest aux)
  (declare (xargs :guard (and (symbolp name) (symbol-listp args))))
  `(defun* ,(next-fn name) ,args :inline
     (declare (xargs :guard ,(mk-signal-guard args)))
     ,@aux))

(defun sim-defp (x)
  (declare (xargs :guard t))
  (and (true-listp x)
       (member-eq (first x) '(defunc defreg defwire))
       (symbolp (second x))
       (symbol-listp (third x))))

(defun sim-def-listp (x)
  (declare (xargs :guard t))
  (or (null x)
      (and (consp x)
           (sim-defp (first x))
           (sim-def-listp (rest x)))))

(defun get-wires (defs)
  (declare (xargs :guard (sim-def-listp defs)))
  (cond ((endp defs) ())
        ((eq (first (first defs)) 'defwire)
         (cons (cons (second (first defs)) (third (first defs)))
               (get-wires (rest defs))))
        (t (get-wires (rest defs)))))

(defun get-regs (defs)
  (declare (xargs :guard (sim-def-listp defs)))
  (cond ((endp defs) ())
        ((eq (first (first defs)) 'defreg)
         (cons (cons (second (first defs)) (third (first defs)))
               (get-regs (rest defs))))
        (t (get-regs (rest defs)))))

(defun signal-listp (x)
  (declare (xargs :guard t))
  (or (null x)
      (and (consp x)
           (symbol-listp (first x))
           (consp (first x))
           (signal-listp (rest x)))))

(defthm signal-listp-get-wires
  (implies (sim-def-listp defs)
           (signal-listp (get-wires defs))))

(defthm signal-listp-get-regs
  (implies (sim-def-listp defs)
           (signal-listp (get-regs defs))))

(defun logic-var-binds (vars rslt)
  (declare (xargs :guard (signal-listp vars)))
  (if (endp vars) rslt
    (let ((var (first (first vars))))
      `(bind ,var (g (quote ,var) x)
         ,(logic-var-binds (rest vars) rslt)))))

(defun logic-wire-upds (wires rslt)
  (declare (xargs :guard (signal-listp wires)))
  (if (endp wires) rslt
    (let ((wire (first (first wires)))
          (args (rest (first wires))))
      `(bind ,wire (,(next-fn wire) ,@args)
         ,(logic-wire-upds (rest wires) rslt)))))

(defun logic-reg-upds (regs rslt)
  (declare (xargs :guard (signal-listp regs)))
  (if (endp regs) rslt
    (let ((reg (first (first regs)))
          (args (rest (first regs))))
      `(bind x (s (quote ,reg) (,(next-fn reg) ,@args) x)
         ,(logic-reg-upds (rest regs) rslt)))))

(defun logic-reg-types (regs)
  (declare (xargs :guard (signal-listp regs)))
  (if (endp regs) ()
    (cons `(wf-rcdp (g (quote ,(first (first regs))) x))
          (logic-reg-types (rest regs)))))

(defun logic-step (name)
  (declare (xargs :guard (symbolp name)))
  (symbol-append name '$logic-step))

(defun logic-run (name)
  (declare (xargs :guard (symbolp name)))
  (symbol-append name '$logic-run))

(defun wf-logicp (name)
  (declare (xargs :guard (symbolp name)))
  (symbol-append name '$wf-logicp))

(defun sim-logic (name defs)
  (declare (xargs :guard (and (symbolp name)
                              (sim-def-listp defs))))
  (let ((wires (get-wires defs))
        (regs (get-regs defs)))
    `((defun ,(wf-logicp name) (x)
        (declare (xargs :guard t))
        (and (wf-rcdp x) ,@(logic-reg-types regs)))
      (defun ,(logic-step name) (x)
        (declare (xargs :guard (,(wf-logicp name) x)))
        ,(logic-var-binds regs (logic-wire-upds wires (logic-reg-upds regs 'x))))
      (defun ,(logic-run name) (x n)
        (declare (xargs :guard (and (natp n) (,(wf-logicp name) x))))
        (if (zp n) x (,(logic-run name) (,(logic-step name) x) (1- n)))))))

;; We assume that all fields satisfy wf-rcdp. This would be unacceptable in
;; practice as a variety of type declarations will be necessary.

(defun stobj-name (name)
  (declare (xargs :guard (symbolp name)))
  (symbol-append 'stobj$ name))

(defun get-fnname (name)
  (declare (xargs :guard (symbolp name)))
  (symbol-append 'get- name))

(defun set-fnname (name)
  (declare (xargs :guard (symbolp name)))
  (symbol-append 'update- name))

(defun stobj-fields (regs)
  (declare (xargs :guard (signal-listp regs)))
  (if (endp regs) ()
    (cons `(,(first (first regs)) :type (satisfies wf-rcdp) :initially nil)
          (stobj-fields (rest regs)))))

(defun stobj-renaming (regs)
  (declare (xargs :guard (signal-listp regs)))
  (if (endp regs) ()
    (cons `(,(first (first regs)) ,(get-fnname (first (first regs))))
          (stobj-renaming (rest regs)))))

(defun sim-stobj (name defs)
  (declare (xargs :guard (and (symbolp name)
                              (sim-def-listp defs))))
  (let ((regs (get-regs defs)))
    `((defstobj ,(stobj-name name) ,@(stobj-fields regs)
        :renaming ,(stobj-renaming regs)
        :inline t))))

(defun exec-var-binds (regs st rslt)
  (declare (xargs :guard (signal-listp regs)))
  (if (endp regs) rslt
    (let ((reg (first (first regs))))
      `(bind ,reg (,(get-fnname reg) ,st)
         ,(exec-var-binds (rest regs) st rslt)))))

(defun exec-wire-upds (wires rslt)
  (declare (xargs :guard (signal-listp wires)))
  (logic-wire-upds wires rslt))

(defun exec-reg-upds (regs st rslt)
  (declare (xargs :guard (signal-listp regs)))
  (if (endp regs) rslt
    (let ((reg (first (first regs)))
          (args (rest (first regs))))
      `(bind ,st (,(set-fnname reg) (,(next-fn reg) ,@args) ,st)
         ,(exec-reg-upds (rest regs) st rslt)))))

(defun exec-load-upds (regs st rslt)
  (declare (xargs :guard (signal-listp regs)))
  (if (endp regs) rslt
    (let ((reg (first (first regs))))
      `(bind ,st (,(set-fnname reg) (g (quote ,reg) x) ,st)
         ,(exec-load-upds (rest regs) st rslt)))))

(defun exec-extract-upds (regs st rslt)
  (declare (xargs :guard (signal-listp regs)))
  (if (endp regs) rslt
    (let ((reg (first (first regs))))
      `(s (quote ,reg) (,(get-fnname reg) ,st)
          ,(exec-extract-upds (rest regs) st rslt)))))

(defun exec-step (name)
  (declare (xargs :guard (symbolp name)))
  (symbol-append name '$exec-step))

(defun exec-run1 (name)
  (declare (xargs :guard (symbolp name)))
  (symbol-append name '$exec-run1))

(defun exec-load (name)
  (declare (xargs :guard (symbolp name)))
  (symbol-append name '$exec-load))

(defun exec-extract (name)
  (declare (xargs :guard (symbolp name)))
  (symbol-append name '$exec-extract))

(defun exec-run (name)
  (declare (xargs :guard (symbolp name)))
  (symbol-append name '$exec-run))

(defun sim-exec (name defs)
  (declare (xargs :guard (and (symbolp name)
                              (sim-def-listp defs))))
  (let ((wires (get-wires defs))
        (regs (get-regs defs))
        (st (stobj-name name)))
    `((defun* ,(exec-step name) (,st) :inline
        (declare (xargs :stobjs ,st))
        ,(exec-var-binds regs st (exec-wire-upds wires (exec-reg-upds regs st st))))
      (defun* ,(exec-run1 name) (,st n)
        (declare (xargs :stobjs ,st
                        :guard (natp n)))
        (if (zp n) ,st
          (bind ,st (,(exec-step name) ,st)
            (,(exec-run1 name) ,st (1- n)))))
      (defun ,(exec-load name) (x ,st)
        (declare (xargs :stobjs ,st
                        :guard (,(wf-logicp name) x)))
        ,(exec-load-upds regs st st))
      (defun ,(exec-extract name) (,st x)
        (declare (xargs :stobjs ,st
                        :guard (wf-rcdp x)))
        ,(exec-extract-upds regs st 'x))
      (defun ,(exec-run name) (x n)
        (declare (xargs :guard (and (,(wf-logicp name) x)
                                    (natp n))))
        (with-local-stobj ,st
            (mv-let (rslt ,st)
                (let* ((,st (,(exec-load name) x ,st))
                       (,st (,(exec-run1 name) ,st n))
                       (rslt (,(exec-extract name) ,st x)))
                  (mv rslt ,st))
              rslt))))))

(defun sim-thms (name)
  (declare (xargs :guard (symbolp name)))
  `((local (defthm ,(symbol-append name '-extract-load)
             (equal (,(exec-extract name) (,(exec-load name) x st) x) x)))
    (local (defthm ,(symbol-append name '-extract-step)
             (equal (,(exec-extract name) (,(exec-step name) st) x)
                    (,(logic-step name) (,(exec-extract name) st x)))))
    (in-theory (disable ,(logic-step name)
                        ,(exec-step name)
                        ,(exec-extract name)
                        ,(exec-load name)))
    (local (defthm ,(symbol-append name '-extract-over-run)
             (equal (,(exec-extract name) (,(exec-run1 name) st n) x)
                    (,(logic-run name) (,(exec-extract name) st x) n))))
    (local (defthm ,(symbol-append name '-exec-run-logic-run)
             (equal (,(exec-run name) x n) (,(logic-run name) x n))))))

(defun sim-top-fn (name)
  (declare (xargs :guard (symbolp name)))
  (symbol-append 'run- name))

(defun sim-top (name)
  (declare (xargs :guard (symbolp name)))
  `((defun ,(sim-top-fn name) (x n)
      (declare (xargs :guard (and (,(wf-logicp name) x) (natp n))))
      (mbe :logic (,(logic-run name) x n) :exec (,(exec-run name) x n)))
    ))

(defmacro defsimulator (name &rest defs)
  (declare (xargs :guard (and (symbolp name)
                              (sim-def-listp defs))))
  (list* 'encapsulate ()
         (append defs
                 (sim-logic name defs)
                 (sim-stobj name defs)
                 (sim-exec name defs)
                 (sim-thms name)
                 (sim-top name))))

(defsimulator teeny

  (defunc instr-op   (i) (and (true-listp i) (first i)))
  (defunc instr-arg1 (i) (and (true-listp i) (second i)))
  (defunc instr-arg2 (i) (and (true-listp i) (third i)))
  (defunc instr-arg3 (i) (and (true-listp i) (fourth i)))

  (defwire instr (pc mem)
    (bind i (g (g :pc pc) mem)
      (s :op (instr-op i)
         (s :arg1 (instr-arg1 i)
            (s :arg2 (instr-arg2 i)
               (s :arg3 (instr-arg3 i)
                  ()))))))

  (defreg pc (instr rfile pc)
    (s :pc
       (if (and (eq (g :op instr) 'jmp0)
                (eql (g (g :arg1 instr) rfile) 0))
           (g :arg2 instr)
         (1+ (nfix pc)))
       ()))

  (defreg mem (instr rfile mem)
    (if (eq (g :op instr) 'store)
        (s (nfix (g (g :arg1 instr) rfile))
           (g (g :arg2 instr) rfile)
           mem)
      mem))

  (defreg rfile (instr rfile mem)
    (bind op (g :op instr)
      (if (eq op 'loadm)
          (s (nfix (g (g :arg1 instr) rfile))
             (g (g (g :arg2 instr) rfile) mem)
             rfile)
        (if (eq op 'loadi)
            (s (nfix (g (g :arg1 instr) rfile))
               (g :arg2 instr)
               rfile)
          (if (eq op 'addi)
              (s (nfix (g (g :arg1 instr) rfile))
                 (+ (nfix (g (g :arg2 instr) rfile))
                    (nfix (g (g :arg3 instr) rfile)))
                 rfile)
            rfile)))))
)

;; And now we prove a simple invariant of run-teeny...

(encapsulate (((R) => *)) (local (defun R () t)))

(defun inv (x)
  (let ((pc (g :pc (g 'pc x)))
        (rfile (g 'rfile x))
        (mem (g 'mem x)))
    (and (natp pc)
         (equal (g (R) rfile) 0)
         (equal (g pc mem) (list 'jmp0 (R) pc)))))

(defthm inv-step
  (implies (inv x) (inv (teeny$logic-step x)))
  :hints (("Goal" :in-theory (enable teeny$logic-step))))

(in-theory (disable inv))

(defthm inv-logic-run
  (implies (inv x) (inv (teeny$logic-run x n))))

(defthm inv-run-teeny
  (implies (inv x) (inv (run-teeny x n))))









