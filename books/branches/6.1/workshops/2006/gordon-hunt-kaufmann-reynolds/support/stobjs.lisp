(in-package "ACL2")

(include-book "data")

(defconst *big-instr-list*
  (make-instrs 0 10 nil (expt 10 6) nil))

(defstobj st
  (mem :type (array t (100))
       :initially 0))

; An instruction is a list (read addr) or (write addr val), where addr and val
; are natural numbers.  A read returns the value read (default 0).

(defun s$read-step (addr st)
  (declare (xargs :guard (and (natp addr) (< addr 100))
                  :stobjs st))
  (memi addr st))

(defun s$write-step (addr val st)
  (declare (xargs :guard (and (natp addr) (< addr 100))
                  :stobjs st))
  (update-memi addr val st))

(defun s$write-p (instr)
  (declare (xargs :guard t))
  (and (true-listp instr)
       (eql (length instr) 3)
       (eq (car instr) 'write)
       (natp (cadr instr))
       (< (cadr instr) 100)
       (natp (caddr instr))))

(defun s$read-p (instr)
  (declare (xargs :guard t))
  (and (true-listp instr)
       (eql (length instr) 2)
       (eq (car instr) 'read)
       (natp (cadr instr))
       (< (cadr instr) 100)))

(defun s$get-addr (instr)
  (declare (xargs :guard (or (s$read-p instr) (s$write-p instr))))
  (cadr instr))

(defun s$get-val (write-instr)
  (declare (xargs :guard (s$write-p write-instr)))
  (caddr write-instr))

(defun s$run (instrs st reversed-values-read)
  (declare (xargs :guard (and (true-listp instrs)
                              (true-listp reversed-values-read))
                  :stobjs st))
  (if (endp instrs)
      (mv reversed-values-read st)
    (let* ((instr (car instrs))
           (st (if (s$write-p instr)
                   (s$write-step (s$get-addr instr) (s$get-val instr) st)
                 st)))
      (s$run (cdr instrs)
             st
             (if (s$read-p instr)
                 (cons (s$read-step (s$get-addr instr) st)
                       reversed-values-read)
               reversed-values-read)))))
