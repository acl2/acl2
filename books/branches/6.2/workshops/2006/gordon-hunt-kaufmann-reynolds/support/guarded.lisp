(in-package "ACL2")

(include-book "data")

(defconst *big-instr-list*
  (make-instrs 0 10 nil (expt 10 6) nil))

; An instruction is a list (read addr) or (write addr val), where addr and val
; are natural numbers.  A read returns the value read (default 0) from the
; given list of pairs (alist).

(defun g$read-step (addr alist)
  (declare (xargs :guard (and (natp addr) (alistp alist))))
  (let ((pair (assoc addr alist)))
    (if pair (cdr pair) 0)))

(defun g$write-step (addr val alist)
  (declare (xargs :guard (and (natp addr) (alistp alist))))
  (put-assoc-eql addr val alist))

(defun g$write-p (instr)
  (declare (xargs :guard t))
  (and (true-listp instr)
       (eql (length instr) 3)
       (eq (car instr) 'write)
       (natp (cadr instr))
       (natp (caddr instr))))

(defun g$read-p (instr)
  (declare (xargs :guard t))
  (and (true-listp instr)
       (eql (length instr) 2)
       (eq (car instr) 'read)
       (natp (cadr instr))))

(defun g$get-addr (instr)
  (declare (xargs :guard (or (g$read-p instr) (g$write-p instr))))
  (cadr instr))

(defun g$get-val (write-instr)
  (declare (xargs :guard (g$write-p write-instr)))
  (caddr write-instr))

; A state is a list of pairs (an alist) mapping natural numbers to values.

(defun g$run (instrs alist reversed-values-read)
  (declare (xargs :guard (and (true-listp instrs)
                              (alistp alist)
                              (true-listp reversed-values-read))))
  (if (endp instrs)
      reversed-values-read
    (let ((instr (car instrs)))
      (g$run (cdr instrs)
             (if (g$write-p instr)
                 (g$write-step (g$get-addr instr) (g$get-val instr) alist)
               alist)
             (if (g$read-p instr)
                 (cons (g$read-step (g$get-addr instr) alist)
                       reversed-values-read)
               reversed-values-read)))))

