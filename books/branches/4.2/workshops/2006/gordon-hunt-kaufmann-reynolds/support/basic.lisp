(in-package "ACL2")

(include-book "data")

(defconst *big-instr-list*
  (make-instrs 0 10 nil (expt 10 6) nil))

; An instruction is a list (read addr) or (write addr val), where addr and val
; are natural numbers.  A read returns the value read (default 0) from the
; given list of pairs (alist).

(defun read-step (addr alist)
  (let ((pair (assoc addr alist)))
    (if pair (cdr pair) 0)))

(defun write-step (addr val alist)
  (put-assoc-eql addr val alist))

(defun write-p (instr)
  (and (true-listp instr)
       (eql (length instr) 3)
       (eq (car instr) 'write)
       (natp (cadr instr))
       (natp (caddr instr))))

(defun read-p (instr)
  (and (true-listp instr)
       (eql (length instr) 2)
       (eq (car instr) 'read)
       (natp (cadr instr))))

(defun get-addr (instr)
  (cadr instr))

(defun get-val (write-instr)
  (caddr write-instr))

; A state is a list of pairs (an alist) mapping natural numbers to values.

(defun run (instrs alist reversed-values-read)
  (if (endp instrs)
      reversed-values-read
    (let ((instr (car instrs)))
      (run (cdr instrs)
           (if (write-p instr)
               (write-step (get-addr instr) (get-val instr) alist)
             alist)
           (if (read-p instr)
               (cons (read-step (get-addr instr) alist)
                     reversed-values-read)
             reversed-values-read)))))

