#|$ACL2s-Preamble$;
(include-book "defexec/other-apps/records/records" :dir :system)
(begin-book t);$ACL2s-Preamble$|#

(in-package "ACL2")

(defun >=0 (x) (>= x 0))


; We introduce aliases for defun that assist in readability.  Wires correspond
; to functions defined by defun-w, which return an ordinary value.  Nodes
; correspond to functions defined by defun-n, which return records.

(defmacro defun-w (&rest args)
  `(defun ,@args))

(defmacro defun-n (&rest args)
  `(defun ,@args))

(defmacro defun-asn (&rest args)
  `(defun ,@args))

(defmacro defthml (&rest args)
  `(local (defthm ,@args)))

(defmacro defthmdl (&rest args)
  `(local (defthmd ,@args)))

; 31 July 2008
; We generate a call to this function when we don't recognize a node type
(defstub unknown (name in)
  t)#|ACL2s-ToDo-Line|#


(defmacro g (a r) `(mget ,a ,r))
(defmacro s (a v r) `(mset ,a ,v ,r))
#|
  02 July 2008
  To avoid the annoyances w/ ill-formed-key in the good-map hypothesis for
  guard verification, I slightly modified the following "set" macro.
|#

(defun s*-fn (args) ; see s*
  (declare (xargs :guard (true-listp args)))
  (if (endp (cdr args))
    nil
    `(s ,(car args) ,(cadr args) ,(s*-fn (cddr args)))))

(defmacro s* (&rest args)

; To set fields with respective values, starting with the empty record:
; ; (s* :fld1 val1 :fld2 val2 ... :fldk valk)

;  (declare (xargs :guard (keyword-value-listp args)))
  (s*-fn args))

(defun a*-fn (args) ; see a*
  (declare (xargs :guard (true-listp args)))
  (if (endp (cdr args))
    nil
    `(list* (cons ,(car args) ,(cadr args))
      ,(a*-fn (cddr args)))))

(defmacro a* (&rest args)
  (a*-fn args))

(add-binop g mget)
(add-binop s mset)

(defun s-alist (alist r)
  (cond ((consp alist)
         (s (caar alist)
            (cdar alist)
            (s-alist (cdr alist) r)))
        (t r)))

(defun nat-listp (l)
  (declare (xargs :guard t))
  (cond ((atom l)
         (eq l nil))
        (t (and (natp (car l))
                (nat-listp (cdr l))))))

(defthm nat-listp-forward-to-integer-listp
  (implies (nat-listp x)
           (integer-listp x))
  :rule-classes :forward-chaining)
