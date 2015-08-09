
(in-package "SAT")

(program)

(include-book "convert-to-cnf")
(include-book "check-output")

(defun make-user-var-entry (a-var i-var)
  `(user-var-entry ,a-var . ,i-var))

(defun uv-entryp (entry)
  (eq 'user-var-entry (car entry)))

(defun uve-a-var (entry)
  (cadr entry))

(defun uve-i-var (entry)
  (cddr entry))

(defun make-user-arg-entry (i-expr)
  `(user-arg-entry . ,i-expr))

(defun ua-entryp (x)
  (eq 'user-arg-entry (car x)))

(defun uae-i-expr (ua-entry)
  (cdr ua-entry))

(defun make-uae-list (i-expr-list acc)
  (cond
   ((endp i-expr-list)
    (revappend acc nil))
   (t
    (make-uae-list (cdr i-expr-list)
                   (cons (make-user-arg-entry (car i-expr-list))
                         acc)))))

(defun make-user-un-fn-entry (fn uf-entry)
  `(user-un-fn-entry
    .
    ((,fn . ,(ufe-defined-var uf-entry))
     .
     ,(make-uae-list (ufe-arg-list uf-entry) nil))))

(defun uuf-entryp (x)
  (eq 'user-un-fn-entry (car x)))

(defun uufe-fn (uuf-entry)
  (car (car (cdr uuf-entry))))

(defun uufe-lhs (uuf-entry)
  (cdr (car (cdr uuf-entry))))

(defun uufe-args (uuf-entry)
  (cdr (cdr uuf-entry)))

(defun invalid-user-entry ()
  nil)

(defun valid-user-entryp (x)
  (consp x))

(defun user-entry-i-expr (entry)
  (cond
   ((uuf-entryp entry)
    (uufe-lhs entry))
   ((uv-entryp entry)
    (uve-i-var entry))
   ((ua-entryp entry)
    (uae-i-expr entry))
   (t
    (er hard 'user-entry-ivar
        "User expression of unexpected type: ~x0~%"
        entry))))

(defun user-entry-i-var (entry)
  (cond
   ((uuf-entryp entry)
    (uufe-lhs entry))
   ((uv-entryp entry)
    (uve-i-var entry))
   (t
    (er hard 'user-entry-i-var
        "User expression of unexpected type: ~x0~%"
        entry))))

(defun uae-list-vals (uae-list acc $sat)
  (declare (xargs :stobjs $sat))
  (cond
   ((endp uae-list)
    (revappend acc nil))
   (t
    (let* ((val (eval-i-expr (uae-i-expr (car uae-list)) $sat)))
      (uae-list-vals (cdr uae-list)
                     (cons `(quote ,val) acc)
                     $sat)))))

(defun uufe-arg-vals (entry $sat)
  (declare (xargs :stobjs $sat))
  (uae-list-vals (uufe-args entry) nil $sat))

(defun simplify-entry (entry $sat)
  (declare (xargs :stobjs $sat))
  (cond
   ((uuf-entryp entry)
    `(,(uufe-fn entry) .
      ,(uufe-arg-vals entry $sat)))
   ((uv-entryp entry)
    (uve-a-var entry))
   (t
    (er hard 'user-entry-ivar
        "User expression of unexpected type: ~x0~%"
        entry))))

(defun full-uve-list1 (alist acc)
  (cond
   ((endp alist)
    acc)
   (t
    (full-uve-list1 (cdr alist)
                    (cons (make-user-var-entry (caar alist) (cdar alist))
                          acc)))))

(defun full-uve-list ($sat)
  (declare (xargs :stobjs $sat))
  (full-uve-list1 (input-alist $sat) nil))
