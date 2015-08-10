(in-package "ACL2")
;; Tue Dec 23 14:49:11 2003 macros that expands a term with a list of
;; abbrevation

(mutual-recursion
 (defun expand-mylet*-2-l (binding term-l)
   (declare (xargs :verify-guards nil
                   :measure (acl2-count term-l)))
   (if (endp term-l) nil
     (cons (expand-mylet*-2 binding (car term-l))
           (expand-mylet*-2-l binding (cdr term-l)))))

 (defun expand-mylet*-2 (binding term)
   (declare (xargs :verify-guards nil
                   :measure (acl2-count term)))
   (let ((key (car binding))
         (value (cdr binding)))
     (cond ((atom term)
            (if (equal term key)
                value
              term))
           ((consp term)
            (if (consp term)
                (cons (car term)
                      (expand-mylet*-2-l binding (cdr term)))
              term))
           (t term)))))

; (expand-mylet*-2 '(x . (f (+ x y)))
;                  '(G (f (x x))))

(defun expand-mylet*-1 (binding alist)
  (declare (xargs :verify-guards nil))
  (if (endp alist) nil
    (cons (cons (caar alist)
                (expand-mylet*-2 binding (cdar alist)))
          (expand-mylet*-1 binding (cdr alist)))))


(defun expand-mylet* (bindings topTerm)
  (declare (xargs :verify-guards nil
                  :measure (len bindings)))
  (if (endp bindings)
      topTerm
    (expand-mylet* (expand-mylet*-1 (car bindings) (cdr bindings))
                   (expand-mylet*-2 (car bindings) topTerm))))

;; this is a flaky substitution implementation.
;; Only used by myself. It is ok.

; (expand-mylet* '((x . (f x))
;                  (y . (f x (f (+ x y)))))
;                '(G (f (+ x y) (y y x))))

(defun extract-bindings (assignments)
  (declare (xargs :verify-guards nil))
  (if (endp assignments) nil
    (cons (cons (caar assignments) (cadar assignments))
          (extract-bindings (cdr assignments)))))

; (extract-bindings
;  '((cid (current-thread s))
;    (tt  (thread-table s))
;    (thread (thread-by-id cid tt))
;    (callstack (thread-call-stack thread))
;    (topframe  (top callstack))))


(defmacro mylet* (assignments theTerm)
 (let ((expanded (expand-mylet* (extract-bindings assignments) theTerm)))
      `,expanded))