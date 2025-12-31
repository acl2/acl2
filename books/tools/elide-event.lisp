; Copyright (C) 2025, ForrestHunt, Inc.
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

(in-package "ACL2")

(defun elide-defun (ev)
  (declare (xargs :guard (true-listp ev)))
  (cond ((and (cddddr ev) ; (defun name args dcl ... body)
              (plausible-dclsp (butlast (cdddr ev) 1)) ; for guard: always true
              )
         `(,(car ev)
           ,(cadr ev)
           ,(caddr ev)
           ,@(strip-dcls '(comment ; to remove from *xargs-keywords*:
                           :guard-hints
                           :guard-debug
                           :hints
                           :measure-debug
                           :otf-flg
                           #+:non-standard-analysis :std-hints)
                         (butlast (cdddr ev) 1))
           ,(car (last ev))))
        (t ev)))
           
(defun elide-defthm (ev)
  (declare (xargs :guard (true-listp ev)))
  (let* ((name (cadr ev))
         (body (caddr ev))
         (rest (cdddr ev))
         (tail (and rest ; optimization
                    (member-eq :rule-classes rest))))
    (cond (tail (list (car ev) name body :rule-classes (cadr tail)))
          (rest (list (car ev) name body))
          (t ev))))

(mutual-recursion

(defun elide-event (ev)
  (declare (xargs :guard (true-listp ev)))
  (case (car ev)
    ((defun defund defun-nx defund-nx) ; for mutual-recursion
     (elide-defun ev))
    ((progn mutual-recursion)
     (cons (car ev)
           (elide-event-lst (cdr ev))))
    (encapsulate (if (cadr ev)
                     ev ; for redundancy
                   (list* 'encapsulate
                          nil
                          (elide-event-lst (cddr ev)))))
    (defthm (elide-defthm ev))
    (t ev)))

(defun elide-event-lst (lst)
  (declare (xargs :guard (true-listp lst)))
  (cond ((endp lst) nil)
        (t (cons (if (true-listp (car lst)) ; for guard: always true
                     (elide-event (car lst))
                   (car lst))
                 (elide-event-lst (cdr lst))))))
)
