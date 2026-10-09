; Copyright (C) 2025, Matt Kaufmann
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

(in-package "ZF")

(mutual-recursion

(defun typ-fn-lst (x)
  (declare (xargs :mode :logic :guard (true-listp x)))
  (cond ((endp x) nil)
        (t (cons (typ-fn (car x))
                 (typ-fn-lst (cdr x))))))

(defun typ-fn-arrow* (a b x)
  (declare (xargs :mode :logic
                  :guard (true-listp x)
                  :measure (1+ (+ (acl2-count a) (acl2-count b) (acl2-count x)))))
  (mv-let (kwd a)
    (case-match a
      ((:implicit y) (mv :ki    y))
      (&             (mv :arrow a)))
    (cond ((endp x)
           (list 'list kwd (typ-fn a) (typ-fn b)))
          (t
           (list 'list
                 kwd
                 (typ-fn a)
                 (typ-fn-arrow* b (car x) (cdr x)))))))

(defun typ-fn (x)
  (declare (xargs :mode :logic :guard t))
  (cond
   ((or (not (true-listp x))
        (atom x))
    x)
   ((eq (car x) :arrow*)
    (if (cddr x) ; expected case: (:arrow* a b) or (:arrow* a b ...)
        (typ-fn-arrow* (cadr x) (caddr x) (cdddr x))
      (if (cdr x)
          (typ-fn (car x))
; Impossible case?:
        nil)))
   (t (list* 'list
             (car x)
             (typ-fn-lst (cdr x))))))
)

(defmacro typ (type-exp) ; expand-type
  (typ-fn type-exp))
