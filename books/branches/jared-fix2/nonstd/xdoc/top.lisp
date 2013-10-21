; WARNING: This book is a stub for directory nonstd/xdoc/ in the ACL2 community
; books.  It has no connection to directory xdoc/.  Rather, it is a stub that
; allows us to certify the nonstd/ books without needing to certify all the
; books that support xdoc/.  That is a worthy goal, but as of this writing in
; Sept. 2013, we're a long way from that.

(in-package "ACL2")

(defun remove-initial-keywords (lst)
  (declare (xargs :guard (true-listp lst)))
  (cond ((endp lst) nil)
        ((keywordp (car lst))
         (remove-initial-keywords (cddr lst)))
        (t lst)))

(defmacro defsection (name &rest args)
  (declare (ignore name))
  `(encapsulate
    ()
    ,@(remove-initial-keywords args)))

(defmacro defxdoc (&rest args)
  (declare (ignore args))
  '(value-triple "Skipping defxdoc form."))
