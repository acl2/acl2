; Copyright (C) 2023, ForrestHunt, Inc.
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

(in-package "ACL2")

(include-book "show-books")

(defun show-books-result-p (x)
  (declare (xargs :guard t))
  (cond ((atom x) (null x))
        (t (let ((entry (car x)))
             (and (consp entry)
                  (or (sysfile-p (car entry))
                      (stringp (car entry)))
                  (show-books-result-p (cdr entry))
                  (show-books-result-p (cdr x)))))))

(defun show-books-flatten (lst)
  (declare (xargs :guard (show-books-result-p lst)))
  (cond ((endp lst) nil)
        (t (cons (caar lst)
                 (append (show-books-flatten (cdar lst))
                         (show-books-flatten (cdr lst)))))))

(encapsulate
  ()
  (local
   (include-book "arithmetic/top-with-meta" :dir :system)) ; no_port
  (local (include-book "centaur/gl/gl" :dir :system))      ; no_port
  (assert-event
   (let ((result (show-books :sysfile nil)))
     (and (show-books-result-p result)
          (equal
           (merge-sort-lexorder (show-books-flatten result))
           (merge-sort-lexorder (book-name-lst-to-filename-lst
                                 (strip-cars
                                  (global-val 'include-book-alist (w state)))
                                 (project-dir-alist (w state)) 'my-top)))))))
