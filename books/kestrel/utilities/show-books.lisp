; Copyright (C) 2023, ForrestHunt, Inc.
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; A test and documentation may be found in show-books-doc.lisp.

(in-package "ACL2")

(program)

(defun world-of-full-book-name (full-book-name project-dir-alist wrld-tail ctx)

; This definition is based on function scan-to-include-book from the ACL2
; sources through Version  8.5 (but removed after that).

; We wish to give meaning to stringp logical names such as "arith".  We
; do it in an inefficient way: we scan the whole world looking for an event
; tuple of type INCLUDE-BOOK and namex full-book-name.

  (cond
   ((null wrld-tail)
    (er hard ctx
        "Implementation error in ~x0: Unable to find event-landmark for the ~
         book with full-book-name ~x1."
        'world-of-full-book-name full-book-name))
   ((and (eq (caar wrld-tail) 'event-landmark)
         (eq (cadar wrld-tail) 'global-value)
         (eq (access-event-tuple-type (cddar wrld-tail)) 'include-book)
         (equal (book-name-to-filename-1 full-book-name project-dir-alist ctx)
                (access-event-tuple-namex (cddar wrld-tail))))
    wrld-tail)
   (t (world-of-full-book-name full-book-name project-dir-alist
                               (cdr wrld-tail) ctx))))

(defun show-books-fal (iba project-dir-alist wrld ctx top-nodes fal)

; Extend fal so that every included book is associated with all books that it
; immediately includes.

  (cond ((endp iba)
         (mv top-nodes fal))
        (t (let* ((book-name (caar iba))
                  (wrld-tail (world-of-full-book-name
                              book-name project-dir-alist wrld ctx))
                  (path (global-val 'include-book-path wrld-tail)))
             (cond (path (show-books-fal
                          (cdr iba) project-dir-alist wrld ctx
                          top-nodes
                          (hons-acons (car path) ; parent
                                      (cons book-name
                                            (cdr (hons-get (car path) fal)))
                                      fal)))
                   (t (show-books-fal
                       (cdr iba) project-dir-alist wrld ctx
                       (cons book-name top-nodes)
                       (hons-acons book-name nil fal))))))))

(defun show-books-tree (lst fal sysfile ctx project-dir-alist)
  (cond
   ((endp lst) nil)
   (t
    (let* ((full-book-name (car lst))
           (children (cdr (hons-get full-book-name fal))))
      (cons (cons (cond
                   ((eq sysfile t) full-book-name)
                   (sysfile ; default
                    (if (and (sysfile-p full-book-name)
                             (eq (sysfile-key full-book-name) :system))
                        (concatenate 'string
                                     "[books]/"
                                     (sysfile-filename full-book-name))
                      (book-name-to-filename-1
                       full-book-name project-dir-alist ctx)))
                   (t
                    (book-name-to-filename-1
                     full-book-name project-dir-alist ctx)))
                  (show-books-tree children fal sysfile ctx project-dir-alist))
            (show-books-tree (cdr lst) fal sysfile ctx project-dir-alist))))))

(defun show-books-fn (sysfile state)
  (declare (xargs :stobjs state))
  (let* ((wrld (w state))
         (project-dir-alist (project-dir-alist wrld))
         (ctx 'show-books))
    (mv-let (top-nodes fal)
      (show-books-fal (global-val 'include-book-alist wrld)
                      project-dir-alist wrld ctx nil nil)
      (fast-alist-free-on-exit
       fal
       (show-books-tree top-nodes fal sysfile ctx project-dir-alist)))))

(defmacro show-books (&key (sysfile ':default))
  (declare (xargs :guard (member-eq sysfile '(t nil :default))))
  `(show-books-fn ,sysfile state))
