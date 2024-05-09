; A wrapper for show-books
;
; Copyright (C) 2023 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "show-books")
(include-book "kestrel/utilities/widen-margins" :dir :system)

(defun print-as-string-or-object (obj)
  (declare (xargs :guard t))
  (if (stringp obj)
      (cw "~s0" obj)
    (cw "~x0" obj)))

(mutual-recursion
 (defun print-show-books-tree (indent tree parens)
   (declare (xargs :guard (and (stringp indent)
                               (booleanp parens))))
   (if (not (consp tree))
       (er hard? 'print-show-books-tree "Unexpected thing in show-books: ~x0." tree)
     (let ((book (car tree))
           (sub-books (cdr tree)))
       (if sub-books
           (progn$ (cw "~s0" indent)
                   (and parens (cw "("))
                   (print-as-string-or-object book)
                   (cw "~%")
                   (print-show-books-trees (concatenate 'string "  " indent) sub-books parens)
                   (and parens (cw ")")))
         ;; leaf node, so no parens:
         (prog2$ (cw "~s0" indent)
                 (print-as-string-or-object book) ; non-string can happen with :sysfile t
                 )))))

 ;; Prints with newlines between the trees, but not after the last tree
 (defun print-show-books-trees (indent trees parens)
   (declare (xargs :guard (and (stringp indent)
                               (booleanp parens))))
   (if (not (consp trees))
       nil
     (progn$ (print-show-books-tree indent (first trees) parens)
             ;; Print newline if not the last element:
             (and (consp (rest trees))
                  (cw "~%"))
             (print-show-books-trees indent (rest trees) parens)))))

(defun my-show-books-fn (parens sysfile state)
  (declare (xargs :mode :program
                  :guard (member-eq sysfile '(t nil :default))
                  :stobjs state))
  (let ((state (widen-margins state)))
    (progn$ (cw "~%Currently included books:~%")
            (print-show-books-trees "" (show-books-fn sysfile state) parens)
            (let ((state (unwiden-margins state)))
              (prog2$ (cw "~%")
                      (value :invisible))))))

;; This is like show-books, except this one prints more compactly and
;; consistently (less punctuation, avoids some issues with pretty-printing and
;; wide lines.)
(defmacro my-show-books (&key
                         (parens 'nil) ; print parens for books with sub-books, to allow easily skipping over a whole subtree
                         (sysfile ':default) ; same as for show-books ; todo: consider nil, to support quickly opening the listed files
                         )
  `(my-show-books-fn ',parens ',sysfile state))
