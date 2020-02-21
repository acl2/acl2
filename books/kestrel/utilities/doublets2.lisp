; Utilities that deal with doublets (true lists of length 2)
;
; Copyright (C) 2016-2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Main Author: Eric Smith (eric.smith@kestrel.edu)
; Contributing Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; STATUS: IN-PROGRESS

(include-book "doublets")

;; A book about "doublets" and lists of doublets (which are similar to alists).

;; Note that the standard recognizer for lists of doublets, doublet-listp, is
;; built in to ACL2.

;; Note that symbol-doublet-listp (which recognizes doublets whose first
;; elements are symbols) is built in to ACL2.

;; Note that alist-to-doublets is built in to ACL2.

; See also TUPLEP in in [books]/std/util/support.lisp.

;; Recognize a doublet (a true list with two elements)
(defun doubletp (x)
  (declare (xargs :guard t))
  (and (true-listp x)
       (= 2 (len x))))

(defun make-doublets (xs ys)
  (declare (xargs :guard (and (true-listp xs)
                              (true-listp ys))))
  (if (endp xs)
      nil
    (cons (list (first xs) (first ys))
          (make-doublets (rest xs) (rest ys)))))

;; Recognize a doublet containing two symbols
(defun symbol-symbol-doubletp (x)
  (declare (xargs :guard t))
  (and (doubletp x)
       (symbolp (first x))
       (symbolp (second x))))

;; TODO This is equivalent to the built-in DOUBLET-STYLE-SYMBOL-TO-SYMBOL-ALISTP?
(defun symbol-symbol-doubletsp (l)
  (declare (xargs :guard t))
  (if (not (consp l))
      (eq l nil)
    (and (symbol-symbol-doubletp (car l))
         (symbol-symbol-doubletsp (cdr l)))))

;todo: add 'doublets' to the name
;; TODO: Or just use strip-cadrs?
(defun strip-seconds (l)
  (declare (xargs :guard (doublet-listp l)))
  (if (endp l)
      nil
    (cons (second (car l))
          (strip-seconds (cdr l)))))
