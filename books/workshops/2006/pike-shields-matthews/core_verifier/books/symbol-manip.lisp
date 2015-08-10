#|
  Book:    symbol-mainp
  Author:    Lee Pike, Galois Connections, Inc. <leepike@galois.com>
|#

(in-package "ACL2")

;; Obtained from Daron Vroon, who obtained this from Dave Greve.  Thanks, Dave!
(defun symbol-list-to-string1 (list)
  (declare (xargs :guard (symbol-listp list)))
  (if (consp list)
      (concatenate 'string
                   (symbol-name (car list))
                   (symbol-list-to-string1 (cdr list)))
    ""))

;; Obtained from Daron Vroon, who obtained this from Dave Greve.  Thanks, Dave!
(defmacro join-symbols1 (witness &rest rst)
  `(intern-in-package-of-symbol (symbol-list-to-string1 (list ,@rst))
                                ,witness))
