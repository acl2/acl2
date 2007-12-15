(in-package "ACL2")

(mutual-recursion
 (defun pack-list (args)
   (declare (xargs :measure (acl2-count args)
                   :guard t
                   :verify-guards nil))
   (if (atom args)
       nil
     (if (atom (cdr args))
         (pack-tree (car args))
       (append (pack-tree (car args))
               (cons #\Space
                     (pack-list (cdr args)))))))
 (defun pack-tree (tree)
   (declare (xargs :measure (acl2-count tree)
                   :guard t))
   (if (atom tree)
       (if (or (acl2-numberp tree)
               (characterp tree)
               (stringp tree)
               (symbolp tree))
           (explode-atom tree 10)
         '(#\Space))
     (append (cons #\( (pack-tree (car tree)))
             (cons #\Space (pack-list (cdr tree)))
             (list #\))))))

(defun pack-term (args)
  (declare (xargs :guard t
                  :verify-guards nil))
  (intern (coerce (pack-list args) 'string) "ACL2"))

(defmacro pack (&rest args)
  `(pack-term (list ,@args)))
