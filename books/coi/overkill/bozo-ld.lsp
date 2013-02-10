;; jcd - bzo - this is a temporary file that can be appended onto the 
;; Makefile.acl2s that we generate in order to prove :dir support for 
;; my-load, a standin for ld, until v2.9.3 is released.

(defun bozo-include-book-dir (dir acl2-defaults-table)
  (cdr (assoc-eq dir
                 (cdr (assoc-eq :include-book-dir-alist
                                acl2-defaults-table)))))

(defmacro bozo-include-book-dir-with-chk (soft-or-hard ctx dir acl2-defaults-table)
  `(let ((ctx ,ctx)
         (dir ,dir)
         (acl2-defaults-table ,acl2-defaults-table))
     (let ((dir-value (bozo-include-book-dir dir acl2-defaults-table)))
       (cond ((null dir-value)
              (er ,soft-or-hard ctx
                  "The legal values for the :DIR argument are keywords that ~
                   include :SYSTEM as well as those added by a call of ~
                   add-include-book-dir.  However, that argument is ~x0, which ~
                   is not among the list of those legal values, ~x1."
                  dir
                  (strip-cars
                   (cdr (assoc-eq :include-book-dir-alist
                                  acl2-defaults-table)))))
             (t ,(if (eq soft-or-hard 'soft) '(value dir-value) 'dir-value))))))

(defmacro bozo-path-plus-dir-to-string (path &key dir)
  `(if ,dir
       (let* ((acl2-defaults-table
               (table-alist 'acl2-defaults-table (w state)))
              (resolve-dir
               (bozo-include-book-dir-with-chk hard 'ld ,dir
                                               acl2-defaults-table)))
         (concatenate 'string resolve-dir ,path))
     ,path))

(defmacro bozo-ld (path &key dir)
  `(if ,dir
       (ld (bozo-path-plus-dir-to-string ,path :dir ,dir))
     (ld ,path)))
 

