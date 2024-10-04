(in-package "ACL2")

(defmacro include-acl2-book
    (book-name
     &key (load-compiled-file ':warn))
  (declare (xargs :guard
		  (member load-compiled-file
			  '(t nil :warn :comp))))
  `(include-book
    ,book-name
    :dir :system
    :load-compiled-file ,load-compiled-file))
