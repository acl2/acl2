; Original author: David Rager <ragerdl@cs.utexas.edu>

(in-package "ACL2")

(defttag in-raw-mode)

(defmacro in-raw-mode (&rest forms)
  `(progn! (set-raw-mode t)
           ,@forms
           (set-raw-mode nil)))
