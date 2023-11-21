(pushnew "/home/cl/browsable-colorize/" asdf:*central-registry* :test #'equal)
(ql:quickload "browsable-colorize")

(pushnew "/home/cl/cl-plus-ssl/" asdf:*central-registry* :test #'equal)
(ql:quickload "cl+ssl")

;; make sure we load the local version,
;; not the one coming with Quicklisp
(assert (string= "/home/cl/cl-plus-ssl/src/package.lisp"
                 (namestring 
                  (asdf:system-relative-pathname "cl+ssl"
                                                 "src/package.lisp"))))

(browsable-colorize:with-browsable-context
    (;; package designators to try when locating unqualified symbols
     '(#:cl+ssl #:cl+ssl/config)
     ;; an alist mapping from local source code directories
     ;; to base github URI
     (list (cons (asdf:system-source-directory "cl+ssl")
                 "https://github.com/cl-plus-ssl/cl-plus-ssl/tree/master/")))

  ;; use the better CSS
  (let ((colorize:*coloring-css* (browsable-colorize:better-css)))

    (colorize:colorize-file :common-lisp-browsable
                            (asdf:system-relative-pathname :cl+ssl
                                                           "src/package.lisp"))
    (colorize:colorize-file :common-lisp-browsable
                            (asdf:system-relative-pathname :cl+ssl
                                                           "src/config.lisp"))))
