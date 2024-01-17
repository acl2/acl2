(pushnew "/home/cl/package-doc-dump/" asdf:*central-registry* :test #'equal)
(ql:quickload "package-doc-dump")

(pushnew "/home/cl/cl-plus-ssl/" asdf:*central-registry* :test #'equal)
(ql:quickload "cl+ssl")

;; make sure we load the local version,
;; not the one coming with Quicklisp
(assert (string= "/home/cl/cl-plus-ssl/src/package.lisp"
                 (namestring 
                  (asdf:system-relative-pathname "cl+ssl"
                                                 "src/package.lisp"))))

(package-doc-dump:dump-html
 "cl+ssl"
 (mapcar (lambda (path)
           (asdf:system-relative-pathname "cl+ssl"
                                          path))
         '("src/config.lisp"
           "src/package.lisp"))
 ;; Remove the implementation of cl+ssl:stream-fd,
 ;; like on CCL `stream-fd ((stream ccl::basic-stream))`,
 ;; so only the generic function reamins.
 :doc-node-filter (lambda (doc-node)
                    (not (and (typep doc-node
                                     'docparser:method-node)
                              (string-equal (docparser:node-name doc-node)
                                            "stream-fd"))))
 :output-file "/home/cl/cl-plus-ssl-api.html")
