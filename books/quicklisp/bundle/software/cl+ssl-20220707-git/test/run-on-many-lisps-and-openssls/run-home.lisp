(defparameter *this-dir*
  (if *load-truename*
      (make-pathname :name nil :type nil :defaults *load-truename*)
      ;; for slime:
      #P"/home/anton/prj/cl+ssl/cl-plus-ssl/test/run-on-many-lisps-and-openssls/"))

(load (merge-pathnames "run-on-many-lisps-and-openssls.lisp" *this-dir*))


(defparameter *abcl-1.3.1* (make-instance 'lisp-exe:abcl
                                          :java-exe-path "java"
                                          :abcl-jar-path "/home/anton/unpacked/abcl-bin-1.3.1/abcl.jar"))
(defparameter *ccl-1.11-x86-64* (make-instance 'lisp-exe:ccl
                                               :exe-path "/home/anton/unpacked/ccl-1.11/lx86cl64"))
(defparameter *sbcl-1.4.13* (make-instance 'lisp-exe:sbcl
                                           :exe-path "/home/anton/unpacked/sbcl-1.4.13-x86-64-linux/run-sbcl.sh"))


;; (run-on-many-lisps-and-openssls:clean-fasls (merge-pathnames "workdir/" *this-dir*))

(let ((*print-pretty* t))
  (format t "~S~%"
          (time
           (run-on-many-lisps-and-openssls:run
            :test-run-description '(:lib-world "quicklisp 2019-01-07 + cl+ssl.head"
                                    :contact-email "avodonosov@yandex.ru")
            :test-run-dir (merge-pathnames "workdir/" *this-dir*)
            :quicklisp-dir (merge-pathnames "quicklisp/" (user-homedir-pathname))
            ;; :cl+ssl-location (uiop:pathname-parent-directory-pathname
            ;;                   (uiop:pathname-parent-directory-pathname *this-dir*))
            :cl+ssl-location  nil ;; to use the cl+ssl version from quicklisp
            :lisps (list *ccl-1.11-x86-64*
                         *sbcl-1.4.13*
                         *abcl-1.3.1*
                         )
            :openssl-releases '("openssl-0.9.8zh"
                                        ; "openssl-1.0.0s"
                                        ; "openssl-1.0.2q"
                                        ; "openssl-1.1.0j"
                                        ; "openssl-1.1.1a"
                                )
            :openssl-releases-dir (merge-pathnames "openssl-releases/bin/"
                                                   *this-dir*)))))

