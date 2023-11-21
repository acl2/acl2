(defparameter *this-dir*
  (if *load-truename*
      (make-pathname :name nil :type nil :defaults *load-truename*)
      ;; for slime:
      #P"/home/anton/prj/cl+ssl/cl-plus-ssl/test/run-on-many-lisps-and-openssls/"))

(load (merge-pathnames "run-on-many-lisps-and-openssls.lisp" *this-dir*))


(defparameter *abcl-1.7.0* (make-instance 'lisp-exe:abcl
                                          :java-exe-path "java"
                                          :abcl-jar-path "/home/anton/unpacked/abcl-bin-1.7.0/abcl.jar"))
(defparameter *abcl-1.9.0* (make-instance 'lisp-exe:abcl
                                          :java-exe-path "java"
                                          :abcl-jar-path "/home/anton/unpacked/abcl-bin-1.9.0/abcl.jar"))
(defparameter *ccl-1.11-x86-64* (make-instance 'lisp-exe:ccl
                                               :exe-path "/home/anton/unpacked/ccl-1.11/lx86cl64"))
(defparameter *sbcl-2.2.9* (make-instance 'lisp-exe:sbcl
                                           :exe-path "/home/anton/unpacked/sbcl-2.2.9-x86-64-linux/run-sbcl.sh"))
(defparameter *sbcl-2.2.1* (make-instance 'lisp-exe:sbcl
                                          :exe-path "/home/anton/unpacked/sbcl-2.2.1-x86-64-linux/run-sbcl.sh"))
(defparameter *cmucl-21d* (make-instance 'lisp-exe:cmucl
                                         :exe-path "/home/anton/unpacked/cmucl-21d/bin/lisp"))


;;(run-on-many-lisps-and-openssls:clean-fasls (merge-pathnames "workdir/" *this-dir*))

(let ((*print-pretty* t))
  (format t "~S~%"
          (time
           (run-on-many-lisps-and-openssls:run
            :test-run-description '(:lib-world "quicklisp 2022-07-08 + cl+ssl.head"
                                    :contact-email "avodonosov@yandex.ru")
            :test-run-dir (merge-pathnames "workdir/" *this-dir*)
            :quicklisp-dir (merge-pathnames "quicklisp/" (user-homedir-pathname))
            ;; :cl+ssl-location (uiop:pathname-parent-directory-pathname
            ;;                   (uiop:pathname-parent-directory-pathname *this-dir*))
            :cl+ssl-location  nil ;; to use the cl+ssl version from quicklisp
            :lisps (list *sbcl-2.2.1*
                         ;*sbcl-2.2.9*
                         ;*ccl-1.11-x86-64*
                         ;*abcl-1.7.0*
                         ;*abcl-1.9.0*
                         ;*cmucl-21d*
                         )
            :openssl-releases '(
                                ;; newest releases
                                "openssl-3.0.4"
                                "openssl-1.1.1p"
                                ;; "libressl-3.5.3"

                                ;; ;; oldest releaes
                                ;; "openssl-0.9.8zh"
                                ;; "libressl-2.2.7"

                                ;; ;; the rest
                                ;; "openssl-1.1.0j"
                                ;; "openssl-1.0.2q"
                                ;; "openssl-1.0.0s"
                                ;; "libressl-3.5.3"
                                ;; "libressl-3.0.1"
                                ;; "libressl-2.8.3"
                                ;; "libressl-2.6.5"
                                ;; "libressl-2.5.5"
                                )
            :bitnesses '("64")
            :openssl-releases-dir (merge-pathnames "openssl-releases/bin/"
                                                   *this-dir*)
            ;; Since we load customly built openssl libs, it may not find the path
            ;; to trusted root serts on our system. Let's configure this path, as
            ;; we have it on my Ubunto and in the CI docker image.
            :verify-location "/etc/ssl/certs/"

            ;; TODO:
            ;; :lib-load-modes ("old" "new")
            ;; ?

            ))))

