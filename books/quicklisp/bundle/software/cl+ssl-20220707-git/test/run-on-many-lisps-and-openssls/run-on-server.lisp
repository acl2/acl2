(defparameter *this-dir*
  (if *load-truename*
      (make-pathname :name nil :type nil :defaults *load-truename*)
      ;; for slime:
      #P"/home/testgrid/cl+ssl/cl-plus-ssl/test/run-on-many-lisps-and-openssls/"))

(pushnew "/home/testgrid/cl-test-grid/" asdf:*central-registry* :test #'equal)

(load (merge-pathnames "run-on-many-lisps-and-openssls.lisp" *this-dir*))


(defparameter *abcl-1.5.0*
  (make-instance 'lisp-exe:abcl
                 :java-exe-path "java"
                 :abcl-jar-path "/home/testgrid/lisps/abcl-bin-1.5.0/abcl.jar"))

(defparameter *acl-10.0*
  (make-instance 'lisp-exe:acl
                 :exe-path "/home/testgrid/lisps/acl100/alisp"))

(defparameter *acl-10.0m*
  (make-instance 'lisp-exe:acl
                 :exe-path "/home/testgrid/lisps/acl100/mlisp"))

(defparameter *acl-10.0-smp*
  (make-instance 'lisp-exe:acl
                 :exe-path "/home/testgrid/lisps/acl100-smp/alisp"))

(defparameter *acl-10.0m-smp*
  (make-instance 'lisp-exe:acl
                 :exe-path "/home/testgrid/lisps/acl100-smp/mlisp"))

(defparameter *ccl-1.11.5*
  (make-instance 'lisp-exe:ccl
                 :exe-path "/home/testgrid/lisps/ccl-1.11.5/lx86cl"))

(defparameter *sbcl-1.3.21*
  (make-instance 'lisp-exe:sbcl
                 :exe-path "/home/testgrid/lisps/sbcl-bin-1.3.21/run.sh"))

(defparameter *cmucl-2016-12*
  (make-instance 'lisp-exe:cmucl
                 :exe-path "/home/testgrid/lisps/cmucl-2016-12/bin/lisp"))

(defparameter *cmucl-2016-12*
  (make-instance 'lisp-exe:cmucl
                 :exe-path "/home/testgrid/lisps/cmucl-2016-12/bin/lisp"))

(defparameter *cmucl-21d*
  (make-instance 'lisp-exe:cmucl
                 :exe-path "/home/testgrid/lisps/cmucl-21d/bin/lisp"))

(defparameter *ecl-16.1.2-bytecode*
  (make-instance 'lisp-exe:ecl
                 :exe-path "/home/testgrid/lisps/ecl-bin-16.1.2/bin/ecl"
                 :compiler :bytecode))

(defparameter *ecl-16.1.2-lisp-to-c*
  (make-instance 'lisp-exe:ecl
                 :exe-path "/home/testgrid/lisps/ecl-bin-16.1.2/bin/ecl"
                 :compiler :lisp-to-c))

(defparameter *clisp*
  (make-instance 'lisp-exe:clisp :exe-path "/usr/bin/clisp"))

(run-on-many-lisps-and-openssls:clean-fasls (merge-pathnames "workdir/" *this-dir*))

(let ((*print-pretty* t))
  (format t "~%~S~%"
          (time
           (run-on-many-lisps-and-openssls:run
            :test-run-description '(:lib-world "quicklisp 2019-01-07 + cl+ssl.head"
                                    :contact-email "avodonosov@yandex.ru")
            :test-run-dir (merge-pathnames "workdir/" *this-dir*)
            :quicklisp-dir (merge-pathnames "quicklisp/" (user-homedir-pathname))
            ;; if we want the cl+ssl from the parent folder
            :cl+ssl-location (uiop:pathname-parent-directory-pathname
                               (uiop:pathname-parent-directory-pathname *this-dir*))
            ;; if we want the cl+ssl version from quicklisp
            ;:cl+ssl-location  nil

            :lisps (list *sbcl-1.3.21*
                         *ccl-1.11.5*
                         *abcl-1.5.0*
                         *acl-10.0* *acl-10.0m* *acl-10.0-smp* *acl-10.0m-smp*
                         *clisp*
                         *ecl-16.1.2-bytecode*
                         *ecl-16.1.2-lisp-to-c*
                         *cmucl-21d*
                         )

            :openssl-releases '("openssl-0.9.8zh"
                                "openssl-1.0.0s"
                                "openssl-1.0.2q"
                                "openssl-1.1.0j"
                                "openssl-1.1.1a"
                                )
            :openssl-releases-dir (merge-pathnames "openssl-releases/bin/"
                                                   *this-dir*)))))

