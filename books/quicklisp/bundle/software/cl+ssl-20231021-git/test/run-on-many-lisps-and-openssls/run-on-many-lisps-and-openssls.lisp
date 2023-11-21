(ql:quickload :test-grid-agent)
(ql:quickload :test-grid-utils)
(ql:quickload :cl-fad)
(ql:quickload :alexandria)
(ql:quickload :log4cl)

(let ((*default-pathname-defaults*
        (or *load-truename*
            #P"/home/anton/my/prj/cl+ssl/cl-plus-ssl/test/run-on-many-lisps-and-openssls/")))
  (load "openssl-releases.lisp"))

(defpackage #:run-on-many-lisps-and-openssls
  (:use :common-lisp)
  (:export #:run
           #:clean-fasls))

(in-package :run-on-many-lisps-and-openssls)

(defun fasl-root (test-run-dir)
  (merge-pathnames "fasl/" test-run-dir))

(defun sanitize-as-path (str)
  ;; Substitute dots by hypens if our main process is CCL, it 
  ;; prepends the > symbol before dots;
  ;; for example: 1.1.0.36.mswinmt.1201-284e340 => 1>.1>.0>.36>.mswinmt.1201-284e340
  ;; When we pass such a pathname to other lisps, they can't handle it.
  (substitute #\- #\. str))

(defun log-name (lisp openssl-release)
  (sanitize-as-path
   (string-downcase (concatenate 'string
                                 (tg-agent::implementation-identifier lisp)
                                 "-"
                                 openssl-release))))

(defun fasl-dir (test-run-dir lisp)
  (merge-pathnames
   (format nil
           "~(~A~)/"
           (sanitize-as-path (tg-agent::implementation-identifier lisp)))
   (fasl-root test-run-dir)))

(defun run (&key test-run-description
              test-run-dir
              quicklisp-dir
              lisps
              openssl-releases
              (bitnesses '("64"))
              openssl-releases-dir
              cl+ssl-location
              verify-location)
  ;; (unless cl+ssl-location
  ;;   (error "cl+ssl-location parameter is not specified and *load-truename* was not available at the load time."))

  (ensure-directories-exist test-run-dir)
  
  (let ((lisp-exe:*temp-dir* test-run-dir))
    (flet ((run-lib-test (lisp openssl-release bitness)
             (tg-agent::proc-run-libtest
              lisp
              :cl+ssl
              (cons :lisp (cons (tg-agent::implementation-identifier lisp)
                                test-run-description))
              (merge-pathnames (log-name lisp openssl-release) test-run-dir)
              quicklisp-dir
              (fasl-dir test-run-dir lisp)
              :eval-before-test `(progn
                                   (set (read-from-string "asdf:*central-registry*")
                                        (cons ,cl+ssl-location
                                              (symbol-value (read-from-string "asdf:*central-registry*"))))
                                   ,(when cl+ssl-location
                                          `(cl-user::fncall "add-asdf-output-translation"
                                                            ,cl+ssl-location
                                                            ,(merge-pathnames "cl+ssl/" (fasl-dir test-run-dir lisp))))

                                   (cl-user::fncall "ql:quickload" :cl+ssl/config)
                                   (eval (list (read-from-string "cl+ssl/config:define-libcrypto-path")
                                               ,(my-openssl-releases:so-path openssl-releases-dir
                                                                             openssl-release
                                                                             bitness
                                                                             "libcrypto.so")))
                                   (eval (list (read-from-string "cl+ssl/config:define-libssl-path")
                                               ,(my-openssl-releases:so-path openssl-releases-dir
                                                                             openssl-release
                                                                             bitness
                                                                             "libssl.so")))

                                   ,@(when verify-location
                                       `((cl-user::fncall "ql:quickload" :cl+ssl)
                                         (cl-user::fncall "cl+ssl:ensure-initialized") ; needed to set the *ssl-global-context*
                                         (cl-user::fncall "cl+ssl::ssl-ctx-set-verify-location"
                                                          (symbol-value (read-from-string "cl+ssl::*ssl-global-context*"))
                                                          ,verify-location)))))))
      (tg-utils::write-to-file
       (alexandria:map-product (lambda (lisp openssl-release bitness)
                                 (list (tg-agent::implementation-identifier lisp)
                                       openssl-release
                                       (getf (run-lib-test lisp openssl-release bitness)
                                             :status)))
                               lisps
                               openssl-releases
                               bitnesses)
       (merge-pathnames "results.lisp" test-run-dir)))))

(defun clean-fasls (test-run-dir)
  (cl-fad:delete-directory-and-files (fasl-root test-run-dir)))
