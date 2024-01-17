(defpackage #:my-openssl-releases
  (:export #:so-path)
  (:use :common-lisp))

(in-package #:my-openssl-releases)

(defun so-path (openssl-releases-dir openssl-release bitness so-name)
  (merge-pathnames (format nil
                           "~A-~Abit/lib~A/~A"
                           openssl-release
                           bitness
                           (if (and (string= "64" bitness)
                                    (search "openssl-3." openssl-release))
                               "64"
                               "")
                           so-name)
                   openssl-releases-dir))


