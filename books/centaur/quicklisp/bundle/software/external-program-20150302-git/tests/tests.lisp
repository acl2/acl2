(defpackage external-program-tests
  (:use #:cl #:external-program #:fiveam)
  (:shadow #:run))

(in-package #:external-program-tests)

(def-suite tests)

(in-suite tests)

;;; FIXME: should probably signal a condition if program isn't found
;;; ... but can't guarantee that 71 isn't returned by the program
;;; itself ...
(test should-have-access-to-shell-builtins
  (multiple-value-bind (status code)
      (external-program:run "cd" '())
    (is (eq :exited status))
    (is (= 0 code))))

(test should-discover-programs-in-path
  (multiple-value-bind (status code)
      (external-program:run "which" '("ls"))
    (is (eq :exited status))
    (is (= 0 code))))

(test should-be-able-to-use-pathname-as-program
  (multiple-value-bind (status code)
      (external-program:run (make-pathname :name "ls") '("."))
    (is (eq :exited status))
    (is (= 0 code))))

(test should-be-able-to-use-pathnames-as-args
  (multiple-value-bind (status code)
      (external-program:run "ls"
                            (list (merge-pathnames (make-pathname :name nil)
                                                   #.*compile-file-truename*)))
    (is (eq :exited status))
    (is (= 0 code))))

(test should-be-able-to-use-numbers-as-args
  (multiple-value-bind (status code)
      (external-program:run "grep"
                            '("-C" 3 "should" #.*compile-file-truename*))
    (is (eq :exited status))
    (is (= 0 code))))

(test should-allow-spaces-in-args
  (multiple-value-bind (status code)
      (external-program:run "grep"
                            '("should probably" #.*compile-file-truename*))
    (is (eq :exited status))
    (is (= 0 code))))

(test environment-vars-should-override-existing
  (multiple-value-bind (status code)
      (external-program:run "which" '("which") :environment '(("PATH" . "")))
    (is (eq :exited status))
    (is (/= 0 code))))

(test empty-env-should-erase-all
  (multiple-value-bind (status code)
      (external-program:run "ls" '(".") :replace-environment-p t)
    (is (eq :exited status))
    (is (/= 0 code))))
