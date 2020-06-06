;;; -*- Lisp -*-

(defsystem :split-sequence
  :author "Arthur Lemmens <alemmens@xs4all.nl>"
  :maintainer "Sharp Lispers <sharplispers@googlegroups.com>"
  :description "Splits a sequence into a list of subsequences
  delimited by objects satisfying a test."
  :license "MIT"
  :version (:read-file-form "version.sexp")
  :components ((:static-file "version.sexp")
               (:file "package")
               (:file "vector")
               (:file "list")
               (:file "extended-sequence" :if-feature (:or :sbcl :abcl))
               (:file "api")
               (:file "documentation")))

(defsystem :split-sequence/tests
  :author "Arthur Lemmens <alemmens@xs4all.nl>"
  :maintainer "Sharp Lispers <sharplispers@googlegroups.com>"
  :description "Split-Sequence test suite"
  :license "MIT"
  :depends-on (:split-sequence :fiveam)
  :components ((:file "tests")))

(defmethod perform ((o test-op) (c (eql (find-system :split-sequence))))
  (load-system :split-sequence/tests)
  (symbol-call :5am :run! :split-sequence))
