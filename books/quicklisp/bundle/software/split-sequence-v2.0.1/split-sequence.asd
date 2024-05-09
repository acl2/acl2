;;; -*- Lisp -*-

#.(unless (or #+asdf3.1 (version<= "3.1" (asdf-version)))
    (error "You need ASDF >= 3.1 to load this system correctly."))

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
               (:file "documentation"))
  :in-order-to ((test-op (test-op :split-sequence/tests))))

(defsystem :split-sequence/tests
  :author "Arthur Lemmens <alemmens@xs4all.nl>"
  :maintainer "Sharp Lispers <sharplispers@googlegroups.com>"
  :description "Split-Sequence test suite"
  :license "MIT"
  :depends-on (:split-sequence :fiveam)
  :components ((:file "tests"))
  :perform (test-op (o c) (symbol-call :5am :run! :split-sequence)))
