;;;; -*- Mode: Lisp; indent-tabs-mode: nil -*-

#.(unless (or #+asdf3.1 (version<= "3.1" (asdf-version)))
    (error "You need ASDF >= 3.1 to load this system correctly."))

(defsystem :static-vectors
  :description "Create vectors allocated in static memory."
  :author "Stelian Ionescu <sionescu@cddr.org>"
  :licence "MIT"
  :version (:read-file-form "version.sexp")
  :defsystem-depends-on (#+(or abcl allegro clasp cmu ecl sbcl) :cffi-grovel)
  :depends-on (:alexandria :cffi)
  :pathname "src/"
  :components ((:file "pkgdcl")
               (:file "constantp" :depends-on ("pkgdcl"))
               #+(or abcl allegro clasp cmu ecl)
               (:cffi-grovel-file "ffi-types" :depends-on ("pkgdcl"))
               (:file "impl"
                      :depends-on ("pkgdcl" "constantp"
                                   #+(or abcl allegro cmu ecl) "ffi-types")
                      :pathname #+abcl      "impl-abcl"
                                #+allegro   "impl-allegro"
                                #+ccl       "impl-clozure"
                                #+clasp     "impl-clasp"
                                #+cmu       "impl-cmucl"
                                #+ecl       "impl-ecl"
                                #+lispworks "impl-lispworks"
                                #+sbcl      "impl-sbcl"
                                #-(or abcl allegro ccl clasp cmu ecl lispworks sbcl)
                                  #.(error "static-vectors does not support this Common Lisp implementation!"))
               (:file "constructor" :depends-on ("pkgdcl" "constantp" "impl"))
               (:file "cffi-type-translator" :depends-on ("pkgdcl" "impl")))
  :in-order-to ((test-op (test-op :static-vectors/test))))

(defsystem :static-vectors/test
  :description "Static-vectors test suite."
  :author "Stelian Ionescu <sionescu@cddr.org>"
  :licence "MIT"
  :version (:read-file-form "version.sexp")
  :depends-on (:static-vectors :fiveam)
  :pathname "tests/"
  :components ((:file "static-vectors-tests"))
  :perform (test-op (o c) (symbol-call :5am :run! :static-vectors)))
