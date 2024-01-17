;;;; -*- Mode: LISP; Syntax: ANSI-Common-lisp; Base: 10; Package: ASDF -*-
;;;; The above modeline is required for Genera. Do not change.

#.(unless (or #+asdf3.1 (version<= "3.1" (asdf-version)))
    (error "You need ASDF >= 3.1 to load this system correctly."))

(eval-when (:compile-toplevel :load-toplevel :execute)
  #+(or armedbear
        (and allegro multiprocessing)
        (and clasp threads)
        (and clisp mt)
        (and openmcl openmcl-native-threads)
        (and cmu mp)
        corman
        (and ecl threads)
        genera
        mezzano
        mkcl
        lispworks
        (and digitool ccl-5.1)
        (and sbcl sb-thread)
        scl)
  (pushnew :thread-support *features*))

#-thread-support
(error "This implementation is unsupported.")

(defsystem :bordeaux-threads
  :author "Stelian Ionescu <sionescu@cddr.org>"
  :licence "MIT"
  :description "Bordeaux Threads makes writing portable multi-threaded apps simple."
  :version (:read-file-form "version.sexp")
  :depends-on (:alexandria :global-vars :trivial-features :trivial-garbage
                           #+(and allegro (version>= 9)) (:require "smputil")
                           #+(and allegro (not (version>= 9))) (:require "process")
                           (:feature :corman (:require "threads")))
  :components ((:static-file "version.sexp")
               (:module "api-v1"
                :pathname "apiv1/"
                :serial t
                :components
                        ((:file "pkgdcl")
                         (:file "bordeaux-threads")
                         (:file "impl-abcl" :if-feature :armedbear)
                         (:file "impl-allegro" :if-feature :allegro)
                         (:file "impl-clasp" :if-feature :clasp)
                         (:file "impl-clisp" :if-feature :clisp)
                         (:file "impl-clozure" :if-feature :openmcl)
                         (:file "impl-cmucl" :if-feature :cmu)
                         (:file "impl-corman" :if-feature :corman)
                         (:file "impl-ecl" :if-feature :ecl)
                         (:file "impl-genera" :if-feature :genera)
                         (:file "impl-mezzano" :if-feature :mezzano)
                         (:file "impl-mkcl" :if-feature :mkcl)
                         (:file "impl-lispworks" :if-feature :lispworks)
                         (:file "impl-mcl" :if-feature :digitool)
                         (:file "impl-sbcl" :if-feature :sbcl)
                         (:file "impl-scl" :if-feature :scl)
                         (:file "impl-lispworks-condition-variables" :if-feature (:and :lispworks
                                                                                       (:or :lispworks4 :lispworks5)))
                         (:file "condition-variables" :if-feature :digitool)
                         (:file "default-implementations")))
               (:module "api-v2"
                :pathname "apiv2/"
                :depends-on ("api-v1")
                :serial t
                :components
                        ((:file "pkgdcl")
                         (:file "bordeaux-threads")
                         (:file "timeout-interrupt")
                         (:file "impl-abcl" :if-feature :abcl)
                         (:file "impl-allegro" :if-feature :allegro)
                         (:file "impl-clasp" :if-feature :clasp)
                         (:file "impl-clisp" :if-feature :clisp)
                         (:file "impl-clozure" :if-feature :clozure)
                         (:file "impl-cmucl" :if-feature :cmu)
                         (:file "impl-corman" :if-feature :corman)
                         (:file "impl-ecl" :if-feature :ecl)
                         (:file "impl-genera" :if-feature :genera)
                         (:file "impl-mezzano" :if-feature :mezzano)
                         (:file "impl-mkcl" :if-feature :mkcl)
                         (:file "impl-lispworks" :if-feature :lispworks)
                         (:file "impl-mcl" :if-feature :digitool)
                         (:file "impl-sbcl" :if-feature :sbcl)
                         (:file "impl-scl" :if-feature :scl)
                         (:file "atomics" :if-feature (:not :abcl))
                         (:file "atomics-java" :if-feature :abcl)
                         (:file "api-locks")
                         (:file "api-threads")
                         (:file "api-semaphores")
                         (:file "impl-condition-variables-semaphores"
                          :if-feature :ccl)
                         (:file "api-condition-variables"))))
  :in-order-to ((test-op (test-op :bordeaux-threads/test))))

(defsystem :bordeaux-threads/test
  :author "Stelian Ionescu <sionescu@cddr.org>"
  :description "Bordeaux Threads test suite."
  :licence "MIT"
  :version (:read-file-form "version.sexp")
  :depends-on (:bordeaux-threads :fiveam)
  :pathname "test/"
  :serial t
  :components ((:file "tests-v1")
               (:file "pkgdcl")
               (:file "not-implemented")
               (:file "tests-v2"))
  :perform (test-op (o c)
             (symbol-call :5am :run! :bordeaux-threads)
             (symbol-call :5am :run! :bordeaux-threads-2)))
