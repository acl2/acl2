;;;; -*- Mode: Lisp; indent-tabs-mode: nil -*-

#|
Copyright 2006,2007 Greg Pfeil

Distributed under the MIT license (see LICENSE file)
|#

(eval-when (:compile-toplevel :load-toplevel :execute)
  #+allegro (require :smputil)
  #+corman  (require :threads))

(eval-when (:compile-toplevel :load-toplevel :execute)
  #+(or armedbear
        (and allegro multiprocessing)
        (and clisp mt)
        (and openmcl openmcl-native-threads)
        (and cmu mp)
        corman
        (and ecl threads)
        mkcl
        lispworks
        (and digitool ccl-5.1)
        (and sbcl sb-thread)
        scl)
  (pushnew :thread-support *features*))

(asdf:defsystem :bordeaux-threads
  :author "Greg Pfeil <greg@technomadic.org>"
  :licence "MIT"
  :description "Bordeaux Threads makes writing portable multi-threaded apps simple"
  :version #.(with-open-file
                 (vers (merge-pathnames "version.lisp-expr" *load-truename*))
               (read vers))
  :depends-on (:alexandria)
  :components ((:module "src"
                :serial t
                :components
                ((:file "pkgdcl")
                 (:file "bordeaux-threads")
                 (:file #+(and thread-support armedbear) "impl-abcl"
                        #+(and thread-support allegro)   "impl-allegro"
                        #+(and thread-support clisp)     "impl-clisp"
                        #+(and thread-support openmcl)   "impl-clozure"
                        #+(and thread-support cmu)       "impl-cmucl"
                        #+(and thread-support corman)    "impl-corman"
                        #+(and thread-support ecl)       "impl-ecl"
                        #+(and thread-support mkcl)      "impl-mkcl"
                        #+(and thread-support lispworks) "impl-lispworks"
                        #+(and thread-support digitool)  "impl-mcl"
                        #+(and thread-support sbcl)      "impl-sbcl"
                        #+(and thread-support scl)       "impl-scl"
                        #-thread-support                 "impl-null")
                 #+(and thread-support lispworks (not lispworks6))
                 (:file "impl-lispworks-condition-variables")
                 #+(and thread-support digitool)
                 (:file "condition-variables")
                 (:file "default-implementations"))))
  :in-order-to ((asdf:test-op (asdf:load-op bordeaux-threads-test)))
  :perform (asdf:test-op :after (op c)
             (asdf:oos 'asdf:test-op :bordeaux-threads-test)))
