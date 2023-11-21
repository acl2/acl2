;;;; -*- Mode: LISP; Base: 10; Syntax: ANSI-Common-lisp; -*-
;;;;
;;;; See the LICENSE file for licensing information.

(in-package :asdf)

;;; NOTE: the key "art" here is, no need to recompile any file when switching
;;; between a native backend and IOlib backend. -- Chun Tian (binghe)

#+sample
(pushnew :usocket-iolib *features*)

(defsystem usocket
    :name "usocket (client, with server symbols)"
    :author "Erik Enge & Erik Huelsmann"
    :maintainer "Chun Tian (binghe) & Hans Huebner"
    :version (:read-file-form "version.sexp")
    :licence "MIT"
    :description "Universal socket library for Common Lisp"
    :depends-on (:split-sequence
                 (:feature (:and (:or :sbcl :ecl)
                                 (:not :usocket-iolib))
                  :sb-bsd-sockets)
                 (:feature :usocket-iolib
                  :iolib))
    :components ((:file "package")
                 (:module "vendor" :depends-on ("package")
                  :if-feature :mcl
                  :components ((:file "kqueue")
                               (:file "OpenTransportUDP")))
                 (:file "usocket" :depends-on ("vendor"))
                 (:file "condition" :depends-on ("usocket"))
                 (:module "backend"
                  :depends-on ("condition")
                  :components ((:file "iolib"
                                :if-feature :usocket-iolib)
                               (:file "abcl"
                                :if-feature (:and :abcl
                                                  (:not :usocket-iolib)))
                               (:file "allegro"
                                :if-feature (:and (:or :allegro :cormanlisp)
                                                  (:not :usocket-iolib)))
                               (:file "clisp"
                                :if-feature (:and :clisp
                                                  (:not :usocket-iolib)))
                               (:file "openmcl"
                                :if-feature (:and (:or :openmcl :clozure)
                                                  (:not :usocket-iolib)))
                               (:file "clozure"
                                :if-feature (:and :clozure
                                                  (:not :usocket-iolib))
                                :depends-on ("openmcl"))
                               (:file "cmucl"
                                :if-feature (:and :cmu
                                                  (:not :usocket-iolib)))
                               (:file "sbcl"
                                :if-feature (:and (:or :sbcl :ecl :clasp)
                                                  (:not :usocket-iolib)))
                               (:file "ecl"
                                :if-feature (:and :ecl
                                                  (:not :usocket-iolib))
                                :depends-on ("sbcl"))
                               (:file "clasp"
                                :if-feature (:and :clasp
                                                  (:not :usocket-iolib))
                                :depends-on ("sbcl"))
                               (:file "lispworks"
                                :if-feature (:and :lispworks
                                                  (:not :usocket-iolib)))
                               (:file "mcl"
                                :if-feature (:and :mcl
                                                  (:not :usocket-iolib)))
                               (:file "mocl"
                                :if-feature (:and :mocl
                                                  (:not :usocket-iolib)))
                               (:file "scl"
                                :if-feature (:and :scl
                                                  (:not :usocket-iolib)))
                               (:file "genera"
                                :if-feature (:and :genera
                                                  (:not :usocket-iolib)))
                               (:file "mezzano"
                                :if-feature (:and :mezzano))))
                 (:file "option"
                  :if-feature (:not :usocket-iolib)
                  :depends-on ("backend")))
    :in-order-to ((test-op (test-op :usocket-test))))
