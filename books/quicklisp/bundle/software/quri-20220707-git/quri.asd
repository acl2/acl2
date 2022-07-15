(defsystem "quri"
  :version "0.6.0"
  :author "Eitaro Fukamachi"
  :maintainer "Pierre Neidhardt"
  :license "BSD 3-Clause"
  :depends-on ("babel"
               "alexandria"
               "split-sequence"
               "cl-utilities"
               #+sbcl "sb-cltl2")
  :components ((:module "src"
                :components
                ((:file "quri" :depends-on ("uri" "uri-classes" "domain" "parser" "decode" "encode" "error"))
                 (:file "uri" :depends-on ("port"))
                 (:module "uri-classes"
                  :pathname "uri"
                  :depends-on ("uri" "port" "encode" "decode")
                  :components
                  ((:file "ftp")
                   (:file "http")
                   (:file "ldap")
                   (:file "file")))
                 (:file "domain" :depends-on ("uri" "etld"))
                 (:file "etld")
                 (:file "parser" :depends-on ("error" "util"))
                 (:file "decode" :depends-on ("error" "util"))
                 (:file "encode" :depends-on ("error" "util"))
                 (:file "port")
                 (:file "util")
                 (:file "error"))))
  :description "Yet another URI library for Common Lisp"
  :in-order-to ((test-op (test-op "quri-test"))))
