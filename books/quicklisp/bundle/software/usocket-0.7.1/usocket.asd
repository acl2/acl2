;;;; -*- Mode: Lisp -*-
;;;;
;;;; See the LICENSE file for licensing information.

(in-package :asdf)

(defsystem #:usocket
    :name "usocket (client, with server symbols)"
    :author "Erik Enge & Erik Huelsmann"
    :maintainer "Chun Tian (binghe) & Hans Huebner"
    :version (:read-file-form "version.sexp")
    :licence "MIT"
    :description "Universal socket library for Common Lisp"
    :depends-on (:split-sequence
		 #+(or sbcl ecl) :sb-bsd-sockets
		 )
    :components ((:file "package")
		 (:module "vendor" :depends-on ("package")
		  :components (#+mcl (:file "kqueue")
			       #+mcl (:file "OpenTransportUDP")))
		 (:file "usocket" :depends-on ("vendor"))
		 (:file "condition" :depends-on ("usocket"))
		 (:module "backend" :depends-on ("condition")
		  :components (#+abcl		(:file "abcl")
			       #+(or allegro cormanlisp)
						(:file "allegro")
			       #+clisp		(:file "clisp")
			       #+(or openmcl clozure)
						(:file "openmcl")
			       #+clozure	(:file "clozure" :depends-on ("openmcl"))
			       #+cmu		(:file "cmucl")
			       #+(or sbcl ecl)	(:file "sbcl")
			       #+ecl		(:file "ecl" :depends-on ("sbcl"))
			       #+lispworks	(:file "lispworks")
			       #+mcl		(:file "mcl")
			       #+mocl		(:file "mocl")
			       #+scl		(:file "scl")
			       #+genera		(:file "genera")))
		 (:file "option" :depends-on ("backend"))
		 ))

(defmethod perform ((op test-op) (c (eql (find-system :usocket))))
  (oos 'load-op :usocket-server)
  (oos 'load-op :usocket-test)
  (oos 'test-op :usocket-test))
