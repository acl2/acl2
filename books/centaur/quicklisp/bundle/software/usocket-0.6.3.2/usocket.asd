;;;; -*- Mode: Lisp -*-
;;;;
;;;; See the LICENSE file for licensing information.

(defsystem usocket
    :name "usocket"
    :author "Erik Enge & Erik Huelsmann"
    :maintainer "Chun Tian (binghe) & Hans Huebner"
    :version "0.6.3.2"
    :licence "MIT"
    :description "Universal socket library for Common Lisp"
    :depends-on (#+(or sbcl ecl) :sb-bsd-sockets)
    :components ((:file "package")
		 (:module "vendor" :depends-on ("package")
		  :components (#+mcl (:file "kqueue")
			       #+mcl (:file "OpenTransportUDP")
			       (:file "spawn-thread")
			       (:file "split-sequence")))
		 (:file "usocket" :depends-on ("vendor"))
		 (:file "condition" :depends-on ("usocket"))
		 (:module "backend" :depends-on ("condition")
		  :components (#+abcl		(:file "abcl")
			       #+(or allegro cormanlisp)
						(:file "allegro")
			       #+clisp		(:file "clisp")
			       #+clozure	(:file "clozure" :depends-on ("openmcl"))
			       #+cmu		(:file "cmucl")
			       #+ecl		(:file "ecl" :depends-on ("sbcl"))
			       #+lispworks	(:file "lispworks")
			       #+mcl		(:file "mcl")
			       #+mocl		(:file "mocl")
			       #+openmcl	(:file "openmcl")
			       #+(or ecl sbcl)	(:file "sbcl")
			       #+scl		(:file "scl")))
		 (:file "option" :depends-on ("backend"))
		 (:file "server" :depends-on ("backend" "option"))))

(defmethod perform ((op test-op) (c (eql (find-system :usocket))))
  (oos 'load-op :usocket-test)
  (oos 'test-op :usocket-test))
