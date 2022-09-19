;;;; -*- Mode: Lisp -*-
;;;;
;;;; See the LICENSE file for licensing information.

(in-package :asdf)

(defsystem usocket-server
    :name "usocket (server)"
    :author "Chun Tian (binghe)"
    :version (:read-file-form "version.sexp")
    :licence "MIT"
    :description "Universal socket library for Common Lisp (server side)"
    :depends-on (:usocket :bordeaux-threads)
    :components ((:file "server")))
