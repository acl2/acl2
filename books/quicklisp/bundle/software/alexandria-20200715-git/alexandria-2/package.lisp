(in-package :cl-user)
(defpackage :alexandria-2
  (:nicknames :alexandria.2)
  (:use :cl :alexandria.1.0.0)
  #+sb-package-locks
  (:lock t)
  (:export
   #:delete-from-plist*
   #:line-up-first
   #:line-up-last
    . #. (let (res) (do-external-symbols (sym :alexandria.1.0.0) (push sym res)) res)
   ))
