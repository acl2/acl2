(in-package :cl-user)
(defpackage :alexandria-2
  (:nicknames :alexandria.2)
  (:use :cl :alexandria.1.0.0)
  #+sb-package-locks
  (:lock t)
  (:export
   ;; arrays
   #:dim-in-bounds-p
   #:row-major-index
   #:rmajor-to-indices
   ;; lists
   #:delete-from-plist*
   ;; control-flow
   #:line-up-first
   #:line-up-last
   #:subseq*
    . #. (let (res) (do-external-symbols (sym :alexandria.1.0.0) (push sym res)) res)
   ))
