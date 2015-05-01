#+xcvb (module (:depends-on ("package")))

(in-package :cl+ssl)

(defconstant +initial-buffer-size+ 2048)

(declaim
 (inline
  make-buffer
  buffer-length
  buffer-elt
  set-buffer-elt
  s/b-replace
  b/s-replace))
