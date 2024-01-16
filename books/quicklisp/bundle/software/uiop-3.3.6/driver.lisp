;;;; ---------------------------------------------------------------------------
;;;; Re-export all the functionality in UIOP

(uiop/package:define-package :uiop/driver
  (:nicknames :uiop ;; Official name we recommend should be used for all references to uiop symbols.
              :asdf/driver) ;; DO NOT USE, a deprecated name, not supported anymore.
  ;; We should remove the name :asdf/driver at some point,
  ;; but not until it has been eradicated from Quicklisp for a year or two.
  ;; The last known user was cffi (PR merged in May 2020).
  (:use :uiop/common-lisp)
  ;; NB: We are not reexporting uiop/common-lisp
  ;; which include all of CL with compatibility modifications on select platforms,
  ;; because that would cause potential conflicts for packages that
  ;; might want to :use (:cl :uiop) or :use (:closer-common-lisp :uiop), etc.
  (:use-reexport
   :uiop/package* :uiop/utility :uiop/version
   :uiop/os :uiop/pathname :uiop/filesystem :uiop/stream :uiop/image
   :uiop/launch-program :uiop/run-program
   :uiop/lisp-build :uiop/configuration :uiop/backward-driver))

;; Provide both lowercase and uppercase, to satisfy more implementations.
(provide "uiop") (provide "UIOP")
