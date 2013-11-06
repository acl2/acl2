#|-*-Lisp-*-=================================================================|#
#|                                                                           |#
#| coi: Computational Object Inference                                       |#
#|                                                                           |#
#|===========================================================================|#
;; compatibility.lisp
;; Macros for compatibility with old names 
;;
;; bzo (jcd) - we want to eventually remove this file and switch to using the
;; standard names.

(in-package "PATH")
(include-book "../alists/top")

(defmacro keys (x)
  `(strip-cars ,x))

(add-macro-alias keys strip-cars)

(defmacro vals (x)
  `(strip-cdrs ,x))

(add-macro-alias vals strip-cdrs)

(defmacro clr-key (k x)
  `(ALIST::clearkey ,k ,x))

(add-macro-alias clr-key ALIST::clearkey)

(defmacro remove-shadowed-pairs (x)
  `(ALIST::deshadow ,x))

(add-macro-alias remove-shadowed-pairs ALIST::deshadow)

(defmacro range (x)
  `(vals (remove-shadowed-pairs ,x)))

(defmacro pre-image-aux (k x)
  `(ALIST::preimage-aux ,k ,x))

(add-macro-alias pre-image-aux ALIST::preimage-aux)

(defmacro pre-image (k x)
  `(ALIST::preimage ,k ,x))

(add-macro-alias pre-image ALIST::preimage)
