; Lists of symbols related to importing and legal variable names
;
; Copyright (C) 2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; See also imported-symbols-theorems.lisp

(include-book "map-symbol-name")

;;;
;;; common-lisp-symbols-from-main-lisp-package
;;;

;; These are the symbols imported into the ACL2 package from the COMMON-LISP
;; package.  Using this function can prevent the large constant list from
;; showing up in proofs.
(defund common-lisp-symbols-from-main-lisp-package ()
  (declare (xargs :guard t))
  *common-lisp-symbols-from-main-lisp-package*)

;; Keep this from expanding, since it is a large list:
(in-theory (disable (:e common-lisp-symbols-from-main-lisp-package)))


;;;
;;; common-lisp-specials-and-constants
;;;

;; Using this function can prevent the large constant list from showing up in
;; proofs.
(defund common-lisp-specials-and-constants ()
  (declare (xargs :guard t))
  *common-lisp-specials-and-constants*)

;; Keep this from expanding, since it is a large list:
(in-theory (disable (:e common-lisp-specials-and-constants)))

;;;
;;; legal-vars-in-common-lisp-package
;;;

;; This list contains the legal variable names in the COMMON-LISP package.  See
;; legal-variablep and legal-variablep-namep-alt-def.  Using this function can
;; prevent the large constant list from showing up in proofs.
(defund legal-vars-in-common-lisp-package ()
  (declare (xargs :guard t
                  :guard-hints (("Goal" :in-theory
                                 (enable (:e common-lisp-symbols-from-main-lisp-package)
                                         (:e common-lisp-specials-and-constants))))))
  (set-difference-eq (common-lisp-symbols-from-main-lisp-package)
                     (common-lisp-specials-and-constants)))

;; Keep this from expanding, since it is a large list:
(in-theory (disable (:e legal-vars-in-common-lisp-package)))

;;;
;;; names-of-common-lisp-specials-and-constants ()
;;;

;; Returns a list of strings
(defund names-of-common-lisp-specials-and-constants ()
  (declare (xargs :guard t
                  :guard-hints (("Goal" :in-theory (enable (:e common-lisp-specials-and-constants))))))
  (map-symbol-name (common-lisp-specials-and-constants)))

;; Keep this from expanding, since it is a large list:
(in-theory (disable (:e names-of-common-lisp-specials-and-constants)))
