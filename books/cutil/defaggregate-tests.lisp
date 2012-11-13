; Tests for defaggregate utility.  Consider moving tests from the bottom of
; defaggregate.lisp into this file.

(in-package "CUTIL")

(include-book "defaggregate")

(encapsulate
 ()

 (defn foof-p (x)
   (keywordp x))

 (defmacro foom-p (x)
   (keywordp x))

 (defaggregate containerf
   (thing)
   :require ((foof-p-of-containerf->thing
              (foof-p thing)))
   :tag :containerf)

; The following defaggregate call is commented out because using a macro, as is
; done in the following example, results in a rewrite rule that is
; unacceptable.  Here is the error:

;;; ACL2 Error in ( DEFTHM FOOM-P-OF-CONTAINERM->THING ...):  A :REWRITE
;;; rule generated from FOOM-P-OF-CONTAINERM->THING is illegal because
;;; it rewrites the quoted constant 'NIL.  See :DOC rewrite.

 ;; (defaggregate containerm
 ;;   (thing)
 ;;   :require ((foom-p-of-containerm->thing
 ;;              (foom-p thing)))
 ;;   :tag :containerm)

 ) ; encapsulate
