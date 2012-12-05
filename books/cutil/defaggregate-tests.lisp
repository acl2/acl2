; Tests for defaggregate utility.  Consider moving tests from the bottom of
; defaggregate.lisp into this file.

(in-package "CUTIL")

(include-book "defaggregate")
(include-book "deflist")

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

(mutual-recursion
 (DEFUND FOO-P (X)
   (DECLARE (XARGS :GUARD T))
   (AND (CONSP X)
        (EQ (CAR X) :FOO)
        (ALISTP (CDR X))
        (CONSP (CDR X))
        (LET ((BAR (CDR (ASSOC 'BAR (CDR X)))))
             (DECLARE (IGNORABLE BAR))
             (AND (FOO-LIST-P BAR)))))

 (DEFUND FOO-LIST-P (X)
   (DECLARE (XARGS :GUARD T
                   :NORMALIZE NIL
                   :VERIFY-GUARDS T
                   :GUARD-DEBUG NIL
                   :GUARD-HINTS NIL))
   (IF (CONSP X)
       (AND (FOO-P (CAR X))
            (FOO-LIST-P (CDR X)))
       (NULL X))))

(cutil::defaggregate foo
  (bar)
  :require ((foo-list-p-of-foo->bar
             (foo-list-p bar)))
  :already-definedp t
  :tag :foo)

(cutil::deflist foo-list-p (x)
  (foo-p x)
  :elementp-of-nil nil
  :already-definedp t
  :true-listp t)
