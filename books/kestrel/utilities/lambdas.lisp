; Utilities for dealing with lambdas
;
; Copyright (C) 2015-2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Main Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/utilities/forms" :dir :system)

;; Basically the same as lambda-formals, but this one is a function, so we can
;; disable it.
(defund ulambda-formals (fn)
  (declare (xargs :guard ;(untranslated-lambda-exprp fn)
                  (true-listp fn)))
  (farg1 fn))

;; These will be IGNORE or IGNORABLE declares.
;; I think only untranslated lambdas have them (translated lambdas seem to do it with HIDE).
(defund ulambda-declares (fn)
  (declare (xargs :guard ;(untranslated-lambda-exprp fn)
                  (true-listp fn)
                  ))
  (butlast (rest (fargs fn)) 1))

;; Get the body of an untranslated lambda.  Note that it may be preceeded by
;; declares.
(defund ulambda-body (fn)
  (declare (xargs :guard ;(untranslated-lambda-exprp fn)
                  (true-listp fn)
                  ))
  (car (last (fargs fn))))

(defthm acl2-count-of-ulambda-body-linear-weak
  (<= (acl2-count (ulambda-body term))
      (acl2-count term))
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable ulambda-body))))

(defund make-ulambda (formals declares body)
  (declare (xargs :guard (true-listp declares))) ;strengthen?
  `(lambda ,formals ,@declares ,body))
