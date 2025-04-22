; An evaluator for JVM code lifting
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2025 Kestrel Institute
; Copyright (C) 2016-2020 Kestrel Technology, LLC
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; TODO: Consider adding functions like jvm::method-program

(include-book "../evaluator-basic")
(include-book "../axe-syntax") ; for work-hard
(include-book "kestrel/bv-lists/bv-array-read-chunk-little" :dir :system)

;(local (in-theory (disable true-listp)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defconst *axe-evaluator-jvm-fns-and-aliases*
  (append '((strip-cars strip-cars-unguarded)
            (strip-cdrs strip-cdrs-unguarded)
            (no-duplicatesp-equal no-duplicatesp-equal-unguarded)
            work-hard ; no special treatent for work-hard in the rewriter, but we may nee to evaluate it on constants
            )
          *axe-evaluator-basic-fns-and-aliases*))

;; Creates acl2::eval-axe-evaluator-jvm, etc. ;; todo: package
;; Makes the evaluator (also checks that each alias given is equivalent to its function):
(make-evaluator-simple jvm *axe-evaluator-jvm-fns-and-aliases*)
