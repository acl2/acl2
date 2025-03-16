; Copyright (C) 2025, Matt Kaufmann
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

(defconst *zf-symbols*
  (set-difference-eq
   (append '(x y z ; variable names
               add-to-set-eq-exec
               append? bad-atom
               conjoin-untranslated-terms error1-state-p
               fix-intern-in-pkg-of-sym formals fquotep get-event packn
               packn-pos pairlis-x1 pairlis-x2 strip-cadrs string-suffixp
               variablep
; For table events:
               val key)
           (union-eq *acl2-exports*
                     *common-lisp-symbols-from-main-lisp-package*))
   '(apply omega union fn-equal map
; The following probably needn't be included (for exclusion) here, but since
; their names are similar to common ZF function symbols, we do so to avoid
; potential user confusion.
           subsetp functionp
           )))

(defpkg "ZF"
  *zf-symbols*)
