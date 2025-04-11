; Copyright (C) 2025, Matt Kaufmann
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; The "ZF" package imports the usual "ACL2" symbols, except for a few
; exceptions as explained below.

(defconst *zf-symbols*
  (set-difference-eq
   (append

; The symbols in the following list are useful in the ZF work, so we import
; them.

    '(add-to-set-eq-exec
      append? bad-atom
      conjoin-untranslated-terms error1-state-p
      fix-intern-in-pkg-of-sym formals fquotep get-event packn
      packn-pos pairlis-x1 pairlis-x2 strip-cadrs string-suffixp
      variablep
; For table events:
      val key)
    (union-eq *acl2-exports*
              *common-lisp-symbols-from-main-lisp-package*))

; We exclude the symbols below to avoid conflicts.  Actually subsetp and
; functionp need not be exclueded, but since their names are similar to common
; ZF function symbols, we exclude them as well so as to avoid potential user
; confusion.

   '(apply omega union fn-equal map
           subsetp functionp
           )))

(defpkg "ZF"
  *zf-symbols*)
