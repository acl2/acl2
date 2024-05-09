; Standard System Library
;
; Copyright (C) 2023, ForrestHunt, Inc.
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; Contributing Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "xdoc/constructors" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection guard-theorem-no-simplify
  :parents (std/system/function-queries)
  :short "A version of @(tsee guard-theorem) that does no simplification."
  :long
  (xdoc::topstring
   (xdoc::p
    "This definition is based on
     the definition of ACL2 source function @('guard-theorem'),
     with the @('simplify') argument set to @('nil'),
     with no state argument,
     and with new @('safe-mode') and @('gc-off') arguments;
     the latter two can reasonably be
     @('(f-get-global \'safe-mode state)') and @('(gc-off state)'),
     respectively.")
   (xdoc::p
    "An advantage of not having the state argument is that
     this function can be called via @(tsee magic-ev-fncall)."))

  (defun guard-theorem-no-simplify (fn guard-debug wrld safe-mode gc-off)
    (declare (xargs :mode :program))
    (cond
     ((not (getpropc fn 'unnormalized-body nil wrld))
      *t*)
     (t
      (let ((names (or (getpropc fn 'recursivep nil wrld)
                       (list fn))))
        (mv-let (cl-set ttree)
            (guard-clauses-for-clique names
                                      guard-debug
                                      :DO-NOT-SIMPLIFY ; ens
                                      wrld
                                      safe-mode
                                      gc-off
                                      nil)
; Note that ttree is assumption-free; see guard-clauses-for-clique.
          (declare (ignore ttree)) ; assumption-free
          (termify-clause-set cl-set)))))))
