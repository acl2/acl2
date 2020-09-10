; Standard System Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "std/util/define" :dir :system)
(include-book "xdoc/constructors" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define if-tree-leaf-terms ((term pseudo-termp))
  :returns (leaf-terms pseudo-term-listp :hyp :guard)
  :parents (std/system/term-queries)
  :short "Collect the leaf terms
          according to the @(tsee if) tree structure of a term."
  :long
  (xdoc::topstring
   (xdoc::p
    "If @('term') is not a call of @(tsee if),
     we return the singleton list with  @('term') as the only leaf.")
   (xdoc::p
    "If @('term') has the form @('(if a b c)'),
     we recursively collect the leaves of @('b') of @('c'),
     and join them into a list."))
  (cond ((variablep term) (list term))
        ((fquotep term) (list term))
        ((eq (ffn-symb term) 'if)
         (append (if-tree-leaf-terms (fargn term 2))
                 (if-tree-leaf-terms (fargn term 3))))
        (t (list term))))
