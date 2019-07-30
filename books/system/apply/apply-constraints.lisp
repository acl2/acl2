; ACL2 Version 7.4 -- A Computational Logic for Applicative Common Lisp
; Copyright (C) 2017, Regents of the University of Texas

; This version of ACL2 is a descendent of ACL2 Version 1.9, Copyright
; (C) 1997 Computational Logic, Inc.  See the documentation topic NOTE-2-0.

; This program is free software; you can redistribute it and/or modify
; it under the terms of the LICENSE file distributed with ACL2.

; This program is distributed in the hope that it will be useful,
; but WITHOUT ANY WARRANTY; without even the implied warranty of
; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
; LICENSE for more details.

; Written by:  Matt Kaufmann               and J Strother Moore
; email:       Kaufmann@cs.utexas.edu      and Moore@cs.utexas.edu
; Department of Computer Science
; University of Texas at Austin
; Austin, TX 78712 U.S.A.

; Many thanks to ForrestHunt, Inc. for supporting the preponderance of this
; work, and for permission to include it here.

; See the Refresher on books/system/, etc. in books/system/apply/apply-prim for
; some background.

; One way to think of this book is that it was derived by taking its source
; file counterpart, e.g., apply-constraints.lisp, and sprinkling in the
; include-books, defthms, declarations, and hints to get the source file
; admitted in guard-verified, :logic mode fashion by a version of ACL2 in
; which these functions weren't already defined.  We supply minimal comments
; here except when discussing the termination/guard verification issues.  See
; the corresponding source files for explanations of the definitions below!

(in-package "ACL2")

(include-book "apply-prim")

; -----------------------------------------------------------------
; Handling the Primitives

; -----------------------------------------------------------------
; BADGE-USERFN and APPLY$-USERFN

(encapsulate
  ((badge-userfn (fn) t))
  (local (defun badge-userfn (fn)
           (declare (ignore fn))
           nil))
  (defthm badge-userfn-type
    (implies (badge-userfn fn)
             (apply$-badgep (badge-userfn fn)))
    :rule-classes
    ((:forward-chaining))))

(encapsulate
  ((apply$-userfn (fn args) t :guard (true-listp args)))
  (local (defun apply$-userfn (fn args)
           (declare (ignore fn args))
           nil))
  (defthm apply$-userfn-takes-arity-args
    (implies (badge-userfn fn)
             (equal (apply$-userfn fn args)
                    (apply$-userfn fn (take (apply$-badge-arity
                                             (badge-userfn fn))
                                            args))))
    :rule-classes nil))

(encapsulate (((untame-apply$ * *) => *
               :formals (fn args)
               :guard (true-listp args)))
  (local (defun untame-apply$ (fn args)
           (declare (ignore fn args))
           nil))
  (defthm untame-apply$-takes-arity-args
    (implies (badge-userfn fn)
             (equal (untame-apply$ fn args)
                    (untame-apply$ fn (take (apply$-badge-arity
                                             (badge-userfn fn))
                                            args))))
    :rule-classes
    ((:rewrite
      :corollary (implies (and (syntaxp (and (quotep fn)
                                             (symbolp args)))
                               (badge-userfn fn))
                          (equal (untame-apply$ fn args)
                                 (untame-apply$ fn (take (apply$-badge-arity
                                                          (badge-userfn fn))
                                                         args))))))))
