; Copyright (C) 2014, Regents of the University of Texas
; Written by David Rager (original date April, 2012)
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

(in-package "ACL2")

; This book is intented to only be included locally.  This is because we define
; a theorem whose consequence is (true-listp x).  This theorem won't typically
; apply, so we recommend including this book locally, so that the ACL2 rewriter
; won't be slowed down.

; Common mistakes when creating the books for verifying mutually recursive
; system functions similar to subst-expr, subst-var, etc., include:

; (1) Forgetting to call the flg function to recursively call itself instead of
;     the original functions.  This occurs because one tends to copy+paste the
;     body of the original functions into the flg function.

; (2) Not defining the *-preserves-len lemma.

(defthm pseudo-termp-implies-pseudo-term-listp-cdr
  (implies (and (pseudo-termp x)
                 (consp x)
                 (not (equal (car x) 'quote)))
           (pseudo-term-listp (cdr x))))

(defthm pseudo-term-listp-implies-true-listp
  (implies (pseudo-term-listp x)
           (true-listp x)))

(defthm pseudo-termp-lambda-lemma
  (implies (and (pseudo-termp x)
                (consp x)
                (not (symbolp (car x))))
           (and (true-listp (car x))
                (equal (length (car x)) 3)
                (eq (car (car x)) 'lambda)
                (symbol-listp (cadr (car x)))
                (pseudo-termp (caddr (car x)))
                (equal (length (cadr (car x)))
                       (length (cdr x))))))
