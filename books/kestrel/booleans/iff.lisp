; A lightweight book about the built-in function IFF
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2022 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "bool-fix")

;; IFF should probably be enabled for most ACL2 proofs, but we include here
;; some theorems that could be useful if it is disabled.  These theorems are
;; also used by Axe.  We don't disable IFF in this book -- a deparature from
;; our usual convention of disabling a function in the book about it.

(defthm iff-of-constant-arg1
  (implies (syntaxp (quotep x))
           (equal (iff x y)
                  (if x ; gets resovled
                      (bool-fix y)
                    (not y)))))

(defthm iff-of-constant-arg2
  (implies (syntaxp (quotep y))
           (equal (iff x y)
                  (if y ; gets resovled
                      (bool-fix x)
                    (not x)))))

(defthm iff-same
  (equal (iff x x)
         t))

(defthm iff-bool-fix-arg1
  (equal (iff (bool-fix x) y)
         (iff x y)))

(defthm iff-bool-fix-arg2
  (equal (iff x (bool-fix y))
         (iff x y)))
