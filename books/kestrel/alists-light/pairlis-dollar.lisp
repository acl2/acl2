; A lightweight book about the built-in function pairlis$
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(defthm symbol-alistp-of-pairlis$
  (equal (symbol-alistp (pairlis$ x y))
         (symbol-listp (true-list-fix x)))
  :hints (("Goal" :in-theory (enable pairlis$))))

;see also a version in books/std/alists/strip-cdrs.lisp
(defthm strip-cdrs-of-pairlis$2
  (implies (and (true-listp y)
                (equal (len x) (len y)))
           (equal (strip-cdrs (pairlis$ x y))
                  y)))

(defthmd pairlis$-opener
  (implies (not (atom keys))
           (equal (pairlis$ keys vals)
                  (acons (car keys)
                         (car vals)
                         (pairlis$ (cdr keys) (cdr vals))))))

(defthmd pairlis$-base
  (implies (atom keys)
           (equal (pairlis$ keys vals)
                  nil)))
