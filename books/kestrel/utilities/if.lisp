; Rules about IF
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; Some simple rewrite rules about IF.  These may be needed by Axe if not by
;; ACL2.  I suppose some might help during backchaining, but most of this
;; reasoning may be built into ACL2.

(defthmd if-same-branches
  (equal (if test x x)
         x))

(defthmd if-of-t
  (equal (if t thenpart elsepart)
         thenpart)
  :hints (("Goal" :in-theory (enable if))))

(defthmd if-when-non-nil-constant
  (implies (and (syntaxp (quotep test))
                test)
           (equal (if test thenpart elsepart)
                  thenpart))
  :hints (("Goal" :in-theory (enable if))))

(defthmd if-of-nil
  (equal (if nil thenpart elsepart)
         elsepart)
  :hints (("Goal" :in-theory (enable if))))

(defthmd if-of-not
  (equal (if (not test) x y)
         (if test y x))
  :hints (("Goal" :in-theory (enable if))))
