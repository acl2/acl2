; Tests of the def-constant-opener utility
;
; Copyright (C) 2018-2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "def-constant-opener")
(include-book "kestrel/utilities/deftest" :dir :system)

;; non-recursive
(deftest
  (def-constant-opener natp)
  ;; expected result:
  (must-be-redundant
   (defthm natp-constant-opener
     (implies (syntaxp (quotep x))
              (equal (natp x)
                     (and (integerp x) (<= 0 x))))
     :hints (("Goal" :in-theory '(natp))))))

;; recursive:
(deftest
  (def-constant-opener len)
  ;; expected result:
  (must-be-redundant
   (defthm len-constant-opener
     (implies (syntaxp (quotep x))
              (equal (len x)
                     (if (consp x) (+ 1 (len (cdr x))) 0)))
     :hints (("Goal" :in-theory '(len))))))

;; function with more than 1 arg:
(deftest
  (def-constant-opener revappend)
  ;; expected result:
  (must-be-redundant
   (defthm common-lisp::revappend-constant-opener ;;todo: use the acl2 package for this somehow?
     (implies (syntaxp (and (quotep x) (quotep y)))
              (equal (revappend x y)
                     (if (endp x)
                         y
                         (revappend (cdr x) (cons (car x) y)))))
     :hints (("Goal" :in-theory '(revappend))))))

;; Test that requires installing the not-normalized body.
(deftest
  (defstub stub (x) t)
  (defun foo (x) (if (stub (not (posp x))) 1 0))
  (def-constant-opener foo))
