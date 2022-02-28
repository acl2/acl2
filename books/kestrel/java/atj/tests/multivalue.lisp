; Java Library
;
; Copyright (C) 2022 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "../atj" :ttags ((:open-output-channel!) (:oslib) (:quicklisp) :quicklisp.osicat))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; This file contains tests for multi-value ACL2 functions,
; i.e. functions that return MV values.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun add-sub (x y)
  (declare (xargs :guard (and (integerp x) (integerp y))))
  (mv (+ x y) (- x y)))

(defconst *add-sub-tests*
  '(("AddSub1" (add-sub 0 0))
    ("AddSub2" (add-sub 5 2))
    ("AddSub3" (add-sub -8 800))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun diff-types (c)
  (declare (xargs :guard (characterp c)))
  (mv (char-code c) (coerce (list c) 'string) c))

(defconst *diff-types-tests*
  '(("DiffTypes1" (diff-types #\H))
    ("DiffTypes2" (diff-types #\3))
    ("DiffTypes3" (diff-types #\w))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defconst *tests*
  (append *add-sub-tests*
          *diff-types-tests*))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Specialize input and output types, for shallow embedding with guards.

(java::atj-main-function-type add-sub
                              (:ainteger :ainteger)
                              (:ainteger :ainteger))

(java::atj-main-function-type diff-types
                              (:acharacter)
                              (:ainteger :astring :acharacter))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Generate Java code, with tests.

(java::atj add-sub
           diff-types
           :deep t
           :guards nil
           :java-class "MultivalueDeepUnguarded"
           :tests *tests*)

(java::atj add-sub
           diff-types
           :deep t
           :guards t
           :java-class "MultivalueDeepGuarded"
           :tests *tests*)

(java::atj add-sub
           diff-types
           :deep nil
           :guards nil
           :java-class "MultivalueShallowUnguarded"
           :tests *tests*)

(java::atj add-sub
           diff-types
           :deep nil
           :guards t
           :java-class "MultivalueShallowGuarded"
           :tests *tests*)
