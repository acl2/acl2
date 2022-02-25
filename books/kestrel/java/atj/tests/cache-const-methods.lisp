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

; Test the caching of the values of certain nullary methods.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define jarray-const ()
  :returns (array java::byte-arrayp)
  (java::byte-array-new-init (list (java::byte-value 0)
                                   (java::byte-value 1)
                                   (java::byte-value 2)
                                   (java::byte-value 3)
                                   (java::byte-value 4)
                                   (java::byte-value 5)
                                   (java::byte-value 6)
                                   (java::byte-value 7)
                                   (java::byte-value 8)
                                   (java::byte-value 9))))

(define jarray-nonconst ((i java::int-valuep))
  :guard (java::byte-array-index-in-range-p (jarray-const) i)
  :returns (byte java::byte-valuep)
  (java::byte-array-read (jarray-const) i))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defconst *tests-deep-or-unguarded*
  `(("Const" (jarray-const))
    ("NonConst0" (jarray-nonconst ',(java::int-value 0)))
    ("NonConst1" (jarray-nonconst ',(java::int-value 1)))
    ("NonConst2" (jarray-nonconst ',(java::int-value 2)))
    ("NonConst3" (jarray-nonconst ',(java::int-value 3)))
    ("NonConst4" (jarray-nonconst ',(java::int-value 4)))
    ("NonConst5" (jarray-nonconst ',(java::int-value 5)))
    ("NonConst6" (jarray-nonconst ',(java::int-value 6)))
    ("NonConst7" (jarray-nonconst ',(java::int-value 7)))
    ("NonConst8" (jarray-nonconst ',(java::int-value 8)))
    ("NonConst9" (jarray-nonconst ',(java::int-value 9)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defconst *tests-shallow-and-guarded*
  '(("Const" (jarray-const))
    ("NonConst0" (jarray-nonconst (java::int-value 0)))
    ("NonConst1" (jarray-nonconst (java::int-value 1)))
    ("NonConst2" (jarray-nonconst (java::int-value 2)))
    ("NonConst3" (jarray-nonconst (java::int-value 3)))
    ("NonConst4" (jarray-nonconst (java::int-value 4)))
    ("NonConst5" (jarray-nonconst (java::int-value 5)))
    ("NonConst6" (jarray-nonconst (java::int-value 6)))
    ("NonConst7" (jarray-nonconst (java::int-value 7)))
    ("NonConst8" (jarray-nonconst (java::int-value 8)))
    ("NonConst9" (jarray-nonconst (java::int-value 9)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Specialize input and output types, for shallow embedding with guards.

(java::atj-main-function-type jarray-const () :jbyte[])

(java::atj-main-function-type jarray-nonconst (:jint) :jbyte)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Generate Java code, with tests.

(java::atj jarray-const
           jarray-nonconst
           :deep t
           :guards nil
           :java-class "CacheConstMethodsDeepUnguarded"
           :tests *tests-deep-or-unguarded*)

(java::atj jarray-const
           jarray-nonconst
           :deep t
           :guards t
           :java-class "CacheConstMethodsDeepGuarded"
           :tests *tests-deep-or-unguarded*)

(java::atj jarray-const
           jarray-nonconst
           :deep nil
           :guards nil
           :java-class "CacheConstMethodsShallowUnguarded"
           :tests *tests-deep-or-unguarded*)

(java::atj jarray-const
           jarray-nonconst
           :deep nil
           :guards t
           :java-class "CacheConstMethodsShallowGuarded"
           :tests *tests-shallow-and-guarded*)

(java::atj jarray-const
           jarray-nonconst
           :deep nil
           :guards t
           :no-aij-types t
           :java-class "CacheConstMethodsNoAIJTypes"
           :tests *tests-shallow-and-guarded*)
