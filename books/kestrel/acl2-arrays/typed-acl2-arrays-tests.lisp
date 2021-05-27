; Tests of the typed-acl2-arrays utilities
;
; Copyright (C) 2019-2020 Kestrel Institute
; Copyright (C) 2019-2020 Kestrel Technology, LLC
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "typed-acl2-arrays")
(include-book "kestrel/utilities/deftest" :dir :system)

(deftest
  (def-typed-acl2-array nat-arrayp (natp val)
    :default-satisfies-predp nil ;since nil does not satisfy natp
    ))

;; The :default value triggers extra theorems to be generated
(deftest
  (def-typed-acl2-array nat-arrayp (natp val) :default 0))

(deftest
  (def-typed-acl2-array nat-less-than-index-arrayp (and (natp val) (< val index))
    :default-satisfies-predp nil ;since nil does not satisfy natp (in fact, there is no default value that will work for all indices)
    ))

;; The :default value triggers extra theorems to be generated
(deftest
  (def-typed-acl2-array nat-less-than-index-arrayp (and (natp val) (<= val index)) :default 0))

;; Uses :nil as the default
(deftest
  (def-typed-acl2-array nat-list-arrayp (nat-listp val)))

;; Test :extra-vars.  The rfix ensures we don't need :extra-guards.
(deftest
  (def-typed-acl2-array nat-less-than-y-arrayp (and (natp val) (< val (rfix y)))
    :extra-vars (y)
    :default-satisfies-predp nil))

;; Test :extra-guards
(deftest
  (def-typed-acl2-array nat-less-than-y-arrayp (and (natp val) (< val y))
    :extra-vars (y)
    :extra-guards ((natp y))
    :default-satisfies-predp nil))

;;;
;;; tests of the "2" variant
;;

(deftest
  (def-typed-acl2-array2 nat-arrayp (natp val)
    :default-satisfies-predp nil ;since nil does not satisfy natp
    ))

;; The :default value triggers extra theorems to be generated
(deftest
  (def-typed-acl2-array2 nat-arrayp (natp val) :default 0))

(deftest
  (def-typed-acl2-array2 nat-less-than-index-arrayp (and (natp val) (< val index))
    :default-satisfies-predp nil ;since nil does not satisfy natp (in fact, there is no default value that will work for all indices)
    ))

;; The :default value triggers extra theorems to be generated
(deftest
  (def-typed-acl2-array2 nat-less-than-index-arrayp (and (natp val) (<= val index)) :default 0))

;; Uses :nil as the default
(deftest
  (def-typed-acl2-array2 nat-list-arrayp (nat-listp val)))

;; Test :extra-vars.  The rfix ensures we don't need :extra-guards.
(deftest
  (def-typed-acl2-array2 nat-less-than-y-arrayp (and (natp val) (< val (rfix y)))
    :extra-vars (y)
    :default-satisfies-predp nil))

;; Test :extra-guards
(deftest
  (def-typed-acl2-array2 nat-less-than-y-arrayp (and (natp val) (< val y))
    :extra-vars (y)
    :extra-guards ((natp y))
    :default-satisfies-predp nil))
