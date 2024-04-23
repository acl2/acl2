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
    )
  ;; expected result:
  (must-be-redundant
    ;; The -aux function for the checker:
    (DEFUND NAT-ARRAYP-AUX (ARRAY-NAME ARRAY INDEX)
      (DECLARE
       (XARGS
         :GUARD (AND (ARRAY1P ARRAY-NAME ARRAY)
                     (INTEGERP INDEX)
                     (< INDEX (ALEN1 ARRAY-NAME ARRAY)))
         :MEASURE (NFIX (+ 1 INDEX))))
      (IF (NOT (NATP INDEX))
          T
        (LET ((VAL (AREF1 ARRAY-NAME ARRAY INDEX)))
          (AND (NATP VAL)
               (NAT-ARRAYP-AUX ARRAY-NAME ARRAY (+ -1 INDEX))))))
    (DEFTHM NAT-ARRAYP-AUX-OF-MINUS1
      (NAT-ARRAYP-AUX ARRAY-NAME ARRAY -1))
    (DEFTHM NAT-ARRAYP-AUX-OF-0
      (EQUAL (NAT-ARRAYP-AUX ARRAY-NAME ARRAY 0)
             (LET ((INDEX 0))
               (LET ((VAL (AREF1 ARRAY-NAME ARRAY INDEX)))
                 (NATP VAL)))))
    (DEFTHM NAT-ARRAYP-AUX-MONOTONE
      (IMPLIES (AND (NAT-ARRAYP-AUX ARRAY-NAME ARRAY N)
                    (<= M N)
                    (INTEGERP M)
                    (INTEGERP N))
               (NAT-ARRAYP-AUX ARRAY-NAME ARRAY M)))
    (DEFTHM TYPE-OF-AREF1-WHEN-NAT-ARRAYP-AUX
      (IMPLIES (AND (NAT-ARRAYP-AUX ARRAY-NAME ARRAY TOP-INDEX)
                    (<= INDEX TOP-INDEX)
                    (NATP INDEX)
                    (INTEGERP TOP-INDEX))
               (LET ((VAL (AREF1 ARRAY-NAME ARRAY INDEX)))
                 (NATP VAL))))
    (DEFTHM NAT-ARRAYP-AUX-OF-ASET1-TOO-HIGH
      (IMPLIES (AND (< INDEX INDEX2)
                    (< INDEX2 (ALEN1 ARRAY-NAME ARRAY))
                    (ARRAY1P ARRAY-NAME ARRAY)
                    (INTEGERP INDEX)
                    (INTEGERP INDEX2))
               (EQUAL (NAT-ARRAYP-AUX ARRAY-NAME
                                      (ASET1 ARRAY-NAME ARRAY INDEX2 VAL)
                                      INDEX)
                      (NAT-ARRAYP-AUX ARRAY-NAME ARRAY INDEX))))
    (DEFTHM NAT-ARRAYP-AUX-OF-ASET1
      (IMPLIES (AND (NAT-ARRAYP-AUX ARRAY-NAME ARRAY INDEX)
                    (LET ((INDEX INDEX2))
                      (DECLARE (IGNORABLE INDEX))
                      (NATP VAL))
                    (< INDEX (ALEN1 ARRAY-NAME ARRAY))
                    (< INDEX2 (ALEN1 ARRAY-NAME ARRAY))
                    (ARRAY1P ARRAY-NAME ARRAY)
                    (INTEGERP INDEX)
                    (NATP INDEX2))
               (NAT-ARRAYP-AUX ARRAY-NAME
                               (ASET1 ARRAY-NAME ARRAY INDEX2 VAL)
                               INDEX)))
    (DEFTHM NAT-ARRAYP-AUX-OF-ASET1-AT-END
      (IMPLIES (AND (NAT-ARRAYP-AUX ARRAY-NAME ARRAY (+ -1 INDEX))
                    (NATP VAL)
                    (< INDEX (ALEN1 ARRAY-NAME ARRAY))
                    (ARRAY1P ARRAY-NAME ARRAY)
                    (NATP INDEX))
               (NAT-ARRAYP-AUX ARRAY-NAME
                               (ASET1 ARRAY-NAME ARRAY INDEX VAL)
                               INDEX)))
    (DEFTHM NAT-ARRAYP-AUX-OF-COMPRESS1
      (IMPLIES (AND (FORCE (ARRAY1P ARRAY-NAME ARRAY))
                    (< INDEX (ALEN1 ARRAY-NAME ARRAY)))
               (EQUAL (NAT-ARRAYP-AUX ARRAY-NAME (COMPRESS1 ARRAY-NAME ARRAY)
                                      INDEX)
                      (NAT-ARRAYP-AUX ARRAY-NAME ARRAY INDEX))))
    (DEFTHM NAT-ARRAYP-AUX-OF-CONS-OF-CONS-OF-HEADER
      (IMPLIES (AND (NAT-ARRAYP-AUX ARRAY-NAME ARRAY INDEX)
                    (EQUAL (DEFAULT ARRAY-NAME ARRAY)
                           (CADR (ASSOC-KEYWORD :DEFAULT HEADER-ARGS))))
               (NAT-ARRAYP-AUX ARRAY-NAME
                               (CONS (CONS :HEADER HEADER-ARGS) ARRAY)
                               INDEX)))
    (DEFTHM NAT-ARRAYP-AUX-OF-CONS-OF-CONS-OF-HEADER-IRREL
      (IMPLIES (AND (NATP INDEX)
                    (EQUAL (DEFAULT ARRAY-NAME ARRAY)
                           (CADR (ASSOC-KEYWORD :DEFAULT HEADER-ARGS))))
               (EQUAL (NAT-ARRAYP-AUX ARRAY-NAME
                                      (CONS (CONS :HEADER HEADER-ARGS) ARRAY)
                                      INDEX)
                      (NAT-ARRAYP-AUX ARRAY-NAME ARRAY INDEX))))

    ;; The main checker function (this version takes NUM-VALID-INDICES):
    (DEFUND NAT-ARRAYP (ARRAY-NAME ARRAY NUM-VALID-INDICES)
      (DECLARE (XARGS :GUARD T))
      (AND (ARRAY1P ARRAY-NAME ARRAY)
           (NATP NUM-VALID-INDICES)
           (<= NUM-VALID-INDICES
               (ALEN1 ARRAY-NAME ARRAY))
           (NAT-ARRAYP-AUX ARRAY-NAME ARRAY (+ -1 NUM-VALID-INDICES))
           (EQUAL (DEFAULT ARRAY-NAME ARRAY) NIL)))
    (DEFTHM ARRAY1P-WHEN-NAT-ARRAYP
      (IMPLIES (NAT-ARRAYP ARRAY-NAME ARRAY NUM-VALID-INDICES)
               (ARRAY1P ARRAY-NAME ARRAY)))
    (DEFTHM NAT-ARRAYP-FORWARD-TO-ARRAY1P
      (IMPLIES (NAT-ARRAYP ARRAY-NAME ARRAY NUM-VALID-INDICES)
               (ARRAY1P ARRAY-NAME ARRAY))
      :RULE-CLASSES :FORWARD-CHAINING)
    (DEFTHM NAT-ARRAYP-FORWARD-TO-LEN-BOUND
      (IMPLIES (NAT-ARRAYP ARRAY-NAME ARRAY NUM-VALID-INDICES)
               (<= NUM-VALID-INDICES (ALEN1 ARRAY-NAME ARRAY)))
      :RULE-CLASSES :FORWARD-CHAINING)
    (DEFTHM NAT-ARRAYP-FORWARD-TO-LEN-BOUND-2
      (IMPLIES (NAT-ARRAYP ARRAY-NAME ARRAY NUM-VALID-INDICES)
               (<= 0 (ALEN1 ARRAY-NAME ARRAY)))
      :RULE-CLASSES :FORWARD-CHAINING)
    (DEFTHM TYPE-OF-AREF1-WHEN-NAT-ARRAYP
      (IMPLIES (AND (NAT-ARRAYP ARRAY-NAME ARRAY NUM-VALID-INDICES)
                    (< INDEX NUM-VALID-INDICES)
                    (NATP INDEX))
               (LET ((VAL (AREF1 ARRAY-NAME ARRAY INDEX)))
                 (NATP VAL))))
    (DEFTHM TYPE-OF-AREF1-WHEN-NAT-ARRAYP-SPECIAL
      (IMPLIES (AND (NAT-ARRAYP ARRAY-NAME ARRAY (+ 1 INDEX))
                    (NATP INDEX))
               (LET ((VAL (AREF1 ARRAY-NAME ARRAY INDEX)))
                 (NATP VAL))))
    (DEFTHM NAT-ARRAYP-MONOTONE
      (IMPLIES (AND (NAT-ARRAYP ARRAY-NAME ARRAY N)
                    (<= M N)
                    (NATP M)
                    (INTEGERP N))
               (NAT-ARRAYP ARRAY-NAME ARRAY M)))
    (DEFTHM NAT-ARRAYP-OF-ASET1
      (IMPLIES (AND (NAT-ARRAYP ARRAY-NAME ARRAY NUM-VALID-INDICES)
                    (NATP VAL)
                    (< INDEX (ALEN1 ARRAY-NAME ARRAY))
                    (NATP INDEX))
               (NAT-ARRAYP ARRAY-NAME
                           (ASET1 ARRAY-NAME ARRAY INDEX VAL)
                           NUM-VALID-INDICES)))
    (DEFTHM NAT-ARRAYP-OF-ASET1-AT-END
      (IMPLIES (AND (NAT-ARRAYP ARRAY-NAME ARRAY INDEX)
                    (NATP VAL)
                    (< INDEX (ALEN1 ARRAY-NAME ARRAY))
                    (NATP INDEX))
               (NAT-ARRAYP ARRAY-NAME
                           (ASET1 ARRAY-NAME ARRAY INDEX VAL)
                           (+ 1 INDEX))))
    (DEFTHM NAT-ARRAYP-OF-ASET1-AT-END-GEN
      (IMPLIES (AND (NAT-ARRAYP ARRAY-NAME ARRAY INDEX)
                    (<= NUM-VALID-INDICES (+ 1 INDEX))
                    (NATP VAL)
                    (< INDEX (ALEN1 ARRAY-NAME ARRAY))
                    (NATP NUM-VALID-INDICES)
                    (NATP INDEX))
               (NAT-ARRAYP ARRAY-NAME
                           (ASET1 ARRAY-NAME ARRAY INDEX VAL)
                           NUM-VALID-INDICES)))
    (DEFTHM NAT-ARRAYP-OF-MAKE-EMPTY-ARRAY-AND-0
      (IMPLIES (AND (POSP LEN)
                    (SYMBOLP ARRAY-NAME)
                    (<= LEN 2147483646))
               (NAT-ARRAYP ARRAY-NAME
                           (MAKE-EMPTY-ARRAY ARRAY-NAME LEN)
                           0)))))

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
