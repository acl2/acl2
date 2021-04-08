; An array for tracking results of operations on nodes
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2020 Kestrel Institute
; Copyright (C) 2016-2020 Kestrel Technology, LLC
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "dargp-less-than")
(include-book "all-dargp")
(include-book "bounded-dag-exprs")
(include-book "axe-trees")
(include-book "kestrel/acl2-arrays/typed-acl2-arrays" :dir :system)

;; The result array maps nodes to either nil (no result) or a nodenum or quotep.
;; TODO: Compare to bounded-node-replacement-array?
(def-typed-acl2-array2 result-arrayp
  (or (null val) ;node is not yet processed
      (dargp-less-than val bound))
  :extra-vars (bound)
  :extra-guards ((natp bound)))

;have def-typed-acl2-array generate this
(DEFTHM DEFAULT-WHEN-result-ARRAYP-cheap
  (IMPLIES (result-ARRAYP ARRAY-NAME ARRAY bound)
           (EQUAL (DEFAULT ARRAY-NAME ARRAY)
                  NIL))
  :RULE-CLASSES ((:REWRITE :BACKCHAIN-LIMIT-LST (0)))
  :HINTS (("Goal" :IN-THEORY (ENABLE result-ARRAYP))))

(defthm result-arrayp-aux-monotone-on-bound
  (implies (and (result-arrayp-aux array-name array index free)
                (natp free)
                (<= free bound))
           (result-arrayp-aux array-name array index bound))
  :hints (("Goal" :in-theory (enable result-arrayp-aux))))

(defthm result-arrayp-monotone-on-bound
  (implies (and (result-arrayp array-name array free)
                (natp free)
                (<= free bound))
           (result-arrayp array-name array bound))
  :hints (("Goal" :in-theory (enable result-arrayp))))

;; just a rephrasing
(defthmd type-of-aref1-when-result-arrayp-2
  (implies (and (result-arrayp array-name array bound)
                (< index (alen1 array-name array))
                (natp index)
                (aref1 array-name array index))
           (dargp-less-than (aref1 array-name array index) bound))
  :hints (("Goal" :use (:instance type-of-aref1-when-result-arrayp)
           :in-theory (disable type-of-aref1-when-result-arrayp))))


;; see also translate-args
(defund lookup-args-in-result-array (args result-array-name result-array)
  (declare (xargs :guard (and (true-listp args)
                              (all-dargp args)
                              ;;(result-arrayp result-array-name result-array dag-len)
                              (array1p result-array-name result-array)
                              (< (largest-non-quotep args) (alen1 result-array-name result-array)))))
  (if (endp args)
      nil
    (let ((arg (car args)))
      (if (consp arg) ;check for quotep
          (cons arg
                (lookup-args-in-result-array (cdr args) result-array-name result-array))
        (cons (aref1 result-array-name result-array arg)
              (lookup-args-in-result-array (cdr args) result-array-name result-array))))))

(defthm all-axe-treep-of-lookup-args-in-result-array
  (implies (and (result-arrayp result-array-name result-array bound)
                ;(all-dargp-less-than args dag-len)
                (all-dargp args)
                )
           ;; works because nil is an axe-tree but it would be better not to rely on that
           (all-axe-treep (lookup-args-in-result-array args result-array-name result-array)))
  :hints (("Goal" :in-theory (enable axe-treep lookup-args-in-result-array))
          ("subgoal *1/5"
           :expand (LOOKUP-ARGS-IN-RESULT-ARRAY ARGS RESULT-ARRAY-NAME RESULT-ARRAY)
           :use (:instance TYPE-OF-AREF1-WHEN-RESULT-ARRAYP
                           (array-name result-array-name)
                           (array result-array)
                           (index (car args)))
           :in-theory (disable TYPE-OF-AREF1-WHEN-RESULT-ARRAYP))))

(defthm all-bounded-axe-treep-of-lookup-args-in-result-array
  (implies (and (result-arrayp result-array-name result-array bound)
                ;(all-dargp-less-than args dag-len)
                (all-dargp args)
                )
           (all-bounded-axe-treep (lookup-args-in-result-array args result-array-name result-array) bound))
  :hints (("Goal" :in-theory (enable axe-treep lookup-args-in-result-array))
          ("subgoal *1/5"
           :expand (lookup-args-in-result-array args result-array-name result-array)
           :use (:instance type-of-aref1-when-result-arrayp
                           (array-name result-array-name)
                           (array result-array)
                           (index (car args)))
           :in-theory (e/d (bounded-axe-treep-when-dargp-less-than)
                           (type-of-aref1-when-result-arrayp)))))
