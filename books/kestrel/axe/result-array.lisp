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
                ;; (< index (alen1 array-name array))
                (natp index)
                (aref1 array-name array index))
           (dargp-less-than (aref1 array-name array index) bound))
  :hints (("Goal" :use (:instance type-of-aref1-when-result-arrayp)
           :in-theory (disable type-of-aref1-when-result-arrayp))))

;;;
;;; lookup-arg-in-result-array
;;;

;does this already exist?
(defund lookup-arg-in-result-array (arg result-array-name result-array)
  (declare (xargs :guard (and ;; (result-arrayp result-array-name result-array dag-len) ;we don't have dag-len
                          (array1p result-array-name result-array)
                          (dargp-less-than arg (alen1 result-array-name result-array)))))
  (if (consp arg) ;check for quotep
      arg
    (aref1 result-array-name result-array arg)))

(defthm dargp-of-lookup-arg-in-result-array
  (implies (and (lookup-arg-in-result-array arg result-array-name result-array) ; ensures it's not nil
                (result-arrayp result-array-name result-array bound) ;bound is a free var
                (dargp-less-than arg (alen1 result-array-name result-array))
                )
           (dargp (lookup-arg-in-result-array arg result-array-name result-array)))
  :hints (("Goal" :in-theory (e/d (lookup-arg-in-result-array) (dargp
                                                                natp
                                                                type-of-aref1-when-result-arrayp))
           :use (:instance type-of-aref1-when-result-arrayp
                           (array-name result-array-name)
                           (array result-array)
                           (index arg)))))

(defthm dargp-of-lookup-arg-in-result-array-alt
  (implies (and (or (consp arg)
                    (aref1 result-array-name result-array arg)) ; ensures it's not nil
                (result-arrayp result-array-name result-array bound) ;bound is a free var
                (dargp-less-than arg (alen1 result-array-name result-array))
                )
           (dargp (lookup-arg-in-result-array arg result-array-name result-array)))
  :hints (("Goal" :in-theory (e/d (lookup-arg-in-result-array) (dargp
                                                                natp
                                                                type-of-aref1-when-result-arrayp))
           :use (:instance type-of-aref1-when-result-arrayp
                           (array-name result-array-name)
                           (array result-array)
                           (index arg)))))

(defthm not-equal-of-1-and-len-of-lookup-arg-in-result-array
  (implies (and ;(lookup-arg-in-result-array arg result-array-name result-array) ; ensures it's not nil
                (result-arrayp result-array-name result-array bound) ;bound is a free var
                (dargp-less-than arg (alen1 result-array-name result-array))
                )
           (not (equal 1 (len (lookup-arg-in-result-array arg result-array-name result-array)))))
  :hints (("Goal" :use (:instance dargp-of-lookup-arg-in-result-array)
           :in-theory (e/d (dargp-less-than len)
                           (dargp-of-lookup-arg-in-result-array-alt
                            dargp-of-lookup-arg-in-result-array)))))

(defthm dargp-less-than-of-lookup-arg-in-result-array
  (implies (and (lookup-arg-in-result-array arg result-array-name result-array) ; ensures it's not nil
                (result-arrayp result-array-name result-array bound) ;bound is a free var
                (dargp-less-than arg (alen1 result-array-name result-array))
                )
           (dargp-less-than (lookup-arg-in-result-array arg result-array-name result-array) bound))
  :hints (("Goal" :in-theory (e/d (lookup-arg-in-result-array) (dargp
                                                                natp
                                                                type-of-aref1-when-result-arrayp))
           :use (:instance type-of-aref1-when-result-arrayp
                           (array-name result-array-name)
                           (array result-array)
                           (index arg)))))

(defthm dargp-less-than-of-lookup-arg-in-result-array-alt
  (implies (and (or (consp arg)
                    (aref1 result-array-name result-array arg)) ; ensures it's not nil
                (result-arrayp result-array-name result-array bound) ;bound is a free var
                (dargp-less-than arg (alen1 result-array-name result-array))
                )
           (dargp-less-than (lookup-arg-in-result-array arg result-array-name result-array) bound))
  :hints (("Goal" :in-theory (e/d (lookup-arg-in-result-array) (dargp
                                                                natp
                                                                type-of-aref1-when-result-arrayp))
           :use (:instance type-of-aref1-when-result-arrayp
                           (array-name result-array-name)
                           (array result-array)
                           (index arg)))))

(defthm <-of-lookup-arg-in-result-array
  (implies (and (lookup-arg-in-result-array arg result-array-name result-array) ; ensures it's not nil
                (not (consp (lookup-arg-in-result-array arg result-array-name result-array)))
                (result-arrayp result-array-name result-array bound) ;bound is a free var
                (dargp-less-than arg (alen1 result-array-name result-array))
                )
           (< (lookup-arg-in-result-array arg result-array-name result-array) bound))
  :hints (("Goal" :in-theory (e/d (lookup-arg-in-result-array) (dargp
                                                                natp
                                                                type-of-aref1-when-result-arrayp))
           :use (:instance type-of-aref1-when-result-arrayp
                           (array-name result-array-name)
                           (array result-array)
                           (index arg)))))

;drop?
(defthm <=-of-0-and-lookup-arg-in-result-array
  (implies (and (lookup-arg-in-result-array arg result-array-name result-array) ; ensures it's not nil
                (not (consp (lookup-arg-in-result-array arg result-array-name result-array)))
                (result-arrayp result-array-name result-array bound)
                (dargp-less-than arg (alen1 result-array-name result-array)))
           (<= 0 (lookup-arg-in-result-array arg result-array-name result-array)))
  :hints (("Goal" :use (:instance dargp-of-lookup-arg-in-result-array)
           :in-theory (disable dargp-of-lookup-arg-in-result-array))))

(defthm natp-of-lookup-arg-in-result-array
  (implies (and (result-arrayp result-array-name result-array bound)
                (dargp-less-than arg (alen1 result-array-name result-array)))
           (equal (natp (lookup-arg-in-result-array arg result-array-name result-array))
                  (and (lookup-arg-in-result-array arg result-array-name result-array) ; ensures it's not nil
                       (not (consp (lookup-arg-in-result-array arg result-array-name result-array))))))
  :hints (("Goal" :use (:instance dargp-of-lookup-arg-in-result-array)
           :in-theory (disable dargp-of-lookup-arg-in-result-array))))

;drop?
(defthm bounded-axe-treep-of-lookup-arg-in-result-array
  (implies (and (result-arrayp result-array-name result-array bound)
                (dargp-less-than arg (alen1 result-array-name result-array)))
           (bounded-axe-treep (lookup-arg-in-result-array arg result-array-name result-array) bound))
  :hints (("Goal" :use (:instance dargp-less-than-of-lookup-arg-in-result-array)
           :in-theory (disable dargp-less-than-of-lookup-arg-in-result-array))))

;;;
;;; lookup-args-in-result-array
;;;

;; see also translate-args
(defund lookup-args-in-result-array (args result-array-name result-array)
  (declare (xargs :guard (and (true-listp args)
                              (all-dargp args)
                              ;;(result-arrayp result-array-name result-array dag-len)
                              (array1p result-array-name result-array)
                              (< (largest-non-quotep args) (alen1 result-array-name result-array)))))
  (if (endp args)
      nil
    ;; TODO: Consider cons-with-hint here:
    (cons (lookup-arg-in-result-array (first args) result-array-name result-array)
          (lookup-args-in-result-array (cdr args) result-array-name result-array))))

(defthm len-of-lookup-args-in-result-array
  (equal (len (lookup-args-in-result-array args result-array-name result-array))
         (len args))
  :hints (("Goal" :in-theory (enable lookup-args-in-result-array))))

(defthm lookup-args-in-result-array-of-nil
  (equal (lookup-args-in-result-array nil result-array-name result-array)
         nil)
  :hints (("Goal" :in-theory (enable lookup-args-in-result-array))))

(defthm all-axe-treep-of-lookup-args-in-result-array
  (implies (and (result-arrayp result-array-name result-array bound)
                (all-dargp-less-than args (alen1 result-array-name result-array)) ;new
                ;(all-dargp args)
                )
           ;; works because nil is an axe-tree but it would be better not to rely on that
           (all-axe-treep (lookup-args-in-result-array args result-array-name result-array)))
  :hints (("Goal" :in-theory (enable axe-treep lookup-args-in-result-array))
          ("subgoal *1/3"
           :expand (lookup-args-in-result-array args result-array-name result-array)
           :use (:instance dargp-of-lookup-arg-in-result-array
                           ;(array-name result-array-name)
                           ;(array result-array)
                           (arg (car args)))
           :in-theory (e/d (;lookup-args-in-result-array ;gross
                            ) (dargp-of-lookup-arg-in-result-array)))))

(defthm all-bounded-axe-treep-of-lookup-args-in-result-array
  (implies (and (result-arrayp result-array-name result-array bound)
                (all-dargp-less-than args (alen1 result-array-name result-array)) ;new
                ;(all-dargp args)
                )
           (all-bounded-axe-treep (lookup-args-in-result-array args result-array-name result-array) bound))
  :hints (("Goal" :in-theory (enable LOOKUP-ARGS-IN-RESULT-ARRAY))))
