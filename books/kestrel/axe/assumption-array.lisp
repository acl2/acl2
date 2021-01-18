; An array to track information from assumptions
;
; Copyright (C) 2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/acl2-arrays/typed-acl2-arrays" :dir :system)
(include-book "kestrel/booleans/bool-fix" :dir :system)
(include-book "dags")
(include-book "equivs")

;; Currently, an assumption always indicates that a node is equal to a
;; particular constant, or indicates that it is non-nil.
(defun assumption-itemp (item)
  (declare (xargs :guard t))
  (or (equal item :non-nil)
      (myquotep item)))

;;;
;;; assumption-arrayp
;;;

;; Each node maps to nil (no replacement), or to a replacement (a quotep or a
;; nodenum), or to the special value :non-nil, indicating that the node is
;; known to be non-nil (but not necessarily known to be t).  TODO: Bake in the
;; name of the array
;; TODO: Consider generalizing this to support mapping a node to another node equal to it.
(def-typed-acl2-array2 assumption-arrayp
  (or (null val) ;; no information about this node
      (assumption-itemp val)))

;; Returns npdenum itself, or a replacement for it
(defund maybe-replace-nodenum-using-assumption-array (nodenum
                                                      equiv
                                                      assumption-array
                                                      assumption-array-num-valid-nodes
                                                      print)
  (declare (xargs :guard (and (natp nodenum)
                              (equivp equiv)
                              (assumption-arrayp 'assumption-array assumption-array)
                              (natp assumption-array-num-valid-nodes)
                              (<= assumption-array-num-valid-nodes (alen1 'assumption-array assumption-array)))
                  :guard-hints (("Goal" :use (:instance type-of-aref1-when-assumption-arrayp
                                                        (array-name 'assumption-array)
                                                        (array assumption-array)
                                                        (index nodenum))
                                 :in-theory (e/d ()
                                                 (natp
                                                  myquotep
                                                  type-of-aref1-when-assumption-arrayp))))))
  (if (not (< nodenum assumption-array-num-valid-nodes))
      nodenum ; no replacement possible
    (let ((assumption-info (aref1 'assumption-array assumption-array nodenum)))
      (if (not assumption-info)
          nodenum ; no assumption info about nodenum
        (if (eq :non-nil assumption-info)
            (if (eq 'iff equiv)
                *t* ;; We know the node is non-nil and only have to preserve iff
              ;; Can't rewrite since we are in an 'equal context and only know that nodenum is non-nil:
              (prog2$ (and print (cw "NOTE: Rewriting non-nil node ~x0 in an equal context.~%" nodenum))
                      nodenum))
          ;; we have a replacement (some constant) for nodenum:
          (if (eq 'iff equiv)
              ;; If the equiv is 'iff, we go ahead and bool-fix the constant:
              (enquote (bool-fix (unquote assumption-info)))
            ;; Return the constant:
            assumption-info))))))

;; This justifies bool-fixing the constant if the equiv is 'iff:
(thm (iff (bool-fix x) x))

;; It's either nodenum itself or a constant
(defthm maybe-replace-nodenum-using-assumption-array-return-type
  (implies (and (assumption-arrayp 'assumption-array assumption-array)
                (natp nodenum)
                (equivp equiv)
                (assumption-arrayp 'assumption-array assumption-array)
                (natp assumption-array-num-valid-nodes)
                (<= assumption-array-num-valid-nodes (alen1 'assumption-array assumption-array)))
           (or (equal nodenum (maybe-replace-nodenum-using-assumption-array nodenum equiv assumption-array assumption-array-num-valid-nodes print))
               (myquotep (maybe-replace-nodenum-using-assumption-array nodenum equiv assumption-array assumption-array-num-valid-nodes print))))
  :hints (("Goal" :use (:instance type-of-aref1-when-assumption-arrayp
                                  (array-name 'assumption-array)
                                  (array assumption-array)
                                  (index nodenum)
                                  )
           :in-theory (e/d (maybe-replace-nodenum-using-assumption-array
                            dargp-less-than)
                           (natp
                            myquotep
                            type-of-aref1-when-assumption-arrayp)))))

(defthm dargp-less-than-of-maybe-replace-nodenum-using-assumption-array
  (implies (and (assumption-arrayp 'assumption-array assumption-array)
                (natp nodenum)
                (< nodenum bound)
                (equivp equiv)
                (assumption-arrayp 'assumption-array assumption-array)
                (natp assumption-array-num-valid-nodes)
                (<= assumption-array-num-valid-nodes (alen1 'assumption-array assumption-array)))
           (dargp-less-than (maybe-replace-nodenum-using-assumption-array nodenum equiv assumption-array assumption-array-num-valid-nodes print)
                            bound))
  :hints (("Goal" :use (:instance maybe-replace-nodenum-using-assumption-array-return-type)
           :in-theory (disable maybe-replace-nodenum-using-assumption-array-return-type))))

(defthm type-of-aref1-when-assumption-arrayp-alt
  (implies (and (assumption-arrayp array-name array)
                (< index (alen1 array-name array))
                (natp index)
                (aref1 array-name array index))
           (assumption-itemp (aref1 array-name array index)))
  :hints (("Goal" :use (:instance type-of-aref1-when-assumption-arrayp)
           :in-theory (disable type-of-aref1-when-assumption-arrayp))))
