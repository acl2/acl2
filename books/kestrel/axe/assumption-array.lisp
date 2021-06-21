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
(include-book "all-dargp-less-than")
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

(defthm type-of-aref1-when-assumption-arrayp-alt
  (implies (and (assumption-arrayp array-name array)
                (< index (alen1 array-name array))
                (natp index)
                (aref1 array-name array index))
           (assumption-itemp (aref1 array-name array index)))
  :hints (("Goal" :use (:instance type-of-aref1-when-assumption-arrayp)
           :in-theory (disable type-of-aref1-when-assumption-arrayp))))

;;;
;;; maybe-replace-nodenum-using-assumption-array
;;;

;; Returns NODENUM itself, or a replacement for it (which will be a quoted
;; constant known, via the ASSUMPTION-ARRAY, to be equivalent to NODENUM using
;; EQUIV).
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
                                 :in-theory (disable natp
                                                     myquotep
                                                     type-of-aref1-when-assumption-arrayp)))))
  (if (not (< nodenum assumption-array-num-valid-nodes))
      nodenum ; no replacement possible
    (let ((assumption-info (aref1 'assumption-array assumption-array nodenum)))
      (if (not assumption-info)
          nodenum ; no assumption info about nodenum
        (if (eq :non-nil assumption-info)
            ;; We know the node is non-nil but not which particular, non-nil value it has:
            (if (eq 'iff equiv)
                *t* ;; We know the node is non-nil, and we only have to preserve iff
              ;; Can't replace, since we are in an 'equal context and only know that nodenum is non-nil:
              (prog2$ (and print (cw "NOTE: Node ~x0 is known to be non-nil, but the context is 'equal, not 'iff.~%" nodenum))
                      nodenum))
          ;; We know that NODENUM is equal to the quoted constant ASSUMPTION-INFO:
          (if (eq 'iff equiv)
              ;; If the equiv is 'iff, we go ahead and bool-fix the constant:
              (let ((unquoted-const (unquote assumption-info)))
                (if (booleanp unquoted-const)
                    assumption-info ;avoid re-consing
                  (enquote (bool-fix unquoted-const))))
            ;; Equiv is 'equal.  Just return the constant:
            assumption-info))))))

;; This justifies bool-fixing the constant if the equiv is 'iff:
(thm (iff (bool-fix x) x))

;; We either get back the nodenum itself or a constant.
(defthm maybe-replace-nodenum-using-assumption-array-return-type
  (implies (and (assumption-arrayp 'assumption-array assumption-array)
                (natp nodenum)
                ;; (equivp equiv)
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

;; In the equiv is 'iff, we either get back the nodenum itself or a quoted t or nil.
;; Just a check, because of how we will use the result.
(defthmd maybe-replace-nodenum-using-assumption-array-of-iff-return-type
  (implies (and (assumption-arrayp 'assumption-array assumption-array)
                (natp nodenum)
                (assumption-arrayp 'assumption-array assumption-array)
                (natp assumption-array-num-valid-nodes)
                (<= assumption-array-num-valid-nodes (alen1 'assumption-array assumption-array)))
           (or (equal nodenum (maybe-replace-nodenum-using-assumption-array nodenum 'iff assumption-array assumption-array-num-valid-nodes print))
               (equal *t* (maybe-replace-nodenum-using-assumption-array nodenum 'iff assumption-array assumption-array-num-valid-nodes print))
               (equal *nil* (maybe-replace-nodenum-using-assumption-array nodenum 'iff assumption-array assumption-array-num-valid-nodes print))))
  :hints (("Goal" :use (:instance type-of-aref1-when-assumption-arrayp
                                  (array-name 'assumption-array)
                                  (array assumption-array)
                                  (index nodenum))
           :in-theory (e/d (maybe-replace-nodenum-using-assumption-array
                            dargp-less-than
                            booleanp
                            myquotep)
                           (natp type-of-aref1-when-assumption-arrayp)))))

(defthm dargp-of-maybe-replace-nodenum-using-assumption-array
  (implies (and (assumption-arrayp 'assumption-array assumption-array)
                (natp nodenum)
;(equivp equiv)
                (assumption-arrayp 'assumption-array assumption-array)
                (natp assumption-array-num-valid-nodes)
                (<= assumption-array-num-valid-nodes (alen1 'assumption-array assumption-array)))
           (dargp (maybe-replace-nodenum-using-assumption-array nodenum equiv assumption-array assumption-array-num-valid-nodes print)))
  :hints (("Goal" :use (:instance maybe-replace-nodenum-using-assumption-array-return-type)
           :in-theory (disable maybe-replace-nodenum-using-assumption-array-return-type))))

(defthm dargp-less-than-of-maybe-replace-nodenum-using-assumption-array
  (implies (and (assumption-arrayp 'assumption-array assumption-array)
                (natp nodenum)
                (< nodenum bound)
                ;(equivp equiv)
                (assumption-arrayp 'assumption-array assumption-array)
                (natp assumption-array-num-valid-nodes)
                (<= assumption-array-num-valid-nodes (alen1 'assumption-array assumption-array)))
           (dargp-less-than (maybe-replace-nodenum-using-assumption-array nodenum equiv assumption-array assumption-array-num-valid-nodes print)
                            bound))
  :hints (("Goal" :use (:instance maybe-replace-nodenum-using-assumption-array-return-type)
           :in-theory (disable maybe-replace-nodenum-using-assumption-array-return-type))))

(defthm <-of-maybe-replace-nodenum-using-assumption-array
  (implies (and (assumption-arrayp 'assumption-array assumption-array)
                (natp nodenum)
                (< nodenum bound)
                ;;(equivp equiv)
                (assumption-arrayp 'assumption-array assumption-array)
                (natp assumption-array-num-valid-nodes)
                (<= assumption-array-num-valid-nodes (alen1 'assumption-array assumption-array)))
           (< (maybe-replace-nodenum-using-assumption-array nodenum equiv assumption-array assumption-array-num-valid-nodes print)
              bound))
  :hints (("Goal" :use (:instance maybe-replace-nodenum-using-assumption-array-return-type)
           :in-theory (disable maybe-replace-nodenum-using-assumption-array-return-type))))

(defthm len-of-maybe-replace-nodenum-using-assumption-array
  (implies (and (assumption-arrayp 'assumption-array assumption-array)
                (natp nodenum)
                ;(equivp equiv)
                (assumption-arrayp 'assumption-array assumption-array)
                (natp assumption-array-num-valid-nodes)
                (<= assumption-array-num-valid-nodes (alen1 'assumption-array assumption-array)))
           (not (equal 1 (len (maybe-replace-nodenum-using-assumption-array nodenum equiv assumption-array assumption-array-num-valid-nodes print)))))
  :hints (("Goal" :use (:instance maybe-replace-nodenum-using-assumption-array-return-type)
           :in-theory (disable maybe-replace-nodenum-using-assumption-array-return-type))))

;;;
;;; maybe-replace-args-using-assumption-array
;;;

;; Returns a list of dargs.  For each arg, we get back either the
;; arg itself, or a replacement for it (which will be a quoted constant known,
;; via the ASSUMPTION-ARRAY, to be equivalent to the arg using EQUIV).
(defund maybe-replace-args-using-assumption-array (args
                                                   equivs
                                                   assumption-array
                                                   assumption-array-num-valid-nodes
                                                   print)
  (declare (xargs :guard (and (all-dargp args)
                              (true-listp args)
                              (equiv-listp equivs)
                              (equal (len args) (len equivs))
                              (assumption-arrayp 'assumption-array assumption-array)
                              (natp assumption-array-num-valid-nodes)
                              (<= assumption-array-num-valid-nodes (alen1 'assumption-array assumption-array)))
                  :guard-hints (("Goal" :in-theory (enable equiv-listp)))))
  (if (endp args)
      nil
    (let ((arg (first args)))
      (cons (if (consp arg) ; test for quotep
                arg         ; no change to a constant
              (maybe-replace-nodenum-using-assumption-array arg (first equivs) assumption-array assumption-array-num-valid-nodes print))
            (maybe-replace-args-using-assumption-array (rest args)
                                                       (rest equivs)
                                                       assumption-array
                                                       assumption-array-num-valid-nodes
                                                       print)))))

(defthm all-dargp-of-maybe-replace-args-using-assumption-array
  (implies (and (all-dargp args)
;(true-listp args)
;(equiv-listp equivs)
;(equal (len args) (len equivs))
                (assumption-arrayp 'assumption-array assumption-array)
                (natp assumption-array-num-valid-nodes)
                (<= assumption-array-num-valid-nodes (alen1 'assumption-array assumption-array)))
           (all-dargp (maybe-replace-args-using-assumption-array args
                                                                 equivs
                                                                 assumption-array
                                                                 assumption-array-num-valid-nodes
                                                                 print)))
  :hints (("Goal" :in-theory (e/d (maybe-replace-args-using-assumption-array) (dargp)))))

(defthm all-dargp-less-than-of-maybe-replace-args-using-assumption-array
  (implies (and (all-dargp-less-than args bound)
                ;(true-listp args)
                ;(equiv-listp equivs)
                ;(equal (len args) (len equivs))
                (assumption-arrayp 'assumption-array assumption-array)
                (natp assumption-array-num-valid-nodes)
                (<= assumption-array-num-valid-nodes (alen1 'assumption-array assumption-array)))
           (all-dargp-less-than (maybe-replace-args-using-assumption-array args
                                                                           equivs
                                                                           assumption-array
                                                                           assumption-array-num-valid-nodes
                                                                           print)
                                bound))
  :hints (("Goal" :in-theory (enable maybe-replace-args-using-assumption-array))))

;; use all-consp as the normal form
(defthm all-myquotep-of-maybe-replace-args-using-assumption-array
  (implies (and (all-dargp args)
                (assumption-arrayp 'assumption-array assumption-array)
                (natp assumption-array-num-valid-nodes)
                (<= assumption-array-num-valid-nodes (alen1 'assumption-array assumption-array)))
           (equal (all-myquotep (maybe-replace-args-using-assumption-array args equivs assumption-array assumption-array-num-valid-nodes print))
                  (all-consp (maybe-replace-args-using-assumption-array args equivs assumption-array assumption-array-num-valid-nodes print))))
  :hints (("Goal" :in-theory (enable all-myquotep-when-all-dargp))))
