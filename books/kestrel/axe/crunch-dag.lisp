; Crunching a DAG (i.e., dropping irrelevant nodes from a dag-array in place)
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2021 Kestrel Institute
; Copyright (C) 2016-2020 Kestrel Technology, LLC
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "supporting-nodes") ;reduce? but we need tag-supporters-of-nodes
(local (include-book "kestrel/arithmetic-light/plus" :dir :system))

(local
 (defthm all-<-of-+-of-1-and-maxelem-alt
   (implies (and (all-natp nodenums)
                 (consp nodenums))
            (all-< nodenums (+ 1 (maxelem nodenums))))
   :hints (("Goal" :in-theory (enable all-natp)))))

(local
 (defthm not-<-of-+-of-1-and-maxelem-when-all-<
   (implies (and (all-< nodenums dag-len)
                 (all-natp nodenums)
                 (consp nodenums)
                 (integerp dag-len))
            (not (< dag-len (+ 1 (maxelem nodenums)))))
   :hints (("Goal" :in-theory (enable all-natp)))))

;; TODO: The resulting array may still have irrelevant nodes above the new
;; dag-len, which might slow things down.

;; Returns (mv dag-array dag-len translation-array).
;; TODO: Check this over.
(defun crunch-dag-array-aux (nodenum
                             max-nodenum
                             next-open-spot
                             dag-array-name
                             dag-array
                             dag-len ;do we need to pass this through?
                             tag-array
                             translation-array)
  (declare (xargs :measure (+ 1 (nfix (+ 1 (- max-nodenum nodenum))))
                  :guard (and (natp nodenum)
                              (natp max-nodenum)
                              (natp next-open-spot)
                              (<= next-open-spot nodenum)
                              (pseudo-dag-arrayp dag-array-name dag-array dag-len)
                              (natp dag-len) ;drop?
                              (<= nodenum (+ 1 max-nodenum))
                              (< max-nodenum dag-len)
                              (array1p 'translation-array translation-array)
                              (equal (alen1 'translation-array translation-array) (+ 1 max-nodenum))
                              (translation-arrayp-aux max-nodenum translation-array)
                              (array1p 'tag-array tag-array)
                              (equal (alen1 'tag-array tag-array) (+ 1 max-nodenum)))))
  (if (or (> nodenum max-nodenum)
          (not (mbt (natp nodenum)))
          (not (mbt (natp max-nodenum))))
      (mv dag-array next-open-spot translation-array)
    (if (not (aref1 'tag-array tag-array nodenum))
        ;; This node is not to be kept:
        (crunch-dag-array-aux (+ 1 nodenum) max-nodenum next-open-spot dag-array-name dag-array dag-len tag-array translation-array)
      ;; This node is to be kept:
      (let* ((expr (aref1 dag-array-name dag-array nodenum)))
        (if (variablep expr)
            ;; Keep the node and record the new position:
            (crunch-dag-array-aux (+ 1 nodenum)
                                  max-nodenum
                                  (+ 1 next-open-spot) ;; we've used a spot
                                  dag-array-name
                                  (if (= nodenum next-open-spot)
                                      ;; node is already in the right place:
                                      dag-array
                                    ;; not already in the right place:
                                    (aset1 dag-array-name dag-array next-open-spot expr))
                                  dag-len
                                  tag-array
                                  (aset1 'translation-array translation-array nodenum next-open-spot))
          (let ((fn (ffn-symb expr)))
            (if (eq 'quote fn)
                ;; Node is a quoted constant, so inline it:
                (crunch-dag-array-aux (+ 1 nodenum)
                                      max-nodenum
                                      next-open-spot ;; did not use a spot
                                      dag-array-name
                                      dag-array ;; constant node gets inlined and so is dropped
                                      dag-len
                                      tag-array
                                      (aset1 'translation-array translation-array nodenum expr))
              ;; Node is a regular function call:
              (b* ((args (dargs expr))
                   ((mv erp new-args changep)
                    (translate-args-with-changep args translation-array))
                   ((when erp)
                    (er hard? 'crunch-dag-array-aux "Error crunching DAG.")
                    (mv dag-array dag-len translation-array))
                   ;; TODO: Remove this check (it should never happen):
                   ((when (not (all-dargp-less-than new-args next-open-spot)))
                    (er hard? 'crunch-dag-array-aux "Bad fixed up args crunching DAG.")
                    (mv dag-array dag-len translation-array))
                   (new-expr (cons fn new-args)))
                ;; Keep the node and record the new position:
                (crunch-dag-array-aux (+ 1 nodenum)
                                      max-nodenum
                                      (+ 1 next-open-spot) ;; we've used a spot
                                      dag-array-name
                                      (if (and (not changep)
                                               (= nodenum next-open-spot))
                                          ;; node is unchanged and already in the right place:
                                          dag-array
                                        ;; changed or not already in the right place:
                                        (aset1 dag-array-name dag-array next-open-spot new-expr))
                                      dag-len
                                      tag-array
                                      (aset1 'translation-array translation-array nodenum next-open-spot))))))))))

;; Remove nodes that do not support NODENUMS and renumber the remaining nodes.
;; Returns (mv dag-len dag-array translation-array).
;; Smashes tag-array and 'translation-array.
;; The resulting dag may have dead nodes at positions at and above the returned dag-len.
;; Another option is to go to a dag-lst and then back to a dag.
;; TODO: Look up all the nodeums and return them.
;; TODO: Should this create a new array?  If so, what about the name?
;; TODO: Rebuild the auxililary structures
;; Note that this inlines constant nodes, so some nodes may map to constants.
(defun crunch-dag-array-for-nodenums (nodenums dag-array-name dag-array dag-len)
  (declare (xargs :guard (and (pseudo-dag-arrayp dag-array-name dag-array dag-len)
                              (true-listp nodenums)
                              (consp nodenums) ; so we can find the max
                              (all-natp nodenums)
                              (all-< nodenums dag-len))))
  (let* ((max-nodenum (maxelem nodenums))
         (tag-array (tag-supporters-of-nodes nodenums dag-array-name dag-array 'tag-array (+ 1 max-nodenum)))
         (translation-array (make-empty-array 'translation-array (+ 1 max-nodenum))))
    (crunch-dag-array-aux 0
                          max-nodenum
                          0
                          dag-array-name
                          dag-array
                          dag-len
                          tag-array
                          translation-array)))
