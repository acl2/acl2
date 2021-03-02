; Extract leaves from a nest of BVXORs in a DAG
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

(include-book "dag-arrays")
(include-book "kestrel/utilities/forms" :dir :system) ;for call-of
(include-book "kestrel/bv/bvxor" :dir :system) ; since this tool knows about bvxor
(local (include-book "kestrel/lists-light/nth" :dir :system))

;; Justifies how constants are handled below:
(thm
 (implies (natp size)
          (equal (bvxor size (bvchop size (ifix x)) y)
                 (bvxor size x y))))

;; Justifies how constants are handled below:
(thm
 (implies (natp size)
          (equal (bvxor size x (bvchop size (ifix y)))
                 (bvxor size x y))))

;; This book deals with "normalized" BVXOR nests.  Such a nest contains nested
;; calls of BVXOR, all with the same size argument.  A normalized nest:
;;
;; 1. is associated to the right.
;;
;; 2. has either no constant or a single constant listed first (as argument 2
;; of the top-level BVXOR).
;;
;; 3. has leaf nodes (nodes that are not BVXORs of the given size) that appear
;; in descending order or nodenum as we explore the nest from the top.

;; Extend NODENUMS-ACC with the bvxor leaves of NODENUM, which should point to
;; a normalized BVXOR nest with no constant first argument.  There will be no
;; constant leaves in the bvxor nest, because the nest is normalized and the
;; caller handles a possible constant at the front.  Returns the list of
;; nodenums of the leaves in the nest (in increasing order by nodenum -- the
;; reverse of the order in which they appear in the nest).
(defund leaves-of-normalized-bvxor-nest-aux (nodenum ;if this points to bvxor nest, that nest is known to be normalized
                                             size    ;not quoted
                                             dag-array-name dag-array dag-len
                                             nodenums-acc)
  (declare (xargs :measure (nfix (+ 1 nodenum))
                  :guard (and (pseudo-dag-arrayp dag-array-name dag-array dag-len)
                              (natp nodenum)
                              (< nodenum dag-len)
                              (natp size))
                  :guard-hints (("Goal" :in-theory (e/d (nth-of-cdr cadr-becomes-nth-of-1
                                                                    pseudo-dag-arrayp ;todo
                                                                    )
                                                        (car-becomes-nth-of-0))))))
  (if (not (mbt (natp nodenum)))
      nodenums-acc
    (let* ((expr (aref1 dag-array-name dag-array nodenum)))
      (if (and (call-of 'bvxor expr)
               (= 3 (len (dargs expr)))
               (let ((size-arg (darg1 expr)))
                 (and (consp size-arg) ;the size argument must be a quotep
                      (eql size (unquote size-arg))))
               (not (consp (darg3 expr))) ;todo: check for error
               (mbt (< (darg3 expr) nodenum)))
          ;;expr is of the form (bvxor '<size> <arg2> <arg3>)  since the nest is normalized, arg2 cannot be a bvxor and arg3 cannot be a constant
          (leaves-of-normalized-bvxor-nest-aux (darg3 expr) size dag-array-name dag-array dag-len (cons (darg2 expr) nodenums-acc))
        (cons nodenum nodenums-acc)))))

;fixme handle bvnots (by negating the accumulated-constant and stripping the not).  or we could rely on rules to do that.
;applies to an already-normalized bvxor nest (constant comes first [if any], nest is associated to the right and leaves are in descending order or nodenum)
;returns (mv accumulated-constant rev-leaf-nodenums) where leaf-nodenums is sorted in increasing order (the opposite of the nest)
; NODENUM-OR-QUOTEP should be an argument to a BVXOR whose size argument is (quote SIZE).
(defund leaves-of-normalized-bvxor-nest (nodenum-or-quotep ;if this points to bvxor nest, that nest is known to be normalized
                                         size ;the unquoted size of the bvxor nest
                                         dag-array-name dag-array
                                         dag-len)
  (declare (xargs :guard  (and (pseudo-dag-arrayp dag-array-name dag-array dag-len)
                               (dargp-less-than nodenum-or-quotep dag-len)
                               (natp size))
                  :guard-hints (("Goal" :in-theory (e/d (nth-of-cdr cadr-becomes-nth-of-1)
                                                        (car-becomes-nth-of-0
                                                         pseudo-dag-arrayp ;todo
                                                         ))))))
  (if (consp nodenum-or-quotep) ;checks for quotep
      (mv (bvchop size (ifix (unquote nodenum-or-quotep))) ;FIXME: the ifix was needed for acl2 5.0;  we had a call to :fake here.
          nil)
    (let* ((expr (aref1 dag-array-name dag-array nodenum-or-quotep)))
      (if (and (call-of 'bvxor expr)
               (= 3 (len (dargs expr)))
               (let ((size-arg (darg1 expr)))
                 (and (consp size-arg) ;the size argument must be a quotep
                      ;; must be the right size:
                      (eql size (unquote size-arg))))
               (not (consp (darg3 expr))) ;actually known to be true (can't be a constant since the bvxor nest is normalized)
               )
          ;; It's of the form (bvxor '<size> <arg2> <arg3>).  Use arg2 (which
          ;; might be a constant) to initialize the constant and nodenums-acc:
          (mv-let (constant nodenums-acc)
            (let ((arg2 (darg2 expr)))
              (if (consp arg2) ;checks for quotep
                  (mv (bvchop size (ifix (unquote arg2)))
                      nil)
                (mv 0
                    (list arg2))))
            (mv constant
                (leaves-of-normalized-bvxor-nest-aux (darg3 expr)
                                                     size dag-array-name dag-array dag-len nodenums-acc)))
        ;;not a bvxor nest of the right size:
        (mv 0
            (list nodenum-or-quotep))))))
