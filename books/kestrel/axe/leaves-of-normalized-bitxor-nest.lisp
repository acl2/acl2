; Extract leaves from a nest of BITXORs in a DAG
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2022 Kestrel Institute
; Copyright (C) 2016-2020 Kestrel Technology, LLC
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "dag-arrays")
(include-book "kestrel/utilities/forms" :dir :system) ;for call-of
(include-book "kestrel/bv/bitxor" :dir :system) ; since this tool knows about bitxor
(local (include-book "kestrel/lists-light/nth" :dir :system))
(local (include-book "kestrel/lists-light/len" :dir :system))
(local (include-book "kestrel/lists-light/cdr" :dir :system))

(local (in-theory (enable consp-of-cdr)))

;; Justifies how constants are handled below:
(thm
 (equal (bitxor (bvchop 1 (ifix x)) y)
        (bitxor x y)))

;; Justifies how constants are handled below:
(thm
 (equal (bitxor x (bvchop 1 (ifix y)))
        (bitxor x y)))

;; This book deals with "normalized" BITXOR nests.  Such a nest contains nested
;; calls of BITXOR.  A normalized nest:
;;
;; 1. is associated to the right.
;;
;; 2. has either no constant or a single constant listed first (as argument 2
;; of the top-level BITXOR).
;;
;; 3. has leaf nodes (nodes that are not BITXORs) that appear
;; in descending order of nodenum as we explore the nest from the top.

;; Extend NODENUMS-ACC with the bitxor leaves of NODENUM, which should point to
;; a normalized BITXOR nest with no constant first argument.  There will be no
;; constant leaves in the bitxor nest, because the nest is normalized and the
;; caller handles a possible constant at the front.  Returns the list of
;; nodenums of the leaves in the nest (in increasing order by nodenum -- the
;; reverse of the order in which they appear in the nest).
(defund leaves-of-normalized-bitxor-nest-aux (nodenum ;if this points to a bitxor nest, that nest is known to be normalized
                                              dag-array dag-len
                                              nodenums-acc)
  (declare (xargs :guard (and (natp nodenum)
                              (pseudo-dag-arrayp 'dag-array dag-array dag-len)
                              (< nodenum dag-len))
                  :measure (nfix (+ 1 nodenum))
                  :guard-hints (("Goal" :in-theory (e/d (nth-of-cdr
                                                         cadr-becomes-nth-of-1)
                                                        (car-becomes-nth-of-0))))))
  (if (not (mbt (natp nodenum)))
      nodenums-acc
    (let* ((expr (aref1 'dag-array dag-array nodenum)))
      (if (and (call-of 'bitxor expr) ; (bitxor <x> <y>)
               (consp (cdr (dargs expr)))
               (not (consp (darg1 expr))) ; a quoted constant should not appear as arg1 since we have handled the top node specially
               (not (consp (darg2 expr))) ; a quoted constant should not appear as arg2 if the nest is normalized
               (mbt (< (darg2 expr) nodenum)))
          ;;expr is of the form (bitxor <arg1> <ar23>).  since the nest is normalized, arg1 cannot be a bitxor and arg2 cannot be a constant
          (leaves-of-normalized-bitxor-nest-aux (darg2 expr) dag-array dag-len (cons (darg1 expr) nodenums-acc))
        ;; Not a suitable bitxor:
        (cons nodenum nodenums-acc)))))

(defthm true-listp-of-leaves-of-normalized-bitxor-nest-aux
  (implies (true-listp nodenums-acc)
           (true-listp (leaves-of-normalized-bitxor-nest-aux nodenum dag-array dag-len nodenums-acc)))
  :hints (("Goal" :in-theory (enable leaves-of-normalized-bitxor-nest-aux))))

(defthm all-integerp-of-leaves-of-normalized-bitxor-nest-aux
  (implies (and (natp nodenum)
                (pseudo-dag-arrayp 'dag-array dag-array dag-len)
                (< nodenum dag-len)
                (all-integerp nodenums-acc))
           (all-integerp (leaves-of-normalized-bitxor-nest-aux nodenum dag-array dag-len nodenums-acc)))
  :hints (("Goal" :in-theory (enable leaves-of-normalized-bitxor-nest-aux))))

(defthm bounded-darg-listp-of-leaves-of-normalized-bitxor-nest-aux
  (implies (and (natp nodenum)
                (pseudo-dag-arrayp 'dag-array dag-array dag-len)
                (< nodenum dag-len)
                (bounded-darg-listp nodenums-acc dag-len))
           (bounded-darg-listp (leaves-of-normalized-bitxor-nest-aux nodenum dag-array dag-len nodenums-acc) dag-len))
  :hints (("Goal" :in-theory (enable leaves-of-normalized-bitxor-nest-aux))))

;fixme handle bvnots (by negating the accumulated-constant and stripping the not).  or we could rely on rules to do that.
;applies to an already-normalized bitxor nest (constant comes first [if any], nest is associated to the right and leaves are in descending order of nodenum)
;; Returns (mv accumulated-constant rev-leaf-nodenums) where leaf-nodenums is sorted in increasing order (the opposite of the nest).
; NODENUM-OR-QUOTEP should be an argument to a BITXOR.
(defund leaves-of-normalized-bitxor-nest (nodenum-or-quotep ;if this points to bitxor nest, that nest is known to be normalized
                                          dag-array
                                          dag-len)
  (declare (xargs :guard (and (pseudo-dag-arrayp 'dag-array dag-array dag-len)
                              (dargp-less-than nodenum-or-quotep dag-len))
                  :guard-hints (("Goal" :in-theory (e/d (nth-of-cdr cadr-becomes-nth-of-1)
                                                        (car-becomes-nth-of-0))))))
  (if (consp nodenum-or-quotep) ;checks for quotep
      ;; Just the constant and no nodenums:
      (mv (bvchop 1 (ifix (unquote nodenum-or-quotep)))
          nil)
    (let* ((expr (aref1 'dag-array dag-array nodenum-or-quotep)))
      (if (and (call-of 'bitxor expr)
               (consp (cdr (dargs expr)))
               (not (consp (darg2 expr))) ;actually known to be true (can't be a constant since the bitxor nest is normalized)
               )
          ;; It's of the form (bitxor <arg1> <arg2>).  Use arg1 (which
          ;; might be a constant) to initialize the constant and nodenums-acc:
          (mv-let (constant nodenums-acc)
            (let ((arg1 (darg1 expr)))
              (if (consp arg1) ;checks for quotep
                  (mv (bvchop 1 (ifix (unquote arg1)))
                      nil)
                (mv 0
                    (list arg1))))
            (mv constant
                (leaves-of-normalized-bitxor-nest-aux (darg2 expr) dag-array dag-len nodenums-acc)))
        ;;not a bitxor nest:
        (mv 0
            (list nodenum-or-quotep))))))

(defthm natp-of-mv-nth-0-of-leaves-of-normalized-bitxor-nest
  (natp (mv-nth 0 (leaves-of-normalized-bitxor-nest nodenum-or-quotep dag-array dag-len)))
  :hints (("Goal" :in-theory (enable leaves-of-normalized-bitxor-nest))))

(defthm true-listp-of-mv-nth-1-of-leaves-of-normalized-bitxor-nest
  (true-listp (mv-nth 1 (leaves-of-normalized-bitxor-nest nodenum-or-quotep dag-array dag-len)))
  :hints (("Goal" :in-theory (enable leaves-of-normalized-bitxor-nest))))

(defthm all-integerp-of-mv-nth-1-of-leaves-of-normalized-bitxor-nest
  (implies (and (pseudo-dag-arrayp 'dag-array dag-array dag-len)
                (dargp-less-than nodenum-or-quotep dag-len))
           (all-integerp (mv-nth 1 (leaves-of-normalized-bitxor-nest nodenum-or-quotep dag-array dag-len))))
  :hints (("Goal" :in-theory (enable leaves-of-normalized-bitxor-nest))))

(defthm bounded-darg-listp-of-leaves-of-normalized-bitxor-nest
  (implies (and (pseudo-dag-arrayp 'dag-array dag-array dag-len)
                (dargp-less-than nodenum-or-quotep dag-len))
           (bounded-darg-listp (mv-nth 1 (leaves-of-normalized-bitxor-nest nodenum-or-quotep dag-array dag-len)) dag-len))
  :hints (("Goal" :in-theory (enable leaves-of-normalized-bitxor-nest))))
