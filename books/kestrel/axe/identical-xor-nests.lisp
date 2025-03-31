; Quickly recognizing identical xor nests
;
; Copyright (C) 2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "normalize-xors")
(local (include-book "kestrel/acl2-arrays/acl2-arrays" :dir :system))
(local (include-book "kestrel/lists-light/nth" :dir :system))
(local (include-book "kestrel/lists-light/len" :dir :system))
(local (include-book "kestrel/typed-lists-light/nat-listp" :dir :system))
(local (include-book "kestrel/arithmetic-light/plus" :dir :system))
(local (include-book "kestrel/arithmetic-light/natp" :dir :system))
(local (include-book "kestrel/arithmetic-light/types" :dir :system))

;; some of these may not be needed
(local (in-theory (e/d (consp-of-cdr
                        nth-of-cdr
                        myquotep-of-nth-when-darg-listp
                        <-of-+-of-1-when-integers
                        natp-of-+-of-1
                        rationalp-when-integerp
                        car-becomes-nth-of-0)
                       (nat-listp
                        natp
                        dag-exprp
                           ;;list::len-when-at-most-1
                        all-natp-when-not-consp
                        all-<-when-not-consp
                        darg-listp-when-not-consp
                           ;; for speed:
                        all-<=-when-not-consp
                        all-<-transitive-free
                        not-<-of-nth-of-dargs-of-aref1-when-pseudo-dag-arrayp-2
                        <=-of-nth-when-all-<= ;disable globally?
                        rational-listp
                        strip-cdrs
                        ifix ; avoid case splits
                        rational-listp maxelem ;prevent inductions
                        not-<-of-nth-when-all-<
                        ))))

;; Do not remove.  These justify the ifixing of constants below
(thm (equal (bitxor (ifix x) y) (bitxor x y)))
(thm (equal (bitxor x (ifix y)) (bitxor x y)))

;; If DARG is a nodenum, combines it with WORKLIST (possibly removing it and a duplicate).
;; If DARG is a constant, bitxors it into CONSTANT.
;; Returns (mv worklist constant).
;; The bitxor of the resulting worklist and constant is equivalent to the bitxor of all 3 arguments.
(defund combine-bitxor-darg-with-worklist-or-constant (darg worklist constant)
  (declare (xargs :guard (and (dargp darg)
                              (nat-listp worklist)
                              (decreasingp worklist)
                              (integerp constant))))
  (if (consp darg) ; checks for quotep
      ;; darg is a quoted constant:
      ;; todo: print a warning if the constant is not a bit?  or not an integer?
      (mv worklist (bitxor (ifix (unquote darg)) constant))
    ;; darg is a nodenum:
    (mv (insert-into-sorted-list-and-remove-dups darg worklist) constant)))

(local
 (defthm nat-listp-of-mv-nth-0-of-combine-bitxor-darg-with-worklist-or-constant
   (implies (and (dargp darg)
                 (nat-listp worklist))
            (nat-listp (mv-nth 0 (combine-bitxor-darg-with-worklist-or-constant darg worklist constant))))
   :hints (("Goal" :in-theory (enable combine-bitxor-darg-with-worklist-or-constant)))))

(local
 (defthm all-<-of-mv-nth-0-of-combine-bitxor-darg-with-worklist-or-constant
   (implies (and (if (consp darg) t (< darg bound))
                 (all-< worklist bound))
            (all-< (mv-nth 0 (combine-bitxor-darg-with-worklist-or-constant darg worklist constant)) bound))
   :hints (("Goal" :in-theory (enable combine-bitxor-darg-with-worklist-or-constant)))))

(local
 (defthm decreasingp-of-mv-nth-0-of-combine-bitxor-darg-with-worklist-or-constant
   (implies (and (dargp darg)
                 (nat-listp worklist) ; drop?
                 (decreasingp worklist))
            (decreasingp (mv-nth 0 (combine-bitxor-darg-with-worklist-or-constant darg worklist constant))))
   :hints (("Goal" :in-theory (enable combine-bitxor-darg-with-worklist-or-constant)))))

(local
 (defthm integerp-of-mv-nth-1-of-combine-bitxor-darg-with-worklist-or-constant
   (implies (integerp constant)
            (integerp (mv-nth 1 (combine-bitxor-darg-with-worklist-or-constant darg worklist constant))))
   :hints (("Goal" :in-theory (enable combine-bitxor-darg-with-worklist-or-constant)))))

(local
 (defthmd not-equal-of-nth-0-and-nth1-when-decreasingp
   (implies (and (decreasingp x)
                 (nat-listp x))
            (equal (equal (nth 0 x) (nth 1 x))
                   (not (consp x))))
   :hints (("Goal" :in-theory (enable decreasingp)))))

;; Checks whether the bitxor of constant1 and all the nodes in worklist1 is equal to the bitxor of constant2 and all the nodes in worklist2.
;; In this "double worklist" algorithm, we traverse the supporters of both nodes, always taking the highest unprocessed node from the 2 worklists.
;; The worklists are maintained in decreasing order.
;; Shared nodes (whether xors or not) are detected and cancelled out without exploration.
;; This should be very fast when the non-shared parts of the 2 nests are small.
;; TODO: Add a version for BVXOR
(defun identical-bitxor-nestsp (worklist1 worklist2 constant1 constant2 dag-array-name dag-array dag-len)
  (declare (xargs :guard (and (nat-listp worklist1)
                              (decreasingp worklist1)
                              (nat-listp worklist2)
                              (decreasingp worklist2)
                              (integerp constant1) ; strengthen?
                              (integerp constant2) ; strengthen?
                              (pseudo-dag-arrayp dag-array-name dag-array dag-len)
                              (all-< worklist1 dag-len)
                              (all-< worklist2 dag-len))
                  :measure (+ (if (and (consp worklist1)
                                       (consp worklist2))
                                  (+ 1 (nfix (max (first worklist1) (first worklist2))))
                                0))
                  :hints (("Goal"
                           :in-theory (enable not-equal-of-nth-0-and-nth1-when-decreasingp
                                              <-of-nth-when-all-<
                                              <-of-nth-1-and-nth-0-when-decreasingp)))))
  (if (not (mbt (and (nat-listp worklist1)  ;; for termination
                     (decreasingp worklist1)
                     (nat-listp worklist2)
                     (decreasingp worklist2)
                     (pseudo-dag-arrayp dag-array-name dag-array dag-len)
                     (all-< worklist1 dag-len)
                     (all-< worklist2 dag-len))))
      nil ; should not happen, but we can just say the nests are not identical
    (if (endp worklist1)
        (if (endp worklist2)
            ;; both worklists are empty (all nodes have cancelled out), so just check the constants (todo: should we chop the constants):
            (= (the integer constant1) (the integer constant2))
          ;; nodes remain in worklist2 only (todo: they could be all constants that make this work out, I guess)
          nil)
      (if (endp worklist2)
          ;; nodes are left in worklist1 only (todo: they could be all constants that make this work out, I guess)
          nil
        ;; nodes are present in both worklists:
        (let ((node1 (first worklist1))
              (node2 (first worklist2)))
          (if (= (the (unsigned-byte 60) node1)
                 (the (unsigned-byte 60) node2))
              ;; shared node, cancel it by removing it from both lists:
              (identical-bitxor-nestsp (rest worklist1) (rest worklist2) constant1 constant2 dag-array-name dag-array dag-len)
            ;; the nodes differ, so we process whichever node is greater:
            (if (> node1 node2)
                ;; We'll process node1:
                (let ((expr (aref1 dag-array-name dag-array node1)))
                  (if (and (call-of 'bitxor expr)
                           (= 2 (len (dargs expr))))
                      ;; "Expand" node1 (it is a bitxor, and we know it is not shared):
                      ;; We remove it but add both its args, thus preserving the xor of the constant and the worklist
                      (b* ((darg1 (first (dargs expr)))
                           (darg2 (second (dargs expr)))
                           (worklist1 (rest worklist1)) ; remove node1
                           ;; Handle darg1:
                           ((mv worklist1 constant1)
                            (combine-bitxor-darg-with-worklist-or-constant darg1 worklist1 constant1))
                           ;; Handle darg2:
                           ((mv worklist1 constant1)
                            (combine-bitxor-darg-with-worklist-or-constant darg2 worklist1 constant1)))
                        (identical-bitxor-nestsp worklist1 worklist2 constant1 constant2 dag-array-name dag-array dag-len))
                    ;; node1 is not a bitxor, and we know it is not present in the other worklist, so fail (todo: maybe deference constant a node here):
                    nil))
              ;; We'll process node2:
              (let ((expr (aref1 dag-array-name dag-array node2)))
                (if (and (call-of 'bitxor expr)
                         (= 2 (len (dargs expr))))
                    ;; Expand node2 (it is a bitxor, and we know it is not shared):
                    ;; We remove it but add both its args, thus preserving the xor of the constant and the worklist
                    (b* ((darg1 (first (dargs expr)))
                         (darg2 (second (dargs expr)))
                         (worklist2 (rest worklist2)) ; remove node2
                         ;; Handle darg1:
                         ((mv worklist2 constant2)
                          (combine-bitxor-darg-with-worklist-or-constant darg1 worklist2 constant2))
                         ;; Handle darg2:
                         ((mv worklist2 constant2)
                          (combine-bitxor-darg-with-worklist-or-constant darg2 worklist2 constant2)))
                      (identical-bitxor-nestsp worklist1 worklist2 constant1 constant2 dag-array-name dag-array dag-len))
                  ;; node2 is not a bitxor, and we know the node is not present in the other worklist, so fail (todo: maybe deference constant a node here):
                  nil)))))))))
