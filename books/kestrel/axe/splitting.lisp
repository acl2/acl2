; Support for the Axe Prover splitting a proof into cases
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

(include-book "dag-arrays")
(include-book "worklists")
(include-book "kestrel/utilities/forms" :dir :system) ; for call-of
(local (include-book "kestrel/lists-light/nth" :dir :system))
(local (include-book "kestrel/lists-light/cons" :dir :system))
(local (include-book "kestrel/lists-light/len" :dir :system))
(local (include-book "kestrel/arithmetic-light/plus" :dir :system))
(local (include-book "kestrel/typed-lists-light/nat-listp" :dir :system))

;dup
(defthmd natp-of-+-of-1-alt
  (implies (integerp x)
           (equal (natp (+ 1 x))
                  (<= -1 x)))
  :hints (("Goal" :in-theory (enable natp))))

(defthm not-<-of-car-when-nat-listp
  (Implies (and (syntaxp k)
                (<= k 0)
                (nat-listp x))
           (not (< (CAR x) k)))
  :hints (("Goal" :in-theory (enable nat-listp))))

;strip off any number of nested calls to not
;returns the "core" nodenum, or nil if the "core" is a constant
(defund strip-nots (nodenum-or-quotep dag-array-name dag-array)
  (declare (xargs :guard (if (natp nodenum-or-quotep)
                             (pseudo-dag-arrayp dag-array-name dag-array (+ 1 nodenum-or-quotep))
                           t)
                  :guard-hints (("Goal" :in-theory (enable car-becomes-nth-of-0)))
                  :measure (nfix nodenum-or-quotep)))
  (if (not (natp nodenum-or-quotep)) ;(quotep nodenum-or-quotep)
      nil
    (let ((expr (aref1 dag-array-name dag-array nodenum-or-quotep)))
      (if (quotep expr)
          nil
        (if (and (call-of 'not expr)
                 (= 1 (len (dargs expr)))
                 (not (consp (darg1 expr))) ;todo: other case?
                 )
            (if (not (and (natp (darg1 expr))
                          (mbt (< (darg1 expr) nodenum-or-quotep))))
                :error
              ;; keep looking:
              (strip-nots (darg1 expr) dag-array-name dag-array))
          nodenum-or-quotep ;we've found the "core" node
          )))))

(defthm natp-of-strip-nots
  (implies (and (strip-nots nodenum-or-quotep dag-array-name dag-array)
                (if (natp nodenum-or-quotep)
                    (pseudo-dag-arrayp dag-array-name dag-array (+ 1 nodenum-or-quotep))
                  t))
           (natp (strip-nots nodenum-or-quotep dag-array-name dag-array)))
  :hints (("Goal" :in-theory (enable strip-nots car-becomes-nth-of-0))))

(defthm strip-nots-when-consp
  (implies (consp nodenum-or-quotep)
           (equal (strip-nots nodenum-or-quotep dag-array-name dag-array)
                  nil))
  :hints (("Goal" :in-theory (enable strip-nots))))

(defthm <-of-strip-nots
  (implies (and (dargp-less-than nodenum-or-quotep dag-len)
                (if (natp nodenum-or-quotep)
                    (pseudo-dag-arrayp dag-array-name dag-array (+ 1 nodenum-or-quotep))
                  t)
                (strip-nots nodenum-or-quotep dag-array-name dag-array))
           (< (strip-nots nodenum-or-quotep dag-array-name dag-array) dag-len))
  :hints (("Goal" :in-theory (enable strip-nots))))

;;;
;;; strip-nots-and-maybe-extend
;;;

;; Strip NOTs and add the resulting nodenum to ACC (if the stripped thing is a constant, just return ACC).
(defund strip-nots-and-maybe-extend (nodenum-or-quotep dag-array-name dag-array acc)
  (declare (xargs :guard (if (natp nodenum-or-quotep)
                             (pseudo-dag-arrayp dag-array-name dag-array (+ 1 nodenum-or-quotep))
                           t)))
  (let ((res (strip-nots nodenum-or-quotep dag-array-name dag-array)))
    (if res
        (cons res acc)
      acc)))

(defthm strip-nots-and-maybe-extend-when-consp
  (implies (consp nodenum-or-quotep)
           (equal (strip-nots-and-maybe-extend nodenum-or-quotep dag-array-name dag-array acc)
                  acc))
  :hints (("Goal" :in-theory (enable strip-nots-and-maybe-extend))))

(defthm true-listp-of-strip-nots-and-maybe-extend
  (equal (true-listp (strip-nots-and-maybe-extend nodenum-or-quotep dag-array-name dag-array acc))
         (true-listp acc))
  :hints (("Goal" :in-theory (enable strip-nots-and-maybe-extend))))

(defthm all-natp-of-strip-nots-and-maybe-extend
  (implies (and (dargp nodenum-or-quotep)
                (if (not (consp nodenum-or-quotep))
                    (pseudo-dag-arrayp dag-array-name dag-array (+ 1 nodenum-or-quotep))
                  t))
           (equal (all-natp (strip-nots-and-maybe-extend nodenum-or-quotep dag-array-name dag-array acc))
                  (all-natp acc)))
  :hints (("Goal" :in-theory (enable strip-nots-and-maybe-extend))))

(defthm all-<-of-strip-nots-and-maybe-extend
  (implies (and (all-< acc dag-len)
                (dargp-less-than nodenum-or-quotep dag-len)
                (if (natp nodenum-or-quotep)
                    (pseudo-dag-arrayp dag-array-name dag-array (+ 1 nodenum-or-quotep))
                  t))
           (all-< (strip-nots-and-maybe-extend nodenum-or-quotep dag-array-name dag-array acc) dag-len))
  :hints (("Goal" :in-theory (enable strip-nots-and-maybe-extend))))

;;;
;;; strip-nots-lst
;;;

;returns a list of nodenums (omits constants and nodenums of constants)
(defund strip-nots-lst (nodenums dag-array-name dag-array dag-len)
  (declare (xargs :guard (and (pseudo-dag-arrayp dag-array-name dag-array dag-len)
                              (nat-listp nodenums)
                              (all-< nodenums dag-len))))
  (if (endp nodenums)
      nil
    (let ((res (strip-nots (first nodenums) dag-array-name dag-array)))
      (if res
          (cons res
                (strip-nots-lst (rest nodenums) dag-array-name dag-array dag-len))
        (strip-nots-lst (rest nodenums) dag-array-name dag-array dag-len)))))

(defthm all-natp-of-strip-nots-lst
  (implies (and (pseudo-dag-arrayp dag-array-name dag-array dag-len)
                (nat-listp nodenums)
                (all-< nodenums dag-len))
           (all-natp (strip-nots-lst nodenums dag-array-name dag-array dag-len)))
  :hints (("Goal" :in-theory (enable strip-nots-lst nat-listp))))

;;;
;;; maybe-add-split-candidates
;;;

;; Possibly extends ACC with one or more nodenums to consider for splitting.  The
;; nodenums returned should not have exprs that are calls of NOT.
;; TODO: Consider splitting on arguments of boolfix.
(defund maybe-add-split-candidates (expr dag-array-name dag-array dag-len acc)
  (declare (xargs :guard (and (pseudo-dag-arrayp dag-array-name dag-array dag-len)
                              (bounded-dag-exprp dag-len ;upper bound
                                         expr))
                  :guard-hints (("Goal" :in-theory (enable bounded-dag-exprp dag-exprp0 car-becomes-nth-of-0)
                                 :do-not '(generalize eliminate-destructors))))
           (ignore dag-len))
  (if (variablep expr)
      acc
    (let* ((fn (ffn-symb expr)))
      (if (eq 'quote fn) ;can this happen?
          acc
        (let ((args (dargs expr)))
          ;;instead of skipping the nots, just include not as a function here?  then x will have a smaller size than (not x) in the size array
          (cond ((and (or (eq 'myif fn) (eq 'if fn))
                      (= 3 (len args)))
                 (strip-nots-and-maybe-extend (first args) dag-array-name dag-array acc))
                ((and (eq fn 'bvif)
                      (= 4 (len args)))
                 (strip-nots-and-maybe-extend (second args) dag-array-name dag-array acc)) ;the test of the bvif is arg2
                ((and (eq fn 'bool-to-bit) ;new
                      (= 1 (len args)))
                 (strip-nots-and-maybe-extend (first args) dag-array-name dag-array acc))
                ;; might we ever not want to split on the argument of a boolor or booland?
                ;; should we split for a boolxor?
;fffixme the args to booland (say) may be boolands, so we want to strip the bool ops (not just nots!) from them too. i guess we'll take the smallest node, but we may waste time (when using this to split a miter) checking whether these booland nodes (which we should never split on) have both true and false test cases...
                ((and (member-eq fn '(boolor booland boolxor))
                      (= 2 (len args)))
                 (strip-nots-and-maybe-extend (first args) dag-array-name dag-array
                                              (strip-nots-and-maybe-extend (second args) dag-array-name dag-array acc)))
                ;;which one should we choose?
                ((and (eq fn 'boolif)
                      (= 3 (len args)))
                 (strip-nots-and-maybe-extend (first args) dag-array-name dag-array
                                              (strip-nots-and-maybe-extend (second args) dag-array-name dag-array
                                                                           (strip-nots-and-maybe-extend (third args) dag-array-name dag-array acc))))
                ;;equality of a pred and something else..
                ((and (eq fn 'iff) ;had 'equal here but the prover had trouble using the fact that the arg was non-nil
                      (= 2 (len args)))
                 (let ((arg1 (first args)))
                   (if (and (integerp arg1)
                            (let ((arg1-expr (aref1 dag-array-name dag-array arg1)))
                              (and (consp arg1-expr)
                                   ;; Do we need this check?:
                                   ;;(member-eq (ffn-symb arg1-expr) *known-predicates-except-not-basic*) ;or pass in a list of known booleans
                                   )))
                       (strip-nots-and-maybe-extend arg1 dag-array-name dag-array acc) ;fixme what about arg2?
                     (let ((arg2 (second args)))
                       (if (and (integerp arg2)
                                (let ((arg2-expr (aref1 dag-array-name dag-array arg2)))
                                  (and (consp arg2-expr)
                                       ;; Do we need this check?:
                                       ;;(member-eq (ffn-symb arg2-expr) *known-predicates-except-not-basic*) ;or pass in a list of known booleans
                                       )))
                           (strip-nots-and-maybe-extend arg2 dag-array-name dag-array acc)
                         acc)))))
                (t acc)))))))

(defthm true-listp-of-maybe-add-split-candidates
  (equal (true-listp (maybe-add-split-candidates expr dag-array-name dag-array dag-len acc))
         (true-listp acc))
  :hints (("Goal" :in-theory (enable maybe-add-split-candidates))))

(defthm all-natp-of-maybe-add-split-candidates
  (implies (and (pseudo-dag-arrayp dag-array-name dag-array dag-len)
                (bounded-dag-exprp dag-len ;upper bound
                           expr)
                (all-natp acc))
           (all-natp (maybe-add-split-candidates expr dag-array-name dag-array dag-len acc)))
  :hints (("Goal" :cases ((integerp (nth '0 (dargs$inline expr))))
           :in-theory (e/d (maybe-add-split-candidates
                            car-becomes-nth-of-0
                            bounded-dag-exprp
                            ;STRIP-NOTS-AND-MAYBE-EXTEND
                            ;;<-of-+-of-1-when-integers
                            NATP-OF-+-OF-1-ALT)
                           (dargp natp)))))

(defthm all-<-of-maybe-add-split-candidates
  (implies (and (pseudo-dag-arrayp dag-array-name dag-array dag-len)
                (bounded-dag-exprp dag-len ;upper bound
                           expr)
                (all-< acc dag-len))
           (all-< (maybe-add-split-candidates expr dag-array-name dag-array dag-len acc)
                  dag-len))
  :hints (("Goal" :cases ((integerp (nth '0 (dargs$inline expr))))
           :in-theory (e/d (maybe-add-split-candidates
                            car-becomes-nth-of-0
                            bounded-dag-exprp
                            ;STRIP-NOTS-AND-MAYBE-EXTEND
                            ;;<-of-+-of-1-when-integers
                            NATP-OF-+-OF-1-ALT)
                           (dargp natp)))))

;; (defthm all-natp-of-maybe-add-split-candidates
;;   (implies (and (pseudo-dag-arrayp dag-array-name dag-array dag-len)
;;                 (bounded-dag-exprp dag-len ;upper bound
;;                            expr))
;;            (equal (all-natp (maybe-add-split-candidates expr dag-array-name dag-array dag-len acc))
;;                   (all-natp acc)))
;;   :hints (("Goal" :in-theory (enable maybe-add-split-candidates BOUNDED-DAG-EXPRP DAG-EXPRP0))))

;; Similar to get-args-not-done and especially to get-unexamined-nodenum-args.
(defund extend-with-not-done-args (args result-array-name result-array acc)
  (declare (xargs :guard (and (array1p result-array-name result-array)
                              (true-listp args)
                              (all-dargp-less-than args (alen1 result-array-name result-array)))))
  (if (endp args)
      acc
    (let* ((arg (first args)))
      (if (or (consp arg) ;it's a quotep, so skip it
              (aref1 result-array-name result-array arg) ;it's tagged as done, so skip it
              )
          (extend-with-not-done-args (rest args) result-array-name result-array acc)
        ;; add the arg:
        (extend-with-not-done-args (rest args) result-array-name result-array (cons arg acc))))))

(defthm nat-listp-of-extend-with-not-done-args
  (implies (and (nat-listp acc)
                (all-dargp args))
           (nat-listp (extend-with-not-done-args args result-array-name result-array acc)))
  :hints (("Goal" :in-theory (enable nat-listp extend-with-not-done-args))))

(defthm all-<-of-extend-with-not-done-args
  (implies (and (all-< acc bound)
                (all-dargp-less-than args bound))
           (all-< (extend-with-not-done-args args result-array-name result-array acc) bound))
  :hints (("Goal" :in-theory (enable extend-with-not-done-args))))

(local (in-theory (disable nat-listp)))

;this never adds to acc any nodes that are calls of not
;the result may contain duplicates
;; TODO: Use worklist-array and make this a standard worklist algorithm?
(defund find-node-to-split-candidates-work-list (worklist dag-array-name dag-array dag-len
                                                          done-array ;tracks which nodenums we have already considered
                                                          acc)
  (declare (xargs :measure (make-ord 1
                                     (+ 1 ;coeff must be positive
                                        (if (not (natp (alen1 'done-array done-array)))
                                            0
                                          (+ 1 (- (alen1 'done-array done-array)
                                                  (num-handled-nodes 'done-array done-array)))))
                                     (len worklist))
                  :guard (and (nat-listp worklist)
                              (pseudo-dag-arrayp dag-array-name dag-array dag-len)
                              (array1p 'done-array done-array)
                              (all-< worklist (alen1 'done-array done-array))
                              (all-< worklist dag-len))))
  (if (or (endp worklist)
          (not (mbt (array1p 'done-array done-array)))
          (not (mbt (nat-listp worklist)))
          (not (mbt (all-< worklist (alen1 'done-array done-array)))))
      acc
    (let ((nodenum (first worklist)))
      (if (aref1 'done-array done-array nodenum)
          (find-node-to-split-candidates-work-list (rest worklist) dag-array-name dag-array dag-len done-array acc)
        (let* ((expr (aref1 dag-array-name dag-array nodenum))
               (acc (maybe-add-split-candidates expr dag-array-name dag-array dag-len acc))) ;can this add more than one candidate?
          (find-node-to-split-candidates-work-list (if (or (variablep expr)
                                                           (quotep expr))
                                                       worklist
;fixme could just add all nodes to the worklist (would save arefs at the expense of consing) - similar changes elsewhere?
;fixme could tag nodes as soon as they are added to the worklist? might prevent them from being added more than once...
                                                     (extend-with-not-done-args (dargs expr) 'done-array done-array worklist))
                                                   dag-array-name dag-array dag-len
                                                   (aset1-safe 'done-array done-array nodenum t)
                                                   acc))))))

(defthm true-listp-of-find-node-to-split-candidates-work-list
  (equal (true-listp (find-node-to-split-candidates-work-list worklist dag-array-name dag-array dag-len done-array acc))
         (true-listp acc))
  :hints (("Goal" :in-theory (enable find-node-to-split-candidates-work-list))))

(defthm all-natp-of-find-node-to-split-candidates-work-list
  (implies (and (all-natp acc)
                (nat-listp worklist)
                (pseudo-dag-arrayp dag-array-name dag-array dag-len)
                (array1p 'done-array done-array)
                (all-< worklist (alen1 'done-array done-array))
                (all-< worklist dag-len))
           (all-natp (find-node-to-split-candidates-work-list worklist dag-array-name dag-array dag-len done-array acc)))
  :hints (("Goal" :in-theory (enable find-node-to-split-candidates-work-list))))

(defund smallest-size-node-aux (nodenums current-smallest-size current-smallest-node size-array size-array-len)
  (declare (xargs :guard (and (all-natp nodenums)
                              (true-listp nodenums)
                              (array1p 'size-array size-array)
                              (natp size-array-len)
                              (<= size-array-len
                                  (alen1 'size-array size-array))
                              (all-< nodenums size-array-len)
                              (natp current-smallest-size))
                  :guard-hints (("Goal" :in-theory (disable car-becomes-nth-of-0)))))
  (if (endp nodenums)
      current-smallest-node
    (let* ((next-nodenum (first nodenums))
           (next-size (nfix (aref1 'size-array size-array next-nodenum)))) ;todo: drop the nfix
      (if (< next-size current-smallest-size)
          (smallest-size-node-aux (rest nodenums) next-size next-nodenum size-array size-array-len)
        (smallest-size-node-aux (rest nodenums) current-smallest-size current-smallest-node size-array size-array-len)))))

(defthm natp-of-smallest-size-node-aux
  (implies (and (all-natp nodenums)
                (true-listp nodenums)
                (array1p 'size-array size-array)
                (natp size-array-len)
                (<= size-array-len
                    (alen1 'size-array size-array))
                (all-< nodenums size-array-len)
                (natp current-smallest-size)
                (natp current-smallest-node)
                )
           (natp (smallest-size-node-aux nodenums current-smallest-size current-smallest-node size-array size-array-len)))
  :hints (("Goal" :in-theory (e/d (smallest-size-node-aux) (natp)))))

(defthm <-of-smallest-size-node-aux
  (implies (and (all-< nodenums bound)
                (all-natp nodenums)
                (true-listp nodenums)
                (array1p 'size-array size-array)
                (natp size-array-len)
                (<= size-array-len
                    (alen1 'size-array size-array))
                (all-< nodenums size-array-len)
                (natp current-smallest-size)
                (< current-smallest-node bound)
                )
           (< (smallest-size-node-aux nodenums current-smallest-size current-smallest-node size-array size-array-len)
              bound))
  :hints (("Goal" :in-theory (e/d (smallest-size-node-aux) (natp)))))

;nodenums must be non-nil
;returns a nodenum
(defund smallest-size-node (nodenums size-array size-array-len)
  (declare (xargs :guard (and (all-natp nodenums)
                              (true-listp nodenums)
                              (consp nodenums)
                              (array1p 'size-array size-array)
                              (natp size-array-len)
                              (<= size-array-len
                                  (alen1 'size-array size-array))
                              (all-< nodenums size-array-len)
                              )
                  :guard-hints (("Goal" :in-theory (disable car-becomes-nth-of-0)))))
  (let* ((first-node (first nodenums))
         (first-size (nfix (aref1 'size-array size-array first-node)))) ;todo: drop the nfix?
    (smallest-size-node-aux (rest nodenums) first-size first-node size-array size-array-len)))

(defthm natp-of-smallest-size-node
  (implies (and (all-natp nodenums)
                (true-listp nodenums)
                (consp nodenums)
                (array1p 'size-array size-array)
                (natp size-array-len)
                (<= size-array-len
                    (alen1 'size-array size-array))
                (all-< nodenums size-array-len))
           (natp (smallest-size-node nodenums size-array size-array-len)))
  :hints (("Goal" :in-theory (e/d (smallest-size-node) (natp)))))

(defthm <-of-smallest-size-node
  (implies (and (all-< nodenums bound)
                (all-natp nodenums)
                (true-listp nodenums)
                (consp nodenums)
                (array1p 'size-array size-array)
                (natp size-array-len)
                (<= size-array-len
                    (alen1 'size-array size-array))
                (all-< nodenums size-array-len))
           (< (smallest-size-node nodenums size-array size-array-len)
              bound))
  :hints (("Goal" :in-theory (e/d (smallest-size-node) (natp)))))
