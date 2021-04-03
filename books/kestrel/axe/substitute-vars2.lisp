; New tools for substituting equated vars in DAGS
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

(include-book "substitute-vars")
(include-book "remove-duplicates-from-sorted-list")
(include-book "rebuild-nodes2") ;reduce
(include-book "../acl2-arrays/typed-acl2-arrays")
(local (include-book "kestrel/lists-light/remove-duplicates-equal" :dir :system))
(local (include-book "kestrel/lists-light/len" :dir :system))
(local (include-book "kestrel/lists-light/true-list-fix" :dir :system))
(local (include-book "kestrel/alists-light/strip-cars" :dir :system))
(local (include-book "merge-sort-less-than-rules"))
(local (include-book "kestrel/arithmetic-light/plus" :dir :system))

(local (in-theory (disable natp strip-cars dargp)))

;; a triple of the form (<nodenum-of-var> <equated-nodenum> <literal-nodenum>).
(defun subst-candidatep (cand)
  (declare (xargs :guard t))
  (and (nat-listp cand)
       (equal 3 (len cand))))

(defund subst-candidate-listp (cands)
  (declare (xargs :guard t))
  (if (atom cands)
      (null cands)
    (and (subst-candidatep (first cands))
         (subst-candidate-listp (rest cands)))))

;; TODO: What if we have the equality of two vars?  Should we consider both?

;; Returns a subst-candidate-listp.  Looks through the literals for ones that
;; equate vars with other nodes.
(defund subst-candidates (literal-nodenums dag-array dag-len acc)
  (declare (xargs :guard (and (pseudo-dag-arrayp 'dag-array dag-array dag-len)
                              (nat-listp literal-nodenums)
                              (all-< literal-nodenums dag-len))))
  (if (endp literal-nodenums)
      acc
    (b* ((literal-nodenum (first literal-nodenums))
         ((mv foundp
              & ;; var
              nodenum-of-var
              nodenum-or-quotep-to-put-in)
          ;; todo: Use a version that doesn't check supporters!:
          (check-for-var-subst-literal literal-nodenum dag-array dag-len)))
      (subst-candidates (rest literal-nodenums)
                        dag-array
                        dag-len
                        (if (and foundp
                                 (not (consp nodenum-or-quotep-to-put-in))) ;todo: allow putting in constants?
                            (cons (list nodenum-of-var nodenum-or-quotep-to-put-in literal-nodenum)
                                  acc)
                          acc)))))

(defthm subst-candidate-listp-of-subst-candidates
  (implies (and (pseudo-dag-arrayp 'dag-array dag-array dag-len)
                (nat-listp literal-nodenums)
                (all-< literal-nodenums dag-len)
                (subst-candidate-listp acc))
           (subst-candidate-listp (subst-candidates literal-nodenums dag-array dag-len acc)))
  :hints (("Goal" :in-theory (e/d (subst-candidates subst-candidate-listp)
                                  ()))))

(defthm subst-candidate-listp-of-cdr
  (implies (subst-candidate-listp subst-candidates)
           (subst-candidate-listp (cdr subst-candidates)))
  :hints (("Goal" :in-theory (enable subst-candidate-listp))))

(defthm natp-of-car-of-car-when-subst-candidate-listp
  (implies (and (subst-candidate-listp subst-candidates)
                (consp subst-candidates))
           (natp (car (car subst-candidates))))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :in-theory (enable subst-candidate-listp))))

;;So we can call strip-cars
(defthm subst-candidate-listp-forward-to-alistp
  (implies (subst-candidate-listp cands)
           (alistp cands))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable subst-candidate-listp alistp))))

(defthm rational-listp-of-strip-cars-when-subst-candidate-listp
  (implies (subst-candidate-listp subst-candidates)
           (rational-listp (strip-cars subst-candidates)))
  :hints (("Goal" :in-theory (enable subst-candidate-listp strip-cars))))

(defthm all-natp-of-strip-cars-when-subst-candidate-listp
  (implies (subst-candidate-listp subst-candidates)
           (all-natp (strip-cars subst-candidates)))
  :hints (("Goal" :in-theory (enable subst-candidate-listp strip-cars))))

;; Maps each node of a candidate var to the nodes of the candidates on which it
;; depends.  We can a candidate var X depends on another candidate var Y when
;; the expression equal to X (according to information from a literal) mentions
;; Y.
(def-typed-acl2-array2 candidate-deps-arrayp
  (and (nat-listp val)
       (no-duplicatesp-equal val)
       (sortedp-<= val)))

(defthm <=-of-maxelem-of-strip-cars-of-cdr
  (implies (consp (cdr x))
           (<= (maxelem (strip-cars (cdr x)))
               (maxelem (strip-cars x))))
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable maxelem strip-cars))))

(defund mark-all-candidates (subst-candidates candidate-deps-array)
  (declare (xargs :guard (and (subst-candidate-listp subst-candidates)
                              (candidate-deps-arrayp 'candidate-deps-array candidate-deps-array)
                              (or (endp subst-candidates)
                                  (< (maxelem (strip-cars subst-candidates))
                                     (alen1 'candidate-deps-array candidate-deps-array))))))
  (if (endp subst-candidates)
      candidate-deps-array
    (let* ((candidate (first subst-candidates))
           (var-nodenum (car candidate)))
      (mark-all-candidates (rest subst-candidates)
                           ;; Mark the nodenum of the var as depending on itself:
                           (aset1 'candidate-deps-array candidate-deps-array var-nodenum (list var-nodenum))))))

(defthm alen1-of-mark-all-candidates
  (implies (subst-candidate-listp subst-candidates)
           (equal (alen1 'candidate-deps-array (mark-all-candidates subst-candidates candidate-deps-array))
                  (alen1 'candidate-deps-array candidate-deps-array)))
  :hints (("Goal" :in-theory (enable mark-all-candidates))))

(defthm candidate-deps-arrayp-of-mark-all-candidates
  (implies (and (subst-candidate-listp subst-candidates)
                (candidate-deps-arrayp 'candidate-deps-array candidate-deps-array)
                (or (endp subst-candidates)
                    (< (maxelem (strip-cars subst-candidates))
                       (alen1 'candidate-deps-array candidate-deps-array))))
           (candidate-deps-arrayp 'candidate-deps-array (mark-all-candidates subst-candidates candidate-deps-array)))
  :hints (;("subgoal *1/4" :cases ((consp (CDR SUBST-CANDIDATES))))
          ("Goal" :do-not '(generalize eliminate-destructors) :in-theory (enable mark-all-candidates STRIP-CARS))))

;; Merges the deps for all the ARGS into ACC
(defun merge-values-for-args (args candidate-deps-array
                                   acc ; should be sorted
                                   )
  (declare (xargs :guard (and (candidate-deps-arrayp 'candidate-deps-array candidate-deps-array)
                              (all-dargp-less-than args (alen1 'candidate-deps-array candidate-deps-array))
                              (true-listp args)
                              (nat-listp acc))))
  (if (endp args)
      acc
    (let ((arg (first args)))
      (if (consp arg) ;check for quotep
          (merge-values-for-args (rest args) candidate-deps-array acc)
        (let ((candidates-arg-depends-on (aref1 'candidate-deps-array candidate-deps-array arg)))
          (merge-values-for-args (rest args)
                                 candidate-deps-array
                                 (merge-< candidates-arg-depends-on acc nil)))))))

(defthm nat-listp-of-merge-values-for-args
  (implies (and (candidate-deps-arrayp 'candidate-deps-array candidate-deps-array)
                (all-dargp-less-than args (alen1 'candidate-deps-array candidate-deps-array))
                (true-listp args)
                (nat-listp acc))
           (nat-listp (merge-values-for-args args candidate-deps-array acc))))

(defthm true-listp-of-merge-values-for-args
  (implies (and (candidate-deps-arrayp 'candidate-deps-array candidate-deps-array)
                (all-dargp-less-than args (alen1 'candidate-deps-array candidate-deps-array))
                (true-listp args)
                (nat-listp acc))
           (true-listp (merge-values-for-args args candidate-deps-array acc)))
  :rule-classes (:rewrite :type-prescription))

(defthm sortedp-<=-of-merge-values-for-args
  (implies (and (candidate-deps-arrayp 'candidate-deps-array candidate-deps-array)
                (all-dargp-less-than args (alen1 'candidate-deps-array candidate-deps-array))
                (true-listp args)
                (nat-listp acc)
                (sortedp-<= acc))
           (sortedp-<= (merge-values-for-args args candidate-deps-array acc))))

;; returns the candidate-deps-array
(defun populate-candidate-deps-array-aux (n max candidate-deps-array dag-array dag-array-len)
  (declare (xargs :guard (and (natp n)
                              (natp max)
                              (candidate-deps-arrayp 'candidate-deps-array candidate-deps-array)
                              (< max (alen1 'candidate-deps-array candidate-deps-array))
                              (pseudo-dag-arrayp 'dag-array dag-array dag-array-len)
                              (< max dag-array-len))
                  :measure (nfix (+ 1 (- max n)))
                  :hints (("Goal" :in-theory (enable natp)))))
  (if (or (not (mbt (natp n)))
          (not (mbt (natp max)))
          (< max n))
      candidate-deps-array
    (let* ((expr (aref1 'dag-array dag-array n)))
      (if (or (variablep expr) ;; variable nodes that are candidates are already marked
              (fquotep expr))
          (populate-candidate-deps-array-aux (+ 1 n) max candidate-deps-array dag-array dag-array-len)
        ;; it's a function call
        (let* ((candiates-node-depends-on (remove-duplicates-from-sorted-list (merge-values-for-args (dargs expr) candidate-deps-array nil) nil))
               (candidate-deps-array (aset1 'candidate-deps-array candidate-deps-array n candiates-node-depends-on)))
          (populate-candidate-deps-array-aux (+ 1 n) max candidate-deps-array dag-array dag-array-len))))))

;; returns the candidate-deps-array
(defun populate-candidate-deps-array (subst-candidates dag-array dag-array-len)
  (declare (xargs :guard (and (subst-candidate-listp subst-candidates)
                              (consp subst-candidates)
                              (pseudo-dag-arrayp 'dag-array dag-array dag-array-len)
                              (or (endp subst-candidates)
                                  (<= (maxelem (strip-cars subst-candidates))
                                      (+ -1 dag-array-len))))))
  (let* ((max-candidate-nodenum (maxelem (strip-cars subst-candidates))) ;todo: optimize
         (candidate-deps-array (make-empty-array 'candidate-deps-array (+ 1 max-candidate-nodenum)))
         (candidate-deps-array (mark-all-candidates subst-candidates candidate-deps-array)))
    (populate-candidate-deps-array-aux 0 max-candidate-nodenum candidate-deps-array dag-array dag-array-len)))
