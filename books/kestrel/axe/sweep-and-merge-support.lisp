; Support for sweeping and merging
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2024 Kestrel Institute
; Copyright (C) 2016-2020 Kestrel Technology, LLC
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/utilities/unify" :dir :system)
(include-book "kestrel/alists-light/lookup-eq" :dir :system)
(include-book "test-cases") ; for test-case-type-alistp
(include-book "kestrel/acl2-arrays/typed-acl2-arrays" :dir :system)
(include-book "kestrel/lists-light/add-to-end" :dir :system)
(include-book "kestrel/typed-lists-light/all-less" :dir :system)
(include-book "kestrel/typed-lists-light/nat-list-listp" :dir :system)
(include-book "merge-sort-less-than")
(include-book "find-probable-facts-common") ; for all-all-<
(local (include-book "kestrel/lists-light/len" :dir :system))
(local (include-book "kestrel/lists-light/cdr" :dir :system))
(local (include-book "kestrel/lists-light/rules2" :dir :system))
(local (include-book "kestrel/alists-light/alistp" :dir :system))
(local (include-book "kestrel/utilities/pseudo-termp" :dir :system))
(local (include-book "kestrel/typed-lists-light/pseudo-term-listp" :dir :system))
(local (include-book "kestrel/typed-lists-light/nat-listp" :dir :system))
(local (include-book "merge-sort-less-than-rules"))

(in-theory (disable mv-nth))

(local (in-theory (e/d (true-listp-when-nat-listp-rewrite)
                       ())))

;term must include at least one variable, so that returning nil can only mean failure
(defund unify-term-with-any (term patterns)
  (declare (xargs :guard (and (pseudo-termp term)
                              (pseudo-term-listp patterns))))
  (if (endp patterns)
      nil
    (let ((pattern (car patterns)))
      (mv-let (matchp alist)
              (unify-term term pattern)
              (if matchp
                  alist
                (unify-term-with-any term (cdr patterns)))))))

(defthm symbol-term-alistp-of-unify-term-with-any
  (implies (and (pseudo-termp term)
                (pseudo-term-listp patterns))
           (symbol-term-alistp (unify-term-with-any term patterns)))
  :hints (("Goal" :in-theory (enable unify-term-with-any))))

;returns the len (a natp) or nil.
(defund find-len-from-hyp (hyps item)
  (declare (xargs :guard (pseudo-term-listp hyps)
                  :guard-hints (("Goal" :in-theory (enable unify-term-with-any))) ; todo
                  ))
  (if (endp hyps)
      nil
    (let* ((hyp (car hyps))
           (alist (unify-term-with-any hyp '((equal (len x) y)
                                             (equal y (len x))))))
      (if (and alist
               (equal item (lookup-eq 'x alist))
               (quotep (lookup-eq 'y alist))
               (natp (unquote (lookup-eq 'y alist))))
          (unquote (lookup-eq 'y alist))
        (find-len-from-hyp (cdr hyps) item)))))

(defund strip-equal-t (term)
  (declare (xargs :guard t))
  (if (call-of 'equal term)
      (if (and (consp (cdr term))
               (consp (cddr term))
               (equal *t* (farg1 term)))
          (farg2 term)
        (if (and (consp (cdr term))
                 (consp (cddr term))
                 (equal *t* (farg2 term)))
            (farg1 term)
          term))
    term))

(local
  (defthm pseudo-termp-of-strip-equal-t
    (implies (pseudo-termp term)
             (pseudo-termp (strip-equal-t term)))
    :rule-classes (:rewrite :type-prescription)
    :hints (("Goal" :in-theory (enable strip-equal-t)))))

(defund extend-var-type-alist-with-hyp (hyp all-hyps var-type-alist)
  (declare (xargs :guard (and (pseudo-termp hyp)
                              (pseudo-term-listp all-hyps)
                              (test-case-type-alistp var-type-alist) ;strengthen?  not all constructs can appear
                              )))
  (let ((hyp (strip-equal-t hyp)))
    (if (and (call-of 'unsigned-byte-p hyp)
             (= 2 (len (fargs hyp)))
             (quotep (second hyp))
             (natp (unquote (second hyp))) ;should we require > 0 ?
             (symbolp (third hyp)))
        (acons-fast (third hyp) (make-bv-type (unquote (second hyp))) var-type-alist)
      ;; an array type comes in three pieces: all-unsigned-byte-p, len, and true-listp
      (let* ((alist (unify-term-with-any hyp '((all-unsigned-byte-p size var)
                                               ;(all-unsigned-byte-p size var)
                                               )))
             (size (lookup-eq 'size alist))
             (var (lookup-eq 'var alist)))
        (if (and alist
                 (quotep size)
                 (natp (unquote size))
                 (symbolp var)
                 (or (member-equal `(true-listp ,var) all-hyps)
                     (member-equal `(equal (true-listp ,var) 't) all-hyps))) ;would be better to always choose just one form?
            (let ((len (find-len-from-hyp all-hyps var)))
              (if len
                  (acons-fast var
                         (make-bv-array-type (unquote size) len) ;fixme what if the size is 0? ffffixme make sure we handle array widths right;  we round up to 1 if all elems are 0
                         var-type-alist)
                var-type-alist))
          var-type-alist)))))

(defthm test-case-type-alistp-of-extend-var-type-alist-with-hyp
  (implies (test-case-type-alistp var-type-alist)
           (test-case-type-alistp (extend-var-type-alist-with-hyp hyp all-hyps var-type-alist)))
  :hints (("Goal" :in-theory (enable extend-var-type-alist-with-hyp))))

;ffixme should we do this for nodes that are not variables?
(defund make-var-type-alist-from-hyps-aux (hyps all-hyps var-type-alist)
  (declare (xargs :guard (and (pseudo-term-listp hyps)
                              (pseudo-term-listp all-hyps)
                              (test-case-type-alistp var-type-alist) ; strengthen further, since some things don't occur?
                              )))
  (if (endp hyps)
      var-type-alist
    (make-var-type-alist-from-hyps-aux (rest hyps)
                                       all-hyps
                                       (extend-var-type-alist-with-hyp (first hyps)
                                                                       all-hyps
                                                                       var-type-alist))))

(defthm test-case-type-alistp-of-make-var-type-alist-from-hyps-aux
  (implies (test-case-type-alistp var-type-alist)
           (test-case-type-alistp (make-var-type-alist-from-hyps-aux hyps all-hyps var-type-alist)))
  :hints (("Goal" :in-theory (enable make-var-type-alist-from-hyps-aux))))

;; use this more?!
;ffixme what about more complicated things, like bounds on (or low bits of) the length of an array?
(defun make-var-type-alist-from-hyps (hyps)
  (declare (xargs :guard (pseudo-term-listp hyps)))
  (make-var-type-alist-from-hyps-aux hyps hyps nil))

(defthm test-case-type-alistp-of-make-var-type-alist-from-hyps
  (implies (test-case-type-alistp var-type-alist)
           (test-case-type-alistp (make-var-type-alist-from-hyps hyps)))
  :hints (("Goal" :in-theory (enable make-var-type-alist-from-hyps))))

;;
;; Tags to determine the order of nodes to attack
;;

;;i make these explicit constants to make sure I don't accidentally mistype one:

(defconst *probable-constant* :probable-constant) ;either nil (to indicate not probably a constant) or the quoted constant value
(defconst *smaller-nodes-that-might-be-equal* :smaller-nodes-that-might-be-equal)
(defconst *larger-nodes-that-might-be-equal* :larger-nodes-that-might-be-equal)

(defconst *sweep-array-tags* (list *probable-constant* *smaller-nodes-that-might-be-equal* *larger-nodes-that-might-be-equal*))

(defun sweep-info-tag-and-valuep (tag val)
  (declare (xargs :guard t))
  (if (eq *probable-constant* tag)
      (or (null val)
          (myquotep val))
    (and (or (eq *smaller-nodes-that-might-be-equal* tag)
             (eq *larger-nodes-that-might-be-equal* tag))
         (nat-listp val))))

(defund sweep-infop (info)
  (declare (xargs :guard t))
  (if (atom info)
      (null info)
    (let* ((entry (first info)))
      (and (consp entry)
           (let ((tag (car entry))
                 (val (cdr entry)))
             (and (sweep-info-tag-and-valuep tag val)
                  (sweep-infop (rest info))))))))

;(def-typed-acl2-array2 sweep-arrayp sweep-infop) ; todo: this should work
(def-typed-acl2-array2 sweep-arrayp (sweep-infop val)) ; todo: reduce output

(local
 (defthm alistp-when-sweep-infop
   (implies (sweep-infop info)
            (alistp info))
   :hints (("Goal" :in-theory (enable sweep-infop)))))

(local
 (defthm nat-listp-of-lookup-equal-when-sweep-infop
   (implies (sweep-infop sweep-info)
            (nat-listp (lookup-equal :smaller-nodes-that-might-be-equal sweep-info)))
   :hints (("Goal" :in-theory (enable sweep-infop lookup-equal)))))

(local
 (defthm nat-listp-of-lookup-equal-when-sweep-infop-2
   (implies (sweep-infop sweep-info)
            (nat-listp (lookup-equal :larger-nodes-that-might-be-equal sweep-info)))
   :hints (("Goal" :in-theory (enable sweep-infop lookup-equal)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;sweep-array associates each nodenums with a little alist from tags to their values
(defund get-node-tag (nodenum tag sweep-array)
  (declare (xargs :guard (and (natp nodenum)
                              (symbolp tag)
                              (sweep-arrayp 'sweep-array sweep-array)
                              (< nodenum (alen1 'sweep-array sweep-array)))
                  :split-types t)
           (type (integer 0 *) nodenum)
           (type symbol tag))
  (let ((node-tags (aref1 'sweep-array sweep-array nodenum)))
    (lookup-eq tag node-tags)))

(local
 (defthm true-listp-of-get-node-tag-of-smaller-nodes-that-might-be-equal
   (implies (and (sweep-arrayp 'sweep-array sweep-array)
                 (natp index)
                 (< index (alen1 'sweep-array sweep-array)))
            (true-listp (get-node-tag index :smaller-nodes-that-might-be-equal sweep-array)))
   :rule-classes (:rewrite :type-prescription)
   :hints (("Goal" :use (:instance type-of-aref1-when-sweep-arrayp
                                   (array-name 'sweep-array)
                                   (array sweep-array)
                                   )
            :in-theory (e/d (get-node-tag sweep-infop)
                            (type-of-aref1-when-sweep-arrayp))))))

(local
 (defthm nat-listp-of-get-node-tag-of-smaller-nodes-that-might-be-equal
   (implies (and (sweep-arrayp 'sweep-array sweep-array)
                 (natp index)
                 (< index (alen1 'sweep-array sweep-array)))
            (nat-listp (get-node-tag index :smaller-nodes-that-might-be-equal sweep-array)))
   :hints (("Goal" :use (:instance type-of-aref1-when-sweep-arrayp
                                   (array-name 'sweep-array)
                                   (array sweep-array)
                                   )
            :in-theory (e/d (get-node-tag sweep-infop)
                            (type-of-aref1-when-sweep-arrayp))))))

(local
 (defthm nat-listp-of-get-node-tag-of-larger-nodes-that-might-be-equal
   (implies (and (sweep-arrayp 'sweep-array sweep-array)
                 (natp index)
                 (< index (alen1 'sweep-array sweep-array)))
            (nat-listp (get-node-tag index :larger-nodes-that-might-be-equal sweep-array)))
   :hints (("Goal" :use (:instance type-of-aref1-when-sweep-arrayp
                                   (array-name 'sweep-array)
                                   (array sweep-array)
                                   )
            :in-theory (e/d (get-node-tag sweep-infop)
                            (type-of-aref1-when-sweep-arrayp))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund set-node-tag (nodenum tag val sweep-array)
  (declare (xargs :guard (and (natp nodenum)
                              (symbolp tag)
                              (sweep-info-tag-and-valuep tag val)
                              (sweep-arrayp 'sweep-array sweep-array)
                              (< nodenum (alen1 'sweep-array sweep-array)))
                  :split-types t)
           (type (integer 0 *) nodenum)
           (type symbol tag))
  (let* ((node-tags (aref1 'sweep-array sweep-array nodenum))
         (new-node-tags (acons-fast tag val node-tags)))
    (aset1-safe 'sweep-array sweep-array nodenum new-node-tags)))

(local
 (defthm sweep-arrayp-of-set-node-tag
   (implies (and (natp nodenum)
                 (sweep-info-tag-and-valuep tag val)
                 (sweep-arrayp 'sweep-array sweep-array)
                 (< nodenum (alen1 'sweep-array sweep-array))
                 )
            (sweep-arrayp 'sweep-array (set-node-tag nodenum tag val sweep-array)))
   :hints (("Goal" :in-theory (enable set-node-tag sweep-infop)))))

(local
 (defthm alen1-of-set-node-tag
   (implies (and (natp nodenum)
                 (sweep-info-tag-and-valuep tag val)
                 (sweep-arrayp 'sweep-array sweep-array)
                 (< nodenum (alen1 'sweep-array sweep-array))
                 )
            (equal (alen1 'sweep-array (set-node-tag nodenum tag val sweep-array))
                   (alen1 'sweep-array sweep-array)))
   :hints (("Goal" :in-theory (enable set-node-tag sweep-infop)))))

(local
  (defthm get-node-tag-of-set-node-tag-diff
    (implies (and (not (equal tag1 tag2))
                  (array1p 'sweep-array sweep-array)
                  (natp nodenum2)
                  (< nodenum2 (alen1 'sweep-array sweep-array))
                  (natp nodenum)
                  (< nodenum (alen1 'sweep-array sweep-array)))
             (equal (get-node-tag nodenum tag1 (set-node-tag nodenum2 tag2 val sweep-array))
                    (get-node-tag nodenum tag1 sweep-array)))
    :hints (("Goal" :in-theory (enable get-node-tag set-node-tag)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;returns sweep-array
;moves nodes one at a time from node-set to smaller-nodes-from-this-set
(defund tag-probably-equal-node-set (node-set ;should be sorted
                                     smaller-nodes-from-this-set ;should be kept sorted (ffixme maybe that's too expensive, in which case choose the minimum one when this is used? but then removing the node may be slow?  maybe that is more rare?)
                                     sweep-array)
  (declare (xargs :guard (and (sweep-arrayp 'sweep-array sweep-array)
                              (nat-listp smaller-nodes-from-this-set)
                              (nat-listp node-set)
                              (all-< node-set (alen1 'sweep-array sweep-array)))
                  :guard-hints (("Goal" :in-theory (enable)))))
  (if (endp node-set)
      sweep-array
    (let* ((node (car node-set))
           ;;fixme could handle the tagging stuff better with separate arrays? but that would mean more consing?
           (sweep-array (set-node-tag node *larger-nodes-that-might-be-equal* (cdr node-set) sweep-array)) ;don't bother to record for the smallest node in each set?
           (sweep-array (set-node-tag node *smaller-nodes-that-might-be-equal* smaller-nodes-from-this-set sweep-array)))
      (tag-probably-equal-node-set (cdr node-set)
                                   (add-to-end node smaller-nodes-from-this-set) ;preserves sorting
                                   sweep-array))))

(defthm sweep-arrayp-of-tag-probably-equal-node-set
  (implies (and (sweep-arrayp 'sweep-array sweep-array)
                (nat-listp smaller-nodes-from-this-set)
                (nat-listp node-set)
                (all-< node-set (alen1 'sweep-array sweep-array)))
           (sweep-arrayp 'sweep-array (tag-probably-equal-node-set node-set smaller-nodes-from-this-set sweep-array)))
  :hints (("Goal" :in-theory (enable tag-probably-equal-node-set))))

(defthm alen1-arrayp-of-tag-probably-equal-node-set
  (implies (and (sweep-arrayp 'sweep-array sweep-array)
                (nat-listp smaller-nodes-from-this-set)
                (nat-listp node-set)
                (all-< node-set (alen1 'sweep-array sweep-array)))
           (equal (alen1 'sweep-array (tag-probably-equal-node-set node-set smaller-nodes-from-this-set sweep-array))
                  (alen1 'sweep-array sweep-array)))
  :hints (("Goal" :in-theory (enable tag-probably-equal-node-set))))

;returns sweep-array
;Tag the elements of probably-equal node sets but exclude sets that are probably constant (TODO: try not excluding them)
(defun tag-probably-equal-node-sets (node-sets sweep-array probably-constant-node-alist)
  (declare (xargs :guard (and (nat-list-listp node-sets)
                              (sweep-arrayp 'sweep-array sweep-array)
                              (all-all-< node-sets (alen1 'sweep-array sweep-array))
                              (alistp probably-constant-node-alist))
                  :guard-hints (("Goal" :in-theory (enable TRUE-LISTP-WHEN-NAT-LISTP-REWRITE)))))
  (if (endp node-sets)
      sweep-array
    (let* ((node-set (first node-sets))
           (node (car node-set))
           (probably-constantp (assoc node probably-constant-node-alist))
           ;;(len-of-set (len node-set))
           ;;do not tag large constant sets:
           (tag-setp (or (not probably-constantp)
                         ;;(< len-of-set 20) ;mon feb  1 06:45:52 2010 (seemed to lead us to merge nodes of different types - both had the value "nil") (perhaps a syntactic check would help distinguish between a boolean nil and a list nil)
                         )))
      (tag-probably-equal-node-sets (rest node-sets)
                                    (if tag-setp
                                        (tag-probably-equal-node-set (merge-sort-< node-set) nil sweep-array)
                                      sweep-array)
                                    probably-constant-node-alist))))


;; Tags all the nodes that are probably constants.
;; Returns sweep-array.
(defund tag-probably-constant-nodes (probably-constant-node-alist sweep-array)
  (declare (xargs :guard (and (alistp probably-constant-node-alist)
                              (nat-listp (strip-cars probably-constant-node-alist))
                              (sweep-arrayp 'sweep-array sweep-array)
                              (all-< (strip-cars probably-constant-node-alist) (alen1 'sweep-array sweep-array)))))
  (if (endp probably-constant-node-alist)
      sweep-array
    (let* ((entry (car probably-constant-node-alist))
           (nodenum (car entry))
           (value (cdr entry))
           ;;fixme, can we handle this for every type of constant (like lists and other non-bv stuff)?
           (sweep-array (set-node-tag nodenum *probable-constant* (enquote value) sweep-array)))
      (tag-probably-constant-nodes (cdr probably-constant-node-alist) sweep-array))))

(defun remove-node-from-smaller-nodes-that-might-be-equal (nodenum nodenum-to-remove sweep-array)
  (declare (xargs :guard (and (natp nodenum)
                              (natp nodenum-to-remove)
                              (sweep-arrayp 'sweep-array sweep-array)
                              (< nodenum (alen1 'sweep-array sweep-array)))))
  (let* ((smaller-nodes-that-might-be-equal (get-node-tag nodenum *smaller-nodes-that-might-be-equal* sweep-array))
         (smaller-nodes-that-might-be-equal (remove1 nodenum-to-remove smaller-nodes-that-might-be-equal))
         (sweep-array (set-node-tag nodenum *smaller-nodes-that-might-be-equal* smaller-nodes-that-might-be-equal sweep-array)))
    sweep-array))

(defun remove-node-from-smaller-nodes-that-might-be-equal-list (nodenums nodenum-to-remove sweep-array)
  (declare (xargs :guard (and (nat-listp nodenums)
                              (natp nodenum-to-remove)
                              (sweep-arrayp 'sweep-array sweep-array)
                              (all-< nodenums (alen1 'sweep-array sweep-array)))))
  (if (endp nodenums)
      sweep-array
    (remove-node-from-smaller-nodes-that-might-be-equal-list
     (cdr nodenums)
     nodenum-to-remove
     (remove-node-from-smaller-nodes-that-might-be-equal (car nodenums) nodenum-to-remove sweep-array))))

;; todo: guard (but need the notion of a bounded-sweep-array)
(defun update-tags-for-proved-constant-node (nodenum sweep-array)
  ;; (declare (xargs :guard (and (natp nodenum)
  ;;                             (sweep-arrayp 'sweep-array sweep-array)
  ;;                             (< nodenum (alen1 'sweep-array sweep-array)))))
  (let* ((sweep-array (set-node-tag nodenum *probable-constant* nil sweep-array)) ;don't try to prove the node is constant (we just proved it)
         ;;don't try to prove some other node is equal to this one:
         (larger-nodes-that-might-be-equal (get-node-tag nodenum *larger-nodes-that-might-be-equal* sweep-array))
         (sweep-array (remove-node-from-smaller-nodes-that-might-be-equal-list larger-nodes-that-might-be-equal nodenum sweep-array)))
    sweep-array))

;we failed to prove the node is constant, but we might be able to prove it equal to some other node we think is the same constant..
(defun update-tags-for-failed-constant-node (nodenum sweep-array)
  (declare (xargs :guard (and (natp nodenum)
                              (sweep-arrayp 'sweep-array sweep-array)
                              (< nodenum (alen1 'sweep-array sweep-array)))))
  (let* ((sweep-array (set-node-tag nodenum *probable-constant* nil sweep-array))) ;don't try to prove that it is the constant
    ;;we leave the node among the smaller-nodes-that-might-be-equal for larger nodes in its set
    sweep-array))

;we proved that nodenum equals some smaller node (and we changed refs to it to point to that smaller node)
;(we know *probable-constant* wasn't set or we would have tried to prove the node constant)
(defun update-tags-for-proved-equal-node (nodenum sweep-array)
  ;; (declare (xargs :guard (and (natp nodenum)
  ;;                             (sweep-arrayp 'sweep-array sweep-array)
  ;;                             (< nodenum (alen1 'sweep-array sweep-array)))
  ;;                 :verify-guards nil ; todo (but need the notion of a bounded-sweep-array)
  ;;                 ))
  (let* ((sweep-array (set-node-tag nodenum *smaller-nodes-that-might-be-equal* nil sweep-array)) ;don't try to prove it equal to anything else
         ;;don't try to prove some other node is equal to this one (we've essentially removed this one from the dag):
         (larger-nodes-that-might-be-equal (get-node-tag nodenum *larger-nodes-that-might-be-equal* sweep-array))
         (sweep-array (remove-node-from-smaller-nodes-that-might-be-equal-list larger-nodes-that-might-be-equal nodenum sweep-array)))
    sweep-array))

;we failed to prove that nodenum is equal to smaller-nodenum-we-tried-to-prove-it-equal-to
;(we know *probable-constant* wasn't set or we would have tried to prove the node constant)
(defun update-tags-for-failed-equal-node (nodenum smaller-nodenum-we-tried-to-prove-it-equal-to sweep-array)
    (declare (xargs :guard (and (natp nodenum)
                                (natp smaller-nodenum-we-tried-to-prove-it-equal-to)
                                (sweep-arrayp 'sweep-array sweep-array)
                                (< nodenum (alen1 'sweep-array sweep-array)))))
  ;;nodenum may still be provably equal to other nodes on the list (if any)
  (let* ((sweep-array (remove-node-from-smaller-nodes-that-might-be-equal nodenum smaller-nodenum-we-tried-to-prove-it-equal-to sweep-array)))
    sweep-array))

;based on the function print-each-list-on-one-line
(defund print-non-constant-probably-equal-sets (sets sweep-array)
  (declare (xargs :guard (and (nat-list-listp sets)
                              (not (member-equal nil sets))
                              (sweep-arrayp 'sweep-array sweep-array)
                              (all-all-< sets (alen1 'sweep-array sweep-array)))))
  (if (atom sets)
      nil
    (let* ((set (first sets))
           (node (first set)))
      (progn$ (if (get-node-tag node *probable-constant* sweep-array) ;pass in array name?
                  nil ;don't print sets where the nodes are probably-constant (or we could print the constant and then the set!)
                (prog2$ (print-list-on-one-line (first sets))
                        (cw "~%")))
              (print-non-constant-probably-equal-sets (rest sets) ;sweep-array-name
                                                      sweep-array)))))


;; TODO: Is this really right, if a set has more than 2 nodes and some of the attempted merges fail?
(defund count-merges-in-probably-equal-node-sets (sets acc)
  (declare (xargs :guard (and (true-list-listp sets)
                              (natp acc))))
  (if (endp sets)
      acc
    (let ((set (first sets)))
      (if (not (consp set))
          (er hard? 'count-merges-in-probably-equal-node-sets "Empty set found.")
        (count-merges-in-probably-equal-node-sets (rest sets)
                                                  (+ -1 ; a set of 2 contributes 1 merge, and so on
                                                     (len set)
                                                     acc))))))

;;go from the bottom up, looking for the next node to handle (is there guaranteed to always be one? i think so.)
;we handle the smallest numbered node that is either 1) an (unhandled) probable constant or 2) the larger of two (unhandled) probably-equal nodes in the same set
;returns (mv nodenum probably-constantp other-val) where other-val is the quoted constant or the smaller nodenum that nodenum is probably equal to
;indicates failure (should never happen) by returning nil for nodenum (and other return vals are irrelevant in that case)
(defund find-a-node-to-replace (nodenum sweep-array len)
  (declare (xargs :guard (and (natp nodenum)
                              (natp len)
                              (sweep-arrayp 'sweep-array sweep-array)
                              (<= nodenum len)
                              (<= len (alen1 'sweep-array sweep-array)) ; usually equal??
                              )
                  :measure (+ 1 (nfix (- len nodenum)))
                  :hints (("Goal" :in-theory (enable natp)))))
  (if (or (not (mbt (and (natp nodenum)
                         (natp len))))
          (>= nodenum len))
      (mv nil nil nil) ; nothing left to try
    (let ((probable-constant (get-node-tag nodenum *probable-constant* sweep-array)))
      ;; if it's probably-constant, we try that first (if that fails, this function will be called again):
      (if probable-constant
          (mv nodenum t probable-constant)
        ;; Not a probable constant. See if it's probably equal to some smaller node (not handling the pair until we reach the larger node allows constant nodes or other probably equal pairs that intrude between members of some probably-equal pair P to be handled before P, which is, i think, the best policy)
        (let ((smaller-nodes-that-might-be-equal (get-node-tag nodenum *smaller-nodes-that-might-be-equal* sweep-array)))
          (if smaller-nodes-that-might-be-equal
              (mv nodenum nil (first smaller-nodes-that-might-be-equal)) ;fixme if the proof for this smaller-node-that-might-be-equal fails but there are others, we'll redo the search and find this same node again (slow?!)
            ;; Nothing to try for this node, so keep looking:
            (find-a-node-to-replace (+ 1 nodenum) sweep-array len)))))))
