; An array to track replacements of nodes
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

(include-book "kestrel/acl2-arrays/typed-acl2-arrays" :dir :system)
(include-book "kestrel/acl2-arrays/expandable-arrays" :dir :system)
(include-book "node-replacement-alist")
(include-book "dargp-less-than")
(local (include-book "kestrel/arithmetic-light/plus" :dir :system))
(local (include-book "kestrel/arithmetic-light/times" :dir :system))
(local (include-book "kestrel/arithmetic-light/min" :dir :system))
(local (include-book "kestrel/arithmetic-light/max" :dir :system))

;; We can build the node-replacement-array by calling make-into-array on the
;; node-replacement-alist produced by make-node-replacement-alist-and-add-to-dag-array.

;; See also node-replacement-array2.lisp.

(local (in-theory (disable ;symbolp-of-car-of-car-when-symbol-term-alistp
                   assoc-equal
                   ;default-car
                   ;;default-cdr
                   )))

;dup
(defthmd bounded-natp-alistp-redef
  (implies (true-listp l)
           (equal (bounded-natp-alistp l n)
                  (and (alistp l)
                       (all-natp (strip-cars l))
                       (all-< (strip-cars l) n))))
  :hints (("Goal" :in-theory (enable bounded-natp-alistp))))

;;add support in typed arrays machinery for make-into-array?

;move
(defthm natp-of-max-key-2
  (implies (and (all-natp (strip-cars alist))
                (natp max-so-far))
           (natp (max-key alist max-so-far)))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :in-theory (enable strip-cars max-key))))

(defthm all-dargp-less-than-of-strip-cdrs-of-cdr
  (implies (all-dargp-less-than (strip-cdrs alist) bound)
           (all-dargp-less-than (strip-cdrs (cdr alist)) bound)))

(defthm not-node-replacement-alistp
  (implies (and (not (integerp (cdr (assoc-equal index alist))))
                (cdr (assoc-equal index alist))
                (not (consp (cdr (assoc-equal index alist)))))
           (not (node-replacement-alistp alist bound)))
  :hints (("Goal" :in-theory (enable node-replacement-alistp
                                     assoc-equal))))

(defthm not-node-replacement-alistp-2
  (implies (and (<= BOUND (CDR (ASSOC-EQUAL INDEX ALIST)))
                (not (consp (CDR (ASSOC-EQUAL INDEX ALIST))))
                (ASSOC-EQUAL INDEX ALIST)
                ;(natp bound)
                )
           (not (node-replacement-alistp alist bound)))
  :hints (("Goal" :in-theory (enable node-replacement-alistp
                                     assoc-equal))))

(defthm not-node-replacement-alistp-3
  (implies (and (< (CDR (ASSOC-EQUAL INDEX ALIST)) 0)
;                (not (consp (CDR (ASSOC-EQUAL INDEX ALIST))))
                (ASSOC-EQUAL INDEX ALIST)
                ;(natp bound)
                )
           (not (node-replacement-alistp alist bound)))
  :hints (("Goal" :in-theory (enable node-replacement-alistp
                                     assoc-equal))))

(defthm integerp-of-cdr-of-assoc-equal-when-node-replacement-alistp
  (implies (and (node-replacement-alistp alist bound)
                (assoc-equal index alist))
           (equal (integerp (cdr (assoc-equal index alist)))
                  (not (consp (cdr (assoc-equal index alist))))))
  :hints (("Goal" :in-theory (enable node-replacement-alistp
                                     assoc-equal))))

(defthm not-cdddr-of-assoc-equal-when-node-replacement-alistp
  (implies (and (node-replacement-alistp alist bound)
                (assoc-equal index alist))
           (not (cdddr (assoc-equal index alist))))
  :hints (("Goal" :in-theory (enable node-replacement-alistp
                                     assoc-equal))))

(defthm consp-cddr-of-assoc-equal-when-node-replacement-alistp
  (implies (and (node-replacement-alistp alist bound)
                (assoc-equal index alist))
           (equal (consp (cddr (assoc-equal index alist)))
                  (consp (cdr (assoc-equal index alist)))))
  :hints (("Goal" :in-theory (enable node-replacement-alistp
                                     assoc-equal))))

(defthm equal-of-quote-and-cadr-of-assoc-equal-when-node-replacement-alistp
  (implies (and (node-replacement-alistp alist bound)
                (assoc-equal index alist))
           (equal (equal 'quote (cadr (assoc-equal index alist)))
                  (consp (cdr (assoc-equal index alist)))))
  :hints (("Goal" :in-theory (enable node-replacement-alistp
                                     assoc-equal))))

;; (defthm BOUNDED-INTEGER-ALISTP-of-+-of-1-and-max-key
;;   (implies (and ;(all-natp (strip-cars alist))
;;             (natp-alistp alist)
;;             (alistp alist))
;;            (BOUNDED-INTEGER-ALISTP ALIST (+ 1 (MAX-KEY ALIST 0))))
;;   :hints (("Goal" :in-theory (enable BOUNDED-INTEGER-ALISTP MAX-KEY))))

;disable?
(defthm natp-alistp-when-node-replacement-alistp
  (implies (node-replacement-alistp alist bound)
           (natp-alistp alist))
  :hints (("Goal" :in-theory (enable node-replacement-alistp natp-alistp))))

(defthm node-replacement-alistp-forward-to-true-listp
  (implies (node-replacement-alistp alist bound)
           (true-listp alist))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable node-replacement-alistp))))

(defthm <-of-max-key-bound
  (implies (and
            (< (max-key alist val2) 2147483646)
            (< val 2147483646)
            (< val2 2147483646)
            )
           (< (max-key alist val)
              2147483646))
  :hints (("Goal" :in-theory (enable max-key))))

(defthm <-of-max-key-when-all-<-of-STRIP-CARS
  (implies (and (ALL-< (STRIP-CARS alist) '2147483646)
                (all-natp (STRIP-CARS alist)) ;drop?
                )
           (< (MAX-KEY alist '0) '2147483646))
  :hints (("Goal" :in-theory (e/d (MAX-KEY max-when-<=-1) (max)))))

;;;
;;; end of library stuff
;;;

;;;
;;; node-replacement-arrayp
;;;

;; Each node maps to nil (no replacement), or to a replacement (a quotep or a nodenum).
;; TODO: Bake in the name of the array
(def-typed-acl2-array2 node-replacement-arrayp
  (or (null val)
      (myquotep val)
      (natp val)))

;;;
;;; bounded-node-replacement-arrayp
;;;

;; Each node maps to nil (no replacement), to a quotep, or to a nodenum less than the bound.
;;todo: make a variant that bakes in the name
(def-typed-acl2-array2 bounded-node-replacement-arrayp
  (or (null val)
      (myquotep val)
      (and (natp val)
           (< val bound)))
  :extra-vars (bound)
  :extra-guards ((natp bound)))

(defthmd bounded-natp-alistp-when-node-replacement-alistp ;todo: are these the same?
  (implies (node-replacement-alistp alist bound)
           (bounded-natp-alistp alist bound))
  :hints (("Goal" :in-theory (enable bounded-natp-alistp node-replacement-alistp))))

(defthm bounded-node-replacement-arrayp-aux-of-make-into-array
  (implies (and (node-replacement-alistp alist bound)
                (natp index)
                (< (max-key alist 0) 2147483646) ;or say bounded-natp-alistp
                (<= index (max-key alist 0))
                (symbolp array-name))
           (bounded-node-replacement-arrayp-aux array-name (make-into-array array-name alist) index bound))
  :hints (("Goal" :in-theory (enable bounded-node-replacement-arrayp-aux
                                     bounded-natp-alistp-when-node-replacement-alistp
                                     make-into-array ;todo
                                     aref1 ;todo
                                     make-into-array-with-len ;todo
                                     ))))

(defthm bounded-node-replacement-arrayp-of-make-into-array
  (implies (and (node-replacement-alistp node-replacement-alist bound)
                (natp bound)
                (<= bound 2147483646)
                ;(equal (alen1 ..) (+ 1 (max-key node-replacement-alist 0)))
                )
           (bounded-node-replacement-arrayp 'node-replacement-array
                                            (make-into-array 'node-replacement-array node-replacement-alist)
                                            bound))
  :hints (("Goal" :cases ((CONSP NODE-REPLACEMENT-ALIST))
           :in-theory (e/d (bounded-NODE-REPLACEMENT-ARRAYP
                                   bounded-NODE-REPLACEMENT-ARRAYP-aux
                                   ;;NODE-REPLACEMENT-ALISTP
                                   ;;MAKE-INTO-ARRAY
                                   BOUNDED-NATP-ALISTP-redef
                                   bounded-natp-alistp-when-node-replacement-alistp
                                   ) (alistp
                                   STRIP-CDRS
                                   STRIP-CARS)))))

(defthm bounded-node-replacement-arrayp-aux-monotone-2
  (implies (and (bounded-node-replacement-arrayp-aux array-name array index bound2)
                (<= bound2 bound)
                (natp bound)
                (natp bound2)
                ;(natp index)
                )
           (bounded-node-replacement-arrayp-aux array-name array index bound))
  :hints (("Goal" :in-theory (enable bounded-node-replacement-arrayp-aux))))

(defthm bounded-node-replacement-arrayp-monotone-2
  (implies (and (bounded-node-replacement-arrayp array-name array bound2)
                (<= bound2 bound)
                (natp bound)
                (natp bound2)
                )
           (bounded-node-replacement-arrayp array-name array bound))
  :hints (("Goal" :in-theory (enable bounded-node-replacement-arrayp))))

(defthm node-replacement-arrayp-aux-when-bounded-node-replacement-arrayp-aux
  (implies (bounded-node-replacement-arrayp-aux name array index bound)
           (node-replacement-arrayp-aux name array index))
  :hints (("Goal" :in-theory (enable bounded-node-replacement-arrayp-aux
                                     node-replacement-arrayp-aux))))

(defthm node-replacement-arrayp-when-bounded-node-replacement-arrayp
  (implies (bounded-node-replacement-arrayp name array bound)
           (node-replacement-arrayp name array))
  :hints (("Goal" :in-theory (enable bounded-node-replacement-arrayp
                                     node-replacement-arrayp))))
;;;
;;; lookup-in-node-replacement-array
;;;

;; Returns nil (no replacement for NODENUM) or a nodenum/quotep with which to replace NODENUM.
;; TODO: Make a version that gives back NODENUM if no replacement is made.  We
;; could even have the array map non-replaced nodes to themselves, to avoid
;; having to check whether the result is nil.
(defund lookup-in-node-replacement-array (nodenum node-replacement-array num-valid-nodes)
  (declare (xargs :guard (and (natp nodenum)
                              (natp num-valid-nodes)
                              (node-replacement-arrayp 'node-replacement-array node-replacement-array)
                              (<= num-valid-nodes (alen1 'node-replacement-array node-replacement-array)))))
  (if (<= num-valid-nodes nodenum) ;can't possibly be replaced, and looking it up would be illegal
      nil
    ;; either nil or a replacement (a nodenum or quotep):
    (aref1 'node-replacement-array node-replacement-array nodenum)))

(defthm dargp-of-lookup-in-node-replacement-array
  (implies (and (lookup-in-node-replacement-array nodenum node-replacement-array num-valid-nodes) ;; node is being replaced with something
                (natp nodenum)
                (natp num-valid-nodes)
                (<= num-valid-nodes (alen1 'node-replacement-array node-replacement-array))
                (node-replacement-arrayp 'node-replacement-array node-replacement-array))
           (dargp (lookup-in-node-replacement-array nodenum node-replacement-array num-valid-nodes)))
  :hints (("Goal" :use (:instance type-of-aref1-when-node-replacement-arrayp
                                  (array-name 'node-replacement-array)
                                  (array node-replacement-array)
                                  (index nodenum))
           :in-theory (e/d (lookup-in-node-replacement-array) (type-of-aref1-when-bounded-node-replacement-arrayp)))))

(defthm dargp-less-than-of-lookup-in-node-replacement-array
  (implies (and (lookup-in-node-replacement-array nodenum node-replacement-array num-valid-nodes) ;; node is being replaced with something
                (natp nodenum)
                (natp num-valid-nodes)
                (<= num-valid-nodes (alen1 'node-replacement-array node-replacement-array))
                (natp bound)
                (bounded-node-replacement-arrayp 'node-replacement-array node-replacement-array bound))
           (dargp-less-than (lookup-in-node-replacement-array nodenum node-replacement-array num-valid-nodes)
                            bound))
  :hints (("Goal" :use (:instance type-of-aref1-when-bounded-node-replacement-arrayp
                                  (array-name 'node-replacement-array)
                                  (array node-replacement-array)
                                  (index nodenum))
           :in-theory (e/d (lookup-in-node-replacement-array) (type-of-aref1-when-bounded-node-replacement-arrayp)))))

;;;
;;; add-node-replacement-entry-and-maybe-expand
;;;

;; Returns (mv node-replacement-array num-valid-nodes).
(defund add-node-replacement-entry-and-maybe-expand (nodenum replacement array-name array num-valid-nodes)
  (declare (xargs :guard (and (natp nodenum)
                              (< nodenum 2147483646)
                              (or (dargp replacement)
                                  (null replacement))
                              (node-replacement-arrayp array-name array)
                              (natp num-valid-nodes)
                              (<= num-valid-nodes (alen1 array-name array)))))
  (let ((array (maybe-expand-array array-name array nodenum)))
    (mv (aset1 array-name array nodenum replacement)
        (max (+ 1 nodenum)
             num-valid-nodes))))

(local (in-theory (disable assoc-keyword))) ;prevent inductions

;; Any index works, because either it's in range and we get a good value, or it's out of range and we get the default
(defthm node-replacement-arrayp-aux-when-node-replacement-arrayp-aux-of-len-minus-1
  (implies (and (array1p name array)
                (node-replacement-arrayp-aux name array (+ -1 (alen1 name array)))
                ;; (<= index 2147483645)
                (natp index)
                (equal nil (default name array)))
           (node-replacement-arrayp-aux name array index))
  :hints (("Goal" :cases ((<= (alen1 name array) index)))))

;todo: have the tool generate a theorem about maybe-exapand-array and don't enable that here
(defthm node-replacement-arrayp-of-mv-nth-0-of-add-node-replacement-entry-and-maybe-expand
  (implies (and (natp nodenum)
                (< nodenum 2147483646)
                (or (dargp replacement)
                    (null replacement))
                (node-replacement-arrayp array-name array)
                ;;(natp num-valid-nodes)
                ;;(<= num-valid-nodes (alen1 array-name array))
                )
           (node-replacement-arrayp array-name
                                    (mv-nth 0 (add-node-replacement-entry-and-maybe-expand nodenum replacement array-name array num-valid-nodes))))
  :hints (("Goal" :in-theory (e/d (maybe-expand-array
                                   add-node-replacement-entry-and-maybe-expand)
                                  (node-replacement-arrayp-aux-of-aset1
                                   alen1-of-expand-array)))))

(defthm bounded-node-replacement-arrayp-of-mv-nth-0-of-add-node-replacement-entry-and-maybe-expand
  (implies (and (natp nodenum)
                (< nodenum 2147483646)
                (or (dargp-less-than replacement bound)
                    (null replacement))
                (bounded-node-replacement-arrayp array-name array bound)
                ;;(natp num-valid-nodes)
                ;;(<= num-valid-nodes (alen1 array-name array))
                )
           (bounded-node-replacement-arrayp array-name
                                            (mv-nth 0 (add-node-replacement-entry-and-maybe-expand nodenum replacement array-name array num-valid-nodes))
                                            bound))
  :hints (("Goal" :cases ((consp replacement))
           :in-theory (e/d (add-node-replacement-entry-and-maybe-expand) (node-replacement-arrayp-aux-of-aset1 alen1-of-expand-array)))))

(defthm natp-of-mv-nth-1-of-add-node-replacement-entry-and-maybe-expand
  (implies (and (natp nodenum)
                (natp num-valid-nodes))
           (natp (mv-nth 1 (add-node-replacement-entry-and-maybe-expand nodenum replacement array-name array num-valid-nodes))))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :in-theory (e/d (maybe-expand-array
                                   add-node-replacement-entry-and-maybe-expand)
                                  (node-replacement-arrayp-aux-of-aset1
                                   alen1-of-expand-array)))))

;; The array doesn't get shorter.
(defthm bound-on-alen1-of-mv-nth-0-of-add-node-replacement-entry-and-maybe-expand
  (implies (and (natp nodenum)
                (< nodenum 2147483646)
                ;; (dargp replacement)
                (node-replacement-arrayp array-name array)
                ;;(natp num-valid-nodes)
                ;;(<= num-valid-nodes (alen1 array-name array))
                )
           (<= (alen1 array-name array)
               (alen1 array-name (mv-nth 0 (add-node-replacement-entry-and-maybe-expand nodenum replacement array-name array num-valid-nodes)))))
  :rule-classes (:rewrite :linear)
  :hints (("Goal" :in-theory (e/d (maybe-expand-array
                                   add-node-replacement-entry-and-maybe-expand)
                                  (node-replacement-arrayp-aux-of-aset1
                                   alen1-of-expand-array)))))

(defthm bound-on-alen1-of-mv-nth-0-of-add-node-replacement-entry-and-maybe-expand-gen
  (implies (and (<= x (alen1 array-name array))
                (integerp x)
                (natp nodenum)
                (< nodenum 2147483646)
                ;; (dargp replacement)
                (node-replacement-arrayp array-name array)
                ;;(natp num-valid-nodes)
                ;;(<= num-valid-nodes (alen1 array-name array))
                )
           (<= x (alen1 array-name (mv-nth 0 (add-node-replacement-entry-and-maybe-expand nodenum replacement array-name array num-valid-nodes)))))
  :hints (("Goal" :use (:instance bound-on-alen1-of-mv-nth-0-of-add-node-replacement-entry-and-maybe-expand)
           :in-theory (disable bound-on-alen1-of-mv-nth-0-of-add-node-replacement-entry-and-maybe-expand))))

(defthm bound-on-mv-nth-1-of-add-node-replacement-entry-and-maybe-expand
  (implies (and (natp nodenum)
                (< nodenum 2147483646)
                ;; (dargp replacement)
                (node-replacement-arrayp array-name array)
                (natp num-valid-nodes)
                (<= num-valid-nodes (alen1 array-name array)))
           (<= (mv-nth 1 (add-node-replacement-entry-and-maybe-expand nodenum replacement array-name array num-valid-nodes))
               (alen1 array-name (mv-nth 0 (add-node-replacement-entry-and-maybe-expand nodenum replacement array-name array num-valid-nodes)))))
  :rule-classes ((:linear :trigger-terms ((mv-nth 1 (add-node-replacement-entry-and-maybe-expand nodenum replacement array-name array num-valid-nodes)))))
  :hints (("Goal" :in-theory (e/d (maybe-expand-array
                                   add-node-replacement-entry-and-maybe-expand
                                   NODE-REPLACEMENT-ARRAYP)
                                  (node-replacement-arrayp-aux-of-aset1
                                   ;alen1-of-expand-array
                                   )))))

(defthm bound-on-mv-nth-1-of-add-node-replacement-entry-and-maybe-expand-gen
  (implies (and (<= x (mv-nth 1 (add-node-replacement-entry-and-maybe-expand nodenum replacement array-name array num-valid-nodes)))
                (natp nodenum)
                (< nodenum 2147483646)
                ;; (dargp replacement)
                (node-replacement-arrayp array-name array)
                (natp num-valid-nodes)
                (<= num-valid-nodes (alen1 array-name array)))
           (<= x (alen1 array-name (mv-nth 0 (add-node-replacement-entry-and-maybe-expand nodenum replacement array-name array num-valid-nodes)))))
  :hints (("Goal" :in-theory (e/d (maybe-expand-array
                                   add-node-replacement-entry-and-maybe-expand
                                   NODE-REPLACEMENT-ARRAYP)
                                  (node-replacement-arrayp-aux-of-aset1
                                   ;alen1-of-expand-array
                                   )))))

;; The num-valid-nodes does not decrease
(defthm bound2-on-mv-nth-1-of-add-node-replacement-entry-and-maybe-expand
  (implies (and (natp nodenum)
                (< nodenum 2147483646)
                ;; (dargp replacement)
                (node-replacement-arrayp array-name array)
                ;;(natp num-valid-nodes)
                ;;(<= num-valid-nodes (alen1 array-name array))
                )
           (<= num-valid-nodes
               (mv-nth 1 (add-node-replacement-entry-and-maybe-expand nodenum replacement array-name array num-valid-nodes))))
  :hints (("Goal" :in-theory (e/d (maybe-expand-array
                                   add-node-replacement-entry-and-maybe-expand)
                                  (node-replacement-arrayp-aux-of-aset1
                                   alen1-of-expand-array)))))

(defthm bound2-on-mv-nth-1-of-add-node-replacement-entry-and-maybe-expand-gen
  (implies (and (<= x num-valid-nodes)
                (natp nodenum)
                (< nodenum 2147483646)
                ;; (dargp replacement)
                (node-replacement-arrayp array-name array)
                ;;(natp num-valid-nodes)
                ;;(<= num-valid-nodes (alen1 array-name array))
                )
           (<= x (mv-nth 1 (add-node-replacement-entry-and-maybe-expand nodenum replacement array-name array num-valid-nodes))))
  :hints (("Goal" :use (:instance bound2-on-mv-nth-1-of-add-node-replacement-entry-and-maybe-expand)
           :in-theory (disable bound2-on-mv-nth-1-of-add-node-replacement-entry-and-maybe-expand))))
