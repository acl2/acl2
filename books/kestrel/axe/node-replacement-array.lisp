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
(include-book "kestrel/utilities/forms" :dir :system)
(include-book "node-replacement-alist")
(include-book "dargp-less-than")
(include-book "merge-term-into-dag-array-basic")
(local (include-book "kestrel/arithmetic-light/plus" :dir :system))
(local (include-book "kestrel/arithmetic-light/times" :dir :system))
(local (include-book "kestrel/arithmetic-light/min" :dir :system))
(local (include-book "kestrel/arithmetic-light/max" :dir :system))

;; We can build the node-replacement-array by calling make-into-array on the
;; node-replacement-alist produced by make-node-replacement-alist-and-add-to-dag-array.

;; TODO: Consider chains of replacement, e.g., if the array indicates to
;; replace B with C, and we add a replacement entry to replace A with B, should
;; we actually add an entry to replace A with C?  That may make it impossible
;; to later unassume the replacement of B, unless we've already unassumed the
;; replacement of A...  We could instead address this by a repeated lookup.

;; See also node-replacement-array2.lisp.

(local (in-theory (disable ;symbolp-of-car-of-car-when-symbol-term-alistp
                   assoc-equal
                   ;default-car
                   ;;default-cdr
                   myquotep
                   natp
                   )))

;dup
(defthmd bounded-natp-alistp-redef
  (implies (true-listp l)
           (equal (bounded-natp-alistp l n)
                  (and (alistp l)
                       (all-natp (strip-cars l))
                       (all-< (strip-cars l) n))))
  :hints (("Goal" :in-theory (enable bounded-natp-alistp
                                     ;;natp
                                     all-natp
                                     all-<
                                     strip-cars
                                     alistp
                                     ))))

;;add support in typed arrays machinery for make-into-array?

;move
(defthm natp-of-max-key-2
  (implies (and (all-natp (strip-cars alist))
                (natp max-so-far))
           (natp (max-key alist max-so-far)))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :in-theory (enable strip-cars max-key))))

(defthm bounded-darg-listp-of-strip-cdrs-of-cdr
  (implies (bounded-darg-listp (strip-cdrs alist) bound)
           (bounded-darg-listp (strip-cdrs (cdr alist)) bound)))

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
                                     assoc-equal
                                     myquotep))))

(defthm consp-cddr-of-assoc-equal-when-node-replacement-alistp
  (implies (and (node-replacement-alistp alist bound)
                (assoc-equal index alist))
           (equal (consp (cddr (assoc-equal index alist)))
                  (consp (cdr (assoc-equal index alist)))))
  :hints (("Goal" :in-theory (enable node-replacement-alistp
                                     assoc-equal
                                     myquotep))))

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

;; Use a defined constant to avoid typos:
(defconst *non-nil* :non-nil)

;; To be left enabled?
(defun node-replacement-valp (val)
  (declare (xargs :guard t))
  (or (null val)
      (dargp val)
      (eq val *non-nil*)))

;; Each node maps to nil (no replacement), or to a replacement (a quotep or a nodenum), or to the special symbol :non-nil.
;; TODO: Bake in the name of the array
(def-typed-acl2-array2 node-replacement-arrayp (node-replacement-valp val))

(defthm type-of-aref1-when-node-replacement-arrayp-alt
  (implies (and (node-replacement-arrayp array-name array)
                (aref1 array-name array index)
                (not (consp (aref1 array-name array index)))
                (not (eq *non-nil* (aref1 array-name array index)))
                (< index (alen1 array-name array))
                (natp index))
           (natp (aref1 array-name array index)))
  :hints (("Goal" :use (:instance type-of-aref1-when-node-replacement-arrayp)
           :in-theory (disable type-of-aref1-when-node-replacement-arrayp))))

(defthm consp-of-cdr-of-aref1-when-node-replacement-arrayp
  (implies (and (node-replacement-arrayp array-name array)
                (< index (alen1 array-name array))
                (natp index))
           (equal (consp (cdr (aref1 array-name array index)))
                  (consp (aref1 array-name array index))))
  :hints (("Goal" :use (:instance type-of-aref1-when-node-replacement-arrayp)
           :in-theory (e/d (myquotep) (type-of-aref1-when-node-replacement-arrayp)))))

(defthm not-cddr-of-aref1-when-node-replacement-arrayp
  (implies (and (node-replacement-arrayp array-name array)
                (< index (alen1 array-name array))
                (natp index))
           (not (cdr (cdr (aref1 array-name array index)))))
  :hints (("Goal" :use (:instance type-of-aref1-when-node-replacement-arrayp)
           :in-theory (e/d (myquotep) (type-of-aref1-when-node-replacement-arrayp)))))

(defthm equal-of-quote-and-car-of-aref1-when-node-replacement-arrayp
  (implies (and (node-replacement-arrayp array-name array)
                (< index (alen1 array-name array))
                (natp index))
           (equal (equal 'quote (car (aref1 array-name array index)))
                  (consp (aref1 array-name array index))))
  :hints (("Goal" :use (:instance type-of-aref1-when-node-replacement-arrayp)
           :in-theory (e/d (myquotep) (type-of-aref1-when-node-replacement-arrayp)))))

;;;
;;; bounded-node-replacement-arrayp
;;;

(defun bounded-node-replacement-valp (val bound)
  (declare (xargs :guard (natp bound)))
  (or (null val)
      (eq val *non-nil*)
      (dargp-less-than val bound)))

(defthm bounded-node-replacement-valp-of-nil
  (bounded-node-replacement-valp nil dag-len)
  :hints (("Goal" :in-theory (enable bounded-node-replacement-valp))))

;; Each node maps to nil (no replacement), to a quotep, or to a nodenum less than the bound, or to the special symbol :non-nil.
;;todo: make a variant that bakes in the name
(def-typed-acl2-array2 bounded-node-replacement-arrayp
  (bounded-node-replacement-valp val bound)
  :extra-vars (bound)
  :extra-guards ((natp bound)))

(DEFTHM TYPE-OF-AREF1-WHEN-BOUNDED-NODE-REPLACEMENT-ARRAYP-alt
  (IMPLIES (AND (BOUNDED-NODE-REPLACEMENT-ARRAYP ARRAY-NAME ARRAY BOUND)
                (< INDEX (ALEN1 ARRAY-NAME ARRAY))
                (NATP INDEX)
                (AREF1 ARRAY-NAME ARRAY INDEX)
                (not (eq *non-nil* (AREF1 ARRAY-NAME ARRAY INDEX))))
           (DARGP-LESS-THAN (AREF1 ARRAY-NAME ARRAY INDEX) BOUND))
  :hints (("Goal" :use (:instance TYPE-OF-AREF1-WHEN-BOUNDED-NODE-REPLACEMENT-ARRAYP)
           :in-theory (disable TYPE-OF-AREF1-WHEN-BOUNDED-NODE-REPLACEMENT-ARRAYP))))

(defthmd bounded-natp-alistp-when-node-replacement-alistp
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
                                     DARGP-LESS-THAN-OF-CDR-OF-ASSOC-EQUAL-WHEN-NODE-REPLACEMENT-ALISTP
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
;;; known-true-in-node-replacement-arrayp
;;;

;; Checks whether NODENUM is known to be non-nil.
(defund known-true-in-node-replacement-arrayp (nodenum node-replacement-array node-replacement-count)
  (declare (xargs :guard (and (natp nodenum)
                              (natp node-replacement-count)
                              (node-replacement-arrayp 'node-replacement-array node-replacement-array)
                              (<= node-replacement-count (alen1 'node-replacement-array node-replacement-array)))))
  (if (<= node-replacement-count nodenum) ; looking it up might be illegal
      nil
    ;; either nil or a replacement (a nodenum or quotep) or :non-nil:
    (let ((res (aref1 'node-replacement-array node-replacement-array nodenum)))
      (or (eq res *non-nil*)
          (and (consp res)   ; test for quotep
               (unquote res) ;constant must be non-nil
               )))))

;;;
;;; apply-node-replacement-array
;;;

;; Returns NODENUM (no replacement for NODENUM) or a nodenum/quotep with which to replace NODENUM.
;; TODO: Consider having the array map non-replaced nodes to themselves, to avoid
;; having to check whether the result is nil.
(defund apply-node-replacement-array (nodenum node-replacement-array node-replacement-count)
  (declare (xargs :guard (and (natp nodenum)
                              (natp node-replacement-count)
                              (node-replacement-arrayp 'node-replacement-array node-replacement-array)
                              (<= node-replacement-count (alen1 'node-replacement-array node-replacement-array)))))
  (if (<= node-replacement-count nodenum) ;can't possibly be replaced, and looking it up might be illegal
      nodenum
    ;; either nil or a replacement (a nodenum or quotep) or :non-nil:
    (let ((res (aref1 'node-replacement-array node-replacement-array nodenum)))
      (if (or (not res)
              (eq res *non-nil*))
          nodenum ; can't replace
        res))))

(defthm dargp-of-apply-node-replacement-array
  (implies (and ;(apply-node-replacement-array nodenum node-replacement-array node-replacement-count) ;; node is being replaced with something
                (natp nodenum)
                (natp node-replacement-count)
                (<= node-replacement-count (alen1 'node-replacement-array node-replacement-array))
                (node-replacement-arrayp 'node-replacement-array node-replacement-array))
           (dargp (apply-node-replacement-array nodenum node-replacement-array node-replacement-count)))
  :hints (("Goal" :use (:instance type-of-aref1-when-node-replacement-arrayp
                                  (array-name 'node-replacement-array)
                                  (array node-replacement-array)
                                  (index nodenum))
           :in-theory (e/d (apply-node-replacement-array) (type-of-aref1-when-bounded-node-replacement-arrayp)))))

(defthm dargp-less-than-of-apply-node-replacement-array
  (implies (and (natp nodenum)
                (< nodenum bound) ; in case no replacement happens
                (natp node-replacement-count)
                (<= node-replacement-count (alen1 'node-replacement-array node-replacement-array))
                (natp bound)
                (bounded-node-replacement-arrayp 'node-replacement-array node-replacement-array bound))
           (dargp-less-than (apply-node-replacement-array nodenum node-replacement-array node-replacement-count)
                            bound))
  :hints (("Goal" :use (:instance type-of-aref1-when-bounded-node-replacement-arrayp
                                  (array-name 'node-replacement-array)
                                  (array node-replacement-array)
                                  (index nodenum))
           :in-theory (e/d (apply-node-replacement-array)
                           (type-of-aref1-when-bounded-node-replacement-arrayp)))))

;;;
;;; apply-node-replacement-array-bool
;;;

;; Returns NODENUM (no replacement for NODENUM) or a nodenum/quotep with which to replace NODENUM.
;; The result is equivalent to NODENUM under iff (but not necessarily equal), given the information in the array.
(defund apply-node-replacement-array-bool (nodenum node-replacement-array node-replacement-count)
  (declare (xargs :guard (and (natp nodenum)
                              (natp node-replacement-count)
                              (node-replacement-arrayp 'node-replacement-array node-replacement-array)
                              (<= node-replacement-count (alen1 'node-replacement-array node-replacement-array)))))
  (if (<= node-replacement-count nodenum) ;can't possibly be replaced, and looking it up might be illegal
      nodenum
    ;; either nil or a replacement (a nodenum or quotep) or *non-nil*:
    (let ((res (aref1 'node-replacement-array node-replacement-array nodenum)))
      (if (not res)
          nodenum ; no change
        (if (eq res *non-nil*)
            *t*           ; equivalent to anything else non-nil under IFF
          (if (consp res) ; check for quotep
              (if (equal res *nil*)
                  *nil*
                *t* ; any non-nil constant is equivalent to t
                )
            res ; a replacement nodenum (this should be rare, but perhaps we just simplified something and replaced it with nodenum using the node-replament-array, and are now replacing again)
            ))))))

(defthm dargp-of-apply-node-replacement-array-bool
  (implies (and ;(apply-node-replacement-array-bool nodenum node-replacement-array node-replacement-count) ;; node is being replaced with something
                (natp nodenum)
                (natp node-replacement-count)
                (<= node-replacement-count (alen1 'node-replacement-array node-replacement-array))
                (node-replacement-arrayp 'node-replacement-array node-replacement-array))
           (dargp (apply-node-replacement-array-bool nodenum node-replacement-array node-replacement-count)))
  :hints (("Goal" :use (:instance type-of-aref1-when-node-replacement-arrayp
                                  (array-name 'node-replacement-array)
                                  (array node-replacement-array)
                                  (index nodenum))
           :in-theory (e/d (apply-node-replacement-array-bool) (type-of-aref1-when-bounded-node-replacement-arrayp)))))

;; Use consp as the normal form
(defthm natp-of-apply-node-replacement-array-bool
  (implies (and (natp nodenum)
                (natp node-replacement-count)
                (<= node-replacement-count (alen1 'node-replacement-array node-replacement-array))
                (node-replacement-arrayp 'node-replacement-array node-replacement-array))
           (equal (natp (apply-node-replacement-array-bool nodenum node-replacement-array node-replacement-count))
                  (not (consp (apply-node-replacement-array-bool nodenum node-replacement-array node-replacement-count)))))
  :hints (("Goal" :use (:instance type-of-aref1-when-node-replacement-arrayp
                                  (array-name 'node-replacement-array)
                                  (array node-replacement-array)
                                  (index nodenum))
           :in-theory (e/d (apply-node-replacement-array-bool) (type-of-aref1-when-bounded-node-replacement-arrayp)))))

(defthm dargp-less-than-of-apply-node-replacement-array-bool
  (implies (and (natp nodenum)
                (< nodenum bound) ; in case no replacement happens
                (natp node-replacement-count)
                (<= node-replacement-count (alen1 'node-replacement-array node-replacement-array))
                (natp bound)
                (bounded-node-replacement-arrayp 'node-replacement-array node-replacement-array bound))
           (dargp-less-than (apply-node-replacement-array-bool nodenum node-replacement-array node-replacement-count)
                            bound))
  :hints (("Goal" :use (:instance type-of-aref1-when-bounded-node-replacement-arrayp
                                  (array-name 'node-replacement-array)
                                  (array node-replacement-array)
                                  (index nodenum))
           :in-theory (e/d (apply-node-replacement-array-bool)
                           (type-of-aref1-when-bounded-node-replacement-arrayp)))))

(defthm <-of-apply-node-replacement-array-bool
  (implies (and (not (consp (apply-node-replacement-array-bool nodenum node-replacement-array node-replacement-count)))
                (natp nodenum)
                (< nodenum bound) ; in case no replacement happens
                (natp node-replacement-count)
                (<= node-replacement-count (alen1 'node-replacement-array node-replacement-array))
                (natp bound)
                (bounded-node-replacement-arrayp 'node-replacement-array node-replacement-array bound))
           (< (apply-node-replacement-array-bool nodenum node-replacement-array node-replacement-count)
              bound))
  :hints (("Goal" :use (:instance type-of-aref1-when-bounded-node-replacement-arrayp
                                  (array-name 'node-replacement-array)
                                  (array node-replacement-array)
                                  (index nodenum))
           :in-theory (e/d (apply-node-replacement-array-bool)
                           (type-of-aref1-when-bounded-node-replacement-arrayp)))))

;;;
;;; add-node-replacement-entry-and-maybe-expand
;;;

;; Augments the node-replacement-array with the fact that NODENUM is equal to REPLACEMENT.
;; Returns (mv node-replacement-array node-replacement-count).
(defund add-node-replacement-entry-and-maybe-expand (nodenum replacement node-replacement-array node-replacement-count)
  (declare (xargs :guard (and (natp nodenum)
                              (< nodenum 2147483646)
                              (node-replacement-valp replacement)
                              (node-replacement-arrayp 'node-replacement-array node-replacement-array)
                              (natp node-replacement-count)
                              (<= node-replacement-count (alen1 'node-replacement-array node-replacement-array)))))
  (let ((node-replacement-array (maybe-expand-array 'node-replacement-array node-replacement-array nodenum)))
    (mv (aset1 'node-replacement-array node-replacement-array nodenum replacement)
        (max (+ 1 nodenum)
             node-replacement-count))))

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
                (node-replacement-valp replacement)
                (node-replacement-arrayp 'node-replacement-array array)
                ;;(natp node-replacement-count)
                ;;(<= node-replacement-count (alen1 'node-replacement-array array))
                )
           (node-replacement-arrayp 'node-replacement-array
                                    (mv-nth 0 (add-node-replacement-entry-and-maybe-expand nodenum replacement array node-replacement-count))))
  :hints (("Goal" :in-theory (e/d (maybe-expand-array
                                   add-node-replacement-entry-and-maybe-expand)
                                  (node-replacement-arrayp-aux-of-aset1
                                   alen1-of-expand-array)))))

(defthm bounded-node-replacement-arrayp-of-mv-nth-0-of-add-node-replacement-entry-and-maybe-expand
  (implies (and (natp nodenum)
                (< nodenum 2147483646)
                (bounded-node-replacement-valp replacement bound)
                (bounded-node-replacement-arrayp 'node-replacement-array array bound)
                ;;(natp node-replacement-count)
                ;;(<= node-replacement-count (alen1 'node-replacement-array array))
                )
           (bounded-node-replacement-arrayp 'node-replacement-array
                                            (mv-nth 0 (add-node-replacement-entry-and-maybe-expand nodenum replacement array node-replacement-count))
                                            bound))
  :hints (("Goal" :cases ((consp replacement))
           :in-theory (e/d (add-node-replacement-entry-and-maybe-expand) (node-replacement-arrayp-aux-of-aset1 alen1-of-expand-array)))))

(defthm natp-of-mv-nth-1-of-add-node-replacement-entry-and-maybe-expand
  (implies (and (natp nodenum)
                (natp node-replacement-count))
           (natp (mv-nth 1 (add-node-replacement-entry-and-maybe-expand nodenum replacement array node-replacement-count))))
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
                (node-replacement-arrayp 'node-replacement-array array)
                ;;(natp node-replacement-count)
                ;;(<= node-replacement-count (alen1 'node-replacement-array array))
                )
           (<= (alen1 'node-replacement-array array)
               (alen1 'node-replacement-array (mv-nth 0 (add-node-replacement-entry-and-maybe-expand nodenum replacement array node-replacement-count)))))
  :rule-classes (:rewrite :linear)
  :hints (("Goal" :in-theory (e/d (maybe-expand-array
                                   add-node-replacement-entry-and-maybe-expand)
                                  (node-replacement-arrayp-aux-of-aset1
                                   alen1-of-expand-array)))))

(defthm bound-on-alen1-of-mv-nth-0-of-add-node-replacement-entry-and-maybe-expand-gen
  (implies (and (<= x (alen1 'node-replacement-array array))
                (integerp x)
                (natp nodenum)
                (< nodenum 2147483646)
                ;; (dargp replacement)
                (node-replacement-arrayp 'node-replacement-array array)
                ;;(natp node-replacement-count)
                ;;(<= node-replacement-count (alen1 'node-replacement-array array))
                )
           (<= x (alen1 'node-replacement-array (mv-nth 0 (add-node-replacement-entry-and-maybe-expand nodenum replacement array node-replacement-count)))))
  :hints (("Goal" :use (:instance bound-on-alen1-of-mv-nth-0-of-add-node-replacement-entry-and-maybe-expand)
           :in-theory (disable bound-on-alen1-of-mv-nth-0-of-add-node-replacement-entry-and-maybe-expand))))

(defthm bound-on-mv-nth-1-of-add-node-replacement-entry-and-maybe-expand
  (implies (and (natp nodenum)
                (< nodenum 2147483646)
                ;; (dargp replacement)
                (node-replacement-arrayp 'node-replacement-array array)
                (natp node-replacement-count)
                (<= node-replacement-count (alen1 'node-replacement-array array)))
           (<= (mv-nth 1 (add-node-replacement-entry-and-maybe-expand nodenum replacement array node-replacement-count))
               (alen1 'node-replacement-array (mv-nth 0 (add-node-replacement-entry-and-maybe-expand nodenum replacement array node-replacement-count)))))
  :rule-classes ((:linear :trigger-terms ((mv-nth 1 (add-node-replacement-entry-and-maybe-expand nodenum replacement array node-replacement-count)))))
  :hints (("Goal" :in-theory (e/d (maybe-expand-array
                                   add-node-replacement-entry-and-maybe-expand
                                   NODE-REPLACEMENT-ARRAYP)
                                  (node-replacement-arrayp-aux-of-aset1
                                   ;alen1-of-expand-array
                                   )))))

(defthm bound-on-mv-nth-1-of-add-node-replacement-entry-and-maybe-expand-gen
  (implies (and (<= x (mv-nth 1 (add-node-replacement-entry-and-maybe-expand nodenum replacement array node-replacement-count)))
                (natp nodenum)
                (< nodenum 2147483646)
                ;; (dargp replacement)
                (node-replacement-arrayp 'node-replacement-array array)
                (natp node-replacement-count)
                (<= node-replacement-count (alen1 'node-replacement-array array)))
           (<= x (alen1 'node-replacement-array (mv-nth 0 (add-node-replacement-entry-and-maybe-expand nodenum replacement array node-replacement-count)))))
  :hints (("Goal" :in-theory (e/d (maybe-expand-array
                                   add-node-replacement-entry-and-maybe-expand
                                   NODE-REPLACEMENT-ARRAYP)
                                  (node-replacement-arrayp-aux-of-aset1
                                   ;alen1-of-expand-array
                                   )))))

;; The node-replacement-count does not decrease
(defthm bound2-on-mv-nth-1-of-add-node-replacement-entry-and-maybe-expand
  (implies (and (natp nodenum)
                (< nodenum 2147483646)
                ;; (dargp replacement)
                (node-replacement-arrayp 'node-replacement-array array)
                ;;(natp node-replacement-count)
                ;;(<= node-replacement-count (alen1 'node-replacement-array array))
                )
           (<= node-replacement-count
               (mv-nth 1 (add-node-replacement-entry-and-maybe-expand nodenum replacement array node-replacement-count))))
  :hints (("Goal" :in-theory (e/d (maybe-expand-array
                                   add-node-replacement-entry-and-maybe-expand)
                                  (node-replacement-arrayp-aux-of-aset1
                                   alen1-of-expand-array)))))

(defthm bound2-on-mv-nth-1-of-add-node-replacement-entry-and-maybe-expand-gen
  (implies (and (<= x node-replacement-count)
                (natp nodenum)
                (< nodenum 2147483646)
                ;; (dargp replacement)
                (node-replacement-arrayp 'node-replacement-array array)
                ;;(natp node-replacement-count)
                ;;(<= node-replacement-count (alen1 'node-replacement-array array))
                )
           (<= x (mv-nth 1 (add-node-replacement-entry-and-maybe-expand nodenum replacement array node-replacement-count))))
  :hints (("Goal" :use (:instance bound2-on-mv-nth-1-of-add-node-replacement-entry-and-maybe-expand)
           :in-theory (disable bound2-on-mv-nth-1-of-add-node-replacement-entry-and-maybe-expand))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; An alist mapping terms to their replacements, either other terms or the
;; special symbol *non-nil*.
(defund term-replacement-alistp (alist)
  (declare (xargs :guard t))
  (if (atom alist)
      (null alist)
    (let ((pair (first alist)))
      (and (consp pair)
           (pseudo-termp (car pair))
           (or (pseudo-termp (cdr pair))
               (eq *non-nil* (cdr pair)))
           (term-replacement-alistp (rest alist))))))

(defthm term-replacement-alistp-forward-to-alistp
  (implies (term-replacement-alistp alist)
           (alistp alist))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable term-replacement-alistp alistp))))

(defthm term-replacement-alistp-of-cdr
  (implies (term-replacement-alistp alist)
           (term-replacement-alistp (cdr alist)))
  :hints (("Goal" :in-theory (enable term-replacement-alistp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Turns ASSUMPTION into an alist mapping terms to replacement terms or *non-nil*.
;; Extends ACC.
;; TODO: What else should we handle here (ifs that represent conjunctions, negated disjunctions?
(defun term-replacement-alist-for-assumption (assumption known-booleans acc)
  (declare (xargs :guard (and (pseudo-termp assumption)
                              (symbol-listp known-booleans)
                              (term-replacement-alistp acc))
                  :guard-hints (("Goal" :in-theory (enable term-replacement-alistp)))
                  :verify-guards nil ; done below
                  :measure (acl2-count assumption)))
  (if (variablep assumption)
      ;; The best we can do is map the var to *non-nil*, since it may not be t:
      (acons assumption *non-nil* acc)
    (let ((fn (ffn-symb assumption)))
      (case fn
        (quote ;can this happen?
         (prog2$ (cw "NOTE: term-replacement-alist-for-assumption is skipping constant assumption ~x0.~%" assumption)
                 acc))
        (equal ;fixme consider more sophisticated tests to decide whether to turn around the assumption?
         (let ((x (farg1 assumption))
               (y (farg2 assumption)))
           (if (and (quotep x) (quotep y))
               (prog2$ (cw "NOTE: term-replacement-alist-for-assumption is skipping unusual assumption ~x0.~%" assumption)
                       acc)
             (if (quotep x)
                 (acons y x acc) ; replace y with x since x is a constant
               (if (quotep y)
                   (acons x y acc) ; replace x with y since y is a constant
                 ;; We're being conservative here and not replacing either term with the other in general (TODO: consider when one is a subterm of the other)
                 ;; We'll add the fact that the equality oriented either way it true
                 ;; TODO: Consider not being conservative, since these are assumptions from the user, which can be taken to be directed equalities
                 (acons assumption *t*
                        (acons `(equal ,y ,x) *t*
                               acc)))))))
        (not ;; (not x) becomes the pair (x . 'nil) ;; the case above for 'equal above handles the (equal x nil) phrasing for nots.
         ;; TODO: If x is a call of EQUAL, add pairs for both orientations?  or handle that later?
         (acons (farg1 assumption) *nil* acc))
        (booland ;; TODO: Other ways of stripping conjuncts!
         (and (consp (cdr (fargs assumption))) ;for termination
              ;; (booland x y) causes x and y to be processed recursively
              (term-replacement-alist-for-assumption (farg2 assumption)
                                                     known-booleans
                                                     (term-replacement-alist-for-assumption (farg1 assumption)
                                                                                            known-booleans
                                                                                            acc))))
        (t ;; (<predicate> x ...) becomes the pair ((<predicate> x ...) . 't)
         (if (member-eq fn known-booleans) ;we test for not above so dont need to exclude it here?
             (acons assumption *t* acc)
           ;; It's not a known boolean, so the best we can do is mark it as non-nil:
           (acons assumption *non-nil* acc)))))))

(defthm term-replacement-alistp-of-term-replacement-alist-for-assumption
  (implies (and (pseudo-termp assumption)
                (symbol-listp known-booleans)
                (term-replacement-alistp acc))
           (term-replacement-alistp (term-replacement-alist-for-assumption assumption known-booleans acc)))
  :hints (("Goal" :in-theory (e/d (term-replacement-alist-for-assumption
                                   term-replacement-alistp)
                                  (quotep)))))

(verify-guards term-replacement-alist-for-assumption :hints (("Goal" :in-theory (enable term-replacement-alistp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund term-replacement-alist-for-assumptions (assumptions known-booleans acc)
  (declare (xargs :guard (and (pseudo-term-listp assumptions)
                              (symbol-listp known-booleans)
                              (term-replacement-alistp acc))))
  (if (endp assumptions)
      acc
    (term-replacement-alist-for-assumptions (rest assumptions)
                                            known-booleans
                                            (term-replacement-alist-for-assumption (first assumptions) known-booleans acc))))

(defthm term-replacement-alistp-of-term-replacement-alist-for-assumptions
  (implies (and (pseudo-term-listp assumptions)
                (symbol-listp known-booleans)
                (term-replacement-alistp acc))
           (term-replacement-alistp (term-replacement-alist-for-assumptions assumptions known-booleans acc)))
  :hints (("Goal" :in-theory (enable term-replacement-alist-for-assumptions
                                     term-replacement-alistp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Returns (mv erp node-replacement-array node-replacement-count dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist).
(defund update-node-replacement-array-and-extend-dag-for-alist (alist
                                                                dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                                                node-replacement-array node-replacement-count)
  (declare (xargs :guard (and (term-replacement-alistp alist)
                              ;; the cdrs of the alist are either terms or the special symbol *non-nil*.
                              (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                              (node-replacement-arrayp 'node-replacement-array node-replacement-array)
                              (natp node-replacement-count)
                              (<= node-replacement-count (alen1 'node-replacement-array node-replacement-array)))
                  :guard-hints (("Goal" :expand (term-replacement-alistp alist)
                                 :in-theory (enable (:d term-replacement-alistp))))))
  (if (endp alist)
      (mv (erp-nil) node-replacement-array node-replacement-count dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
    (b* ((pair (first alist))
         (term (car pair))
         (replacement (cdr pair))
         ;; Merge in the term being replaced:
         ((mv erp term-nodenum-or-quotep dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
          (merge-term-into-dag-array-basic term
                                           nil ;var-replacement-alist
                                           dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist 'dag-array 'dag-parent-array
                                           nil ;interpreted-function-alist
                                           ))
         ((when erp) (mv erp node-replacement-array node-replacement-count dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist))
         ((when (consp term-nodenum-or-quotep)) ; check for quotep -- todo: prove this can't happen
          (er hard? 'update-node-replacement-array-and-extend-dag-for-alist "Assumption with a quotep LHS: ~x0." `(equal ,term ,replacement))
          (mv :unexpected-quote node-replacement-array node-replacement-count dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist))
         ;; Add the replacement if it is not *non-nil*:
         ((mv erp replacement-item dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
          (if (eq replacement *non-nil*)
              ;; no term to add:
              (mv (erp-nil) *non-nil* dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
            (merge-term-into-dag-array-basic replacement
                                             nil ;var-replacement-alist
                                             dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist 'dag-array 'dag-parent-array
                                             nil ;interpreted-function-alist
                                             )))
         ((when erp) (mv erp node-replacement-array node-replacement-count dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist))
         ((mv node-replacement-array node-replacement-count)
          (add-node-replacement-entry-and-maybe-expand term-nodenum-or-quotep replacement-item node-replacement-array node-replacement-count)))
      (update-node-replacement-array-and-extend-dag-for-alist (rest alist)
                                                              dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                                              node-replacement-array node-replacement-count))))

(defthm update-node-replacement-array-and-extend-dag-for-alist-return-type
  (implies (and (term-replacement-alistp alist)
                ;; the cdrs of the alist are either terms or the special symbol *non-nil*.
                (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                ;(node-replacement-arrayp 'node-replacement-array node-replacement-array)
                (bounded-node-replacement-arrayp 'node-replacement-array node-replacement-array dag-len)
                (natp node-replacement-count)
                (<= node-replacement-count (alen1 'node-replacement-array node-replacement-array)))
           (mv-let (erp new-node-replacement-array node-replacement-count dag-array new-dag-len dag-parent-array dag-constant-alist dag-variable-alist)
             (update-node-replacement-array-and-extend-dag-for-alist alist
                                                                        dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                                                        node-replacement-array node-replacement-count)
             (implies (not erp)
                      (and (natp node-replacement-count)
                           (node-replacement-arrayp 'node-replacement-array new-node-replacement-array) ; convenient but follows from the below
                           (bounded-node-replacement-arrayp 'node-replacement-array new-node-replacement-array new-dag-len)
                           (<= dag-len new-dag-len)
                           (<= node-replacement-count (alen1 'node-replacement-array new-node-replacement-array))
                           (<= (alen1 'node-replacement-array node-replacement-array) (alen1 'node-replacement-array new-node-replacement-array))
                           (wf-dagp 'dag-array dag-array new-dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)))))
  :hints (("Goal" :induct t
           :expand (term-replacement-alistp alist)
           :in-theory (e/d (update-node-replacement-array-and-extend-dag-for-alist) (pseudo-termp)))))

;drop?
;; (defthm update-node-replacement-array-and-extend-dag-for-alist-return-type-corollary
;;   (implies (and (term-replacement-alistp alist)
;;                 ;; the cdrs of the alist are either terms or the special symbol *non-nil*.
;;                 (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
;;                 (node-replacement-arrayp 'node-replacement-array node-replacement-array)
;;                 (natp node-replacement-count)
;;                 (<= node-replacement-count (alen1 'node-replacement-array node-replacement-array)))
;;            (mv-let (erp node-replacement-array node-replacement-count dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
;;              (update-node-replacement-array-and-extend-dag-for-alist alist
;;                                                                         dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
;;                                                                         node-replacement-array node-replacement-count)
;;              (declare (ignore DAG-ARRAY DAG-LEN DAG-PARENT-ARRAY DAG-CONSTANT-ALIST DAG-VARIABLE-ALIST))
;;              (implies (not erp)
;;                       (<= node-replacement-count (alen1 'node-replacement-array node-replacement-array)))))
;;   :rule-classes :linear
;;   :hints (("Goal" :use update-node-replacement-array-and-extend-dag-for-alist-return-type
;;            :in-theory (disable update-node-replacement-array-and-extend-dag-for-alist-return-type))))

(defthm update-node-replacement-array-and-extend-dag-for-alist-return-type-corollary-2
  (implies (and (term-replacement-alistp alist)
                ;; the cdrs of the alist are either terms or the special symbol *non-nil*.
                (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                (node-replacement-arrayp 'node-replacement-array node-replacement-array)
                (bounded-node-replacement-arrayp 'node-replacement-array node-replacement-array dag-len)
                (natp node-replacement-count)
                (<= node-replacement-count (alen1 'node-replacement-array node-replacement-array)))
           (mv-let (erp node-replacement-array new-node-replacement-count dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
             (update-node-replacement-array-and-extend-dag-for-alist alist
                                                                        dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                                                        node-replacement-array node-replacement-count)
             (declare (ignore DAG-ARRAY DAG-LEN DAG-PARENT-ARRAY DAG-CONSTANT-ALIST DAG-VARIABLE-ALIST
                              new-node-replacement-count))
             (implies (and (not erp))
                      (<= node-replacement-count (alen1 'node-replacement-array node-replacement-array)))))
  :hints (("Goal" :use update-node-replacement-array-and-extend-dag-for-alist-return-type
           :in-theory (disable update-node-replacement-array-and-extend-dag-for-alist-return-type))))

;; ;; Returns (mv erp node-replacement-array node-replacement-count dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist).
;; (defun update-node-replacement-array-and-extend-dag-for-assumption (assumption
;;                                                                        dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
;;                                                                        node-replacement-array node-replacement-count
;;                                                                        known-booleans)
;;   (declare (xargs :guard (and (pseudo-termp assumption)
;;                               (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
;;                               (node-replacement-arrayp 'node-replacement-array array)
;;                               (natp node-replacement-count)
;;                               (<= node-replacement-count (alen1 'node-replacement-array array))
;;                               (symbol-listp known-booleans))))

;; )




  ;; (if (variablep assumption) ;; Could add an assumption from (equal nil x) to nil...
  ;;     (b* (;; Add the var to the DAG:
  ;;          ((mv erp nodenum dag-array dag-len dag-parent-array dag-variable-alist)
  ;;           (add-variable-to-dag-array assumption dag-array dag-len dag-parent-array dag-variable-alist))
  ;;          ((when erp) (mv erp node-replacement-array node-replacement-count dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist))
  ;;          ;; Add the fact that the var's node in non-nil:
  ;;          ((mv node-replacement-array node-replacement-count)
  ;;           (add-node-replacement-entry-and-maybe-expand nodenum *non-nil* node-replacement-array node-replacement-count)))
  ;;       (mv (erp-nil) node-replacement-array node-replacement-count dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist))
  ;;   (let ((fn (ffn-symb assumption)))
  ;;     (if (eq 'quote fn)  ;can this happen?
  ;;       (prog2$ (cw "NOTE: Skipping constant assumption ~x0.~%" assumption)
  ;;               (mv (erp-nil) node-replacement-array node-replacement-count dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist))
  ;;       (mv-let (term replacement)
  ;;         (case fn
  ;;           (not (mv (farg1 assumption) *nil*)) ; (not <nodenum>) means assuming <nodenum> is nil
  ;;           ..)
  ;;         .. now merge the rhs and lhs

  ;;         split out term-equalt

  ;;       (not
  ;;        ;; Add the argument of NOT to the DAG:
  ;;        ((mv erp nodenum dag-array dag-len dag-parent-array dag-variable-alist)
  ;;         (add-variable-to-dag-array assumption dag-array dag-len dag-parent-array dag-variable-alist))
  ;;        ((when erp) (mv erp node-replacement-array node-replacement-count dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist))


  ;;       (if (eq 'equal fn) ;fixme consider more sophisticated tests to decide whether to turn around the assumption?
  ;;           (if (quotep (farg1 assumption))
  ;;               ;; (equal x y) becomes the pair (y . x) because x is a quotep
  ;;               (cons (cons (farg2 assumption) (farg1 assumption))
  ;;                     acc)
  ;;             ;; (equal x y) becomes the pair (x . y)
  ;;             (cons (cons (farg1 assumption) (farg2 assumption))
  ;;                   acc))
  ;;         (if (eq 'not fn)
  ;;             ;; (not x) becomes the pair (x . 'nil) ;;the case above for 'equal above handles the (equal x nil) phrasing for nots..
  ;;             (cons (cons (farg1 assumption) ''nil)
  ;;                   acc)
  ;;           (if (and (eq 'booland fn) ;; TODO: Other ways of stripping conjuncts?
  ;;                    (= 2 (len (fargs assumption)))) ;for termination
  ;;               ;; (booland x y) causes x and y to be processed recursively
  ;;               (add-equality-pairs-for-assumption (farg2 assumption)
  ;;                                                  known-booleans
  ;;                                                  (add-equality-pairs-for-assumption (farg1 assumption)
  ;;                                                                                     known-booleans
  ;;                                                                                     acc))
  ;;             ;; (<predicate> x ...) becomes the pair ((<predicate> x ...) . 't)
  ;;             (if (member-eq fn known-booleans) ;we test for not above so dont need to exclude it here?
  ;;                 (cons (cons assumption ''t)
  ;;                       acc)
  ;;               ;; TODO: Consider putting back this printing once we stop using member-equal for assumptions
  ;;               ;; about initialized classes:
  ;;               (prog2$ nil ;(cw "NOTE: add-equality-pairs-for-assumption is skipping a ~x0 assumption.~%" fn) ;todo: print the assumption if small?
  ;;                       acc))))))))


;; ;; Returns (mv erp node-replacement-array node-replacement-count dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist).
;; (defun make-node-replacement-array-and-extend-dag-aux (assumptions
;;                                                           dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
;;                                                           node-replacement-array node-replacement-count)
;;   (declare (xargs :guard (and (pseudo-term-listp assumptions)
;;                               (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
;;                               (node-replacement-arrayp 'node-replacement-array array)
;;                               (natp node-replacement-count)
;;                               (<= node-replacement-count (alen1 'node-replacement-array array)))))
;;   (if (endp assumptions)
;;       (mv (erp-nil) node-replacement-array node-replacement-count dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
;;     (let ((assumption (first assumptions)))
;;       (mv-let (mv erp node-replacement-array node-replacement-count dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
;;         (update-node-replacement-array-and-extend-dag-for-assumption assumption
;;                                                                         dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
;;                                                                         node-replacement-array node-replacement-count)
;;         (if erp
;;             (mv erp node-replacement-array node-replacement-count dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
;;           (make-node-replacement-array-and-extend-dag-aux (rest assumptions)
;;                                                              dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
;;                                                              node-replacement-array node-replacement-count))))))

;; Returns (mv erp node-replacement-array node-replacement-count dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist).
(defund make-node-replacement-array-and-extend-dag (assumptions
                                                    dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                                    known-booleans)
  (declare (xargs :guard (and (pseudo-term-listp assumptions)
                              (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                              (symbol-listp known-booleans))))
  (let ((alist (term-replacement-alist-for-assumptions assumptions known-booleans nil))
        (node-replacement-array (make-empty-array 'node-replacement-array 1))
        (node-replacement-count 0))
    (update-node-replacement-array-and-extend-dag-for-alist alist
                                                            dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                                            node-replacement-array node-replacement-count)))

(defthm make-node-replacement-array-and-extend-dag-return-type
  (implies (and (pseudo-term-listp assumptions)
                (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                (symbol-listp known-booleans))
           (mv-let (erp node-replacement-array node-replacement-count dag-array new-dag-len dag-parent-array dag-constant-alist dag-variable-alist)
             (make-node-replacement-array-and-extend-dag assumptions
                                                            dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                                            known-booleans)
             (implies (not erp)
                      (and (natp node-replacement-count)
                           (node-replacement-arrayp 'node-replacement-array node-replacement-array)
                           (bounded-node-replacement-arrayp 'node-replacement-array node-replacement-array new-dag-len)
                           (<= node-replacement-count (alen1 'node-replacement-array node-replacement-array))
                           (wf-dagp 'dag-array dag-array new-dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                           (<= dag-len new-dag-len)
                           ))))
  :hints (("Goal" :in-theory (e/d (make-node-replacement-array-and-extend-dag) (symbol-listp)))))

(defthm make-node-replacement-array-and-extend-dag-return-type-corollary
  (implies (and (pseudo-term-listp assumptions)
                (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                (symbol-listp known-booleans))
           (mv-let (erp node-replacement-array node-replacement-count dag-array new-dag-len dag-parent-array dag-constant-alist dag-variable-alist)
             (make-node-replacement-array-and-extend-dag assumptions
                                                            dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                                            known-booleans)
             (declare (ignore node-replacement-array node-replacement-count dag-array dag-parent-array dag-constant-alist dag-variable-alist))
             (implies (not erp)
                      (and
                           (integerp new-dag-len)
                           ))))
  :hints (("Goal" :use make-node-replacement-array-and-extend-dag-return-type
           :in-theory (disable make-node-replacement-array-and-extend-dag-return-type))))

(defthm make-node-replacement-array-and-extend-dag-return-type-chain
  (implies (and (pseudo-term-listp assumptions)
                (wf-dagp 'dag-array dag-array dag-len 'dag-parent-array dag-parent-array dag-constant-alist dag-variable-alist)
                (symbol-listp known-booleans)
                (<= bound dag-len))
           (mv-let (erp node-replacement-array node-replacement-count dag-array new-dag-len dag-parent-array dag-constant-alist dag-variable-alist)
             (make-node-replacement-array-and-extend-dag assumptions
                                                            dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                                            known-booleans)
             (declare (ignore NODE-REPLACEMENT-ARRAY NODE-REPLACEMENT-COUNT DAG-ARRAY DAG-PARENT-ARRAY DAG-CONSTANT-ALIST DAG-VARIABLE-ALIST))
             (implies (not erp)
                      (<= bound new-dag-len))))
  :hints (("Goal" :use make-node-replacement-array-and-extend-dag-return-type
           :in-theory (disable make-node-replacement-array-and-extend-dag-return-type))))
