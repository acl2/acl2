; A book about patterns of values in BV lists
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;these are rules about lists of BVs

(include-book "kestrel/bv/getbit" :dir :system)
(include-book "kestrel/lists-light/firstn" :dir :system)
(include-book "bvnth")
(include-book "bvnot-list")

;; (in-theory (disable firstn-of-one-more))
;; (theory-invariant (incompatible (:rewrite cons-nth-onto-firstn) (:rewrite  firstn-of-one-more)))

;; (thm
;;  (equal (MAXELEM (FIRSTN (+ 1 n) lst))
;;         (if (< (MAXELEM (FIRSTN n lst))

;(local (in-theory (disable len))) ;bozo looped too

;; (thm
;;  (IMPLIES (< N (LEN LST))
;;           (EQUAL (LIST::CLEAR-NTH N (BYTE-FIX-LIST LST))
;;                  (BYTE-FIX-LIST (LIST::CLEAR-NTH N LST))))
;;  :hints (("Goal" :in-theory (enable BYTE-FIX-LIST LIST::CLEAR-NTH))))


;; ;ffffixme change this to use the unsiged representation
;; ;BBBOZO change this to handle booleans
;; ;adding len and type params..
;; ;BBBOZO should this really byte-fix (etc.) its values?  if so, don't use it to phrase the postcond, or you'll be able to prove that the contents are something not quite true (but that byte-fixes) to the real values
;; ;this used to change the length
;; (defund store-array (ref contents len type heap)
;;   (acl2::set-field ref
;;                    (array-contents-pair) ;(array-contents-pair)
;;                    ;;bbozo handle other types
;;                    (if (equal type ':byte)
;;                        (bvchop-list 8 (take len contents)) ;(byte-fix-list (take len contents))
;;                      (if (equal type ':int)
;;                          (bvchop-list 32 (take len contents)) ;(int-fix-list (take len contents))
;;                        (list 'error-unknown-type-in-store-array type)))
;;                    heap))

;; (defund store-array-list (ref-list contents-list len type heap)
;;   (if (endp ref-list)
;;       heap
;;     (store-array (car ref-list)
;;                  (car contents-list)
;;                  len
;;                  type
;;                  (store-array-list (cdr ref-list) (cdr contents-list) len type heap))))

;; (defthm store-array-list-of-true-list-fix
;;   (equal (store-array-list (true-list-fix ref-list) contents-list len type heap)
;;          (store-array-list ref-list contents-list len type heap))
;;   :hints (("Goal" :in-theory (enable store-array-list TRUE-LIST-FIX))))


;; (defthm array-contents-of-store-array
;;   (equal (array-contents ad (store-array ad contents len ':byte heap))
;;          ;(byte-fix-list (take len contents))
;;          (bvchop-list 8 (take len contents))
;;          )
;;   :hints (("Goal" :in-theory (enable store-array))))

;; (defund store-array-2d (ref contents numrows rowsize type heap)
;;   (store-array-list (take numrows (array-contents ref heap)) contents rowsize type heap))

;; (defthm get-field-of-store-array-irrel
;;   (implies (not (equal ref ref2))
;;            (equal (get-field ref pair (store-array ref2 contents-list len type heap))
;;                   (get-field ref pair heap)))
;;   :hints (("Goal" :in-theory (enable store-array))))

;; (defthm get-field-of-store-array-list-irrel
;;   (implies (not (memberp ref ref-list))
;;            (equal (get-field ref pair (store-array-list ref-list contents-list len type heap))
;;                   (get-field ref pair heap)))
;;   :hints (("Goal" :in-theory (enable store-array-list))))

;; (in-theory (enable store-array)) ;bozo okay?

;; (thm
;;  (implies (cdr x)
;;          (> (len x) 0))
;;  :hints (("Goal" :in-theory (e/d (len) (list::len-of-cdr)))))

;; ;use polarities!
;; (defthmd consp-len-bound-hack
;;   (implies (consp term)
;;            (equal (<= (len term) 1)
;;                   (equal 1 (len term)))))

;; (defun bitnot-list (lst)
;;   (declare (xargs :guard (all-integerp lst)))
;;   (if (atom lst)
;;       nil
;;     (cons (bitnot (car lst))
;;           (bitnot-list (cdr lst)))))

;define in terms of a map-bvnot?
;;(defmap bitnot-list (x) (bitnot x) :declares ((xargs :guard (all-integerp x))))

;; Check whether each item of LST1 is the negation of the corresponding item in LST2.
;this stops when the first list runs out
(defun negated-elems-listp (width lst1 lst2)
  (declare (xargs :guard (natp width)))
  (if (atom lst1)
      t
    (and (consp lst2)
         (let ((item1 (first lst1)))
           (and (integerp item1)
                (equal (bvnot width item1) (first lst2))
                (negated-elems-listp width (rest lst1) (rest lst2)))))))

(defthm negated-elems-listp-rewrite
  (implies (true-listp lst1)
           (iff (negated-elems-listp width lst1 lst2)
                (and (all-integerp lst1)
                     (equal (firstn (len lst1) lst2) (bvnot-list width lst1)))))
  :hints (("Goal" :in-theory (disable ;CDR-OF-TAKE-BECOMES-SUBRANGE-BETTER
                              ))))

;; ;do we still use this?
;; (defun push-bvchop-list (size lst)
;;   (declare (type (integer 0 *) size)
;;            (xargs :guard ;(all-integerp lst)
;;                   (true-listp lst)
;;                   ))
;;   (bvchop-list size lst))

;; (defund array-ref-p (arrayref)
;;   (and (equal (len arrayref) 2) ;ex: '(ref 3)
;;        (equal (car arrayref) 'ref) ;bozo
;;        (true-listp arrayref)
;;        ))

;; ;bozo handle this better?
;; (defthm cadrs-equal
;;   (implies (and (array-ref-p a1)
;;                 (array-ref-p a2))
;;            (equal (equal (cadr a1)
;;                          (cadr a2))
;;                   (equal a1
;;                          a2)))
;;   :hints (("Goal" :in-theory (enable array-ref-p))))

(defund getbit-is-always-0 (n items)
  (declare (xargs :guard (all-integerp items))
           (type (integer 0 *) n)
           )
  (if (atom items)
      t
    (and (equal 0 (getbit n (car items)))
         (getbit-is-always-0 n (cdr items)))))

(defund getbit-is-always-1 (n items)
  (declare (xargs :guard (all-integerp items))
           (type (integer 0 *) n)
           )
  (if (atom items)
      t
    (and (equal 1 (getbit n (car items)))
         (getbit-is-always-1 n (cdr items)))))

;; ;bozo remove definitions of this stuff elsewhere:
;; ;bits come in with the least significant bit first
;; ;deprecate?
;; (defun rev-bitlist-to-bv (bitlist)
;;   (if (endp bitlist)
;;       0
;;     (bvcat (+ -1 (len bitlist))
;;            (rev-bitlist-to-bv (cdr bitlist)) 1
;;            (car bitlist))))

;; (DEFthmd REV-BITLIST-TO-BV-opener
;;   (implies (consp bitlist)
;;            (equal (REV-BITLIST-TO-BV BITLIST)
;;                   (bvcat (+ -1 (LEN BITLIST))
;;                          (REV-BITLIST-TO-BV (CDR BITLIST))
;;                          1 (CAR BITLIST)))))

;; ;bits come in with the most significant bit first
;; ;deprecate?
;; (defund bitlist-to-bv (bitlist)
;;   (rev-bitlist-to-bv (reverse-list bitlist)))

;; ;move?
;; (defun contiguousp (items)
;;   (declare (xargs :guard (and (all-integerp items) ;gen?
;;                               (true-listp items))))
;;   (if (endp items)
;;       t
;;     (if (endp (cdr items))
;;         t
;;       (and (equal (second items) (+ 1 (first items)))
;;            (contiguousp (cdr items))))))

;; (defthm all-signed-byte-p-implies-all-integerp
;;   (implies (all-signed-byte-p free x)
;;            (all-integerp x))
;;   :hints (("Goal" :in-theory (enable all-signed-byte-p all-integerp))))

(defthm getbit-of-nth-when-getbit-is-always-0
  (implies (and (getbit-is-always-0 n vals)
                (natp n)
                (natp index))
           (equal (getbit n (nth index vals))
                  0))
  :hints (("Goal" :in-theory (e/d (getbit-is-always-0 nth
                                     GETBIT-WHEN-VAL-IS-NOT-AN-INTEGER) (;nth-of-cdr
                                                                         )))))

(defthm getbit-of-bvnth-when-getbit-is-always-0
  (implies (and (getbit-is-always-0 n vals)
                (natp n)
                (natp esize))
           (equal (getbit n (bvnth esize isize index vals))
                  0))
  :hints (("Goal" :cases ((< N ESIZE))
           :in-theory (enable bvnth))))

(defthm getbit-of-nth-when-getbit-is-always-1
  (implies (and (getbit-is-always-1 n vals)
                (natp n)
                (natp index)
                (< index (len vals)) ;bozo
                )
           (equal (getbit n (nth index vals))
                  1))
  :hints (("Goal" :in-theory (e/d (getbit-is-always-1 nth) (;nth-of-cdr
                                                            )))))

(defthmd getbit-is-always-1-implies-ALL-INTEGERP
  (implies (getbit-is-always-1 n lst)
           (ALL-INTEGERP lst))
  :hints (("Goal" :in-theory (enable ALL-INTEGERP getbit-is-always-1 GETBIT-WHEN-VAL-IS-NOT-AN-INTEGER))))

(defthm getbit-of-bvnth-when-getbit-is-always-1
  (implies (and (getbit-is-always-1 n vals)
                (natp n)
                (natp esize)
                (< n esize)
                (natp isize)
                (natp index)
                (< index (len vals)) ;ffixme new - can i drop this again?
                )
           (equal (getbit n (bvnth esize isize index vals))
                  1))
  :hints (("Goal" :cases ((< N ESIZE))
           :in-theory (enable bvnth getbit-is-always-1-implies-ALL-INTEGERP ;BVCHOP-LEQ
                              ))))
