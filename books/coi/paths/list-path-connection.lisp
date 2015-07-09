; Computational Object Inference
; Copyright (C) 2005-2014 Kookamara LLC
;
; Contact:
;
;   Kookamara LLC
;   11410 Windermere Meadows
;   Austin, TX 78759, USA
;   http://www.kookamara.com/
;
; License: (An MIT/X11-style license)
;
;   Permission is hereby granted, free of charge, to any person obtaining a
;   copy of this software and associated documentation files (the "Software"),
;   to deal in the Software without restriction, including without limitation
;   the rights to use, copy, modify, merge, publish, distribute, sublicense,
;   and/or sell copies of the Software, and to permit persons to whom the
;   Software is furnished to do so, subject to the following conditions:
;
;   The above copyright notice and this permission notice shall be included in
;   all copies or substantial portions of the Software.
;
;   THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
;   IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
;   FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
;   AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
;   LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
;   FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
;   DEALINGS IN THE SOFTWARE.

 (in-package "ACL2")

;;This book provides functions to translate back and forth between lists
;;(which are accessed positionally) and records (which are accessed by named
;;keys).  The order of names in the KEY-NAMES arguments to RECORD-TO-LIST and
;;LIST-TO-RECORD indicates how the keys for the record correspond to the
;;positions in the list.

;;bzo Maybe this book should be renamed, since it doesn't really include any path stuff (now it does, at the bottom)

(include-book "../records/domain")

(include-book "../bags/extras")
(local (include-book "arithmetic/top-with-meta" :dir :system))





;rename and move
(defthm list::memberp-of-nth-cdr
  (implies (bag::unique lst)
           (equal (list::memberp (nth 0 lst) (cdr lst))
                  nil)))

(defthm nth-equal-car-when-unique-rewrite
  (implies (and (bag::unique lst)
                (< n (len lst))
                (consp lst))
           (equal (equal (nth n lst) (car lst))
                  (equal (nfix n) 0)))
  :hints (("Goal" :in-theory (enable NTH BAG::UNIQUE-OF-CONS))))

(defthm list::find-index-of-nth-same
  (implies (and (bag::unique key-names)
                (< (nfix n) (len key-names))
                (natp n) ;bzo drop?
                )
           (equal (list::find-index (nth n key-names) key-names)
                  n))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (e/d (list::find-index nth)
                           (;find-index-of-cdr
                            )))))



(local (in-theory (enable G-OF-S-REDUX)))

;;
;; LIST-TO-RECORD
;;

(defund list-to-record (lst key-names)
  (if (endp key-names)
      nil ;the emoty record
    (s (car key-names)
       (car lst)
       (list-to-record (cdr lst) (cdr key-names)))))

;;
;; RECORD-TO-LIST
;;

;the order of the key-names determines the order in which their corresponding values end up in the list
(defund record-to-list (r key-names)
  (if (endp key-names)
      nil ;the empty list
    (cons (g (car key-names) r)
          (record-to-list
           ;(clr (car key-names)
                r;
                ;) ;trying...
           (cdr key-names)))))

;; (defun my-ind (lst key-names)
;;   (if (not (consp key-names))
;;       (list lst key-names)
;;     (my-ind (lst key-names)

(defthm RECORD-TO-LIST-of-s-irrel
  (implies (not (list::memberp key key-names))
           (equal (RECORD-TO-LIST (S key val r) KEY-NAMES)
                  (RECORD-TO-LIST r KEY-NAMES)))
  :hints (("Goal" :in-theory (enable record-to-list))))


(defthm record-to-list-of-list-to-record
  (implies (and (equal (len lst) (len key-names))
                (bag::unique key-names))
           (list::equiv (record-to-list (list-to-record lst key-names) key-names)
                        lst))
  :hints (("Goal" :in-theory (enable list-to-record record-to-list)
           :do-not '(generalize eliminate-destructors))))

;; (defun ind (keys r)
;;   (declare (xargs :verify-guards nil))
;;   (if (not (consp keys))
;;       (list keys r)
;;     (ind (cdr keys)
;;          (clr (set::head (RKEYS R)) r);
;;          ;(gacc::wr (set::head keys) (gacc::rd (set::head keys) tr) tr)
;;          )))

(defthm record-to-list-of-clr-irrel
  (implies (not (list::memberp key keys))
           (equal (record-to-list (clr key r) keys)
                  (record-to-list r keys)))
  :hints (("Goal" :in-theory (enable record-to-list))))


;; (thm
;;  (implies
;;   :pl (ACL2-COUNT (CLR x R))

;; (thm
;;  (IMPLIES (CONSP R)
;;           (< (ACL2-COUNT (CLR (SET::HEAD (RKEYS R)) R))
;;              (ACL2-COUNT R))))

;; ;bzo try putting in remove-1 for remove-all
;; (skip-proofs
;; (defun ind99 (keys r)
;;   (declare (xargs :verify-guards nil))
;;   (if (not (consp r))
;;       (list keys r)
;;     (ind99 (bag::remove-all (set::head (rkeys r)) keys)
;;            (clr (set::head (rkeys r)) r) ;
;; ;(gacc::wr (set::head keys) (gacc::rd (set::head keys) tr) tr)
;;            )))
;;         )


;bzo redo everything to make key-names a set?

;; (local
;;  (defthm list-to-record-of-record-to-list
;;    (implies (and (equal rk (list::2set key-names))
;;                  (equal (rkeys r) rk)
;;                  (bag::unique key-names) ;can drop??
;;                  )
;;             (equal (list-to-record (record-to-list r key-names) key-names)
;;                    r))
;;    :hints (("Goal" ;:induct (ind key-names r)
;;             :in-theory (e/d (list-to-record)
;;                             (SET::DOUBLE-CONTAINMENT))
;; ;           :induct t
;;             :induct (ind101 rk key-names r)
;;             :expand ((RECORD-TO-LIST R KEY-NAMES)
;; ;(RECORD-TO-LIST R (CDR KEY-NAMES))
;;                      )
;;             :do-not '(generalize eliminate-destructors)))))

;; ;drop?
;; (defthm list-to-record-of-record-to-list-better
;;   (implies (and (equal (rkeys r) (list::2set key-names))
;;                 (bag::unique key-names) ;can drop??
;;                 )
;;            (equal (list-to-record (record-to-list r key-names) key-names)
;;                   r)))




;bzo tons of stuff to move out...

;bzo what other theorems do we need?
(defthm g-of-list-to-record
  (implies (list::memberp key key-names) ;bzo use list::memberp?
           (equal (g key (list-to-record lst key-names))
                  (nth (list::find-index key key-names) lst)))
  :hints (("Goal" :in-theory (enable list-to-record))))

(local
 (defun cdr-cdr-minus1-induct (x y n)
   (if (endp x)
       (list x y n)
     (cdr-cdr-minus1-induct (cdr x) (cdr y) (+ -1 n)))))

(defthm clr-of-list-to-record
  (implies (bag::unique key-names) ;t;(consp key-names)
           (equal (clr key (list-to-record lst key-names))
                  (list-to-record (list::clear-nth (list::find-index key key-names) lst) key-names)))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (e/d (list-to-record
                            list::find-index
                            list::CDR-OF-clear-NTH
                            )
                           (;FIND-INDEX-OF-CDR
                            )))))



(defthm g-of-list-to-record-irrel
  (implies (not (list::memberp key keys))
           (equal (g key (list-to-record lst keys))
                  nil))
  :hints (("Goal" :in-theory (enable LIST-TO-RECORD))))


;; (thm
;;  (equal (LIST-TO-RECORD (UPDATE-NTH n val lst) key-names)
;;         (if (< (nfix n) (len key-names))
;;             (cpath::s (nth n key-names) val (LIST-TO-RECORD lst key-names))
;;           (LIST-TO-RECORD lst key-names)))
;;  :hints (("Goal" :in-theory (enable LIST-TO-RECORD))))

;(in-theory (disable TAG-LOCATION-ELIMINATION))

(local (defun cdr-minus1-induction (x n)
         (if (endp x)
             (list x n)
           (cdr-minus1-induction (cdr x) (+ -1 n)))))

(defthm nth-of-record-to-list
  (implies (and (natp n)
                (bag::unique keys)
                (< n (len keys)))
           (equal (nth n (record-to-list r keys))
                  (g (nth n keys) r)))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :induct (cdr-cdr-minus1-induct keys lst n)
           :in-theory (e/d (list::nth-0-becomes-car
                            record-to-list) ()))))


;now characterize how s and update-nth change what these functions do?


;bzo delete this old stuff if we don't need it

;; ;functions to map back and forth from a list (accessed positionally with nth
;; ;and update-nth) to a nested record suitable for accessing with paths
;; ;The list in question can be the logical representation of a stobj.

;; (defun wrap (x)
;;   (s :val x nil))

;; (defun unwrap (wrapped-x)
;;   (g :val wrapped-x))

;; ;This wraps the values so that, looking at a record, we can tell the
;; ;difference between a wrapped nil and nothing at all?
;; (defun list-to-record-aux (n lst)
;;   (declare (xargs :measure (nfix (+ 1 n))))
;;   (if (or (not (integerp n))
;;           (< n 0))
;;       nil
;;     (s n
;;        (wrap (nth n lst))
;;        (list-to-record-aux (+ -1 n) lst))))

;; (defun list-to-record (lst)
;;   (list-to-record-aux (len lst) lst))

;; (defund record-to-list-aux (keys r)
;;   (if (set::empty keys)
;;       nil ;the empty typed record
;;     (update-nth (set::head keys) ;nfix?
;;                 (unwrap (g (set::head keys) r))
;;                 (record-to-list-aux (set::tail keys) r))))

;; (defun record-to-list (r)
;;   (record-to-list-aux (rkeys r) r))

;; (defund all-values-wrapped-aux (keys r)
;;   (if (set::empty keys)
;;       t
;;     (let ((value (g (set::head keys) r)))
;;       (and (consp value)
;;            (equal (car value) ':val)))))

;; (defun all-values-wrapped (r)
;;   (all-values-wrapped-aux (rkeys r) r))

;; (set::quantify-predicate (natp x))

;; (defthm nth-of-record-to-list-aux
;;   (implies (set::all-list<natp> keys) ;otherwise might be a that nfixes to n but isn't equal to n (or several such keys)
;;            (equal (nth n (record-to-list-aux keys r))
;;                   (if (set::in (nfix n) keys) ;could say n is among the nfixed keys?
;;                       (unwrap (g (nfix n) r))
;;                     nil)))
;;   :hints (("Goal" :induct (record-to-list-aux keys r)
;;            :in-theory (enable record-to-list-aux)
;;            :do-not '(generalize eliminate-destructors))))

;; (defun convertible-to-list (r)
;;   (and (set::all-list<natp> (rkeys r))
;;        (all-values-wrapped r)))

;; ;for dave
;; (defthm nth-of-record-to-list
;;   (implies (convertible-to-list r)
;;            (equal (nth n (record-to-list r))
;;                   (if (set::in (nfix n) (rkeys r))
;;                       (unwrap (g (nfix n) r))
;;                     nil))))

;; Is the wrapping okay?

;; how do we really want these accessors to look?

;; (gp '(:st *aamp.tos* :val) st)

;; ;i'd rather have:
;; (gp '(:st :tos) st)

;; pass in sotbj field descriptor?





;; (thm
;;  (implies t
;;           (equal (record-to-list (s a v r))
;;                  (update-nth (nfix a)




;; g of list-to-record
;; list-to-record of update-nth
;; wf-list of update-nth
;; convertible-to-list of s?

;; 2 inverses

(defthm len-of-record-to-list
  (equal (len (record-to-list r keys))
         (len keys))
  :hints (("Goal" :in-theory (enable record-to-list))))

(local (defun cdr-sub1-induct (x n)
         (if (endp x)
             (list x n)
           (cdr-sub1-induct (cdr x) (+ -1 n)))))

(defthm clear-nth-of-record-to-list
  (implies (and (natp n)
                (< n (len keys))
                (bag::unique keys)
                )
           (equal (list::clear-nth n (record-to-list r keys))
                  (record-to-list (clr (nth n keys) r) keys)))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :induct (cdr-sub1-induct keys n)
           :in-theory (enable record-to-list))))

(defun ind101 (keys r)
  (if (endp keys)
      (list keys r)
    (ind101 (cdr keys) (clr (car keys) r))))

(local
 (defthm unique-implies-open-subsetp
   (implies
    (and
     (bag::unique list)
     (consp list))
    (equal (subsetp x list)
           (subsetp (remove (car list) x) (cdr list))))
   :hints (("Goal" :in-theory (enable bag::memberp))))
 )

(local
 (defthm list-to-record-of-record-to-list-better2
   (implies (and
             (list::subsetp (rkeys r) key-names)
             (bag::unique key-names))
            (equal (list-to-record (record-to-list r key-names) key-names)
                   r))
   :hints (("Goal"
            :in-theory (e/d (list-to-record)
                            (REMOVE))
            :induct (ind101 key-names r)
            :expand ((RECORD-TO-LIST R KEY-NAMES))
            :do-not '(generalize eliminate-destructors))))
 )

(defthm list-to-record-of-record-to-list-better3
  (implies (and (list::subsetp (rkeys r) key-names)
                (bag::unique key-names) ;can drop??
                )
           (equal (list-to-record (record-to-list r key-names) key-names)
                  r)))

(include-book "path") ;move this up?

(defthm clrp-singleton-of-list-to-record
  (implies (bag::unique key-names)
           (equal (cpath::clrp (list key) (list-to-record lst key-names))
                  (list-to-record
                   (update-nth (list::find-index key key-names)
                               nil lst)
                   key-names)))
  :hints (("Goal" :in-theory (e/d (cpath::clrp cpath::sp s-becomes-clr)
                                  (cpath::sp==r cpath::s-to-sp s==r CPATH::SP-TO-CLRP)))))

;gen to non singletons?
(defthm gp-singleton-of-list-to-record
  (implies (list::memberp key key-names)
           (equal (cpath::gp (list key)
                            (list-to-record lst key-names))
                  (nth (list::find-index key key-names)
                       lst)))
  :hints (("Goal" :in-theory (enable cpath::gp))))



(defthm list-to-record-of-update-nth-usual-case
  (implies (and (< (nfix n) (len key-names))
                (natp n)
                (bag::unique key-names)
                )
           (equal (list-to-record (update-nth n val lst) key-names)
                  (cpath::s (nth n key-names) val (list-to-record lst key-names))))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :induct (cdr-cdr-minus1-induct lst key-names n)
           :expand ((list-to-record (update-nth 0 nil (update-nth n nil lst))
                                          key-names))
           :in-theory (e/d (list::clear-nth
                            list-to-record
                            list::update-nth-of-cdr
                            list::clear-nth-of-cdr)
                           (list::cdr-of-update-nth
                            LIST::UPDATE-NTH-BECOMES-CLEAR-NTH
                            LIST::UPDATE-NTH-EQUAL-REWRITE
                            )))))

(defthm acl2::record-to-list-of-s-not-irrel
  (implies (and (list::memberp acl2::key acl2::key-names)
                (bag::unique acl2::key-names))
           (equal (acl2::record-to-list (s acl2::key acl2::val acl2::r)
                                        acl2::key-names)
                  (update-nth (list::find-index acl2::key acl2::key-names)
                              acl2::val (acl2::record-to-list acl2::r acl2::key-names))))
  :hints (("Goal" :in-theory (enable acl2::record-to-list))))
