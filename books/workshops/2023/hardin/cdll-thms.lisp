;; Copyright (C) 2023-2024 David S. Hardin
;;
;; License: (An MIT/X11-style license)
;;
;;   Permission is hereby granted, free of charge, to any person obtaining a
;;   copy of this software and associated documentation files (the "Software"),
;;   to deal in the Software without restriction, including without limitation
;;   the rights to use, copy, modify, merge, publish, distribute, sublicense,
;;   and/or sell copies of the Software, and to permit persons to whom the
;;   Software is furnished to do so, subject to the following conditions:
;;
;;   The above copyright notice and this permission notice shall be included in
;;   all copies or substantial portions of the Software.
;;
;;   THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
;;   IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
;;   FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
;;   AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
;;   LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
;;   FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
;;   DEALINGS IN THE SOFTWARE.

;; **** Circular Doubly-Linked List (CDLL) theorems to support Knuth's "Dancing Links"


(in-package "RTL")

(include-book "half-rac-thms")

(include-book "cdll-trans")

(include-book "data-structures/list-defthms" :dir :system)

(include-book "take-thms")

(include-book "nthcdr-thms")

(include-book "rtl/rel11/lib/bits" :dir :system)

(include-book "arithmetic-5/top" :dir :system)


(defund CDLL_VAL_EXP () 63)
(defund CDLL_MIN_VAL () (1+ (- (expt 2 (CDLL_VAL_EXP)))))     ;; -2**63 + 1
(defund CDLL_MAX_VAL () (1- (expt 2 (CDLL_VAL_EXP))))         ;; (2**63 - 1)


;; CDLL theorems

(defun cdllnodep (nd)
  (and ;; (consp nd)
       (integerp (ag 'alloc nd))
       (<= 2 (ag 'alloc nd))
       (<= (ag 'alloc nd) 3)
       (integerp (ag 'val nd))
       (not (= (si (ag 'val nd) (1+ (CDLL_VAL_EXP))) (- (CDLL_MIN_VAL) 1)))
       (integerp (ag 'prev nd))
       (<= 0 (ag 'prev nd))
       (< (ag 'prev nd) (CDLL_MAX_NODE1))
       (integerp (ag 'next nd))
       (<= 0 (ag 'next nd))
       (< (ag 'next nd) (CDLL_MAX_NODE1))))


(defthm cdllnodep-consp--thm
  (implies (cdllnodep nd)
           (consp nd))
 :hints (("Goal" :use (:instance one-ag-ne-default-consp--thm (r nd) (a 'alloc))))
;; AP :rule-classes ((:forward-chaining :trigger-terms ((cdllnodep nd))) :rewrite))
 :rule-classes ((:forward-chaining :trigger-terms ((cdllnodep nd)))))

(defthm cdllnodep-arcdp--thm
  (implies (cdllnodep nd)
           (arcdp nd))
 :hints (("Goal" :use (:instance one-ag-ne-default-arcdp--thm (r nd) (a 'alloc))))
;; AP :rule-classes ((:forward-chaining :trigger-terms ((cdllnodep nd))) :rewrite))
 :rule-classes ((:forward-chaining :trigger-terms ((cdllnodep nd)))))


(defthm cdllnodep-ne-default-get-valu--thm
  (implies (cdllnodep nd)
           (not (= nd (default-get-valu)))))


(defthm as-next-preserves-cdllnodep--thm
  (implies
   (and (cdllnodep nd)
        (integerp v) (<= 0 v) (< v (cdll_max_node1)))
   (cdllnodep (as 'next v nd))))


(defthm as-prev-preserves-cdllnodep--thm
  (implies
   (and (cdllnodep nd)
        (integerp v) (<= 0 v) (< v (cdll_max_node1)))
   (cdllnodep (as 'prev v nd))))


(defun cdllnodeArrp-helper (arr j)
  (cond ((not (true-listp arr)) nil)
        ((null arr) t)
        ((not (and (integerp j) (<= 0 j))) nil)
        ((not (consp (car arr))) nil)
        ((not (= (car (car arr)) j)) nil)
        ((not (cdllnodep (cdr (car arr)))) nil)
        (t (cdllnodeArrp-helper (cdr arr) (1+ j)))))


(defthm cdllnodeArrp-helper-true-listp--thm
  (implies (cdllnodeArrp-helper arr j)
           (true-listp arr)))

(defthm cdllnodeArrp-helper-car-nth-natp--thm
  (implies
   (and (integerp k) (<= 0 k) (< k (len arr))
        (integerp j) ;; (<= 0 j)
        (cdllnodeArrp-helper arr j))
   (natp (car (nth k arr)))))

(defthm cdllnodeArrp-helper-car-nth--thm
  (implies
   (and (integerp k) (<= 0 k) (< k (len arr))
        (integerp j) ;; (<= 0 j)
        (cdllnodeArrp-helper arr j))
   (= (car (nth k arr)) (+ j k))))

(defthmd cdllnodeArrp-helper-cdr-nth--thm
  (implies
   (and (integerp k) (<= 0 k) (< k (len arr))
        (integerp j) ;; (<= 0 j)
        (cdllnodeArrp-helper arr j))
   (cdllnodep (cdr (nth k arr)))))

(defthm cdllnodeArrp-helper-car-<<--thm
  (implies
   (and (integerp k) (<= 0 k) (< k (1- (len arr)))
        (integerp j) ;; (<= 0 j)
        (cdllnodeArrp-helper arr j))
   (acl2::<< (car (nth k arr)) (car (nth (1+ k) arr))))
  :hints (("Goal" :in-theory (e/d (acl2::<< lexorder alphorder) ()))))

(defthm cdllnodeArrp-helper-car-car-<<-car-cadr--thm
  (implies
   (and (integerp j) ;; (<= 0 j)
        (not (null arr))
        (cdllnodeArrp-helper arr j))
   (acl2::<< (car (car arr)) (car (cadr arr))))
  :hints (("Goal" :in-theory (e/d (acl2::<< lexorder alphorder) ()))))

(defthmd cdllnodeArrp-helper-arcdp--thm
  (implies (cdllnodeArrp-helper arr j)
           (arcdp arr)))


(defthm cdllnodeArrp-helper-take--thm
  (implies
   (and (integerp j) (<= 0 j) (< j (len arr))
        (cdllnodeArrp-helper arr m))
   (cdllnodeArrp-helper (take j arr) m)))

(defthm cdllnodeArrp-helper-nthcdr--thm
  (implies
   (and (integerp j) (<= 0 j) ;; (< j (len arr))
        (cdllnodeArrp-helper arr m))
   (cdllnodeArrp-helper (nthcdr j arr) (+ j m))))


(defthmd cdllnodeArrp-helper-take-nthcdr--thm
  (implies
   (and (true-listp arr)
        (integerp j)
        (<= 0 j)
        (< j (len arr))
        (integerp m)
        (<= 0 m))
   (= (cdllnodeArrp-helper arr m)
      (and (cdllnodeArrp-helper (take j arr) m) (cdllnodeArrp-helper (nthcdr j arr) (+ j m))))))


(defthmd cdllnodeArrp-helper-append-2-take-nthcdr--thm
  (implies
   (and (true-listp arr)
        (integerp j) (<= 0 j) (< j (len arr))
        (integerp m) (<= 0 m))
   (= (cdllnodeArrp-helper (append (take j arr) (nthcdr j arr)) m)
      (and (cdllnodeArrp-helper (take j arr) m) (cdllnodeArrp-helper (nthcdr j arr) (+ j m))))))

(defthmd cdllnodeArrp-helper-take-list-nthcdr--thm
  (implies
   (and (true-listp arr)
        (integerp j) (<= 0 j) (< j (len arr))
        (integerp m) (<= 0 m))
   (= (cdllnodeArrp-helper arr m)
      (and (cdllnodeArrp-helper (take j arr) m)
           (cdllnodeArrp-helper (list (nth j arr)) (+ j m))
           (cdllnodeArrp-helper (nthcdr (1+ j) arr) (+ j m 1))))))

(DEFTHMD CDLLNODEARRP-HELPER-APPEND-3-TAKE-LIST-NTHCDR--THM
  (IMPLIES
   (AND (TRUE-LISTP ARR)
        (INTEGERP J) (<= 0 J) (< J (LEN ARR))
        (INTEGERP M) (<= 0 M))
   (= (CDLLNODEARRP-HELPER (APPEND (TAKE J ARR) (LIST (NTH J ARR)) (NTHCDR (1+ J) ARR)) M)
      (AND (CDLLNODEARRP-HELPER (TAKE J ARR) M)
           (CDLLNODEARRP-HELPER (LIST (NTH J ARR)) (+ J M))
           (CDLLNODEARRP-HELPER (NTHCDR (1+ J) ARR) (+ J M 1)))))
 :INSTRUCTIONS
 (:PROMOTE
  (:CLAIM (= (APPEND (TAKE J ARR) (LIST (NTH J ARR)) (NTHCDR (1+ J) ARR)) ARR)
          :HINTS (("Goal" :USE (:INSTANCE ACL2::APPEND-3-TAKE-LIST-NTH-NTHCDR--THM
                                           (I J)
                                           (LST ARR)))))
  (:DIVE 1 1)
  (:= ARR)
  :TOP
  (:PROVE :HINTS (("Goal" :USE (:INSTANCE CDLLNODEARRP-HELPER-TAKE-LIST-NTHCDR--THM))))))


(defun cdllnodeArrp (arr)
  (cdllnodeArrp-helper arr 0))


(defthm cdllnodeArrp-car-nth--thm
  (implies
   (and (integerp k) (<= 0 k) (< k (len arr))
        (cdllnodeArrp arr))
   (= (car (nth k arr)) k))
  :hints (("Goal" :use (:instance cdllnodeArrp-helper-car-nth--thm (j 0)))))

(defthm cdllnodeArrp-cdr-nth--thm
  (implies
   (and (integerp k) (<= 0 k) (< k (len arr))
        (cdllnodeArrp arr))
   (cdllnodep (cdr (nth k arr))))
  :hints (("Goal" :use (:instance cdllnodeArrp-helper-cdr-nth--thm (j 0)))))


(DEFTHMD CDLLNODEARRP-CDR-NTH-NE-AIFRP-TAG--THM
  (IMPLIES
   (AND (INTEGERP K) (<= 0 K) (< K (LEN ARR))
        (CDLLNODEARRP ARR))
   (NOT (= (CDR (NTH K ARR)) (AIFRP-TAG))))
  :INSTRUCTIONS
  (:PROMOTE
   (:CLAIM (CDLLNODEP (CDR (NTH K ARR))))
   (:CLAIM (CONSP (CDR (NTH K ARR))))
   :BASH))


(defthm cdllnodearrp-true-listp--thm
  (implies (cdllnodeArrp arr)
           (true-listp arr)))


(defthm cdllnodearrp-arcdp--thm
  (implies (cdllnodeArrp arr)
           (arcdp arr))
 :hints (("Goal" :use (:instance cdllnodearrp-helper-arcdp--thm (j 0))))
 :rule-classes ((:forward-chaining :trigger-terms ((cdllnodeArrp arr))) :rewrite))


(defthmd cdllnodeArrp-append-2-take-nthcdr--thm
  (implies
   (and (true-listp arr)
        (integerp j) (<= 0 j) (< j (len arr)))
   (= (cdllnodeArrp (append (take j arr) (nthcdr j arr)))
      (and (cdllnodeArrp-helper (take j arr) 0) (cdllnodeArrp-helper (nthcdr j arr) j))))
  :hints (("Goal" :use (:instance cdllnodeArrp-helper-append-2-take-nthcdr--thm (m 0)))))

(defthmd cdllnodearrp-append-3-take-list-nthcdr--thm
  (implies
   (and (true-listp arr)
        (integerp j) (<= 0 j) (< j (len arr)))
   (= (cdllnodeArrp (append (take j arr) (list (nth j arr)) (nthcdr (1+ j) arr)))
      (and (cdllnodeArrp-helper (take j arr) 0)
           (cdllnodeArrp-helper (list (nth j arr)) j)
           (cdllnodeArrp-helper (nthcdr (1+ j) arr) (1+ j)))))
  :hints (("Goal" :use (:instance cdllnodearrp-helper-append-3-take-list-nthcdr--thm (m 0)))))


(defthmd cdllnodeArrp-ag--thm
  (implies
   (and (cdllnodeArrp arr)
        (integerp k) (<= 0 k) (< k (len arr)))
   (= (ag k arr) (cdr (nth k arr))))
  :hints (("Goal" :use (:instance arcdp-ag-key-is-cdr-of-nth--thm (lst arr)))))

(defthm cdllnodeArrp-ag-is-cdllnodep--thm
  (implies
   (and (cdllnodeArrp arr)
        (integerp k) (<= 0 k) (< k (len arr)))
   (cdllnodep (ag k arr)))
  :hints (("Goal" :in-theory (e/d (cdllnodeArrp-ag--thm) ())))
  :rule-classes ((:forward-chaining :trigger-terms ((cdllnodeArrp arr))) :rewrite))


(DEFTHMD CDLLNODEARRP-AS-HELPER--THM
  (IMPLIES
   (AND (CDLLNODEARRP ARR)
        (INTEGERP K) (<= 0 K) (< K (LEN ARR))
        (CDLLNODEP V))
   (= (AS (CAR (NTH K ARR)) V ARR)
      (UPDATE-NTH K (CONS (CAR (NTH K ARR)) V) ARR)))
 :INSTRUCTIONS
 (:PROMOTE
  (:CLAIM (ARCDP ARR))
  (:CLAIM (NOT (= V (DEFAULT-GET-VALU))))
  (:CLAIM (ATOM (CAR (NTH K ARR))))
  (:CLAIM (NOT (EQUAL V (AIFRP-TAG))))
  (:CLAIM (NOT (= (CDR (NTH K ARR)) (AIFRP-TAG)))
   :HINTS (("Goal" :USE (:INSTANCE CDLLNODEARRP-CDR-NTH-NE-AIFRP-TAG--THM))))
  (:PROVE :HINTS (("Goal" :USE (:INSTANCE ARCDP-AS-K-IS-UPDATE-NTH-K--THM
                                           (LST ARR)))))))

(defthmd cdllnodearrp-as--thm
  (implies
   (and (cdllnodeArrp arr)
        (integerp k) (<= 0 k) (< k (len arr))
        (cdllnodep v))
   (= (as k v arr)
      (update-nth k (cons k v) arr)))
  :hints (("Goal" :use (:instance cdllnodearrp-as-helper--thm))))


(defthm cdllnodeArrp-update-nth-k-kth--thm
  (implies
   (and (cdllnodeArrp arr) ;; (cdllnodep v)
        (integerp k) (<= 0 k) (< k (len arr))
        (integerp j) (<= 0 j) (< j (len arr)))
   (= (car (nth j (update-nth k (cons k v) arr))) j)))

(defthm cdllnodeArrp-update-nth-k-car-nth-j--thm
  (implies
   (and (cdllnodeArrp arr) ;; (cdllnodep v)
        (integerp k) (<= 0 k) (< k (len arr))
        (integerp j) (<= 0 j) (< j (len arr)))
   (= (car (nth j (update-nth k (cons k v) arr))) j)))

(defthm cdllnodeArrp-update-nth-k-cdr-nth-j--thm
  (implies
   (and (cdllnodeArrp arr) (cdllnodep v)
        (integerp k) (<= 0 k) (< k (len arr))
        (integerp j) (<= 0 j) (< j (len arr)))
   (cdllnodep (cdr (nth j (update-nth k (cons k v) arr))))))


(defthm cdllnodeArrp-as-k-car-nth-j--thm
  (implies
   (and (cdllnodeArrp arr) (cdllnodep v)
        (integerp k) (<= 0 k) (< k (len arr))
        (integerp j) (<= 0 j) (< j (len arr)))
   (= (car (nth j (as k v arr))) j))
  :hints (("Goal" :in-theory (e/d (CDLLNODEARRP-AS--THM) ()))))

(defthm cdllnodeArrp-as-k-cdr-nth-j--thm
  (implies
   (and (cdllnodeArrp arr) (cdllnodep v)
        (integerp k) (<= 0 k) (< k (len arr))
        (integerp j) (<= 0 j) (< j (len arr)))
   (cdllnodep (cdr (nth j (as k v arr)))))
  :hints (("Goal" :in-theory (e/d (CDLLNODEARRP-AS--THM) ()))))


(DEFTHM AS-PRESERVES-CDLLNODEARRP--THM
  (IMPLIES
   (AND (CDLLNODEARRP ARR)
        (INTEGERP K) (<= 0 K) (< K (LEN ARR))
        (CDLLNODEP V))
   (CDLLNODEARRP (AS K V ARR)))
 :INSTRUCTIONS
 (:PROMOTE
  (:DIVE 1)
  (:CLAIM (= (AS K V ARR) (UPDATE-NTH K (CONS K V) ARR))
          :HINTS (("Goal" :USE (:INSTANCE CDLLNODEARRP-AS--THM))))
  (:= (UPDATE-NTH K (CONS K V) ARR))
  (:CLAIM
     (= (APPEND (TAKE K ARR) (LIST (CONS K V)) (NTHCDR (1+ K) ARR))
        (UPDATE-NTH K (CONS K V) ARR))
     :HINTS (("Goal" :USE (:INSTANCE ACL2::UPDATE-NTH-APPEND-TAKE-NTHCDR--THM
                                      (I K)
                                      (LST ARR)
                                      (Y (CONS K V))))))
  :TOP (:CLAIM (TRUE-LISTP ARR))
  (:CLAIM (TRUE-LISTP (UPDATE-NTH K (CONS K V) ARR)))
  (:CLAIM (= (LEN (UPDATE-NTH K (CONS K V) ARR))
             (LEN ARR)))
  (:CLAIM
    (= (CDLLNODEARRP (APPEND (TAKE K (UPDATE-NTH K (CONS K V) ARR))
                             (LIST (NTH K (UPDATE-NTH K (CONS K V) ARR)))
                             (NTHCDR (1+ K)
                                     (UPDATE-NTH K (CONS K V) ARR))))
       (AND (CDLLNODEARRP-HELPER (TAKE K (UPDATE-NTH K (CONS K V) ARR)) 0)
            (CDLLNODEARRP-HELPER (LIST (NTH K (UPDATE-NTH K (CONS K V) ARR))) K)
            (CDLLNODEARRP-HELPER (NTHCDR (1+ K) (UPDATE-NTH K (CONS K V) ARR)) (1+ K))))
    :HINTS
    (("Goal" :USE (:INSTANCE CDLLNODEARRP-APPEND-3-TAKE-LIST-NTHCDR--THM
                             (J K)
                             (ARR (UPDATE-NTH K (CONS K V) ARR))))))
  (:CONTRAPOSE 11)
  (:DIVE 1 1 1 1)
  (:= (TAKE K ARR))
  :UP (:DIVE 2 1 1)
  (:= (CONS K V))
  :UP :UP (:DIVE 2)
  (:= (NTHCDR (+ 1 K) ARR))
  :TOP (:DIVE 1 2 1 1)
  (:= (TAKE K ARR))
  :UP (:= T)
  :UP (:DIVE 2 1 1 1)
  (:= (CONS K V))
  :UP :UP (:= T)
  :UP (:DIVE 2 1)
  (:= (NTHCDR (+ 1 K) ARR))
  :UP
  (:CLAIM (CDLLNODEARRP-HELPER (NTHCDR (+ 1 K) ARR) (+ 1 K))
          :HINTS (("Goal" :USE (:INSTANCE CDLLNODEARRP-HELPER-NTHCDR--THM (J (+ 1 K)) (M 0)))))
  (:= T)
  :TOP (:CONTRAPOSE 11)
  :BASH))


(defthm cdllnodearrp-as-len--thm
  (implies
   (and (cdllnodeArrp arr)
        (integerp k) (<= 0 k) (< k (len arr))
        (cdllnodep v))
   (= (len (as k v arr)) (len arr)))
 :hints (("Goal" :in-theory (e/d (cdllnodearrp-as--thm) (len)))))


(in-theory (disable cdllnodeArrp))


(defun cdllp (CDObj)
  (and (integerp (ag 'nodeHd CDObj))
       (<= 0 (ag 'nodeHd CDObj))
       (< (ag 'nodeHd CDObj) (CDLL_MAX_NODE1))
       (integerp (ag 'nodeCount CDObj))
       (<= 0 (ag 'nodeCount CDObj))
       (<= (ag 'nodeCount CDObj) (CDLL_MAX_NODE1))
       (cdllnodeArrp (ag 'nodeArr CDObj))
       (= (len (ag 'nodeArr CDObj)) (CDLL_MAX_NODE1))))


(defthmd cdllp-consp--thm
  (implies (cdllp CDObj)
           (consp CDObj))
 :hints (("Goal" :use (:instance one-ag-ne-default-consp--thm (r CDObj) (a 'nodeArr)))))


(defthm cdllp-arcdp--thm
  (implies (cdllp CDObj)
           (arcdp CDObj))
 :hints (("Goal" :use (:instance one-ag-ne-default-arcdp--thm (r CDObj) (a 'nodeArr))))
 :rule-classes ((:forward-chaining :trigger-terms ((cdllp CDObj))) :rewrite))


(defmacro good-nodep (ndcount j arr)
  `(or (= ,ndcount 0)
       (and (< 0 ,ndcount)
            (integerp ,j)
            (<= 0 ,j)
            (< ,j (CDLL_MAX_NODE1))
            (= 3 (ag 'alloc (ag ,j ,arr))))))

(defmacro good-node-nextp (ndcount j arr)
  `(or (= ,ndcount 0)
       (and (< 0 ,ndcount)
            ;; (integerp (ag 'next (ag ,j ,arr)))
            ;; (<= 0 (ag 'next (ag ,j ,arr)))
            (< (ag 'next (ag ,j ,arr)) (CDLL_MAX_NODE1))
            (= 3 (ag 'alloc (ag (ag 'next (ag ,j ,arr)) ,arr))))))

(defmacro good-node-prevp (ndcount j arr)
  `(or (= ,ndcount 0)
       (and (< 0 ,ndcount)
            ;; (integerp (ag 'prev (ag ,j ,arr)))
            ;; (<= 0 (ag 'prev (ag ,j ,arr)))
            (< (ag 'prev (ag ,j ,arr)) (CDLL_MAX_NODE1))
            (= 3 (ag 'alloc (ag (ag 'prev (ag ,j ,arr)) ,arr))))))

(defmacro good-node-prev-nextp (ndcount j arr)
  `(or (= ,ndcount 0)
       (and (= ,ndcount 1)
            (= (ag 'next (ag ,j ,arr)) ,j)
            (= (ag 'prev (ag ,j ,arr)) ,j)
            (= (ag 'next (ag (ag 'prev (ag ,j ,arr)) ,arr)) ,j)
            (= (ag 'prev (ag (ag 'next (ag ,j ,arr)) ,arr)) ,j))
       (and (= ,ndcount 2)
            (not (= (ag 'next (ag ,j ,arr)) ,j))
            (not (= (ag 'prev (ag ,j ,arr)) ,j))
            (= (ag 'prev (ag ,j ,arr))
               (ag 'next (ag ,j ,arr)))
            (= (ag 'next (ag (ag 'prev (ag ,j ,arr)) ,arr)) ,j)
            (= (ag 'prev (ag (ag 'next (ag ,j ,arr)) ,arr)) ,j))
       (and (< 2 ,ndcount)
            (not (= (ag 'next (ag ,j ,arr)) ,j))
            (not (= (ag 'prev (ag ,j ,arr)) ,j))
            (not (= (ag 'prev (ag ,j ,arr))
                    (ag 'next (ag ,j ,arr))))
            (= (ag 'next (ag (ag 'prev (ag ,j ,arr)) ,arr)) ,j)
            (= (ag 'prev (ag (ag 'next (ag ,j ,arr)) ,arr)) ,j))))


;; Specialization for size == 2

(defmacro good-2-nodep (j CDObj)
  `(and (integerp ,j) (<= 0 ,j)  (< ,j (CDLL_MAX_NODE1))
        (= 3 (ag 'alloc (ag ,j (ag 'nodeArr ,CDObj))))
        (integerp (ag 'prev (ag ,j (ag 'nodeArr ,CDObj))))
        (<= 0 (ag 'prev (ag ,j (ag 'nodeArr ,CDObj))))
        (< (ag 'prev (ag ,j (ag 'nodeArr ,CDObj))) (CDLL_MAX_NODE1))
        (not (= (ag 'prev (ag ,j (ag 'nodeArr ,CDObj))) ,j))
        (= 3 (ag 'alloc (ag (ag 'prev (ag ,j (ag 'nodeArr ,CDObj))) (ag 'nodeArr ,CDObj))))
        (= (ag 'prev (ag ,j (ag 'nodeArr ,CDObj)))
           (ag 'next (ag ,j (ag 'nodeArr ,CDObj))))
        (integerp (ag 'next (ag ,j (ag 'nodeArr ,CDObj))))
        (<= 0 (ag 'next (ag ,j (ag 'nodeArr ,CDObj))))
        (< (ag 'next (ag ,j (ag 'nodeArr ,CDObj))) (CDLL_MAX_NODE1))
        (not (= (ag 'next (ag ,j (ag 'nodeArr ,CDObj))) ,j))
        (= 3 (ag 'alloc (ag (ag 'next (ag ,j (ag 'nodeArr ,CDObj))) (ag 'nodeArr ,CDObj))))
        (= (ag 'next (ag (ag 'prev (ag ,j (ag 'nodeArr ,CDObj))) (ag 'nodeArr ,CDObj))) ,j)
        (= (ag 'prev (ag (ag 'next (ag ,j (ag 'nodeArr ,CDObj))) (ag 'nodeArr ,CDObj))) ,j)))


(defun good-Objp (CDObj)
  (or (= 0 (ag 'nodeCount CDObj))
       (and (= (ag 'nodeCount CDObj) 1)
            (integerp (ag 'nodeHd CDObj))
            (<= 0 (ag 'nodeHd CDObj))
            (= 3 (ag 'alloc (ag (ag 'nodeHd CDObj) (ag 'nodeArr CDObj))))
            (< (ag 'nodeHd CDObj) (CDLL_MAX_NODE1))
            (= (ag 'prev (ag (ag 'nodeHd CDObj) (ag 'nodeArr CDObj))) (ag 'nodeHd CDObj))
            (= (ag 'next (ag (ag 'nodeHd CDObj) (ag 'nodeArr CDObj))) (ag 'nodeHd CDObj)))
       (and (= (ag 'nodeCount CDObj) 2)
            (good-2-nodep (ag 'nodeHd CDObj) CDObj)
            (good-2-nodep (ag 'next (ag (ag 'nodeHd CDObj) (ag 'nodeArr CDObj))) CDObj))
       (and (> (ag 'nodeCount CDObj) 2)
            (good-nodep (ag 'nodeCount CDObj) (ag 'nodeHd CDObj) (ag 'nodeArr CDObj))
            (good-node-nextp (ag 'nodeCount CDObj) (ag 'nodeHd CDObj) (ag 'nodeArr CDObj))
            (good-node-prevp (ag 'nodeCount CDObj) (ag 'nodeHd CDObj) (ag 'nodeArr CDObj))
            (good-node-prev-nextp (ag 'nodeCount CDObj) (ag 'nodeHd CDObj) (ag 'nodeArr CDObj)))))


(defun spacep (CDObj)
  (and (not (= (ag 'nodeCount CDObj) (CDLL_MAX_NODE1)))
       (< (cdll_find_free_node (ag 'nodeCount CDObj) (ag 'nodeArr CDObj)) (CDLL_MAX_NODE1))))


(DEFTHM AG-GE-LEN-ARR-EQ-DEFAULT-GET-VALU--THM
  (IMPLIES
   (AND (CDLLNODEARRP ARR)
        (INTEGERP J)
        (<= (LEN ARR) J))
   (= (AG J ARR) (DEFAULT-GET-VALU)))
 :INSTRUCTIONS
 (:PROMOTE
  (:CASESPLIT (NULL ARR))
  :BASH
  (:CLAIM (< 0 (LEN ARR)))
  (:CLAIM (= (CAR (NTH (1- (LEN ARR)) ARR)) (1- (LEN ARR)))
          :HINTS (("Goal" :USE (:INSTANCE CDLLNODEARRP-CAR-NTH--THM
                                           (K (1- (LEN ARR)))))))
  (:CLAIM (INTEGERP (CAR (NTH (1- (LEN ARR)) ARR))))
  (:CLAIM (ACL2::<< (CAR (NTH (1- (LEN ARR)) ARR)) J)
          :HINTS (("Goal" :IN-THEORY (E/D (ACL2::<< ALPHORDER LEXORDER) ()))))
  (:PROVE :HINTS (("Goal" :USE (:INSTANCE AG-ATOM-A-R-NTH-LEN-MINUS-1-R-<<-A--THM
                                           (A J)
                                           (R ARR)))))))

(DEFTHMD CDLLP-AG-GT-CDLL_MAX_NODE-NODEARR-EQ-DEFAULT-GET-VALU--THM
  (IMPLIES
   (AND (CDLLP CDOBJ)
        (INTEGERP J) (< (CDLL_MAX_NODE) J))
   (= (AG J (AG 'NODEARR CDOBJ)) (DEFAULT-GET-VALU)))
 :INSTRUCTIONS
 (:PROMOTE
  (:CLAIM (CDLLNODEARRP (AG 'NODEARR CDOBJ)))
  (:CLAIM (= (LEN (AG 'NODEARR CDOBJ))
             (1+ (CDLL_MAX_NODE))))
  (:CLAIM (= (CAR (NTH (CDLL_MAX_NODE) (AG 'NODEARR CDOBJ)))
             (CDLL_MAX_NODE))
          :HINTS (("Goal" :USE (:INSTANCE CDLLNODEARRP-CAR-NTH--THM
                                           (K (CDLL_MAX_NODE))
                                           (ARR (AG 'NODEARR CDOBJ))))))
  (:CLAIM (INTEGERP (CAR (NTH (CDLL_MAX_NODE) (AG 'NODEARR CDOBJ)))))
  (:CLAIM (ACL2::<< (CAR (NTH (CDLL_MAX_NODE) (AG 'NODEARR CDOBJ))) J)
          :HINTS (("Goal" :IN-THEORY (E/D (ACL2::<< ALPHORDER LEXORDER) NIL))))
  (:PROVE :HINTS (("Goal" :USE (:INSTANCE AG-ATOM-A-R-NTH-LEN-MINUS-1-R-<<-A--THM
                                           (A J)
                                           (R (AG 'NODEARR CDOBJ))))))))


(DEFTHM AG-NEXT-AG-INDEX-OF-ARR-IS-INTEGERP--THM
  (IMPLIES
   (AND (CDLLNODEARRP ARR)
        (INTEGERP INDEX) (<= 0 INDEX))
   (INTEGERP (AG 'NEXT (AG INDEX ARR))))
  :INSTRUCTIONS
  (:PROMOTE
   (:CASESPLIT (NULL ARR))
   :BASH
   (:CASESPLIT (NOT (< INDEX (LEN ARR))))
   :BASH
   (:CLAIM (CDLLNODEP (AG INDEX ARR)))
   :BASH))

(DEFTHM CDLLP-AG-NEXT-AG-INDEX-AG-NODEARR-IS-INTEGERP--THM
  (IMPLIES
   (AND (CDLLP CDOBJ)
        (INTEGERP INDEX) (<= 0 INDEX))
   (INTEGERP (AG 'NEXT (AG INDEX (AG 'NODEARR CDOBJ)))))
  :INSTRUCTIONS
  (:PROMOTE
   (CLAIM (CDLLNODEARRP (AG 'NODEARR CDOBJ)))
   (:CASESPLIT (NOT (< INDEX (CDLL_MAX_NODE1))))
   :BASH
   (:CLAIM (CDLLNODEP (AG INDEX (AG 'NODEARR CDOBJ))))
   :BASH))


(DEFTHM AG-NEXT-AG-INDEX-OF-ARR-GE-0--THM
  (IMPLIES
   (AND (CDLLNODEARRP ARR)
        (INTEGERP INDEX) (<= 0 INDEX))
   (<= 0 (AG 'NEXT (AG INDEX ARR))))
  :INSTRUCTIONS
  (:PROMOTE
   (:CASESPLIT (NULL ARR))
   :BASH
   (:CLAIM (< 0 (LEN ARR)))
   (:CASESPLIT (NOT (< INDEX (LEN ARR))))
   :BASH
   (:CLAIM (CDLLNODEP (AG INDEX ARR)))
   :BASH))

(DEFTHM CDLLP-AG-NEXT-AG-INDEX-AG-NODEARR-GE-0--THM
  (IMPLIES
   (AND (CDLLP CDOBJ)
        (INTEGERP INDEX) (<= 0 INDEX))
   (<= 0 (AG 'NEXT (AG INDEX (AG 'NODEARR CDOBJ)))))
  :INSTRUCTIONS
  (:PROMOTE
   (:CLAIM (CDLLNODEARRP (AG 'NODEARR CDOBJ)))
   (:CASESPLIT (NOT (< INDEX (CDLL_MAX_NODE1))))
   :BASH
   (:CLAIM (CDLLNODEP (AG INDEX (AG 'NODEARR CDOBJ))))
   :BASH))


(DEFTHM AG-NEXT-AG-INDEX-OF-ARR-LT-CDLL_MAX_NODE1--THM
  (IMPLIES
   (AND (CDLLNODEARRP ARR)
        (INTEGERP INDEX) (<= 0 INDEX))
   (< (AG 'NEXT (AG INDEX ARR)) (CDLL_MAX_NODE1)))
  :INSTRUCTIONS
  (:PROMOTE
   (:CASESPLIT (NULL ARR))
   :BASH
   (:CLAIM (< 0 (LEN ARR)))
   (:CASESPLIT (NOT (< INDEX (LEN ARR))))
   :BASH
   (:CLAIM (CDLLNODEP (AG INDEX ARR)))
   :BASH))

(DEFTHM CDLLP-AG-NEXT-AG-INDEX-AG-NODEARR-LT-CDLL_MAX_NODE1--THM
  (IMPLIES
   (AND (CDLLP CDOBJ)
        (INTEGERP INDEX) (<= 0 INDEX))
   (< (AG 'NEXT (AG INDEX (AG 'NODEARR CDOBJ))) (CDLL_MAX_NODE1)))
  :INSTRUCTIONS
  (:PROMOTE
   (:CLAIM (CDLLNODEARRP (AG 'NODEARR CDOBJ)))
   (:CASESPLIT (NOT (< INDEX (CDLL_MAX_NODE1))))
   :BASH
   (:CLAIM (CDLLNODEP (AG INDEX (AG 'NODEARR CDOBJ))))
   :BASH))


(DEFTHM AG-PREV-AG-INDEX-OF-ARR-IS-INTEGERP--THM
  (IMPLIES
   (AND (CDLLNODEARRP ARR)
        (INTEGERP INDEX) (<= 0 INDEX))
   (INTEGERP (AG 'PREV (AG INDEX ARR))))
  :INSTRUCTIONS
  (:PROMOTE
   (:CASESPLIT (NULL ARR))
   :BASH
   (:CASESPLIT (NOT (< INDEX (LEN ARR))))
   :BASH
   (:CLAIM (CDLLNODEP (AG INDEX ARR)))
   :BASH))

(DEFTHM CDLLP-AG-PREV-AG-INDEX-AG-NODEARR-IS-INTEGERP--THM
  (IMPLIES
   (AND (CDLLP CDOBJ)
        (INTEGERP INDEX) (<= 0 INDEX))
   (INTEGERP (AG 'PREV (AG INDEX (AG 'NODEARR CDOBJ)))))
  :INSTRUCTIONS
  (:PROMOTE
   (:CLAIM (CDLLNODEARRP (AG 'NODEARR CDOBJ)))
   (:CASESPLIT (NOT (< INDEX (CDLL_MAX_NODE1))))
   :BASH
   (:CLAIM (CDLLNODEP (AG INDEX (AG 'NODEARR CDOBJ))))
   :BASH))


(DEFTHM AG-PREV-AG-INDEX-OF-ARR-GE-0--THM
  (IMPLIES
   (AND (CDLLNODEARRP ARR)
        (INTEGERP INDEX) (<= 0 INDEX))
   (<= 0 (AG 'PREV (AG INDEX ARR))))
  :INSTRUCTIONS
  (:PROMOTE
   (:CASESPLIT (NULL ARR))
   :BASH
   (:CLAIM (< 0 (LEN ARR)))
   (:CASESPLIT (NOT (< INDEX (LEN ARR))))
   :BASH
   (:CLAIM (CDLLNODEP (AG INDEX ARR)))
   :BASH))

(DEFTHM CDLLP-AG-PREV-AG-INDEX-AG-NODEARR-GE-0--THM
  (IMPLIES
   (AND (CDLLP CDOBJ)
        (INTEGERP INDEX)
        (<= 0 INDEX))
   (<= 0 (AG 'PREV (AG INDEX (AG 'NODEARR CDOBJ)))))
  :INSTRUCTIONS
  (:PROMOTE
   (:CLAIM (CDLLNODEARRP (AG 'NODEARR CDOBJ)))
   (:CASESPLIT (NOT (< INDEX (CDLL_MAX_NODE1))))
   :BASH
   (:CLAIM (CDLLNODEP (AG INDEX (AG 'NODEARR CDOBJ))))
   :BASH))


(DEFTHM AG-PREV-AG-INDEX-OF-ARR-LT-CDLL_MAX_NODE1--THM
  (IMPLIES
   (AND (CDLLNODEARRP ARR)
        (INTEGERP INDEX) (<= 0 INDEX))
   (< (AG 'PREV (AG INDEX ARR)) (CDLL_MAX_NODE1)))
  :INSTRUCTIONS
  (:PROMOTE
   (:CASESPLIT (NULL ARR))
   :BASH   
   (:CLAIM (< 0 (LEN ARR)))
   (:CASESPLIT (NOT (< INDEX (LEN ARR))))
   :BASH
   (:CLAIM (CDLLNODEP (AG INDEX ARR)))
   :BASH))

(DEFTHM CDLLP-AG-PREV-AG-INDEX-AG-NODEARR-LT-CDLL_MAX_NODE1--THM
  (IMPLIES
   (AND (CDLLP CDOBJ)
        (INTEGERP INDEX)
        (<= 0 INDEX))
   (< (AG 'PREV (AG INDEX (AG 'NODEARR CDOBJ))) (CDLL_MAX_NODE1)))
  :INSTRUCTIONS
  (:PROMOTE
   (:CLAIM (CDLLNODEARRP (AG 'NODEARR CDOBJ)))
   (:CASESPLIT (NOT (< INDEX (CDLL_MAX_NODE1))))
   :BASH
   (:CLAIM (CDLLNODEP (AG INDEX (AG 'NODEARR CDOBJ))))
   :BASH))


(DEFTHM AG-ALLOC-AG-INDEX-OF-ARR-IS-INTEGERP--THM
  (IMPLIES
   (AND (CDLLNODEARRP ARR)
        (INTEGERP INDEX) (<= 0 INDEX))
   (INTEGERP (AG 'ALLOC (AG INDEX ARR))))
  :INSTRUCTIONS
  (:PROMOTE
   (:CASESPLIT (NULL ARR))
   :BASH   
   (:CASESPLIT (NOT (< INDEX (LEN ARR))))
   :BASH
   (:CLAIM (CDLLNODEP (AG INDEX ARR)))
   :BASH))

(DEFTHM CDLLP-AG-ALLOC-INTEGERP--THM
  (IMPLIES
   (AND (CDLLP CDOBJ)
        (INTEGERP INDEX) (<= 0 INDEX))
   (INTEGERP (AG 'ALLOC (AG INDEX (AG 'NODEARR CDOBJ)))))
  :INSTRUCTIONS
  (:PROMOTE
   (:CLAIM (CDLLNODEARRP (AG 'NODEARR CDOBJ)))
   (:CASESPLIT (NOT (< INDEX (CDLL_MAX_NODE1))))
   :BASH
   (:CLAIM (CDLLNODEP (AG INDEX (AG 'NODEARR CDOBJ))))
   :BASH))


(in-theory (enable cdll_find_free_node-loop-0 cdll_find_free_node cdll_ln cdll_cns cdll_cns1 cdll_add_node_at_index cdll_rst cdll_delete_node cdll_snc cdll_tsr cdll_hd cdll_tl cdll_remove cdll_restore cdll_nth cdll_nth_prev cdll_ins cdll_del))

(defthm find_free_node-loop-0-integerp--thm
  (implies (integerp i)
           (integerp (cdll_find_free_node-loop-0 i arr))))

(defthm find_free_node-loop-0-ge--thm
  (implies (integerp i)
           (>= (cdll_find_free_node-loop-0 i arr) i)))

(defthm find_free_node-loop-0-le--thm
  (implies
   (and (integerp i)
        (<= i (cdll_MAX_NODE1)))
   (<= (cdll_find_free_node-loop-0 i arr) (CDLL_MAX_NODE1))))

(defthm find_free_node-loop-0-bits--thm
  (implies
   (and (posp i)
        (<= i (CDLL_MAX_NODE1)))
   (not (= (bits (cdll_find_free_node-loop-0 i arr) (CDLL_MSB) 0) 0))))

(defthm find_free_node-loop-0-i-le-bits-elim--thm
  (implies
   (and (integerp i) (<= 0 i) (<= i (CDLL_MAX_NODE1)))
   (= (bits (cdll_find_free_node-loop-0 i arr) (CDLL_MSB) 0)
      (cdll_find_free_node-loop-0 i arr))))

(defthm find_free_node-loop-0-0-le-bits-elim--thm
  (= (bits (cdll_find_free_node-loop-0 0 arr) (CDLL_MSB) 0)
     (cdll_find_free_node-loop-0 0 arr))
  :hints (("Goal"
           :use (:instance find_free_node-loop-0-i-le-bits-elim--thm (i 0)))))

(defthm find_free_node-loop-0-i-lt-bits-elim--thm
  (implies
   (and (posp i)
        (< (cdll_find_free_node-loop-0 i arr) (CDLL_MAX_NODE1)))
   (= (bits (cdll_find_free_node-loop-0 i arr) (CDLL_MSB) 0)
      (cdll_find_free_node-loop-0 i arr))))

(defthm find_free_node-loop-0-0-lt-bits-elim--thm
  (implies (< (cdll_find_free_node-loop-0 0 arr) (CDLL_MAX_NODE1))
           (= (bits (cdll_find_free_node-loop-0 0 arr) (CDLL_MSB) 0)
              (cdll_find_free_node-loop-0 0 arr)))
  :hints (("Goal"
           :use (:instance find_free_node-loop-0-i-lt-bits-elim--thm (i 1)))))


(defthm find_free_node-loop-0-i-ne-tail--thm
  (implies
   (and (integerp i)
        ;; (cdllp CDObj)
        (< 0 ndcount)
        (good-nodep ndcount hd arr)
        (good-node-nextp ndcount hd arr)
        (good-node-prevp ndcount hd arr)
        (good-node-prev-nextp ndcount hd arr))
   (not (= (cdll_find_free_node-loop-0 i arr)
           (ag 'prev (ag hd arr))))))


(defthm find_free_node-loop-0-0-ne-tail--thm
  (implies
   (and ;; (cdllp CDObj) 
        (< 0 ndcount)
        (good-nodep ndcount hd arr)
        (good-node-nextp ndcount hd arr)
        (good-node-prevp ndcount hd arr)
        (good-node-prev-nextp ndcount hd arr))
   (not (= (cdll_find_free_node-loop-0 0 arr)
           (ag 'prev (ag hd arr)))))
  :hints (("Goal" :use (:instance find_free_node-loop-0-i-ne-tail--thm (i 0)))))


(defthm find_free_node-loop-0-works--thm
  (implies
   (and (integerp i) ;;  (<= 0 i)
        (< (cdll_find_free_node-loop-0 i arr) (CDLL_MAX_NODE1)))
   (= (ag 'alloc (ag (cdll_find_free_node-loop-0 i arr) arr)) 2)))


(defthm find_free_node-loop-0-as-nodeHd-irrelevant--thm
  (= (cdll_find_free_node-loop-0 x (ag 'nodeArr (as 'nodeHd y CDObj)))
     (cdll_find_free_node-loop-0 x (ag 'nodeArr CDObj))))


(defthm find_free_node-integerp--thm
  (integerp (cdll_find_free_node ndCount arr)))


(defthm find_free_node-ge-0--thm
  (<= 0 (cdll_find_free_node ndCount arr)))


(defthm find_free_node-le--thm
  (<= (cdll_find_free_node ndCount arr) (CDLL_MAX_NODE1))
  :hints (("Goal" :use (:instance find_free_node-loop-0-le--thm (i 0)))))


(defthm find_free_node-bits-elim--thm
  (implies
   (< (cdll_find_free_node ndCount arr) (CDLL_MAX_NODE1))
   (= (bits (cdll_find_free_node ndCount arr) (CDLL_MSB) 0)
      (cdll_find_free_node ndCount arr))))


(defthm find_free_node-works--thm
  (implies
   (< (CDLL_find_free_node ndCount arr) (CDLL_MAX_NODE1))
   (= (ag 'alloc (ag (cdll_find_free_node ndCount arr) arr)) 2)))


;; (defthm find_free_node-ag-alloc-ne-3--thm
;;   (implies
;;    (cdllp CDObj)
;;    (not (= (ag 'alloc
;;                (ag (cdll_find_free_node (ag 'nodeCount CDObj) (ag 'nodeArr CDObj))
;;                    (ag 'nodeArr CDObj)))
;;            3)))
;;   :hints
;;   (("Goal"
;;     :in-theory (e/d () (cdll_find_free_node))
;;     :cases ((< (cdll_find_free_node (ag 'nodeCount CDObj) (ag 'nodeArr CDObj)) (CDLL_MAX_NODE1))
;;             (not
;;              (< (cdll_find_free_node (ag 'nodeCount CDObj) (ag 'nodeArr CDObj)) (CDLL_MAX_NODE1)))))))

(defthm find_free_node-ag-alloc-ne-3--thm
  (implies
   (< (cdll_find_free_node ndcount arr) (CDLL_MAX_NODE1))
   (not (= (ag 'alloc (ag (cdll_find_free_node ndcount arr) arr)) 3)))
  :hints (("Goal" :in-theory (e/d () (cdll_find_free_node))))
  :rule-classes
  ((:forward-chaining
    :trigger-terms ((< (cdll_find_free_node ndcount arr) (CDLL_MAX_NODE1))))
   :rewrite))


(defthm alloc-3-not-eq-cdll_find_free_node--thm
  (implies
   (and (< (cdll_find_free_node ndCount arr) (CDLL_MAX_NODE1))
        (= (ag 'alloc (ag x arr)) 3))
   (not (= (cdll_find_free_node ndCount arr) x)))
  :hints (("Goal" :in-theory (e/d () (cdll_find_free_node)))))


(defthm find_free_node-ne-nodeHd--thm
  (implies
   (and ;; (cdllp CDObj)
        (= (ag 'alloc (ag (ag 'nodeHd CDObj) (ag 'nodeArr CDObj))) 3)
        (< (cdll_find_free_node (ag 'nodeCount CDObj) (ag 'nodeArr CDObj)) (CDLL_MAX_NODE1)))
   (not (= (cdll_find_free_node (ag 'nodeCount CDObj) (ag 'nodeArr CDObj)) (ag 'nodeHd CDObj))))
  :rule-classes
  ((:forward-chaining
    :trigger-terms ((= (ag 'alloc (ag (ag 'nodeHd CDObj) (ag 'nodeArr CDObj))) 3)))
   :rewrite))

(defthm find_free_node-ne-ag-next-nodeHd--thm
  (implies
   (and ;; (cdllp CDObj)
        (good-node-nextp ndcount hd arr)
        (< 0 ndcount)
        (< (cdll_find_free_node ndcount arr) (CDLL_MAX_NODE1)))
   (not (= (cdll_find_free_node ndcount arr)
           (ag 'next (ag hd arr)))))
  :hints (("Goal" :in-theory (e/d () (cdll_find_free_node)))))

(defthm find_free_node-ne-ag-prev-nodeHd--thm
  (implies
   (and ;; (cdllp CDObj)
        (good-node-prevp ndcount hd arr)
        (< 0 ndcount)
        (< (cdll_find_free_node ndcount arr) (CDLL_MAX_NODE1)))
   (not (= (cdll_find_free_node ndcount arr)
           (ag 'prev (ag hd arr)))))
  :hints (("Goal" :in-theory (e/d () (cdll_find_free_node)))))


(defthm find_free_node-ne-tail--thm
  (implies
   (and (good-nodep (ag 'nodeCount CDObj) (ag 'nodeHd CDObj) (ag 'nodeArr CDObj))
        (good-node-nextp (ag 'nodeCount CDObj) (ag 'nodeHd CDObj) (ag 'nodeArr CDObj))
        (good-node-prevp (ag 'nodeCount CDObj) (ag 'nodeHd CDObj) (ag 'nodeArr CDObj))
        (good-node-prev-nextp (ag 'nodeCount CDObj) (ag 'nodeHd CDObj) (ag 'nodeArr CDObj))
        (< 0 (ag 'nodeCount CDObj)))
   (not (= (cdll_find_free_node (ag 'nodeCount CDObj) (ag 'nodeArr CDObj))
           (ag 'prev (ag (ag 'nodeHd CDObj) (ag 'nodeArr CDObj))))))
  :hints (("Goal" :use (:instance find_free_node-loop-0-0-ne-tail--thm
                                   (ndcount (ag 'nodeCount CDObj))
                                   (hd (ag 'nodeHd CDObj))
                                   (arr (ag 'nodeArr CDObj))))))


(defthm find_free_node-as-nodeHd-irrelevant--thm
  (= (cdll_find_free_node (ag 'nodeCount CDObj) (ag 'nodeArr (as 'nodeHd y CDObj)))
     (cdll_find_free_node (ag 'nodeCount CDObj) (ag 'nodeArr CDObj))))


(in-theory (disable cdll_find_free_node-loop-0 cdll_find_free_node))


;; CDLL_nthNodeBy-loop-0 lemmas

(defthm nthNodeBy-loop-0-integerp--thm
  (implies
   (and (cdllnodeArrp arr) ;; (integerp i))
        (integerp index) (<= 0 index))
   (integerp (cdll_nthNodeBy-loop-0 i n edgenum arr index)))
  :hints (("Goal" :in-theory (e/d (cdll_nthNodeBy-loop-0) ()))
          ("Subgoal *1/2.2" :use (:instance ag-next-ag-index-of-arr-ge-0--thm))
          ("Subgoal *1/2.1" :use (:instance ag-prev-ag-index-of-arr-ge-0--thm))
          ("Subgoal *1/1.2" :use (:instance ag-next-ag-index-of-arr-is-integerp--thm))
          ("Subgoal *1/1.1" :use (:instance ag-prev-ag-index-of-arr-is-integerp--thm))))


(defthm nthNodeBy-loop-0-ge-0--thm
  (implies
   (and (cdllnodeArrp arr) ;;(integerp i) (integerp n)
        (integerp index) (<= 0 index))
   (<= 0 (cdll_nthNodeBy-loop-0 i n edgenum arr index)))
  :hints (("Goal" :in-theory (e/d (cdll_nthNodeBy-loop-0) ()))
          ("Subgoal *1/2.2" :use (:instance ag-next-ag-index-of-arr-ge-0--thm))
          ("Subgoal *1/2.1" :use (:instance ag-prev-ag-index-of-arr-ge-0--thm))
          ("Subgoal *1/1.2" :use (:instance ag-next-ag-index-of-arr-is-integerp--thm))
          ("Subgoal *1/1.1" :use (:instance ag-prev-ag-index-of-arr-is-integerp--thm))))


(defthm nthNodeBy-loop-0-le-CDLL_MAX_NODE1--thm
  (implies
   (and (cdllnodeArrp arr) ;; (integerp i) (integerp n)
        (integerp index) (<= 0 index) (<= index (CDLL_MAX_NODE1)))
   (<= (cdll_nthNodeBy-loop-0 i n edgenum arr index) (CDLL_MAX_NODE1)))
  :hints (("Goal" :in-theory (e/d (cdll_nthNodeBy-loop-0) ()))
          ("Subgoal *1/3.2" :use (:instance ag-next-ag-index-of-arr-lt-CDLL_MAX_NODE1--thm))
          ("subgoal *1/3.1" :use (:instance ag-prev-ag-index-of-arr-lt-CDLL_MAX_NODE1--thm))
          ("subgoal *1/2.2" :use (:instance ag-next-ag-index-of-arr-ge-0--thm))
          ("subgoal *1/2.1" :use (:instance ag-prev-ag-index-of-arr-ge-0--thm))
          ("subgoal *1/1.2" :use (:instance ag-next-ag-index-of-arr-is-integerp--thm))
          ("subgoal *1/1.1" :use (:instance ag-prev-ag-index-of-arr-is-integerp--thm))))

;; ????
(defthm nthNodeBy-loop-0-alloc-at-index-ne-3-eq-CDLL_MAX_NODE1--thm
  (implies
   (and (integerp i) (< 0 i)
        (integerp index) (<= 0 index) (<= index (CDLL_MAX_NODE1))
        (not (= (ag 'alloc (ag index arr)) 3)))
   (= (cdll_nthNodeBy-loop-0 i n edgenum arr index) (CDLL_MAX_NODE1)))
  :hints (("Goal" :in-theory (e/d (cdll_nthNodeBy-loop-0) ()))))

;; Accumulated Persistence
(defthmd nthNodeBy-loop-0-lt-CDLL_MAX_NODE1-alloc-at-index-eq-3--thm
  (implies
   (and (integerp i) (< 0 i)
        (integerp index) (<= 0 index) (<= index (CDLL_MAX_NODE1))
        (< (cdll_nthNodeBy-loop-0 i n edgenum arr index) (CDLL_MAX_NODE1)))
   (= (ag 'alloc (ag index arr)) 3))
  :hints (("Goal" :in-theory (e/d (cdll_nthNodeBy-loop-0) ()))))


(defthmd nthnodeby-loop-0-arg-2-irrelevant--thm
  (= (cdll_nthnodeby-loop-0 i n edgenum arr index) (cdll_nthnodeby-loop-0 i m edgenum arr index))
  :hints (("Goal" :in-theory (e/d (cdll_nthNodeBy-loop-0) ()))))

(defthmd nthnodeby-loop-0-nodecount-update-irrelevant--thm
  (= (cdll_nthnodeby-loop-0 i n edgenum (ag 'nodeArr (as 'nodeCount x CDObj)) index)
     (cdll_nthnodeby-loop-0 i n edgenum (ag 'nodeArr CDObj) index))
  :hints (("Goal" :in-theory (e/d (cdll_nthNodeBy-loop-0) ()))))


(defthmd nthNodeBy-loop-0-next-opener--thm
  (implies
   (and (integerp i) (< 0 i)
        ;; (integerp index)
        (< index (CDLL_MAX_NODE1))
        (= (AG 'ALLOC (AG INDEX ARR)) 3))
   (= (cdll_nthNodeBy-loop-0 i n 0 arr index)
      (cdll_nthnodeby-loop-0 (1- i) n 0 arr (ag 'next (ag index arr)))))
  :hints (("Goal" :in-theory (e/d (cdll_nthNodeBy-loop-0) ()))))


(DEFTHMD NTHNODEBY-LOOP-0-NEXT-OPENER-FRONT-AUX-1--THM
  (IMPLIES
   (AND (CDLLNODEARRP ARR)
        (INTEGERP I)
        (< 0 I)
        (INTEGERP INDEX)
        (<= 0 INDEX)
        (< INDEX (CDLL_MAX_NODE1))
        (NOT (EQUAL (AG 'ALLOC (AG INDEX ARR)) 3))
        (< (CDLL_NTHNODEBY-LOOP-0 (+ -1 I) N 0 ARR INDEX) (CDLL_MAX_NODE1))
        (EQUAL 3 (AG 'ALLOC (AG (CDLL_NTHNODEBY-LOOP-0 (+ -1 I) N 0 ARR INDEX) ARR))))
   (EQUAL (AG 'NEXT (AG (CDLL_NTHNODEBY-LOOP-0 (+ -1 I) N 0 ARR INDEX) ARR))
          (CDLL_MAX_NODE1)))
  :INSTRUCTIONS
  (:PROMOTE
       (:CASESPLIT (< 1 I))
       (:CONTRAPOSE 8)
       (:DIVE 1 1)
       (:CLAIM (< 0 (+ -1 I)))
       (:CLAIM (<= INDEX (CDLL_MAX_NODE1)))
       (:REWRITE NTHNODEBY-LOOP-0-ALLOC-AT-INDEX-NE-3-EQ-CDLL_MAX_NODE1--THM)
       :TOP :BASH (:CLAIM (= I 1))
       (:CONTRAPOSE 9)
       (:DIVE 1 2 2 1)
       (:REWRITE CDLL_NTHNODEBY-LOOP-0)
       :S :TOP :BASH))


(defthmd nthNodeBy-loop-0-next-opener-front--thm
  (implies
   (and (cdllnodeArrp arr)
        (integerp i) (< 0 i)
        (integerp index) (<= 0 index) (< index (CDLL_MAX_NODE1))
        (< (cdll_nthNodeBy-loop-0 (1- i) n 0 arr index) (CDLL_MAX_NODE1))
        (= (ag 'alloc (ag (cdll_nthNodeBy-loop-0 (1- i) n 0 arr index) arr)) 3))
   (= (cdll_nthNodeBy-loop-0 i n 0 arr index)
      (ag 'next (ag (cdll_nthNodeBy-loop-0 (1- i) n 0 arr index) arr))))
  :hints (("Goal" :in-theory (e/d (cdll_nthNodeBy-loop-0) ()))
          ("Subgoal *1/5.3" :use (:instance nthNodeBy-loop-0-next-opener-front-aux-1--thm))
          ("Subgoal *1/5.2" :use (:instance ag-next-ag-index-of-arr-lt-CDLL_MAX_NODE1--thm))
          ("Subgoal *1/5.1" :use (:instance ag-next-ag-index-of-arr-lt-CDLL_MAX_NODE1--thm))))

 
(defthmd nthNodeBy-loop-0-prev-opener--thm
  (implies
   (and (integerp i) (< 0 i) (not (= edgenum 0))
        ;; (integerp index)
        (< index (CDLL_MAX_NODE1))
        (= (AG 'ALLOC (AG INDEX arr)) 3))
   (= (cdll_nthNodeBy-loop-0 i n edgenum arr index)
      (cdll_nthnodeby-loop-0 (1- i) n edgenum arr (ag 'prev (ag index arr)))))
  :hints (("Goal" :in-theory (e/d (cdll_nthNodeBy-loop-0) ()))))


(DEFTHMD NTHNODEBY-LOOP-0-PREV-OPENER-FRONT-AUX-1--THM
  (IMPLIES
   (AND (CDLLNODEARRP ARR)
        (INTEGERP I)
        (< 0 I)
        (INTEGERP INDEX)
        (<= 0 INDEX)
        (< INDEX (CDLL_MAX_NODE1))
        (NOT (= EDGENUM 0))
        (NOT (EQUAL (AG 'ALLOC (AG INDEX ARR)) 3))
        (< (CDLL_NTHNODEBY-LOOP-0 (+ -1 I) N EDGENUM ARR INDEX) (CDLL_MAX_NODE1))
        (EQUAL 3 (AG 'ALLOC (AG (CDLL_NTHNODEBY-LOOP-0 (+ -1 I) N EDGENUM ARR INDEX) ARR))))
   (EQUAL (AG 'PREV (AG (CDLL_NTHNODEBY-LOOP-0 (+ -1 I) N EDGENUM ARR INDEX) ARR))
          (CDLL_MAX_NODE1)))
  :INSTRUCTIONS
  (:PROMOTE
       (:CASESPLIT (< 1 I))
       (:CONTRAPOSE 9)
       (:DIVE 1 1)
       (:CLAIM (< 0 (+ -1 I)))
       (:CLAIM (<= INDEX (CDLL_MAX_NODE1)))
       (:REWRITE NTHNODEBY-LOOP-0-ALLOC-AT-INDEX-NE-3-EQ-CDLL_MAX_NODE1--THM)
       :TOP :BASH (:CLAIM (= I 1))
       (:CONTRAPOSE 10)
       (:DIVE 1 2 2 1)
       (:REWRITE CDLL_NTHNODEBY-LOOP-0)
       :S :TOP :BASH))


(defthmd nthNodeBy-loop-0-prev-opener-front--thm
  (implies
   (and (cdllnodeArrp arr)
        (integerp i) (< 0 i)
        (integerp index) (<= 0 index) (< index (CDLL_MAX_NODE1))
        (not (= edgenum 0))
        (< (cdll_nthNodeBy-loop-0 (1- i) n edgenum arr index) (CDLL_MAX_NODE1))
        (= (ag 'alloc (ag (cdll_nthNodeBy-loop-0 (1- i) n edgenum arr index) arr)) 3))
   (= (cdll_nthNodeBy-loop-0 i n edgenum arr index)
      (ag 'prev (ag (cdll_nthnodeby-loop-0 (1- i) n edgenum arr index) arr))))
  :hints (("Goal" :in-theory (e/d (cdll_nthNodeBy-loop-0) ()))
          ("Subgoal *1/5.3" :use (:instance nthNodeBy-loop-0-prev-opener-front-aux-1--thm))
          ("Subgoal *1/5.2" :use (:instance ag-prev-ag-index-of-arr-lt-CDLL_MAX_NODE1--thm))
          ("Subgoal *1/5.1" :use (:instance ag-prev-ag-index-of-arr-lt-CDLL_MAX_NODE1--thm))))


(defthm nthnodeby-loop-0-0-opener--thm
  (= (CDLL_nthNodeBy-loop-0 0 n edgenum arr index)
     index)
  :hints (("Goal" :in-theory (e/d (CDLL_nthNodeBy-loop-0) ()))))


;; CDLL_nthNodeBy lemmas

(DEFTHM NTHNODEBY-INTEGERP--THM
  (IMPLIES
   (AND (CDLLNODEARRP ARR)
        (INTEGERP INDEX)
        (<= 0 INDEX))
   (INTEGERP (CDLL_NTHNODEBY N EDGENUM INDEX ARR)))
  :INSTRUCTIONS
  (:PROMOTE
   (:DIVE 1)
   (:REWRITE CDLL_NTHNODEBY)
   :S :S
   (:CLAIM (INTEGERP (CDLL_NTHNODEBY-LOOP-0 N N EDGENUM ARR INDEX)))
   :S
   (:CASESPLIT (NOT (< (CDLL_NTHNODEBY-LOOP-0 N N EDGENUM ARR INDEX) (CDLL_MAX_NODE1))))
   (:= (CDLL_MAX_NODE1))
   :TOP :S :TOP (:CONTRAPOSE 5)
   (:DIVE 1 2)
   :S))


(defthm nthNodeBy-ge-0--thm
  (implies
   (and (cdllnodeArrp arr)
        (integerp index) (<= 0 index))
   (<= 0 (CDLL_nthNodeBy n edgenum index arr)))
  :hints (("Goal" :in-theory (e/d (CDLL_nthNodeBy) ()))))


(defthm nthNodeBy-le-CDLL_MAX_NODE1--thm
  (<= (CDLL_nthNodeBy n edgenum index arr) (CDLL_MAX_NODE1))
  :hints (("Goal" :in-theory (e/d (CDLL_nthNodeBy) ()))
          ("Goal''" :use (:instance nthNodeBy-loop-0-le-CDLL_MAX_NODE1--thm (i n)))))


(defthm nthNodeBy-lt-CDLL_MAX_NODE1-index-lt-CDLL_MAX_NODE1--thm
  (implies
   (< (CDLL_nthNodeBy n edgenum index arr) (CDLL_MAX_NODE1))
   (< index (CDLL_MAX_NODE1)))
  :hints (("Goal" :in-theory (e/d (CDLL_nthNodeBy CDLL_nthNodeBy-loop-0) ()))))

;; AP???<<<
(defthm nthNodeBy-lt-CDLL_MAX_NODE1-ag-alloc-index-eq-3--thm
  (implies
   (AND (cdllnodeArrp arr)
        (integerp index)
        (<= 0 index)
        (< (cdll_nthNodeBy n edgenum index arr) (CDLL_MAX_NODE1)))
   (= (AG 'ALLOC (AG INDEX arr)) 3))
  :hints (("Goal" :in-theory (e/d (CDLL_nthNodeBy CDLL_nthNodeBy-loop-0) ()))))


(defthm nthNodeBy-lt-CDLL_MAX_NODE1-ag-alloc-eq-3--thm
  (implies (< (cdll_nthNodeBy n edgenum index arr) (CDLL_MAX_NODE1))
           (= (ag 'alloc (ag (cdll_nthNodeBy n edgenum index arr) arr)) 3))
  :hints (("Goal" :in-theory (e/d (CDLL_nthNodeBy) ()))))


(defthmd nthNodeBy-lt-CDLL_MAX_NODE1-eq-CDLL_nthNodeBy-loop-0--thm
  (implies
   (and ;; (cdllnodeArrp arr) ;; (integerp i)
        ;; (integerp index) ;; (<= 0 index) (< index (CDLL_MAX_NODE1))
        (< (cdll_nthNodeBy i edgenum index arr) (CDLL_MAX_NODE1)))
   (= (cdll_nthNodeBy i edgenum index arr)
      (cdll_nthNodeBy-loop-0 i i edgenum arr index)))
  :hints (("Goal" :in-theory (e/d (cdll_nthNodeBy) ()))))


(defthmd nthnodeby-loop-0-j-lt-CDLL_MAX_NODE1-means-nthnodeby-loop-0-lt-j-lt-CDLL_MAX_NODE1--thm
  (implies
   (and (cdllnodeArrp arr)
        (integerp j)
        (integerp i) (<= 0 i) (< i j)
        ;; (integerp index) (<= 0 index) (< index (CDLL_MAX_NODE1))
        (< (cdll_nthNodeBy-loop-0 j n edgenum arr index) (CDLL_MAX_NODE1)))
   (< (cdll_nthNodeBy-loop-0 i n edgenum arr index) (CDLL_MAX_NODE1)))
  :hints (("Goal" :in-theory (e/d (cdll_nthNodeBy-loop-0) ()))))


(defthmd nthnodeby-loop-0-j-alloc-eq-3-means-nthnodeby-loop-0-lt-j-alloc-eq-3--thm
  (implies
   (and (cdllnodeArrp arr)
        (integerp j)
        (integerp i) (<= 0 i) (< i j)
        ;; (integerp index) (<= 0 index) (< index (CDLL_MAX_NODE1))
        (< (cdll_nthNodeBy-loop-0 j n edgenum arr index) (CDLL_MAX_NODE1))
        (= (ag 'alloc (ag (cdll_nthNodeBy-loop-0 j n edgenum arr index) arr)) 3))
   (= (ag 'alloc (ag (cdll_nthNodeBy-loop-0 i n edgenum arr index) arr)) 3))
  :hints (("Goal" :in-theory (e/d (cdll_nthNodeBy-loop-0) ()))))


(DEFTHMD NTHNODEBY-J-NO-ERR-MEANS-NTHNODEBY-LT-J-NO-ERR-AUX-1--THM
  (IMPLIES
   (AND (CDLLNODEARRP ARR)
        (INTEGERP J)
        (INTEGERP I)
        (<= 0 I)
        (< I J)
        ;; (INTEGERP INDEX)
        ;; (<= 0 INDEX)
        ;; (< INDEX (CDLL_MAX_NODE1))
        (< (CDLL_NTHNODEBY-LOOP-0 J J EDGENUM ARR INDEX) (CDLL_MAX_NODE1))
        (EQUAL (AG 'ALLOC (AG (CDLL_NTHNODEBY-LOOP-0 J J EDGENUM ARR INDEX) ARR)) 3))
   (< (CDLL_NTHNODEBY-LOOP-0 I I EDGENUM ARR INDEX) (CDLL_MAX_NODE1)))
  :INSTRUCTIONS
  (:PROMOTE
   (:CLAIM (< (CDLL_NTHNODEBY-LOOP-0 J N EDGENUM ARR INDEX) (CDLL_MAX_NODE1))
           :HINTS (("Goal" :USE (:INSTANCE NTHNODEBY-LOOP-0-ARG-2-IRRELEVANT--THM
                                           (I J) (N J) (M N)))))
   (:CLAIM (< (CDLL_NTHNODEBY-LOOP-0 I N EDGENUM ARR INDEX) (CDLL_MAX_NODE1))
     :HINTS (("Goal" :USE (:INSTANCE
       NTHNODEBY-LOOP-0-J-LT-CDLL_MAX_NODE1-MEANS-NTHNODEBY-LOOP-0-LT-J-LT-CDLL_MAX_NODE1--THM))))
   (:PROVE :HINTS (("Goal" :USE (:INSTANCE NTHNODEBY-LOOP-0-ARG-2-IRRELEVANT--THM (M I)))))))

(DEFTHMD NTHNODEBY-J-NO-ERR-MEANS-NTHNODEBY-LT-J-NO-ERR-AUX-2--THM
  (IMPLIES
   (AND (CDLLNODEARRP ARR)
        (INTEGERP J)
        (INTEGERP I)
        (<= 0 I)
        (< I J)
        ;; (INTEGERP INDEX)
        ;; (<= 0 INDEX)
        ;; (< INDEX (CDLL_MAX_NODE1))
        (< (CDLL_NTHNODEBY-LOOP-0 J J EDGENUM ARR INDEX) (CDLL_MAX_NODE1))
        (EQUAL (AG 'ALLOC (AG (CDLL_NTHNODEBY-LOOP-0 J J EDGENUM ARR INDEX) ARR)) 3)
        (< (CDLL_NTHNODEBY-LOOP-0 J J EDGENUM ARR INDEX) (CDLL_MAX_NODE1)))
   (EQUAL (AG 'ALLOC (AG (CDLL_NTHNODEBY-LOOP-0 I I EDGENUM ARR INDEX) ARR)) 3))
 :INSTRUCTIONS
 (:PROMOTE
  (:CLAIM (EQUAL (AG 'ALLOC (AG (CDLL_NTHNODEBY-LOOP-0 J N EDGENUM ARR INDEX) ARR)) 3)
          :HINTS (("Goal" :USE (:INSTANCE NTHNODEBY-LOOP-0-ARG-2-IRRELEVANT--THM (I J) (N J) (M N)))))
  (:CLAIM (< (CDLL_NTHNODEBY-LOOP-0 J N EDGENUM ARR INDEX) (CDLL_MAX_NODE1))
          :HINTS (("Goal" :USE (:INSTANCE NTHNODEBY-LOOP-0-ARG-2-IRRELEVANT--THM (I J) (N J) (M N)))))
  (:CLAIM (= (AG 'ALLOC (AG (CDLL_NTHNODEBY-LOOP-0 I N EDGENUM ARR INDEX) ARR)) 3)
          :HINTS (("Goal" :USE
                   (:INSTANCE NTHNODEBY-LOOP-0-J-ALLOC-EQ-3-MEANS-NTHNODEBY-LOOP-0-LT-J-ALLOC-EQ-3--THM))))
  (:PROVE :HINTS (("Goal" :USE (:INSTANCE NTHNODEBY-LOOP-0-ARG-2-IRRELEVANT--THM (M I)))))))

(defthmd nthnodeby-j-no-err-means-nthnodeby-lt-j-no-err--thm
  (implies
   (and (cdllnodeArrp arr)
        (integerp j)
        (integerp i) (<= 0 i) (< i j)
        (integerp index) (<= 0 index) ;; (< index (CDLL_MAX_NODE1))
        (< (cdll_nthNodeBy j edgenum index arr) (CDLL_MAX_NODE1)))
   (< (cdll_nthNodeBy i edgenum index arr) (CDLL_MAX_NODE1)))
  :hints (("Goal" :in-theory (e/d (cdll_nthNodeBy) ()))
          ("Subgoal 2" :use (:instance nthnodeby-j-no-err-means-nthnodeby-lt-j-no-err-aux-1--thm))
          ("Subgoal 1" :use (:instance nthnodeby-j-no-err-means-nthnodeby-lt-j-no-err-aux-2--thm))))


(DEFTHMD NTHNODEBY-NEXT-OPENER-AUX-1--THM
  (IMPLIES
   (AND (INTEGERP N) (< 0 N)
        (INTEGERP INDEX) (< INDEX (CDLL_MAX_NODE1))
        (EQUAL (AG 'ALLOC (AG INDEX arr)) 3))
   (EQUAL (CDLL_NTHNODEBY-LOOP-0 N N 0 arr INDEX)
          (CDLL_NTHNODEBY-LOOP-0 (+ -1 N) (+ -1 N) 0 arr (AG 'NEXT (AG INDEX arr)))))
  :INSTRUCTIONS
  (:PROMOTE
   (:DIVE 2)
   (:REWRITE NTHNODEBY-LOOP-0-ARG-2-IRRELEVANT--THM ((M N)))
   :TOP (:DIVE 1)
   (:REWRITE NTHNODEBY-LOOP-0-NEXT-OPENER--THM)
   :TOP :BASH))

(defthmd nthNodeBy-next-opener--thm
  (implies
   (and (integerp n) (< 0 n)
        (integerp index) (< index (CDLL_MAX_NODE1))
        (= (ag 'alloc (ag index arr)) 3))
   (= (cdll_nthNodeBy n 0 index arr)
      (cdll_nthNodeBy (1- n) 0 (ag 'next (ag index arr)) arr)))
  :hints (("Goal" :in-theory (e/d (cdll_nthNodeBy) ()))
          ("Goal'" :use (:instance nthnodeby-next-opener-aux-1--thm))))


(defthm nthNodeBy-lt-CDLL_MAX_NODE1-alloc-eq-3--thm
  (implies (< (cdll_nthNodeBy n edgenum index arr) (CDLL_MAX_NODE1))
           (= (ag 'alloc (ag (cdll_nthNodeBy n edgenum index arr) arr)) 3))
  :hints (("Goal" :in-theory (e/d (cdll_nthNodeBy) ()))))

;; ?????
(defthm nthNodeBy-alloc-at-index-ne-3-eq-CDLL_MAX_NODE1--thm
  (implies
   (and (integerp i) (<= 0 i)
        (integerp index) (<= 0 index) (<= index (CDLL_MAX_NODE1))
        (not (= (ag 'alloc (ag index arr)) 3)))
   (= (cdll_nthNodeBy i edgenum index arr) (CDLL_MAX_NODE1)))
  :hints (("Goal" :in-theory (e/d (cdll_nthNodeBy) ())
                  :cases ((< 0 i) (= 0 i)))))

(defthm alloc-at-index-ne-3-not-eq-nthNodeBy--thm
   (implies
    (and ;; (integerp x) (<= 0 x)
         (< x (CDLL_MAX_NODE1))
         (not (= (ag 'alloc (ag x arr)) 3)))
    (not (equal (cdll_nthNodeBy i edgenum index arr) x)))
   :hints (("Goal" :in-theory (e/d (nthNodeBy-lt-CDLL_MAX_NODE1-alloc-eq-3--thm) ()))))


(defthm nthnodeBy-err--thm
  (implies (= (logand1 (log< (cdll_nthnodeby-loop-0 n n edgenum arr index) (CDLL_MAX_NODE1))
                       (log= (ag 'alloc (ag (cdll_nthnodeby-loop-0 n n edgenum arr index) arr)) 3))
              0)
           (= (cdll_nthnodeBy n edgenum index arr)
              (CDLL_MAX_NODE1)))
  :hints (("Goal" :in-theory (e/d (cdll_nthnodeBy) ()))))


(defthmd nthnodeBy-no-err--thm
  (implies
   (not (= (logand1 (log< (cdll_nthnodeBy-loop-0 n n edgenum arr index) (CDLL_MAX_NODE1))
                    (log= (ag 'alloc (ag (cdll_nthnodeBy-loop-0 n n edgenum arr index) arr)) 3)) 0))
   (= (cdll_nthnodeBy n edgenum index arr)
      (cdll_nthnodeBy-loop-0 n n edgenum arr index)))
  :hints (("Goal" :in-theory (e/d (cdll_nthnodeBy) ()))))

(defthm nthnodeBy-no-err-means-cdll_nthnodeby-lt-CDLL_MAX_NODE1--thm
  (implies
   (not (= (logand1 (log< (cdll_nthnodeBy-loop-0 n n edgenum arr index) (CDLL_MAX_NODE1))
        (log= (ag 'alloc (ag (cdll_nthnodeBy-loop-0 n n edgenum arr index) arr)) 3)) 0))
   (< (cdll_nthnodeBy n edgenum index arr)
      (CDLL_MAX_NODE1)))
  :hints (("Goal" :in-theory (e/d (cdll_nthnodeBy) ()))))


(DEFTHMD NTHNODEBY-NEXT-OPENER-FRONT-AUX-1--THM
  (IMPLIES
   (AND (CDLLNODEARRP ARR)
        (INTEGERP I)
        (< 1 I)
        (INTEGERP INDEX)
        (<= 0 INDEX)
        (< INDEX (CDLL_MAX_NODE1))
        (< (CDLL_NTHNODEBY (+ -1 I) 0 INDEX ARR) (CDLL_MAX_NODE1))
        (< (AG 'NEXT (AG (CDLL_NTHNODEBY (+ -1 I) 0 INDEX ARR) ARR)) (CDLL_MAX_NODE1))
        (EQUAL (AG 'ALLOC (AG (AG 'NEXT (AG (CDLL_NTHNODEBY (+ -1 I) 0 INDEX ARR) ARR)) ARR))
               3))
   (EQUAL (CDLL_NTHNODEBY I 0 INDEX ARR)
          (AG 'NEXT (AG (CDLL_NTHNODEBY (+ -1 I) 0 INDEX ARR) ARR))))
 :INSTRUCTIONS
 (:PROMOTE
  (:DIVE 1)
  (:CLAIM
   (= (AG 'ALLOC (AG INDEX ARR)) 3)
   :HINTS (("Goal" :USE (:INSTANCE NTHNODEBY-LT-CDLL_MAX_NODE1-AG-ALLOC-INDEX-EQ-3--THM
                                    (N (+ -1 I))
                                    (EDGENUM 0)))))
  (:CLAIM (NOT (EQUAL (LOGAND1 (LOG< INDEX (CDLL_MAX_NODE1)) (LOG= (AG 'ALLOC (AG INDEX ARR)) 3)) 0)))
  (:REWRITE CDLL_NTHNODEBY)
  :TOP
  (:= (EQUAL (CDLL_NTHNODEBY-LOOP-0 I I 0 ARR INDEX)
             (AG 'NEXT (AG (CDLL_NTHNODEBY (+ -1 I) 0 INDEX ARR) ARR))))
  (:DIVE 2 2 1)
  (:REWRITE NTHNODEBY-LT-CDLL_MAX_NODE1-EQ-CDLL_NTHNODEBY-LOOP-0--THM)
  :TOP
  (:CLAIM (< (CDLL_NTHNODEBY (+ -1 I) 0 INDEX ARR) (CDLL_MAX_NODE1)))
  (:CONTRAPOSE 12)
  (:DIVE 1 1)
  (:REWRITE NTHNODEBY-LT-CDLL_MAX_NODE1-EQ-CDLL_NTHNODEBY-LOOP-0--THM)
  :TOP (:CONTRAPOSE 12)
  (:CLAIM (= (AG 'ALLOC (AG (CDLL_NTHNODEBY (+ -1 I) 0 INDEX ARR) ARR)) 3)
          :HINTS (("Goal" :USE (:INSTANCE NTHNODEBY-LT-CDLL_MAX_NODE1-ALLOC-EQ-3--THM
                                           (N (+ -1 I))
                                           (EDGENUM 0)))))
  (:CONTRAPOSE 13)
  (:DIVE 1 1 2 1)
  (:REWRITE NTHNODEBY-LT-CDLL_MAX_NODE1-EQ-CDLL_NTHNODEBY-LOOP-0--THM)
  :TOP (:CONTRAPOSE 13)
  (:DIVE 1)
  (:REWRITE NTHNODEBY-LOOP-0-ARG-2-IRRELEVANT--THM ((M (+ -1 I))))
  (:REWRITE NTHNODEBY-LOOP-0-NEXT-OPENER-FRONT--THM)
  :TOP :BASH))

(defthmd nthNodeBy-next-opener-front--thm
  (implies
   (and (cdllnodeArrp arr)
        (integerp i) (< 0 i)
        (integerp index) (<= 0 index) (< index (CDLL_MAX_NODE1))
        (< (cdll_nthnodeby (+ -1 i) 0 index arr) (CDLL_MAX_NODE1))
        (< (ag 'next (ag (cdll_nthnodeby (+ -1 i) 0 index arr) arr)) (cdll_max_node1))
        (equal (ag 'alloc (ag (ag 'next (ag (cdll_nthnodeby (+ -1 i) 0 index arr) arr)) arr))
               3))
   (= (cdll_nthNodeby i 0 index arr)
      (ag 'next (ag (cdll_nthNodeBy (1- i) 0 index arr) arr))))
  :hints (("Goal" :cases ((= 1 i) (< 1 i)))
          ("Subgoal 2" :in-theory (e/d (cdll_nthNodeBy cdll_nthNodeBy-loop-0) ()))
          ("Subgoal 1" :use (:instance nthNodeBy-next-opener-front-aux-1--thm))))


(DEFTHMD NTHNODEBY-PREV-OPENER-FRONT-AUX-1--THM
  (IMPLIES
   (AND (CDLLNODEARRP ARR)
        (INTEGERP I)
        (< 1 I)
        (INTEGERP INDEX)
        (<= 0 INDEX)
        (< INDEX (CDLL_MAX_NODE1))
        (NOT (EQUAL EDGENUM 0))
        (< (CDLL_NTHNODEBY (+ -1 I) EDGENUM INDEX ARR) (CDLL_MAX_NODE1))
        (< (AG 'PREV (AG (CDLL_NTHNODEBY (+ -1 I) EDGENUM INDEX ARR) ARR)) (CDLL_MAX_NODE1))
        (EQUAL (AG 'ALLOC (AG (AG 'PREV (AG (CDLL_NTHNODEBY (+ -1 I) EDGENUM INDEX ARR) ARR)) ARR))
               3))
   (EQUAL (CDLL_NTHNODEBY I EDGENUM INDEX ARR)
          (AG 'PREV (AG (CDLL_NTHNODEBY (+ -1 I) EDGENUM INDEX ARR) ARR))))
 :INSTRUCTIONS
 (:PROMOTE
  (:DIVE 1)
  (:CLAIM
   (= (AG 'ALLOC (AG INDEX ARR)) 3)
   :HINTS (("Goal" :USE (:INSTANCE NTHNODEBY-LT-CDLL_MAX_NODE1-AG-ALLOC-INDEX-EQ-3--THM
                                    (N (+ -1 I))))))
  (:CLAIM (NOT (EQUAL (LOGAND1 (LOG< INDEX (CDLL_MAX_NODE1)) (LOG= (AG 'ALLOC (AG INDEX ARR)) 3)) 0)))
  (:REWRITE CDLL_NTHNODEBY)
  :TOP
  (:= (EQUAL (CDLL_NTHNODEBY-LOOP-0 I I EDGENUM ARR INDEX)
             (AG 'PREV (AG (CDLL_NTHNODEBY (+ -1 I) EDGENUM INDEX ARR) ARR))))
  (:DIVE 2 2 1)
  (:REWRITE NTHNODEBY-LT-CDLL_MAX_NODE1-EQ-CDLL_NTHNODEBY-LOOP-0--THM)
  :TOP
  (:CLAIM (< (CDLL_NTHNODEBY (+ -1 I) EDGENUM INDEX ARR) (CDLL_MAX_NODE1)))
  (:CONTRAPOSE 13)
  (:DIVE 1 1)
  (:REWRITE NTHNODEBY-LT-CDLL_MAX_NODE1-EQ-CDLL_NTHNODEBY-LOOP-0--THM)
  :TOP (:CONTRAPOSE 13)
  (:CLAIM (= (AG 'ALLOC (AG (CDLL_NTHNODEBY (+ -1 I) EDGENUM INDEX ARR) ARR))
             3)
          :HINTS (("Goal" :USE (:INSTANCE NTHNODEBY-LT-CDLL_MAX_NODE1-ALLOC-EQ-3--THM
                                           (N (+ -1 I))))))
  (:CONTRAPOSE 14)
  (:DIVE 1 1 2 1)
  (:REWRITE NTHNODEBY-LT-CDLL_MAX_NODE1-EQ-CDLL_NTHNODEBY-LOOP-0--THM)
  :TOP (:CONTRAPOSE 14)
  (:DIVE 1)
  (:REWRITE NTHNODEBY-LOOP-0-ARG-2-IRRELEVANT--THM ((M (+ -1 I))))
  (:REWRITE NTHNODEBY-LOOP-0-PREV-OPENER-FRONT--THM)
  :TOP :BASH))

(defthmd nthNodeBy-prev-opener-front--thm
  (implies
   (and (cdllnodeArrp arr)
        (integerp i) (< 0 i)
        (integerp index) (<= 0 index) (< index (CDLL_MAX_NODE1))
        (not (= edgenum 0))
        (< (cdll_nthNodeBy (+ -1 i) edgenum index arr) (CDLL_MAX_NODE1))
        (< (ag 'prev (ag (cdll_nthNodeBy (+ -1 i) edgenum index arr) arr)) (CDLL_MAX_NODE1))
        (equal (ag 'alloc (ag (ag 'prev (ag (cdll_nthNodeBy (+ -1 i) edgenum index arr) arr)) arr))
               3))
   (= (cdll_nthNodeBy i edgenum index arr)
      (ag 'prev (ag (cdll_nthNodeBy (1- i) edgenum index arr) arr))))
  :hints (("Goal"  :cases ((= 1 i) (< 1 i)))
          ("Subgoal 2" :in-theory (e/d (cdll_nthNodeBy cdll_nthNodeBy-loop-0) ()))
          ("Subgoal 1" :use (:instance nthNodeBy-prev-opener-front-aux-1--thm))))


(defthm nthNodeBy-loop-0-as-nodeCount-irrelevant--thm
  (= (cdll_nthNodeBy-loop-0 i n edgenum (ag 'nodeArr (as 'nodeCount c CDObj)) index)
     (cdll_nthNodeBy-loop-0 i n edgenum (ag 'nodeArr CDObj) index))
  :hints (("Goal" :in-theory (e/d (cdll_nthNodeBy-loop-0) ()))))

(defthm nthNodeBy-as-nodeCount-irrelevant--thm
  (= (cdll_nthNodeBy i edgenum index (ag 'nodeArr (as 'nodecount c CDObj)))
     (cdll_nthNodeBy i edgenum index (ag 'nodeArr CDObj)))
  :hints (("Goal" :in-theory (e/d (cdll_nthNodeBy) ()))))


(defthm nthNodeBy-loop-0-as-nodeHd-irrelevant--thm
  (= (cdll_nthNodeBy-loop-0 i n edgenum (ag 'nodeArr (as 'nodeHd h CDObj)) index)
     (cdll_nthNodeBy-loop-0 i n edgenum (ag 'nodeArr CDObj) index))
  :hints (("Goal" :in-theory (e/d (cdll_nthNodeBy-loop-0) ()))))

(defthm nthNodeBy-as-nodeHd-irrelevant--thm
  (= (cdll_nthNodeBy i edgenum index (ag 'nodeArr (as 'nodeHd h CDObj)))
     (cdll_nthNodeBy i edgenum index (ag 'nodeArr CDObj)))
  :hints (("Goal" :in-theory (e/d (cdll_nthNodeBy) ()))))


(DEFTHMD NTHNODEBY-LOOP-0-AS-VAL-IRRELEVANT-AUX-1--THM
  (IMPLIES
   (AND (INTEGERP I)
        (< 0 I)
        (< INDEX (CDLL_MAX_NODE1))
        (NOT (EQUAL (AG 'ALLOC (AG INDEX ARR)) 3))
        (CDLLNODEARRP ARR)
        (<= 0 I)
        (INTEGERP INDEX)
        (<= 0 INDEX))
   (EQUAL (CDLL_NTHNODEBY-LOOP-0 I N EDGENUM (AS X (AS 'VAL V (AG X ARR)) ARR) INDEX)
          (CDLL_MAX_NODE1)))
  :INSTRUCTIONS
  (:PROMOTE
   (:CASESPLIT (= X INDEX))
   (:DIVE 1 4)
   :S :UP (:REWRITE CDLL_NTHNODEBY-LOOP-0)
   :S (:REWRITE CDLL_NTHNODEBY-LOOP-0)
   :S :TOP :BASH (:DIVE 1)
   (:REWRITE CDLL_NTHNODEBY-LOOP-0)
   :S (:REWRITE CDLL_NTHNODEBY-LOOP-0)
   :S :TOP :BASH))

(DEFTHMD NTHNODEBY-LOOP-0-AS-VAL-IRRELEVANT-AUX-2--THM
  (IMPLIES
     (AND (INTEGERP I)
          (< 0 I)
          (< INDEX (CDLL_MAX_NODE1))
          (EQUAL (AG 'ALLOC (AG INDEX ARR)) 3)
          (EQUAL (CDLL_NTHNODEBY-LOOP-0 (+ -1 I) N 0 (AS X (AS 'VAL V (AG X ARR)) ARR)
                                        (AG 'NEXT (AG INDEX ARR)))
                 (CDLL_NTHNODEBY-LOOP-0 (+ -1 I) N 0 ARR (AG 'NEXT (AG INDEX ARR))))
          (CDLLNODEARRP ARR)
          (<= 0 I)
          (INTEGERP INDEX)
          (<= 0 INDEX))
     (EQUAL (CDLL_NTHNODEBY-LOOP-0 I N 0 (AS X (AS 'VAL V (AG X ARR)) ARR) INDEX)
            (CDLL_NTHNODEBY-LOOP-0 (+ -1 I) N 0 ARR (AG 'NEXT (AG INDEX ARR)))))
  :INSTRUCTIONS
  (:PROMOTE
   (:DIVE 2)
   (:= (CDLL_NTHNODEBY-LOOP-0 (+ -1 I) N 0 (AS X (AS 'VAL V (AG X ARR)) ARR) (AG 'NEXT (AG INDEX ARR))))
   :UP (:CASESPLIT (= X INDEX))
   (:DIVE 2)
   :S :UP (:DIVE 1) :S
   (:CLAIM (= (AG 'ALLOC (AG INDEX (AS INDEX (AS 'VAL V (AG INDEX ARR)) ARR)))
              (AG 'ALLOC (AG INDEX (AS INDEX (AS 'VAL V (AG INDEX ARR)) ARR)))))
   :TOP (:CONTRAPOSE 11)
   (:DIVE 1 2 2)
   :S :UP :S :TOP (:CONTRAPOSE 11)
   (:DIVE 1)
   (:REWRITE NTHNODEBY-LOOP-0-NEXT-OPENER--THM)
   :S :TOP :BASH
   (:CLAIM (= (AG 'ALLOC (AG INDEX (AS X (AS 'VAL V (AG X ARR)) ARR)))
              (AG 'ALLOC (AG INDEX (AS X (AS 'VAL V (AG X ARR)) ARR)))))
   (:CONTRAPOSE 11)
   (:DIVE 1 2 2)
   :S :UP :S :TOP (:CONTRAPOSE 11)
   (:DIVE 1)
   (:REWRITE NTHNODEBY-LOOP-0-NEXT-OPENER--THM)
   :S :TOP (:DIVE 2)
   :S :TOP :BASH))

(DEFTHMD NTHNODEBY-LOOP-0-AS-VAL-IRRELEVANT-AUX-3--THM
  (IMPLIES
   (AND (INTEGERP I)
        (< 0 I)
        (< INDEX (CDLL_MAX_NODE1))
        (EQUAL (AG 'ALLOC (AG INDEX ARR)) 3)
        (NOT (EQUAL EDGENUM 0))
        (EQUAL (CDLL_NTHNODEBY-LOOP-0 (+ -1 I) N EDGENUM
                                      (AS X (AS 'VAL V (AG X ARR)) ARR)
                                      (AG 'PREV (AG INDEX ARR)))
               (CDLL_NTHNODEBY-LOOP-0 (+ -1 I) N EDGENUM ARR (AG 'PREV (AG INDEX ARR))))
        (CDLLNODEARRP ARR)
        (<= 0 I)
        (INTEGERP INDEX)
        (<= 0 INDEX))
   (EQUAL (CDLL_NTHNODEBY-LOOP-0 I N EDGENUM
                                 (AS X (AS 'VAL V (AG X ARR)) ARR)
                                 INDEX)
          (CDLL_NTHNODEBY-LOOP-0 (+ -1 I) N EDGENUM ARR (AG 'PREV (AG INDEX ARR)))))
  :INSTRUCTIONS
  (:PROMOTE
   (:DIVE 2)
   (:= (CDLL_NTHNODEBY-LOOP-0 (+ -1 I) N EDGENUM (AS X (AS 'VAL V (AG X ARR)) ARR)
                              (AG 'PREV (AG INDEX ARR))))
   :UP (:CLAIM (< INDEX (CDLL_MAX_NODE1)))
   (:CASESPLIT (= X INDEX))
   (:DIVE 2)
   :S :UP (:DIVE 1)
   :S
   (:CLAIM (= (AG 'ALLOC (AG INDEX (AS INDEX (AS 'VAL V (AG INDEX ARR)) ARR)))
              (AG 'ALLOC (AG INDEX (AS INDEX (AS 'VAL V (AG INDEX ARR)) ARR)))))
   :TOP (:CONTRAPOSE 13)
   (:DIVE 1 2 2)
   :S :UP :S :TOP (:CONTRAPOSE 13)
   (:DIVE 1)
   (:REWRITE NTHNODEBY-LOOP-0-PREV-OPENER--THM)
   :S :TOP :BASH
   (:CLAIM (= (AG 'ALLOC (AG INDEX (AS X (AS 'VAL V (AG X ARR)) ARR)))
              (AG 'ALLOC (AG INDEX (AS X (AS 'VAL V (AG X ARR)) ARR)))))
   (:CONTRAPOSE 13)
   (:DIVE 1 2 2)
   :S :UP :S :TOP (:CONTRAPOSE 13)
   (:DIVE 1)
   (:REWRITE NTHNODEBY-LOOP-0-PREV-OPENER--THM)
   :S :TOP (:DIVE 2)
   :S :TOP :BASH))

(defthm nthNodeBy-loop-0-as-val-irrelevant--thm
  (implies
   (and (cdllnodeArrp arr)
        (integerp i) (<= 0 i) (integerp index) (<= 0 index))
   (= (cdll_nthNodeBy-loop-0 i n edgenum (as x (as 'val v (ag x arr)) arr) index)
      (cdll_nthNodeBy-loop-0 i n edgenum arr index)))
  :hints (("Goal" :in-theory (e/d (cdll_nthNodeBy-loop-0) ()))
          ("Subgoal *1/5.3" :use (:instance nthNodeBy-loop-0-as-val-irrelevant-aux-1--thm))
          ("Subgoal *1/5.2" :use (:instance nthNodeBy-loop-0-as-val-irrelevant-aux-2--thm))
          ("Subgoal *1/5.1" :use (:instance nthNodeBy-loop-0-as-val-irrelevant-aux-3--thm))))


(DEFTHMD NTHNODEBY-AS-VAL-IRRELEVANT-AUX-1--THM
  (IMPLIES
   (AND (CDLLNODEARRP ARR)
        (INTEGERP I)
        (<= 0 I)
        (INTEGERP INDEX)
        (<= 0 INDEX)
        (< (CDLL_NTHNODEBY-LOOP-0 I I EDGENUM ARR INDEX) (CDLL_MAX_NODE1))
        (EQUAL (AG 'ALLOC (AG (CDLL_NTHNODEBY-LOOP-0 I I EDGENUM ARR INDEX)
                              (AS X (AS 'VAL V (AG X ARR)) ARR)))
               3)
        (NOT (EQUAL (AG 'ALLOC (AG (CDLL_NTHNODEBY-LOOP-0 I I EDGENUM ARR INDEX) ARR)) 3)))
   (EQUAL (CDLL_NTHNODEBY-LOOP-0 I I EDGENUM ARR INDEX) (CDLL_MAX_NODE1)))
 :INSTRUCTIONS
 (:PROMOTE
      (:CONTRAPOSE 7)
      (:DIVE 1 1 2)
      (:CASESPLIT (NOT (= (CDLL_NTHNODEBY-LOOP-0 I I EDGENUM ARR INDEX) X)))
      :S :TOP :BASH :S (:DIVE 3 1)
      (:= (CDLL_NTHNODEBY-LOOP-0 I I EDGENUM ARR INDEX))
      :TOP :BASH))

(DEFTHMD NTHNODEBY-AS-VAL-IRRELEVANT-AUX-2--THM
  (IMPLIES
   (AND (CDLLNODEARRP ARR)
        (INTEGERP I)
        (<= 0 I)
        (INTEGERP INDEX)
        (<= 0 INDEX)
        (< (CDLL_NTHNODEBY-LOOP-0 I I EDGENUM ARR INDEX) (CDLL_MAX_NODE1))
        (NOT (EQUAL (AG 'ALLOC (AG (CDLL_NTHNODEBY-LOOP-0 I I EDGENUM ARR INDEX)
                                   (AS X (AS 'VAL V (AG X ARR)) ARR)))
                    3))
        (EQUAL (AG 'ALLOC (AG (CDLL_NTHNODEBY-LOOP-0 I I EDGENUM ARR INDEX) ARR)) 3))
   (EQUAL (CDLL_NTHNODEBY-LOOP-0 I I EDGENUM ARR INDEX) (CDLL_MAX_NODE1)))
 :INSTRUCTIONS
 (:PROMOTE
  (:CONTRAPOSE 7)
  (:DIVE 1 2 1)
  (:CASESPLIT (= (CDLL_NTHNODEBY-LOOP-0 I I EDGENUM ARR INDEX) X))
  :S :TOP :BASH
  :TOP :BASH))

(defthm nthNodeBy-as-val-irrelevant--thm
  (implies
   (and (cdllnodeArrp arr)
        (integerp i) (<= 0 i)
        (integerp index) (<= 0 index))
   (= (cdll_nthNodeBy
        i edgenum index
        (as x (as 'val v (ag x arr)) arr))
      (cdll_nthNodeBy i edgenum index arr)))
  :hints (("Goal" :in-theory (e/d (cdll_nthNodeBy) ()))
          ("Subgoal 2" :use (:instance nthNodeBy-as-val-irrelevant-aux-1--thm))
          ("Subgoal 1" :use (:instance nthNodeBy-as-val-irrelevant-aux-2--thm))))


(DEFTHMD NTHNODEBY-LOOP-0-AS-ND-ALLOC-NE-3-IRRELEVANT-AUX-1--THM
  (IMPLIES
   (AND (INTEGERP I)
        (< 0 I)
        (< INDEX (CDLL_MAX_NODE1))
        (EQUAL (AG 'ALLOC (AG INDEX ARR)) 3)
        (EQUAL (CDLL_NTHNODEBY-LOOP-0 (+ -1 I)
                                      N 0 (AS ND ELEM ARR)
                                      (AG 'NEXT (AG INDEX ARR)))
               (CDLL_NTHNODEBY-LOOP-0 (+ -1 I) N 0 ARR (AG 'NEXT (AG INDEX ARR))))
        (CDLLNODEARRP ARR)
        (INTEGERP INDEX)
        (<= 0 INDEX)
        (< (CDLL_NTHNODEBY-LOOP-0 (+ -1 I) N 0 ARR (AG 'NEXT (AG INDEX ARR)))
           (CDLL_MAX_NODE1))
        (not (= (ag 'alloc (ag nd arr)) 3)))
   (EQUAL (CDLL_NTHNODEBY-LOOP-0 I N 0 (AS ND ELEM ARR) INDEX)
          (CDLL_NTHNODEBY-LOOP-0 (+ -1 I) N 0 ARR (AG 'NEXT (AG INDEX ARR)))))
  :INSTRUCTIONS
  (:PROMOTE
   (:DIVE 1)
   (:CLAIM (NOT (= INDEX ND)))
   (:CLAIM (< INDEX (CDLL_MAX_NODE1)))
   (:CLAIM (= (AG 'ALLOC (AG INDEX (AS ND ELEM ARR))) 3))
   (:REWRITE NTHNODEBY-LOOP-0-NEXT-OPENER--THM)
   (:DIVE 5 2)
   (:= (AG INDEX ARR))
   :TOP :BASH))

(defthm nthNodeBy-loop-0-as-nd-alloc-ne-3-irrelevant--thm
  (implies
    (and (cdllnodeArrp arr)
         (integerp index) (<= 0 index)
         (< (cdll_nthNodeBy-loop-0 i n 0 arr index) (CDLL_MAX_NODE1))
         (not (= (ag 'alloc (ag nd arr)) 3)))
    (= (cdll_nthNodeBy-loop-0 i n 0 (as nd elem arr) index)
       (cdll_nthNodeBy-loop-0 i n 0 arr index)))
  :hints (("Goal" :in-theory (e/d (cdll_nthNodeBy-loop-0) ()))
          ("Subgoal *1/4"
           :use (:instance nthNodeBy-loop-0-as-nd-alloc-ne-3-irrelevant-aux-1--thm))))


(defthm nthNodeBy-as-nd-alloc-ne-3-irrelevant--thm
  (implies
    (and (cdllnodeArrp arr)
         (integerp index) (<= 0 index)
         (< (cdll_nthNodeBy i 0 index arr) (CDLL_MAX_NODE1))
         (not (= nd (cdll_nthNodeby i 0 index arr)))
         (not (= (ag 'alloc (ag nd arr)) 3)))
         ;;(not (= (ag 'alloc elem) 3)))
    (= (cdll_nthNodeBy i 0 index (as nd elem arr))
       (cdll_nthNodeBy i 0 index arr)))
  :hints (("Goal" :in-theory (e/d (cdll_nthNodeBy) ()))))


(DEFTHMD NTHNODEBY-LOOP-0-AS-PREV-IRRELEVANT-AUX-1--THM
  (IMPLIES
    (AND (INTEGERP I)
         (< 0 I)
         (< INDEX (CDLL_MAX_NODE1))
         (EQUAL (AG 'ALLOC (AG INDEX ARR)) 3)
         (EQUAL (CDLL_NTHNODEBY-LOOP-0 (+ -1 I) N 0 (AS X (AS 'PREV P (AG X ARR)) ARR)
                                       (AG 'NEXT (AG INDEX ARR)))
                (CDLL_NTHNODEBY-LOOP-0 (+ -1 I) N 0 ARR (AG 'NEXT (AG INDEX ARR))))
         (CDLLNODEARRP ARR)
         (<= 0 I)
         (INTEGERP INDEX)
         (<= 0 INDEX))
    (EQUAL (CDLL_NTHNODEBY-LOOP-0 I N 0 (AS X (AS 'PREV P (AG X ARR)) ARR) INDEX)
           (CDLL_NTHNODEBY-LOOP-0 (+ -1 I) N 0 ARR (AG 'NEXT (AG INDEX ARR)))))
  :INSTRUCTIONS
  (:PROMOTE
   (:DIVE 2)
   (:= (CDLL_NTHNODEBY-LOOP-0 (+ -1 I) N 0 (AS X (AS 'PREV P (AG X ARR)) ARR)
                              (AG 'NEXT (AG INDEX ARR))))
   :UP (:CLAIM (< INDEX (CDLL_MAX_NODE1)))
   (:CASESPLIT (= X INDEX))
   (:DIVE 2)
   :S :UP (:DIVE 1)
   :S
   (:CLAIM (= (AG 'ALLOC (AG INDEX (AS INDEX (AS 'PREV P (AG INDEX ARR)) ARR)))
              (AG 'ALLOC (AG INDEX (AS INDEX (AS 'PREV P (AG INDEX ARR)) ARR)))))
   :TOP (:CONTRAPOSE 12)
   (:DIVE 1 2 2)
   :S :UP :S :TOP (:CONTRAPOSE 12)
   (:DIVE 1)
   (:REWRITE NTHNODEBY-LOOP-0-NEXT-OPENER--THM)
   :S :TOP :BASH
   (:CLAIM (= (AG 'ALLOC (AG INDEX (AS X (AS 'PREV P (AG X ARR)) ARR)))
              (AG 'ALLOC (AG INDEX (AS X (AS 'PREV P (AG X ARR)) ARR)))))
   (:CONTRAPOSE 12)
   (:DIVE 1 2 2)
   :S :UP :S :TOP (:CONTRAPOSE 12)
   (:DIVE 1)
   (:REWRITE NTHNODEBY-LOOP-0-NEXT-OPENER--THM)
   :S :TOP (:DIVE 2)
   :S :TOP :BASH))

(DEFTHMD NTHNODEBY-LOOP-0-AS-PREV-IRRELEVANT-AUX-2--THM
  (IMPLIES
     (AND (INTEGERP I)
          (< 0 I)
          (< INDEX (CDLL_MAX_NODE1))
          (NOT (EQUAL (AG 'ALLOC (AG INDEX ARR)) 3))
          (CDLLNODEARRP ARR)
          (<= 0 I)
          (INTEGERP INDEX)
          (<= 0 INDEX))
     (EQUAL (CDLL_NTHNODEBY-LOOP-0 I N 0 (AS X (AS 'PREV P (AG X ARR)) ARR) INDEX) (CDLL_MAX_NODE1)))
  :INSTRUCTIONS
  (:PROMOTE
   (:CASESPLIT (= X INDEX))
   (:DIVE 1 4)
   :S :UP (:REWRITE CDLL_NTHNODEBY-LOOP-0)
   :S (:REWRITE CDLL_NTHNODEBY-LOOP-0)
   :S :TOP :BASH (:DIVE 1)
   (:REWRITE CDLL_NTHNODEBY-LOOP-0)
   :S (:REWRITE CDLL_NTHNODEBY-LOOP-0)
   :S
   :TOP :BASH))

(defthm nthNodeby-loop-0-as-prev-irrelevant--thm
  (implies
   (and (cdllnodeArrp arr)
        (integerp i) (<= 0 i)
        (integerp index) (<= 0 index))
   (= (cdll_nthNodeBy-loop-0 i n 0 (as x (as 'prev p (ag x arr)) arr) index)
      (cdll_nthNodeBy-loop-0 i n 0 arr index)))
  :hints (("Goal" :in-theory (e/d (cdll_nthNodeBy-loop-0) ()))
          ("Subgoal *1/5.2" :use (:instance nthNodeBy-loop-0-as-prev-irrelevant-aux-1--thm))
          ("Subgoal *1/5.1" :use (:instance nthNodeBy-loop-0-as-prev-irrelevant-aux-2--thm))))


(DEFTHMD NTHNODEBY-AS-PREV-IRRELEVANT-AUX-1--THM
  (IMPLIES
   (AND (CDLLNODEARRP ARR)
        (INTEGERP INDEX)
        (<= 0 INDEX)
        (< (CDLL_NTHNODEBY-LOOP-0 I I 0 ARR INDEX) (CDLL_MAX_NODE1))
        (EQUAL (AG 'ALLOC (AG (CDLL_NTHNODEBY-LOOP-0 I I 0 ARR INDEX)
                              (AS X (AS 'PREV P (AG X ARR)) ARR)))
               3)
        (NOT (EQUAL (AG 'ALLOC (AG (CDLL_NTHNODEBY-LOOP-0 I I 0 ARR INDEX) ARR)) 3)))
   (EQUAL (CDLL_NTHNODEBY-LOOP-0 I I 0 ARR INDEX) (CDLL_MAX_NODE1)))
  :INSTRUCTIONS
  (:PROMOTE
   (:CONTRAPOSE 5)
   (:DIVE 1 1 2)
   (:CASESPLIT (NOT (= (CDLL_NTHNODEBY-LOOP-0 I I 0 ARR INDEX) X)))
   :S :TOP :BASH (:DIVE 2 1)
   (:= (CDLL_NTHNODEBY-LOOP-0 I I 0 ARR INDEX))
   :UP :S (:DIVE 1)
   (:= (CDLL_NTHNODEBY-LOOP-0 I I 0 ARR INDEX))
   :UP :UP :S :UP :S (:DIVE 2 1)
   (:= (CDLL_NTHNODEBY-LOOP-0 I I 0 ARR INDEX))
   :TOP :BASH))

(DEFTHMD NTHNODEBY-AS-PREV-IRRELEVANT-AUX-2--THM
  (IMPLIES
   (AND (CDLLNODEARRP ARR)
        (INTEGERP INDEX)
        (<= 0 INDEX)
        (< (CDLL_NTHNODEBY-LOOP-0 I I 0 ARR INDEX) (CDLL_MAX_NODE1))
        (NOT (EQUAL (AG 'ALLOC (AG (CDLL_NTHNODEBY-LOOP-0 I I 0 ARR INDEX)
                                   (AS X (AS 'PREV P (AG X ARR)) ARR)))
                    3))
        (EQUAL (AG 'ALLOC (AG (CDLL_NTHNODEBY-LOOP-0 I I 0 ARR INDEX) ARR)) 3))
   (EQUAL (CDLL_NTHNODEBY-LOOP-0 I I 0 ARR INDEX) (CDLL_MAX_NODE1)))
  :INSTRUCTIONS
  (:PROMOTE
   (:CONTRAPOSE 5)
   (:DIVE 1 2)
   (:CASESPLIT (NOT (= (CDLL_NTHNODEBY-LOOP-0 I I 0 ARR INDEX) X)))
   :S :TOP :BASH (:DIVE 2 1)
   (:= (CDLL_NTHNODEBY-LOOP-0 I I 0 ARR INDEX))
   :UP :S (:DIVE 1)
   (:= (CDLL_NTHNODEBY-LOOP-0 I I 0 ARR INDEX))
   :UP :UP :S (:DIVE 3 1)
   (:= (CDLL_NTHNODEBY-LOOP-0 I I 0 ARR INDEX))
   :UP :UP :UP :S (:DIVE 2 1)
   (:= (CDLL_NTHNODEBY-LOOP-0 I I 0 ARR INDEX))
   :TOP :BASH))

(defthm nthNodeBy-as-prev-irrelevant--thm
  (implies
   (and (cdllnodeArrp arr)
        (integerp i) (<= 0 i)
        (integerp index) (<= 0 index))
   (= (cdll_nthNodeBy 
         i 0 index
         (as x (as 'prev p (ag x arr)) arr))
      (cdll_nthNodeBy i 0 index arr)))
  :hints (("Goal" :in-theory (e/d (cdll_nthNodeBy) ()))
          ("Subgoal 2" :use (:instance nthnodeBy-as-prev-irrelevant-aux-1--thm))
          ("Subgoal 1" :use (:instance nthnodeBy-as-prev-irrelevant-aux-2--thm))))


(defthmd nth-nthNodeBy-aux-1--thm
  (implies (< (cdll_nthNodeBy 0 0 (ag 'nodeHd CDObj) (ag 'nodeArr CDObj)) (CDLL_MAX_NODE1))
           (equal (ag 'val (ag (ag 'nodeHd CDObj) (ag 'nodeArr CDObj)))
                  (ag 'val (ag (cdll_nthNodeBy 0 0 (ag 'nodeHd CDObj) (ag 'nodeArr CDObj))
                               (ag 'nodeArr CDObj)))))
  :hints (("Goal" :in-theory (e/d (cdll_nthNodeBy) ()))))

(defthmd nth-nthNodeBy--thm
  (implies
   (and ;; (cdllp CDObj)
        ;; (integerp (ag 'nodeCount CDObj)) (< 0 (ag 'nodeCount CDObj))
        (integerp n) (<= 0 n) (< n (ag 'nodeCount CDObj))
        (integerp (cdll_nthnodeBy n 0 (ag 'nodeHd CDObj) (ag 'nodeArr CDObj)))
        (< (cdll_nthnodeBy n 0 (ag 'nodeHd CDObj) (ag 'nodeArr CDObj)) (CDLL_MAX_NODE1)))
   (= (cdll_nth n CDObj)
      (ag 'val (ag (cdll_nthNodeBy n 0 (ag 'nodeHd CDObj) (ag 'nodeArr CDObj))
                   (ag 'nodeArr CDObj)))))
  :hints (("Goal" :in-theory (e/d (nth-nthnodeBy-aux-1--thm) ()))))


(DEFTHMD NTH-NTHNODEBY-N-MINUS-1-AUX-1--THM
  (IMPLIES
   (AND (CDLLNODEARRP (AG 'NODEARR CDOBJ))
        (INTEGERP (AG 'NODEHD CDOBJ))
        (< 0 (AG 'NODEHD CDOBJ))
        (< (AG 'NODEHD CDOBJ) (CDLL_MAX_NODE1))
        (INTEGERP N)
        (< 0 N)
        (ACL2-NUMBERP (AG 'NODECOUNT CDOBJ))
        (< N (AG 'NODECOUNT CDOBJ))
        (< (CDLL_NTHNODEBY N 0 (AG 'NODEHD CDOBJ) (AG 'NODEARR CDOBJ)) (CDLL_MAX_NODE1))
        (< (CDLL_NTHNODEBY (+ -1 N) 0 (AG 'NODEHD CDOBJ) (AG 'NODEARR CDOBJ))
           (CDLL_MAX_NODE1))
        (< (AG 'NEXT (AG (CDLL_NTHNODEBY (+ -1 N) 0 (AG 'NODEHD CDOBJ) (AG 'NODEARR CDOBJ))
                         (AG 'NODEARR CDOBJ)))
           (CDLL_MAX_NODE1))
        (EQUAL
         (AG 'ALLOC (AG (AG 'NEXT (AG (CDLL_NTHNODEBY (+ -1 N) 0 (AG 'NODEHD CDOBJ) (AG 'NODEARR CDOBJ))
                                      (AG 'NODEARR CDOBJ)))
                        (AG 'NODEARR CDOBJ)))
         3)
        (NOT (EQUAL (CDLL_NTHNODEBY N 0 (AG 'NODEHD CDOBJ) (AG 'NODEARR CDOBJ)) (CDLL_MAX_NODE1))))
   (EQUAL (AG 'VAL (AG (CDLL_NTHNODEBY N 0 (AG 'NODEHD CDOBJ) (AG 'NODEARR CDOBJ)) (AG 'NODEARR CDOBJ)))
          (AG 'VAL
              (AG (AG 'NEXT (AG (CDLL_NTHNODEBY (+ -1 N) 0 (AG 'NODEHD CDOBJ) (AG 'NODEARR CDOBJ))
                                (AG 'NODEARR CDOBJ)))
                  (AG 'NODEARR CDOBJ)))))
  :INSTRUCTIONS
  (:PROMOTE
   (:DIVE 1 2 1)
   (:CLAIM (< (AG 'NODEHD CDOBJ) (CDLL_MAX_NODE1)))
   (:CLAIM (<= 0 (CDLL_NTHNODEBY (+ -1 N) 0 (AG 'NODEHD CDOBJ) (AG 'NODEARR CDOBJ))))
   (:CLAIM (< (CDLL_NTHNODEBY (+ -1 N) 0 (AG 'NODEHD CDOBJ) (AG 'NODEARR CDOBJ))
              (CDLL_MAX_NODE1)))
   (:CLAIM (EQUAL (AG 'ALLOC (AG (CDLL_NTHNODEBY (+ -1 N) 0 (AG 'NODEHD CDOBJ) (AG 'NODEARR CDOBJ))
                                 (AG 'NODEARR CDOBJ)))
                  3))
   (:CLAIM (< (AG 'NEXT (AG (CDLL_NTHNODEBY (+ -1 N) 0 (AG 'NODEHD CDOBJ) (AG 'NODEARR CDOBJ))
                            (AG 'NODEARR CDOBJ)))
              (CDLL_MAX_NODE1)))
   (:CLAIM (EQUAL (AG 'ALLOC
                      (AG (AG 'NEXT (AG (CDLL_NTHNODEBY (+ -1 N) 0 (AG 'NODEHD CDOBJ)
                                                        (AG 'NODEARR CDOBJ))
                                        (AG 'NODEARR CDOBJ)))
                          (AG 'NODEARR CDOBJ)))
                  3))
   (:CLAIM (INTEGERP (CDLL_NTHNODEBY (+ -1 N) 0 (AG 'NODEHD CDOBJ) (AG 'NODEARR CDOBJ))))
   (:REWRITE NTHNODEBY-NEXT-OPENER-FRONT--THM)
   :TOP :BASH))

(defthmd nth-nthNodeBy-n-minus-1--thm
  (implies
   (and (cdllnodeArrp (ag 'nodeArr CDObj))
        (integerp (ag 'nodeHd CDObj))
        (< 0 (ag 'nodeHd CDObj))
        (< (ag 'nodeHd CDObj) (CDLL_MAX_NODE1))
        (integerp n) (< 0 n) (< n (ag 'nodeCount CDObj))
        (< (cdll_nthNodeBy n 0 (ag 'nodeHd CDObj) (ag 'nodeArr CDObj)) (CDLL_MAX_NODE1))
        (good-nodep (ag 'nodeCount CDObj)
                    (cdll_nthNodeBy (1- n) 0 (ag 'nodeHd CDObj) (ag 'nodeArr CDObj))
                    (ag 'nodeArr CDObj))
        (good-node-nextp (ag 'nodeCount CDObj)
                         (cdll_nthNodeBy (1- n) 0 (ag 'nodeHd CDObj) (ag 'nodeArr CDObj))
                         (ag 'nodeArr CDObj)))
   (= (cdll_nth n CDObj)
      (ag 'val (ag (ag 'next (ag (cdll_nthNodeBy (1- n) 0 (ag 'nodeHd CDObj) (ag 'nodeArr CDObj))
                                 (ag 'nodeArr CDObj)))
                   (ag 'nodeArr CDObj)))))
:hints (("Goal" :use (:instance nth-nthNodeBy-n-minus-1-aux-1--thm))))


(DEFTHM NTHNODEBY-0-OPENER-NO-ERR--THM
  (IMPLIES
   (AND (< INDEX (CDLL_MAX_NODE1))
        (= (AG 'ALLOC (AG INDEX (AG 'NODEARR CDOBJ))) 3))
   (= (CDLL_NTHNODEBY 0 EDGENUM INDEX (AG 'NODEARR CDOBJ))
      INDEX))
  :INSTRUCTIONS
  (:PROMOTE
   (:DIVE 1)
   (:REWRITE CDLL_NTHNODEBY)
   (:DIVE 1)
   (:= INDEX)
   :UP
   (:CLAIM (NOT (= (LOGAND1 (LOG< INDEX (CDLL_MAX_NODE1))
                            (LOG= (AG 'ALLOC (AG INDEX (AG 'NODEARR CDOBJ))) 3))
                   0)))
   (:= INDEX)
   :TOP :BASH))

(DEFTHM NTHNODEBY-0-OPENER-ERR--THM
  (IMPLIES
    (OR (= INDEX (CDLL_MAX_NODE1))
        (NOT (= (AG 'ALLOC (AG INDEX (AG 'NODEARR CDOBJ))) 3)))
    (= (CDLL_NTHNODEBY 0 EDGENUM INDEX (AG 'NODEARR CDOBJ))
       (CDLL_MAX_NODE1)))
  :INSTRUCTIONS
  (:PROMOTE
   (:DIVE 1)
   (:REWRITE CDLL_NTHNODEBY)
   (:DIVE 1)
   (:= INDEX)
   :UP
   (:CLAIM (= (LOGAND1 (LOG< INDEX (CDLL_MAX_NODE1))
                       (LOG= (AG 'ALLOC (AG INDEX (AG 'NODEARR CDOBJ))) 3))
              0))
   (:= (CDLL_MAX_NODE1))
   :TOP :BASH))

(defthmd nthNodeBy-0-err-ag-alloc-index-ne-3--thm
  (implies
   (and (< index (CDLL_MAX_NODE1))
        (= (cdll_nthNodeBy 0 edgenum index arr) (CDLL_MAX_NODE1)))
   (not (= (ag 'alloc (ag index arr)) 3)))
  :hints (("Goal" :in-theory (e/d (cdll_nthNodeBy cdll_nthNodeBy-loop-0) ()))))


(defthm nthnodeby-0-nthnodeby-n--thm
  (= (cdll_nthnodeBy 0 edgenum (cdll_nthnodeBy n edgenum index arr) arr)
     (cdll_nthnodeBy n edgenum index arr))
 :hints (("Goal" :in-theory (e/d (cdll_nthNodeBy cdll_nthNodeBy-loop-0) ()))))


(defthm nthnodeBy-0-as-nthnodeBy-n--thm
  (= (cdll_nthNodeBy 0 0 (ag 'nodeHd (as 'nodeHd
                                         (cdll_nthnodeBy n 0 (ag 'nodeHd CDObj) (ag 'nodeArr CDObj))
                                         CDObj))
                     (ag 'nodeArr (as 'nodeHd
                                      (cdll_nthnodeBy n 0 (ag 'nodeHd CDObj) (ag 'nodeArr CDObj))
                                      CDObj)))
     (cdll_nthNodeBy n 0 (ag 'nodeHd CDObj) (ag 'nodeArr CDObj))))


(defthmd nthnodeBy-n-nthnodeBy-0--thm
  (= (cdll_nthnodeBy n edgenum index arr)
     (cdll_nthnodeBy 0 edgenum (cdll_nthNodeby n edgenum index arr) arr))
 :hints (("Goal" :in-theory (e/d (cdll_nthNodeBy cdll_nthNodeBy-loop-0) ()))))

;;;;;;;;;;;;

(defthm ln-of-cns--thm
  (implies
   (and (spacep CDObj)
        (integerp (ag 'nodeHd CDObj))
        ;; (<= 0 (ag 'nodeHd CDObj))
        (< (ag 'nodeHd CDObj) (CDLL_MAX_NODE1))
        (equal (ag 'alloc (ag (ag 'nodeHd CDObj) (ag 'nodeArr CDObj))) 3)
        (acl2::signed-byte-p 64 v)
        (>= v (CDLL_MIN_VAL)))
   (= (CDLL_ln (CDLL_cns v CDObj))
      (1+ (CDLL_ln CDObj))))
  :hints (("Goal" :in-theory (e/d (si) ()))))


(defthm ln-of-cns1--thm
  (implies
   (and (spacep CDObj)
        (< 0 (ag 'nodeCount CDObj))
        (integerp (ag 'nodeHd CDObj))
        ;; (<= 0 (ag 'nodeHd CDObj))
        (< (ag 'nodeHd CDObj) (CDLL_MAX_NODE1))
        (equal (ag 'alloc (ag (ag 'nodeHd CDObj) (ag 'nodeArr CDObj))) 3)
        (acl2::signed-byte-p 64 v)
        (>= v (CDLL_MIN_VAL)))
   (= (CDLL_ln (CDLL_cns1 v CDObj))
      (1+ (CDLL_ln CDObj))))
  :hints (("Goal" :in-theory (e/d (si) ()))))


(defthm ln-of-rst--thm
  (implies (< 0 (cdll_ln CDObj))
           (= (cdll_ln (cdll_rst CDObj)) (1- (cdll_ln CDObj)))))

(defthm ln-of-snc--thm
  (implies
   (and (spacep CDObj)
        (integerp (ag 'nodeHd CDObj))
        (<= 0 (ag 'nodeHd CDObj))
        (< (ag 'nodeHd CDObj) (CDLL_MAX_NODE1))
        (equal (ag 'alloc (ag (ag 'nodeHd CDObj) (ag 'nodeArr CDObj))) 3)
        (acl2::signed-byte-p 64 v)
        (>= v (CDLL_MIN_VAL)))
   (= (cdll_ln (cdll_snc v CDObj))
      (1+ (cdll_ln CDObj))))
  :hints (("Goal" :in-theory (e/d (si) ()))))

(defthm ln-of-tsr--thm
  (implies (< 0 (cdll_ln CDObj))
           (= (cdll_ln (cdll_tsr CDObj)) (1- (cdll_ln CDObj)))))


(defthm cns-nodeHd-changes--thm
  (implies
   (and (cdllp CDObj)
        (good-nodep (ag 'nodeCount CDObj) (ag 'nodeHd CDObj) (ag 'nodeArr CDObj))
        (good-node-nextp (ag 'nodeCount CDObj) (ag 'nodeHd CDObj) (ag 'nodeArr CDObj))
        (good-node-prevp (ag 'nodeCount CDObj) (ag 'nodeHd CDObj) (ag 'nodeArr CDObj))
        (good-node-prev-nextp (ag 'nodeCount CDObj) (ag 'nodeHd CDObj) (ag 'nodeArr CDObj))
        (spacep CDObj)
        (< 0 (ag 'nodeCount CDObj))
        (acl2::signed-byte-p 64 v)
        (>= v (CDLL_MIN_VAL)))
   (not (= (ag 'nodeHd (cdll_cns v CDObj))
           (ag 'nodeHd CDObj))))
  :hints (("Goal" :in-theory (e/d (si) ())
                  :use (:instance find_free_node-ne-nodeHd--thm))))


(defthm cns1-nodeHd-same--thm
  (= (ag 'nodeHd (cdll_cns1 v CDObj))
     (ag 'nodeHd CDObj)))


(defthm cns1-nodeHd-alloc-same--thm
  (implies
   (and ;; (cdllp CDObj)
        (good-nodep (ag 'nodeCount CDObj) (ag 'nodeHd CDObj) (ag 'nodeArr CDObj))
        ;; (good-node-nextp (ag 'nodeCount CDObj) (ag 'nodeHd CDObj) (ag 'nodeArr CDObj))
        ;; (good-node-prevp (ag 'nodeCount CDObj) (ag 'nodeHd CDObj) (ag 'nodeArr CDObj))
        (good-node-prev-nextp (ag 'nodeCount CDObj) (ag 'nodeHd CDObj) (ag 'nodeArr CDObj)))
   (= (ag 'alloc (ag (ag 'nodeHd (cdll_cns1 v CDObj))
                     (ag 'nodeArr (cdll_cns1 v CDObj))))
      (ag 'alloc (ag (ag 'nodeHd CDObj) (ag 'nodeArr CDObj)))))
  :hints (("Goal" :use (:instance find_free_node-ne-nodeHd--thm))))


(DEFTHM NTHNODEBY-0-OF-CNS1-SAME--THM
  (IMPLIES
   (AND (GOOD-NODEP (AG 'NODECOUNT CDOBJ) (AG 'NODEHD CDOBJ) (AG 'NODEARR CDOBJ))
        ;; (GOOD-NODE-NEXTP (AG 'NODECOUNT CDOBJ) (AG 'NODEHD CDOBJ) (AG 'NODEARR CDOBJ))
        ;; (GOOD-NODE-PREVP (AG 'NODECOUNT CDOBJ) (AG 'NODEHD CDOBJ) (AG 'NODEARR CDOBJ))
        (GOOD-NODE-PREV-NEXTP (AG 'NODECOUNT CDOBJ) (AG 'NODEHD CDOBJ) (AG 'NODEARR CDOBJ)))
   (= (CDLL_NTHNODEBY 0 0 (AG 'NODEHD (CDLL_CNS1 V CDOBJ))
                      (AG 'NODEARR (CDLL_CNS1 V CDOBJ)))
      (CDLL_NTHNODEBY 0 0 (AG 'NODEHD CDOBJ)
                      (AG 'NODEARR CDOBJ))))
  :INSTRUCTIONS
   (:PROMOTE
    (:CLAIM (= (AG 'NODEHD (CDLL_CNS1 V CDOBJ))
               (AG 'NODEHD CDOBJ))
            :HINTS (("Goal" :USE (:INSTANCE CNS1-NODEHD-SAME--THM))))
    (:CLAIM (= (AG 'ALLOC (AG (AG 'NODEHD (CDLL_CNS1 V CDOBJ))
                              (AG 'NODEARR (CDLL_CNS1 V CDOBJ))))
               (AG 'ALLOC (AG (AG 'NODEHD CDOBJ) (AG 'NODEARR CDOBJ))))
            :HINTS (("Goal" :USE (:INSTANCE CNS1-NODEHD-ALLOC-SAME--THM))))
    (:DIVE 2)
    (:REWRITE CDLL_NTHNODEBY)
    (:CASESPLIT (AND (< (AG 'NODEHD CDOBJ) (CDLL_MAX_NODE1))
                     (= (AG 'ALLOC (AG (AG 'NODEHD CDOBJ) (AG 'NODEARR CDOBJ))) 3)))
    (:= (AG 'NODEHD CDOBJ))
    :TOP (:DIVE 1)
    (:CLAIM (< (AG 'NODEHD (CDLL_CNS1 V CDOBJ)) (CDLL_MAX_NODE1)))
    (:DIVE 3)
    (:= (AG 'NODEHD CDOBJ))
    :UP (:REWRITE CDLL_NTHNODEBY)
    (:= (AG 'NODEHD CDOBJ))
    :TOP :BASH (:= (CDLL_MAX_NODE1))
    :UP (:DIVE 1 3)
    (:= (AG 'NODEHD CDOBJ))
    :UP (:REWRITE CDLL_NTHNODEBY)
    (:= (CDLL_MAX_NODE1))
    :TOP :BASH))


(defthm snc-nodetl-changes--thm
  (implies
   (and ;; (cdllp CDObj)
        (< 0 (CDLL_ln CDObj))
        (good-nodep (ag 'nodeCount CDObj) (ag 'nodeHd CDObj) (ag 'nodeArr CDObj))
        (good-node-nextp (ag 'nodeCount CDObj) (ag 'nodeHd CDObj) (ag 'nodeArr CDObj))
        (good-node-prevp (ag 'nodeCount CDObj) (ag 'nodeHd CDObj) (ag 'nodeArr CDObj))
        ;; (good-node-prev-nextp (ag 'nodeCount CDObj) (ag 'nodeHd CDObj) (ag 'nodeArr CDObj))
        (spacep CDObj)
        (acl2::signed-byte-p 64 v)
        (>= v (CDLL_MIN_VAL)))
   (not (= (ag 'prev (ag (ag 'nodeHd (cdll_snc v CDObj)) (ag 'nodeArr (cdll_snc v CDObj))))
           (ag 'prev (ag (ag 'nodeHd CDObj) (ag 'nodeArr CDObj))))))
  :hints (("Goal" :in-theory (e/d (si) ())
                  :use (:instance find_free_node-ne-nodeHd--thm))))


(defthm cns1-nodeHd-next--thm
  (implies
   (AND ;; (cdllp CDObj)
        (< 0 (ag 'nodeCount CDObj))
        (good-nodep (ag 'nodeCount CDObj) (ag 'nodeHd CDObj) (ag 'nodeArr CDObj))
        (spacep CDObj)
        (signed-byte-p 64 v)
        (>= v (CDLL_MIN_VAL)))
   (= (ag 'next (ag (ag 'nodeHd CDObj) (ag 'nodeArr (cdll_cns1 v CDObj))))
      (cdll_find_free_node (ag 'nodeCount CDObj) (ag 'nodeArr CDObj))))
  :hints (("Goal" :in-theory (e/d (si) (cdll_nthNodeBy)))))


(defthm nth-0-of-cns--thm
  (implies
   (and ;; (cdllp CDObj)
        (good-nodep (ag 'nodeCount CDObj) (ag 'nodeHd CDObj) (ag 'nodeArr CDObj))
        (spacep CDObj)
        (acl2::signed-byte-p 64 v)
        (>= v (CDLL_MIN_VAL)))
   (= (CDLL_nth 0 (CDLL_cns v CDObj))
      v))
  :hints (("Goal" :in-theory (e/d (si) ()))))


(defthm nth-1-of-cns--thm
  (implies
   (and ;; (cdllp CDObj)
        (< 0 (cdll_ln CDObj))
        (good-nodep (ag 'nodeCount CDObj) (ag 'nodeHd CDObj) (ag 'nodeArr CDObj))
        (good-node-nextp (ag 'nodeCount CDObj) (ag 'nodeHd CDObj) (ag 'nodeArr CDObj))
        (not (= (ag 'prev (ag (ag 'nodeHd CDObj) (ag 'nodeArr CDObj))) (ag 'nodeHd CDObj)))
        (spacep CDObj)
        (acl2::signed-byte-p 64 v)
        (>= v (CDLL_MIN_VAL)))
   (= (cdll_nth 1 (cdll_cns v CDObj))
      (cdll_hd CDObj)))
  :hints (("Goal" :in-theory (e/d (si cdll_find_free_node cdll_nthnodeBy cdll_nthnodeBy-loop-0) ())
                  :use (:instance find_free_node-ne-nodeHd--thm))))


(defthmd nth-1-of-cns1-aux-1--thm
  (implies
   (and ;;(cdllp CDObj)
        (< 0 (cdll_ln CDObj))
        (good-nodep (ag 'nodeCount CDObj) (ag 'nodeHd CDObj) (ag 'nodeArr CDObj))
        ;; (good-node-nextp (ag 'nodeCount CDObj) (ag 'nodeHd CDObj) (ag 'nodeArr CDObj))
        ;; (good-node-prevp (ag 'nodeCount CDObj) (ag 'nodeHd CDObj) (ag 'nodeArr CDObj))
        (good-node-prev-nextp (ag 'nodeCount CDObj) (ag 'nodeHd CDObj) (ag 'nodeArr CDObj))
        (not (= (CDLL_FIND_FREE_NODE (AG 'NODECOUNT CDOBJ) (AG 'NODEARR CDOBJ))
                (AG 'NEXT (AG (AG 'NODEHD CDOBJ) (AG 'NODEARR CDOBJ)))))
        (not (= (CDLL_FIND_FREE_NODE (AG 'NODECOUNT CDOBJ) (AG 'NODEARR CDOBJ))
                (AG 'PREV (AG (AG 'NODEHD CDOBJ) (AG 'NODEARR CDOBJ)))))
        (spacep CDObj)
        (acl2::signed-byte-p 64 v)
        (>= v (CDLL_MIN_VAL)))
   (= (cdll_nth 1 (cdll_cns1 v CDObj))
      v))
  :hints (("Goal" :in-theory (e/d (si cdll_nthNodeBy cdll_nthNodeBy-loop-0) ())
                  :use (:instance find_free_node-ne-nodeHd--thm))))

(DEFTHM NTH-1-OF-CNS1--THM
  (IMPLIES
   (AND (< 0 (CDLL_LN CDOBJ))
        (GOOD-NODEP (AG 'NODECOUNT CDOBJ) (AG 'NODEHD CDOBJ) (AG 'NODEARR CDOBJ))
        (GOOD-NODE-NEXTP (AG 'NODECOUNT CDOBJ) (AG 'NODEHD CDOBJ) (AG 'NODEARR CDOBJ))
        (GOOD-NODE-PREVP (AG 'NODECOUNT CDOBJ) (AG 'NODEHD CDOBJ) (AG 'NODEARR CDOBJ))
        (GOOD-NODE-PREV-NEXTP (AG 'NODECOUNT CDOBJ) (AG 'NODEHD CDOBJ) (AG 'NODEARR CDOBJ))
        (SPACEP CDOBJ)
        (SIGNED-BYTE-P 64 V)
        (>= V (CDLL_MIN_VAL)))
   (= (CDLL_NTH 1 (CDLL_CNS1 V CDOBJ))
      V))
  :INSTRUCTIONS
  (:PROMOTE
   (:CLAIM (NOT (= (CDLL_FIND_FREE_NODE (AG 'NODECOUNT CDOBJ) (AG 'NODEARR CDOBJ))
                   (AG 'NEXT (AG (AG 'NODEHD CDOBJ) (AG 'NODEARR CDOBJ))))))
   (:CLAIM (NOT (= (CDLL_FIND_FREE_NODE (AG 'NODECOUNT CDOBJ) (AG 'NODEARR CDOBJ))
                   (AG 'PREV (AG (AG 'NODEHD CDOBJ) (AG 'NODEARR CDOBJ))))))
   (:PROVE :HINTS (("Goal" :USE (:INSTANCE NTH-1-OF-CNS1-AUX-1--THM))))))


(defthm tl-of-cns--thm
  (implies
   (and ;; (cdllp CDObj)
        (good-nodep (ag 'nodeCount CDObj) (ag 'nodeHd CDObj) (ag 'nodeArr CDObj))
        (good-node-nextp (ag 'nodeCount CDObj) (ag 'nodeHd CDObj) (ag 'nodeArr CDObj))
        (good-node-prevp (ag 'nodeCount CDObj) (ag 'nodeHd CDObj) (ag 'nodeArr CDObj))
        (good-node-prev-nextp (ag 'nodeCount CDObj) (ag 'nodeHd CDObj) (ag 'nodeArr CDObj))
        (< 0 (cdll_ln CDObj)))
   (= (cdll_tl (cdll_cns v CDObj))
      (cdll_tl CDObj)))
  :hints (("Goal" :use (:instance find_free_node-ne-tail--thm))))


(defthm tl-of-cns1--thm
  (implies
   (and (cdllp CDObj)
        (good-nodep (ag 'nodeCount CDObj) (ag 'nodeHd CDObj) (ag 'nodeArr CDObj))
        (good-node-nextp (ag 'nodeCount CDObj) (ag 'nodeHd CDObj) (ag 'nodeArr CDObj))
        (good-node-prevp (ag 'nodeCount CDObj) (ag 'nodeHd CDObj) (ag 'nodeArr CDObj))
        (good-node-prev-nextp (ag 'nodeCount CDObj) (ag 'nodeHd CDObj) (ag 'nodeArr CDObj))
        (< 1 (cdll_ln CDObj)))
   (= (cdll_tl (cdll_cns1 v CDObj))
      (cdll_tl CDObj)))
  :hints (("Goal" :use (:instance find_free_node-ne-nodeHd--thm))
          ("Subgoal 6" :use (:instance find_free_node-ne-tail--thm))
          ("Subgoal 3" :use (:instance find_free_node-ne-tail--thm))))


(defthm hd-of-snc--thm
  (implies
   (and ;; (cdllp CDObj)
        (< 0 (cdll_ln CDObj))
        (good-nodep (ag 'nodeCount CDObj) (ag 'nodeHd CDObj) (ag 'nodeArr CDObj))
        (not (= (ag 'prev (ag (ag 'nodeHd CDObj) (ag 'nodeArr CDObj))) (ag 'nodeHd CDObj))))
   (= (cdll_hd (cdll_snc v CDObj))
      (cdll_hd CDObj)))
  :hints (("Goal" :in-theory (e/d (cdll_find_free_node) ())
                    :use (:instance find_free_node-ne-nodeHd--thm))))


(defthm tl-of-snc--thm
  (implies
   (and ;; (cdllp CDObj)
        (< 0 (cdll_ln CDObj))
        (good-nodep (ag 'nodeCount CDObj) (ag 'nodeHd CDObj) (ag 'nodeArr CDObj))
        (good-node-nextp (ag 'nodeCount CDObj) (ag 'nodeHd CDObj) (ag 'nodeArr CDObj))
        (spacep CDObj)
        (acl2::signed-byte-p 64 v)
        (>= v (CDLL_MIN_VAL)))
   (= (cdll_tl (cdll_snc v CDObj))
      v))
  :hints (("Goal" :in-theory (e/d (si cdll_find_free_node) ())
                  :use (:instance find_free_node-ne-nodeHd--thm))))


(defthm nth_prev-1-of-snc--thm
  (implies
   (and ;;(cdllp CDObj)
        (< 0 (cdll_ln CDObj))
        (good-nodep (ag 'nodeCount CDObj) (ag 'nodeHd CDObj) (ag 'nodeArr CDObj))
        (good-node-nextp (ag 'nodeCount CDObj) (ag 'nodeHd CDObj) (ag 'nodeArr CDObj))
        (not (= (ag 'prev (ag (ag 'nodeHd CDObj) (ag 'nodeArr CDObj))) (ag 'nodeHd CDObj)))
        (spacep CDObj)
        (acl2::signed-byte-p 64 v)
        (>= v (CDLL_MIN_VAL)))
   (= (cdll_nth_prev 1 (cdll_snc v CDObj))
      v))
  :hints (("Goal" :in-theory (e/d (si cdll_find_free_node cdll_nthnodeBy cdll_nthnodeBy-loop-0) ())
                  :use (:instance find_free_node-ne-nodeHd--thm))))


;; Compositions

(defthm hd-of-rst-of-cns--thm
  (implies
   (and (cdllp CDObj)
        (good-nodep (ag 'nodeCount CDObj) (ag 'nodeHd CDObj) (ag 'nodeArr CDObj))
        (good-node-nextp (ag 'nodeCount CDObj) (ag 'nodeHd CDObj) (ag 'nodeArr CDObj))
        (not (= (ag 'prev (ag (ag 'nodeHd CDObj) (ag 'nodeArr CDObj))) (ag 'nodeHd CDObj)))
        (spacep CDObj)
        (acl2::signed-byte-p 64 v)
        (>= v (CDLL_MIN_VAL)))
   (= (cdll_hd (cdll_rst (cdll_cns v CDObj))) (cdll_hd CDObj)))
  :hints (("Goal" :in-theory (e/d (si) ()) ;; cdll_find_free_node) ())
                  :use (:instance find_free_node-ne-nodeHd--thm))))


(defthm tl-of-tsr-of-snc--thm
  (implies
   (and (cdllp CDObj)
        (good-Objp CDObj)
        (spacep CDObj)
        (acl2::signed-byte-p 64 v)
        (>= v (CDLL_MIN_VAL)))
   (= (cdll_tl (cdll_tsr (cdll_snc v CDObj))) (cdll_tl CDObj)))
  :hints (("Goal" :in-theory (e/d (si) ())
                  :use (:instance find_free_node-ne-nodeHd--thm))))


(defthmd cns-eq-snc-if-ln-eq-0--thm
  (implies
   (= 0 (cdll_ln CDObj))
   (= (cdll_cns v CDObj) (cdll_snc v CDObj))))

(defthmd rst-eq-tsr-if-ln-eq-1--thm
  (implies
   (and ;;(cdllp CDObj)
        (= 1 (cdll_ln CDObj))
        (good-Objp CDObj))
   (= (cdll_rst CDObj) (cdll_tsr CDObj))))


;; Knuth "Dancing Links"

(defthm ln-of-remove--thm
  (implies
   (and (cdllp CDObj)
        (integerp n)
        (<= n (CDLL_MAX_NODE))
        (not (= n (ag 'nodeHd CDObj)))
        (< 2 (ag 'nodeCount CDObj)))
   (= (cdll_ln (cdll_remove n CDObj)) (1- (cdll_ln CDObj)))))

(defthm remove-not-enough-elements--thm
  (implies
   (< (ag 'nodeCount CDObj) 3)
   (= (cdll_remove n CDObj) CDObj)))

(defthm remove-of-nodeHd--thm
  (implies
   (= n (ag 'nodeHd CDObj))
   (= (cdll_remove n CDObj) CDObj)))


(defthm ln-of-restore--thm
  (implies
   (and (posp n)
        (<= n (CDLL_MAX_NODE))
        (not (= n (ag 'nodeHd CDObj)))
        (< (ag 'nodeCount CDObj) (CDLL_MAX_NODE))
        (< 2 (ag 'nodeCount CDObj)))
   (= (cdll_ln (cdll_restore n CDObj)) (1+ (cdll_ln CDObj)))))


(defthm restore-not-enough-elements--thm
  (implies (< (ag 'nodeCount CDObj) 2)
           (= (cdll_restore n CDObj) CDObj)))

(defthm restore-of-nodeHd--thm
  (implies (= n (ag 'nodeHd CDObj))
           (= (CDLL_restore n CDObj) CDObj)))


(defthm restore-n-prev-next-not-loop--thm
  (implies
   (and (not (= (ag 'prev (ag n (ag 'nodeArr CDObj))) n))
        (not (= (ag 'next (ag n (ag 'nodeArr CDObj))) n)))
   (= (ag n (ag 'nodeArr (cdll_restore n CDObj)))
      (ag n (ag 'nodeArr CDObj)))))


(defthm restore-n-prev-next-both-loop--thm
 (implies
  (and (= (ag 'prev (ag n (ag 'nodeArr CDObj))) n)
       (= (ag 'next (ag n (ag 'nodeArr CDObj))) n))
  (= (ag n (ag 'nodeArr (cdll_restore n CDObj)))
     (ag n (ag 'nodeArr CDObj)))))


(defthm ln-of-restore-of-remove--thm
  (implies
   (and (cdllp CDObj)
        (integerp n) (<= 0 n) (<= n (CDLL_MAX_NODE))
        (not (= n (ag 'nodeHd CDObj)))
        (< 2 (ag 'nodeCount CDObj)))
   (= (cdll_ln (cdll_restore n (cdll_remove n CDObj))) (cdll_ln CDObj))))


(defthm restore-of-remove-n-n-too-big--thm
   (implies
    (> n (CDLL_MAX_NODE))
    (= (cdll_restore n (cdll_remove n CDObj)) CDObj)))


(defthm restore-of-remove-not-enough-elements--thm
  (implies (< (ag 'nodeCount CDObj) 2)
           (= (cdll_restore n (cdll_remove n CDObj)) CDObj)))

(defthm restore-of-remove-of-nodeHd--thm
  (implies (= n (ag 'nodeHd CDObj))
           (= (cdll_restore n (cdll_remove n CDObj)) CDObj)))


(defthm remove-n--thm
  (= (ag n (ag 'nodeArr (cdll_remove n CDObj)))
     (ag n (ag 'nodeArr CDObj)))
  :hints (("Goal" :cases ((and (not (= (ag 'prev (ag n (ag 'nodeArr CDObj))) n))
                               (not (= (ag 'next (ag n (ag 'nodeArr CDObj))) n)))
                          (and (not (= (ag 'prev (ag n (ag 'nodeArr CDObj))) n))
                               (= (ag 'next (ag n (ag 'nodeArr CDObj))) n))
                          (and (= (ag 'prev (ag n (ag 'nodeArr CDObj))) n)
                               (not (= (ag 'next (ag n (ag 'nodeArr CDObj))) n)))
                          (and (= (ag 'prev (ag n (ag 'nodeArr CDObj))) n)
                               (= (ag 'next (ag n (ag 'nodeArr CDObj))) n))))))


(defthm restore-of-remove--thm
  (implies
   (and (cdllp CDObj)
        (good-node-prev-nextp (ag 'nodeCount CDObj) n (ag 'nodeArr CDObj))
        (not (= n (ag 'nodeHd CDObj)))
        (>= (ag 'nodeCount CDObj) 3))
   (= (cdll_restore n (cdll_remove n CDObj))
      CDObj)))
