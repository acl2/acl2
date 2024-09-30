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

(in-package "RTL")

(include-book "rtl/rel11/lib/rac" :dir :system)

(include-book "std/lists/update-nth" :dir :system)

(include-book "data-structures/list-defthms" :dir :system)

(include-book "rtl/rel11/lib/bits" :dir :system)

(include-book "bits-thms")

(include-book "arithmetic-5/top" :dir :system)


(defthmd integerp-forward-to-rationalp--thm
  (implies (integerp x)
           (rationalp x))
  :rule-classes ((:forward-chaining :trigger-terms ((integerp x))) :rewrite))

(defthmd integerp-forward-to-acl2-numberp--thm
  (implies (integerp x)
           (acl2-numberp x))
  :rule-classes ((:forward-chaining :trigger-terms ((integerp x))) :rewrite))


;; From RAC book
;; (DEFTHM AS-SAME-AG (EQUAL (AS A (AG A R) R) R))

(defthm as-ag-same--thm
  (implies (= (ag k r) n)
           (= (as k n r) r)))


(defthm arcdp-true-listp--thm
  (implies (arcdp lst)
           (true-listp lst))
  :rule-classes ((:forward-chaining :trigger-terms ((arcdp lst))) :rewrite))

;; From rtl/rel11/support/rac.lisp

(defthm as-aux-is-bounded
  (implies
   (and (arcdp r)
        (as-aux a v r)
        (acl2::<< e a)
        (acl2::<< e (caar r)))
   (acl2::<< e (caar (as-aux a v r)))))

(defthm as-aux-preserves-arcdp--thm
  (implies (arcdp r)
           (arcdp (as-aux a v r))))


;; Accumulated Persistence
(defthmd not-aifrp-means-arcdp--thm
  (implies (not (aifrp x))
           (arcdp x)))

;; AP
(defthmd arcdp-len-gt-1-not-aifrp--thm
  (implies
   (and (arcdp x)
        (cdr x))
   (not (aifrp x))))

(defthmd arcdp-len-eq-1-not-aifrp--thm
  (implies
   (and (arcdp x)
        ;; (consp x)
        ;; (not (cdr x))
        (not (= (cdr (car x)) (aifrp-tag))))
   (not (aifrp x))))

(defthmd null-not-aifrp--thm
  (implies (null x)
           (not (aifrp x))))

(defthmd arcdp-not-aifrp--thm
  (implies
   (and (arcdp x)
        (not (= (cdr (car x)) (aifrp-tag))))
   (not (aifrp x))))


(defthmd arcdp-acl2->arcd--thm
  (implies
   (and (arcdp x)
        (not (= (cdr (car x)) (aifrp-tag))))
   (= (acl2->arcd x) x)))

(defthmd arcdp-arcd->acl2--thm
  (implies
   (and (arcdp x)
        (not (= (cdr (car x)) (aifrp-tag))))
   (= (arcd->acl2 x) x)))


;; AP  
(defthmd as-preserves-arcdp--thm
  (implies
   (and (arcdp r)
        (not (= (cdr (car r)) (aifrp-tag)))
        (not (= (cdr (cadr r)) (aifrp-tag)))
        (not (= v (aifrp-tag))))
   (arcdp (as a v r)))
  :hints (("Goal" :in-theory (e/d (as) ()))))


(defthmd arcdp-nil--thm
  (arcdp nil))


(defthm <<-nil-means-not-consp--thm
  (implies (acl2::<< a nil)
           (not (consp a)))
  :hints (("Goal" :in-theory (e/d (acl2::<< lexorder alphorder) ()))))


(defthmd len-eq-1-ag-not-eq-default-get-valu-means-ag-is-cdr-car--thm
  (implies
   (and (acl2::<< a nil)
        ;; (null (cdr r))
        (not (= (ag a r) (DEFAULT-GET-VALU))))
   (not (= (cdr (car r)) (DEFAULT-GET-VALU))))
  :hints (("Goal" :in-theory (e/d (ag) ()))))


(defthmd len-eq-1-cdar-not-eq-default-get-valu-means-arcdp--thm
  (implies
   (and (consp (car r))
        (null (cdr r))
        (not (equal (cdar r) (default-get-valu))))
   (arcdp r)))

(defthmd len-eq-1-ag-not-eq-default-get-valu-means-consp-car--thm
  (implies
   (and (acl2::<< a nil)
        (consp r)
        (null (cdr r))
        (not (= (ag a r) (default-get-valu))))
   (consp (car r)))
  :hints (("Goal" :in-theory (e/d (ag) nil))))


(DEFTHMD LEN-EQ-1-AG-NOT-EQ-DEFAULT-GET-VALU-MEANS-ARCDP--THM
  (IMPLIES
   (AND (ACL2::<< A NIL)
        (CONSP R)
        (NULL (CDR R))
        (NOT (= (AG A R) (DEFAULT-GET-VALU))))
   (ARCDP R))
 :INSTRUCTIONS
 (:PROMOTE
  (:CLAIM
   (CONSP (CAR R))
   :HINTS (("Goal" :USE (:INSTANCE LEN-EQ-1-AG-NOT-EQ-DEFAULT-GET-VALU-MEANS-CONSP-CAR--THM))))
  (:CLAIM
   (NOT (= (CDR (CAR R)) (DEFAULT-GET-VALU)))
   :HINTS (("Goal" :USE (:INSTANCE LEN-EQ-1-AG-NOT-EQ-DEFAULT-GET-VALU-MEANS-AG-IS-CDR-CAR--THM))))
  (:REWRITE LEN-EQ-1-CDAR-NOT-EQ-DEFAULT-GET-VALU-MEANS-ARCDP--THM)))


(defthm one-ag-ne-default-true-listp--thm
  (implies
   (and (not (= (ag a r) (default-get-valu)))
        (not (= (ag a r) (aifrp-tag))))
   (true-listp r))
  :hints (("Goal" :in-theory (e/d (ag) ()))))

;; AP
(defthmd one-ag-ne-default-consp--thm
  (implies
   (and (not (= (ag a r) (default-get-valu)))
        (not (= (ag a r) (aifrp-tag))))
   (consp r))
  :hints (("Goal" :in-theory (e/d (ag) ()))))

(defthm one-ag-ne-default-arcdp--thm
  (implies
   (and (not (= (ag a r) (default-get-valu)))
        (not (= (ag a r) (aifrp-tag))))
   (arcdp r))
  :hints (("Goal" :in-theory (e/d (ag) ()))))


(defthm two-ag-ne-default-true-listp--thm
  (implies
   (and (not (= (ag a r) (default-get-valu)))
        (not (= (ag b r) (default-get-valu)))
        (not (= a b)))
   (true-listp r))
  :hints (("Goal" :in-theory (e/d (ag)))))

(defthmd two-ag-ne-default-consp--thm
  (implies
   (and (not (= (ag a r) (default-get-valu)))
        (not (= (ag b r) (default-get-valu)))
        (not (= a b)))
   (consp r))
  :hints (("Goal" :in-theory (e/d (ag)))))

(defthmd two-ag-ne-default-len-gt-1--thm
  (implies
   (and (not (= (ag a r) (default-get-valu)))
        (not (= (ag b r) (default-get-valu)))
        (not (= a b)))
   (cdr r))
  :hints (("Goal" :in-theory (e/d (ag)))))


(defthm two-ag-ne-default-arcdp--thm
  (implies
   (and (not (= (ag a r) (default-get-valu)))
        (not (= (ag b r) (default-get-valu)))
        (not (= a b)))
   (arcdp r))
  :hints (("Goal" :in-theory (e/d (ag)))))


(defthmd ag-ne-default-get-valu-len-gt-2--thm
  (implies
   (and (not (= (ag a r) (default-get-valu)))
        (not (= (ag b r) (default-get-valu)))
        (not (= (ag c r) (default-get-valu)))
        (not (= a b)) (not (= a c))
        (not (= b c)))
   (cdr (cdr r)))
  :hints (("Goal" :in-theory (e/d (ag)))))


(defthm arcdp-len-gt-1-ag-ne-default-get-valu--thm
  (implies
   (and (arcdp lst)
        (cdr lst)
        (integerp k) (<= 0 k) (< k (len lst)))
   (not (= (ag (car (nth k lst)) lst) (default-get-valu))))
  :hints (("Goal" :in-theory (e/d (ag) ()))))

(defthm arcdp-len-eq-1-ag-ne-default-get-valu--thm
  (implies
   (and (arcdp lst)
        (not (cdr lst))
        (integerp k) (<= 0 k) (< k (len lst))
        (not (equal (cdr (car lst)) (aifrp-tag))))
   (not (= (ag (car (nth k lst)) lst) (default-get-valu))))
  :hints (("Goal" :in-theory (e/d (ag) ()))))


(defthm arcdp-cdr-car-ne-aifrp-tag-ag-ne-default-get-valu--thm
  (implies
   (and (arcdp lst)
        (integerp k) (<= 0 k) (< k (len lst))
        (not (equal (cdr (car lst)) (aifrp-tag))))
   (not (= (ag (car (nth k lst)) lst) (default-get-valu))))
  :hints (("Goal" :cases ((not (cdr lst)) (cdr lst)))
          ("Subgoal 2" :use (:instance arcdp-len-eq-1-ag-ne-default-get-valu--thm))
          ("Subgoal 1" :use (:instance arcdp-len-gt-1-ag-ne-default-get-valu--thm))))


(defthm ag-i-ne-ag-j-means-i-ne-j--thm
 (implies (not (= (ag i lst) (ag j lst)))
          (not (= i j)))
:hints (("Goal" :in-theory (e/d (ag) ()))))


(DEFTHMD ARCDP-AG-KEY-EQ-DEFAULT-GET-VALU-NE-CAR-NTH--THM
  (IMPLIES
   (AND (ARCDP LST)
        (INTEGERP K) (<= 0 K) (< K (LEN LST))
        (NOT (EQUAL (CDR (CAR LST)) (AIFRP-TAG)))
        (= (AG KEY LST) (DEFAULT-GET-VALU)))
   (NOT (= (CAR (NTH K LST)) KEY)))
  :INSTRUCTIONS
  (:PROMOTE
   (:CLAIM (NOT (= (AG (CAR (NTH K LST)) LST) (DEFAULT-GET-VALU)))
           :HINTS (("Goal" :USE (:INSTANCE ARCDP-CDR-CAR-NE-AIFRP-TAG-AG-NE-DEFAULT-GET-VALU--THM))))
   (:PROVE :HINTS (("Goal" :USE (:INSTANCE AG-I-NE-AG-J-MEANS-I-NE-J--THM
                                            (I (CAR (NTH K LST)))
                                            (J KEY)))))))


(defthm arcdp-ag-car-car-eq-cdr-car--thm
  (implies
   (and (arcdp lst)
        (cdr lst))
   (= (ag (car (car lst)) lst) (cdr (car lst))))
  :hints (("Goal" :in-theory (e/d (ag) ()))))


(defthm nth-of-cdr--thm
  (implies
   (and (integerp x)
        (<= 0 x))
   (= (nth x (cdr lst)) (nth (1+ x) lst))))


(defthm arcdp-cdr-nth-ne-default-get-valu--thm
  (implies (arcdp lst)
           (not (= (cdr (nth k lst)) (default-get-valu)))))


(DEFTHMD ARCDP-LEN-GT-1-AG-KEY-IS-CDR-OF-NTH-AUX-1--THM
  (IMPLIES
   (AND (CONSP LST)
        (NOT (ZP K))
        (CDDR LST)
        (EQUAL 0 (CDR (NTH K LST)))
        (CONSP (CAR LST))
        (CONSP (CDR LST))
        (CONSP (CADR LST))
        (ARCDP (CDDR LST))
        (NOT (EQUAL (CDR (CADR LST)) 0))
        (ACL2::<< (CAR (CADR LST))
                  (CAR (CADDR LST)))
        (NOT (EQUAL (CDR (CAR LST)) 0))
        (ACL2::<< (CAR (CAR LST))
                  (CAR (CADR LST)))
        (CDR LST)
        (< K (+ 2 (LEN (CDDR LST)))))
   (NOT (EQUAL (CAR (NTH K LST))
               (CAR (CAR LST)))))
   :INSTRUCTIONS
   (:PROMOTE
    (:CLAIM (ARCDP LST))
    (:CLAIM (NOT (= (CDR (NTH K LST)) 0))
            :HINTS (("Goal" :USE (:INSTANCE ARCDP-CDR-NTH-NE-DEFAULT-GET-VALU--THM))))
    :BASH))

(DEFTHMD ARCDP-LEN-GT-1-AG-KEY-IS-CDR-OF-NTH-AUX-2--THM
  (IMPLIES
   (AND (CONSP LST)
        (NOT (ZP K))
        (NOT (EQUAL (CDR (CADR LST))
                    (AIFRP-TAG)))
        (EQUAL 0 (CDR (NTH K LST)))
        (CONSP (CAR LST))
        (ARCDP (CDR LST))
        (NOT (EQUAL (CDR (CAR LST)) 0))
        (ACL2::<< (CAR (CAR LST))
                  (CAR (CADR LST)))
        (CDR LST)
        (< K (+ 1 (LEN (CDR LST)))))
   (NOT (EQUAL (CAR (NTH K LST))
               (CAR (CAR LST)))))
 :INSTRUCTIONS
 (:PROMOTE
  (:CLAIM (ARCDP LST))
  (:CLAIM (NOT (= (CDR (NTH K LST)) 0))
          :HINTS (("Goal" :USE (:INSTANCE ARCDP-CDR-NTH-NE-DEFAULT-GET-VALU--THM))))
  :BASH))

(DEFTHMD ARCDP-LEN-GT-1-AG-KEY-IS-CDR-OF-NTH-AUX-3--THM
  (IMPLIES
   (AND (CONSP LST)
        (NOT (ZP K))
        (NOT (AIFRP (CAR (CADR LST))))
        (EQUAL 0 (CDR (NTH K LST)))
        (CONSP (CAR LST))
        (ARCDP (CDR LST))
        (NOT (EQUAL (CDR (CAR LST)) 0))
        (ACL2::<< (CAR (CAR LST))
                  (CAR (CADR LST)))
        (CDR LST)
        (< K (+ 1 (LEN (CDR LST)))))
   (NOT (EQUAL (CAR (NTH K LST))
               (CAR (CAR LST)))))
   :INSTRUCTIONS
   (:PROMOTE
    (:CLAIM (ARCDP LST))
    (:CLAIM (NOT (= (CDR (NTH K LST)) 0))
            :HINTS (("Goal" :USE (:INSTANCE ARCDP-CDR-NTH-NE-DEFAULT-GET-VALU--THM))))
    :BASH))

(defthm arcdp-len-gt-1-ag-key-is-cdr-of-nth--thm
  (implies
   (and (arcdp lst)
        (cdr lst)
        (integerp k) (<= 0 k) (< k (len lst)))
   (= (ag (car (nth k lst)) lst) (cdr (nth k lst))))
  :hints (("Goal" :in-theory (e/d (ag) ()))
          ("Subgoal *1/3.1.3" :use (:instance ARCDP-LEN-GT-1-AG-KEY-IS-CDR-OF-NTH-AUX-1--THM))
          ("Subgoal *1/3.1.2" :use (:instance ARCDP-LEN-GT-1-AG-KEY-IS-CDR-OF-NTH-AUX-2--THM))
          ("Subgoal *1/3.1.1" :use (:instance ARCDP-LEN-GT-1-AG-KEY-IS-CDR-OF-NTH-AUX-3--THM))))


(defthm arcdp-len-gt-1-ag-key-eq-default-get-valu-ne-car-nth--thm
  (implies
   (and (arcdp lst)
        (integerp k)
        (<= 0 k)
        (< k (len lst))
        (cdr lst)
        (= (ag key lst) (default-get-valu)))
   (not (= (car (nth k lst)) key))))


(defthm len-eq-1-ag-car-of-car-is-cdr-of-car--thm
  (implies
   (and (not (cdr lst))
        (consp (car lst))
        (not (equal (cdr (car lst)) (aifrp-tag))))
   (= (ag (car (car lst)) lst) (cdr (car lst))))
  :hints (("Goal" :in-theory (e/d (ag) ()))))


(defthm arcdp-ag-key-is-cdr-of-nth--thm
  (implies
   (and (arcdp lst)
        (not (equal (cdr (car lst)) (aifrp-tag)))
        (integerp k) (<= 0 k) (< k (len lst)))
   (= (ag (car (nth k lst)) lst) (cdr (nth k lst))))
  :hints (("Goal" :cases ((null lst) (not (cdr lst)) (cdr lst)))))


(defthmd ag-atom-a-r-last-r-<<-a--thm
  (implies
   (and (arcdp r)
        (atom a)
        (acl2::<< (caar (last r)) a))
   (equal (ag a r) (default-get-valu)))
  :hints (("Goal" :in-theory (e/d (ag) ()))))

(defthmd nth-len-minus-1-eq-car-last--thm
  (implies (true-listp lst)
           (= (nth (1- (len lst)) lst) (car (last lst)))))


(DEFTHMD AG-ATOM-A-R-NTH-LEN-MINUS-1-R-<<-A--THM
  (IMPLIES
   (AND (ARCDP R)
        (ATOM A)
        (ACL2::<< (CAR (NTH (1- (LEN R)) R)) A))
   (EQUAL (AG A R) (DEFAULT-GET-VALU)))
 :INSTRUCTIONS
 (:PROMOTE
   (:CLAIM (= (NTH (1- (LEN R)) R) (CAR (LAST R)))
           :HINTS (("Goal" :USE (:INSTANCE NTH-LEN-MINUS-1-EQ-CAR-LAST--THM
                                            (LST R)))))
   (:PROVE :HINTS (("Goal" :USE (:INSTANCE AG-ATOM-A-R-LAST-R-<<-A--THM))))))


(defthm arcdp-as-k-is-update-nth-k--thm
  (implies
   (and (arcdp lst)
        (not (= v (default-get-valu)))
        (integerp k) (<= 0 k) (< k (len lst))
        (atom (car (nth k lst)))
        ;; Instead of the two hyps above, could just be the following:
        ;;(consp v)
        (not (equal v (aifrp-tag)))
        (NOT (EQUAL (CDR (NTH K LST)) (aifrp-tag))))
   (= (as (car (nth k lst)) v lst) (update-nth k (cons (car (nth k lst)) v) lst)))
  :hints (("Goal" :in-theory (e/d (as) ()))))
