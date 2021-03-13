; Copyright (C) 2020 David S. Hardin
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


(in-package "RTL")

(include-book "stk")

(include-book "rtl/rel11/lib/bits" :dir :system)

(include-book "std/lists/update-nth" :dir :system)

(include-book "data-structures/list-defthms" :dir :system)

(include-book "arithmetic-5/top" :dir :system)

(defconst *STK_EXP* 14)
(defconst *STK_MSB* (1- *STK_EXP*))
(defconst *STK_VAL_EXP* 63)
(defconst *STK_MAX_SZ* (1- (expt 2 *STK_EXP*)))           ;; 16383
(defconst *STK_MAX_NODE* (1- *STK_MAX_SZ*))               ;; 16382
(defconst *STK_MIN_VAL* (- (expt 2 *STK_VAL_EXP*)))          ;; -2**63
(defconst *STK_MAX_VAL* (1- (expt 2 *STK_VAL_EXP*)))         ;; (2**63 - 1)

(defthmd integerp-forward-to-rationalp--thm
  (implies (integerp x)
           (rationalp x))
  :rule-classes ((:forward-chaining :trigger-terms ((integerp x))) :rewrite))

(defthmd integerp-forward-to-acl2-numberp--thm
  (implies (integerp x)
           (acl2-numberp x))
  :rule-classes ((:forward-chaining :trigger-terms ((integerp x))) :rewrite))

(DEFTHM BITS-UPPER-BOUND-LE
 (IMPLIES (AND (INTEGERP I) (INTEGERP J) (<= 0 I) (>= i j))
          (<= (BITS X I j) (1- (EXPT 2 (1+ (- I J))))))
 :INSTRUCTIONS
 (:PROMOTE (:CLAIM (INTEGERP (EXPT 2 (1+ (- I J)))))
           (:CLAIM (< (BITS X I J) (EXPT 2 (1+ (- I J))))
                   :HINTS (("Goal" :USE (:INSTANCE BITS-UPPER-BOUND))))
           :BASH)
  :rule-classes ((:forward-chaining :trigger-terms ((BITS X I J))) :rewrite))

(DEFTHM BITS-ELIM--THM
  (IMPLIES
   (AND
    (INTEGERP X)
    (INTEGERP I)
    (<= 0 I)
    (<= 0 X)
    (< X (EXPT 2 (1+ I))))
   (EQUAL (BITS X I 0) X))
  :hints (("Goal" :in-theory (e/d (bits-mod) ()))))


;; STK theorems

(defun stknodeArrp (arr)
  (or (null arr)
      (and (integerp (cdr (car arr)))
           (>= (cdr (car arr)) *STK_MIN_VAL*)
           (<= (cdr (car arr)) *STK_MAX_VAL*)
           (stknodeArrp (cdr arr)))))

(defthm stknodeArr-true-listp--thm
  (implies (stknodeArrp arr)
           (true-listp arr)))

(defun stkp (Obj)
  (and (consp Obj)
       (integerp (ag 'nodeTop Obj))
       (<= 0 (ag 'nodeTop Obj))
       (<= (ag 'nodeTop Obj) *STK_MAX_SZ*)
       (stknodeArrp (ag 'nodeArr Obj))
       (<= (len (ag 'nodeArr Obj)) *STK_MAX_SZ*)))


(defun spacep (Obj)
  (> (ag 'nodeTop Obj) 0))

(defthm bitn-eq-0--thm
  (implies
   (AND (INTEGERP R) (integerp N)
        (>= r 0)
        (< r (expt 2 n)))
   (= (bitn r n) 0))
  :hints (("Goal" :in-theory (e/d (bitn bvecp) ()))))

(in-theory (enable stk_sz stk_pop stk_top stk_push))

(defthm STK_top-no-err--thm
  (implies
   (and
    (stkp Obj)
    (< (ag 'nodeTop Obj) *STK_MAX_SZ*))
   (= (nth 0 (STK_top Obj)) 0)))

(defthm STK_top-err--thm
  (implies
   (and
    (stkp Obj)
    (= (ag 'nodeTop Obj) *STK_MAX_SZ*))
   (not (= (nth 0 (STK_top Obj)) 0))))


(defthm STK_top-of-STK_push-no-err--thm
  (implies
   (and
    (stkp Obj)
    (spacep Obj)
    (acl2::signed-byte-p 64 n))
   (= (nth 0 (STK_top (STK_push n Obj))) 0)))

(defthm STK_top-of-STK_push-val--thm
  (implies
   (and
    (stkp Obj)
    (spacep Obj)
    (acl2::signed-byte-p 64 n))
   (= (nth 1 (STK_top (STK_push n Obj))) n)))


(defthm stk_sz-of-STK_push--thm
  (implies
   (and
    (stkp Obj)
    (spacep Obj)
    (acl2::signed-byte-p 64 n))
   (= (stk_sz (STK_push n Obj))
      (1+ (stk_sz Obj)))))


(defthm stk_sz-of-STK_pop--thm
  (implies
   (and
    (stkp Obj)
    (< 0 (stk_sz Obj)))
   (= (stk_sz (STK_pop Obj)) (1- (stk_sz Obj)))))

;;;

(defthm STK_top-of-STK_pop-of-STK_push-err-val--thm
  (implies
   (and
    (stkp Obj)
    (spacep Obj)
    (acl2::signed-byte-p 64 n))
   (= (nth 0 (STK_top (STK_pop (STK_push n Obj)))) (nth 0 (STK_top Obj)))))

(defthm STK_top-of-STK_pop-of-STK_push-val--thm
  (implies
   (and
    (stkp Obj)
    (spacep Obj)
    (acl2::signed-byte-p 64 n))
   (= (nth 1 (STK_top (STK_pop (STK_push n Obj)))) (nth 1 (STK_top Obj)))))
