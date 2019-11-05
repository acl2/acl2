; Hash Tables in Stobjs
; Copyright (C) 2008-2015 Centaur Technology
;
; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/
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
;
; Original author: Sol Swords <sswords@centtech.com>

; Matt K. comment, 10/31/2019:
; This book originally contained support for stobjs with hash table members.
; That support is now part of ACL2, but parts of the original book remain here,
; including many comments, reasoning support, and some tests.  After moving
; (and tweaking) ACL2 source code modes from this book into the ACL2 sources, I
; left the rest of this book essentially unchanged, other than adding tests at
; the end for EQ and HONS-EQUAL hash tables (to the existing tests for EQL and
; EQUAL hash tables).

(in-package "ACL2")

(include-book "std/alists/hons-remove-assoc" :dir :system)

;; To extend the example used in defstobj:

#|


(defstobj $st
    (flag :type t :initially run)
    (pctr   :type (integer 0 255) :initially 128)
    (mem  :type (array (integer 0 255) (256)) :initially 0)
    (tab :type (hash-table eql)))

(defstobj equalht
  (equaltab :type (hash-table equal)))

(defstobj hons-equalht
  (hons-equaltab :type (hash-table hons-equal)))



|#

;; Since array members are represented by lists, we'll represent hash
;; table members as alists, as illustrated below.

;; Is this sound?  See the theorems proven below about the
;; interactions of the logical definitions of the access and update
;; functions.  I argue that these theorems are exactly the contract of
;; a hash table (provided that the inputs are well-formed,
;; i.e. EQLABLE for an EQL table, etc).  If this is the case, then
;; this is only unsound in the event that the underlying Lisp has a
;; bug in its hash table implementation.

;; We make guards on these functions as weak as possible since they
;; have nothing to do with the performance in raw Lisp, and arguably
;; we care more about ease of proving guard conjectures than we do
;; about how well they perform in the logic.

(defthm hons-remove-assoc-acl2-count-weak
  (<= (acl2-count (hons-remove-assoc x al)) (acl2-count al))
  :rule-classes :linear)

(defthm not-assoc-hons-remove-assoc
  (not (hons-assoc-equal k (hons-remove-assoc k al))))

(defthm assoc-hons-remove-assoc-diff
  (implies (not (equal j k))
           (equal (hons-assoc-equal k (hons-remove-assoc j al))
                  (hons-assoc-equal k al))))

(defthm hons-remove-assoc-repeat
  (equal (hons-remove-assoc k (hons-remove-assoc k al))
         (hons-remove-assoc k al)))

(local (include-book "arithmetic/top-with-meta" :dir :system))

(defthm count-keys-hons-remove-assoc
  (equal (count-keys (hons-remove-assoc k al))
         (if (consp (hons-assoc-equal k al))
             (1- (count-keys al))
           (count-keys al))))

(defthm count-keys-cons
  (equal (count-keys (cons (cons k v) al))
         (if (consp (hons-assoc-equal k al))
             (count-keys al)
           (+ 1 (count-keys al)))))


#||

;; Using this example stobj definition, we'll illustrate the logical
;; definitions of the functions used to access and update the table.

(defstobj htable
  (tab :type (hash-table eql))) ;; or (hash-table equal)

(defun tabp
  (declare (xargs :guard t))
  ;; Because we made the guards on hons-assoc-equal and hons-remove-assoc T, we
  ;; don't need to constrain what tabp is logically.
  t)

(defun htablep (x)
  (declare (xargs :guard t))
  (true-listp x))

;; CREATE-HTABLE:
(defun create-htable ()
  (declare (xargs :guard t))
  (list nil))

;; GET, logic:
(defun tab-get (k htable)
  (declare (xargs :guard (and (htablep htable)
                              ;; eqlablep only in EQL version
                              (eqlablep k))))
  (cdr (hons-assoc-equal k (nth 0 htable))))

;; BOUNDP, logic:
(defun tab-boundp (k htable)
  (declare (xargs :guard (and (htablep htable)
                              ;; eqlablep only in EQL version
                              (eqlablep k))))
  (consp (hons-assoc-equal k (nth 0 htable))))

;; GET?, logic:
(defun tab-get? (k htable)
  (declare (xargs :guard (and (htablep htable)
                              ;; eqlablep only in EQL version
                              (eqlablep k))))
  (mv (tab-get k htable)
      (tab-boundp k htable)))

;; PUT, logic:
(defun tab-put (k v htable)
  (declare (xargs :guard (and (htablep htable)
                              ;; eqlablep only in EQL version
                              (eqlablep k))))
  (update-nth 0 (cons (cons k v)
                      (nth 0 htable)) htable))

;; REM, logic:
(defun tab-rem (k htable)
  (declare (xargs :guard (and (htablep htable)
                              ;; eqlablep only in EQL version
                              (eqlablep k))))
  (update-nth 0 (hons-remove-assoc k (nth 0 htable)) htable))

;; COUNT, logic:
(defun tab-count (htable)
  (count-keys (nth 0 htable)))

;; CLEAR, logic:
(defun tab-clear (htable)
  (declare (xargs :guard (htablep htable)))
  (update-nth 0 nil htable))

(defun tab-init (size rehash-size rehash-threshold htable)
  (declare (xargs :guard (and (htablep htable)
                              (or (natp size)
                                  (not size))
                              (or (and (rationalp rehash-size)
                                       (< 1 rehash-size))
                                  (not rehash-size))
                              (or (and (rationalp rehash-threshold)
                                       (<= 0 rehash-threshold)
                                       (<= rehash-threshold 1))
                                  (not rehash-threshold)))))
  (declare (ignore size rehash-size rehash-threshold))
  (update-nth 0 nil htable))

;; Theorems about the interactions of the functions above: Our
;; approach is sound if these theorems completely and accurately model
;; the functionality of a Common Lisp hash table, modulo assumptions
;; about what keys are allowed.  We can argue that these are complete
;; since we can completely specify the values of any of the accessors
;; (tab-get, tab-boundp, tab-count) on any nesting of the updaters
;; (tab-put, tab-rem), by induction:
;; Base case 1: empty table; tab-get and tab-boundp both return nil.
;; Base case 2: (tab-put k v htable), where k is the key being
;; searched for:  tab-get returns v, tab-boundp returns t.
;; Base case 3: (tab-rem k htable), where k is the key being searched
;; for: tab-get and tab-boundp again both return nil.
;; Base case 4: (tab-clear htable): both return nil.
;; Induction case 1: (tab-put j v htable), j not equal k, reduces to
;; access of htable,
;; Induction case 2: (tab-rem j htable), j not equal k, reduces to
;; access of htable.

(defthm tab-init-is-tab-clear
  (equal (tab-init size rehash-size rehash-threshold htable)
         (tab-clear htable)))

(defthm tab-get-tab-boundp
  (implies (tab-get k htable)
           (tab-boundp k htable)))

(defthm tab-boundp-start
  (not (tab-boundp k (create-htable))))

(defthm tab-boundp-clear
  (not (tab-boundp k (tab-clear htable))))

(defthm tab-boundp-tab-put-same
  (tab-boundp k (tab-put k v htable)))

(defthm tab-boundp-tab-put-diff
  (implies (not (equal j k))
           (equal (tab-boundp k (tab-put j v htable))
                  (tab-boundp k htable))))

(defthm tab-get-tab-put-same
  (equal (tab-get k (tab-put k v htable))
         v))

(defthm tab-get-tab-put-diff
  (implies (not (equal j k))
           (equal (tab-get k (tab-put j v htable))
                  (tab-get k htable))))

(defthm tab-rem-tab-boundp-same
  (not (tab-boundp k (tab-rem k htable))))

(defthm tab-rem-tab-boundp-diff
  (implies (not (equal j k))
           (equal (tab-boundp k (tab-rem j htable))
                  (tab-boundp k htable))))

(defthm tab-rem-tab-get-diff
  (implies (not (equal j k))
           (equal (tab-get k (tab-rem j htable))
                  (tab-get k htable))))

(defthm tab-count-start
  (equal (tab-count (create-htable)) 0))

(defthm tab-count-put
  (equal (tab-count (tab-put k v htable))
         (if (tab-boundp k htable)
             (tab-count htable)
           (+ 1 (tab-count htable)))))

(defthm tab-count-rem
  (equal (tab-count (tab-rem k htable))
         (if (tab-boundp k htable)
             (- (tab-count htable) 1)
           (tab-count htable))))

(defthm tab-count-clear
  (equal (tab-count (tab-clear htable)) 0))

;; CREATE-HTABLE, raw:
(defun create-htable ()
  (vector (make-hash-table :test 'eql)))

;; GET, raw:
(defun tab-get (k htable)
  ;; Replace K with (HONS-COPY K) in HONS-EQUAL version
  (values (gethash k
                   (svref htable 0))))
;; BOUNDP, raw:
(defun tab-boundp (k htable)
  (multiple-value-bind (ans boundp)
      ;; Replace K with (HONS-COPY K) in HONS-EQUAL version
      (gethash k (svref htable 0))
    (declare (ignore ans))
    boundp))
;; GET?, raw:
(defun tab-get? (k htable)
  ;; Replace K with (HONS-COPY K) in HONS-EQUAL version
  (gethash k (svref htable 0)))

;; PUT, raw:
(defun tab-put (k v htable)
  ;; Replace K with (HONS-COPY K) in HONS-EQUAL version
  (setf (gethash k (svref htable 0)) v)
  htable)

;; REM, raw:
(defun tab-rem (k htable)
  ;; replace K with (HONS-COPY K) in HONS-EQUAL version
  (remhash k (svref htable 0))
  htable)

;; COUNT, raw:
(defun tab-count (htable)
  (hash-table-count (svref htable 0)))

(defun tab-clear (htable)
  (clrhash (svref htable 0))
  htable)

(defun tab-init (size rehash-size rehash-threshold htable)
  (setf (svref htable 0)
        (make-hash-table
         :size (or size 60)
         :rehash-size (if rehash-size
                          (float rehash-size)
                        (float 17/10))
         :rehash-threshold (if rehash-threshold
                               (float rehash-threshold)
                             (float 3/4))))
  htable)

||#

;; Macro for proving theorems like the ones above about a hash field:

(defmacro prove-ht-theorems (field stobj &optional renaming)
  (let ((get (defstobj-fnname field :accessor :hash-table renaming))
        (boundp (defstobj-fnname field :boundp :hash-table renaming))
        (put (defstobj-fnname field :updater :hash-table renaming))
        (rem (defstobj-fnname field :remove :hash-table renaming))
        (count (defstobj-fnname field :count :hash-table renaming))
        (clear (defstobj-fnname field :clear :hash-table renaming))
        (init (defstobj-fnname field :init :hash-table renaming))
        (make (defstobj-fnname stobj :creator :hash-table renaming)))
    `(progn
       (defthm ,(packn-pos (list field "-INIT-IS-CLEAR") field)
         (equal (,init size rehash-size rehash-threshold ,stobj)
                (,clear ,stobj)))

       (defthm ,(packn-pos (list field "-GET-BOUNDP") field)
         (implies (,get k ,stobj)
                  (,boundp k ,stobj)))

       (defthm ,(packn-pos (list field "-BOUNDP-START") field)
         (not (,boundp k (,make))))

       (defthm ,(packn-pos (list field "-BOUNDP-CLEAR") field)
         (not (,boundp k (,clear ,stobj))))

       (defthm ,(packn-pos (list field "-BOUNDP-PUT-SAME") field)
         (,boundp k (,put k v ,stobj)))

       (defthm ,(packn-pos (list field "-BOUNDP-PUT-DIFF") field)
         (implies (not (equal j k))
                  (equal (,boundp k (,put j v ,stobj))
                         (,boundp k ,stobj))))

       (defthm ,(packn-pos (list field "-GET-PUT-SAME") field)
         (equal (,get k (,put k v ,stobj))
                v))

       (defthm ,(packn-pos (list field "-GET-PUT-DIFF") field)
         (implies (not (equal j k))
                  (equal (,get k (,put j v ,stobj))
                         (,get k ,stobj))))

       (defthm ,(packn-pos (list field "-REM-BOUNDP-SAME") field)
         (not (,boundp k (,rem k ,stobj))))

       (defthm ,(packn-pos (list field "-REM-BOUNDP-DIFF") field)
         (implies (not (equal j k))
                  (equal (,boundp k (,rem j ,stobj))
                         (,boundp k ,stobj))))

       (defthm ,(packn-pos (list field "-REM-GET-DIFF") field)
         (implies (not (equal j k))
                  (equal (,get k (,rem j ,stobj))
                         (,get k ,stobj))))

       (defthm ,(packn-pos (list field "-COUNT-START") field)
         (equal (,count (,make)) 0))

       (defthm ,(packn-pos (list field "-COUNT-PUT") field)
         (equal (,count (,put k v ,stobj))
                (if (,boundp k ,stobj)
                    (,count ,stobj)
                  (+ 1 (,count ,stobj)))))

       (defthm ,(packn-pos (list field "-COUNT-REM") field)
         (equal (,count (,rem k ,stobj))
                (if (,boundp k ,stobj)
                    (- (,count ,stobj) 1)
                  (,count ,stobj))))

       (defthm ,(packn-pos (list field "-COUNT-CLEAR") field)
         (equal (,count (,clear ,stobj))
                0)))))



(local
 (progn

   (defstobj bigstobj
     (bigarray :type (array (unsigned-byte 16) (100))
               :initially 0)
     (bighash :type (hash-table eql))
     (slowhash :type (hash-table equal))
     (eqhash :type (hash-table eq 70))
     (honshash :type (hash-table hons-equal))
     )

   (make-event
    (let* ((bigstobj (bighash-put 0 0 bigstobj))
           (bigstobj (slowhash-put (list 0) 0 bigstobj))
           (bigstobj (eqhash-put 'a 0 bigstobj))
           (bigstobj (honshash-put (list 0) 0 bigstobj)))
      (mv nil '(value-triple :invisible) state bigstobj)))

   (include-book "misc/assert" :dir :system)

   (assert! (equal (bighash-get 0 bigstobj) 0))
   (assert! (equal (slowhash-get '(0) bigstobj) 0))
   (assert! (equal (eqhash-get 'a bigstobj) 0))
   (assert! (equal (honshash-get '(0) bigstobj) 0))

   (defun init-stuff (n bigstobj state)
     (declare (xargs :stobjs (bigstobj state)
                     :verify-guards nil
                     :guard (natp n)))
     (if (zp n)
         (mv bigstobj state)
       (mv-let (rnd state) (random$ 10000 state)
         (let* ((bigstobj (update-bigarrayi n rnd bigstobj))
                (bigstobj (bighash-put n rnd bigstobj))
                (bigstobj (slowhash-put (list n) rnd bigstobj))
                (bigstobj (eqhash-put (packn (list 'a n)) rnd bigstobj))
                (bigstobj (honshash-put (list n) rnd bigstobj)))
           (init-stuff (- n 1) bigstobj state)))))

   (make-event
    (mv-let (bigstobj state)
      (init-stuff 99 bigstobj state)
      (mv nil '(value-triple :invisible) state bigstobj)))

   (assert! (equal (bighash-count bigstobj) 100))
   (assert! (equal (slowhash-count bigstobj) 100))
   (assert! (equal (eqhash-count bigstobj) 100))
   (assert! (equal (honshash-count bigstobj) 100))

   (make-event
    (let* ((bigstobj (slowhash-put (cons 1 2) 3 bigstobj))
           (bigstobj (slowhash-put (cons 1 2) 4 bigstobj))
           (bigstobj (honshash-put (cons 1 2) 3 bigstobj))
           (bigstobj (honshash-put (cons 1 2) 4 bigstobj)))
      (mv nil '(value-triple :invisible) state bigstobj)))

   (assert! (equal (slowhash-get (cons 1 2) bigstobj) 4))
   (assert! (equal (slowhash-count bigstobj) 101))
   (assert! (equal (honshash-get (cons 1 2) bigstobj) 4))
   (assert! (equal (honshash-count bigstobj) 101))



   (defun check-same (n bigstobj)
     (declare (xargs :stobjs (bigstobj)
                     :verify-guards nil
                     :guard (natp n)))
     (if (zp n)
         t
       (let ((expect (bigarrayi n bigstobj)))
         (and (equal (bighash-get n bigstobj) expect)
              (equal (slowhash-get (list n) bigstobj) expect)
              (equal (bighash-boundp n bigstobj) t)
              (equal (slowhash-boundp (list n) bigstobj) t)
              (equal (eqhash-boundp (packn (list 'a n)) bigstobj) t)
              (equal (honshash-boundp (list n) bigstobj) t)
              (equal (mv-list 2 (bighash-get? n bigstobj))
                     (list expect t))
              (equal (mv-list 2 (slowhash-get? (list n) bigstobj))
                     (list expect t))
              (equal (mv-list 2 (eqhash-get? (packn (list 'a n)) bigstobj))
                     (list expect t))
              (equal (mv-list 2 (honshash-get? (list n) bigstobj))
                     (list expect t))
              (check-same (- n 1) bigstobj)))))

   (assert! (check-same 99 bigstobj))

   (assert! (not (bighash-boundp 101 bigstobj)))
   (assert! (equal (mv-list 2 (bighash-get? 101 bigstobj)) (list nil nil)))

   (assert! (not (slowhash-boundp 101 bigstobj)))
   (assert! (equal (mv-list 2 (slowhash-get? 101 bigstobj)) (list nil nil)))

   (assert! (not (slowhash-boundp (list 101) bigstobj)))
   (assert! (equal (mv-list 2 (slowhash-get? (list 101) bigstobj)) (list nil nil)))

   (assert! (not (eqhash-boundp (packn (list 'a 101)) bigstobj)))
   (assert! (equal (mv-list 2 (honshash-get? (packn (list 'a 101)) bigstobj)) (list nil nil)))

   (assert! (not (honshash-boundp 101 bigstobj)))
   (assert! (equal (mv-list 2 (honshash-get? 101 bigstobj)) (list nil nil)))

   (assert! (not (honshash-boundp (list 101) bigstobj)))
   (assert! (equal (mv-list 2 (honshash-get? (list 101) bigstobj)) (list nil nil)))


   (make-event
    (let* ((bigstobj (bighash-rem 3 bigstobj))
           (bigstobj (slowhash-rem (list 3) bigstobj))
           (bigstobj (eqhash-rem (packn (list 'a 3)) bigstobj))
           (bigstobj (honshash-rem (list 3) bigstobj)))
      (mv nil '(value-triple :invisible) state bigstobj)))

   (assert! (not (bighash-boundp 3 bigstobj)))
   (assert! (not (slowhash-boundp (list 3) bigstobj)))
   (assert! (not (eqhash-boundp (packn (list 'a 3)) bigstobj)))
   (assert! (not (honshash-boundp (list 3) bigstobj)))

   (assert! (equal (slowhash-count bigstobj) 100))
   (assert! (equal (honshash-count bigstobj) 100))
   (assert! (equal (bighash-count bigstobj) 99))
   (assert! (equal (eqhash-count bigstobj) 99))

   (make-event
    (let* ((bigstobj (slowhash-clear bigstobj))
           (bigstobj (honshash-clear bigstobj))
           (bigstobj (bighash-init 10000 nil nil bigstobj))
           (bigstobj (eqhash-init 1 30 1/2 bigstobj)))
      (mv nil '(value-triple :invisible) state bigstobj)))

   (assert! (equal (bighash-count bigstobj) 0))
   (assert! (equal (slowhash-count bigstobj) 0))
   (assert! (equal (eqhash-count bigstobj) 0))
   (assert! (equal (honshash-count bigstobj) 0))
   (assert! (equal (bighash-get 5 bigstobj) nil))
   (assert! (equal (slowhash-get (list 5) bigstobj) nil))
   (assert! (equal (eqhash-get (packn (list 'a 5)) bigstobj) nil))
   (assert! (equal (slowhash-get (list 5) bigstobj) nil))

   ))




