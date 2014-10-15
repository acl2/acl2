; Defsort - Defines a stable sort when given a comparison function
; Copyright (C) 2008 Centaur Technology
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
; Original author: Jared Davis <jared@centtech.com>

(in-package "ACL2")
(include-book "uniquep")
(local (include-book "std/lists/sets" :dir :system))
(local (include-book "std/lists/no-duplicatesp" :dir :system))


; DUPLICATED-MEMBERS and HONS-DUPLICATED-MEMBERS
;
; Duplicated-members, introduced below, returns all members of a list whose
; duplicity is greater than 1.  It operates by sorting its argument and then
; scanning for adjacent duplicates, which is pretty fast.  So, the total
; complexity is O(n log n).
;
; Hons-duplicated-members does the same thing except that it may return the
; elements in a different order.  It operates by building a fast alist which
; associates each element with its duplicity, then scanning the alist for
; objects whose duplicity is greater than 1.  If one believes that hons-acons
; and hons-get are effectively O(1), then its efficiency is O(n).
;
; In practice, both functions are pretty good, and hons-duplicated-members
; tends to outperform duplicated-members by slight margins in speed and memory
; consumption.

(defund collect-adjacent-duplicates (x)
  (declare (xargs :guard t))
  (cond ((atom x)
         nil)
        ((atom (cdr x))
         nil)
        ((equal (first x) (second x))
         (if (atom (cddr x))
             (list (first x))
           (if (not (equal (first x) (third x)))
               (cons (first x)
                     (collect-adjacent-duplicates (cddr x)))
             (collect-adjacent-duplicates (cdr x)))))
        (t
         (collect-adjacent-duplicates (cdr x)))))

(defthm collect-adjacent-duplicates-when-not-consp
  (implies (not (consp x))
           (equal (collect-adjacent-duplicates x)
                  nil))
  :hints(("Goal" :in-theory (enable collect-adjacent-duplicates))))

(defthm collect-adjacent-duplicates-when-not-consp-of-cdr
  (implies (not (consp (cdr x)))
           (equal (collect-adjacent-duplicates x)
                  nil))
  :hints(("Goal" :in-theory (enable collect-adjacent-duplicates))))

(defthm collect-adjacent-duplicates-of-cons-and-cons
  (equal (collect-adjacent-duplicates (cons a (cons b x)))
         (if (equal a b)
             (if (not (consp x))
                 (list a)
               (if (equal a (car x))
                   (collect-adjacent-duplicates (cons a x))
                 (cons a (collect-adjacent-duplicates x))))
           (collect-adjacent-duplicates (cons b x))))
  :hints(("Goal" :in-theory (enable collect-adjacent-duplicates))))

(encapsulate
 ()
 (local (defthm lemma
          (implies (and (member-equal a (collect-adjacent-duplicates (cons x1 x4)))
                        (not (<< b a))
                        (<< b x1))
                   (member-equal a (collect-adjacent-duplicates x4)))
          :hints(("Goal" :in-theory (enable collect-adjacent-duplicates)))))

 (local (defthm lemma2
          (implies (and (<<-ordered-p x)
                        (equal (duplicity a x) 1)
                        (not (<< b a))
                        (<< b (car x)))
                   (member-equal a (collect-adjacent-duplicates (cons b x))))
          :hints(("Goal" :in-theory (enable <<-ordered-p)))))

 (local (defthm lemma3
          (implies (and (<<-ordered-p x)
                        (equal (duplicity a x) 1)
                        (not (<< b a))
                        (not (<< (car x) b)))
                   (member-equal a (collect-adjacent-duplicates (cons b x))))
          :hints(("Goal" :in-theory (enable <<-ordered-p)))))

 (local (defthm lemma4
          (implies (and (<<-ordered-p x)
                        (< 1 (duplicity a x)))
                   (member-equal a (collect-adjacent-duplicates x)))
          :hints(("Goal" :in-theory (enable <<-ordered-p
                                            collect-adjacent-duplicates)))))

 (local (defthm lemma5
          (implies (and (<<-ordered-p x)
                        (not (< 1 (duplicity a x))))
                   (not (member-equal a (collect-adjacent-duplicates x))))
          :hints(("Goal" :in-theory (enable <<-ordered-p
                                            collect-adjacent-duplicates
                                            duplicity)))))

 (defthm member-equal-of-collect-adjacent-duplicates-when-<<-ordered-p
   (implies (<<-ordered-p x)
            (iff (member-equal a (collect-adjacent-duplicates x))
                 (< 1 (duplicity a x))))))

(encapsulate
 ()
 (local (defthm crock0
          (implies (<<-ordered-p x)
                   (<<-ordered-p (cdr x)))
          :hints(("Goal" :in-theory (enable <<-ordered-p)))))

 (local (defthm crock1
          (implies (no-duplicatesp-equal x)
                   (equal (duplicity a x)
                          (if (member-equal a x)
                              1
                            0)))
          :hints(("Goal" :in-theory (enable duplicity)))))

 (local (defthm crock3
          (implies (and (no-duplicatesp-equal (collect-adjacent-duplicates (cons b x)))
                        (<<-ordered-p x)
                        (<< a b)
                        (not (<< (car x) b)))
                   (<= (duplicity a x) 1))
          :hints(("Goal" :in-theory (enable duplicity
                                            <<-ordered-p
                                            collect-adjacent-duplicates)))))

 (defthm no-duplicatesp-equal-of-collect-adjacent-duplicates-when-<<-ordered-p
   (implies (<<-ordered-p x)
            (no-duplicatesp-equal (collect-adjacent-duplicates x)))
   :hints(("Goal" :in-theory (enable collect-adjacent-duplicates <<-ordered-p)))))



(defund duplicated-members (x)
  (declare (xargs :guard (true-listp x)))
  (collect-adjacent-duplicates (<<-sort x)))

(defthm member-equal-of-duplicated-members
  (iff (member-equal a (duplicated-members x))
       (< 1 (duplicity a x)))
  :hints(("Goal" :in-theory (enable duplicated-members))))

(defthm no-duplicatesp-equal-of-duplicated-members
  (no-duplicatesp-equal (duplicated-members x))
  :hints(("Goal" :in-theory (enable duplicated-members))))

(local (defthm element-p-by-duplicity-in-element-list-p
         (implies (and (element-list-p x)
                       (< 0 (duplicity a x)))
                  (element-p a))))

(local (defthm element-list-p-when-subset-of-duplicated-members
         (implies (and (subsetp x (duplicated-members y))
                       (element-list-p y))
                  (equal (element-list-p x)
                         (or (element-list-final-cdr-p t)
                             (true-listp x))))))

(def-listp-rule element-list-p-of-duplicated-members
  (implies (element-list-p x)
           (element-list-p (duplicated-members x)))
  :hints (("goal" :use ((:instance element-list-p-when-subset-of-duplicated-members
                         (y x) (x (duplicated-members x))))
           :in-theory (disable element-list-p-when-subset-of-duplicated-members)))
  :tags (:duplicated-members))


(encapsulate
  ()
  (local (defthm l0
           (implies (duplicated-members x)
                    (not (no-duplicatesp-equal x)))
           :hints(("Goal"
                   :in-theory (disable no-duplicatesp-equal-when-high-duplicity
                                       member-equal-of-duplicated-members)
                   :use ((:instance no-duplicatesp-equal-when-high-duplicity
                                    (a (car (duplicated-members x))))
                         (:instance member-equal-of-duplicated-members
                                    (a (car (duplicated-members x)))))))))

  (local (defthm l1
           (implies (not (duplicated-members x))
                    (no-duplicatesp-equal x))
           :hints(("Goal"
                   :in-theory (disable member-equal-of-duplicated-members)
                   :use ((:instance member-equal-of-duplicated-members
                                    (a (car (duplicity-badguy x)))
                                    (x x)))))))

  (defthm duplicated-members-under-iff
    (iff (duplicated-members x)
         (not (no-duplicatesp-equal x)))))




;; An alternate approach to constructing the duplicated members, based upon hons,
;; is shown below.  We construct an alist mapping each member of the list to its
;; duplicity, then walk the alist and see what we have found.

(defund hons-duplicity-alist-p (x)
  (declare (xargs :guard t))
  (if (consp x)
      (and (consp (car x))
           (natp (cdar x))
           (hons-duplicity-alist-p (cdr x)))
    (not x)))

(defthm hons-duplicity-alist-p-when-not-consp
  (implies (not (consp x))
           (equal (hons-duplicity-alist-p x)
                  (not x)))
  :hints(("Goal" :in-theory (enable hons-duplicity-alist-p))))

(defthm hons-duplicity-alist-p-of-cons
  (equal (hons-duplicity-alist-p (cons a x))
         (and (consp a)
              (natp (cdr a))
              (hons-duplicity-alist-p x)))
  :hints(("Goal" :in-theory (enable hons-duplicity-alist-p))))

(defthm alistp-when-hons-duplicity-alist-p
  (implies (hons-duplicity-alist-p x)
           (alistp x))
  :hints(("Goal" :induct (len x))))



(defund hons-duplicity-alist-aux (x alist)
  (declare (xargs :guard (hons-duplicity-alist-p alist)))
  (if (atom x)
      alist
    (hons-duplicity-alist-aux
     (cdr x)
     (hons-acons (car x)
                 (+ 1 (nfix (cdr (hons-get (car x) alist))))
                 alist))))

(defthm hons-duplicity-alist-p-of-hons-duplicity-alist-aux
  (implies (hons-duplicity-alist-p alist)
           (hons-duplicity-alist-p (hons-duplicity-alist-aux x alist)))
  :hints(("Goal" :in-theory (enable hons-duplicity-alist-aux))))

(defthm hons-assoc-equal-of-hons-duplicity-alist-aux
  (implies (hons-duplicity-alist-p alist)
           (equal (hons-assoc-equal a (hons-duplicity-alist-aux x alist))
                  (if (or (member-equal a x)
                          (hons-assoc-equal a alist))
                      (cons a (+ (duplicity a x)
                                 (nfix (cdr (hons-assoc-equal a alist)))))
                    nil)))
  :hints(("Goal"
          :in-theory (enable hons-duplicity-alist-aux duplicity)
          :do-not '(generalize fertilize)
          :induct (hons-duplicity-alist-aux x alist))))



(defund hons-duplicity-alist (x)
  (declare (xargs :guard t))
  (hons-shrink-alist (hons-duplicity-alist-aux x nil) nil))

(defthm hons-duplicity-alist-p-of-hons-shrink-alist
  (implies (and (hons-duplicity-alist-p alist)
                (hons-duplicity-alist-p ans))
           (hons-duplicity-alist-p (hons-shrink-alist alist ans)))
  :hints(("Goal" :in-theory (enable hons-shrink-alist))))

(defthm hons-duplicity-alist-p-of-hons-duplicity-alist
  (hons-duplicity-alist-p (hons-duplicity-alist x))
  :hints(("Goal" :in-theory (enable hons-duplicity-alist))))

(local (defthm iff-of-hons-assoc-equal
         (implies (alistp x)
                  (iff (hons-assoc-equal a x)
                       (member-equal a (strip-cars x))))))

(defthm no-duplicatesp-equal-of-strip-cars-of-hons-shrink-alist
  (implies (alistp y)
           (equal (no-duplicatesp-equal (strip-cars (hons-shrink-alist x y)))
                  (no-duplicatesp-equal (strip-cars y))))
  :hints(("Goal" :in-theory (enable hons-shrink-alist))))

(defthm no-duplicatesp-equal-of-strip-cars-of-hons-duplicity-alist
  (no-duplicatesp-equal (strip-cars (hons-duplicity-alist x)))
  :hints(("Goal" :in-theory (enable hons-duplicity-alist))))

(defthm hons-assoc-equal-of-hons-shrink-alist
  (equal (hons-assoc-equal a (hons-shrink-alist x y))
         (or (hons-assoc-equal a y)
             (hons-assoc-equal a x)))
  :hints(("Goal" :in-theory (enable hons-shrink-alist))))

(defthm hons-assoc-equal-of-hons-duplicity-alist
  (equal (hons-assoc-equal a (hons-duplicity-alist x))
         (if (member-equal a x)
             (cons a (duplicity a x))
           nil))
  :hints(("Goal" :in-theory (enable hons-duplicity-alist))))



(defund hons-duplicated-members-aux (alist)
  ;; Walks over the shrunken duplicity alist and gathers keys which occurred
  ;; more than once.
  (declare (xargs :guard (alistp alist)))
  (cond ((atom alist)
         nil)
        ((> (nfix (cdar alist)) 1)
         (cons (caar alist)
               (hons-duplicated-members-aux (cdr alist))))
        (t
         (hons-duplicated-members-aux (cdr alist)))))

(defthm member-equal-of-strip-cars-when-member-equal-of-hons-duplicated-members-aux
  (implies (member-equal a (hons-duplicated-members-aux x))
           (member-equal a (strip-cars x)))
  :hints(("Goal" :in-theory (enable hons-duplicated-members-aux))))

(defthm member-equal-of-hons-duplicated-members-aux
  (implies (no-duplicatesp-equal (strip-cars x))
           (iff (member-equal a (hons-duplicated-members-aux x))
                (> (nfix (cdr (hons-assoc-equal a x))) 1)))
  :hints(("Goal" :in-theory (enable hons-duplicated-members-aux))))

(defthm no-duplicatesp-equal-of-hons-duplicated-members-aux
  (implies (no-duplicatesp-equal (strip-cars alist))
           (no-duplicatesp-equal (hons-duplicated-members-aux alist)))
  :hints(("Goal" :in-theory (enable hons-duplicated-members-aux))))




(defund hons-duplicated-members (x)
  (declare (xargs :guard t))
  (let* ((dalist (hons-duplicity-alist x))
         (result (hons-duplicated-members-aux dalist)))
    (prog2$
     (flush-hons-get-hash-table-link dalist)
     result)))

(defthm member-equal-of-hons-duplicated-members
  (iff (member-equal a (hons-duplicated-members x))
       (< 1 (duplicity a x)))
  :hints(("Goal" :in-theory (enable hons-duplicated-members))))

(defthm no-duplicatesp-equal-of-hons-duplicated-members
  (no-duplicatesp-equal (hons-duplicated-members x))
  :hints(("Goal" :in-theory (enable hons-duplicated-members))))




#|

:q

(defconst *test1*
  (append (loop for i from 1 to 10000 collect i)
          (loop for i from 1 to 5000 collect i)
          (loop for i from 1 to 5000 collect i)))

;; Lisp2 takes 3.31 seconds, 207 MB allocated
(time (loop for i from 1 to 100 do (hons-duplicated-members *test1*)))

;; Lisp2 takes 3.16 seconds, 278 MB allocated
(time (loop for i from 1 to 100 do (duplicated-members *test1*)))



(defconst *test2*
  (append (loop for i from 1 to 10000 collect (concatenate 'string
                                                           "foo bar baz "
                                                           (coerce (explode-atom i 10) 'string)))
          (loop for i from 1 to 5000 collect (concatenate 'string
                                                          "foo bar baz "
                                                          (coerce (explode-atom i 10) 'string)))
          (loop for i from 1 to 5000 collect (concatenate 'string
                                                          "foo bar baz "
                                                          (coerce (explode-atom i 10) 'string)))))


;; Lisp2 takes 5.06 seconds, 208 MB allocated
(time (loop for i from 1 to 100 do (hons-duplicated-members *test2*)))

;; Lisp2 takes 6.03 seconds, 313 MB allocated
(time (loop for i from 1 to 100 do (duplicated-members *test2*)))

|#

