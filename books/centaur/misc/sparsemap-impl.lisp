; Centaur Miscellaneous Books
; Copyright (C) 2008-2013 Centaur Technology
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

(in-package "ACL2")
(include-book "std/lists/resize-list" :dir :system)
(include-book "count-up")
(include-book "remove-assoc")
(include-book "std/basic/arith-equivs" :dir :system)
(include-book "std/util/bstar" :dir :system)
(include-book "tools/mv-nth" :dir :system)
(include-book "misc/definline" :dir :system)
(include-book "std/stobjs/absstobjs" :dir :system)
(local (include-book "std/alists/strip-cars" :dir :system))
(local (in-theory (enable* arith-equiv-forwarding)))

; cert_param: (non-acl2r)

(defthm nth-out-of-bounds
  (implies (<= (len lst) (nfix idx))
           (equal (nth idx lst)
                  nil))
  :hints(("Goal" :in-theory (enable nth))))

;; This data structure is based on the description here:
;; http://research.swtch.com/sparse

;; The idea is that we want to map some subset of the integers from 0 to N-1
;; to some objects, and we want to be able to frequently clear the mapping and
;; start again from a state where nothing is yet mapped.  N is big enough that
;; we don't want to frequently do linear sweeps of size N, but small enough
;; that we don't mind having one array of size N.

;; This data structure provides constant-time set, get, delete, and clear
;; operations.

;; Here is the data structure:
(defstobj sm

  ;; Array with N entries.  This may contain trash except for the elements that
  ;; actually have mappings.  For each element x that has a mapping, we arrange:
  ;; sm-indices[x] < sm-count
  ;; sm-backptrs[sm-indices[x]] == x
  ;; sm-data[sm-indices[x]] is the mapped data.
  (sm-indices   :type (array (unsigned-byte 32) (0))
                :resizable t
                :initially 0)
  (sm-backptrs  :type (array (unsigned-byte 32) (0))
                :resizable t
                :initially 0) ;; doesn't matter

  ;; If all we want is a set representation (mapping of elements to t/nil) we
  ;; can leave this as size 0 and just ask whether elements are present or not.
  (sm-data      :type (array t (0))
                :resizable t
                ;; the default element for something that's bound but
                ;; did not have its data explicitily set
                :initially t)
  (sm-count     :type (unsigned-byte 32)
                :initially 0)

  (sm-range     :type (unsigned-byte 32)
                :initially 0)

  :inline t)

(defun u32-listp (x)
  (declare (xargs :guard t))
  (if (atom x)
      (eq x nil)
    (and (unsigned-byte-p 32 (car x))
         (u32-listp (cdr x)))))

(defthm sm-indicesp-is-u32-listp
  (equal (sm-indicesp x)
         (u32-listp x)))

(defthm sm-backptrsp-is-u32-listp
  (equal (sm-backptrsp x)
         (u32-listp x)))

(defthm sm-datap-is-true-listp
  (equal (sm-datap x)
         (true-listp x)))

(in-theory (disable nth update-nth natp))

(defthm nth-in-u32-listp
  (implies (and (u32-listp x)
                (< (nfix n) (len x)))
           (let ((k (nth n x)))
             (and (integerp k)
                  (rationalp k)
                  (acl2-numberp k)
                  (natp k)
                  (<= 0 k)
                  (< k 4294967296)
                  (unsigned-byte-p 32 k))))
  :hints(("Goal" :in-theory (enable nth))))

(defthm nfix-nth-in-u32-listp
  (implies (u32-listp x)
           (let ((k (nfix (nth n x))))
             (and (< k 4294967296)
                  (unsigned-byte-p 32 k))))
  :hints(("Goal" :in-theory (enable nth))))

(definline sm-get-range (sm)
  (declare (xargs :stobjs sm))
  (lnfix (sm-range sm)))

(defun sm-set-range1 (n sm)
  (declare (xargs :stobjs sm)
           (type (integer 0 *) n))
  (mbe :logic (b* ((sm (update-sm-range (nfix n) sm))
                   (sm (if (< (sm-indices-length sm) (nfix n))
                           (resize-sm-indices (nfix n) sm)
                         sm)))
                sm)
       :exec (b* ((sm (if (< n (expt 2 32))
                          (update-sm-range n sm)
                        (ec-call (update-sm-range n sm)))))
               (if (< (sm-indices-length sm) (nfix n))
                   (resize-sm-indices (nfix n) sm)
                 sm))))


;; Very loose well-formedness condition: just that the backptrs array is larger
;; than the count.
(defun sm-okp (sm)
  (declare (xargs :stobjs sm))
  ;;(and (< (sm-indices-length sm) (expt 2 32))
  ;;     (< (sm-backptrs-length sm) (expt 2 32))
  ;;     (< (sm-data-length sm) (expt 2 32))
  (and (<= (lnfix (sm-count sm))
           (sm-backptrs-length sm))
       (<= (sm-get-range sm)
           (sm-indices-length sm))))

;;(defund sm-fix (sm)
;;  (declare (xargs :stobjs sm))
;;  (if (sm-okp sm)
;;      sm
;;    (resize-sm-backptrs (lnfix (sm-count sm)) sm)))

;;(defmacro lsm-fix (smv)
;;  `(mbe :logic (sm-fix ,smv)
;;        :exec ,smv))

(definline sm-get-index (n sm)
  (declare (type (integer 0 *) n)
           (xargs :stobjs sm
                  :guard t))
  (mbe :logic (nfix (sm-indicesi n sm))
       :exec (the (unsigned-byte 32)
               (if (< (lnfix n) (sm-indices-length sm))
                   (sm-indicesi n sm)
                 0))))

(definline sm-get-index-fast (n sm)
  (declare (type (integer 0 *) n)
           (xargs :stobjs sm
                  :guard (< (nfix n) (sm-indices-length sm))))
  (mbe :logic (sm-get-index n sm)
       :exec (the (unsigned-byte 32)
               (sm-indicesi n sm))))

(definline sm-get-backptr (n sm)
  (declare (type (integer 0 *) n)
           (xargs :stobjs sm
                  :guard t))
  (mbe :logic (nfix (sm-backptrsi n sm))
       :exec (the (unsigned-byte 32)
               (if (< (lnfix n) (sm-backptrs-length sm))
                   (sm-backptrsi n sm)
                 0))))

(definline sm-get-backptr-fast (n sm)
  (declare (type (integer 0 *) n)
           (xargs :stobjs sm
                  :guard (< (nfix n) (sm-backptrs-length sm))))
  (mbe :logic (sm-get-backptr n sm)
       :exec (the (unsigned-byte 32)
               (sm-backptrsi n sm))))


(defun sm-inp1 (n sm)
  (declare (xargs :stobjs sm))
  (b* ((n (the (integer 0 *) (nfix n)))
       (idx (the (unsigned-byte 32)
              (sm-get-index n sm)))
       ((unless (< idx (the (unsigned-byte 32)
                         (lnfix (sm-count sm)))))
        nil)
       (backptr (the (unsigned-byte 32)
                  (lnfix (sm-get-backptr idx sm)))))
    (and (= backptr n)
         idx)))

(defcong nat-equiv equal (sm-inp1 n sm) 1)



(local (include-book "arithmetic/top-with-meta" :dir :system))

(defun sm-compactp-aux (n sm)
  (declare (type (integer 0 *) n)
           (xargs :stobjs sm
                  :guard (count-up-guard n (sm-count sm))
                  :measure (count-up-meas n (sm-count sm))))
  (if (count-up-done n (sm-count sm))
      t
    (and (let* ((idx (sm-get-backptr n sm)))
           (and (< idx (sm-indices-length sm))
                (equal (sm-inp1 idx sm)
                       (lnfix n))))
         (sm-compactp-aux (1+ (lnfix n)) sm))))

(defun sm-compactp (sm)
  (declare (xargs :stobjs sm
                  :guard (sm-okp sm)))
  (sm-compactp-aux 0 sm))

;; Strict well-formedness condition.
(defun sm-wfp (sm)
  (declare (xargs :stobjs sm))
  (and (sm-okp sm) (sm-compactp sm)))

(defun sm-fix (sm)
  (declare (xargs :stobjs sm))
  (if (sm-wfp sm)
      sm
    (b* ((sm (update-sm-count 0 sm))
         (range (sm-get-range sm))
         (sm (if (< (sm-indices-length sm) range)
                 (resize-sm-indices range sm)
               sm)))
      sm)))

(defthm sm-wfp-of-sm-fix
  (sm-wfp (sm-fix sm)))

(defthm sm-fix-when-sm-wfp
  (implies (sm-wfp sm)
           (equal (sm-fix sm) sm))
  :hints(("Goal" :in-theory (disable sm-wfp))))

(in-theory (disable sm-fix))

(defmacro lsm-fix (smv)
  `(mbe :logic (sm-fix ,smv) :exec ,smv))

(definlined sm-eltcount (sm)
  (declare (xargs :stobjs sm :guard (sm-wfp sm)))
  (mbe :logic (if (sm-wfp sm) (nfix (sm-count sm)) 0)
       :exec (sm-count sm)))

(local (defthm sm-eltcount-local
         (equal (sm-eltcount sm) (nfix (sm-count (sm-fix sm))))
         :hints(("Goal" :in-theory (enable sm-eltcount sm-fix)))))

(defthm sm-eltcount-of-sm-fix
  (equal (sm-eltcount (sm-fix sm))
         (sm-eltcount sm)))

(defthm sm-wfp-implies
  (implies (sm-wfp sm)
           (and (sm-okp sm)
                (sm-compactp sm)))
  :hints(("Goal" :in-theory (disable sm-okp sm-compactp))))

(defthm sm-wfp-linear
  (implies (sm-wfp sm)
           (and (<= (nfix (nth *sm-count* sm))
                    (len (nth *sm-backptrsi* sm)))
                (<= (nfix (nth *sm-range* sm))
                    (len (nth *sm-indicesi* sm)))))
  :rule-classes :linear)

(defthm sm-wfp-linear-natp
  (implies (sm-wfp sm)
           (and (implies (natp (nth *sm-count* sm))
                         (<= (nth *sm-count* sm)
                             (len (nth *sm-backptrsi* sm))))
                (implies (natp (nth *sm-range* sm))
                         (<= (nth *sm-range* sm)
                             (len (nth *sm-indicesi* sm))))))
  :rule-classes :linear)

(in-theory (disable sm-wfp))


(definlined sm-inp (n sm)
  (declare (type (integer 0 *) n)
           (xargs :stobjs sm
                  :guard (and (natp n)
                              (< n (sm-get-range sm))
                              (sm-wfp sm))))
  (b* (((unless (mbt (sm-wfp sm)))
        nil)
       (n (the (unsigned-byte 32) (lnfix n)))
       (idx (the (unsigned-byte 32)
              (sm-get-index-fast n sm)))
       ((unless (< idx (the (unsigned-byte 32) (sm-eltcount sm))))
        nil)
       ;; bozo try to get this to fixnum size
       (backptr (the (unsigned-byte 32) (lnfix (sm-backptrsi idx sm)))))
    (and (= backptr n)
         idx)))

(defcong nat-equiv equal (sm-inp n sm) 1
  :hints(("Goal" :in-theory (enable sm-inp))))

(local (defthm sm-inp-is-sm-inp1-local
         (equal (sm-inp n sm)
                (sm-inp1 n (sm-fix sm)))
         :hints(("Goal" :in-theory (enable sm-inp sm-fix)))))

(in-theory (disable sm-inp))

(definline sm-clear (sm)
  (declare (xargs :stobjs sm
                  :guard (sm-wfp sm)))
  (b* ((sm (lsm-fix sm)))
    (update-sm-count 0 sm)))

(encapsulate nil
  (local (defthm sm-wfp-of-sm-clear-1
           (implies (sm-wfp sm)
                    (sm-wfp (sm-clear sm)))
           :hints ((and stable-under-simplificationp
                        '(:in-theory (enable sm-wfp))))))
  (defthm sm-wfp-of-sm-clear
    (sm-wfp (sm-clear sm))
    :hints (("goal" :use ((:instance sm-wfp-of-sm-clear-1)
                          (:instance sm-wfp-of-sm-clear-1
                           (sm (sm-fix sm))))))))

(defthm sm-inp1-of-sm-clear
  (not (sm-inp1 n (sm-clear sm))))

(local (defthm sm-okp-of-sm-clear
         (sm-okp (sm-clear sm))
         :hints (("goal" :use sm-wfp-of-sm-clear
                  :in-theory (disable sm-wfp-of-sm-clear sm-clear sm-okp)))))

(local (defthm sm-compactp-of-sm-clear
         (sm-compactp (sm-clear sm))
         :hints (("goal" :use sm-wfp-of-sm-clear
                  :in-theory (disable sm-wfp-of-sm-clear sm-clear
                                      sm-compactp)))))

(defthmd sm-compactp-aux-lemma
  (implies (and (sm-compactp-aux n sm)
                (<= (nfix n) (nfix m))
                (< (nfix m) (nfix (sm-count sm))))
           (and (equal (sm-inp1 (nth m (nth *sm-backptrsi* sm)) sm)
                       (nfix m))
                (< (nfix (nth m (nth *sm-backptrsi* sm)))
                   (len (nth *sm-indicesi* sm))))))

(defthm sm-compactp-implies-backptr-match
  (implies (and (sm-compactp sm)
                (< (nfix m) (nfix (sm-count sm))))
           (equal (sm-inp1 (nth m (nth *sm-backptrsi* sm)) sm)
                  (nfix m)))
  :hints(("Goal" :in-theory (e/d (sm-wfp)
                                 (sm-compactp-aux sm-inp))
          :use ((:instance sm-compactp-aux-lemma (n 0))))))

(defthm sm-compactp-implies-backptr-in-range
  (implies (and (sm-compactp sm)
                (< (nfix m) (nfix (sm-count sm))))
           (< (nfix (nth m (nth *sm-backptrsi* sm)))
              (len (nth *sm-indicesi* sm))))
  :hints(("Goal" :in-theory (e/d (sm-wfp)
                                 (sm-compactp-aux sm-inp))
          :use ((:instance sm-compactp-aux-lemma (n 0)))))
  :rule-classes (:rewrite :linear))





(defthm sm-inp1-equal
  (implies (and (sm-inp1 m sm)
                (sm-inp1 n sm))
           (equal (equal (sm-inp1 m sm)
                         (sm-inp1 n sm))
                  (equal (nfix m) (nfix n))))
  :hints(("Goal" :in-theory (enable sm-inp1)
          :cases ((equal (nfix n) (nfix m))))))

(defthmd nat-equiv-of-backptrs-when-compact-aux
  (implies (and (sm-compactp-aux a sm)
                (<= (nfix a) (nfix b))
                (<= (nfix a) (nfix c))
                (< (nfix b) (nfix (sm-count sm)))
                (< (nfix c) (nfix (sm-count sm))))
           (equal (equal (nfix (nth b (nth *sm-backptrsi* sm)))
                         (nfix (nth c (nth *sm-backptrsi* sm))))
                  (equal (nfix b) (nfix c))))
  :hints (("goal" :use ((:instance sm-inp1-equal
                         (m (nth b (nth *sm-backptrsi* sm)))
                         (n (nth c (nth *sm-backptrsi* sm)))))
           :in-theory (e/d (sm-compactp-aux-lemma)
                           (sm-inp1-equal
                            sm-inp1
                            ;; bozo yuck
                            INEQUALITY-WITH-NFIX-FORWARD-TO-NATP-1
                            ))
           :do-not '(generalize fertilize))))

(defthm nat-equiv-of-backptrs-when-compact
  (implies (and (sm-compactp sm)
                (< (nfix b) (nfix (sm-count sm)))
                (< (nfix c) (nfix (sm-count sm))))
           (equal (equal (nfix (nth b (nth *sm-backptrsi* sm)))
                         (nfix (nth c (nth *sm-backptrsi* sm))))
                  (equal (nfix b) (nfix c))))
  :hints (("goal" :in-theory (e/d (sm-compactp)
                                  (sm-compactp-aux))
           :use ((:instance nat-equiv-of-backptrs-when-compact-aux
                  (a 0))))))

(defun sm-list-aux (n sm)
  (declare (type (unsigned-byte 32) n)
           (xargs :stobjs sm
                  :guard (and (sm-wfp sm)
                              (<= n (sm-eltcount sm)))
                  :measure (count-up-meas n (sm-eltcount sm))))
  (if (count-up-done n (sm-eltcount sm))
      nil
    (cons (lnfix (sm-backptrsi n sm))
          (sm-list-aux (1+ (lnfix n)) sm))))

(defun sm-list (sm)
  (declare (xargs :stobjs sm
                  :guard (sm-wfp sm)))
  (sm-list-aux 0 sm))


(defthm sm-count-of-sm-fix-when-not-wfp
  (implies (not (sm-wfp sm))
           (equal (nth *sm-count* (sm-fix sm))
                  0))
  :hints(("Goal" :in-theory (enable sm-fix))))

(defthm member-of-sm-list-aux
  (iff (member n (sm-list-aux m sm))
       (and (natp n)
            (sm-inp n sm)
            (<= (nfix m) (sm-inp n sm))))
  :hints(("Goal" :in-theory (e/d () (sm-inp1 sm-compactp))
          :induct t)
         '(:cases ((sm-wfp sm)))
         (and stable-under-simplificationp
              '(:in-theory (e/d (sm-inp) (sm-compactp)))))
  :otf-flg t)

(defthm member-of-sm-list
  (iff (member n (sm-list sm))
       (and (natp n)
            (sm-inp n sm)))
  :hints(("Goal" :in-theory (disable sm-list-aux sm-compactp sm-inp))))

(defthm no-duplicatesp-sm-list-aux
  (no-duplicatesp (sm-list-aux m sm))
  :hints(("Goal" :in-theory (e/d* ()
                                  (sm-compactp sm-inp))
          :induct t)
         '(:cases ((sm-wfp sm)))))

(defthm no-duplicatesp-sm-list
  (no-duplicatesp (sm-list sm))
  :hints(("Goal" :in-theory (disable sm-compactp sm-inp
                                     sm-list-aux))))

(defthm len-sm-list-aux
  (equal (len (sm-list-aux m sm))
         (nfix (- (sm-eltcount sm) (nfix m)))))

(defthm len-sm-list
  (equal (len (sm-list sm))
         (sm-eltcount sm)))

(in-theory (disable sm-compactp sm-list))



(definline set-sm-count (c sm)
  (declare (type (integer 0 *) c)
           (xargs :stobjs sm))
  (mbe :logic (update-sm-count c sm)
       :exec (if (< c (expt 2 32))
                 (update-sm-count c sm)
               (ec-call (update-sm-count c sm)))))

(definline set-sm-index (n v sm)
  (declare (type (integer 0 *) n v)
           (xargs :stobjs sm))
  (mbe :logic (update-sm-indicesi n v sm)
       :exec (if (or (<= (sm-indices-length sm) n)
                     (<= (expt 2 32) v))
                 (ec-call (update-sm-indicesi n v sm))
               (update-sm-indicesi n v sm))))

(definline set-sm-index-fast (n v sm)
  (declare (type (integer 0 *) n v)
           (xargs :stobjs sm
                  :guard (< n (sm-indices-length sm))))
  (mbe :logic (update-sm-indicesi n v sm)
       :exec (if (<= (expt 2 32) v)
                 (ec-call (update-sm-indicesi n v sm))
               (update-sm-indicesi n v sm))))

(definline set-sm-index-u32 (n v sm)
  (declare (type (integer 0 *) n)
           (type (unsigned-byte 32) v)
           (xargs :stobjs sm))
  (mbe :logic (update-sm-indicesi n v sm)
       :exec (if (<= (sm-indices-length sm) n)
                 (ec-call (update-sm-indicesi n v sm))
               (update-sm-indicesi n v sm))))

(definline set-sm-index-fast-u32 (n v sm)
  (declare (type (integer 0 *) n v)
           (type (unsigned-byte 32) v)
           (xargs :stobjs sm
                  :guard (< n (sm-indices-length sm))))
  (update-sm-indicesi n v sm))

(definline set-sm-backptr (n v sm)
  (declare (type (integer 0 *) n v)
           (xargs :stobjs sm
                  :guard (< n (sm-backptrs-length sm))))
  (mbe :logic (update-sm-backptrsi n v sm)
       :exec (if (<= (expt 2 32) v)
                 (ec-call (update-sm-backptrsi n v sm))
               (update-sm-backptrsi n v sm))))

(defun sm-add (n sm)
  (declare (type (integer 0 *) n)
           (xargs :stobjs sm
                  :guard (and (sm-wfp sm)
                              (< n (sm-get-range sm)))))
  (b* ((sm (lsm-fix sm))
       (n (the (unsigned-byte 32) (lnfix n)))
       ((when (sm-inp n sm))
        sm)
       (count (the (unsigned-byte 32) (sm-eltcount sm)))
       (sm (set-sm-index-fast-u32 n count sm))
       (newcount (the (unsigned-byte 33) (+ 1 count)))
       (sm (if (< count (the (integer 0 *) (sm-backptrs-length sm)))
               sm
             (resize-sm-backptrs (the (unsigned-byte 34)
                                   (* 2 newcount))
                                 sm)))
       (sm (update-sm-backptrsi count n sm))
       (sm (set-sm-count newcount sm)))
    sm))

(defthm sm-add-of-sm-fix
  (equal (sm-add n (sm-fix sm))
         (sm-add n sm)))

(defcong nat-equiv equal (sm-add n sm) 1)


(defthm sm-inp1-lt-count
  (implies (sm-inp1 n sm)
           (< (sm-inp1 n sm)
              (nfix (nth *sm-count* sm))))
  :rule-classes (:rewrite :linear))

(defthm sm-inp1-lt-count-natp
  (implies (and (sm-inp1 n sm)
                (natp (nth *sm-count* sm)))
           (< (sm-inp1 n sm)
              (nth *sm-count* sm)))
  :rule-classes (:rewrite :linear))


(defthm not-sm-inp1-of-sm-fix-when-not-sm-wfp
  (implies (not (sm-wfp sm))
           (not (sm-inp1 m (sm-fix sm))))
  :hints(("Goal" :in-theory (enable sm-fix sm-inp1))))

(defthm sm-inp1-lt-count-sm-fix
  (implies (sm-inp n sm)
           (< (sm-inp1 n (sm-fix sm))
              (nfix (nth *sm-count* sm))))
  :hints (("goal" :cases ((sm-wfp sm))
           :in-theory (disable sm-inp1)))
  :rule-classes (:rewrite :linear))

(defthm sm-inp1-lt-count-sm-fix-natp
  (implies (and (sm-inp n sm)
                (natp (nth *sm-count* sm)))
           (< (sm-inp1 n (sm-fix sm))
              (nth *sm-count* sm)))
  :hints (("goal" :cases ((sm-wfp sm))
           :in-theory (disable sm-inp1)))
  :rule-classes (:rewrite :linear))

;;(local (defthm nth-of-nil
;;         (equal (nth nil x)
;;                (nth 0 x))
;;         :hints(("Goal" :in-theory (enable nth)))))


(defthm sm-inp1-of-sm-add-iff
  (iff (sm-inp1 n (sm-add m sm))
       (or (equal (nfix n) (nfix m))
           (sm-inp n sm)))
  :hints(("Goal" :in-theory (e/d (nat-equiv sm-inp1)
                                 (true-listp-update-nth
                                  zp-open len
                                  nth-in-u32-listp
                                  resize-list
                                  (:type-prescription max))))))


(defthm sm-inp1-of-sm-add-equal
  (equal (sm-inp1 n (sm-add m sm))
         (if (equal (nfix n) (nfix m))
             (or (sm-inp n sm)
                 (sm-eltcount sm))
           (sm-inp n sm)))
  :hints(("Goal" :in-theory (e/d (nat-equiv sm-inp1)
                                 (true-listp-update-nth
                                  zp-open len
                                  resize-list
                                  nth-in-u32-listp)))
         (and stable-under-simplificationp
              '(:in-theory (enable sm-fix)))))

(defthm sm-okp-of-sm-add
  (sm-okp (sm-add n sm))
  :hints (("goal" :do-not-induct t)))

(defthmd sm-count-of-sm-add
  (equal (nfix (nth *sm-count* (sm-add n sm)))
         (if (sm-inp n sm)
             (sm-eltcount sm)
           (1+ (sm-eltcount sm))))
  :hints(("Goal" :in-theory (disable sm-inp1))))

(defthm sm-backptrs-after-sm-add-when-not-count
  (implies (not (equal (nfix n) (nfix (sm-count (sm-fix sm)))))
           (nat-equiv (nth n (nth *sm-backptrsi* (sm-add m sm)))
                      (nth n (nth *sm-backptrsi* (sm-fix sm)))))
  :hints(("Goal" :in-theory (disable sm-inp))))

(defthm sm-add-when-boundp
  (implies (sm-inp m sm)
           (equal (sm-add m sm) sm))
  :hints(("Goal" :in-theory (e/d (sm-fix)))))


(defthm sm-backptr-of-count-after-sm-add
  (implies (and (equal (nfix n) (sm-eltcount sm))
                (not (sm-inp m sm)))
           (equal (nth n (nth *sm-backptrsi* (sm-add m sm)))
                  (nfix m)))
  :hints(("Goal" :in-theory (disable sm-inp))))


;;(defthmd equal-of-nfixes1
;;  (equal (equal (nfix n) (nfix m))
;;         (double-rewrite (nat-equiv n m))))

(encapsulate nil

  (local (defthm sm-compactp-incr
           (implies (and (sm-compactp-aux n sm)
                         (<= (nfix n) (nfix m)))
                    (sm-compactp-aux m sm))
           :hints (("goal" :induct (sm-compactp-aux n sm)
                    :expand ((sm-compactp-aux m sm))))))

  (defthm sm-compactp-aux-of-sm-fix
    (sm-compactp-aux m (sm-fix sm))
    :hints (("goal" :use ((:instance sm-wfp-of-sm-fix))
             :in-theory (e/d (sm-wfp sm-compactp)
                             (sm-wfp-of-sm-fix
                              sm-compactp-aux
                               sm-inp1))))))


(defthm sm-range-of-sm-fix
  (equal (nth *sm-range* (sm-fix sm))
         (nth *sm-range* sm))
  :hints(("Goal" :in-theory (enable sm-fix))))

(defthm nth-sm-range-of-sm-add
  (equal (nth *sm-range* (sm-add m sm))
         (nth *sm-range* sm)))

(defthm sm-indices-length-of-sm-fix
  (<= (len (nth *sm-indicesi* sm))
      (len (nth *sm-indicesi* (sm-fix sm))))
  :hints(("Goal" :in-theory (enable sm-fix)))
  :rule-classes (:rewrite :linear))

(defthm sm-indices-length-of-sm-add
  (<= (len (nth *sm-indicesi* sm))
      (len (nth *sm-indicesi* (sm-add m sm))))
  :rule-classes (:rewrite :linear))

(defthm sm-indices-length-of-sm-add-2
  (< (nfix m)
     (len (nth *sm-indicesi* (sm-add m sm))))
  :rule-classes (:rewrite :linear))



(encapsulate nil
  (local (defthmd sm-compactp-aux-of-sm-add-1
           (implies (and (sm-compactp-aux m sm)
                         (sm-wfp sm))
                    (sm-compactp-aux m (sm-add n sm)))
           :hints(("Goal" :in-theory (e/d (sm-count-of-sm-add)
                                          (nth-out-of-bounds
                                           sm-inp1 sm-add))
                   :induct (sm-compactp-aux m sm)
                   :expand ((:free (sm) (sm-compactp-aux m sm))))
                  (and stable-under-simplificationp
                       '(:cases ((equal (nfix m) (nfix (sm-count sm)))))))))
  (defthmd sm-compactp-aux-of-sm-add
    (sm-compactp-aux m (sm-add n sm))
    :hints(("Goal" :use ((:instance sm-compactp-aux-of-sm-add-1
                          (sm (sm-fix sm))))
            :in-theory (disable sm-compactp-aux-of-sm-add-1 sm-add)))))

(defthm sm-compactp-of-sm-add
  (sm-compactp (sm-add n sm))
  :hints(("Goal" :in-theory (e/d (sm-compactp-aux-of-sm-add
                                  sm-compactp)
                                 (sm-compactp-aux sm-add)))))

(defthm sm-wfp-of-sm-add
  (sm-wfp (sm-add n sm))
  :hints(("Goal" :in-theory (enable sm-wfp))))

(defthm sm-inp-after-sm-add
  (implies (not (sm-inp n sm))
           (equal (sm-inp n (sm-add n sm))
                  (nfix (sm-eltcount sm))))
  :hints(("Goal" :in-theory (disable sm-add sm-inp1))))

(encapsulate nil
  (local (in-theory (disable true-listp-update-nth
                             nth-out-of-bounds
                             nth-in-u32-listp
                             natp-rw)))
  (defthm sm-list-aux-of-sm-add
    (equal (sm-list-aux m (sm-add n sm))
           (if (sm-inp n sm)
               (sm-list-aux m sm)
             (and (<= (nfix m) (nfix (sm-count (sm-fix sm))))
                  (append (sm-list-aux m sm) (list (nfix n))))))
    :hints(("Goal" :in-theory (e/d (sm-list-aux)
                                   (sm-inp-is-sm-inp1-local
                                    sm-add sm-inp))
            :induct (sm-list-aux m sm))
           (and stable-under-simplificationp
                '(:in-theory (e/d (sm-count-of-sm-add)
                                  (sm-count-of-sm-fix-when-not-wfp
                                   sm-add sm-inp
                                   sm-inp-is-sm-inp1-local))
                  :use sm-count-of-sm-fix-when-not-wfp))
           (and stable-under-simplificationp
                '(:in-theory (e/d (sm-add sm-inp)
                                  (sm-wfp-of-sm-add))
                  :use (sm-wfp-of-sm-add)
                  :expand ((:free (sm) (sm-list-aux m sm)))))))

  (defthm sm-list-of-sm-add
    (equal (sm-list (sm-add n sm))
           (if (sm-inp n sm)
               (sm-list sm)
             (append (sm-list sm) (list (nfix n)))))
    :hints(("Goal" :in-theory (e/d (sm-list)
                                   (sm-inp-is-sm-inp1-local
                                    sm-add sm-inp))))))

(defthm sm-list-of-sm-clear
  (equal (sm-list (sm-clear sm)) nil)
  :hints(("Goal" :in-theory (e/d (sm-list)
                                 (sm-wfp-of-sm-clear))
          :use sm-wfp-of-sm-clear
          :expand ((:free (sm) (sm-list-aux 0 sm))))))

(in-theory (disable sm-add sm-inp sm-clear))

(defthm sm-inp1-of-sm-add-type
  (natp (sm-inp1 n (sm-add n sm)))
  :hints (("goal" :use ((:instance sm-inp1-of-sm-add-iff
                         (m n)))
           :in-theory (disable sm-inp1-of-sm-add-iff)))
  :rule-classes :type-prescription)

(definline sm-get-count (sm)
  (declare (xargs :stobjs sm))
  (the (unsigned-byte 32)
    (lnfix (sm-count sm))))

(defthm sm-eltcount-of-sm-add
  (equal (sm-eltcount (sm-add n sm))
         (if (sm-inp n sm)
             (sm-eltcount sm)
           (+ 1 (sm-eltcount sm))))
  :hints((and stable-under-simplificationp
              '(:in-theory (enable sm-add)))))


(local (in-theory (disable sm-add sm-inp1)))


;; assumes idx belongs to a bound n
(definline sm-put-aux (idx val sm)
  (declare (type (integer 0 *) idx)
           (xargs :stobjs sm
                  :guard (< idx (nfix (sm-count sm)))))
  (b* ((idx (the (unsigned-byte 32) (lnfix idx)))
       ((when (eq val t))
        (if (< idx (the (integer 0 *)
                     (sm-data-length sm)))
            (update-sm-datai idx val sm)
          sm))
       (sm (if (< idx (the (integer 0 *)
                        (sm-data-length sm)))
               sm
             (resize-sm-data
              (mbe :logic (max (* 2 (+ 1 idx)) (* 2 (nfix (sm-count sm))))
                   :exec (* 2 (sm-get-count sm)))
              sm))))
    (update-sm-datai idx val sm)))

(defun sm-add/idx (n sm)
  (declare (type (integer 0 *) n)
           (xargs :stobjs sm
                  :guard (and (sm-wfp sm)
                              (< n (sm-get-range sm)))
                  :guard-hints ((and stable-under-simplificationp
                                     '(:in-theory (e/d (sm-add)))))))
  (mbe :logic (b* ((sm (sm-add n sm)))
                (mv sm (sm-inp n sm)))
       :exec
       (b* ((n (the (unsigned-byte 32) (lnfix n)))
            (sm (lsm-fix sm))
            (idx (sm-inp n sm))
            ((when idx)
             (mv sm idx))
            (count (the (unsigned-byte 32)
                     (sm-eltcount sm)))
            (sm (set-sm-index-fast-u32 n count sm))
            (newcount (the (unsigned-byte 33) (+ 1 count)))
            (sm (if (< count (the (integer 0 *)
                               (sm-backptrs-length sm)))
                    sm
                  (resize-sm-backptrs
                   (the (unsigned-byte 34) (* 2 newcount)) sm)))
            (sm (update-sm-backptrsi count n sm))
            (sm (set-sm-count newcount sm)))
         (mv sm count))))

(defun sm-put (n val sm)
  (declare (type (integer 0 *) n)
           (xargs :stobjs sm
                  :guard (and (sm-wfp sm)
                              (< n (sm-get-range sm)))
                  :guard-hints (("goal" :in-theory (e/d (sm-count-of-sm-add)
                                                        (sm-okp))))))
  (b* ((n (lnfix n))
       (sm (lsm-fix sm))
       ((mv sm (the (unsigned-byte 32) idx))
        (sm-add/idx n sm)))
    (sm-put-aux idx val sm)))


(defthm sm-put-of-sm-fix
  (equal (sm-put n val (sm-fix sm))
         (sm-put n val sm)))


;;(defthmd sm-okp-of-update-nth
;;  (implies (and (not (equal n *sm-count*))
;;                (not (equal n *sm-backptrsi*)))
;;           (equal (sm-okp (update-nth n v sm))
;;                  (sm-okp sm)))
;;  :hints(("Goal" :in-theory (enable nfix))))

(defthm sm-okp-of-sm-put-aux
  (implies (sm-okp sm)
           (sm-okp (sm-put-aux idx val sm))))

(defthm sm-okp-of-sm-put
  (implies (sm-okp sm)
           (sm-okp (sm-put n val sm))))

(defthm sm-data-of-sm-fix
  (equal (nth *sm-datai* (sm-fix sm))
         (nth *sm-datai* sm))
  :hints(("Goal" :in-theory (enable sm-fix))))

(definline sm-get-aux (idx sm)
  (declare (type (integer 0 *) idx)
           (xargs :stobjs sm))
  (b* ((idx (lnfix idx))
       ((when (<= (the (integer 0 *)
                    (sm-data-length sm))
                  idx))
        t))
    (sm-datai idx sm)))

(defthm sm-get-aux-of-sm-fix
  (equal (sm-get-aux idx (sm-fix sm))
         (sm-get-aux idx sm)))

(defcong nat-equiv equal (sm-get-aux idx sm) 1)


(defun sm-get (n sm)
  (declare (type (integer 0 *) n)
           (xargs :stobjs sm
                  :guard (and (sm-wfp sm)
                              (< n (sm-get-range sm)))))
  (b* ((n (lnfix n))
       (idx (sm-inp n sm))
       ((unless idx) nil))
    (sm-get-aux (the (unsigned-byte 32) idx) sm)))

(defthm sm-get-of-sm-fix
  (equal (sm-get n (sm-fix sm))
         (sm-get n sm)))

(defthmd sm-inp1-of-update-data
  (equal (sm-inp1 n (update-nth *sm-datai* val sm))
         (sm-inp1 n sm))
  :hints(("Goal" :in-theory (enable sm-inp1))))

(defthmd sm-data-of-sm-add
  (equal (nth *sm-datai* (sm-add m sm))
         (nth *sm-datai* sm))
  :hints(("Goal" :in-theory (enable sm-add sm-fix))))


(defthm sm-get-aux-of-sm-put-aux
  (equal (sm-get-aux i (sm-put-aux j val sm))
         (if (equal (nfix i) (nfix j))
             val
           (sm-get-aux i sm))))


(defthmd sm-compactp-aux-of-update-data
  (equal (sm-compactp-aux m (update-nth *sm-datai* val sm))
         (sm-compactp-aux m sm))
  :hints(("Goal" :in-theory (enable sm-inp1-of-update-data))))

(defthm sm-compactp-aux-of-sm-put-aux
  (equal (sm-compactp-aux m (sm-put-aux idx val sm))
         (sm-compactp-aux m sm))
  :hints(("Goal" :in-theory (e/d (sm-compactp-aux-of-update-data)
                                 (sm-compactp-aux)))))

(defthm sm-compactp-of-sm-put-aux
  (implies (sm-compactp sm)
           (sm-compactp (sm-put-aux idx val sm)))
  :hints(("Goal" :in-theory (e/d (sm-compactp-aux-of-sm-put-aux
                                  sm-compactp)
                                 (sm-compactp-aux sm-put-aux)))))

(defthm sm-wfp-of-sm-put-aux
  (implies (sm-wfp sm)
           (sm-wfp (sm-put-aux idx val sm)))
  :hints(("Goal" :in-theory (e/d (sm-wfp) (sm-put-aux)))))



(defthm sm-inp1-of-sm-put-aux
  (equal (sm-inp1 n (sm-put-aux idx val sm))
         (sm-inp1 n sm))
  :hints(("Goal" :in-theory (enable sm-inp1-of-update-data))))

(defthm sm-get-aux-of-sm-add
  (equal (sm-get-aux idx (sm-add m sm))
         (sm-get-aux idx sm))
  :hints(("Goal" :in-theory (enable sm-data-of-sm-add))))

(defthm sm-inp1-of-sm-put
  (equal (sm-inp1 n (sm-put m val sm))
         (sm-inp1 n (sm-add m sm)))
  :hints(("Goal" :in-theory (disable sm-put-aux
                                     sm-inp1-of-sm-add-equal))))


(defthm sm-get-of-sm-put
  (equal (sm-get n (sm-put m val sm))
         (if (equal (nfix n) (nfix m))
             val
           (sm-get n sm)))
  :hints(("Goal" :in-theory (e/d ()
                                 (sm-get-aux sm-put-aux))
          :cases ((sm-wfp sm)))))

(defthm sm-compactp-of-sm-put
  (implies (sm-compactp sm)
           (sm-compactp (sm-put n val sm)))
  :hints(("Goal" :in-theory (e/d ()
                                 (sm-compactp-aux sm-put-aux)))))

(encapsulate nil
  (local (defthmd sm-wfp-of-sm-put1
           (implies (sm-wfp sm)
                    (sm-wfp (sm-put n val sm)))
           :hints(("Goal" :in-theory (e/d (sm-wfp) (sm-put))))))

  (defthm sm-wfp-of-sm-put
    (sm-wfp (sm-put n val sm))
    :hints (("goal" :use ((:instance sm-wfp-of-sm-put1
                           (sm (sm-fix sm))))))))


(defthmd nth-of-sm-put-aux
  (implies (not (equal n *sm-datai*))
           (equal (nth n (sm-put-aux idx v sm))
                  (nth n sm)))
  :hints(("Goal" :in-theory (enable nfix))))

(defthm sm-eltcount-of-sm-put
  (equal (sm-eltcount (sm-put m v sm))
         (sm-eltcount (sm-add m sm)))
  :hints (("goal" :in-theory (disable sm-add sm-put))
          (and stable-under-simplificationp
               '(:in-theory (enable sm-put)))))

(defthm sm-inp-implies-count-nonzero
  (implies (sm-inp1 n sm)
           (posp (nth *sm-count* sm)))
  :hints(("Goal" :in-theory (enable sm-inp1 sm-fix nfix)))
  :rule-classes :type-prescription)

(defthm backptr-in-bounds-when-sm-compactp-aux
  (implies (and (sm-compactp-aux m sm)
                (<= (nfix m) (nfix n))
                (< (nfix n) (nfix (nth *sm-count* sm))))
           (< (nfix (nth n (nth *sm-backptrsi* sm)))
              (len (nth *sm-indicesi* sm))))
  :hints (("goal" :induct t)
          (and stable-under-simplificationp
               '(:expand ((sm-inp1 (nth m (nth *sm-backptrsi* sm)) sm))))))

(defthm sm-compactp-implies-backptr-in-range-natp
  (implies (and (sm-compactp sm)
                (< (nfix m) (nfix (sm-count sm)))
                (natp (nth m (nth *sm-backptrsi* sm))))
           (< (nth m (nth *sm-backptrsi* sm))
              (len (nth *sm-indicesi* sm))))
  :hints(("Goal" :in-theory (disable sm-compactp-implies-backptr-in-range)
          :use sm-compactp-implies-backptr-in-range))
  :rule-classes (:rewrite :linear))

(defun sm-delete (n sm)
  (declare (type (integer 0 *) n)
           (xargs :stobjs sm
                  :guard (and (sm-wfp sm)
                              (< n (sm-get-range sm)))
                  :guard-hints (("goal" :do-not-induct t))
                  :guard-debug t))
  (b* ((n (the (unsigned-byte 32) (lnfix n)))
       (sm (lsm-fix sm))
       (nidx (sm-inp n sm))
       ((unless nidx) sm)
       (count (the (and (unsigned-byte 32)
                        (integer 1 *))
                (sm-eltcount sm)))
       (lastidx (the (unsigned-byte 32)
                  (1- count)))
       ;; this must be bound b/c of compactness
       (lastelt (sm-get-backptr-fast lastidx sm))
       ;; data associated with lastelt
       (lastdata (sm-get-aux lastidx sm))
       ;; set up lastelt in n's slots
       (sm (set-sm-index-fast lastelt nidx sm))
       (sm (update-sm-backptrsi nidx lastelt sm))
       ;; move the data
       (sm (sm-put-aux nidx lastdata sm))
       ;; decrement the count
       (sm (update-sm-count lastidx sm)))
    sm))


(local (in-theory (disable sm-get-aux sm-put-aux)))


(defthm sm-compactp-implies-backptr-match-rev
  (implies (and (sm-compactp sm)
                (< (nfix m) (nfix (sm-count sm))))
           (nat-equiv (nth (nth m (nth *sm-backptrsi* sm))
                           (nth *sm-indicesi* sm))
                      m))
  :hints (("goal" :use sm-compactp-implies-backptr-match
           :in-theory (e/d (sm-inp1) (sm-compactp-implies-backptr-match)))))

(defthm sm-compactp-implies-backptr-match-rev-match
  (implies (and (sm-compactp sm)
                (equal (nfix n) (nfix (nth m (nth *sm-backptrsi* sm))))
                (< (nfix m) (nfix (sm-count sm))))
           (nat-equiv (nth n ;; (nth m (nth *sm-backptrsi* sm))
                           (nth *sm-indicesi* sm))
                      m))
  :hints (("goal" :use sm-compactp-implies-backptr-match
           :in-theory (e/d (sm-inp1) (sm-compactp-implies-backptr-match)))))



(defcong nat-equiv equal (sm-delete m sm) 1)

(defthm sm-inp1-of-sm-delete
  (iff (sm-inp1 n (sm-delete m sm))
       (and (not (equal (nfix n) (nfix m)))
            (sm-inp1 n (sm-fix sm))))
  :hints(("goal" :in-theory (e/d (sm-inp1 nth-of-sm-put-aux)
                                 (nth-out-of-bounds
                                  true-listp-update-nth
                                  natp-rw nth-in-u32-listp)))))

(defthm sm-compactp-aux-of-sm-delete
  (sm-compactp-aux n (sm-delete m sm))
  :hints(("Goal" :in-theory (e/d (sm-inp1 nth-of-sm-put-aux)
                                 (sm-compactp-implies-backptr-in-range-natp
                                  ;; nfix-when-zp
                                  natp-rw
                                  nth-in-u32-listp
                                  nth-out-of-bounds))
          :induct t)))

(defthm sm-wfp-of-sm-delete
  (sm-wfp (sm-delete n sm))
  :hints(("Goal" :in-theory (e/d (sm-wfp sm-compactp sm-okp)
                                 (sm-delete)))
         (and stable-under-simplificationp
              '(:in-theory (enable sm-delete
                                   nth-of-sm-put-aux)))
         (and stable-under-simplificationp
              '(:in-theory (enable sm-fix)))))

(defthmd sm-get-aux-of-update-nth
  (implies (not (equal n *sm-datai*))
           (equal (sm-get-aux idx (update-nth n v sm))
                  (sm-get-aux idx sm)))
  :hints(("Goal" :in-theory (enable sm-get-aux nfix))))

(encapsulate nil
  (local (in-theory (disable nth-out-of-bounds
                             ;; nfix-when-zp
                             nth-in-u32-listp)))
  (defthm sm-get-of-sm-delete
    (equal (sm-get n (sm-delete m sm))
           (and (not (equal (nfix n) (nfix m)))
                (sm-get n (sm-fix sm))))
    :hints(("Goal" :in-theory (e/d (sm-get) (sm-delete)))
           (and stable-under-simplificationp
                '(:in-theory (enable sm-delete sm-inp1
                                     sm-get-aux-of-update-nth
                                     nth-of-sm-put-aux))))))

;;;; This causes n to be unbound, but doesn't preserve compactness.
;;;; Returns the former index of n so that we can fix it up.
;;(definline sm-delete-aux (n sm)
;;  (declare (type (integer 0 *) n)
;;           (xargs :stobjs sm
;;                  :guard (and (sm-wfp sm)
;;                              (< n (sm-get-range sm)))))
;;  (b* ((n (the (unsigned-byte 32) (lnfix n)))
;;       (sm (lsm-fix sm))
;;       (idx (sm-inp n sm))
;;       ((unless idx) (mv sm nil))
;;       (idx (the (integer 0 *) idx))
;;       (count (the (and (unsigned-byte 32)
;;                        (integer 1 *))
;;                (sm-eltcount sm)))
;;       (sm (set-sm-index-u32 n count sm)))
;;    (mv sm idx)))

;;(defcong nat-equiv equal (sm-delete-aux n sm) 1)

;;(defthm sm-inp1-of-sm-delete-aux
;;  (equal (sm-inp1 m (mv-nth 0 (sm-delete-aux n sm)))
;;         (if (equal (nfix n) (nfix m))
;;             nil
;;           (sm-inp m sm)))
;;  :hints(("Goal" :in-theory (enable sm-inp1))))

;;(defthm sm-delete-aux-idx-type
;;  (or (not (mv-nth 1 (sm-delete-aux n sm)))
;;      (natp (mv-nth 1 (sm-delete-aux n sm))))
;;  :rule-classes :type-prescription)

;;(defthm sm-delete-aux-idx-bound
;;  (implies (mv-nth 1 (sm-delete-aux n sm))
;;           (< (mv-nth 1 (sm-delete-aux n sm))
;;              (nfix (nth *sm-count* sm))))
;;  :rule-classes :linear)

;;(defthm sm-delete-aux-count
;;  (equal (nfix (nth *sm-count* (mv-nth 0 (sm-delete-aux n sm))))
;;         (nfix (nth *sm-count* (sm-fix sm)))))


;;(local (defthmd integerp-+
;;         (implies (and (integerp x) (integerp y))
;;                  (integerp (+ x y)))))

;;(defthm sm-okp-of-sm-delete-aux
;;  (sm-okp (mv-nth 0 (sm-delete-aux n sm))))

;;;; Assumes idx is the index in backptrs of a deleted element.  Relocates the
;;;; last element to that index to restore compactness.
;;(definline sm-delete-fixup (idx sm)
;;  (declare (type (integer 0 *) idx)
;;           (xargs :stobjs sm
;;                  :guard (and (sm-okp sm)
;;                              (< 0 (sm-count sm))
;;                              (< idx (nfix (sm-count sm))))
;;                  :guard-debug t
;;                  :guard-hints (("goal" :do-not-induct t)
;;                                (and stable-under-simplificationp
;;                                     '(:in-theory (enable integerp-+)))
;;                                )))
;;  (b* ((idx (the (unsigned-byte 32) (lnfix idx)))
;;       (count (the (and (unsigned-byte 32)
;;                        (integer 1 *))
;;                (lnfix (sm-count sm))))
;;       (newcount (the (unsigned-byte 32) (1- count)))
;;       ;; decrease the count
;;       (sm (update-sm-count newcount sm))
;;       ((when (= newcount idx))
;;        ;; done because the element we deleted was the last
;;        sm)
;;       ;; lastn: element whose index is currently newcount
;;       (lastn (lnfix (sm-backptrsi newcount sm)))
;;       ;; this must equal newcount if we were previously compact
;;       ;; (lastidx (sm-get-index lastn sm))
;;       ;; check that
;;       ;; ((unless (= lastidx newcount)) sm)

;;       ;; restore validity of element by moving it to idx
;;       (sm (set-sm-index lastn idx sm))
;;       (sm (update-sm-backptrsi idx lastn sm))

;;       ;; move that element's data to its new slot
;;       (val (sm-get-aux newcount sm))
;;       (sm (sm-put-aux idx val sm)))
;;    sm))

;;(defthmd nth-of-sm-put-aux
;;  (implies (not (equal n *sm-datai*))
;;           (equal (nth n (sm-put-aux idx val sm))
;;                  (nth n sm)))
;;  :hints(("Goal" :in-theory (enable nfix))))

;;(defthmd nfix-equal-strong
;;  (equal (equal (nfix x) n)
;;         (and (natp n)
;;              (nat-equiv x n))))

;;(defthmd sm-get-aux-of-update
;;  (implies (not (equal n *sm-datai*))
;;           (equal (sm-get-aux idx (update-nth n v sm))
;;                  (sm-get-aux idx sm)))
;;  :hints(("Goal" :in-theory (enable nfix))))



;;(encapsulate nil
;;  (local (in-theory (e/d (sm-inp1
;;                          nth-of-sm-put-aux
;;                          sm-get-aux-of-update)
;;                         (nth-in-u32-listp
;;                          nfix-when-zp zp-open
;;                          true-listp-update-nth
;;                          len default-<-2 default-<-1
;;                          sm-get-aux sm-put-aux))))
;;  (set-default-hints '((and stable-under-simplificationp
;;                            '(:in-theory (e/d (nfix-equal-strong)
;;                                              (nat-equiv-to-zp))))))

;;  (defthm sm-inp1-of-sm-delete-fixup-<=
;;    (implies (and (not (equal (nfix idx)
;;                              (nfix (sm-indicesi (sm-backptrsi idx sm) sm))))
;;                  (< (nfix idx) (nfix (sm-count sm))))
;;             (implies (sm-inp1 n sm)
;;                      (sm-inp1 n (sm-delete-fixup idx sm))))
;;    :rule-classes nil)

;;  (defthm sm-inp1-of-sm-delete-fixup-=>
;;    (implies (and (not (equal (nfix idx)
;;                              (nfix (sm-indicesi (sm-backptrsi idx sm) sm))))
;;                  (< (nfix idx) (nfix (sm-count sm))))
;;             (implies (sm-inp1 n (sm-delete-fixup idx sm))
;;                      (sm-inp1 n sm)))
;;    :rule-classes nil)

;;  (defthm sm-inp1-of-sm-delete-fixup
;;    (implies (and (not (equal (nfix idx)
;;                              (nfix (sm-indicesi (sm-backptrsi idx sm) sm))))
;;                  (< (nfix idx) (nfix (sm-count sm))))
;;             (iff (sm-inp1 n (sm-delete-fixup idx sm))
;;                  (sm-inp1 n sm)))))


;;(defthm nat-equiv-non-natp
;;  (implies (and (syntaxp (quotep b))
;;                (not (natp b)))
;;           (equal (nat-equiv a b)
;;                  (nat-equiv a 0)))
;;  :hints(("Goal" :in-theory (e/d (nat-equiv)
;;                                 (equal-of-nfixes)))))

;;(encapsulate nil
;;  (local (in-theory (e/d (sm-inp
;;                          nth-of-sm-put-aux
;;                          sm-get-aux-of-update)
;;                         (nth-in-u32-listp
;;                          nfix-when-zp zp-open
;;                          true-listp-update-nth
;;                          len default-<-2 default-<-1
;;                          sm-get-aux sm-put-aux))))

;;  (defthm sm-backptrs-of-sm-delete-fixup
;;    (implies (and (not (equal (nfix idx)
;;                              (nfix (sm-indicesi (sm-backptrsi idx sm) sm))))
;;                  (< (nfix idx) (nfix (sm-count sm))))
;;             (nat-equiv
;;              (nth n (nth *sm-backptrsi* (sm-delete-fixup idx sm)))
;;              (if (and (equal (nfix n) (nfix idx))
;;                       (not (equal (nfix idx) (1- (nfix (sm-count sm)))))
;;                       (equal (1- (nfix (sm-count sm)))
;;                              (nfix (sm-indicesi
;;                                     (nfix (sm-backptrsi
;;                                            (1- (nfix (sm-count sm)))
;;                                            sm))
;;                                     sm))))
;;                  (nth (1- (nfix (sm-count sm)))
;;                       (nth *sm-backptrsi* sm))
;;                (nth n (nth *sm-backptrsi* sm)))))))

;;(defthm sm-okp-of-sm-delete-fixup
;;  (implies (sm-okp sm)
;;           (sm-okp (sm-delete-fixup idx sm)))
;;  :hints ((and stable-under-simplificationp
;;               '(:in-theory (enable nfix)))))

;;(defthm sm-inp1-is-not-sm-count
;;  (not (equal (sm-inp1 n sm) (nfix (nth *sm-count* sm))))
;;  :hints (("goal" :use sm-inp1-lt-count
;;           :in-theory (disable sm-inp1-lt-count))))

;;(defthm sm-inp1-implies-backptr
;;  (implies (sm-inp1 n sm)
;;           (nat-equiv (nth (sm-inp1 n sm)
;;                           (nth *sm-backptrsi* sm))
;;                      n))
;;  :hints(("Goal" :in-theory (enable sm-inp1))))


;;(defthm nth-of-sm-delete-aux
;;  (implies (not (equal (nfix n) *sm-indicesi*))
;;           (equal (nth n (mv-nth 0 (sm-delete-aux m sm)))
;;                  (nth n (sm-fix sm)))))

;;(defthm sm-delete-aux-idx-invalid
;;  (let* ((idx (sm-inp1 n (sm-fix sm)))
;;         (sm2 (mv-nth 0 (sm-delete-aux n sm))))
;;    (implies idx
;;             (not (equal idx
;;                         (nfix (nth (nth idx (nth *sm-backptrsi* (sm-fix sm)))
;;                                    (nth *sm-indicesi* sm2)))))))
;;  :hints(("Goal" :in-theory (enable nfix-equal-strong))))

;;(defthm sm-delete-aux-idx-invalid2
;;  (let* ((n (nth idx (nth *sm-backptrsi* (sm-fix sm))))
;;         (sm2 (mv-nth 0 (sm-delete-aux n sm))))
;;    (implies (and (sm-inp n sm)
;;                  (not (equal (nfix idx) (nfix (sm-count (sm-fix sm))))))
;;             (not (nat-equiv idx
;;                             (nth (nth idx (nth *sm-backptrsi* (sm-fix sm)))
;;                                  (nth *sm-indicesi* sm2))))))
;;  :hints(("Goal" :in-theory (e/d (nat-equiv) (equal-of-nfixes)))))

;;(defthm sm-delete-aux-idx-invalid3
;;  (let* ((idx (sm-inp1 n (sm-fix sm)))
;;         (sm2 (mv-nth 0 (sm-delete-aux n sm))))
;;    (implies idx
;;             (not (equal idx
;;                         (nfix (nth n (nth *sm-indicesi* sm2)))))))
;;  :hints(("Goal" :in-theory (enable nfix-equal-strong))))

;;(defthm sm-delete-aux-idx
;;  (equal (mv-nth 1 (sm-delete-aux n sm))
;;         (sm-inp n sm)))



;;;;(defthm sm-delete-aux-idx-lt-count
;;;;  (implies (mv-nth 1 (sm-delete-aux n sm))
;;;;           (< (mv-nth 1 (sm-delete-aux n sm))
;;;;              (nth *sm-count* sm)))
;;;;  :rule-classes (:rewrite :linear))

;;(in-theory (disable sm-delete-aux sm-delete-fixup))



;;(defun sm-delete (n sm)
;;  (declare (type (integer 0 *) n)
;;           (xargs :stobjs sm
;;                  :guard (and (sm-wfp sm)
;;                              (< n (sm-get-range sm)))
;;                  :guard-hints (("goal" :in-theory (disable sm-okp)))
;;                  :guard-debug t))
;;  (b* (((mv sm idx) (sm-delete-aux n sm))
;;       ((unless idx) sm))
;;    (sm-delete-fixup idx sm)))


;;(defthm sm-inp-of-sm-delete
;;  (iff (sm-inp1 n (sm-delete m sm))
;;       (if (equal (nfix n) (nfix m))
;;           nil
;;         (sm-inp n sm))))



;;(local (defthmd dumb-lemma
;;         (<= (nfix (+ -1 (nfix n)))
;;             (nfix n))
;;         :hints(("Goal" :in-theory (enable nfix)))))

;;(defthm sm-count-of-sm-delete-fixup
;;  (equal (nth *sm-count* (sm-delete-fixup idx sm))
;;         (1- (nfix (nth *sm-count* sm))))
;;  :hints(("Goal" :in-theory (e/d (sm-delete-fixup
;;                                  dumb-lemma)
;;                                 (nth-out-of-bounds)))))

;;(defthm sm-inp-of-sm-delete-fixup-lemma
;;  (implies (and (not (equal (nfix idx)
;;                            (nfix (sm-indicesi (sm-backptrsi idx sm) sm))))
;;                (< (nfix idx) (nfix (sm-count sm)))
;;                ;;(sm-inp x sm)
;;                ;;(not (equal (sm-inp x (sm-delete-fixup idx sm))
;;                ;;            (sm-inp x sm)))
;;                ;;(not (equal (sm-inp x (sm-delete-fixup idx sm))
;;                ;;            (nfix idx)))
;;                (< (nfix x) (nfix (sm-count
;;                                   (sm-delete-fixup idx sm))))
;;                (equal (sm-inp1 (sm-backptrsi x sm) sm)
;;                       (nfix x)))
;;           (equal (sm-inp1 (nth x (nth *sm-backptrsi*
;;                                       (sm-delete-fixup idx sm)))
;;                           (sm-delete-fixup idx sm))
;;                  (nfix x)))
;;  :hints(("Goal" :in-theory (e/d (sm-inp1 sm-delete-fixup)
;;                                 (true-listp-update-nth
;;                                  nfix-when-zp len natp-rw
;;                                  nth-in-u32-listp)))))


;;(defcong nat-equiv equal (sm-delete-fixup idx sm) 1
;;  :hints(("Goal" :in-theory (enable sm-delete-fixup))))

;;(defthm sm-inp-of-sm-delete-fixup-lemma2
;;  (implies (and (not (equal (nfix idx)
;;                            (nfix (sm-indicesi (sm-backptrsi idx sm) sm))))
;;                (< (nfix idx) (+ -1 (nfix (sm-count sm))))
;;                ;;(sm-inp x sm)
;;                ;;(not (equal (sm-inp x (sm-delete-fixup idx sm))
;;                ;;            (sm-inp x sm)))
;;                ;;(not (equal (sm-inp x (sm-delete-fixup idx sm))
;;                ;;            (nfix idx)))
;;                ;;(< (nfix x) (nfix (sm-count
;;                ;;                   (sm-delete-fixup idx sm))))
;;                (equal (sm-inp1 (sm-backptrsi (1- (nfix (sm-count sm))) sm) sm)
;;                       (nfix (1- (nfix (sm-count sm))))))
;;           (let ((x idx))
;;             (equal (sm-inp1 (nth x (nth *sm-backptrsi*
;;                                           (sm-delete-fixup idx sm)))
;;                               (sm-delete-fixup idx sm))
;;                    (nfix x))))
;;  :hints(("Goal" :in-theory (e/d (sm-inp1 sm-delete-fixup)
;;                                 (true-listp-update-nth
;;                                  nfix-when-zp len natp-rw
;;                                  nth-in-u32-listp)))))










;;(encapsulate nil

;;  (local (in-theory (e/d (sm-compactp-aux-lemma)
;;                         (sm-backptrs-of-sm-delete-fixup
;;                          sm-inp1-implies-backptr
;;                          ;; sm-inp-of-sm-delete-aux
;;                          (:definition sm-compactp-aux)))))

;;  (local
;;   (defthm terrible-lemma
;;     (let ((sm2 (mv-nth 0 (sm-delete-aux (nth m (nth *sm-backptrsi* (sm-fix sm)))
;;                                        sm))))
;;       (implies (and (< (nfix m) (+ -1 (nth *sm-count* (sm-fix sm))))
;;                     (sm-inp1 (nth m (nth *sm-backptrsi* (sm-fix sm)))
;;                              (sm-fix sm)))
;;                (equal (sm-inp1
;;                        (nth (+ -1 (nth *sm-count* (sm-fix sm)))
;;                             (nth *sm-backptrsi* (sm-fix sm)))
;;                        sm2)
;;                       (+ -1 (nth *sm-count* (sm-fix sm))))))))


;;  (local (defun ind (m max)
;;           (declare (xargs :measure (nfix (- (nfix max) (nfix m)))))
;;           (if (zp (- (nfix max) (nfix m)))
;;               m
;;             (ind (1+ (nfix m)) max))))

;;  (defthm sm-compactp-aux-of-sm-delete
;;    (sm-compactp-aux m (sm-delete n sm))
;;    :hints (("goal" :induct (ind m (sm-count (sm-delete n sm)))
;;             :in-theory (e/d (nat-equiv)
;;                             (equal-of-nfixes))
;;             :expand ((sm-compactp-aux m (mv-nth 0 (sm-delete-aux n sm)))
;;                      (:free (i sm)
;;                       (sm-compactp-aux m (sm-delete-fixup i sm))))
;;             :do-not-induct t)
;;            (and stable-under-simplificationp
;;                 '(:cases ((equal (nfix n)
;;                                  (nfix (sm-backptrsi m (sm-fix sm)))))))
;;            (and stable-under-simplificationp
;;                 '(:in-theory (enable)))))


;;  (defthm sm-compactp-of-sm-delete
;;    (sm-compactp (sm-delete n sm))
;;    :hints(("Goal" :in-theory (e/d (sm-compactp)
;;                                   (sm-compactp-aux sm-delete)))))

;;  (defthm sm-wfp-of-sm-delete
;;    (sm-wfp (sm-delete n sm))
;;    :hints(("Goal" :in-theory (e/d (sm-wfp) (sm-okp))))))

;;(defthm sm-get-aux-of-sm-delete-aux
;;  (equal (sm-get-aux n (mv-nth 0 (sm-delete-aux m sm)))
;;         (sm-get-aux n sm)))

;;(defstub foo () nil)

;;(defthm sm-get-aux-of-sm-delete-fixup
;;  (implies (sm-inp1 n (sm-delete-fixup m sm))
;;           (equal (sm-get-aux (sm-inp1 n (sm-delete-fixup m sm))
;;                              (sm-delete-fixup m sm))
;;                  (sm-get-aux (sm-inp1 n sm) sm)))
;;  :hints(("Goal" :in-theory (enable sm-delete-fixup sm-inp1)))
;;  :otf-flg t)

;;(defthm sm-get-of-sm-delete
;;  (equal (sm-get n (sm-delete m sm))
;;         (if (equal (nfix n) (nfix m))
;;             nil
;;           (sm-get n sm)))
;;  :hints(("Goal" :in-theory (e/d (sm-get)
;;                                 (sm-wfp-of-sm-delete
;;                                  sm-inp1
;;                                  sm-get-aux
;;                                  sm-delete))
;;          :use ((:instance sm-wfp-of-sm-delete
;;                 (n m))))
;;         (and stable-under-simplificationp
;;              '(:in-theory (e/d (sm-delete) (sm-inp1 sm-get-aux))))))



(defun sm-alist-aux (m sm)
  (declare (type (integer 0 *) m)
           (xargs :stobjs sm
                  :guard (and (sm-wfp sm)
                              (count-up-guard m (sm-eltcount sm)))
                  :measure (count-up-meas m (sm-eltcount sm))))
  (if (count-up-done m (sm-eltcount sm))
      nil
    (cons (cons (nfix (sm-backptrsi m sm))
                (sm-get-aux m sm))
          (sm-alist-aux (1+ (lnfix m)) sm))))


(defthm sm-alist-aux-of-sm-fix
  (equal (sm-alist-aux m (sm-fix sm))
         (sm-alist-aux m sm))
  :hints (("goal" :induct t)
          (and stable-under-simplificationp
               '(:cases ((sm-wfp sm))))))

(defun sm-alist (sm)
  (declare (xargs :stobjs sm
                  :guard (sm-wfp sm)))
  (sm-alist-aux 0 sm))


(defthm sm-compactp-implies-indices-lemma
  (implies (and (sm-compactp sm)
                (< (nfix n) (nfix (sm-count sm))))
           (equal (nfix (nth (nth n (nth *sm-backptrsi* sm))
                             (nth *sm-indicesi* sm)))
                  (nfix n)))
  :hints (("goal" :use ((:instance sm-compactp-implies-backptr-match
                         (m n)))
           :in-theory (e/d (sm-inp1)
                           (sm-compactp-implies-backptr-match)))))

(encapsulate
  nil
  (local (defthm lemma
           (implies (and ; (sm-wfp sm)
                         (< (nfix m) (nfix n)))
                    (not (member-equal (nfix (nth m (nth *sm-backptrsi* sm)))
                                       (strip-cars (sm-alist-aux n sm)))))
           :hints (("goal" :induct t)
                   '(:cases ((sm-wfp sm))))))

  (defthm no-duplicatesp-of-strip-cars-of-sm-alist-aux
    (no-duplicatesp (strip-cars (sm-alist-aux m sm)))))

(defthm no-duplicatesp-of-strip-cars-of-sm-alist
  (no-duplicatesp (strip-cars (sm-alist sm)))
  :hints(("Goal" :in-theory (enable sm-alist))))

(encapsulate nil
  (local (defthmd assoc-in-sm-alist-aux-lemma
           (implies (sm-wfp sm)
                    (equal (assoc n (sm-alist-aux m sm))
                           (and (natp n)
                                (sm-inp n sm)
                                (<= (nfix m) (sm-inp n sm))
                                (cons n (sm-get n sm)))))
           :hints(("Goal" :in-theory (e/d (sm-inp1 sm-get)
                                          (sm-get-aux))))))
  (defthm assoc-in-sm-alist-aux
    (equal (assoc n (sm-alist-aux m sm))
           (and (natp n)
                (sm-inp n sm)
                (<= (nfix m) (sm-inp n sm))
                (cons n (sm-get n sm))))
    :hints (("goal" :use ((:instance assoc-in-sm-alist-aux-lemma
                           (sm (sm-fix sm))))
             :in-theory (disable sm-alist-aux sm-get)))))


(defthm assoc-in-sm-alist
  (equal (assoc n (sm-alist sm))
         (and (natp n)
              (sm-inp n sm)
              (cons n (sm-get n sm))))
  :hints(("Goal" :in-theory (e/d (sm-alist) (sm-alist-aux sm-get)))))


(defthm sm-wfp-of-sm-create
  (sm-wfp '(nil nil nil 0 0)))


(defthm sm-inp-of-sm-create
  (not (sm-inp n '(nil nil nil 0 0)))
  :hints(("Goal" :in-theory (enable sm-inp1))))

(defthm sm-inp-of-sm-clear
  (not (sm-inp n (sm-clear sm))))

(defthm sm-inp-of-sm-add-same
  (iff (sm-inp n (sm-add n sm))
       t))

(defthm sm-inp-of-sm-add-diff
  (implies (not (equal (nfix n) (nfix m)))
           (iff (sm-inp n (sm-add m sm))
                (sm-inp n sm))))

(defthmd sm-inp-of-sm-add-casesplit
  (iff (sm-inp n (sm-add m sm))
       (or (equal (nfix n) (nfix m))
           (sm-inp n sm))))

(defthm sm-inp-of-sm-put-same-as-sm-add
  (iff (sm-inp n (sm-put m v sm))
       (sm-inp n (sm-add m sm)))
  :hints(("Goal" :in-theory (disable sm-put))))

(defthm sm-inp-of-sm-delete-same
  (not (sm-inp n (sm-delete n sm)))
  :hints(("Goal" :in-theory (disable sm-delete))))

(defthm sm-inp-of-sm-delete-diff
  (implies (not (equal (nfix n) (nfix m)))
           (iff (sm-inp n (sm-delete m sm))
                (sm-inp n sm)))
  :hints(("Goal" :in-theory (disable sm-delete))))

(defthmd sm-inp-of-sm-delete-casesplit
  (iff (sm-inp n (sm-delete m sm))
       (and (not (equal (nfix n) (nfix m)))
            (sm-inp n sm)))
  :hints(("Goal" :in-theory (disable sm-delete))))



(defthm sm-get-of-sm-create
  (not (sm-get n '(nil nil nil 0 0)))
  :hints(("Goal" :in-theory (enable sm-inp1))))

(defthm sm-get-of-sm-put-same
  (equal (sm-get n (sm-put n v sm))
         v)
  :hints(("Goal" :in-theory (disable sm-get sm-put))))

(defthm sm-get-of-sm-put-diff
  (implies (not (equal (nfix n) (nfix m)))
           (equal (sm-get n (sm-put m v sm))
                  (sm-get n sm)))
  :hints(("Goal" :in-theory (disable sm-get sm-put))))

(defthm sm-get-of-sm-put-casesplit
  (equal (sm-get n (sm-put m v sm))
         (if (equal (nfix n) (nfix m))
             v
           (sm-get n sm)))
  :hints(("Goal" :in-theory (disable sm-get sm-put))))

(defthm sm-get-of-sm-delete-same
  (not (sm-get n (sm-delete n sm)))
  :hints(("Goal" :in-theory (disable sm-get-aux sm-delete))))

(defthm sm-get-of-sm-delete-diff
  (implies (not (equal (nfix n) (nfix m)))
           (equal (sm-get n (sm-delete m sm))
                  (sm-get n sm)))
  :hints(("Goal" :in-theory (disable sm-get sm-delete))))

(defthm sm-eltcount-of-sm-delete
  (equal (sm-eltcount (sm-delete n sm))
         (if (sm-inp n sm)
             (1- (sm-eltcount sm))
           (sm-eltcount sm)))
  :hints(("Goal" :in-theory (disable sm-delete))
         (and stable-under-simplificationp
              '(:in-theory (enable sm-delete)))))


(in-theory (disable sm-delete sm-get sm-put sm-wfp sm-add sm-inp sm-clear sm-inp))



;; Set range.

(defun sm-set-range (n sm)
  (declare (type (integer 0 *) n)
           (xargs :stobjs sm
                  :guard (sm-wfp sm)))
  (b* ((sm (lsm-fix sm)))
    (sm-set-range1 n sm)))

(defthm sm-inp1-of-sm-set-range
  (equal (sm-inp1 n (sm-set-range m sm))
         (sm-inp1 n (sm-fix sm)))
  :hints(("Goal" :in-theory (enable sm-inp1))))

(defthm sm-compactp-aux-of-sm-set-range
  (sm-compactp-aux m (sm-set-range n sm))
  :hints(("Goal" :in-theory (disable sm-set-range)
          :induct t)
         (and stable-under-simplificationp
              '(:in-theory (enable sm-set-range sm-inp1)))))

(defthm sm-wfp-of-sm-set-range
  (sm-wfp (sm-set-range n sm))
  :hints(("Goal" :in-theory (enable sm-wfp sm-compactp)))
  :otf-flg t)

(defthm sm-inp-of-sm-set-range
  (equal (sm-inp n (sm-set-range m sm))
         (sm-inp n sm))
  :hints(("Goal" :in-theory (e/d (sm-inp-is-sm-inp1-local)
                                 (sm-set-range)))))

(defthm sm-get-aux-of-sm-set-range
  (equal (sm-get-aux n (sm-set-range m sm))
         (sm-get-aux n sm))
  :hints(("Goal" :in-theory (enable sm-set-range sm-fix sm-get-aux))))

(defthm sm-get-of-sm-set-range
  (equal (sm-get n (sm-set-range m sm))
         (sm-get n sm))
  :hints(("Goal" :in-theory (e/d (sm-get) (sm-set-range)))))

(defthm sm-eltcount-of-sm-set-range
  (equal (sm-eltcount (sm-set-range n sm))
         (sm-eltcount sm))
  :hints(("Goal" :in-theory (disable sm-set-range))
         (and stable-under-simplificationp
              '(:in-theory (enable sm-set-range)))))

(defthm sm-eltcount-of-sm-clear
  (equal (sm-eltcount (sm-clear sm))
         0)
  :hints((and stable-under-simplificationp
              '(:in-theory (enable sm-clear)))))


(defthmd sm-get-of-sm-delete-casesplit
  (equal (sm-get n (sm-delete m sm))
         (and (not (equal (nfix n) (nfix m)))
              (sm-get n sm))))

(defthm sm-get-range-of-sm-create
  (equal (sm-get-range '(nil nil nil 0 0)) 0))

(defthm sm-get-range-of-sm-clear
  (equal (sm-get-range (sm-clear sm))
         (sm-get-range sm))
  :hints(("Goal" :in-theory (enable sm-clear))))

(defthm sm-get-range-of-sm-add
  (equal (sm-get-range (sm-add n sm))
         (sm-get-range sm)))

(defthm sm-get-range-of-sm-delete
  (equal (sm-get-range (sm-delete n sm))
         (sm-get-range sm))
  :hints(("Goal" :in-theory (enable sm-delete sm-put-aux))))

(defthm sm-get-range-of-sm-put
  (equal (sm-get-range (sm-put n v sm))
         (sm-get-range sm))
  :hints(("Goal" :in-theory (enable sm-put sm-put-aux))))

(defthm sm-get-range-of-sm-set-range
  (equal (sm-get-range (sm-set-range n sm))
         (nfix n)))

(defthm type-of-sm-get-range
  (implies (smp sm)
           (natp (sm-get-range sm)))
  :rule-classes :type-prescription)


(defun smsetp$a (smset)
  (declare (xargs :guard t))
  (and (consp smset)
       (true-listp (car smset))
       (natp (cdr smset))))

(defun smset-create$a ()
  (declare (xargs :guard t))
  (cons nil 0))

(defun smset-get-range$a (smset)
  (declare (xargs :guard (smsetp$a smset)))
  (lnfix (cdr smset)))

(defun smset-set-range$a (n smset)
  (declare (xargs :guard (and (natp n)
                              (smsetp$a smset))))
  (cons (car smset)
        (lnfix n)))

(defun smset-inp$a (n smset)
  (declare (xargs :guard (and (natp n)
                              (smsetp$a smset)
                              (< n (smset-get-range$a smset)))))
  (consp (member (lnfix n) (car smset))))

(defun smset-add$a (n smset)
  (declare (xargs :guard (and (natp n)
                              (smsetp$a smset)
                              (< n (smset-get-range$a smset)))))
  (if (member (lnfix n) (car smset))
      smset
    (cons (cons (lnfix n) (car smset))
          (cdr smset))))

(defun smset-delete$a (n smset)
  (declare (xargs :guard (and (natp n)
                              (smsetp$a smset)
                              (< n (smset-get-range$a smset)))))
  (cons (remove (lnfix n) (car smset))
        (cdr smset)))

(defun smset-eltcount$a (smset)
  (declare (xargs :guard (smsetp$a smset)))
  (len (car smset)))

(defun smset-clear$a (smset)
  (declare (xargs :guard (smsetp$a smset)))
  (cons nil (cdr smset)))


(include-book "centaur/misc/equal-sets" :dir :system)


(definline smset-inp$c (n sm)
  (declare (xargs :stobjs sm
                  :guard (and (natp n)
                              (sm-wfp sm)
                              (< n (sm-get-range sm)))))
  (and (sm-inp n sm) t))


(local (defthm consp-member-equal-iff
         (iff (consp (member-equal k x))
              (member-equal k x))))

(local (set-default-hints '((set-reasoning))))

;; (defthm nat-listp-remove-equal
;;   (implies (nat-listp x)
;;            (nat-listp (remove-equal k x))))

(defthm no-duplicatesp-remove-equal
  (implies (no-duplicatesp x)
           (no-duplicatesp (remove-equal k x))))

(local (in-theory (disable sm-set-range)))

(encapsulate nil
  (local (defun no-dups-len-ind (x y)
           (if (atom x)
               y
             (no-dups-len-ind (cdr x) (remove (car x) y)))))
  (local (defthm len-remove
           (implies (no-duplicatesp y)
                    (equal (len (remove k y))
                           (if (member k y)
                               (1- (len y))
                             (len y))))))
  (local (defthm len-when-no-duplicates-and-set-equiv
           (implies (and (set-equiv x y)
                         (no-duplicatesp x)
                         (no-duplicatesp y))
                    (equal (len x) (len y)))
           :hints (("goal" :induct (no-dups-len-ind x y))
                   (set-reasoning))
           :rule-classes nil))

  (defthm len-lemma-for-eltcount
    (implies (and (set-equiv x (sm-list sm))
                  (no-duplicatesp x))
             (equal (len x)
                    (len (sm-list sm))))
    :hints (("goal" :use ((:instance
                           len-when-no-duplicates-and-set-equiv
                           (x x) (y (sm-list sm))))))))

(encapsulate nil
  (local (defun-nx smset$corr (sm smset)
           (and (smsetp$a smset)
                (sm-wfp sm)
                (set-equiv (car smset) (sm-list sm))
                (no-duplicatesp (car smset))
                (equal (smset-get-range$a smset)
                       (sm-get-range sm)))))

  (local (in-theory (disable (smset$corr))))

  ;; This abstracts a set-only sparsemap (no sm-set/sm-get, only sm-add/sm-inp)
  ;; as a pair of a list and an upper bound (range)
  (defabsstobj-events smset
    :foundation sm
    :recognizer (smsetp :logic smsetp$a :exec smp)
    :creator (smset-create :logic smset-create$a :exec create-sm)
    :corr-fn smset$corr
    :exports ((smset-get-range :logic smset-get-range$a :exec sm-get-range$inline)
              (smset-inp :logic smset-inp$a :exec smset-inp$c$inline)
              (smset-add :logic smset-add$a :exec sm-add
                         :protect t)
              (smset-delete :logic smset-delete$a :exec sm-delete
                            :protect t)
              (smset-set-range :logic smset-set-range$a :exec sm-set-range
                               :protect t)
              (smset-eltcount :logic smset-eltcount$a :exec sm-eltcount$inline)
              (smset-clear :logic smset-clear$a :exec sm-clear$inline
                           :protect t))))




(defun smmapp$a (smmap)
  (declare (xargs :guard t))
  (and (consp smmap)
       (alistp (car smmap))
       (natp (cdr smmap))))

(defun smmap-create$a ()
  (declare (xargs :guard t))
  (cons nil 0))

(defun smmap-get-range$a (smmap)
  (declare (xargs :guard (smmapp$a smmap)))
  (lnfix (cdr smmap)))

(defun smmap-set-range$a (n smmap)
  (declare (xargs :guard (and (natp n)
                              (smmapp$a smmap))))
  (cons (car smmap)
        (nfix n)))

(defun smmap-inp$a (n smmap)
  (declare (xargs :guard (and (natp n)
                              (smmapp$a smmap)
                              (< n (smmap-get-range$a smmap)))))
  (consp (assoc (lnfix n) (car smmap))))

(defun smmap-get$a (n smmap)
  (declare (xargs :guard (and (natp n)
                              (smmapp$a smmap)
                              (< n (smmap-get-range$a smmap)))))
  (cdr (assoc (lnfix n) (car smmap))))

(defun smmap-put$a (n v smmap)
  (declare (xargs :guard (and (natp n)
                              (smmapp$a smmap)
                              (< n (smmap-get-range$a smmap)))))
    (cons (cons (cons (lnfix n) v) (car smmap))
          (cdr smmap)))

(defun smmap-delete$a (n smmap)
  (declare (xargs :guard (and (natp n)
                              (smmapp$a smmap)
                              (< n (smmap-get-range$a smmap)))))
  (cons (remove-assoc (lnfix n) (car smmap))
        (cdr smmap)))

(defun smmap-eltcount$a (smmap)
  (declare (xargs :guard (smmapp$a smmap)))
  (len (remove-duplicates-equal (strip-cars (car smmap)))))

(defun smmap-clear$a (smmap)
  (declare (xargs :guard (smmapp$a smmap)))
  (cons nil (cdr smmap)))


(include-book "centaur/misc/alist-equiv" :dir :system)


(definline smmap-inp$c (n sm)
  (declare (xargs :stobjs sm
                  :guard (and (natp n)
                              (sm-wfp sm)
                              (< n (sm-get-range sm)))))
  (and (sm-inp n sm) t))


(local (in-theory (disable sm-alist)))

(local (set-default-hints nil))

(local (defthmd assoc-when-alistp
         (implies (alistp a)
                  (equal (assoc k a)
                         (hons-assoc-equal k a)))))

(defthm alistp-sm-alist-aux
  (alistp (sm-alist-aux n x)))

(defthm alistp-sm-alist
  (alistp (sm-alist x))
  :hints(("Goal" :in-theory (enable sm-alist))))

(local
 (defthm assoc-in-sm-alist-rewrite
   (implies (and (alist-equiv x (sm-alist sm))
                 (alistp x))
            (equal (assoc k x)
                   (assoc k (sm-alist sm))))
   :hints(("Goal" :in-theory (e/d (assoc-when-alistp)
                                  (assoc-in-sm-alist))))))

(defthm sm-get-when-not-sm-inp1
  (implies (not (sm-inp1 n (sm-fix sm)))
           (not (sm-get n sm)))
  :hints(("Goal" :in-theory (enable sm-get))))

(defthmd alist-equiv-iff-agree-on-bad-guy-for-assoc
  (implies (and (syntaxp ((lambda (al1 al2 mfc state)
                            (declare (ignore state))
                            (and (null (mfc-ancestors mfc))
                                 (member-equal `(alist-equiv ,al1 ,al2)
                                               (mfc-clause mfc))))
                          al1 al2 mfc state))
                (alistp al1) (alistp al2))
           (iff (alist-equiv al1 al2)
                (let ((bg (alist-equiv-bad-guy al1 al2)))
                  (equal (assoc bg al1)
                         (assoc bg al2)))))
  :hints(("Goal" :in-theory (enable alist-equiv-iff-agree-on-bad-guy
                                    assoc-when-alistp))))

(defthm alistp-of-remove-assoc
  (implies (alistp x)
           (alistp (remove-assoc k x))))

(local (set-default-hints '((and stable-under-simplificationp
                                 '(:in-theory (enable alist-equiv-iff-agree-on-bad-guy-for-assoc))))))

(defthm remove-duplicates-when-no-duplicatesp
  (implies (and (no-duplicatesp x)
                (true-listp x))
           (equal (remove-duplicates-equal x) x)))

(defthm len-sm-alist-aux
  (equal (len (sm-alist-aux m sm))
         (nfix (- (sm-eltcount sm) (nfix m)))))

(defthm len-sm-alist
  (equal (len (sm-alist sm))
         (sm-eltcount sm))
  :hints(("Goal" :in-theory (enable sm-alist))))

(encapsulate nil
  (local (defun ind (x y)
           (if (atom x)
               y
             (ind (remove-assoc (caar x) (cdr x)) (remove-assoc (caar x) y)))))
  (local (defthm member-strip-cars
           (implies (alistp x)
                    (iff (member k (strip-cars x))
                         (assoc k x)))))
  (local (defthm len-remove-dups-cars-remove-assoc
           (implies (alistp x)
                    (equal (len (remove-duplicates-equal (strip-cars (remove-assoc k
                                                                                   x))))
                           (if (assoc k x)
                               (1- (len (remove-duplicates-equal (strip-cars x))))
                             (len (remove-duplicates-equal (strip-cars x))))))
           :hints (("Goal" :in-theory (enable remove-assoc-equal)))))

  (local (defthm not-alist-equiv-when-lookup-unequal
           (implies (and (alistp x) (alistp y)
                         (not (equal (assoc k (cdr x))
                                     (assoc k y)))
                         (not (equal k (caar x)))
                         (consp x) (consp (car x)))
                    (not (alist-equiv x y)))
           :hints(("Goal" :in-theory (enable assoc-when-alistp
                                             hons-assoc-equal)))))

  (local (defthm alist-equiv-nil-when-alistp
           (implies (alistp y)
                    (iff (alist-equiv nil y)
                         (atom y)))
           :hints (("goal"
                    :expand ((alistp y))
                    ;; :in-theory (enable assoc-when-alistp)
                    :do-not-induct t)
                   (and stable-under-simplificationp
                        '(:use ((:instance
                                 alist-equiv-implies-equal-hons-assoc-equal-2
                                 (x (caar y))
                                 (a nil) (a-equiv y)))
                               :in-theory
                               (e/d (alist-equiv)
                                    (alist-equiv-implies-equal-hons-assoc-equal-2)))))))

  (local (encapsulate
           ()
           (local (defthm l0
                    (implies (alistp x)
                             (equal (assoc-equal key x)
                                    (hons-assoc-equal key x)))))

           (local (defthm l1
                    (implies (and (alistp x)
                                  (alistp y)
                                  (assoc-equal key x)
                                  (not (assoc-equal key y)))
                             (not (alist-equiv x y)))))

           (defthm helper
             (implies (and (consp x)
                           (alistp x)
                           (alistp y)
                           (NOT (ASSOC-EQUAL (FIRST (FIRST X)) Y)))
                      (not (alist-equiv x y)))
             :hints(("Goal"
                     :in-theory (disable l1 l0)
                     :use ((:instance l1 (key (caar x)))))))))

  (defthmd len-remove-dups-strip-cars-when-alist-equiv
    (implies (and (alist-equiv x y)
                  (alistp x)
                  (alistp y))
             (equal (len (remove-duplicates-equal (strip-cars x)))
                    (len (remove-duplicates-equal (strip-cars y)))))
    :hints (("goal"
             :in-theory (disable strip-cars-of-remove-assoc-equal)
             :induct (ind x y)
             :do-not-induct t)))

  (defthm len-remove-dups-lemma-for-eltcount
    (implies (and (alist-equiv x (sm-alist sm))
                  (alistp x))
             (equal (len (remove-duplicates-equal (strip-cars x)))
                    (len (strip-cars (sm-alist sm)))))
    :hints (("goal" :use ((:instance len-remove-dups-strip-cars-when-alist-equiv
                                     (y (sm-alist sm))))))))


(encapsulate
  nil
  (local (defun-nx smmap$corr (sm smmap)
           (and (smmapp$a smmap)
                (sm-wfp sm)
                (alist-equiv (car smmap) (sm-alist sm))
                (equal (smmap-get-range$a smmap)
                       (sm-get-range sm)))))

  (local (in-theory (disable (smmap$corr))))

  ;; This abstracts a set-only sparsemap (no sm-set/sm-get, only sm-add/sm-inp)
  ;; as a pair of a list and an upper bound (range)
  (defabsstobj-events smmap
    :foundation sm
    :recognizer (smmapp :logic smmapp$a :exec smp)
    :creator (smmap-create :logic smmap-create$a :exec create-sm)
    :corr-fn smmap$corr
    :exports ((smmap-get-range :logic smmap-get-range$a :exec sm-get-range$inline)
              (smmap-inp :logic smmap-inp$a :exec smmap-inp$c$inline)
              (smmap-get :logic smmap-get$a :exec sm-get)
              (smmap-put :logic smmap-put$a :exec sm-put
                         :protect t)
              (smmap-delete :logic smmap-delete$a :exec sm-delete
                            :protect t)
              (smmap-set-range :logic smmap-set-range$a :exec sm-set-range
                               :protect t)
              (smmap-eltcount :logic smmap-eltcount$a :exec sm-eltcount$inline)
              (smmap-clear :logic smmap-clear$a :exec sm-clear$inline
                           :protect t))))







(defun-nx create-sm$a ()
  (declare (xargs :guard t))
  (create-sm))

(defun-nx sm$ap (sm)
  (declare (xargs :guard t))
  (ec-call (sm-wfp sm)))


(defun-nx sm$a-get-range (sm)
  (declare (xargs :guard (sm$ap sm)))
  (ec-call (sm-get-range sm)))

(defun-nx sm$a-get (n sm)
  (declare (xargs :guard (and (natp n)
                              (sm$ap sm)
                              (< n (sm$a-get-range sm)))))
  (ec-call (sm-get n sm)))

(defun-nx sm$a-inp (n sm)
  (declare (xargs :guard (and (natp n)
                              (sm$ap sm)
                              (< n (sm$a-get-range sm)))))
  (ec-call (sm-inp n sm)))


(defun-nx sm$a-add (n sm)
  (declare (xargs :guard (and (natp n)
                              (sm$ap sm)
                              (< n (sm$a-get-range sm)))))
  (ec-call (sm-add n sm)))

(defun-nx sm$a-put (n val sm)
  (declare (xargs :guard (and (natp n)
                              (sm$ap sm)
                              (< n (sm$a-get-range sm)))))
  (ec-call (sm-put n val sm)))

(defun-nx sm$a-eltcount (sm)
  (declare (xargs :guard (sm$ap sm)))
  (ec-call (sm-eltcount sm)))

(defun-nx sm$a-set-range (n sm)
  (Declare (Xargs :guard (and (natp n) (sm$ap sm))))
  (ec-call (sm-set-range n sm)))

(defun-nx sm$a-delete (n sm)
  (declare (xargs :guard (and (natp n) (sm$ap sm)
                              (< n (sm$a-get-range sm)))))
  (ec-call (sm-delete n sm)))

(defun-nx sm$a-clear (sm)
  (declare (xargs :guard (sm$ap sm)))
  (ec-call (sm-clear sm)))


;; This "abstracts" a sparsemap as just a sparsemap, but folds sm-wfp into the
;; stobj recognizer.
(defabsstobj-events sma
    :foundation sm
    :recognizer (smap :logic sm$ap :exec smp)
    :creator (create-sma :logic create-sm$a :exec create-sm)
    :corr-fn equal
    :exports ((sma-get-range :logic sm$a-get-range :exec sm-get-range$inline)
              (sma-get :logic sm$a-get :exec sm-get)
              (sma-inp :logic sm$a-inp :exec sm-inp$inline)
              (sma-add :logic sm$a-add :exec sm-add
                       :protect t)
              (sma-put :logic sm$a-put :exec sm-put
                       :protect t)
              (sma-eltcount :logic sm$a-eltcount :exec sm-eltcount$inline)
              (sma-set-range :logic sm$a-set-range :exec sm-set-range
                             :protect t)
              (sma-delete :logic sm$a-delete :exec sm-delete
                          :protect t)
              (sma-clear :logic sm$a-clear :exec sm-clear$inline
                          :protect t)))
