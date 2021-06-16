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
(include-book "count-up")
(include-book "remove-assoc")
(include-book "std/basic/arith-equivs" :dir :system)
(include-book "misc/definline" :dir :system)
(include-book "std/util/bstar" :dir :system)
(local (include-book "sparsemap-impl"))
(set-enforce-redundancy t)

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
  (and (<= (lnfix (sm-count sm))
           (sm-backptrs-length sm))
       (<= (sm-get-range sm)
           (sm-indices-length sm))))

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

(defmacro lsm-fix (smv)
  `(mbe :logic (sm-fix ,smv) :exec ,smv))

(definlined sm-eltcount (sm)
  (declare (xargs :stobjs sm :guard (sm-wfp sm)))
  (mbe :logic (if (sm-wfp sm) (nfix (sm-count sm)) 0)
       :exec (sm-count sm)))


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

(defcong nat-equiv equal (sm-inp n sm) 1)

(definline sm-clear (sm)
  (declare (xargs :stobjs sm
                  :guard (sm-wfp sm)))
  (b* ((sm (lsm-fix sm)))
    (update-sm-count 0 sm)))

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

(defcong nat-equiv equal (sm-add n sm) 1)

(definline sm-get-count (sm)
  (declare (xargs :stobjs sm))
  (the (unsigned-byte 32)
    (lnfix (sm-count sm))))


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

(definline sm-get-aux (idx sm)
  (declare (type (integer 0 *) idx)
           (xargs :stobjs sm))
  (b* ((idx (lnfix idx))
       ((when (<= (the (integer 0 *)
                    (sm-data-length sm))
                  idx))
        t))
    (sm-datai idx sm)))


(defun sm-get (n sm)
  (declare (type (integer 0 *) n)
           (xargs :stobjs sm
                  :guard (and (sm-wfp sm)
                              (< n (sm-get-range sm)))))
  (b* ((n (lnfix n))
       (idx (sm-inp n sm))
       ((unless idx) nil))
    (sm-get-aux (the (unsigned-byte 32) idx) sm)))

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

(defcong nat-equiv equal (sm-delete m sm) 1)


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

(defun sm-alist (sm)
  (declare (xargs :stobjs sm
                  :guard (sm-wfp sm)))
  (sm-alist-aux 0 sm))


;; Set range.

(defun sm-set-range (n sm)
  (declare (type (integer 0 *) n)
           (xargs :stobjs sm
                  :guard (sm-wfp sm)))
  (b* ((sm (lsm-fix sm)))
    (sm-set-range1 n sm)))



;; -------------   Top-level API -----------------

;; All updaters produce well-formed SMs.
(defthm sm-wfp-of-sm-create
  (sm-wfp '(nil nil nil 0 0)))

(defthm sm-wfp-of-sm-clear
  (sm-wfp (sm-clear sm)))

(defthm sm-wfp-of-sm-add
  (sm-wfp (sm-add n sm)))

(defthm sm-wfp-of-sm-put
  (sm-wfp (sm-put n val sm)))

(defthm sm-wfp-of-sm-delete
  (sm-wfp (sm-delete n sm)))

(defthm sm-wfp-of-sm-set-range
  (sm-wfp (sm-set-range n sm)))


;; Interaction of SM-INP with each of the updaters.
(defthm sm-inp-of-sm-create
  (not (sm-inp n '(nil nil nil 0 0))))

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

(defthm sm-inp-of-sm-set-range
  (equal (sm-inp n (sm-set-range m sm))
         (sm-inp n sm)))


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

(defthmd sm-get-of-sm-delete-casesplit
  (equal (sm-get n (sm-delete m sm))
         (and (not (equal (nfix n) (nfix m)))
              (sm-get n sm))))

(defthm sm-get-of-sm-set-range
  (equal (sm-get n (sm-set-range m sm))
         (sm-get n sm)))


(defthm sm-eltcount-of-sm-clear
  (equal (sm-eltcount (sm-clear sm))
         0))

(defthm sm-eltcount-of-sm-add
  (equal (sm-eltcount (sm-add n sm))
         (if (sm-inp n sm)
             (sm-eltcount sm)
           (+ 1 (sm-eltcount sm)))))

(defthm sm-eltcount-of-sm-put
  (equal (sm-eltcount (sm-put m v sm))
         (sm-eltcount (sm-add m sm))))

(defthm sm-eltcount-of-sm-delete
  (equal (sm-eltcount (sm-delete n sm))
         (if (sm-inp n sm)
             (1- (sm-eltcount sm))
           (sm-eltcount sm))))

(defthm sm-eltcount-of-sm-set-range
  (equal (sm-eltcount (sm-set-range n sm))
         (sm-eltcount sm)))


(defthm member-of-sm-list
  (iff (member n (sm-list sm))
       (and (natp n)
            (sm-inp n sm))))

(defthm no-duplicatesp-sm-list
  (no-duplicatesp (sm-list sm))
  :hints(("Goal" :in-theory (disable sm-compactp sm-inp
                                     sm-list-aux))))

(defthm len-sm-list
  (equal (len (sm-list sm))
         (sm-eltcount sm)))

(defthm assoc-in-sm-alist
  (equal (assoc n (sm-alist sm))
         (and (natp n)
              (sm-inp n sm)
              (cons n (sm-get n sm)))))


(defthm sm-get-range-of-sm-create
  (equal (sm-get-range '(nil nil nil 0 0)) 0))

(defthm sm-get-range-of-sm-clear
  (equal (sm-get-range (sm-clear sm))
         (sm-get-range sm))
  :hints(("Goal" :in-theory (enable sm-clear))))

(defthm sm-get-range-of-sm-add
  (equal (sm-get-range (sm-add n sm))
         (sm-get-range sm)))

(defthm sm-get-range-of-sm-put
  (equal (sm-get-range (sm-put n v sm))
         (sm-get-range sm))
  :hints(("Goal" :in-theory (enable sm-put sm-put-aux))))

(defthm sm-get-range-of-sm-delete
  (equal (sm-get-range (sm-delete n sm))
         (sm-get-range sm)))

(defthm sm-get-range-of-sm-set-range
  (equal (sm-get-range (sm-set-range n sm))
         (nfix n)))

(in-theory (disable smp sm-wfp sm-inp sm-get sm-eltcount sm-get-range sm-list sm-alist
                    sm-clear sm-add sm-put sm-delete sm-set-range))

(defthm type-of-sm-get-range
  (implies (smp sm)
           (natp (sm-get-range sm)))
  :rule-classes :type-prescription)

(defthm sm-list-of-sm-clear
  (equal (sm-list (sm-clear sm)) nil))

(defthm sm-list-of-sm-add
  (equal (sm-list (sm-add n sm))
         (if (sm-inp n sm)
             (sm-list sm)
           (append (sm-list sm) (list (nfix n))))))



;; Abstractions

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

(definline smset-inp$c (n sm)
  (declare (xargs :stobjs sm
                  :guard (and (natp n)
                              (sm-wfp sm)
                              (< n (sm-get-range sm)))))
  (and (sm-inp n sm) t))


;; This abstracts a set-only sparsemap (no sm-set/sm-get, only sm-add/sm-inp)
;; as a pair of a list and an upper bound (range)
(defabsstobj smset
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
                         :protect t)))

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

(definline smmap-inp$c (n sm)
  (declare (xargs :stobjs sm
                  :guard (and (natp n)
                              (sm-wfp sm)
                              (< n (sm-get-range sm)))))
  (and (sm-inp n sm) t))

(defun smmap-clear$a (smmap)
  (declare (xargs :guard (smmapp$a smmap)))
  (cons nil (cdr smmap)))

(defabsstobj smmap
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
                         :protect t)))


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
(defabsstobj sma
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

