; Centaur AIG Library
; Copyright (C) 2012 Centaur Technology
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
; AIG input variable collecting -- specialized/aux functions
; Original author: Sol Swords <sswords@centtech.com>

(in-package "ACL2")
;; (include-book "defsort/defsort" :dir :system)
(include-book "aig-base")
(include-book "std/util/bstar" :dir :system)
(include-book "std/bitsets/sbitsets" :dir :system)
(include-book "centaur/misc/hons-extra" :dir :system)
(include-book "centaur/misc/alist-defs" :dir :system)
(include-book "centaur/misc/numlist" :dir :system)

(local (include-book "centaur/bitops/ihsext-basics" :dir :system))
(local (include-book "ihs/quotient-remainder-lemmas" :dir :system)) ;; floor stuff
(local (include-book "arithmetic/top-with-meta" :dir :system))


(defun atom< (x y)
  (declare (xargs :guard (and (atom x) (atom y))))
  (mbe :logic (not (alphorder (and (atom y) y) (and (atom x) x)))
       :exec (not (fast-alphorder y x))))

(defsort alphorder-sort
  :prefix alphorder
  :comparablep (lambda (x) (not (consp x)))
  :compare< atom<
  :comparable-listp atom-listp
  :true-listp t
  :weak t)

;; Accumulates the AIG vars of X into acc, excluding those that are only found
;; within x inside subtrees that are bound in nodetable.  Accumulates into
;; nodetable all subtrees of x that it encounters while skipping those found in
;; nodetable.
(defun accumulate-aig-vars (x nodetable acc)
  (declare (xargs :guard t))
  (b* (((when (aig-atom-p x)) (if (or (booleanp x)
                                      (hons-get x nodetable))
                                  (mv nodetable acc)
                                (mv (hons-acons x t nodetable)
                                    (cons x acc))))
       ((when (eq (cdr x) nil))
        (accumulate-aig-vars (car x) nodetable acc))
       ((when (hons-get x nodetable))
        (mv nodetable acc))
       (nodetable (hons-acons x t nodetable))
       ((mv nodetable acc)
        (accumulate-aig-vars (car x) nodetable acc)))
    (accumulate-aig-vars (cdr x) nodetable acc)))

(defun accumulate-aig-vars-list (x nodetable acc)
  (declare (xargs :guard t))
  (b* (((when (atom x)) (mv nodetable acc))
       ((mv nodetable acc) (accumulate-aig-vars (car x) nodetable acc)))
    (accumulate-aig-vars-list (cdr x) nodetable acc)))

(defun aig-vars-unordered (x)
  (declare (xargs :guard t))
  (b* (((mv nodetable acc)
        (accumulate-aig-vars x nil nil)))
    (fast-alist-free nodetable)
    acc))

(defun aig-vars-unordered-list (x)
  (declare (xargs :guard t))
  (b* (((mv nodetable acc)
        (accumulate-aig-vars-list x nil nil)))
    (fast-alist-free nodetable)
    acc))


;; Does a search through the AIG table, accumulating seen variables.  Each
;; variable is only added to the queue when it is added to the nodetable, so
;; even though we don't check the seen list for duplicates we know that we
;; never visit a node more than once.  The queue and nodetable should be
;; initialized to contain the same variables (the queue a list, nodetable a
;; fast alist.)  Then the result (seen) contains all variables reachable from
;; the starting list.
(defun aigtab-collect-vars1 (queue aigtab nodetable seen)
  (declare (xargs :guard t :mode :program))
  (b* (((when (atom queue))
        (fast-alist-free nodetable)
        seen)
       (seen (cons (car queue) seen))
       (aig (cdr (hons-get (car queue) aigtab)))
       ((mv nodetable queue)
        (accumulate-aig-vars aig nodetable (cdr queue))))
    (aigtab-collect-vars1 queue aigtab nodetable seen)))


;; Given an initial set of names (queue), collects the set of names recursively
;; reachable through the AIGTAB.  That is, if a is in the queue and a is bound
;; in aigtab to an AIG containing variable b, then b goes into the queue, and
;; every variable that is thus reached is returned.
(defun aigtab-collect-vars (queue aigtab)
  (declare (xargs :guard t :mode :program))
  (aigtab-collect-vars1 queue aigtab
                        (make-fast-alist (pairlis$ queue nil))
                        nil))



(defsection aig-vars-1pass
  :parents (aig-vars)
  :short "Faster, raw Lisp implementation of @(see aig-vars)."
  :long "<p>Logically this is just @(see aig-vars).</p>"

  (defun aig-vars-1pass (x)
    (declare (xargs :guard t))
    (aig-vars x)))


(defsection aig-vars-fast
  :parents (aig-vars)
  :short "Faster, raw Lisp implementation of @(see aig-vars), with
under-the-hood memoization; kind of nasty."

  (defun aig-vars-fast (x)
    ;; under-the-hood memoization, kind of nasty
    (declare (xargs :guard t))
    (aig-vars x)))


;; New map-aig-vars-fast implementation:

;; (program)

(defun aig-vars-dfsorder-aux2 (x seen vars)
  (declare (Xargs :guard t))
  (b* (((when (atom x))
        (if (or (booleanp x)
                (hons-get x vars))
            (mv seen vars)
          (mv seen (hons-acons x nil vars))))
       ((when (hons-get x seen))
        (mv seen vars))
       (seen (hons-acons x nil seen))
       ((unless (cdr x))
        (aig-vars-dfsorder-aux2 (car x) seen vars))
       ((mv seen vars)
        (aig-vars-dfsorder-aux2 (car x) seen vars)))
    (aig-vars-dfsorder-aux2 (cdr x) seen vars)))

(defun aig-vars-dfsorder-aux2-list (x seen vars)
  (declare (Xargs :guard t))
  (b* (((when (atom x))
        (mv seen vars))
       ((mv seen vars)
        (aig-vars-dfsorder-aux2 (car x) seen vars)))
    (aig-vars-dfsorder-aux2-list (cdr x) seen vars)))

(defun sbitset-alistp (x)
  (declare (xargs :guard t))
  (if (atom x)
      t
    (and (consp (car x))
         (sbitsetp (cdar x))
         (sbitset-alistp (cdr x)))))

(defthm sbitsetp-of-lookup-in-sbitset-alistp
  (implies (and (sbitset-alistp x)
                (hons-assoc-equal k x))
           (sbitsetp (cdr (hons-assoc-equal k x)))))

;; Making this local mostly in case of name conflicts
(local
 (defun max-nat-list (x)
   (declare (xargs :guard (nat-listp x)))
   (if (atom x)
       0
     (max (lnfix (car x))
          (max-nat-list (cdr x))))))

(defun aig-vars-sparse/trans-aux (x memo-table nalist)
  (declare (xargs :guard (sbitset-alistp memo-table)
                  :verify-guards nil))
  ;; alternative that translates as it goes
  (b* (((when (atom x))
        (mv (if (booleanp x)
                nil
              (sbitset-singleton (nfix (cdr (hons-get x nalist)))))
            memo-table))
       ((unless (cdr x))
        (aig-vars-sparse/trans-aux (car x) memo-table nalist))
       (look (hons-get x memo-table))
       ((when look)
        (mv (cdr look) memo-table))
       ((mv car-vars memo-table)
        (aig-vars-sparse/trans-aux (car x) memo-table nalist))
       ((mv cdr-vars memo-table)
        (aig-vars-sparse/trans-aux (cdr x) memo-table nalist))
       (all-vars   (sbitset-union car-vars cdr-vars))
       (memo-table (hons-acons x all-vars memo-table)))
    (mv all-vars memo-table)))

(defthm sbitsetp-of-aig-vars-sparse-trans-aux
  (implies (sbitset-alistp memo-table)
           (and (sbitsetp (mv-nth 0 (aig-vars-sparse/trans-aux x memo-table nalist)))
                (sbitset-alistp (mv-nth 1 (aig-vars-sparse/trans-aux x memo-table nalist))))))

(verify-guards aig-vars-sparse/trans-aux)


(defun map-aig-vars-sparse/trans (x memo-table nalist)
  (declare (xargs :guard (sbitset-alistp memo-table)))
  (b* (((when (atom x))
        (fast-alist-free memo-table)
        nil)
       ((mv vars1 memo-table)
        (aig-vars-sparse/trans-aux (car x) memo-table nalist)))
    (cons vars1
          (map-aig-vars-sparse/trans (cdr x) memo-table nalist))))


(defun sbitset-listp (x)
  (declare (xargs :guard t))
  (if (atom x)
      (eq x nil)
    (and (sbitsetp (car x))
         (sbitset-listp (cdr x)))))

(defthm sbitset-listp-of-map-aig-vars-sparse-trans
  (implies (sbitset-alistp memo-table)
           (sbitset-listp (map-aig-vars-sparse/trans x memo-table nalist))))

(defmacro maybe-add-translated-sbit (bit x offset acc tbl)
  `(if (logbitp ,bit ,x)
       (cons (aref1 'map-aig-vars-fast-array ,tbl (+ ,bit ,offset))
             ,acc)
     ,acc))


(defund 60bits-0-7-trans (offset x acc tbl)
  ;; Identical to bits-0-7, but for 60-bit unsigned ints
  (declare (xargs :guard (and (natp offset)
                              (array1p 'map-aig-vars-fast-array tbl)
                              (<= (+ 8 offset)
                                  (car (dimensions 'map-aig-vars-fast-array tbl)))))
           (type (unsigned-byte 60) x))
  (b* ((acc (maybe-add-translated-sbit 7 x offset acc tbl))
       (acc (maybe-add-translated-sbit 6 x offset acc tbl))
       (acc (maybe-add-translated-sbit 5 x offset acc tbl))
       (acc (maybe-add-translated-sbit 4 x offset acc tbl))
       (acc (maybe-add-translated-sbit 3 x offset acc tbl))
       (acc (maybe-add-translated-sbit 2 x offset acc tbl))
       (acc (maybe-add-translated-sbit 1 x offset acc tbl))
       (acc (maybe-add-translated-sbit 0 x offset acc tbl)))
    acc))

(defund 60bits-0-3-trans (offset x acc tbl)
  ;; Since 8 doesn't divide 60, we have this goofy function for the final
  ;; bits.
  (declare (xargs :guard (and (natp offset)
                              (array1p 'map-aig-vars-fast-array tbl)
                              (<= (+ 4 offset)
                                  (car (dimensions 'map-aig-vars-fast-array tbl)))))
           (type (unsigned-byte 60) x))
  (b* ((acc (maybe-add-translated-sbit 3 x offset acc tbl))
       (acc (maybe-add-translated-sbit 2 x offset acc tbl))
       (acc (maybe-add-translated-sbit 1 x offset acc tbl))
       (acc (maybe-add-translated-sbit 0 x offset acc tbl)))
    acc))

(defund 60bits-0-59-trans (offset x acc tbl)
  (declare (xargs :guard (and (natp offset)
                              (array1p 'map-aig-vars-fast-array tbl)
                              (<= (+ 60 offset)
                                  (car (dimensions 'map-aig-vars-fast-array tbl)))))
           (type (unsigned-byte 60) x))
  ;; We could do a check against zero like in bits-0-31, but since this is
  ;; used in sparse bitsets where the data should never be zero, we think
  ;; that wouldn't be good.
  (b* ((acc (60bits-0-3-trans (+ offset 56) (the (unsigned-byte 60) (ash x -56)) acc tbl))
       (acc (60bits-0-7-trans (+ offset 48) (the (unsigned-byte 60) (ash x -48)) acc tbl))
       (acc (60bits-0-7-trans (+ offset 40) (the (unsigned-byte 60) (ash x -40)) acc tbl))
       (acc (60bits-0-7-trans (+ offset 32) (the (unsigned-byte 60) (ash x -32)) acc tbl))
       (acc (60bits-0-7-trans (+ offset 24) (the (unsigned-byte 60) (ash x -24)) acc tbl))
       (acc (60bits-0-7-trans (+ offset 16) (the (unsigned-byte 60) (ash x -16)) acc tbl))
       (acc (60bits-0-7-trans (+ offset 8)  (the (unsigned-byte 60) (ash x -8)) acc tbl)))
    (60bits-0-7-trans offset x acc tbl)))

(defun sbitset-max-offset (x)
  (declare (xargs :guard (sbitsetp x)))
  (if (atom x)
      0
    (max (lnfix (bitsets::sbitset-pair-offset (car x)))
         (sbitset-max-offset (cdr x)))))

;; (defthm sbitset-offset-<=-max
;;   (implies (and (sbitsetp x)
;;                 (consp x))
;;            (<= (sbitset-pair-offset (car x))
;;                (sbitset-max-offset x)))
;;   :rule-classes (:rewrite :linear))

(defun sbitset-members-exec-trans (x acc tbl)
  (declare (xargs :guard (and (sbitsetp x)
                              (array1p 'map-aig-vars-fast-array tbl)
                              (<= (+ 60 (* 60 (sbitset-max-offset x)))
                                  (car (dimensions 'map-aig-vars-fast-array tbl))))))
  (if (atom x)
      acc
    (let* ((pair1   (car x))
           (offset1 (bitsets::sbitset-pair-offset pair1))
           (block1  (bitsets::sbitset-pair-block pair1)))
      ;; BOZO should probably use ash 5 for 32-bit case
      (60bits-0-59-trans (* offset1 60)
                         block1
                         (sbitset-members-exec-trans (cdr x) acc tbl)
                         tbl))))

(defun sbitset-members-trans (x tbl)
  (declare (xargs :guard (and (sbitsetp x)
                              (array1p 'map-aig-vars-fast-array tbl)
                              (<= (+ 60 (* 60 (sbitset-max-offset x)))
                                  (car (dimensions 'map-aig-vars-fast-array tbl))))))
  (sbitset-members-exec-trans x nil tbl))

(memoize 'sbitset-members-trans)

(defun max-sbitset-max-offset (x)
  (declare (xargs :guard (sbitset-listp x)))
  (if (atom x)
      0
    (max (sbitset-max-offset (car x))
         (max-sbitset-max-offset (cdr x)))))


(defun map-sbitset-members-trans (x tbl)
  (declare (xargs :guard (and (sbitset-listp x)
                              (array1p 'map-aig-vars-fast-array tbl)
                              (<= (+ 60 (* 60 (max-sbitset-max-offset x)))
                                  (car (dimensions 'map-aig-vars-fast-array tbl))))))
  (if (atom x)
      nil
    (cons (sbitset-members-trans (car x) tbl)
          (map-sbitset-members-trans (cdr x) tbl))))

(local (defthm consp-assoc-equal-when-alistp
         (implies (alistp x)
                  (iff (consp (assoc k x))
                       (assoc k x)))))

(local (defthm consp-assoc-equal-when-key
         (implies k
                  (iff (consp (assoc k x))
                       (assoc k x)))))

(local
 (defthm car-of-assoc-equal-when-key
   (implies (and key
                 (assoc key x))
            (equal (car (assoc key x)) key))))

(local
 (defthm bounded-integer-alistp-of-compress11
   (implies (and (natp bound)
                 (natp i))
            (bounded-integer-alistp
             (compress11 name x i bound default)
             bound))))


(local
 (defthm alistp-of-compress11
   (implies i
            (alistp (compress11 name x i bound default)))))


(defun finish-map-aig-vars-fast (array-len valist ndeps)
  (declare (xargs :guard (and (posp array-len)
                              (< array-len *maximum-positive-32-bit-integer*)
                              (bounded-integer-alistp valist array-len)
                              (sbitset-listp ndeps)
                              (<= (+ 60 (* 60 (max-sbitset-max-offset ndeps)))
                                  array-len))
                  ;; :guard-hints ((and stable-under-simplificationp
                  ;;                    '(:use ((:instance max-sbitset-max-offset-bound
                  ;;                             (x ndeps)))
                  ;;                      :in-theory (disable max-sbitset-max-offset-bound))))
                  ))

  (b* ((varr     (compress1 'map-aig-vars-fast-array
                            (cons (list :HEADER
                                        :DIMENSIONS (list array-len)
                                        :MAXIMUM-LENGTH (+ array-len 1)
                                        :DEFAULT 0
                                        :NAME 'map-aig-vars-fast-array
                                        )
                                  valist)))
       (nlists   (map-sbitset-members-trans ndeps varr)))
    (flush-compress 'map-aig-vars-fast-array)
    nlists))

(defthm sbitset-max-offset-of-sbitset-union-exec
  (implies (and (sbitsetp x)
                (sbitsetp y))
           (equal (sbitset-max-offset (bitsets::sbitset-union-exec x y))
                  (max (sbitset-max-offset x)
                       (sbitset-max-offset y))))
  :hints(("Goal" :in-theory (enable bitsets::sbitset-union-exec))))

(defthm sbitset-max-offset-of-sbitset-union
  (implies (and (sbitsetp x) (sbitsetp y))
           (equal (sbitset-max-offset (sbitset-union x y))
                  (max (sbitset-max-offset x)
                       (sbitset-max-offset y))))
  :hints(("Goal" :in-theory (enable sbitset-union))))

(defthm sbitset-max-offset-of-sbitset-singleton
  (equal (sbitset-max-offset (sbitset-singleton n))
         (floor (nfix n) bitsets::*sbitset-block-size*))
  :hints(("Goal" :in-theory (enable sbitset-singleton
                                    bitsets::sbitset-singleton-pair))))

(defthm sbitset-max-offset-of-lookup
  (<= (sbitset-max-offset (cdr (hons-assoc-equal x memo-table)))
      (max-sbitset-max-offset (alist-vals memo-table)))
  :hints(("Goal" :in-theory (enable alist-vals)))
  :rule-classes :linear)

(local
 (progn
   (defthm floor-of-lookup-when-max-nat-list
     (<= (floor (nfix (cdr (hons-assoc-equal x nalist))) 60)
         (floor (max-nat-list (alist-vals nalist)) 60))
     :hints(("Goal" :in-theory (enable alist-vals))))

   (defthm sbitset-max-offset-of-aig-vars-sparse/trans-aux
     (implies (and (sbitset-alistp memo-table)
                   (<= (max-sbitset-max-offset (alist-vals memo-table))
                       (floor (max-nat-list (alist-vals nalist)) 60)))
              (mv-let (bitset memo-table)
                (aig-vars-sparse/trans-aux x memo-table nalist)
                (and (<= (max-sbitset-max-offset (alist-vals memo-table))
                         (floor (max-nat-list (alist-vals nalist)) 60))
                     (<= (sbitset-max-offset bitset)
                         (floor (max-nat-list (alist-vals nalist)) 60)))))
     :hints(("Goal" :in-theory (enable alist-vals)))
     :rule-classes (:rewrite :linear))

   (defthm max-sbitset-max-offset-of-map-aig-vars-sparse/trans
     (implies (and (sbitset-alistp memo-table)
                   (<= (max-sbitset-max-offset (alist-vals memo-table))
                       (floor (max-nat-list (alist-vals nalist)) 60)))
              (<= (max-sbitset-max-offset
                   (map-aig-vars-sparse/trans x memo-table nalist))
                  (floor (max-nat-list (alist-vals nalist)) 60)))
     :hints(("Goal" :in-theory (disable aig-vars-sparse/trans-aux)))
     :rule-classes (:rewrite :linear))

   (defthm alist-vals-of-pairlis
     (implies (equal (len X) (len y))
              (equal (alist-vals (pairlis$ x y))
                     (list-fix y)))
     :hints(("Goal" :in-theory (enable list-fix alist-vals))))

   (defthm max-nat-list-of-numlist
     (implies (and (natp start) (natp by))
              (equal (max-nat-list (numlist start by n))
                     (if (zp n)
                         0
                       (+ start (* (+ -1 n) by))))))

   (defthm max-sbitset-max-offset-of-map-aig-vars-sparse/trans-start
     (implies (atom memo-table)
              (<= (max-sbitset-max-offset
                   (map-aig-vars-sparse/trans x memo-table nalist))
                  (floor (max-nat-list (alist-vals nalist)) 60)))
     :hints (("goal" :use max-sbitset-max-offset-of-map-aig-vars-sparse/trans
              :in-theory (e/d (alist-vals)
                              (max-sbitset-max-offset-of-map-aig-vars-sparse/trans))))
     :rule-classes (:rewrite :linear))

   (defthm nat-listp-of-numlist
     (implies (and (natp start) (natp by))
              (nat-listp (numlist start by n))))

   (defthm bounded-integer-alistp-of-pairlis
     (implies (and (natp bound)
                   (nat-listp keys)
                   (force (< (max-nat-list keys) bound)))
              (bounded-integer-alistp (pairlis$ keys vals) bound)))))


(defun map-aig-vars-fast (aigs)
  ;; inline translation to numeric aigs + sparse algorithm + convert back
  (declare (xargs :guard t
                  :guard-hints ('(:cases ((< 0 (len (alist-keys
                                                     (mv-nth 1 (aig-vars-dfsorder-aux2-list
                                                                aigs nil nil))))))))))
  (b* (((mv seen vars) (aig-vars-dfsorder-aux2-list aigs nil nil))
       (nseen (fast-alist-len seen)) ;; bozo use length instead?
       (- (fast-alist-free seen))
       (- (fast-alist-free vars))
       (all-vars (alist-keys vars))
       (len      (len all-vars))
       (numlist  (numlist 0 1 len))
       (nalist   (pairlis$ all-vars numlist))
       (valist   (pairlis$ numlist all-vars))
       ((with-fast nalist))
       (ndeps    (map-aig-vars-sparse/trans aigs nseen nalist))
       (array-len (* 60 (+ 1 (floor len 60)))))
    (mbe :logic (finish-map-aig-vars-fast array-len valist ndeps)
         :exec (if (<= *maximum-positive-32-bit-integer* array-len)
                   (prog2$
                    (er hard? 'map-aig-vars-fast "Array length out of bounds: ~x0" array-len)
                    (non-exec (finish-map-aig-vars-fast array-len valist ndeps)))
                 (finish-map-aig-vars-fast array-len valist ndeps)))))



#||

bunch of messy stuff about all the different things we tried


(defun aig-vars-sparse (x)
  ;; core sbitsets version, requires numeric aigs
  (if (atom x)
      (if (booleanp x)
          nil
        (sbitset-singleton (nfix x)))
    (if (cdr x)
        (sbitset-union (aig-vars-sparse (car x))
                       (aig-vars-sparse (cdr x)))
      (aig-vars-sparse (car x)))))

(defttag asdf)
(progn!
 (set-raw-mode t)
 (memoize-fn 'aig-vars-sparse :condition '(and (consp x) (cdr x))))

(defun map-aig-vars-sparse (x)
  ;; core sbitsets version, requires numeric aigs
  (declare (xargs :guard t))
  (if (atom x)
      nil
    (cons (aig-vars-sparse (car x))
          (map-aig-vars-sparse (cdr x)))))

(defun map-sbitset-members (x)
  (if (atom x)
      nil
    (cons (sbitset-members (car x))
          (map-sbitset-members (cdr x)))))





(defun translate-back-to-vars (ndeps valist)
  (declare (Xargs :guard t))
  (if (atom ndeps)
      nil
    (cons (alist-vals (fal-extract (car ndeps) valist))
          (translate-back-to-vars (cdr ndeps) valist))))


(defstobj translate-back-stobj
  (translate-back-arr :type (array t (0))
                      :initially 0
                      :resizable t)
  :inline t)

(defun load-up-translate-back-stobj (nalist translate-back-stobj)
  (declare (xargs :stobjs translate-back-stobj))
  (if (atom nalist)
      translate-back-stobj
    (let ((translate-back-stobj
           (update-translate-back-arri (cdar nalist)
                                       (caar nalist)
                                       translate-back-stobj)))
      (load-up-translate-back-stobj (cdr nalist)
                                    translate-back-stobj))))

(defun translate-back-list (list translate-back-stobj)
  (declare (xargs :stobjs translate-back-stobj))
  (if (atom list)
      nil
    (cons (translate-back-arri (car list) translate-back-stobj)
          (translate-back-list (cdr list) translate-back-stobj))))

(defun translate-back-to-vars2 (ndeps translate-back-stobj)
  (declare (xargs :stobjs translate-back-stobj))
  (if (atom ndeps)
      nil
    (cons (translate-back-list (car ndeps) translate-back-stobj)
          (translate-back-to-vars2 (cdr ndeps) translate-back-stobj))))

(defun translate-back-top (ndeps nalist)
  (with-local-stobj translate-back-stobj
    (mv-let (result translate-back-stobj)
      (b* ((translate-back-stobj
            (cwtime (resize-translate-back-arr (fast-alist-len nalist)
                                               translate-back-stobj)))
           (translate-back-stobj
            (cwtime (load-up-translate-back-stobj nalist translate-back-stobj)))
           (ret
            (cwtime (translate-back-to-vars2 ndeps translate-back-stobj))))
        (mv ret translate-back-stobj))
      result)))

(top-level
 (let ((alist '((a . 1) (b . 2) (c . 3) (d . 4))))
   (with-fast-alist alist
     (translate-back-top '((1 2) (3 4)) alist))))




(defconst *tmp*
  ;; Array of pre-computed strings "[0]", "[1]", ..., "[255]"
  (compress1 'sally
             (cons (list :HEADER
                         :DIMENSIONS (list 256)
                         :MAXIMUM-LENGTH 257
                         :DEFAULT 0
                         :NAME 'sally)
                   (pairlis$ (numlist 0 1 256)
                             (repeat 'foo 256)))))

(resize-translate-back-arr 256 translate-back-stobj)

(defconst *ht*
  (let ((ht (make-hash-table :size 1000 :test 'eql)))
    (loop for i fixnum from 0 to 256 do
          (setf (gethash i ht) 'foo))
    ht))

(let ((tmp *tmp*)
      (ht *ht*)
      (translate-back-stobj *the-live-translate-back-stobj*)
      (times 100000000))
  (time (loop for i fixnum from 1 to times do
              (aref1 'sally tmp 35)))
  (time (loop for i fixnum from 1 to times do
              (gethash 35 ht)))
  (time (loop for i fixnum from 1 to times do
              (translate-back-arri 35 translate-back-stobj))))









(defun map-aig-vars-smart (aigs)
  ;; naive translation to numeric aigs + sparse algorithm + convert back
  (declare (xargs :guard t))
  (b* ((all-vars (cwtime (aig-vars-1pass aigs)))
       (numlist  (numlist 0 1 (len all-vars)))
       (nalist   (pairlis$ all-vars numlist))
       (valist   (pairlis$ numlist all-vars))
       (naigs    (cwtime (with-fast-alist nalist
                           (aig-restrict-list aigs nalist))))
       (ndeps    (cwtime (map-aig-vars-sparse naigs)))
       (nlists   (cwtime (map-sbitset-members ndeps)))
       ((with-fast valist)))
    (cwtime (translate-back-to-vars nlists valist))))



;; alternative to aig-vars-1pass, etc., to preserve variable ordering
;; better(?) and avoid sorting

(defun aig-vars-dfsorder-aux (x acc)
  (declare (Xargs :guard t))
  (b* (((when (or (booleanp x)
                  (hons-get x acc)))
        acc)
       (acc (hons-acons x nil acc))
       ((when (atom x)) acc)
       ((unless (cdr x))
        (aig-vars-dfsorder-aux (car x) acc)))
    (aig-vars-dfsorder-aux
     (cdr x)
     (aig-vars-dfsorder-aux
      (car x) acc))))

(defun remove-conses (x)
  (declare (Xargs :guard t))
  (if (Atom x)
      nil
    (if (atom (car x))
        (cons (car x) (remove-conses (cdr x)))
      (remove-conses (cdr x)))))

(defun aig-vars-dfsorder (x)
  (declare (xargs :guard t))
  (remove-conses (alist-keys (fast-alist-free (aig-vars-dfsorder-aux x nil)))))

(defun map-aig-vars-smarter1 (aigs)
  ;; naive translation to numeric aigs + sparse algorithm + convert back
  (declare (xargs :guard t))
  (b* ((all-vars (cwtime (aig-vars-dfsorder aigs)))
       (numlist  (numlist 0 1 (len all-vars)))
       (nalist   (pairlis$ all-vars numlist))
       (valist   (pairlis$ numlist all-vars))
       (naigs    (cwtime (with-fast-alist nalist
                           (aig-restrict-list aigs nalist))))
       (ndeps    (cwtime (map-aig-vars-sparse naigs)))
       (nlists   (cwtime (map-sbitset-members ndeps)))
       ((with-fast valist)))
    (cwtime (translate-back-to-vars nlists valist))))





;; same thing but possibly better/worse way to memoize

(defun aig-vars-dfsorder-aux2 (x seen vars)
  (declare (Xargs :guard t))
  (b* (((when (atom x))
        (if (or (booleanp x)
                (hons-get x vars))
            (mv seen vars)
          (mv seen (hons-acons x nil vars))))
       ((when (hons-get x seen))
        (mv seen vars))
       (seen (hons-acons x nil seen))
       ((unless (cdr x))
        (aig-vars-dfsorder-aux2 (car x) seen vars))
       ((mv seen vars)
        (aig-vars-dfsorder-aux2 (car x) seen vars)))
    (aig-vars-dfsorder-aux2 (cdr x) seen vars)))

(defun aig-vars-dfsorder2 (x)
  (declare (xargs :guard t))
  (b* (((mv seen vars) (aig-vars-dfsorder-aux2 x nil nil)))
    (fast-alist-free seen)
    (fast-alist-free vars)
    (alist-keys vars)))

(defun map-aig-vars-smarter2 (aigs)
  ;; naive translation to numeric aigs + sparse algorithm + convert back
  (declare (xargs :guard t))
  (b* ((all-vars (cwtime (aig-vars-dfsorder2 aigs)))
       (numlist  (numlist 0 1 (len all-vars)))
       (nalist   (pairlis$ all-vars numlist))
       (valist   (pairlis$ numlist all-vars))
       (naigs    (cwtime (with-fast-alist nalist
                           (aig-restrict-list aigs nalist))))
       (ndeps    (cwtime (map-aig-vars-sparse naigs)))
       (nlists   (cwtime (map-sbitset-members ndeps)))
       ((with-fast valist)))
    (cwtime (translate-back-to-vars nlists valist))))




(defun aig-vars-sparse/trans-aux (x memo-table nalist)
  ;; alternative that translates as it goes
  (b* (((when (atom x))
        (mv (if (booleanp x)
                nil
              (sbitset-singleton (cdr (hons-get x nalist))))
            memo-table))
       ((unless (cdr x))
        (aig-vars-sparse/trans-aux (car x) memo-table nalist))
       (look (hons-get x memo-table))
       ((when look)
        (mv (cdr look) memo-table))
       ((mv car-vars memo-table)
        (aig-vars-sparse/trans-aux (car x) memo-table nalist))
       ((mv cdr-vars memo-table)
        (aig-vars-sparse/trans-aux (cdr x) memo-table nalist))
       (all-vars   (sbitset-union car-vars cdr-vars))
       (memo-table (hons-acons x all-vars memo-table)))
    (mv all-vars memo-table)))

(defun map-aig-vars-sparse/trans (x memo-table nalist)
  (b* (((when (atom x))
        (fast-alist-free memo-table)
        nil)
       ((mv vars1 memo-table)
        (aig-vars-sparse/trans-aux (car x) memo-table nalist)))
    (cons vars1
          (map-aig-vars-sparse/trans (cdr x) memo-table nalist))))

(defun map-aig-vars-smarter3 (aigs)
  ;; naive translation to numeric aigs + sparse algorithm + convert back
  (declare (xargs :guard t))
  (b* ((all-vars (cwtime (aig-vars-dfsorder2 aigs)))
       (numlist  (numlist 0 1 (len all-vars)))
       (nalist   (pairlis$ all-vars numlist))
       (valist   (pairlis$ numlist all-vars))
       ;(naigs    (cwtime (with-fast-alist nalist
       ;                    (aig-restrict-list aigs nalist))))
       (ndeps    (cwtime (with-fast-alist nalist
                           (map-aig-vars-sparse/trans aigs nil nalist))))
       (nlists   (cwtime (map-sbitset-members ndeps)))
       ((with-fast valist)))
    (cwtime (translate-back-to-vars nlists valist))))




(time$ (map-aig-vars-smarter4 *foo*))
; AIG-VARS-DFSORDER-AUX2: 2.42 seconds, 169,202,048 bytes.
; WITH-FAST-ALIST: 0.51 seconds, 172,851,216 bytes.
; MAP-SBITSET-MEMBERS: 7.17 seconds, 8,093,634,080 bytes.


;;; Starting full GC,  19,977,601,024 bytes allocated.
;;; Finished full GC.   3,339,812,496 bytes freed in 31.171611 s

;;; 29038 soft faults, 0 faults, 0 pageins



;;; Starting full GC,  20,944,912,384 bytes allocated.
;;; Finished full GC.   2,153,665,280 bytes freed in 33.907863 s

;;; 3690 soft faults, 0 faults, 0 pageins



;;; Starting full GC,  23,148,756,992 bytes allocated.
;;; Finished full GC.   2,178,840,000 bytes freed in 33.982115 s

;;; 8406 soft faults, 0 faults, 0 pageins

; TRANSLATE-BACK-TO-VARS: 173.32 seconds, 16,177,948,112 bytes.
; (EV-REC *RETURN-LAST-ARG3* ...) took
; 183.44 seconds realtime, 183.40 seconds runtime
; (24,617,664,416 bytes allocated).


(defun map-aig-vars-smarter4 (aigs)
  ;; inline translation to numeric aigs + sparse algorithm + convert back
  (declare (xargs :guard t))
  (b* (((mv seen vars) (cwtime (aig-vars-dfsorder-aux2 aigs nil nil)))
       (nseen (fast-alist-len seen)) ;; bozo use length instead?
       (- (fast-alist-free seen))
       (- (fast-alist-free vars))
       (all-vars (alist-keys vars))
       (numlist  (numlist 0 1 (len all-vars)))
       (nalist   (pairlis$ all-vars numlist))
       (valist   (pairlis$ numlist all-vars))
       ;(naigs    (cwtime (with-fast-alist nalist
       ;                    (aig-restrict-list aigs nalist))))
       (ndeps    (cwtime (with-fast-alist nalist
                           (map-aig-vars-sparse/trans aigs nseen nalist))))
       (nlists   (cwtime (map-sbitset-members ndeps)))
       ((with-fast valist)))
    (cwtime (translate-back-to-vars nlists valist))))



(prog2$ (time$ (map-aig-vars-smarter5 *foo*))
        nil)
; AIG-VARS-DFSORDER-AUX2: 2.41 seconds, 169,171,280 bytes.
; MAP-AIG-VARS-SPARSE/TRANS: 0.50 seconds, 170,883,456 bytes.
; MAP-SBITSET-MEMBERS: 5.97 seconds, 8,093,634,080 bytes.
; RESIZE-TRANSLATE-BACK-ARR: 0.00 seconds, 172,064 bytes.
; LOAD-UP-TRANSLATE-BACK-STOBJ: 0.00 seconds, 944 bytes.
; TRANSLATE-BACK-TO-VARS2: 12.89 seconds, 8,093,634,080 bytes.
; TRANSLATE-BACK-TOP: 12.90 seconds, 8,093,812,624 bytes.
; (EV-REC *RETURN-LAST-ARG3* ...) took
; 21.80 seconds realtime, 21.80 seconds runtime
; (16,530,845,920 bytes allocated).
(defun map-aig-vars-smarter5 (aigs)
  ;; inline translation to numeric aigs + sparse algorithm + convert back
  (declare (xargs :guard t))
  (b* (((mv seen vars) (cwtime (aig-vars-dfsorder-aux2 aigs nil nil)))
       (nseen (fast-alist-len seen)) ;; bozo use length instead?
       (- (fast-alist-free seen))
       (- (fast-alist-free vars))
       (all-vars (alist-keys vars))
       (numlist  (numlist 0 1 (len all-vars)))
       (nalist   (pairlis$ all-vars numlist))
       ;; (valist   (pairlis$ numlist all-vars))
       ;(naigs    (cwtime (with-fast-alist nalist
       ;                    (aig-restrict-list aigs nalist))))
       ((with-fast nalist))
       (ndeps    (cwtime (map-aig-vars-sparse/trans aigs nseen nalist)))
       (nlists   (cwtime (map-sbitset-members ndeps))))
    (cwtime (translate-back-top nlists nalist))))



(prog2$ (time$ (map-aig-vars-smarter6 *foo*))
        nil)
; AIG-VARS-DFSORDER-AUX2: 2.21 seconds, 169,402,592 bytes.
; MAP-AIG-VARS-SPARSE/TRANS: 0.50 seconds, 170,983,248 bytes.
; MAP-SBITSET-MEMBERS-TRANS: 23.54 seconds, 2,946,840,192 bytes.
; (EV-REC *RETURN-LAST-ARG3* ...) took
; 26.28 seconds realtime, 26.28 seconds runtime
; (3,293,220,816 bytes allocated).

(defun map-aig-vars-smarter6 (aigs)
  ;; inline translation to numeric aigs + sparse algorithm + convert back
  (declare (xargs :guard t))
  (b* (((mv seen vars) (cwtime (aig-vars-dfsorder-aux2 aigs nil nil)))
       (nseen (fast-alist-len seen)) ;; bozo use length instead?
       (- (fast-alist-free seen))
       (- (fast-alist-free vars))
       (all-vars (alist-keys vars))
       (numlist  (numlist 0 1 (len all-vars)))
       (nalist   (pairlis$ all-vars numlist))
       (valist   (pairlis$ numlist all-vars))
       ;(naigs    (cwtime (with-fast-alist nalist
       ;                    (aig-restrict-list aigs nalist))))
       ((with-fast nalist))
       (ndeps    (cwtime (map-aig-vars-sparse/trans aigs nseen nalist)))
       ((with-fast valist))
       (nlists   (cwtime (map-sbitset-members-trans ndeps valist))))
    nlists))

ACL2 p!>(prog2$ (time$ (map-aig-vars-smarter7 *foo*))
        nil)
; AIG-VARS-DFSORDER-AUX2: 2.21 seconds, 169,403,072 bytes.
; MAP-AIG-VARS-SPARSE/TRANS: 0.57 seconds, 170,937,024 bytes.
; MAP-SBITSET-MEMBERS-TRANS: 6.46 seconds, 2,946,840,192 bytes.
; (EV-REC *RETURN-LAST-ARG3* ...) took
; 9.26 seconds realtime, 9.26 seconds runtime
; (3,291,378,848 bytes allocated).

(defun map-aig-vars-smarter7 (aigs)
  ;; inline translation to numeric aigs + sparse algorithm + convert back
  (declare (xargs :guard t))
  (b* (((mv seen vars) (cwtime (aig-vars-dfsorder-aux2 aigs nil nil)))
       (nseen (fast-alist-len seen)) ;; bozo use length instead?
       (- (fast-alist-free seen))
       (- (fast-alist-free vars))
       (all-vars (alist-keys vars))
       (len      (len all-vars))
       (numlist  (numlist 0 1 len))
       (nalist   (pairlis$ all-vars numlist))
       (valist   (pairlis$ numlist all-vars))
       ;(naigs    (cwtime (with-fast-alist nalist
       ;                    (aig-restrict-list aigs nalist))))
       ((with-fast nalist))
       (ndeps    (cwtime (map-aig-vars-sparse/trans aigs nseen nalist)))
       (varr     (compress1 'blarg
                            (cons (list :HEADER
                                        :DIMENSIONS (list len)
                                        :MAXIMUM-LENGTH (+ len 1)
                                        :DEFAULT 0
                                        :NAME 'blarg)
                                  valist)))
       (nlists   (cwtime (map-sbitset-members-trans ndeps varr))))
    (flush-compress 'blarg)
    nlists))

(prog2$ (time$ (map-aig-vars-smarter8 *foo*))
        nil)
; AIG-VARS-1PASS: 7.30 seconds, 66,538,832 bytes.
; MAP-AIG-VARS-SPARSE/TRANS: 0.86 seconds, 336,210,224 bytes.
; MAP-SBITSET-MEMBERS-TRANS: 7.55 seconds, 2,950,279,712 bytes.
; (EV-REC *RETURN-LAST-ARG3* ...) took
; 15.74 seconds realtime, 15.74 seconds runtime
; (3,356,884,976 bytes allocated).

(defun map-aig-vars-smarter8 (aigs)
  ;; inline translation to numeric aigs + sparse algorithm + convert back
  (declare (xargs :guard t))
  (b* ((all-vars (cwtime (aig-vars-1pass aigs)))
       ;;(nseen (fast-alist-len seen)) ;; bozo use length instead?
       ;;(- (fast-alist-free seen))
       ;; (- (fast-alist-free vars))
       ;; (all-vars (alist-keys vars))
       (len      (len all-vars))
       (numlist  (numlist 0 1 len))
       (nalist   (pairlis$ all-vars numlist))
       (valist   (pairlis$ numlist all-vars))
       ;(naigs    (cwtime (with-fast-alist nalist
       ;                    (aig-restrict-list aigs nalist))))
       ((with-fast nalist))
       (ndeps    (cwtime (map-aig-vars-sparse/trans
                          aigs nil nalist)))
       (varr     (compress1 'blarg
                            (cons (list :HEADER
                                        :DIMENSIONS (list len)
                                        :MAXIMUM-LENGTH (+ len 1)
                                        :DEFAULT 0
                                        :NAME 'blarg)
                                  valist)))
       (nlists   (cwtime (map-sbitset-members-trans ndeps varr))))
    (flush-compress 'blarg)
    nlists))

(prog2$ (time$ (map-aig-vars-smarter9 *foo*))
        nil)
; AIG-VARS-DFSORDER2: 2.22 seconds, 169,790,992 bytes.
; MAP-AIG-VARS-SPARSE/TRANS: 0.59 seconds, 163,065,568 bytes.
; MAP-SBITSET-MEMBERS-TRANS: 6.53 seconds, 2,948,558,224 bytes.
; (EV-REC *RETURN-LAST-ARG3* ...) took
; 9.36 seconds realtime, 9.36 seconds runtime
; (3,285,271,024 bytes allocated).
NIL

(defun map-aig-vars-smarter9 (aigs)
  ;; inline translation to numeric aigs + sparse algorithm + convert back
  (declare (xargs :guard t))
  (b* ((all-vars (cwtime (aig-vars-dfsorder2 aigs)))
       ;;(nseen (fast-alist-len seen)) ;; bozo use length instead?
       ;;(- (fast-alist-free seen))
       ;; (- (fast-alist-free vars))
       ;; (all-vars (alist-keys vars))
       (len      (len all-vars))
       (numlist  (numlist 0 1 len))
       (nalist   (pairlis$ all-vars numlist))
       (valist   (pairlis$ numlist all-vars))
       ;(naigs    (cwtime (with-fast-alist nalist
       ;                    (aig-restrict-list aigs nalist))))
       ((with-fast nalist))
       (ndeps    (cwtime (map-aig-vars-sparse/trans
                          aigs nil nalist)))
       (varr     (compress1 'blarg
                            (cons (list :HEADER
                                        :DIMENSIONS (list len)
                                        :MAXIMUM-LENGTH (+ len 1)
                                        :DEFAULT 0
                                        :NAME 'blarg)
                                  valist)))
       (nlists   (cwtime (map-sbitset-members-trans ndeps varr))))
    (flush-compress 'blarg)
    nlists))


        nil)


ACL2 p!>(prog2$ (time$ (map-aig-vars-smarter10 *foo*))
        nil)
; AIG-VARS-DFSORDER: 2.11 seconds, 183,191,360 bytes.
; MAP-AIG-VARS-SPARSE/TRANS: 0.59 seconds, 163,065,568 bytes.
; MAP-SBITSET-MEMBERS-TRANS: 6.57 seconds, 2,956,304,272 bytes.
; (EV-REC *RETURN-LAST-ARG3* ...) took
; 9.29 seconds realtime, 9.29 seconds runtime
; (3,306,417,440 bytes allocated).
NIL
(defun map-aig-vars-smarter10 (aigs)
  ;; inline translation to numeric aigs + sparse algorithm + convert back
  (declare (xargs :guard t))
  (b* ((all-vars (cwtime (aig-vars-dfsorder aigs)))
       ;;(nseen (fast-alist-len seen)) ;; bozo use length instead?
       ;;(- (fast-alist-free seen))
       ;; (- (fast-alist-free vars))
       ;; (all-vars (alist-keys vars))
       (len      (len all-vars))
       (numlist  (numlist 0 1 len))
       (nalist   (pairlis$ all-vars numlist))
       (valist   (pairlis$ numlist all-vars))
       ;(naigs    (cwtime (with-fast-alist nalist
       ;                    (aig-restrict-list aigs nalist))))
       ((with-fast nalist))
       (ndeps    (cwtime (map-aig-vars-sparse/trans
                          aigs nil nalist)))
       (varr     (compress1 'blarg
                            (cons (list :HEADER
                                        :DIMENSIONS (list len)
                                        :MAXIMUM-LENGTH (+ len 1)
                                        :DEFAULT 0
                                        :NAME 'blarg)
                                  valist)))
       (nlists   (cwtime (map-sbitset-members-trans ndeps varr))))
    (flush-compress 'blarg)
    nlists))


(i-am-here)

(defconsts (*foo* state)
  (serialize-read "/n/fv2/sswords/proofs/transistor/formality/prop-aigtab.sao"))

(defconst *bar* (alist-vals *foo*))

(defconsts (*foo*)
  (alist-vals (@m :prop-aigtab)))

(time$ (map-aig-vars-smart *foo*))
(time$ (map-aig-vars-smarter1 *foo*))
(time$ (map-aig-vars-smarter2 *foo*))
(time$ (map-aig-vars-smarter3 *foo*))
(prog2$ (time$ (map-aig-vars-smarter4 *foo*)) nil)

(prog2$ (time$ (map-aig-vars-smarter5 *foo*))
        nil)

(prog2$ (time$ (map-aig-vars-smarter6 *foo*))
        nil)

(prog2$ (time$ (map-aig-vars-smarter7 *bar*))
        nil)

(prog2$ (time$ (map-aig-vars-smarter8 *foo*))
        nil)


;; reduce by dependencies
(time$
 (b* ((aigtab (@m :prop-aigtab))
      (vars (append (aig-vars-1pass (alist-vals (@m :prop-aigtab)))
                    (map-varn (append (@m :ios)
                                      (alist-vals (@m :states))
                                      (@m :cut-outnames))
                              1)
                    (map-varn (append (@m :ios)
                                      (alist-vals (@m :states))
                                      (@m :cut-outnames))
                              0)))
      (new-aigtab (fal-extract vars aigtab)))
   (asm :reduced-prop-aigtab new-aigtab)))

(defun map-mergesort (x)
  (if (Atom x)
      nil
    (cons (set::mergesort (car x))
          (map-mergesort (cdr x)))))

(defun equal-mergesorts (x y)
  (if (atom x)
      (atom y)
    (and (equal (mergesort (car x))
                (mergesort (car y)))
         (equal-mergesorts (cdr x) (cdr y)))))

(equal-mergesorts
 (time$ (map-aig-vars (alist-vals (@m :reduced-prop-aigtab))))
 (time$ (map-aig-vars-smarter7 (alist-vals (@m :reduced-prop-aigtab)))))



(set::mergesort
 (n-counts (map-len (map-aig-vars-smarter7 (alist-vals (@m
                                                        :reduced-prop-aigtab))))
           nil))

(defconsts *var-sets*
  (map-aig-vars-smarter7 (alist-vals (@m :reduced-prop-aigtab))))

(len *var-sets*)

(defconst *sorted-var-set-set*
  (set::mergesort (map-mergesort *var-sets*)))

(set::mergesort (n-counts (map-len *sorted-var-set-set*) nil))




     ((with-fast aigtab))
     (aigtab (remove-on/off-self-deps (alist-keys (@m :nodetable)) aigtab))
     ((with-fast aigtab))
     ((mv reduced-aigtab
          reduced-nodes-to-deps
          reduced-deps-to-nodes)
      (time$ (find-relevant-update-fns aigtab
                                       (append (alist-keys (@m :states))
                                               (alist-keys (@m :nodes))
                                               (@m :ios)
                                               (@m :cut-outnames))
                                       (append (@m :ios)
                                               (alist-vals (@m :states))
                                               (@m :cut-outnames))
                                       t))))
  (pprogn
   (asm :prop-reduced-aigtab (make-fast-alist reduced-aigtab))
   (asm :prop-nodes-to-deps reduced-nodes-to-deps)
   (asm :prop-deps-to-nodes reduced-deps-to-nodes)))




||#
