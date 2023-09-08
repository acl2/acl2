; AIGNET - And-Inverter Graph Networks
; Copyright (C) 2013 Centaur Technology
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

(in-package "AIGNET")

(include-book "centaur/aignet/vecsim" :dir :system)
(include-book "centaur/bitops/part-select" :dir :system)
(include-book "centaur/misc/u32-listp" :dir :system)
(include-book "centaur/misc/s32-listp" :dir :system)
(include-book "std/alists/alist-keys" :dir :system)
(include-book "is-xor")
(local (include-book "centaur/bitops/ihsext-basics" :dir :system))
(local (include-book "arithmetic/top-with-meta" :dir :system))
(local (include-book "std/lists/resize-list" :dir :system))
(local (include-book "std/lists/sets" :dir :system))
(local (in-theory (disable nth update-nth acl2::resize-list-when-atom)))
(local (include-book "centaur/fty/fixequiv" :dir :system))
(local (std::add-default-post-define-hook :fix))
;; Each node has a next and a head.  The head is the lowest-numbered node in
;; the equiv class.  The next is the next-higher-numbered node in the equiv
;; class.  If next<=node, the node is the last in its class.
;; If head >= node, the node is first in its class and head is the last.
;; So head == node indicates a singleton class.
(defstobj classes
  (class-nexts :type (array (unsigned-byte 32) (0)) :initially 0 :resizable t)
  (class-heads :type (array (unsigned-byte 32) (0)) :initially 0 :resizable t)
  :inline t)

(define classes-size (classes)
  (min (class-nexts-length classes)
       (class-heads-length classes)))

;; (define classes-sized ((size natp) classes)
;;   (and (<= (lnfix size) (class-nexts-length classes))
;;        (<= (lnfix size) (class-heads-length classes)))
;;   ///
;;   (defthm classes-sized-when-greater
;;     (implies (and (classes-sized size2 classes)
;;                   (<= (nfix size1) (nfix size2)))
;;              (classes-sized size1 classes))))


(local (defthm class-nextsp-is-u32-listp
         (equal (class-nextsp x)
                (acl2::u32-listp x))))

(local (defthm class-headsp-is-u32-listp
         (equal (class-headsp x)
                (acl2::u32-listp x))))

(local (defthm natp-nth-in-u32-listp
         (implies (and (acl2::u32-listp x)
                       (< (nfix n) (len x)))
                  (and (natp (nth n x))
                       (integerp (nth n x))
                       (<= 0 (nth n x))))))

(local (in-theory (disable class-nextsp class-headsp acl2::u32-listp)))

(define node-next ((node natp) classes)
  :guard (< node (classes-size classes)) ;; (classes-sized (+ 1 node) classes)
  :guard-hints (("goal" :in-theory (enable classes-size)))
  :inline t
  (lnfix (class-nextsi node classes)))

(define node-head ((node natp) classes)
  :guard (< node (classes-size classes)) ;; (classes-sized (+ 1 node) classes)
  :guard-hints (("goal" :in-theory (enable classes-size)))
  :inline t
  (lnfix (class-headsi node classes)))

(define node-class-head ((node natp) classes)
  :guard (< node (classes-size classes)) ;; (classes-sized (+ 1 node) classes)
  :returns (class-head natp :rule-classes :type-prescription)
  (b* ((node (lnfix node))
       (head (node-head node classes)))
    (if (<= head node)
        head
      node))
  ///
  (defret node-class-head-bound
    (<= (node-class-head node classes) (nfix node))
    :rule-classes :linear))

(define classes-wellformed-aux ((n natp)
                                classes)
  :guard (<= n (classes-size classes))
  :measure (nfix n)
  (if (zp n)
      t
    (and (< (node-next (1- n) classes) (classes-size classes))
         (< (node-head (1- n) classes) (classes-size classes))
         (classes-wellformed-aux (1- n) classes)))
  ///
  (defthmd classes-wellformed-aux-implies
    (implies (and (classes-wellformed-aux n classes)
                  (< (nfix m) (nfix n)))
             (and (< (node-next m classes) (classes-size classes))
                  (< (node-head m classes) (classes-size classes))))
    :hints (("goal" :induct (classes-wellformed-aux n classes))
            (and stable-under-simplificationp
                 '(:expand ((classes-wellformed-aux (nfix m) classes)))))))

(define classes-wellformed (classes)
  (classes-wellformed-aux (classes-size classes) classes)
  ///
  (defthm classes-wellformed-implies
    (implies (and (classes-wellformed classes)
                  (< (nfix m) (classes-size classes)))
             (and (< (node-next m classes) (classes-size classes))
                  (< (node-head m classes) (classes-size classes))))
    :hints(("Goal" :in-theory (enable classes-wellformed-aux-implies)))
    :rule-classes (:rewrite :linear)))



(define node-set-next ((node natp) (next natp) classes)
  :guard (< node (classes-size classes)) ;; (classes-sized (+ 1 node) classes)
  :guard-hints (("goal" :in-theory (enable classes-size)))
  :returns (new-classes)
  (mbe :logic (update-class-nextsi node (nfix next) classes)
       :exec (if (< next (ash 1 32))
                 (update-class-nextsi node next classes)
               (non-exec (update-class-nextsi node next classes))))
  ///
  (std::defret classes-size-of-node-set-next
    (<= (classes-size classes)
        (classes-size new-classes))
    :hints(("Goal" :in-theory (enable classes-size)))
    :rule-classes :linear)

  (std::defret classes-size-of-node-set-next-equal
    (implies (< (nfix node) (classes-size classes))
             (equal (classes-size new-classes)
                    (classes-size classes)))
    :hints(("Goal" :in-theory (enable classes-size))))

  (std::defret node-set-next-preserves-wellformed-aux
    (implies (and (< (nfix next) (classes-size classes))
                  (< (nfix node) (classes-size classes))
                  (classes-wellformed-aux n classes))
             (classes-wellformed-aux n new-classes))
    :hints(("Goal" :in-theory (enable classes-wellformed-aux classes-size node-next node-head)
            :induct (classes-wellformed-aux n classes))))

  (std::defret node-set-next-preserves-wellformed
    (implies (and (< (nfix next) (classes-size classes))
                  (< (nfix node) (classes-size classes))
                  (classes-wellformed classes))
             (classes-wellformed new-classes))
    :hints(("Goal" :in-theory (e/d (classes-wellformed)
                                   (node-set-next)))))

  (std::defret node-head-of-node-set-next
    (equal (node-head n (node-set-next m v classes))
           (node-head n classes))
    :hints(("Goal" :in-theory (enable node-head))))

  (std::defret node-next-of-node-set-next
    (equal (node-next n (node-set-next m v classes))
           (if (equal (nfix n) (nfix m))
               (nfix v)
             (node-next n classes)))
    :hints(("Goal" :in-theory (enable node-next)))))

(define node-set-head ((node natp) (head natp) classes)
  :guard (< node (classes-size classes)) ;; (classes-sized (+ 1 node) classes)
  :guard-hints (("goal" :in-theory (enable classes-size)))
  :returns (new-classes)
  (mbe :logic (update-class-headsi node (nfix head) classes)
       :exec (if (< head (ash 1 32))
                 (update-class-headsi node head classes)
               (non-exec (update-class-headsi node head classes))))
  ///
  (std::defret classes-size-of-node-set-head
    (<= (classes-size classes)
        (classes-size new-classes))
    :hints(("Goal" :in-theory (enable classes-size)))
    :rule-classes :linear)

  (std::defret classes-size-of-node-set-head-equal
    (implies (< (nfix node) (classes-size classes))
             (equal (classes-size new-classes)
                    (classes-size classes)))
    :hints(("Goal" :in-theory (enable classes-size))))
  ;; (std::defret classes-sized-of-node-set-head
  ;;   (implies (classes-sized size classes)
  ;;            (classes-sized size new-classes))
  ;;   :hints(("Goal" :in-theory (enable classes-sized))))
  

  (std::defret node-set-head-preserves-wellformed-aux
    (implies (and (< (nfix head) (classes-size classes))
                  (< (nfix node) (classes-size classes))
                  (classes-wellformed-aux n classes))
             (classes-wellformed-aux n new-classes))
    :hints(("Goal" :in-theory (enable classes-wellformed-aux classes-size node-next node-head)
            :induct (classes-wellformed-aux n classes))))

  (std::defret node-set-head-preserves-wellformed
    (implies (and (< (nfix head) (classes-size classes))
                  (< (nfix node) (classes-size classes))
                  (classes-wellformed classes))
             (classes-wellformed new-classes))
    :hints(("Goal" :in-theory (e/d (classes-wellformed)
                                   (node-set-head)))))

  (std::defret node-next-of-node-set-head
    (equal (node-next n (node-set-head m v classes))
           (node-next n classes))
    :hints(("Goal" :in-theory (enable node-next))))

  (std::defret node-head-of-node-set-head
    (equal (node-head n (node-set-head m v classes))
           (if (equal (nfix n) (nfix m))
               (nfix v)
             (node-head n classes)))
    :hints(("Goal" :in-theory (enable node-head)))))


(define class-list ((n natp) classes)
  :guard (and (< n (classes-size classes))
              (classes-wellformed classes))
  :measure (nfix (- (classes-size classes) (nfix n)))
  (b* ((n (lnfix n))
       (next (node-next n classes))
       ((when (and (mbt (and (< n (classes-size classes))
                             (classes-wellformed classes)))
                   (< n next)))
        (cons n (class-list next classes))))
    (list n)))

(define class-size ((n natp) classes)
  :guard (and (< n (classes-size classes))
              (classes-wellformed classes))
  :measure (nfix (- (classes-size classes) (nfix n)))
  (b* ((n (lnfix n))
       (next (node-next n classes))
       ((when (and (mbt (and (< n (classes-size classes))
                             (classes-wellformed classes)))
                   (< n next)))
        (+ 1 (class-size next classes))))
    1))

(define classes-record-sizes ((n natp) acl2::natarr classes)
  :guard (and (<= n (classes-size classes))
              (classes-wellformed classes))
  :returns (new-natarr)
  (b* (((when (zp n)) acl2::natarr)
       (n (1- n))
       (head (node-head n classes))
       ((when (< head n))
        (classes-record-sizes n acl2::natarr classes))
       (size (class-size n classes))
       (acl2::natarr (if (>= size (acl2::nats-length acl2::natarr))
                         (acl2::resize-nats (+ 1 size (ash size -1)) acl2::natarr)
                       acl2::natarr))
       (acl2::natarr (acl2::set-nat size (+ 1 (acl2::get-nat size acl2::natarr)) acl2::natarr)))
    (classes-record-sizes n acl2::natarr classes)))

(define classes-report-sizes-aux ((n natp) acl2::natarr)
  :measure (nfix (- (acl2::nats-length acl2::natarr) (nfix n)))
  (if (mbe :logic (zp (- (acl2::nats-length acl2::natarr) (nfix n)))
           :exec (<= (acl2::nats-length acl2::natarr) n))
      nil
    (prog2$ (b* ((count (acl2::get-nat n acl2::natarr)))
              (and (< 0 count)
                   (cw "~x0 classes of size ~x1~%" count n)))
            (classes-report-sizes-aux (1+ (lnfix n)) acl2::natarr))))

(define classes-report-sizes (classes)
  :guard (classes-wellformed classes)
  (b* (((acl2::local-stobjs acl2::natarr)
        (mv acl2::natarr null))
       (acl2::natarr (classes-record-sizes (classes-size classes) acl2::natarr classes)))
    (classes-report-sizes-aux 2 acl2::natarr)
    (mv acl2::natarr nil)))
       
       


(define class-consistent ((n natp) (head natp) classes)
  :guard (and (< n (classes-size classes))
              (classes-wellformed classes))
  :measure (nfix (- (classes-size classes) (nfix n)))
  (and (or (eql (node-head n classes) (lnfix head))
           (cw "~x0 was expected to have head ~x1 but instead its head was ~x2~%"
               n head (node-head n classes)))
       (b* ((next (node-next n classes)))
         (if (and (mbt (and (< (nfix n) (classes-size classes))
                            (classes-wellformed classes)))
                  (< (lnfix n) next))
             (class-consistent next head classes)
           (and (or (eql (node-head head classes) (lnfix n))
                    (cw "head node ~x0 was expected to have head (tail) ~x1 but instead it was ~x2~%"
                        head n (node-head head classes)))
                ;; (or (eql next (lnfix n))
                ;;     (cw "next node of tail node ~x0 was expected to be itself but instead was ~x1~%"
                ;;         n next))
                )))))

(define class-check-consistency ((n natp) classes)
  :guard (and (< n (classes-size classes))
              (classes-wellformed classes))
  (b* ((n (lnfix n))
       (head (node-head n classes))
       ((when (<= head n))
        (or (<= n (node-head head classes))
            (cw "Node ~x0's head node ~x1 has head (tail) node ~x2, which is less than that node~%"
                n head (node-head head classes)))))
    (or (class-consistent (node-next n classes) n classes)
        (cw "inconsistent class: head ~x0 next ~x1 tail ~x2~%"
            n (node-next n classes) (node-head n classes)))))


(define classes-check-consistency ((n natp) classes)
  :guard (and (<= n (classes-size classes))
              (classes-wellformed classes))
  (b* (((when (zp n)) t)
       (n (1- n)))
    (and (class-check-consistency n classes)
         (classes-check-consistency n classes))))
       
    

(defsection classes-consistent
  (defun-sk classes-consistent (classes)
    (forall n
            (implies (and (natp n)
                          (< n (classes-size classes)))
                     (and (implies (<= (node-head n classes) n)
                                   ;; n is not a head or is a singleton head
                                   (and (member-equal n (class-list (node-head n classes) classes))
                                        (<= n (node-head (node-head n classes) classes))))
                          (implies (<= n (node-head n classes))
                                   (member-equal (node-head n classes)
                                                 (class-list n classes))))))
    :rewrite :direct)
  
  (in-theory (disable classes-consistent
                      classes-consistent-necc))

  (defthm classes-consistent-implies-member-class-list-of-head
    (implies (and (classes-consistent classes)
                  (equal n2 (nfix n))
                  (< n2 (classes-size classes))
                  (<= (node-head n classes) n2))
             (member-equal n2 (class-list (node-head n classes) classes)))
    :hints (("goal" :use ((:instance classes-consistent-necc
                           (n (nfix n))))
             :in-theory (disable classes-consistent-necc))))

  (defthm classes-consistent-implies-node-head-of-node-head-gte
    (implies (and (classes-consistent classes)
                  (< (nfix n) (classes-size classes))
                  (<= (node-head n classes) (nfix n)))
             (<= (nfix n) (node-head (node-head n classes) classes)))
    :hints (("goal" :use ((:instance classes-consistent-necc
                           (n (nfix n))))
             :in-theory (disable classes-consistent-necc)))
    :rule-classes :linear)

  (defthm classes-consistent-implies-head-node-head-in-class
    (implies (and (classes-consistent classes)
                  (< (nfix n) (classes-size classes))
                  (<= (nfix n) (node-head n classes)))
             (member-equal (node-head n classes) (class-list n classes)))
    :hints (("goal" :use ((:instance classes-consistent-necc
                           (n (nfix n))))
             :in-theory (disable classes-consistent-necc)))))




(define classes-init-aux ((n natp) classes)
  :guard (<= n (classes-size classes))
  :returns (new-classes)
  (if (zp n)
      classes
    (b* ((n-1 (1- n))
         (classes (node-set-head n-1 0 classes))
         (classes (node-set-next n-1 n classes)))
      (classes-init-aux n-1 classes)))
  ///
  ;; (std::defret classes-sized-of-classes-init-aux
  ;;   (implies (classes-sized size classes)
  ;;            (classes-sized size new-classes)))

  (defretd node-next-of-<fn>
    (equal (node-next m new-classes)
           (if (< (nfix m) (nfix n))
               (+ 1 (nfix m))
             (node-next m classes))))

  (defretd node-head-of-<fn>
    (equal (node-head m new-classes)
           (if (< (nfix m) (nfix n))
               0
             (node-head m classes))))

  
  
  (std::defret classes-size-of-classes-init-aux
    (<= (classes-size classes)
        (classes-size new-classes))
    :rule-classes :linear)

  (std::defret classes-size-of-classes-init-aux-equal
    (implies (<= (nfix n) (classes-size classes))
             (equal (classes-size new-classes)
                    (classes-size classes))))

  ;; (local (std::defret len-of-arrays-prserved-of-classes-init-aux-equal
  ;;          (implies (<= (nfix n) (classes-size classes))
  ;;                   (and (equal (len (nth *class-nextsi* new-classes))
  ;;                               (len (nth *class-nextsi* classes)))
  ;;                        (equal (len (nth *class-headsi* new-classes))
  ;;                               (len (nth *class-headsi* classes)))))
  ;;          :hints(("Goal" :in-theory (enable classes-size node-set-next node-set-head)))))

  (std::defret classes-init-aux-preserves-upper
    (implies (<= (nfix n) (nfix m))
             (and (equal (node-head m new-classes)
                         (node-head m classes))
                  (equal (node-next m new-classes)
                         (node-next m classes)))))

  (std::defret classes-wellformed-aux-of-classes-init-aux
    (implies (< n (classes-size classes))
             (classes-wellformed-aux n new-classes))
    :hints(("Goal" :in-theory (enable classes-wellformed-aux
                                      ;; node-set-head node-head
                                      ;; node-set-next node-next
                                      ;; classes-size
                                      )
            :induct t))))


(define classes-init ((size natp) classes)
  ;; Puts everything in one big equiv class.
  :returns (new-classes)
  :prepwork ((local (defthm classes-size-of-resize
                      (implies (equal (len a) (len b))
                               (equal (classes-size (update-nth *class-headsi*
                                                                a
                                                                (update-nth *class-nextsi* b classes)))
                                      (len a)))
                      :hints(("Goal" :in-theory (enable classes-size))))))
  ;; :guard-hints ((and stable-under-simplificationp
  ;;                    '(:in-theory (enable classes-sized))))
  (b* ((classes (resize-class-nexts size classes))
       (classes (resize-class-heads size classes))
       ((when (zp size)) classes)
       ;; Set the last node separately because its next will be itself instead
       ;; of itself+1.
       (last (1- size))
       (classes (node-set-head last 0 classes))
       (classes (node-set-next last last classes))
       (classes (classes-init-aux last classes)))
    (node-set-head 0 last classes))
  ///

  (std::defret classes-size-of-classes-init
    (equal (classes-size new-classes) (nfix size)))

  (std::defret classes-wellformed-of-classes-init
    (classes-wellformed new-classes)
    :hints((and stable-under-simplificationp
                '(:in-theory (enable classes-wellformed)
                  :expand ((:free (foo) (classes-wellformed-aux size foo))
                           (:free (foo) (classes-wellformed-aux 0 foo)))))))

  (defretd node-next-of-<fn>
    (implies (< (nfix n) (nfix size))
             (equal (node-next n new-classes)
                    (if (eql (nfix n) (1- (nfix size)))
                        (nfix n)
                      (+ 1 (nfix n)))))
    :hints(("Goal" :in-theory (enable node-next-of-classes-init-aux))))

  (defretd node-head-of-<fn>
    (implies (< (nfix n) (nfix size))
             (equal (node-head n new-classes)
                    (if (zp n)
                        (1- (nfix size))
                      0)))
    :hints(("Goal" :in-theory (enable node-head-of-classes-init-aux))))

  
  (local (defun count-down (n)
           (if (zp n)
               n
             (count-down (1- n)))))

  (local (defun count-up (n k)
           (declare (xargs :measure (nfix (- (nfix k) (nfix n)))))
           (if (>= (nfix n) (nfix k))
               (list n k)
             (count-up (1+ (nfix n)) k))))

  (defretd class-list-of-classes-init
    (implies (and (integerp k)
                  (<= (nfix m) k)
                  (< k (nfix size)))
             (member-equal k (class-list m new-classes)))
    :hints (("goal" :induct (count-up m k)
             :in-theory (e/d (node-head-of-<fn>
                              node-next-of-<fn>)
                             (<fn>))
             :expand ((:free (classes) (class-list m classes))))))

  (defretd classes-consistent-of-<fn>
    (classes-consistent new-classes)
    :hints (("goal" :in-theory (e/d (classes-consistent
                                     class-list-of-classes-init
                                     node-head-of-<fn>)
                                    (<fn>))))))




(define classes-init-filtered-aux ((n natp) (next acl2::maybe-natp) bitarr classes)
  :guard (and (<= n (classes-size classes))
              (or (not next)
                  (and (<= n next)
                       (< next (classes-size classes))))
              (<= (classes-size classes) (bits-length bitarr)))
  :guard-hints (("goal" :in-theory (enable acl2::maybe-natp)))
  :guard-debug t
  :returns (new-classes)
  (b* (((when (zp n)) classes)
       (n-1 (1- n))
       ((when (eql 0 (get-bit n-1 bitarr)))
        (b* ((classes (node-set-head n-1 n-1 classes))
             (classes (node-set-next n-1 n-1 classes)))
          (classes-init-filtered-aux (1- n) next bitarr classes)))
       (classes (node-set-head n-1 0 classes))
       (classes (node-set-next n-1 (if next (lnfix next) n-1) classes)))
    (classes-init-filtered-aux n-1 n-1 bitarr classes))
  ///
  (std::defret classes-size-of-classes-init-filtered-aux
    (<= (classes-size classes)
        (classes-size new-classes))
    :rule-classes :linear)

  (std::defret classes-size-of-classes-init-filtered-aux-equal
    (implies (<= (nfix n) (classes-size classes))
             (equal (classes-size new-classes)
                    (classes-size classes))))

  ;; (local (std::defret len-of-arrays-prserved-of-classes-init-filtered-aux-equal
  ;;          (implies (<= (nfix n) (classes-size classes))
  ;;                   (and (equal (len (nth *class-nextsi* new-classes))
  ;;                               (len (nth *class-nextsi* classes)))
  ;;                        (equal (len (nth *class-headsi* new-classes))
  ;;                               (len (nth *class-headsi* classes)))))
  ;;          :hints(("Goal" :in-theory (enable classes-size node-set-next node-set-head)))))

  (std::defret classes-init-filtered-aux-preserves-upper
    (implies (<= (nfix n) (nfix m))
             (and (equal (node-head m new-classes)
                         (node-head m classes))
                  (equal (node-next m new-classes)
                         (node-next m classes)))))

  (std::defret classes-wellformed-aux-of-classes-init-filtered-aux
    (implies (and (<= (nfix n) (classes-size classes))
                  (implies next
                           (and (<= (nfix n) (nfix next))
                                (< (nfix next) (classes-size classes)))))
             (classes-wellformed-aux n new-classes))
    :hints(("Goal" :in-theory (enable classes-wellformed-aux
                                      ;; node-set-head node-head
                                      ;; node-set-next node-next
                                      ;; classes-size
                                      )
            :induct t))))



(define classes-init-empty-aux ((n natp) classes)
  :guard (<= n (classes-size classes))
  :guard-hints (("goal" :in-theory (enable acl2::maybe-natp)))
  :guard-debug t
  :returns (new-classes)
  (b* (((when (zp n)) classes)
       (n-1 (1- n))
       (classes (node-set-head n-1 n-1 classes))
       (classes (node-set-next n-1 n-1 classes)))
    (classes-init-empty-aux (1- n) classes))
  ///
  (std::defret classes-size-of-classes-init-empty-aux
    (<= (classes-size classes)
        (classes-size new-classes))
    :rule-classes :linear)

  (std::defret classes-size-of-classes-init-empty-aux-equal
    (implies (<= (nfix n) (classes-size classes))
             (equal (classes-size new-classes)
                    (classes-size classes))))

  ;; (local (std::defret len-of-arrays-prserved-of-classes-init-empty-aux-equal
  ;;          (implies (<= (nfix n) (classes-size classes))
  ;;                   (and (equal (len (nth *class-nextsi* new-classes))
  ;;                               (len (nth *class-nextsi* classes)))
  ;;                        (equal (len (nth *class-headsi* new-classes))
  ;;                               (len (nth *class-headsi* classes)))))
  ;;          :hints(("Goal" :in-theory (enable classes-size node-set-next node-set-head)))))

  (std::defret classes-init-empty-aux-preserves-upper
    (implies (<= (nfix n) (nfix m))
             (and (equal (node-head m new-classes)
                         (node-head m classes))
                  (equal (node-next m new-classes)
                         (node-next m classes)))))

  (std::defret classes-wellformed-aux-of-classes-init-empty-aux
    (implies (<= (nfix n) (classes-size classes))
             (classes-wellformed-aux n new-classes))
    :hints(("Goal" :in-theory (enable classes-wellformed-aux
                                      ;; node-set-head node-head
                                      ;; node-set-next node-next
                                      ;; classes-size
                                      )
            :induct t)))

  (std::defret classes-wellformed-of-classes-init-empty-aux
    (implies (equal (nfix n) (classes-size classes))
             (classes-wellformed new-classes))
    :hints(("Goal" :in-theory (e/d (classes-wellformed) (<fn>)
                                      ;; node-set-head node-head
                                      ;; node-set-next node-next
                                      ;; classes-size
                                      )))))


(define add-equiv-class-to-other ((head natp) (class natp) classes)
  :guard (and (< class (classes-size classes))
              (< head class)
              (classes-wellformed classes))
  ;; Class is a node which may be in an equiv class.  Set the heads of all
  ;; nodes in its equiv class to head, and set the head of head (tail) of the
  ;; class to the last node.  This is appropriate when class is greater than
  ;; the greatest node currently in the equivalence class of head.  Otherwise,
  ;; need to use join-equiv-classes-aux. Note that we don't update the nexts
  ;; here, because class is already assumed to be fully linked. So before
  ;; calling, the last node of head's current class should have been set to
  ;; class.
  :measure (nfix (- (classes-size classes) (nfix class)))
  :returns (new-classes)
  (b* ((ok (mbt (and (< (lnfix class) (classes-size classes))
                     (classes-wellformed classes))))
       (classes (node-set-head class head classes))
       (next (node-next class classes))
       ((when (and (mbt ok)
                   (> next (lnfix class))))
        (add-equiv-class-to-other head next classes)))
    ;; class is the last node in the new class; set the head of head to it
    (b* ((classes (node-set-head head class classes)))
      (or (class-check-consistency head classes)
          (cw "add-equiv-class-to-other: inconsistent class: head ~x0 next ~x1 tail ~x2~%"
              head (node-next head classes) (node-head head classes))
          (break$))
      classes))
  ///
  (defret classes-size-of-<fn>
    (implies (and (< (nfix class) (classes-size classes))
                  (< (nfix head) (nfix class))
                  (classes-wellformed classes))
             (equal (classes-size new-classes)
                    (classes-size classes))))

  (defret classes-wellformed-of-<fn>
    (implies (and (< (nfix class) (classes-size classes))
                  (< (nfix head) (nfix class))
                  (classes-wellformed classes))
             (classes-wellformed new-classes))))
       

(define join-equiv-classes-aux ((head natp)
                                (prev natp)
                                (class1 natp)
                                (class2 natp)
                                classes)
  :guard (and (<= head prev)
              (< prev class1)
              (< prev class2)
              (< class1 (classes-size classes))
              (< class2 (classes-size classes))
              (classes-wellformed classes))
  :measure (+ (nfix (- (classes-size classes) (nfix class1)))
              (nfix (- (classes-size classes) (nfix class2))))
  :returns (new-classes)
  (b* ((class1 (lnfix class1))
       (class2 (lnfix class2))
       (prev   (lnfix prev))
       (ok (mbt (and (< prev (classes-size classes))
                     (< class1 (classes-size classes))
                     (< class2 (classes-size classes))
                     (classes-wellformed classes))))
       ((when (eql class1 class2))
        ;; same class already -- shouldn't happen
        classes)
       ((mv class1 class2)
        (if (< class1 class2)
            (mv class1 class2)
          (mv class2 class1)))
       (classes (node-set-next prev class1 classes))
       (classes (node-set-head class1 (lnfix head) classes))
       (next (node-next class1 classes))
       
       ((when (and (mbt ok)
                   (> next class1)))
        (join-equiv-classes-aux head class1 next class2 classes))

       ;; class1 is the last node in its class.  Set its next to class2 and use
       ;; add-equiv-class-to-other to finish.
       (classes (node-set-next class1 class2 classes)))
    (add-equiv-class-to-other head class2 classes))
  ///
  (fty::deffixequiv join-equiv-classes-aux
    :hints (("goal" :induct (join-equiv-classes-aux head prev class1 class2 classes)
             :expand ((:free (head) (join-equiv-classes-aux head prev class1 class2 classes))
                      (:free (prev) (join-equiv-classes-aux head prev class1 class2 classes))
                      (:free (class1) (join-equiv-classes-aux head prev class1 class2 classes))
                      (:free (class2) (join-equiv-classes-aux head prev class1 class2 classes))))))

  (defret classes-size-of-<fn>
    (implies (and (<= (nfix head) (nfix prev))
                  (< (nfix prev) (nfix class1))
                  (< (nfix prev) (nfix class2))
                  (< (nfix class1) (classes-size classes))
                  (< (nfix class2) (classes-size classes))
                  (classes-wellformed classes))
             (equal (classes-size new-classes)
                    (classes-size classes))))

  (defret classes-wellformed-of-<fn>
    (implies (and (<= (nfix head) (nfix prev))
                  (< (nfix prev) (nfix class1))
                  (< (nfix prev) (nfix class2))
                  (< (nfix class1) (classes-size classes))
                  (< (nfix class2) (classes-size classes))
                  (classes-wellformed classes))
             (classes-wellformed new-classes))))

  
(define join-equiv-classes ((head1 natp)
                            (head2 natp)
                            classes)
  :guard (and (< head1 (classes-size classes))
              (< head2 (classes-size classes))
              (classes-wellformed classes))
  :returns (new-classes)
  (b* ((head1 (lnfix head1))
       (head2 (lnfix head2)))
    (if (< head1 head2)
        (b* ((next (node-next head1 classes))
             ((when (< head1 next))
              (join-equiv-classes-aux head1 head1 next head2 classes))
             ;; head1 is a singleton class
             (classes (node-set-next head1 head2 classes)))
          (add-equiv-class-to-other head1 head2 classes))
      (if (< head2 head1)
          (b* ((next (node-next head2 classes))
               ((when (< head2 next))
                (join-equiv-classes-aux head2 head2 next head1 classes))
               ;; head2 is a singleton class
               (classes (node-set-next head2 head1 classes)))
            (add-equiv-class-to-other head2 head1 classes))
        ;; already the same class
        classes)))
  ///
  (defret classes-size-of-<fn>
    (implies (and (< (nfix head1) (classes-size classes))
                  (< (nfix head2) (classes-size classes))
                  (classes-wellformed classes))
             (equal (classes-size new-classes)
                    (classes-size classes))))

  (defret classes-wellformed-of-<fn>
    (implies (and (< (nfix head1) (classes-size classes))
                  (< (nfix head2) (classes-size classes))
                  (classes-wellformed classes))
             (classes-wellformed new-classes))))

(define classes-join-miters-rec ((lit litp) mark aignet classes)
  ;; If lit is a non-negated AND gate recur into its children.
  ;; If it is an XOR/IFF, join the equivalence classes of the two.
  :guard (and (fanin-litp lit aignet)
              (<= (num-fanins aignet) (classes-size classes))
              (classes-wellformed classes)
              (<= (num-fanins aignet) (bits-length mark)))
  :returns (mv new-mark new-classes)
  :measure (lit->var lit)
  :verify-guards nil
  (b* ((id (lit->var lit))
       ((when (eql 1 (get-bit id mark)))
        (mv mark classes))
       (mark (set-bit id 1 mark))
       ((unless (int= (id->type id aignet) (gate-type)))
        (mv mark classes))
       ((mv is-xor child1 child2) (id-is-xor id aignet))
       ((when is-xor)
        (b* ((classes (join-equiv-classes (node-class-head (lit->var child1) classes)
                                          (node-class-head (lit->var child2) classes)
                                          classes)))
          (mv mark classes)))
       ;; AND gate
       ((when (eql (lit->neg lit) 1))
        (mv mark classes))
       ;; non-negated AND -- recur on branches
       ((mv mark classes)
        (classes-join-miters-rec (gate-id->fanin0 id aignet) mark aignet classes)))
    (classes-join-miters-rec (gate-id->fanin1 id aignet) mark aignet classes))
  ///
  
  (defret mark-len-of-<fn>
    (implies (and (equal len (len mark))
                  (< (lit->var lit) len))
             (equal (len new-mark) len)))

  (defret mark-len-incr-of-<fn>
    (<= (len mark) (len new-mark))
    :rule-classes :linear)
  
  (defret classes-size/wellformed-of-<fn>
    (implies (and (<= (num-fanins aignet) (classes-size classes))
                  (classes-wellformed classes))
             (and (equal (classes-size new-classes)
                         (classes-size classes))
                  (classes-wellformed new-classes))))

  (verify-guards classes-join-miters-rec
    :hints(("Goal" :in-theory (enable aignet-idp)))))



(define classes-join-po-miters ((n natp) mark aignet classes)
  :guard (and (<= n (num-outs aignet))
              (<= (num-fanins aignet) (classes-size classes))
              (classes-wellformed classes)
              (<= (num-fanins aignet) (bits-length mark)))
  :returns (mv new-mark new-classes)
  (b* (((when (zp n)) (mv mark classes))
       (n-1 (1- n))
       (fanin-id (lit->var (outnum->fanin n-1 aignet)))
       ((mv mark classes) (classes-join-miters-rec (make-lit fanin-id 0) mark aignet classes)))
    (classes-join-po-miters n-1 mark aignet classes))
  ///
  
  (defret classes-size/wellformed-of-<fn>
    (implies (and (<= (num-fanins aignet) (classes-size classes))
                  (classes-wellformed classes))
             (and (equal (classes-size new-classes)
                         (classes-size classes))
                  (classes-wellformed new-classes))))
  
  (defret mark-len-of-<fn>
    (implies (and (equal len (len mark))
                  (< (fanin-count aignet) len)
                  (<= (nfix n) (num-outs aignet)))
             (equal (len new-mark) len)))

  (defret mark-len-incr-of-<fn>
    (<= (len mark) (len new-mark))
    :rule-classes :linear))


(define classes-join-nxst-miters ((n natp) mark aignet classes)
  :guard (and (<= n (num-regs aignet))
              (<= (num-fanins aignet) (classes-size classes))
              (classes-wellformed classes)
              (<= (num-fanins aignet) (bits-length mark)))
  :returns (mv new-mark new-classes)
  (b* (((when (zp n)) (mv mark classes))
       (n-1 (1- n))
       (fanin-id (lit->var (regnum->nxst n-1 aignet)))
       ((mv mark classes) (classes-join-miters-rec (make-lit fanin-id 0) mark aignet classes)))
    (classes-join-nxst-miters n-1 mark aignet classes))
  ///
  
  (defret classes-size/wellformed-of-<fn>
    (implies (and (<= (num-fanins aignet) (classes-size classes))
                  (classes-wellformed classes))
             (and (equal (classes-size new-classes)
                         (classes-size classes))
                  (classes-wellformed new-classes))))
  
  (defret mark-len-of-<fn>
    (implies (and (equal len (len mark))
                  (< (fanin-count aignet) len)
                  (<= (nfix n) (num-regs aignet)))
             (equal (len new-mark) len)))

  (defret mark-len-incr-of-<fn>
    (<= (len mark) (len new-mark))
    :rule-classes :linear))



(define classes-init-out-miters (classes aignet)
  ;; Puts everything in one big equiv class.
  :returns (new-classes)
  :prepwork ((local (defthm classes-size-of-resize
                      (implies (equal (len a) (len b))
                               (equal (classes-size (update-nth *class-headsi*
                                                                a
                                                                (update-nth *class-nextsi* b classes)))
                                      (len a)))
                      :hints(("Goal" :in-theory (enable classes-size)))))
             (local (in-theory (disable acl2::lower-bound-of-len-when-sublistp
                                        acl2::resize-list-when-atom))))
  :guard-hints (("goal" :do-not-induct t))
  ;; :guard-hints ((and stable-under-simplificationp
  ;;                    '(:in-theory (enable classes-sized))))
  (b* ((size (num-fanins aignet))
       (classes (resize-class-nexts size classes))
       (classes (resize-class-heads size classes))
       ((when (zp size)) classes)
       ((acl2::local-stobjs  mark)
        (mv mark classes))
       (mark (resize-bits size mark))
       (classes (classes-init-empty-aux (num-fanins aignet) classes))
       ((mv mark classes) (classes-join-po-miters (num-outs aignet) mark aignet classes))
       ((mv mark classes)
        (classes-join-nxst-miters (num-regs aignet) mark aignet classes)))
    (classes-report-sizes classes)
    (classes-check-consistency (num-fanins aignet) classes)
    (mv mark classes))
       
  ///

  (std::defret classes-size-of-<fn>
    (equal (classes-size new-classes) (+ 1 (fanin-count aignet))))

  (std::defret classes-wellformed-of-<fn>
    (classes-wellformed new-classes)
    :hints((and stable-under-simplificationp
                '(:in-theory (enable classes-wellformed)
                  :expand ((:free (foo) (classes-wellformed-aux 0 foo))))))))















(define classes-init-miters-rec ((lit litp) bitarr mark aignet)
  ;; If lit is a non-negated AND gate recur into its children.
  ;; If it is a negated AND gate or variable, mark it in bitarr
  ;; If it is an XOR/IFF, mark its children in bitarr.
  :guard (and (fanin-litp lit aignet)
              (<= (num-fanins aignet) (bits-length bitarr))
              (<= (num-fanins aignet) (bits-length mark)))
  :returns (mv new-bitarr new-mark)
  :measure (lit->var lit)
  :verify-guards nil
  (b* ((id (lit->var lit))
       ((when (eql 1 (get-bit id mark)))
        (mv bitarr mark))
       (mark (set-bit id 1 mark))
       ((unless (int= (id->type id aignet) (gate-type)))
        (b* ((bitarr (set-bit id 1 bitarr)))
          (mv bitarr mark)))
       ((mv is-xor child1 child2) (id-is-xor id aignet))
       ((when is-xor)
        (b* ((bitarr (set-bit (lit->var child1) 1 bitarr))
             (bitarr (set-bit (lit->var child2) 1 bitarr)))
          (mv bitarr mark)))
       ;; AND gate
       ((when (eql (lit->neg lit) 1))
        (b* ((bitarr (set-bit id 1 bitarr)))
          (mv bitarr mark)))
       ;; non-negated AND -- recur on branches
       ((mv bitarr mark)
        (classes-init-miters-rec (gate-id->fanin0 id aignet) bitarr mark aignet)))
    (classes-init-miters-rec (gate-id->fanin1 id aignet) bitarr mark aignet))
  ///
  (defret bitarr-len-of-<fn>
    (implies (and (equal len (len bitarr))
                  (< (lit->var lit) len))
             (equal (len new-bitarr) len)))

  (defret bitarr-len-incr-of-<fn>
    (<= (len bitarr) (len new-bitarr))
    :rule-classes :linear)
  
  (defret mark-len-of-<fn>
    (implies (and (equal len (len mark))
                  (< (lit->var lit) len))
             (equal (len new-mark) len)))

  (defret mark-len-incr-of-<fn>
    (<= (len mark) (len new-mark))
    :rule-classes :linear)
  
  (verify-guards classes-init-miters-rec
    :hints(("Goal" :in-theory (enable aignet-idp)))))


(define classes-init-po-miters-bitarr ((n natp) bitarr mark aignet)
  :guard (and (<= n (num-outs aignet))
              (<= (num-fanins aignet) (bits-length bitarr))
              (<= (num-fanins aignet) (bits-length mark)))
  :returns (mv new-bitarr new-mark)
  (b* (((when (zp n)) (mv bitarr mark))
       (n-1 (1- n))
       (fanin-id (lit->var (outnum->fanin n-1 aignet)))
       ((mv bitarr mark) (classes-init-miters-rec (make-lit fanin-id 0) bitarr mark aignet)))
    (classes-init-po-miters-bitarr n-1 bitarr mark aignet))
  ///
  (defret bitarr-len-of-<fn>
    (implies (and (equal len (len bitarr))
                  (< (fanin-count aignet) len)
                  (<= (nfix n) (num-outs aignet)))
             (equal (len new-bitarr) len)))

  (defret bitarr-len-incr-of-<fn>
    (<= (len bitarr) (len new-bitarr))
    :rule-classes :linear)
  
  (defret mark-len-of-<fn>
    (implies (and (equal len (len mark))
                  (< (fanin-count aignet) len)
                  (<= (nfix n) (num-outs aignet)))
             (equal (len new-mark) len)))

  (defret mark-len-incr-of-<fn>
    (<= (len mark) (len new-mark))
    :rule-classes :linear))

(define classes-init-nxst-miters-bitarr ((n natp) bitarr mark aignet)
  :guard (and (<= n (num-regs aignet))
              (<= (num-fanins aignet) (bits-length bitarr))
              (<= (num-fanins aignet) (bits-length mark)))
  :returns (mv new-bitarr new-mark)
  (b* (((when (zp n)) (mv bitarr mark))
       (n-1 (1- n))
       (fanin-id (lit->var (regnum->nxst n-1 aignet)))
       ((mv bitarr mark) (classes-init-miters-rec (make-lit fanin-id 0) bitarr mark aignet)))
    (classes-init-nxst-miters-bitarr n-1 bitarr mark aignet))
  ///
  (defret bitarr-len-of-<fn>
    (implies (and (equal len (len bitarr))
                  (< (fanin-count aignet) len)
                  (<= (nfix n) (num-regs aignet)))
             (equal (len new-bitarr) len)))

  (defret bitarr-len-incr-of-<fn>
    (<= (len bitarr) (len new-bitarr))
    :rule-classes :linear)
  
  (defret mark-len-of-<fn>
    (implies (and (equal len (len mark))
                  (< (fanin-count aignet) len)
                  (<= (nfix n) (num-regs aignet)))
             (equal (len new-mark) len)))

  (defret mark-len-incr-of-<fn>
    (<= (len mark) (len new-mark))
    :rule-classes :linear))

(define classes-init-out-miters-old (classes aignet)
  ;; Calculates equiv classes filtered on only nodes that are part of the output miter.
  :returns (new-classes)
  :prepwork ((local (defthm classes-size-of-resize
                      (implies (equal (len a) (len b))
                               (equal (classes-size (update-nth *class-headsi*
                                                                a
                                                                (update-nth *class-nextsi* b classes)))
                                      (len a)))
                      :hints(("Goal" :in-theory (enable classes-size)))))
             (local (in-theory (disable acl2::lower-bound-of-len-when-sublistp
                                        acl2::resize-list-when-atom))))
  :guard-hints (("goal" :do-not-induct t))
  ;; :guard-hints ((and stable-under-simplificationp
  ;;                    '(:in-theory (enable classes-sized))))
  (b* ((size (num-fanins aignet))
       (classes (resize-class-nexts size classes))
       (classes (resize-class-heads size classes))
       ((when (zp size)) classes)
       ((acl2::local-stobjs bitarr mark)
        (mv bitarr mark classes))
       (bitarr (resize-bits size bitarr))
       (mark (resize-bits size mark))
       ((mv bitarr mark) (classes-init-po-miters-bitarr (num-outs aignet) bitarr mark aignet))
       ((mv bitarr mark) (classes-init-nxst-miters-bitarr (num-regs aignet) bitarr mark aignet))
       ;; Always flag the constant node so that it will be in the class.
       (bitarr (set-bit 0 1 bitarr))
       (classes (classes-init-filtered-aux size nil bitarr classes)))
    (mv bitarr mark classes))
  ///

  (std::defret classes-size-of-<fn>
    (equal (classes-size new-classes) (+ 1 (fanin-count aignet))))

  (std::defret classes-wellformed-of-<fn>
    (classes-wellformed new-classes)
    :hints((and stable-under-simplificationp
                '(:in-theory (enable classes-wellformed)
                  :expand ((:free (foo) (classes-wellformed-aux 0 foo))))))))


(define classes-init-pos-bitarr ((n natp) bitarr aignet)
  :guard (and (<= n (num-outs aignet))
              (<= (num-fanins aignet) (bits-length bitarr)))
  :returns (new-bitarr)
  (b* (((when (zp n)) bitarr)
       (n-1 (1- n))
       (fanin-id (lit->var (outnum->fanin n-1 aignet)))
       (bitarr (set-bit fanin-id 1 bitarr)))
    (classes-init-pos-bitarr n-1 bitarr aignet))
  ///
  (defret bitarr-size-of-classes-init-pos-bitarr
    (<= (len bitarr) (len new-bitarr))
    :rule-classes :linear)
  (defret bitarr-size-of-classes-init-pos-bitarr-equal
    (implies (and (< (fanin-count aignet) (len bitarr))
                  (<= (nfix n) (num-outs aignet)))
             (equal (len new-bitarr) (len bitarr)))))

(define classes-init-nxsts-bitarr ((n natp) bitarr aignet)
  :guard (and (<= n (num-regs aignet))
              (<= (num-fanins aignet) (bits-length bitarr)))
  :returns (new-bitarr)
  (b* (((when (zp n)) bitarr)
       (n-1 (1- n))
       (fanin-id (lit->var (regnum->nxst n-1 aignet)))
       (bitarr (set-bit fanin-id 1 bitarr)))
    (classes-init-nxsts-bitarr n-1 bitarr aignet))
  ///
  (defret bitarr-size-of-classes-init-nxsts-bitarr
    (<= (len bitarr) (len new-bitarr))
    :rule-classes :linear)
  (defret bitarr-size-of-classes-init-nxsts-bitarr-equal
    (implies (and (< (fanin-count aignet) (len bitarr))
                  (<= (nfix n) (num-regs aignet)))
             (equal (len new-bitarr) (len bitarr)))))

(define classes-init-outs (classes aignet)
  ;; Puts everything in one big equiv class.
  :returns (new-classes)
  :prepwork ((local (defthm classes-size-of-resize
                      (implies (equal (len a) (len b))
                               (equal (classes-size (update-nth *class-headsi*
                                                                a
                                                                (update-nth *class-nextsi* b classes)))
                                      (len a)))
                      :hints(("Goal" :in-theory (enable classes-size)))))
             (local (in-theory (disable acl2::lower-bound-of-len-when-sublistp
                                        acl2::resize-list-when-atom))))
  :guard-hints (("goal" :do-not-induct t))
  ;; :guard-hints ((and stable-under-simplificationp
  ;;                    '(:in-theory (enable classes-sized))))
  (b* ((size (num-fanins aignet))
       (classes (resize-class-nexts size classes))
       (classes (resize-class-heads size classes))
       ((when (zp size)) classes)
       ((acl2::local-stobjs bitarr)
        (mv bitarr classes))
       (bitarr (resize-bits size bitarr))
       (bitarr (classes-init-pos-bitarr (num-outs aignet) bitarr aignet))
       (bitarr (classes-init-nxsts-bitarr (num-regs aignet) bitarr aignet))
       ;; Always flag the constant node so that it will be in the class.
       (bitarr (set-bit 0 1 bitarr))
       (classes (classes-init-filtered-aux size nil bitarr classes)))
    (mv bitarr classes))
  ///

  (std::defret classes-size-of-classes-init-outs
    (equal (classes-size new-classes) (+ 1 (fanin-count aignet))))

  (std::defret classes-wellformed-of-classes-init-outs
    (classes-wellformed new-classes)
    :hints((and stable-under-simplificationp
                '(:in-theory (enable classes-wellformed)
                  :expand ((:free (foo) (classes-wellformed-aux 0 foo))))))))



(local (in-theory (disable unsigned-byte-p)))

(defmacro u32trunc (x)
  `(mbe :logic (acl2::loghead 32 ,x)
        :exec (the (unsigned-byte 32)
                   (logand #xffffffff ,x))))

(defmacro u32fix (x)
  `(mbe :logic (acl2::loghead 32 ,x)
        :exec (the (unsigned-byte 32) ,x)))

;; Bob Jenkins one-at-a-time hash
(define oathash1 ((byte :type (unsigned-byte 8))
                  (h :type (unsigned-byte 32)))
  :returns (new-h natp :rule-classes :type-prescription)
  (b* ((h (u32trunc (+ (u32fix h)
                       (mbe :logic (acl2::loghead 8 byte) :exec byte))))
       (h (u32trunc (+ h (ash h 10)))))
    (u32trunc (logxor h (ash h -6))))
  ///
  (std::defret unsigned-32-of-oathash1
    (unsigned-byte-p 32 new-h)))

(define oathash-u32 ((word :type (unsigned-byte 32))
                     (h :type (unsigned-byte 32)))
  :returns (new-h natp :rule-classes :type-prescription)
  (oathash1 (acl2::part-select word :low 24 :width 8)
            (oathash1 (acl2::part-select word :low 16 :width 8)
                      (oathash1 (acl2::part-select word :low 8 :width 8)
                                (oathash1 (acl2::part-select word :low 0 :width 8)
                                          h))))
  ///
  (std::defret unsigned-32-of-oathash-u32
    (unsigned-byte-p 32 new-h)))

(define oathash-s32 ((word :type (signed-byte 32))
                     (h :type (unsigned-byte 32)))
  :returns (new-h natp :rule-classes :type-prescription)
  (oathash1 (acl2::part-select word :low 24 :width 8)
            (oathash1 (acl2::part-select word :low 16 :width 8)
                      (oathash1 (acl2::part-select word :low 8 :width 8)
                                (oathash1 (acl2::part-select word :low 0 :width 8)
                                          h))))
  ///
  (std::defret unsigned-32-of-oathash-s32
    (unsigned-byte-p 32 new-h)))


(defthm s32ve-datap-is-s32-listp
  (equal (s32ve-datap x)
         (acl2::s32-listp x))
  :hints(("Goal" :in-theory (enable acl2::s32-listp))))

(defthm s32-listp-nth-of-s32vl-data
  (implies (s32vl-arr2-data-wfp x width)
           (acl2::s32-listp (nth n x)))
  :hints(("Goal" :in-theory (enable nth))))

(local (in-theory (enable ACL2::NTH-IN-S32-LISTP-S32P)))
(local (in-theory (disable signed-byte-p)))

(local (fty::deffixcong bit-equiv equal (bit-extend bit) bit
         :hints(("Goal" :in-theory (enable bit-extend)))))

(define s32-apply-parity ((x (signed-byte-p 32 x):type (signed-byte 32))
                          (parity bitp :type bit))
  :split-types t
  :returns (new-x integerp :rule-classes :type-prescription)
  (logxor (mbe :logic (acl2::logext 32 x) :exec x)
          (bit-extend parity))
  ///
  (defret signed-32-of-u32-apply-parity
    (signed-byte-p 32 new-x)))

(define oathash-s32v-aux ((row natp :type (integer 0 *))
                          (col natp :type (integer 0 *))
                          (h (unsigned-byte-p 32 h) :type (unsigned-byte 32))
                          (parity bitp :type bit)
                          s32v)
  :split-types t
  :guard (and (< row (s32v-nrows s32v))
              (<= col (s32v-ncols s32v)))
  :measure (nfix (- (s32v-ncols s32v) (nfix col)))
  :returns (new-h)
  (if (mbe :logic (zp (- (s32v-ncols s32v) (nfix col)))
           :exec (eql col (s32v-ncols s32v)))
      (u32fix h)
    (oathash-s32v-aux row (+ 1 (lnfix col))
                      (oathash-s32 (s32-apply-parity (s32v-get2 row col s32v) parity)
                                   h)
                      parity
                      s32v))
  ///
  (std::defret unsigned-32-of-oathash-s32v-aux
    (unsigned-byte-p 32 new-h)))

(define oathash-s32v ((row natp) (parity bitp) s32v)
  :guard (< row (s32v-nrows s32v))
  :returns (h)
  (b* ((h (oathash-s32v-aux row 0 0 parity s32v))
       (h (u32trunc (+ h (ash h 3))))
       (h (u32trunc (logxor h (ash h -11))))
       (h (u32trunc (+ h (ash h 15)))))
    h)
  ///
  (std::defret unsigned-32-of-oathash-s32v
    (unsigned-byte-p 32 h)))
       
  
(defstobj classhash      
  ;; Maps hashes of s32v values to a list* of nodes.
  (classhash-table :type (hash-table eql))
  :inline t)

(define s32v-compare-aux ((row1 natp)
                          (row2 natp)
                          (parity1 bitp)
                          (parity2 bitp)
                          (col natp)
                          s32v)
  :guard (and (< row1 (s32v-nrows s32v))
              (< row2 (s32v-nrows s32v))
              (<= col (s32v-ncols s32v)))
  :measure (nfix (- (s32v-ncols s32v) (nfix col)))
  :returns (equalp)
  :prepwork ((local (defthm eqlablep-when-natp
                      (implies (natp x)
                               (eqlablep x)))))
  (if (mbe :logic (zp (- (s32v-ncols s32v) (nfix col)))
           :exec (eql col (s32v-ncols s32v)))
      t
    (and (eql (s32-apply-parity (s32v-get2 row1 col s32v) parity1)
              (s32-apply-parity (s32v-get2 row2 col s32v) parity2))
         (s32v-compare-aux row1 row2 parity1 parity2 (1+ (lnfix col)) s32v))))

(define s32v-compare ((row1 natp)
                      (row2 natp)
                      (parity1 bitp)
                      (parity2 bitp)
                      s32v)
  :guard (and (< row1 (s32v-nrows s32v))
              (< row2 (s32v-nrows s32v)))
  (s32v-compare-aux row1 row2 parity1 parity2 0 s32v))

(define classes-hash-find-aux ((node natp)
                               (lookup)
                               (s32v)
                               aignet)
  :guard (and (< node (s32v-nrows s32v))
              (< node (num-fanins aignet)))
  :guard-hints (("goal" :in-theory (enable aignet-idp)))
  :returns (match (or (not match) (natp match)) :rule-classes :type-prescription)
  (b* (((unless lookup) nil)
       ((mv try end) (if (consp lookup)
                         (mv (car lookup) nil)
                       (mv lookup t)))
       ((when (and (natp try)
                   (< try (lnfix node))
                   (s32v-compare node try (id->phase node aignet) (id->phase try aignet) s32v)))
        try)
       ((when end) nil))
    (classes-hash-find-aux node (cdr lookup) s32v aignet))
  ///
  (std::defret classes-hash-find-aux-bound
    (implies match
             (< match (nfix node)))))
            
                               
  
(define classes-hash-find ((node natp)
                           (hash :type (unsigned-byte 32))
                           (s32v)
                           (classhash)
                           (aignet))
  :guard (and (< node (s32v-nrows s32v))
              (< node (num-fanins aignet)))
  :returns (match (or (not match) (natp match)) :rule-classes :type-prescription)
  (b* ((lookup (classhash-table-get hash classhash)))
    (classes-hash-find-aux node lookup s32v aignet))
  ///
  (std::defret classes-hash-find-bound
    (implies match
             (< match (nfix node)))
    :rule-classes :linear))

(define classes-hash-add ((node natp)
                          (hash :type (unsigned-byte 32))
                          (classhash))
  (b* ((lookup (classhash-table-get hash classhash)))
    (classhash-table-put hash (if lookup (cons (lnfix node) lookup) (lnfix node)) classhash)))
       

(define u32-list-p (x)
  :enabled t
  (or (null x) (and (consp x) (unsigned-byte-p 32 (first x)) (u32-list-p (rest x)))))

(define classes-hash-rem-lst ((rem-hash-lst u32-list-p)
                              (classhash))
  :returns (new-classhash)
  (if (endp rem-hash-lst) classhash
    (b* ((classhash (classhash-table-rem (first rem-hash-lst) classhash)))
      (classes-hash-rem-lst (rest rem-hash-lst) classhash)))
  ///

  (local (defthm subsetp-remove-equal
           (implies (subsetp x y)
                    (subsetp (remove-equal (car y) x) (cdr y)))))
  
  (local (defthm alist-keys-of-hons-remove-assoc
           (equal (alist-keys (acl2::hons-remove-assoc key al))
                  (remove-equal key (alist-keys al)))
           :hints(("Goal" :in-theory (enable alist-keys acl2::hons-remove-assoc remove-equal)))))

  (std::defret classhash-keys-subset-of-remhash-implies-empty-of-<fn>
    (implies (subsetp-equal (alist-keys (nth *classhash-table-get* classhash))
                            rem-hash-lst)
             (equal (alist-keys (nth *classhash-table-get* new-classhash)) nil))))

(define classes-refine-class-aux ((prev natp)
                                  (node natp)
                                  (nrefines natp)
                                  (rem-hash-lst u32-list-p)
                                  (s32v)
                                  (classhash)
                                  (classes)
                                  (aignet))
  ;; Node is always in the class of prev.  When we start prev is the head node and node is its next.
  ;; When its next turns out to be part of the same class, we then iterate on next with node as prev.  The
  ;; first node not in the same class as the head becomes head of its own class.
  ;; Its head is updated to the tail of the class as more nodes get added.
  ;;
  ;; Added rem-hash-lst parameter to avoid non-tail call which removed
  ;; hashtable entries after recursive call..
  :guard (and (<= prev node)
              (< node (classes-size classes))
              (equal (classes-size classes) (s32v-nrows s32v))
              (<= (classes-size classes) (num-fanins aignet))
              (classes-wellformed classes))
  :Guard-hints (("goal" :in-theory (enable aignet-idp)))
  :measure (nfix (- (classes-size classes) (nfix node)))
  :returns (mv new-classhash
               new-classes
               (nrefines-out natp :rule-classes :type-prescription))
  (b* ((node (lnfix node)) (prev (lnfix prev)) (nrefines (lnfix nrefines))
       ((unless (mbt (and (< node (classes-size classes))
                          (< prev (classes-size classes))
                          (classes-wellformed classes))))
        (b* ((classhash (classes-hash-rem-lst rem-hash-lst classhash)))
          (mv classhash classes nrefines)))
       (head (node-head node classes))
       (same (s32v-compare head node
                           (id->phase head aignet)
                           (id->phase node aignet)
                           s32v))
       (next (node-next node classes))
       ((when same)
        ;; (cw "same~%")
        ;; stays in this class; ensure next of prev points to this node
        (b* ((classes (node-set-next prev node classes)))
          (if (<= next node)
              ;; was the last node in the class, so set head of head to this
              (b* ((classes (node-set-head head node classes))
                   (classhash (classes-hash-rem-lst rem-hash-lst classhash)))
                (mv classhash classes nrefines))
            (classes-refine-class-aux node next nrefines rem-hash-lst s32v classhash classes aignet))))
       (nrefines  (+ 1 nrefines))
       (hash (oathash-s32v node (id->phase node aignet) s32v))
       (match (classes-hash-find node hash s32v classhash aignet))
       ((unless match)
        ;; (cw "head~%")
        ;; node breaks off into its own class, iterate on prev/next
        (b* ((classes (node-set-head node node classes))
             (classes (node-set-next node node classes))
             ((when (<= next node))
              (b* ((classes (node-set-head head prev classes))
                   (classes (node-set-next prev head classes))
                   (classhash (classes-hash-rem-lst rem-hash-lst classhash)))
                (mv classhash classes nrefines)))
             (classhash (classes-hash-add node hash classhash))
             (rem-hash-lst (cons hash rem-hash-lst)))
          (classes-refine-class-aux prev next nrefines rem-hash-lst s32v classhash classes aignet)))
       ;; (- (cw "match ~x0~%" match))
       ;; match is a head node, so its head is the last in its class -- set it to point to node
       (classes (node-set-next (node-head match classes) node classes))
       (classes (node-set-head match node classes))
       (classes (node-set-head node match classes))
       (classes (node-set-next node match classes))
       ((when (<= next node))
        (b* ((classes (node-set-head head prev classes))
             (classes (node-set-next prev head classes))
             (classhash (classes-hash-rem-lst rem-hash-lst classhash)))
          (mv classhash classes nrefines))))
    (classes-refine-class-aux prev next nrefines rem-hash-lst s32v classhash classes aignet))
  ///
  (std::defret classes-size-of-classes-refine-class-aux
    (equal (classes-size new-classes) (classes-size classes)))

  (std::defret classes-wellformed-of-classes-refine-class-aux
    (implies (classes-wellformed classes)
             (classes-wellformed new-classes)))

  (std::defret classhash-keys-subset-of-remhash-implies-empty-of-<fn>
    (implies (subsetp-equal (alist-keys (nth *classhash-table-get* classhash))
                            rem-hash-lst)
             (equal (alist-keys (nth *classhash-table-get* new-classhash)) nil))
    :hints(("Goal" :in-theory (enable classes-hash-add))))

  


  )

(define classhash-table-clear-prof (classhash)
  :enabled t
  (classhash-table-clear classhash))

;; (define classes-refine-class ((node natp)
;;                               (s32v)
;;                               (classhash)
;;                               (classes)
;;                               (aignet))
;;   ;; :inline t
;;   :guard (and (< node (classes-size classes))
;;               (equal (classes-size classes) (s32v-nrows s32v))
;;               (<= (classes-size classes) (num-fanins aignet))
;;               (classes-wellformed classes))
;;   :returns (mv new-classhash
;;                new-classes
;;                (nrefines-out natp :rule-classes :type-prescription))
;;   (b* ((node (lnfix node))
       ;; ((when (or (>= node (node-head node classes))
       ;;            (< (node-next node classes) node)))
;;        ;;  ;; Either node is not the head or it is in a singleton class, so no refinement.
;;        ;;  (mv classhash classes 0))
;;        ;; (classhash (classhash-table-clear-prof classhash))
;;        )
;;     (classes-refine-class-aux node (node-next node classes) 0
;;                               s32v classhash classes aignet))
;;   ///
  
;;   (std::defret classes-size-of-classes-refine-class
;;     (equal (classes-size new-classes) (classes-size classes)))

;;   (std::defret classes-wellformed-of-classes-refine-class
;;     (implies (classes-wellformed classes)
;;              (classes-wellformed new-classes))))


(define show-class-nexts ((n natp) classes)
  :measure (nfix (- (classes-size classes) (nfix n)))
  :guard (<= n (classes-size classes))
  (if (zp (- (classes-size classes) (nfix n)))
      nil
    (cons (node-next n classes)
          (show-class-nexts (1+ (lnfix n)) classes))))

(define show-class-heads ((n natp) classes)
  :measure (nfix (- (classes-size classes) (nfix n)))
  :guard (<= n (classes-size classes))
  (if (zp (- (classes-size classes) (nfix n)))
      nil
    (cons (node-head n classes)
          (show-class-heads (1+ (lnfix n)) classes))))

(Define show-classes (classes)
  (list (cons :nexts (show-class-nexts 0 classes))
        (cons :heads (show-class-heads 0 classes))))


(define classes-refine-update-stats ((node natp)
                                     (nrefines-class natp)
                                     (nclass-lits-refined natp)
                                     (nconst-lits-refined natp)
                                     (nclasses-refined natp))
  :inline t
  :returns (mv (nclass-lits-refined-out natp :rule-classes :type-prescription)
               (nconst-lits-refined-out natp :rule-classes :type-prescription)
               (nclasses-refined-out natp :rule-classes :type-prescription))
  (b* ((nclasses-refined (+ (if (eql 0 (lnfix nrefines-class)) 0 1) (lnfix nclasses-refined))))
    (if (mbe :logic (zp node) :exec (eql node 0))
        (mv (lnfix nclass-lits-refined)
            (+ (lnfix nrefines-class) (lnfix nconst-lits-refined))
            nclasses-refined)
      (mv (+ (lnfix nrefines-class) (lnfix nclass-lits-refined))
            (lnfix nconst-lits-refined)
            nclasses-refined))))
                                     


(define classes-refine-aux ((node natp :type (integer 0 *))
                            (nclass-lits-refined natp :type (integer 0 *))
                            (nconst-lits-refined natp :type (integer 0 *))
                            (nclasses-refined natp :type (integer 0 *))
                            (s32v)
                            (classhash)
                            (classes)
                            (aignet))
  ;; This loop needs to be really highly optimized, especially for singleton nodes!
  :guard (and (<= node (classes-size classes))
              (equal (classes-size classes) (s32v-nrows s32v))
              (<= (classes-size classes) (num-fanins aignet))
              (classes-wellformed classes))
  :split-types t
  :returns (mv new-classhash
               new-classes
               (nclass-lits-refined-out natp :rule-classes :type-prescription)
               (nconst-lits-refined-out natp :rule-classes :type-prescription)
               (nclasses-refined-out natp :rule-classes :type-prescription))
  (b* (((when (mbe :logic (zp node)
                   :exec (int= node 0)))
        ;; (or (classes-check-consistency (classes-size classes) classes)
        ;;     (cw "Became inconsistent after refine~%")
        ;;     (break$))
        (mv classhash classes (lnfix nclass-lits-refined) (lnfix nconst-lits-refined) (lnfix nclasses-refined)))
       (node (the (integer 0 *)
                  (+ -1 (the (integer 0 *) node))))
       ((when ;; if head is less, node is in a class but is not not the head node; if equal, it's a singleton
            (or (>= (the (integer 0 *) node)
                    (the (integer 0 *) (node-head node classes)))
                (< (the (integer 0 *) (node-next node classes))
                   (the (integer 0 *) node))
                ))
        (classes-refine-aux node nclass-lits-refined nconst-lits-refined nclasses-refined
                            s32v classhash classes aignet))
       ((mv classhash classes nrefines-class) (classes-refine-class-aux node (node-next node classes)
                                                                        0 nil s32v classhash classes aignet))
       ((mv nclass-lits-refined nconst-lits-refined nclasses-refined)
        (classes-refine-update-stats node nrefines-class nclass-lits-refined nconst-lits-refined nclasses-refined)))
    (classes-refine-aux node nclass-lits-refined nconst-lits-refined nclasses-refined
                        s32v classhash classes aignet))
  ///
  (std::defret classes-size-of-classes-refine-aux
    (equal (classes-size new-classes) (classes-size classes)))

  (std::defret classes-wellformed-of-classes-refine-aux
    (implies (classes-wellformed classes)
             (classes-wellformed new-classes))))

(define classes-refine ((s32v)
                        (classes)
                        (aignet))
  :guard (and (equal (classes-size classes) (s32v-nrows s32v))
              (<= (classes-size classes) (num-fanins aignet))
              (classes-wellformed classes))
  :returns (mv new-classes
               (nclass-lits-refined natp :rule-classes :type-prescription)
               (nconst-lits-refined natp :rule-classes :type-prescription)
               (nclasses-refined natp :rule-classes :type-prescription))
  ;; might be memory hungry to keep recreating classhash?
  (b* (((acl2::local-stobjs classhash)
        (mv classhash classes nclass-lits-refined nconst-lits-refined nclasses-refined)))
    (classes-refine-aux (classes-size classes) 0 0 0 s32v classhash classes aignet))
  ///
  (std::defret classes-size-of-classes-refine
    (equal (classes-size new-classes) (classes-size classes)))

  (std::defret classes-wellformed-of-classes-refine
    (implies (classes-wellformed classes)
             (classes-wellformed new-classes))))


  
    
(define classes-counts-aux ((n natp)
                            (max natp)
                            (nclasses natp)
                            (nconst-lits natp)
                            (nclass-lits natp)
                            (classes))
  :guard (and (eql max (classes-size classes))
              (<= (nfix n) (classes-size classes)))
  :returns (mv (nclasses-out natp :rule-classes :type-prescription)
               (nconst-lits-out natp :rule-classes :type-prescription)
               (nclass-lits-out natp :rule-classes :type-prescription))
  :measure (nfix (- (classes-size classes) (nfix n)))
  ;; The three stats returned are disjoint subsets of the nodes, so the number of nodes with no equivalences is
  ;; (- (num-fanins) (+ nconst-lits nclasses nclass-lits)) (where the 1 is for the constant-0 node).
  (b* ((nclasses (lnfix nclasses))
       (nconst-lits (lnfix nconst-lits))
       (nclass-lits (lnfix nclass-lits))
       ((when (mbe :logic (zp (- (classes-size classes) (nfix n)))
                   :exec (eql n max)))
        (mv nclasses nconst-lits nclass-lits))
       (n (lnfix n))
       ((mv nclasses nconst-lits nclass-lits)
        (b* (((when (eql 0 (node-head n classes)))
              ;; node is equivalent to 0
              (if (eql n 0)
                  (mv nclasses nconst-lits nclass-lits)
                (mv nclasses (+ 1 nconst-lits) nclass-lits)))
             ((when (< (node-head n classes) n))
              ;; node is in some other equivalence class
              (mv nclasses nconst-lits (+ 1 nclass-lits)))
             ;; node is its own head -- check whether it has a next, otherwise it's a singleton class
             ((when (<= (node-next n classes) n))
              (mv nclasses nconst-lits nclass-lits)))
          (mv (+ 1 nclasses) nconst-lits nclass-lits))))
    (classes-counts-aux (1+ n) max nclasses nconst-lits nclass-lits classes)))

(define classes-counts (classes &key ((start-node natp) '0))
  :guard (<= start-node (classes-size classes))
  :returns (mv (nclasses natp :rule-classes :type-prescription)
               (nconst-lits natp :rule-classes :type-prescription)
               (nclass-lits natp :rule-classes :type-prescription))
  (classes-counts-aux start-node (classes-size classes) 0 0 0 classes))




(define classes-delete-class-aux ((node natp) (nremoved natp) (classes))
  :guard (and (< node (classes-size classes))
              (classes-wellformed classes))
  :measure (nfix (- (classes-size classes) (nfix node)))
  :returns (mv new-classes (nremoved natp :rule-classes :type-prescription))
  (b* ((node (lnfix node))
       (nremoved (lnfix nremoved))
       (next (node-next node classes))
       ((unless (mbt (and (< node (classes-size classes))
                          (classes-wellformed classes))))
        (mv classes nremoved))
       (classes (node-set-next node node classes))
       (classes (node-set-head node node classes))
       (nremoved (1+ nremoved))
       ((unless (< node next))
        ;; (or (classes-check-consistency (classes-size classes) classes)
        ;;     (cw "Became inconsistent after delete~%")
        ;;     (break$))
        (mv classes nremoved)))
    (classes-delete-class-aux next nremoved classes))
  ///
  (std::defret classes-size-of-<fn>
    (equal (classes-size new-classes) (classes-size classes)))

  (std::defret classes-wellformed-of-<fn>
    (implies (classes-wellformed classes)
             (classes-wellformed new-classes))))


(define classes-delete-class ((node natp) (classes))
  :guard (and (< node (classes-size classes))
              (classes-wellformed classes))
  :returns (mv new-classes (nremoved natp :rule-classes :type-prescription))
  (b* ((head (node-head node classes))
       ((when (eql head 0))
        ;; refuse to delete the constant class...
        (mv classes 0)))
    (classes-delete-class-aux head 0 classes))
  ///
  (std::defret classes-size-of-<fn>
    (equal (classes-size new-classes) (classes-size classes)))

  (std::defret classes-wellformed-of-<fn>
    (implies (classes-wellformed classes)
             (classes-wellformed new-classes))))




