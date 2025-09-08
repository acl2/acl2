; FGL - A Symbolic Simulation Framework for ACL2
;; SPDX-FileCopyrightText: Copyright 2025 Arm Limited and/or its affiliates <open-source-office@arm.com>
;; SPDX-License-Identifier: BSD-3-Clause
;; 
;; Redistribution and use in source and binary forms, with or without
;; modification, are permitted provided that the following conditions are
;; met:

;; o Redistributions of source code must retain the above copyright
;;   notice, this list of conditions and the following disclaimer.

;; o Redistributions in binary form must reproduce the above copyright
;;   notice, this list of conditions and the following disclaimer in the
;;   documentation and/or other materials provided with the distribution.

;; o Neither the name of the copyright holder nor the names of
;;   its contributors may be used to endorse or promote products derived
;;   from this software without specific prior written permission.

;; THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
;; "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
;; LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
;; A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
;; HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
;; SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
;; LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
;; DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
;; THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
;; (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
;; OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.

;; Author: Sol Swords <sol.swords@arm.com>

(in-package "FGL")

(include-book "stack")
(local (include-book "std/lists/nth" :dir :system))
(local (include-book "std/lists/nthcdr" :dir :system))
(local (include-book "arithmetic/top-with-meta" :dir :system))

(local (std::add-default-post-define-hook :fix))




(define stack-scratchobj-bfrs-ok ((n natp) stack
                                  &optional ((bfrstate bfrstate-p) 'bfrstate))
  :guard (< n (stack-full-scratch-len stack))
  :guard-hints (("goal" :in-theory (e/d (scratchobj-bfrs-ok
                                         stack$a-nth-scratch-kind
                                         stack$a-nth-scratch)
                                        (scratchobj-bfrs-ok-in-terms-of-bfrlist))))
  (mbe :logic (scratchobj-bfrs-ok (stack-nth-scratch n stack))
       :exec (case (stack-nth-scratch-kind n stack)
               (:fgl-obj (fgl-bfr-object-p (stack-nth-scratch-fgl-obj n stack)))
               (:fgl-objlist (fgl-bfr-objectlist-p (stack-nth-scratch-fgl-objlist n stack)))
               (:bfr (bfr-p (stack-nth-scratch-bfr n stack)))
               (:bfrlist (bfr-listp (stack-nth-scratch-bfrlist n stack)))
               (:cinst (constraint-instance-bfrs-ok (stack-nth-scratch-cinst n stack)))
               (:cinstlist (constraint-instancelist-bfrs-ok (stack-nth-scratch-cinstlist n stack)))
               (t t))))



(define scratch-index->minor-stack-indices ((n natp) (x minor-stack-p))
  :guard (< n (minor-stack-scratch-len x))
  :measure (len x)
  :hints(("Goal" :in-theory (enable len)))
  :verify-guards nil
  :returns (mv (frame-idx natp :rule-classes :type-prescription)
               (scratch-idx natp :rule-classes :type-prescription))
  (b* ((scratch (minor-frame->scratch (car x)))
       (len (len scratch)))
    (if (mbe :logic (or (< (lnfix n) len) (atom (cdr x)))
             :exec (< (lnfix n) len))
        (mv 0 (lnfix n))
      (b* (((mv frame-idx scratch-idx)
            (scratch-index->minor-stack-indices (- (lnfix n) len) (cdr x))))
        (mv (+ 1 frame-idx) scratch-idx))))
  ///
  (verify-guards scratch-index->minor-stack-indices
    :hints (("goal" :in-theory (enable minor-stack-scratch-len))))
  (defretd minor-stack-nth-scratch-in-terms-of-indices
    (implies (< (nfix n) (minor-stack-scratch-len x))
             (equal (minor-stack-nth-scratch n x)
                    (nth scratch-idx
                         (minor-frame->scratch
                          (nth frame-idx (minor-stack-fix x))))))
    :hints(("Goal" :in-theory (enable minor-stack-nth-scratch
                                      minor-stack-scratch-len))))

  (defret <fn>-frame-idx-bound
    (< frame-idx (len (minor-stack-fix x)))
    :hints(("Goal" :in-theory (enable len max)))
    :rule-classes :linear)

  (defret <fn>-scratch-idx-bound
    (implies (< (nfix n) (minor-stack-scratch-len x))
             (< scratch-idx (len (minor-frame->scratch (nth frame-idx x)))))
    :hints(("Goal" :in-theory (enable minor-stack-scratch-len)))
    :rule-classes :linear))


(define scratch-index->stack-indices ((n natp) (x major-stack-p))
  :guard (< n (major-stack-scratch-len x))
  :measure (len x)
  :hints(("Goal" :in-theory (enable len)))
  :verify-guards nil
  :returns (mv (major-idx natp :rule-classes :type-prescription)
               (minor-idx natp :rule-classes :type-prescription)
               (scratch-idx natp :rule-classes :type-prescription))
  (b* ((minor-stack (major-frame->minor-stack (car x)))
       (len (minor-stack-scratch-len minor-stack)))
    (if (mbe :logic (or (< (lnfix n) len) (atom (cdr x)))
             :exec (< (lnfix n) len))
        (b* (((mv minor-idx scratch-idx)
              (scratch-index->minor-stack-indices n minor-stack)))
          (mv 0 minor-idx scratch-idx))
      (b* (((mv major-idx minor-idx scratch-idx)
            (scratch-index->stack-indices (- (lnfix n) len) (cdr x))))
        (mv (+ 1 major-idx) minor-idx scratch-idx))))
  ///
  (verify-guards scratch-index->stack-indices
    :hints(("Goal" :in-theory (enable major-stack-scratch-len))))
  
  (defretd major-stack-nth-scratch-in-terms-of-indices
    (implies (< (nfix n) (major-stack-scratch-len x))
             (equal (major-stack-nth-scratch n x)
                    (nth scratch-idx
                         (minor-frame->scratch
                          (nth minor-idx
                               (major-frame->minor-stack
                                (nth major-idx x)))))))
    :hints(("Goal" :in-theory (enable major-stack-nth-scratch
                                      major-stack-scratch-len
                                      minor-stack-nth-scratch-in-terms-of-indices))))

  (defret <fn>-major-idx-bound
    (< major-idx (len (major-stack-fix x)))
    :hints(("Goal" :in-theory (enable len max)))
    :rule-classes :linear)

  (defret <fn>-minor-idx-bound
    (< minor-idx (len (major-frame->minor-stack (nth major-idx x))))
    :rule-classes :linear)

  (defret <fn>-scratch-idx-bound
    (implies (< (nfix n) (major-stack-scratch-len x))
             (< scratch-idx (len (minor-frame->scratch
                                  (nth minor-idx
                                       (major-frame->minor-stack
                                        (nth major-idx x)))))))
    :hints(("Goal" :in-theory (enable major-stack-scratch-len)))
    :rule-classes :linear))

(define minor-frame->scratch-base-index ((n natp) (x minor-stack-p))
  :guard (< n (len x))
  :measure (len x)
  :hints(("Goal" :in-theory (enable len)))
  :ruler-extenders :all
  :verify-guards nil
  :returns (scratch-idx natp :rule-classes :type-prescription)
  (if (zp n)
      0
    (+ (len (minor-frame->scratch (car x)))
       (if (mbt (consp x))
           (minor-frame->scratch-base-index (1- n) (cdr x))
         0)))
  ///
  (verify-guards minor-frame->scratch-base-index
    :hints(("Goal" :in-theory (enable len minor-stack-p))))
  
  (defretd scratch-index->minor-stack-indices-of-<fn>
    (implies (and (< k (len (minor-frame->scratch (nth n x))))
                  (natp k))
             (equal (scratch-index->minor-stack-indices
                     (+ scratch-idx k) x)
                    (mv (nfix n) k)))
    :hints(("Goal" :in-theory (enable scratch-index->minor-stack-indices nth)
            :expand ((:free (idx) (scratch-index->minor-stack-indices idx x)))
            :induct t :do-not '(generalize))))

  (defthmd minor-frame->scratch-base-index-of-scratch-index->minor-stack-indices
    (implies (< (nfix idx) (minor-stack-scratch-len x))
             (b* (((mv minor-idx scratch-idx)
                   (scratch-index->minor-stack-indices idx x)))
               (equal (minor-frame->scratch-base-index minor-idx x)
                      (- (nfix idx) scratch-idx))))
    :hints(("Goal" :in-theory (enable scratch-index->minor-stack-indices
                                      minor-stack-scratch-len
                                      minor-frame->scratch-base-index))))
  
  (defret <fn>-bound
    (<= scratch-idx (- (minor-stack-scratch-len x)
                       (len (minor-frame->scratch (nth n x)))))
    :hints(("Goal" :in-theory (enable minor-stack-scratch-len len nth)))
    :rule-classes :linear)

  (defretd minor-frame->scratch-base-index-inverse
    (implies (< (nfix n) (len (minor-stack-fix x)))
             (equal (minor-frame->scratch-base-index n x)
                    (if (zp n)
                        0
                      (+ (len (minor-frame->scratch (nth (1- n) (minor-stack-fix x))))
                         (minor-frame->scratch-base-index (1- n) x)))))
    :hints(("Goal" :in-theory (enable len nth)))
    :rule-classes ((:definition :install-body nil)))

  (local (in-theory (enable max))))




(define major-frame->scratch-base-index ((n natp) (x major-stack-p))
  :guard (< n (len x))
  :measure (len x)
  :hints(("Goal" :in-theory (enable len)))
  :ruler-extenders :all
  :verify-guards nil
  :returns (scratch-idx natp :rule-classes :type-prescription)
  (if (zp n)
      0
    (+ (minor-stack-scratch-len (major-frame->minor-stack (car x)))
       (if (mbt (consp x))
           (major-frame->scratch-base-index (1- n) (cdr x))
         0)))
  ///
  (verify-guards major-frame->scratch-base-index
    :hints(("Goal" :in-theory (enable len major-stack-p))))
  
  (defretd scratch-index->stack-indices-of-<fn>
    (implies (and (< k (minor-stack-scratch-len
                        (major-frame->minor-stack (nth n x))))
                  (natp k))
             (equal (scratch-index->stack-indices
                     (+ scratch-idx k) x)
                    (b* (((mv minor-idx offset)
                          (scratch-index->minor-stack-indices
                           k (major-frame->minor-stack (nth n x)))))
                      (mv (nfix n) minor-idx offset))))
    :hints(("Goal" :in-theory (enable scratch-index->stack-indices nth)
            :induct t :do-not '(generalize))))

  (defthmd major-frame->scratch-base-index-of-scratch-index->stack-indices
    (implies (< (nfix idx) (major-stack-scratch-len x))
             (b* (((mv major-idx minor-idx scratch-idx)
                   (scratch-index->stack-indices idx x)))
               (equal (+ (major-frame->scratch-base-index major-idx x)
                         (minor-frame->scratch-base-index minor-idx
                                                          (major-frame->minor-stack
                                                           (nth major-idx x)))
                         scratch-idx)
                      (nfix idx))))
    :hints(("Goal" :in-theory (enable scratch-index->stack-indices
                                      major-stack-scratch-len
                                      minor-frame->scratch-base-index-of-scratch-index->minor-stack-indices))))
  (defret <fn>-bound
    (<= scratch-idx (- (major-stack-scratch-len x)
                       (minor-stack-scratch-len
                        (major-frame->minor-stack (nth n x)))))
    :hints(("Goal" :in-theory (enable major-stack-scratch-len len nth)))
    :rule-classes :linear)

  (defretd major-frame->scratch-base-index-inverse
    (implies (< (nfix n) (len (major-stack-fix x)))
             (equal (major-frame->scratch-base-index n x)
                    (if (zp n)
                        0
                      (+ (minor-stack-scratch-len (major-frame->minor-stack (nth (1- n) (major-stack-fix x))))
                         (major-frame->scratch-base-index (1- n) x)))))
    :hints(("Goal" :in-theory (enable len nth major-stack-fix max)))
    :rule-classes ((:definition :install-body nil))))





(defthmd nth-scratch-of-minor-in-terms-of-minor-stack-nth-scratch
  (b* ((minor-frame (nth m minor-stack))
       (scratch (minor-frame->scratch minor-frame)))
    (implies (and (< (nfix m) (len (minor-stack-fix minor-stack)))
                  (< (nfix k) (len scratch)))
             (equal (nth k scratch)
                    (minor-stack-nth-scratch (+ (minor-frame->scratch-base-index m minor-stack)
                                                (nfix k))
                                             minor-stack))))
  :hints(("Goal" :in-theory (enable minor-stack-nth-scratch
                                    minor-frame->scratch-base-index
                                    len max nth))))

(defthmd nth-scratch-of-minor-of-major-in-terms-of-stack-nth-scratch
  (b* ((major-frame (nth n (major-stack-fix stack)))
       (minor-stack (major-frame->minor-stack major-frame))
       (minor-frame (nth m minor-stack))
       (scratch (minor-frame->scratch minor-frame)))
    (implies (and (< (nfix n) (len (major-stack-fix stack)))
                  (< (nfix m) (len minor-stack))
                  (< (nfix k) (len scratch)))
             (equal (nth k scratch)
                    (major-stack-nth-scratch
                     (+ (major-frame->scratch-base-index n stack)
                        (minor-frame->scratch-base-index m minor-stack)
                        (nfix k))
                     stack))))
  :hints(("Goal" :in-theory (enable major-stack-nth-scratch
                                    major-frame->scratch-base-index
                                    len max nth
                                    nth-scratch-of-minor-in-terms-of-minor-stack-nth-scratch)
          :induct (major-frame->scratch-base-index n stack)
          :expand ((:free (idx) (major-stack-nth-scratch idx stack))))))


(define stack-scratch-range ((from natp) (to natp) stack)
  :guard (and (<= from to)
              (<= to (stack-full-scratch-len stack)))
  :measure (nfix (- (nfix to) (nfix from)))
  :Returns (range scratchlist-p)
  (if (mbe :logic (zp (- (nfix to) (nfix from)))
           :exec (eql from to))
      nil
    (cons (stack-nth-scratch from stack) 
          (stack-scratch-range (1+ (lnfix from)) to stack)))
  ///
  (local (defun ind (n from)
           (if (zp n)
               from
             (ind (1- n) (1+ (lnfix from))))))
  (defret nth-of-<fn>
    (implies (< (+ (nfix n) (nfix from)) (nfix to))
             (equal (nth n range)
                    (stack-nth-scratch (+ (nfix n) (nfix from)) stack)))
    :hints(("Goal" :in-theory (enable nth)
            :expand ((stack-scratch-range from to stack))
            :induct (ind n from))))

  (defret len-of-<fn>
    (equal (len range) (nfix (- (nfix to) (nfix from))))
    :hints(("Goal" :in-theory (enable len))))

  (local (include-book "std/lists/nth" :dir :system))
  (defthmd minor-frame->scratch-in-terms-of-stack-scratch-range
    (b* ((major-frame (nth n (major-stack-fix stack)))
         (minor-stack (major-frame->minor-stack major-frame))
         (minor-frame (nth m minor-stack))
         (scratch (minor-frame->scratch minor-frame)))
      (implies (and (< (nfix n) (len (major-stack-fix stack)))
                    (< (nfix m) (len minor-stack)))
               (equal scratch
                      (stack-scratch-range (+ (major-frame->scratch-base-index n stack)
                                              (minor-frame->scratch-base-index m minor-stack))
                                           (+ (major-frame->scratch-base-index n stack)
                                              (minor-frame->scratch-base-index m minor-stack)
                                              (len scratch))
                                           stack))))
    :hints ((acl2::equal-by-nths-hint)
            '(:in-theory (enable stack$a-nth-scratch
                                 nth-scratch-of-minor-of-major-in-terms-of-stack-nth-scratch)))))


(define stack-scratch-range-bfrs-ok ((from natp) (to natp) stack
                                     &optional ((bfrstate bfrstate-p) 'bfrstate))
  :guard (and (<= from to)
              (<= to (stack-full-scratch-len stack)))
  :measure (nfix (- (nfix to) (nfix from)))
  :returns (ok)
  (if (mbe :logic (zp (- (nfix to) (nfix from)))
           :exec (eql from to))
      t
    (and (stack-scratchobj-bfrs-ok from stack)
         (stack-scratch-range-bfrs-ok (1+ (lnfix from)) to stack)))
  ///
  (defthm stack-scratch-range-bfrs-ok-decomp
    (implies (and (<= (nfix from) (nfix split))
                  (<= (nfix split) (nfix to)))
             (equal (stack-scratch-range-bfrs-ok from to stack)
                    (and (stack-scratch-range-bfrs-ok from split stack)
                         (stack-scratch-range-bfrs-ok split to stack))))
    :hints (("goal" :induct (stack-scratch-range-bfrs-ok from split stack)
             :in-theory (enable* acl2::arith-equiv-forwarding)
             :expand ((:free (to) (stack-scratch-range-bfrs-ok from to stack)))))
    :rule-classes nil)

  (defret <fn>-in-terms-of-stack-scratch-range
    (equal ok
           (bfr-listp (scratchlist-bfrlist (stack-scratch-range from to stack))))
    :hints(("Goal" :in-theory (enable stack-scratchobj-bfrs-ok
                                      stack-scratch-range)
            :induct t
            :expand ((stack-scratch-range from to stack)
                     (stack-scratch-range-bfrs-ok from to stack)))))

  
  (defthmd minor-frame->scratch-bfrlist-in-terms-of-stack-scratch-range-bfrs-ok
    (b* ((major-frame (nth n (major-stack-fix stack)))
         (minor-stack (major-frame->minor-stack major-frame))
         (minor-frame (nth m minor-stack))
         (scratch (minor-frame->scratch minor-frame)))
      (implies (and (< (nfix n) (len (major-stack-fix stack)))
                    (< (nfix m) (len minor-stack)))
               (equal (bfr-listp (scratchlist-bfrlist scratch))
                      (stack-scratch-range-bfrs-ok (+ (major-frame->scratch-base-index n stack)
                                                      (minor-frame->scratch-base-index m minor-stack))
                                                   (+ (major-frame->scratch-base-index n stack)
                                                      (minor-frame->scratch-base-index m minor-stack)
                                                      (len scratch))
                                                   stack))))
    :hints(("Goal" :use minor-frame->scratch-in-terms-of-stack-scratch-range))))




(define stack-nth-frame-minor-bindings-range-bfrs-ok ((n natp)
                                                      (from natp) (to natp)
                                                      stack
                                                      &optional ((bfrstate bfrstate-p) 'bfrstate))
  :guard (and (< n (stack-frames stack))
              (<= from to)
              (<= to (stack-nth-frame-minor-frames n stack)))
  :measure (nfix (- (nfix to) (nfix from)))
  (if (mbe :logic (zp (- (nfix to) (nfix from)))
           :exec (eql from to))
      t
    (and (fgl-bfr-object-bindings-p (stack-nth-frame-minor-bindings n from stack))
         (stack-nth-frame-minor-bindings-range-bfrs-ok n (1+ (lnfix from)) to stack)))
  ///


  ;; (local
  ;;  (defthm stack-scratch-range-bfrs-ok-decomp-special
  ;;    (implies (and (<= (nfix from) (nfix split))
  ;;                  (<= (nfix split) (nfix to)))
  ;;             (equal (bfr-listp (scratchlist-bfrlist (stack-scratch-range from to stack)))
  ;;                    (and (bfr-listp (scratchlist-bfrlist (stack-scratch-range from split stack))
  ;;                                    (stack-scratch-range-bfrs-ok split to stack))))
  ;;    :hints (("goal" :induct (stack-scratch-range-bfrs-ok from split stack)
  ;;             :expand ((:free (to) (stack-scratch-range-bfrs-ok from to stack)))))
  ;;    :rule-classes nil)

  (local (defthm minor-frame->scratch-base-index-plus-len-scratch-when-length-minus-1-lemma
           (implies (consp x)
                    (equal (+ (minor-frame->scratch-base-index (+ -1 (len x)) x)
                              (len (minor-frame->scratch (nth (+ -1 (len x)) x))))
                           (minor-stack-scratch-len x)))
           :hints(("Goal" :in-theory (enable minor-frame->scratch-base-index
                                             minor-stack-scratch-len
                                             len nth)))))

  (local (defthm minor-frame->scratch-base-index-plus-len-scratch-when-length-minus-1
           (implies (equal (nfix m) (+ -1 (len x)))
                    (equal (+ (minor-frame->scratch-base-index m x)
                              (len (minor-frame->scratch (nth m x))))
                           (minor-stack-scratch-len x)))
           :hints(("Goal" :use ((:instance minor-frame->scratch-base-index-plus-len-scratch-when-length-minus-1-lemma))
                   :in-theory (e/d (len)
                                   (minor-frame->scratch-base-index-plus-len-scratch-when-length-minus-1-lemma))))))

  (local (defthm consp-cdr-nthcdr
           (equal (consp (cdr (nthcdr n x)))
                  (< (+ 1 (nfix n)) (len x)))
           :hints(("Goal" :in-theory (enable nthcdr len)))))

  (local (in-theory (disable len-of-major-stack-fix)))
  
  (defthmd minor-stack-bfrlist-ok-in-terms-of-stack-scan-lemma
    (b* ((major-frame (nth n (major-stack-fix stack)))
         (minor-stack (major-frame->minor-stack major-frame)))
      (implies (and (< (nfix n) (len (major-stack-fix stack)))
                    (< (nfix m) (len minor-stack)))
               (equal (bfr-listp (minor-stack-bfrlist (nthcdr m minor-stack)))
                      (and (stack-scratch-range-bfrs-ok
                            (+ (major-frame->scratch-base-index n stack)
                               (minor-frame->scratch-base-index m minor-stack))
                            (+ (major-frame->scratch-base-index n stack)
                               (minor-stack-scratch-len minor-stack))
                            stack)
                           (stack-nth-frame-minor-bindings-range-bfrs-ok
                            n m (stack-nth-frame-minor-frames n stack) stack)))))
    :hints (("goal" :induct (stack-nth-frame-minor-bindings-range-bfrs-ok
                             n m (stack-nth-frame-minor-frames n stack) stack)
             :in-theory (enable stack$a-nth-frame-minor-bindings
                                stack$a-nth-frame-minor-frames
                                minor-frame->scratch-bfrlist-in-terms-of-stack-scratch-range-bfrs-ok
                                minor-frame-bfrlist
                                stack$a-frames
                                len)
             :expand ((minor-stack-bfrlist
                       (nthcdr m (major-frame->minor-stack (nth n (major-stack-fix stack)))))))
            (and stable-under-simplificationp
                 '(:use ((:instance stack-scratch-range-bfrs-ok-decomp
                          (from (+ (MAJOR-FRAME->SCRATCH-BASE-INDEX N STACK)
                                   (MINOR-FRAME->SCRATCH-BASE-INDEX
                                    M
                                    (MAJOR-FRAME->MINOR-STACK (NTH N (MAJOR-STACK-FIX STACK))))))
                          (split (+ (MAJOR-FRAME->SCRATCH-BASE-INDEX N STACK)
                                    (MINOR-FRAME->SCRATCH-BASE-INDEX
                                     (+ 1 (NFIX M))
                                     (MAJOR-FRAME->MINOR-STACK (NTH N (MAJOR-STACK-FIX STACK))))))
                          (to (+ (MAJOR-FRAME->SCRATCH-BASE-INDEX N STACK)
                                 (MINOR-STACK-SCRATCH-LEN
                                  (MAJOR-FRAME->MINOR-STACK (NTH N (MAJOR-STACK-FIX STACK))))))))
                   :expand ((:with minor-frame->scratch-base-index-inverse
                             (:free (stack) (minor-frame->scratch-base-index (+ 1 (nfix m)) stack))))))))

  (local (defthm len-equal-0
           (equal (equal (len x) 0)
                  (not (consp x)))
           :hints(("Goal" :in-theory (enable len)))))
  

  (defthmd minor-stack-bfrlist-ok-in-terms-of-stack-scan
    (b* ((major-frame (nth n (major-stack-fix stack)))
         (minor-stack (major-frame->minor-stack major-frame)))
      (implies (< (nfix n) (len (major-stack-fix stack)))
               (equal (bfr-listp (minor-stack-bfrlist minor-stack))
                      (and (stack-scratch-range-bfrs-ok
                            (major-frame->scratch-base-index n stack)
                            (+ (major-frame->scratch-base-index n stack)
                               (minor-stack-scratch-len minor-stack))
                            stack)
                           (stack-nth-frame-minor-bindings-range-bfrs-ok
                            n 0 (stack-nth-frame-minor-frames n stack) stack)))))
    :hints (("goal" :use ((:instance minor-stack-bfrlist-ok-in-terms-of-stack-scan-lemma
                           (m 0)))
             :in-theory (enable MINOR-FRAME->SCRATCH-BASE-INDEX)))))


(define stack-frame-range-bindings-bfrs-ok ((from natp) (to natp)
                                            stack
                                            &optional ((bfrstate bfrstate-p) 'bfrstate))
  :guard (and (<= from to)
              (<= to (stack-frames stack)))
  :measure (nfix (- (nfix to) (nfix from)))
  (if (mbe :logic (zp (- (nfix to) (nfix from)))
           :exec (eql from to))
      t
    (and (stack-nth-frame-minor-bindings-range-bfrs-ok
          from 0 (stack-nth-frame-minor-frames from stack) stack)
         (fgl-bfr-object-bindings-p (stack-nth-frame-bindings from stack))
         (stack-frame-range-bindings-bfrs-ok (1+ (lnfix from)) to stack)))
  ///
  (local (defthm consp-cdr-nthcdr
           (equal (consp (cdr (nthcdr n x)))
                  (< (+ 1 (nfix n)) (len x)))
           :hints(("Goal" :in-theory (enable nthcdr len)))))

  (local (in-theory (disable len-of-major-stack-fix)))

  (local (defthm major-frame->scratch-base-index-plus-len-scratch-when-length-minus-1-lemma
           (implies (major-stack-p x)
           (equal (+ (major-frame->scratch-base-index (+ -1 (len x)) x)
                     (minor-stack-scratch-len (major-frame->minor-stack (nth (+ -1 (len x)) x))))
                  (major-stack-scratch-len x)))
           :hints(("Goal" :in-theory (enable major-frame->scratch-base-index
                                             major-stack-scratch-len
                                             len nth)))))

  (local (defthm minor-frame->scratch-base-index-plus-len-scratch-when-length-minus-1
           (implies (equal (nfix m) (+ -1 (len (major-stack-fix x))))
                    (equal (+ (major-frame->scratch-base-index m x)
                              (minor-stack-scratch-len (major-frame->minor-stack (nth m (major-stack-fix x)))))
                           (major-stack-scratch-len x)))
           :hints(("Goal" :use ((:instance major-frame->scratch-base-index-plus-len-scratch-when-length-minus-1-lemma (x (major-stack-fix x))))
                   :in-theory (e/d ()
                                   (major-frame->scratch-base-index-plus-len-scratch-when-length-minus-1-lemma))))))
  
  (defthmd major-stack-bfrlist-ok-in-terms-of-stack-scan-lemma
    (implies (< (nfix n) (len (major-stack-fix stack)))
             (equal (bfr-listp (major-stack-bfrlist (nthcdr n (major-stack-fix stack))))
                    (and (stack-scratch-range-bfrs-ok
                          (major-frame->scratch-base-index n stack)
                          (major-stack-scratch-len stack)
                          stack)
                         (stack-frame-range-bindings-bfrs-ok
                          n (stack-frames stack) stack))))
    :hints (("goal" :induct (stack-frame-range-bindings-bfrs-ok
                             n (stack-frames stack) stack)
             :expand ((major-stack-bfrlist (nthcdr n (major-stack-fix stack)))
                      (:with major-frame->scratch-base-index-inverse
                             (:free (stack) (major-frame->scratch-base-index (+ 1 (nfix n)) stack))))
             :in-theory (enable stack$a-nth-frame-minor-frames
                                minor-stack-bfrlist-ok-in-terms-of-stack-scan
                                stack$a-frames
                                stack$a-nth-frame-bindings
                                major-frame-bfrlist
                                len)
             :do-not '(generalize))
            (and stable-under-simplificationp
                 '(:use ((:instance stack-scratch-range-bfrs-ok-decomp
                          (from (MAJOR-FRAME->SCRATCH-BASE-INDEX N STACK))
                          (split (+ (MAJOR-FRAME->SCRATCH-BASE-INDEX N STACK)
                                    (MINOR-STACK-SCRATCH-LEN
                                     (MAJOR-FRAME->MINOR-STACK (NTH N (MAJOR-STACK-FIX STACK))))))
                          (to (major-stack-scratch-len stack))))))))

  (defthmd major-stack-bfrlist-ok-in-terms-of-stack-scan
    (equal (bfr-listp (major-stack-bfrlist stack))
           (and (stack-scratch-range-bfrs-ok
                 0 (major-stack-scratch-len stack) stack)
                (stack-frame-range-bindings-bfrs-ok 0 (stack-frames stack) stack)))
    :hints (("goal" :use ((:instance major-stack-bfrlist-ok-in-terms-of-stack-scan-lemma
                           (n 0)))
             :in-theory (e/d (len-of-major-stack-fix MAJOR-FRAME->SCRATCH-BASE-INDEX)
                             (major-stack-bfrlist-ok-in-terms-of-stack-scan-lemma))))))


(define stack-bfrs-ok (stack
                       &optional ((bfrstate bfrstate-p) 'bfrstate))
  :enabled t
  :guard-hints (("goal" :in-theory (enable major-stack-bfrlist-ok-in-terms-of-stack-scan
                                           stack$a-full-scratch-len)))
  (mbe :logic (bfr-listp (major-stack-bfrlist (stack-extract stack)))
       :exec (and (stack-scratch-range-bfrs-ok 0 (stack-full-scratch-len stack) stack)
                  (stack-frame-range-bindings-bfrs-ok 0 (stack-frames stack) stack))))
