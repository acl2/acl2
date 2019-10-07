; FGL - A Symbolic Simulation Framework for ACL2
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

(in-package "AIGNET")

(include-book "pathcond-aignet")
(include-book "mark-bfrs-base")

(local (defthm natp-car-nth-of-nbalist
         (implies (and (nbalistp x)
                       (< (nfix n) (len x)))
                  (natp (car (nth n x))))))

(local (defthm hons-assoc-equal-of-nth-when-nbalistp
         (implies (and (nbalistp x)
                       (< (nfix n) (len x)))
                  (equal (hons-assoc-equal (car (nth n x)) x)
                         (nth n x)))
         :hints(("Goal" :in-theory (enable nth nbalistp)))))

(local (defthmd hons-assoc-equal-when-equal-car-nth
         (implies (and (nbalistp x)
                       (equal a (car (nth n x)))
                       (< (nfix n) (len x)))
                  (equal (hons-assoc-equal a x)
                         (nth n x)))))

(local (defthm consp-nth-when-nbalistp
         (implies (and (nbalistp x)
                       (< n (len x))
                       (natp n))
                  (consp (nth n x)))
         :rule-classes :type-prescription))
         

(local (defthm nbalist-lookup-of-nth-n
         (implies (and (nbalistp x)
                       (< (nfix n) (len x)))
                  (equal (nbalist-lookup (car (nth n x)) x)
                         (cdr (nth n x))))
         :hints(("Goal" :in-theory (enable nbalist-lookup nbalistp nth hons-assoc-equal
                                           hons-assoc-equal-when-equal-car-nth)
                 :induct (nth n x)))))

(local (defthm nthcdr-of-nil
         (equal (nthcdr n nil) nil)))

(local (defthm consp-of-nthcdr
         (iff (consp (nthcdr n x))
              (< (nfix n) (len x)))))

(local (defthm car-of-nthcdr
         (equal (car (nthcdr n x))
                (nth n x))))

(local (defthm cdr-of-nthcdr
         (equal (cdr (nthcdr n x))
                (nthcdr n (cdr x)))))

(local (defthm nbalistp-of-nthcdr
         (implies (nbalistp x)
                  (nbalistp (nthcdr n x)))
         :hints(("Goal" :in-theory (enable nbalistp nthcdr)))))

(define aignet-pathcond-bfrlist-aux ((n natp)
                                     (aignet-pathcond)
                                     (cube lit-listp))
  :guard (<= n (aignet-pathcond-len aignet-pathcond))
  :measure (nfix (- (aignet-pathcond-len aignet-pathcond) (nfix n)))
  :returns (new-cube lit-listp)
  (b* (((when (mbe :logic (zp (- (aignet-pathcond-len aignet-pathcond) (nfix n)))
                   :exec (eql (aignet-pathcond-len aignet-pathcond) n)))
        (lit-list-fix cube))
       (id (aignet-pathcond-nthkey n aignet-pathcond))
       (bit (aignet-pathcond-lookup id aignet-pathcond))
       ;; For a pathcond to eval to true, each ID has to evaluate to its
       ;; corresponding bit from the nbalist.  For the corresponding lit to
       ;; eval to true, we need to NOT negate it if the resulting evaluation is
       ;; 1.  So we negate the bit.
       (lit (make-lit id (b-not bit)))
       (cube (cons lit (lit-list-fix cube))))
    (aignet-pathcond-bfrlist-aux (1+ (lnfix n)) aignet-pathcond cube))
  ///
  (defret aignet-pathcond-bfrlist-aux-elim
    (equal new-cube
           (revappend (nthcdr n (nbalist-to-cube aignet-pathcond))
                      (lit-list-fix cube)))
    :hints (("goal" :induct <call>
             :in-theory (enable nbalist-lookup)
             :expand (<call>
                      (acl2::rev (nthcdr n (nbalist-to-cube aignet-pathcond))))))))

(define aignet-pathcond-bfrlist ((aignet-pathcond))
  :returns (cube lit-listp)
  :prepwork ((local (defthm lit-listp-of-rev
                      (implies (lit-listp X)
                               (lit-listp (acl2::rev x)))
                      :hints(("Goal" :in-theory (enable acl2::rev))))))
  (aignet-pathcond-bfrlist-aux 0 aignet-pathcond nil)
  ///
  (defret aignet-pathcond-bfrlist-elim
    (equal cube
           (acl2::rev (nbalist-to-cube aignet-pathcond)))))


(local (defthm natp-caar-of-nbalist-fix
         (implies (consp (nbalist-fix x))
                  (natp (caar (nbalist-fix x))))
         :rule-classes :type-prescription))

(local (defthm cdar-of-nbalist-fix-when-caar-zero
         (implies (equal (caar (nbalist-fix x)) 0)
                  (equal (cdar (nbalist-fix x)) 1))
         :hints(("Goal" :in-theory (enable nbalist-fix)))))

(defsection nbalist-to-cube
  (local (std::set-define-current-function nbalist-to-cube))
  (local (in-theory (enable nbalist-to-cube)))

  (defthm bfr-listp-of-nbalist-to-cube
    (implies (bounded-pathcond-p x (+ 1 (nfix num-fanins)))
             (fgl::bfr-listp (remove 0 (nbalist-to-cube x))
                             (fgl::bfrstate (fgl::bfrmode :aignet) num-fanins)))
    :hints(("Goal" :in-theory (enable fgl::bfr-p fgl::bfr-listp
                                      bounded-pathcond-p-redef
                                      satlink::equal-of-make-lit)))))




(local (defthm car-nth-bound-when-bounded-pathcond-p
         (implies (and (bounded-pathcond-p x bound)
                       (< (nfix n) (len x))
                       (nbalistp x)
                       (natp bound))
                  (< (car (nth n x)) bound))
         :hints(("Goal" :in-theory (enable bounded-pathcond-p-redef
                                           nth)))))

(local (defthm natp-car-nth-of-nbalist-type
         (implies (and (nbalistp x)
                       (< n (len x))
                       (natp n))
                  (natp (car (nth n x))))
         :rule-classes :type-prescription))

;; (defthm nbalist-lookup-of-car-nth
;;   (implies (< (nfix n) (len (nbalist-fix x)))
;;            (equal (nbalist-lookup (car (nth n (nbalist-fix x))) x)
;;                   (cdr (nth n (nbalist-fix x)))))
;;   :hints(("Goal" :in-theory (enable nbalist-lookup))))

(local (in-theory (enable nbalist-lookup)))


(local
 #!fgl
 (defsection bfrs-markedp

   (acl2::defexample bfrs-markedp-example
     :pattern (bfr-markedp bfr bitarr)
     :templates (bfr)
     :instance-rulename bfrs-markedp-instancing)
   
   (defthm bfrs-markedp-nil
     (bfrs-markedp nil bitarr)
     :hints(("Goal" :in-theory (enable bfrs-markedp))))

   (defthm bfrs-markedp-of-append
     (iff (bfrs-markedp (append x y) bitarr)
          (and (bfrs-markedp x bitarr)
               (bfrs-markedp y bitarr)))
     :hints ((acl2::witness)))

   (defthm bfr-markedp-of-cons
     (iff (bfrs-markedp (cons x y) bitarr)
          (and (bfr-markedp x bitarr)
               (bfrs-markedp y bitarr)))
     :hints ((acl2::witness)))))

#!fgl
(defthm bfrs-markedp-of-remove-0
  (iff (bfrs-markedp (remove 0 bfrs) bitarr)
       (bfrs-markedp bfrs bitarr))
  :hints ((and stable-under-simplificationp
               (let ((lit (assoc 'bfrs-markedp clause)))
                 `(:expand (,lit)
                   :in-theory (enable bfrs-markedp-necc)
                   :cases ((equal 0 (bfrs-markedp-witness . ,(cdr lit)))))))))

(define aignet-pathcond-mark-bfrs-aux ((n natp)
                                       (aignet-pathcond)
                                       bitarr)
  :guard (and (<= n (aignet-pathcond-len aignet-pathcond))
              (ec-call (bounded-pathcond-p aignet-pathcond (bits-length bitarr))))
  :measure (nfix (- (aignet-pathcond-len aignet-pathcond) (nfix n)))
  :guard-hints (("goal" :in-theory (enable fgl::bfr-mark)))
  :returns new-bitarr
  (b* (((when (mbe :logic (zp (- (aignet-pathcond-len aignet-pathcond) (nfix n)))
                   :exec (eql (aignet-pathcond-len aignet-pathcond) n)))
        bitarr)
       (id (aignet-pathcond-nthkey n aignet-pathcond))
       ((when (eql id 0))
        (aignet-pathcond-mark-bfrs-aux (1+ (lnfix n)) aignet-pathcond bitarr))
       ;; For a pathcond to eval to true, each ID has to evaluate to its
       ;; corresponding bit from the nbalist.  For the corresponding lit to
       ;; eval to true, we need to NOT negate it if the resulting evaluation is
       ;; 1.  So we negate the bit.
       (bitarr (mbe :logic (b* ((bit (aignet-pathcond-lookup id aignet-pathcond))
                                (lit (make-lit id (b-not bit))))
                             (fgl::bfr-mark lit bitarr))
                    :exec (set-bit id 1 bitarr))))
    (aignet-pathcond-mark-bfrs-aux (1+ (lnfix n)) aignet-pathcond bitarr))
  ///
  (local (defthm nth-of-nbalist-fix-to-nth-of-nbalist-to-cube
           (implies (and (nbalistp x)
                         (equal neg (b-not (cdr (nth n x))))
                         (< (nfix n) (len x)))
                    (equal (make-lit (car (nth n x)) neg)
                           (nth n (nbalist-to-cube x))))))

  (local (in-theory (disable nth-of-nbalist-to-cube)))

  (local (defthm bfr-listp-nthcdr-implies-bfr-p-nth
           (implies (and (fgl::bfr-listp (remove 0 (nthcdr n x)))
                         (not (equal (nth n x) 0)))
                    (fgl::bfr-p (nth n x)))
           :hints(("Goal" :expand ((fgl::bfr-listp (remove 0 (nthcdr n x))))))))

  (local (defun nth-of-nbalist-ind (n nbalist)
           (if (zp n)
               nbalist
             (nth-of-nbalist-ind (1- n) (cdr (nbalist-fix nbalist))))))

  

  (local (defthm cdr-nth-of-nbalist-fix-when-car-nth-0
           (implies (equal (car (nth n (nbalist-fix x))) 0)
                    (equal (cdr (nth n (nbalist-fix x))) 1))
           :hints(("Goal" :in-theory (enable nbalist-fix nth)
                   :induct (nth-of-nbalist-ind n x)))))

  (local (defthm nth-of-nbalist-to-cube-equal-0
           (iff (equal (nth n (nbalist-to-cube nbalist)) 0)
                (equal (car (nth n (nbalist-fix nbalist))) 0))
           :hints(("Goal" :in-theory (enable nbalist-to-cube nth
                                             satlink::equal-of-make-lit)
                   :induct (nth-of-nbalist-ind n nbalist)
                   :expand ((nbalist-to-cube nbalist))))))

  (local (defthm nth-of-nbalist-to-cube-equal-0-rw
           (implies (equal (car (nth n (nbalist-fix nbalist))) 0)
                    (equal (nth n (nbalist-to-cube nbalist)) 0))
           :hints(("Goal" :in-theory (enable nbalist-to-cube nth
                                             satlink::equal-of-make-lit)
                   :induct (nth-of-nbalist-ind n nbalist)
                   :expand ((nbalist-to-cube nbalist))))))
  
  (defret length-of-<fn>
    (implies (fgl::bfr-listp (remove 0 (nthcdr n (nbalist-to-cube aignet-pathcond)))
                             (fgl::bfrstate (fgl::bfrmode :aignet) (1- (len bitarr))))
             (equal (len new-bitarr) (len bitarr)))
    :hints(("Goal" :in-theory (disable member remove
                                       fgl::bfr-listp$-when-subsetp-equal)
            :induct t)
           (and stable-under-simplificationp
                '(:expand ((remove-equal 0 (nthcdr n (nbalist-to-cube aignet-pathcond))))))))

  (defret length-of-<fn>-incr
    (>= (len new-bitarr) (len bitarr))
    :rule-classes :linear)

  (defret bfr-markedp-preserved-of-<fn>
    (implies (fgl::bfr-markedp y bitarr)
             (fgl::bfr-markedp y new-bitarr)))

  (defret bitarr-subsetp-of-<fn>
    (fgl::bitarr-subsetp bitarr new-bitarr)
    :hints(("Goal" :in-theory (enable fgl::bitarr-subsetp))))

  ;; (defret <fn>-preserves-invar
  ;;   (implies (fgl-object-mark-bfrs-invar seen bitarr)
  ;;            (fgl-object-mark-bfrs-invar new-seen new-bitarr)))

  (local (defthm nthcdr-of-gte
           (implies (and (<= (len x) (nfix n))
                         (true-listp x))
                    (equal (nthcdr n x) nil))))

  (local (defthmd nthcdr-n-expand
           (implies (< (nfix n) (len x))
                    (equal (nthcdr n x)
                           (cons (nth n x)
                                 (nthcdr n (cdr x)))))))


  (defret <fn>-marks-bfrs
    (fgl::bfrs-markedp (nthcdr n (nbalist-to-cube aignet-pathcond)) new-bitarr)
    :hints (("goal" :induct <call>)
            (and stable-under-simplificationp
                 '(:in-theory (enable nthcdr-n-expand))))))



(local
 #!fgl
 (def-updater-independence-thm bfrs-markedp-when-bitarr-subsetp
   (implies (and (bfrs-markedp x old)
                 (bitarr-subsetp old new))
            (bfrs-markedp x new))
   :hints ((acl2::witness))))

(define aignet-pathcond-mark-bfrs (aignet-pathcond
                                   bitarr)
  :guard (ec-call (bounded-pathcond-p aignet-pathcond (bits-length bitarr)))
  :returns new-bitarr
  (aignet-pathcond-mark-bfrs-aux 0 aignet-pathcond bitarr)
  ///
  (defret length-of-<fn>
    (implies (fgl::bfr-listp (remove 0 (nbalist-to-cube aignet-pathcond))
                             (fgl::bfrstate (fgl::bfrmode :aignet) (1- (len bitarr))))
             (equal (len new-bitarr) (len bitarr))))

  (defret length-of-<fn>-incr
    (>= (len new-bitarr) (len bitarr))
    :rule-classes :linear)

  (defret bfr-markedp-preserved-of-<fn>
    (implies (fgl::bfr-markedp y bitarr)
             (fgl::bfr-markedp y new-bitarr)))

  (defret bitarr-subsetp-of-<fn>
    (fgl::bitarr-subsetp bitarr new-bitarr)
    :hints(("Goal" :in-theory (enable fgl::bitarr-subsetp))))

  (defret bfrs-markedp-preserved-of-<fn>
    (implies (fgl::bfrs-markedp y bitarr)
             (fgl::bfrs-markedp y new-bitarr))
    :hints(("Goal" :in-theory (e/d ()
                                   (<fn>)))))

  (defret <fn>-marks-bfrs
    (fgl::bfrs-markedp (nbalist-to-cube aignet-pathcond) new-bitarr)
    :hints (("Goal" :use ((:instance aignet-pathcond-mark-bfrs-aux-marks-bfrs
                           (n 0)))
             :in-theory (disable aignet-pathcond-mark-bfrs-aux-marks-bfrs)))))
