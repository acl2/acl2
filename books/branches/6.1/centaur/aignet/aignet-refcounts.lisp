; AIGNET - And-Inverter Graph Networks
; Copyright (C) 2013 Centaur Technology
;
; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/
;
; This program is free software; you can redistribute it and/or modify it under
; the terms of the GNU General Public License as published by the Free Software
; Foundation; either version 2 of the License, or (at your option) any later
; version.  This program is distributed in the hope that it will be useful but
; WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
; FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
; more details.  You should have received a copy of the GNU General Public
; License along with this program; if not, write to the Free Software
; Foundation, Inc., 51 Franklin Street, Suite 500, Boston, MA 02110-1335, USA.
;
; Original author: Sol Swords <sswords@centtech.com>

(in-package "AIGNET")

(include-book "aignet-base")

(local (include-book "arithmetic/top-with-meta" :dir :system))
(local (in-theory (enable* acl2::arith-equiv-forwarding)))

(local (in-theory (disable nth update-nth
                           acl2::nth-with-large-index
                           true-listp-update-nth)))

(defstobj-clone aignet-refcounts u32arr :suffix "-COUNTS")

(defsection aignet-refcounts

  (defun aignet-count-refs (n aignet-refcounts aignet)
    (declare (type (integer 0 *) n)
             (xargs :stobjs (aignet-refcounts aignet)
                    :guard (and (aignet-well-formedp aignet)
                                (u32arr-sizedp aignet-refcounts aignet)
                                (aignet-iterator-p n aignet))
                    :guard-debug t
                    :guard-hints ('(:do-not-induct t))
                    :measure (nfix (- (nfix (num-nodes aignet))
                                      (nfix n)))))
    (b* (((when (mbe :logic (zp (- (nfix (num-nodes aignet))
                                   (nfix n)))
                     :exec (int= n (num-nodes aignet))))
          aignet-refcounts)
         (id (to-id n))
         (aignet-refcounts
          (aignet-case
           (id->type id aignet)
           :gate  (b* ((id0 (lit-id (gate-id->fanin0 id aignet)))
                       (id1 (lit-id (gate-id->fanin1 id aignet)))
                       (aignet-refcounts
                        (set-id->nat id0 (+ 1 (get-id->nat id0 aignet-refcounts))
                                 aignet-refcounts)))
                    (set-id->nat id1 (+ 1 (get-id->nat id1 aignet-refcounts))
                             aignet-refcounts))
           :out (b* ((fid (lit-id (co-id->fanin id aignet))))
                  (set-id->nat fid (+ 1 (get-id->nat fid aignet-refcounts)) aignet-refcounts))
           :in aignet-refcounts
           :const aignet-refcounts))
         (aignet-refcounts (set-id->nat id 0 aignet-refcounts)))
      (aignet-count-refs (1+ (lnfix n)) aignet-refcounts aignet)))

  (defthm aignet-refcounts-well-sizedp-after-aignet-refcounts
    (implies (u32arr-sizedp aignet-refcounts aignet)
             (memo-tablep (aignet-count-refs n aignet-refcounts aignet) aignet))))
