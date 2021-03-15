; MiMC Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Eric McCarthy (mccarthy@kestrel.edu)

(in-package "MIMC")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(include-book "kestrel/ethereum/semaphore/baby-jubjub-prime" :dir :system)

(include-book "mimcsponge")

(include-book "std/testing/assert-equal" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Field Prime
;; Used to supply arguments like  F_r - 1.

;; F_r is the order of the BN254 curve group, and
;; it is also the order of the field in which the BabyJubjub curve is defined.
;; This definition is just an alias for brevity.
(defund F_r ()
  (zksemaphore::baby-jubjub-prime))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Regression tests have been validated against Weijie Koh's copy of
;; mimcsponge.js.

(acl2::assert-equal
 (mimcsponge-semaphore 1 1 '(0))
 '(14543742788565021628577424853847564376151732847602780516906950225481254681152))
(acl2::assert-equal
 (mimcsponge-semaphore 1 1 '(100))
 '(5937383347670340356790482596018186675243707605339237148393421376818032413399))
(acl2::assert-equal
 (mimcsponge-semaphore 1 1 (list (- (F_r) 1)))
 '(15988839458591077582407698608992024557809304192191492261081585163915109842729))

(acl2::assert-equal
 (mimcsponge-semaphore 2 1 '(0 0))
 '(20636625426020718969131298365984859231982649550971729229988535915544421356929))
(acl2::assert-equal
 (mimcsponge-semaphore 2 1 '(3 7))
 '(10697433524604798991244515643013269995289226482009717983049256333491533830463))
(acl2::assert-equal
 (mimcsponge-semaphore 3 1 (list (- (F_r) 1) (- (F_r) 10) (- (F_r) 100)))
 '(3042651175468126521311143642888263941623419698127671987637482460844187992892))
(acl2::assert-equal
 (mimcsponge-semaphore 4 2 '(1 2 3 4))
 '(1767591491111054304950637348678561461191266274283762027709516319108521879132
   15037773584147449158705789226892568445769432872737236935657733009659386555457))

(acl2::assert-equal
 (mimcsponge-semaphore 5 1 '(1 2 3 4 0))
 '(15037773584147449158705789226892568445769432872737236935657733009659386555457))
(acl2::assert-equal
 (mimcsponge-semaphore 5 1 (list (- (F_r) 1) (- (F_r) 10) (- (F_r) 100) (- (F_r) 1000) (- (F_r) 10000)))
 '(17488744717604475499757358457785686401076949641727777576491131935346413354346))
