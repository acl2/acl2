;;
;; Copyright (C) 2023, Collins Aerospace
;; All rights reserved.
;;
;; This software may be modified and distributed under the terms
;; of the 3-clause BSD license.  See the LICENSE file for details.
;;
(in-package "ACL2")

(include-book "dpss")

(def::un UAV->LP-equiv (x y)
  (declare (xargs :fty ((uav uav) bool)))
  (equal (UAV->LP x)
         (UAV->LP y)))

(defequiv UAV->LP-equiv)

(defcong UAV->LP-equiv equal (UAV->LP x) 1)

(def::un UAV->LC-equiv (x y)
  (declare (xargs :fty ((uav uav) bool)))
  (equal (UAV->LC x)
         (UAV->LC y)))

(defequiv UAV->LC-equiv)

(defcong UAV->LC-equiv equal (UAV->LC x) 1)

(def::un UAV->xx-equiv (x y)
  (declare (xargs :fty ((uav uav) bool)))
  (equal (UAV->xx x)
         (UAV->xx y)))

(defequiv UAV->xx-equiv)

(defcong UAV->xx-equiv equal (UAV->xx x) 1)

(def::un UAV->dx-equiv (x y)
  (declare (xargs :fty ((uav uav) bool)))
  (equal (UAV->dx x)
         (UAV->dx y)))

(defequiv UAV->dx-equiv)

(defcong UAV->dx-equiv equal (UAV->dx x) 1)

(def::un UAV->RC-equiv (x y)
  (declare (xargs :fty ((uav uav) bool)))
  (equal (UAV->RC x)
         (UAV->RC y)))

(defequiv UAV->RC-equiv)

(defcong UAV->RC-equiv equal (UAV->RC x) 1)

(def::un UAV->RP-equiv (x y)
  (declare (xargs :fty ((uav uav) bool)))
  (equal (UAV->RP x)
         (UAV->RP y)))

(defequiv UAV->RP-equiv)

(defcong UAV->RP-equiv equal (UAV->RP x) 1)

(defthmd UAV-equiv-extensionality-2
  (iff (UAV-equiv x y)
       (and (UAV->LP-equiv x y)
            (UAV->LC-equiv x y)
            (UAV->xx-equiv x y)
            (UAV->dx-equiv x y)
            (UAV->RC-equiv x y)
            (UAV->RP-equiv x y)))
  :hints (("Goal" :in-theory (enable UAV-EXTENSIONALITY))))

;; (in-theory
;;  (disable
;;   UAV->LP-equiv
;;   UAV->LC-equiv
;;   UAV->xx-equiv
;;   UAV->dx-equiv
;;   UAV->RC-equiv
;;   UAV->RP-equiv
;;   ))

(local (in-theory (enable UAV-equiv-extensionality-2)))
   
(defrefinement UAV-equiv UAV->LP-equiv)
(defrefinement UAV-equiv UAV->LC-equiv)
(defrefinement UAV-equiv UAV->dx-equiv)
(defrefinement UAV-equiv UAV->xx-equiv)
(defrefinement UAV-equiv UAV->RC-equiv)
(defrefinement UAV-equiv UAV->RP-equiv)

;; (def::un set-LP (LP uav)
;;   (declare (xargs :fty ((rational uav) uav)))
;;   (change-uav uav :LP LP))

;; (def::un set-L (L uav)
;;   (declare (xargs :fty ((nat uav) uav)))
;;   (change-uav uav :L L))

;; (def::un set-x (x uav)
;;   (declare (xargs :fty ((rational uav) uav)))
;;   (change-uav uav :x x))

;; (def::un set-dx (dx uav)
;;   (declare (xargs :fty ((sign uav) uav)))
;;   (change-uav uav :dx dx))

;; (def::un set-R (R uav)
;;   (declare (xargs :fty ((nat uav) uav)))
;;   (change-uav uav :R R))

;; (def::un set-RP (RP uav)
;;   (declare (xargs :fty ((rational uav) uav)))
;;   (change-uav uav :RP RP))


(def::un UAV->LP-def-equiv (x y)
  (declare (xargs :fty ((uav uav) bool)))
  (and (UAV->LC-equiv x y)
       (UAV->xx-equiv x y)
       (UAV->dx-equiv x y)
       (UAV->RC-equiv x y)
       (UAV->RP-equiv x y)
       ))

(defequiv UAV->LP-def-equiv)

(defrefinement UAV-equiv UAV->LP-def-equiv)

;; (defthm def-LP-set-LP
;;   (UAV->LP-def-equiv (set-LP LP uav) uav))

(def::un UAV->LC-def-equiv (x y)
  (declare (xargs :fty ((uav uav) bool)))
  (and (UAV->LP-equiv x y)
       (UAV->xx-equiv x y)
       (UAV->dx-equiv x y)
       (UAV->RC-equiv x y)
       (UAV->RP-equiv x y)
       ))

(defequiv UAV->LC-def-equiv)

(defrefinement UAV-equiv UAV->LC-def-equiv)

(def::un UAV->xx-def-equiv (x y)
  (declare (xargs :fty ((uav uav) bool)))
  (and (UAV->LP-equiv x y)
       (UAV->LC-equiv x y)
       (UAV->dx-equiv x y)
       (UAV->RC-equiv x y)
       (UAV->RP-equiv x y)
       ))

(defequiv UAV->xx-def-equiv)

(defrefinement UAV-equiv UAV->xx-def-equiv)

(def::un UAV->dx-def-equiv (x y)
  (declare (xargs :fty ((uav uav) bool)))
  (and (UAV->LP-equiv x y)
       (UAV->LC-equiv x y)
       (UAV->xx-equiv x y)
       (UAV->RC-equiv x y)
       (UAV->RP-equiv x y)
       ))

(defequiv UAV->dx-def-equiv)

(defrefinement UAV-equiv UAV->dx-def-equiv)

(def::un UAV->RC-def-equiv (x y)
  (declare (xargs :fty ((uav uav) bool)))
  (and (UAV->LP-equiv x y)
       (UAV->LC-equiv x y)
       (UAV->xx-equiv x y)
       (UAV->dx-equiv x y)
       (UAV->RP-equiv x y)
       ))

(defequiv UAV->RC-def-equiv)

(defrefinement UAV-equiv UAV->RC-def-equiv)

(def::un UAV->RP-def-equiv (x y)
  (declare (xargs :fty ((uav uav) bool)))
  (and (UAV->LP-equiv x y)
       (UAV->LC-equiv x y)
       (UAV->xx-equiv x y)
       (UAV->dx-equiv x y)
       (UAV->RC-equiv x y)
       ))

(defequiv UAV->RP-def-equiv)

(defrefinement UAV-equiv UAV->RP-def-equiv)

;; (defcong UAV->RP-def-equiv UAV-equiv (set-RP RP uav) 2)
;; (defcong UAV->RC-def-equiv UAV-equiv (set-R  R  uav) 2)
;; (defcong UAV->xx-def-equiv UAV-equiv (set-x  x  uav) 2)
;; (defcong UAV->dx-def-equiv UAV-equiv (set-dx dx uav) 2)
;; (defcong UAV->LC-def-equiv UAV-equiv (set-L  L  uav) 2)
;; (defcong UAV->LP-def-equiv UAV-equiv (set-LP LP uav) 2)

;; ;;(defcong UAV->LP-def-equiv UAV->LP-def-equiv (set-LP LP  uav) 2)
;; (defcong UAV->LP-def-equiv UAV->LP-def-equiv (set-L  L   uav) 2)
;; (defcong UAV->LP-def-equiv UAV->LP-def-equiv (set-x  x   uav) 2)
;; (defcong UAV->LP-def-equiv UAV->LP-def-equiv (set-dx dx  uav) 2)
;; (defcong UAV->LP-def-equiv UAV->LP-def-equiv (set-R  R   uav) 2)
;; (defcong UAV->LP-def-equiv UAV->LP-def-equiv (set-RP RP  uav) 2)

;; (defcong UAV->LC-def-equiv UAV->LC-def-equiv (set-LP LP  uav) 2)
;; ;;(defcong UAV->LC-def-equiv UAV->LC-def-equiv (set-L  L   uav) 2)
;; (defcong UAV->LC-def-equiv UAV->LC-def-equiv (set-x  x   uav) 2)
;; (defcong UAV->LC-def-equiv UAV->LC-def-equiv (set-dx dx  uav) 2)
;; (defcong UAV->LC-def-equiv UAV->LC-def-equiv (set-R  R   uav) 2)
;; (defcong UAV->LC-def-equiv UAV->LC-def-equiv (set-RP RP  uav) 2)

;; (defcong UAV->xx-def-equiv UAV->xx-def-equiv (set-LP LP  uav) 2)
;; (defcong UAV->xx-def-equiv UAV->xx-def-equiv (set-L  L   uav) 2)
;; ;;(defcong UAV->xx-def-equiv UAV->xx-def-equiv (set-x  x   uav) 2)
;; (defcong UAV->xx-def-equiv UAV->xx-def-equiv (set-dx dx  uav) 2)
;; (defcong UAV->xx-def-equiv UAV->xx-def-equiv (set-R  R   uav) 2)
;; (defcong UAV->xx-def-equiv UAV->xx-def-equiv (set-RP RP  uav) 2)

;; (defcong UAV->dx-def-equiv UAV->dx-def-equiv (set-LP LP  uav) 2)
;; (defcong UAV->dx-def-equiv UAV->dx-def-equiv (set-L  L   uav) 2)
;; (defcong UAV->dx-def-equiv UAV->dx-def-equiv (set-x  x   uav) 2)
;; ;;(defcong UAV->dx-def-equiv UAV->dx-def-equiv (set-dx dx  uav) 2)
;; (defcong UAV->dx-def-equiv UAV->dx-def-equiv (set-R  R   uav) 2)
;; (defcong UAV->dx-def-equiv UAV->dx-def-equiv (set-RP RP  uav) 2)

;; (defcong UAV->RP-def-equiv UAV->RP-def-equiv (set-LP LP  uav) 2)
;; (defcong UAV->RP-def-equiv UAV->RP-def-equiv (set-L  L   uav) 2)
;; (defcong UAV->RP-def-equiv UAV->RP-def-equiv (set-x  x   uav) 2)
;; (defcong UAV->RP-def-equiv UAV->RP-def-equiv (set-dx dx  uav) 2)
;; (defcong UAV->RP-def-equiv UAV->RP-def-equiv (set-R  R   uav) 2)
;; ;;(defcong UAV->RP-def-equiv UAV->RP-def-equiv (set-RP RP  uav) 2)

;; (defcong UAV->RC-def-equiv UAV->RC-def-equiv (set-LP LP  uav) 2)
;; (defcong UAV->RC-def-equiv UAV->RC-def-equiv (set-L  L   uav) 2)
;; (defcong UAV->RC-def-equiv UAV->RC-def-equiv (set-x  x   uav) 2)
;; (defcong UAV->RC-def-equiv UAV->RC-def-equiv (set-dx dx  uav) 2)
;; ;;(defcong UAV->RC-def-equiv UAV->RC-def-equiv (set-R  R   uav) 2)
;; (defcong UAV->RC-def-equiv UAV->RC-def-equiv (set-RP RP  uav) 2)

;; dag

;; (in-theory (disable SET-DX set-l set-pl set-R set-RP))

;; (in-theory (disable UAV-EQUIV-EXTENSIONALITY-2))

;; (defthm test-1
;;   (UAV-equiv (set-RP RP1 (set-R R (set-RP RP2 (set-dx dx (set-RP RP2 (set-R R2 (set-LP LP (set-RP RP2 (set-L L uav)))))))))
;;              (set-RP RP1 (set-R R (set-dx dx (set-LP LP (set-L L uav)))))))

;; ;; For every function you add you need to add non-interference
;; ;; rules.

;; (def::un foo (x)
;;   (declare (xargs :fty ((uav) uav)))
;;   (set-x 0 (set-dx 1 (set-LP (+ (UAV->xx x) (UAV->RP x)) x))))

;; ;; Get the ball rolling ..
;; ;;
;; ;; Any fields that are always defined by the function can be
;; ;; ignored in its argument unless they are also used ..

;; (defcong UAV->LP-def-equiv UAV-equiv (foo x) 1)
;; (defcong UAV->dx-def-equiv UAV-equiv (foo x) 1)

;; ;; Keep the ball rolling ..
;; ;; Any field that is unused by the function ..
;; ;;

;; (defcong UAV->LP-def-equiv UAV->LP-def-equiv (foo x) 1)
;; (defcong UAV->LC-def-equiv  UAV->LC-def-equiv  (foo x) 1)
;; (defcong UAV->dx-def-equiv UAV->dx-def-equiv (foo x) 1)
;; (defcong UAV->RC-def-equiv  UAV->RC-def-equiv  (foo x) 1)
;; ;; We use both of these ..
;; ;;(defcong UAV-equiv UAV->xx-def-equiv  (foo x) 1)
;; ;;(defcong UAV-equiv UAV->RP-def-equiv (foo x) 1)

;; ;; Any field that is always undefined ..
;; ;;(defthm UAV->LC-equiv-foo  (UAV->LC-equiv  (foo x) x))
;; (defthm UAV->LC-equiv-foo  (UAV->LC-equiv  (foo x) x))
;; ;(defthm UAV->xx-equiv-foo  (UAV->xx-equiv  (foo x) x))
;; ;(defthm UAV->dx-equiv-foo (UAV->dx-equiv (foo x) x))
;; (defthm UAV->RC-equiv-foo  (UAV->RC-equiv  (foo x) x))
;; (defthm UAV->RP-equiv-foo (UAV->RP-equiv (foo x) x))

;; dag


;; (encapsulate
;;     ()
;;   (local
;;    (in-theory (disable
;;                UAV->LP-equiv
;;                UAV->LC-equiv
;;                UAV->xx-equiv
;;                UAV->dx-equiv
;;                UAV->RC-equiv
;;                UAV->RP-equiv
;;                )))
   
;;    (local (in-theory (enable UAV-equiv-extensionality-2)))
   
;;    (defrefinement UAV-equiv UAV->LP-def-equiv)
;;    (defrefinement UAV-equiv UAV->LC-def-equiv)
;;    (defrefinement UAV-equiv UAV->dx-def-equiv)
;;    (defrefinement UAV-equiv UAV->xx-def-equiv)
;;    (defrefinement UAV-equiv UAV->RC-def-equiv)
;;    (defrefinement UAV-equiv UAV->RP-def-equiv)

;;    )

;; (def::un LP-def-equiv (x y)
;;   (and (equal 

;; (def::un LP-def-equiv (x y)
;;   (and (equal 

;; (def::un LP-def-equiv (x y)
;;   (and (equal 

;; (def::un LP-def-equiv (x y)
;;   (and (equal 

