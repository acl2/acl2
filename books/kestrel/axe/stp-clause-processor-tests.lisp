; Tests of the STP clause processor
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2020 Kestrel Institute
; Copyright (C) 2016-2020 Kestrel Technology, LLC
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "stp-clause-processor")

;; ;full syntax for the :clause-processor hint:
;; (defthm stp-clause-processor-test-0
;;   (not (not (equal (bvplus 32 x y) (bvplus 32 y x))))
;;   :hints (("Goal" :in-theory nil :clause-processor (stp-clause-processor clause nil state))))

;; ;short syntax for the :clause-processor hint:
;; (defthm stp-clause-processor-test-0b
;;   (not (not (equal (bvplus 32 x y) (bvplus 32 y x))))
;;   :hints (("Goal" :in-theory nil :clause-processor stp-clause-processor)))

;; ;; (defthm mytest
;; ;;   (not (not (equal (bvplus 33 x y) (bvplus 32 z x))))
;; ;;   :hints (("Goal" :in-theory nil :clause-processor (stp-clause-processor clause nil state))))

;; (defthm-with-stp-clause-processor stp-clause-processor-test-1
;;   (equal (bvplus 32 x y)
;;          (bvplus 32 y x)))

;; ; Same as above but with double negation added
;; (defthm-with-stp-clause-processor stp-clause-processor-test-2
;;   (not (not (equal (bvplus 32 x y)
;;                    (bvplus 32 y x)))))

;; ;; (defthm-with-stp-clause-processor mytest (not (not (equal (bvplus 32 x y) (bvplus 33 y x)))))

;; ;; (defthm mytest
;; ;;   (implies (equal 0 x) (equal (bvplus 32 x 0) 0))
;; ;;   :hints (("Goal" :clause-processor (stp-clause-processor clause nil state))))
