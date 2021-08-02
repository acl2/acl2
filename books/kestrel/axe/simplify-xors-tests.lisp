; Tests of simplify-xors
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

(include-book "simplify-xors")
(include-book "make-term-into-dag-array-basic")
(include-book "std/testing/assert-equal" :dir :system)

;(defmap aref1-list (array-name array indices) (aref1 array-name array indices) :fixed (array-name array))

;; Returns (list constant non-constant-terms-in-nest)
(defun bitxor-nest-leaves-of-term (term)
  (mv-let (erp nodenum-or-quotep dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
    (make-term-into-dag-array-basic term 'test-dag-array 'test-dag-parent-array nil ;interpreted-function-alist
                              )
    (declare (ignore dag-parent-array dag-constant-alist dag-variable-alist))
    (if erp
        (prog2$ (er hard? 'bitxor-nest-leaves-of-term "Error returned.")
                (list nil nil))
      (if (consp nodenum-or-quotep) ;test for quotep
          (list (unquote nodenum-or-quotep) nil)
        (mv-let (acc acc-constant)
          (bitxor-nest-leaves-aux (list nodenum-or-quotep) 'test-dag-array dag-array dag-len nil 0)
          (list acc-constant (dag-to-term-aux-lst-array 'test-dag-array dag-array acc)))))))

(assert-equal (bitxor-nest-leaves-of-term '(bitxor x y))
              '(0 (x y)))

(assert-equal (bitxor-nest-leaves-of-term '(bitxor x x))
              '(0 nil))

(assert-equal (bitxor-nest-leaves-of-term '(bitxor x (bitxor x y)))
              '(0 (y)))

(assert-equal (bitxor-nest-leaves-of-term '(bitxor x (bitxor y x)))
              '(0 (y)))

(assert-equal (bitxor-nest-leaves-of-term '(bitxor (foo x) (bitxor (foo x) (foo x))))
              '(0 ((foo x))))

(assert-equal (bitxor-nest-leaves-of-term '(bitxor x '1))
              '(1 (x)))

(assert-equal (bitxor-nest-leaves-of-term '(bitxor x '3))
              '(1 (x)))

(assert-equal (bitxor-nest-leaves-of-term '(bitxor x (bitxor y '3)))
              '(1 (x y)))

(assert-equal (bitxor-nest-leaves-of-term '(bitxor (bitxor (bitxor w '0) x) (bitxor (bitxor x '1) (bitxor y (bitxor y y)))))
              '(1 (W Y)))


;; ;; Tests of the newer implementation:

;; ;; Returns (list constant non-constant-terms-in-nest)
;; (defun bitxor-nest-leaves-of-term2 (term)
;;   (mv-let (erp nodenum-or-quotep dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
;;     (make-term-into-dag-array term 'test-dag-array 'test-dag-parent-array nil ;interpreted-function-alist
;;                               )
;;     (declare (ignore dag-len dag-parent-array dag-constant-alist dag-variable-alist))
;;     (if erp
;;         (prog2$ (er hard? 'bitxor-nest-leaves-of-term "Error returned.")
;;                 (list nil nil))

;;       (if (consp nodenum-or-quotep) ;test for quotep
;;           (list (unquote nodenum-or-quotep) nil)
;;         (mv-let (acc acc-constant)
;;           (bitxor-nest-leaves-for-node nodenum-or-quotep 'test-dag-array dag-array)
;;           (list acc-constant (dag-to-term-aux-lst-array 'test-dag-array dag-array acc)))))))

;; (assert-equal (bitxor-nest-leaves-of-term2 '(bitxor x y))
;;               '(0 (x y)))

;; (assert-equal (bitxor-nest-leaves-of-term2 '(bitxor x x))
;;               '(0 nil))

;; (assert-equal (bitxor-nest-leaves-of-term2 '(bitxor x (bitxor x y)))
;;               '(0 (y)))

;; (assert-equal (bitxor-nest-leaves-of-term2 '(bitxor x (bitxor y x)))
;;               '(0 (y)))

;; (assert-equal (bitxor-nest-leaves-of-term2 '(bitxor (foo x) (bitxor (foo x) (foo x))))
;;               '(0 ((foo x))))

;; (assert-equal (bitxor-nest-leaves-of-term2 '(bitxor x '1))
;;               '(1 (x)))

;; (assert-equal (bitxor-nest-leaves-of-term2 '(bitxor x '3))
;;               '(1 (x)))

;; (assert-equal (bitxor-nest-leaves-of-term2 '(bitxor x (bitxor y '3)))
;;               '(1 (x y)))

;; (assert-equal (bitxor-nest-leaves-of-term2 '(bitxor (bitxor (bitxor w '0) x) (bitxor (bitxor x '1) (bitxor y (bitxor y y)))))
;;               '(1 (W Y)))

(assert-equal (mv-let (erp dag-lst-or-quotep changep)
                (simplify-xors '((2 bvxor '64 1 0) (1 bvxor '32 0 0) (0 . y)) nil)
                (list erp dag-lst-or-quotep changep))
              (list (erp-nil)
                    '((1 BVCHOP '64 0) (0 . Y))
                    T))
