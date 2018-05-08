; Copyright (C) 2004, Regents of the University of Texas
; Written by Sol Swords
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; Note: this book doesn't appear to be used anywhere.  Consider deleting it.
(in-package "ACL2")



(include-book "defset-macros")


(defun true-fun0 (x)
  (declare (xargs :guard t)
           (ignore x))
  t)

(defun true-fun1 (x p)
  (declare (xargs :guard t)
           (ignore x p))
  t)

(encapsulate
 (((defset-element-equiv * *) => *))
 (local (defun defset-element-equiv (a b)
          (declare (xargs :guard t))
          (equal a b)))
 (defequiv defset-element-equiv))


;; (encapsulate
;;  (((equiv * *) => *)
;;   ((elemp *) => *)
;;   ((elempp * *) => *)
;; ;;  ((binary-op * *) => *)
;;   )
;;  (local (defun elemp (x)
;;           (declare (xargs :guard t))
;;           (integerp x)))
;;  (local (defun elempp (x p)
;;           (declare (xargs :guard t))
;;           (and (integerp x)
;;                (integerp p)
;;                (< 0 x)
;;                (< p x))))
;;  (local (defun equiv (x y)
;;           (declare (xargs :guard (and (elemp x) (elemp y))))
;;           (= x y)))
;;  (local (defun binary-op (x y)
;;           (declare (xargs :guard (and (elemp x) (elemp y))))
;;           (+ x y)))
;;  (defequiv equiv)
;;  (defun ensure-guards-ok (x)
;;    (declare (xargs :guard (elemp x)))
;;    (equiv x x))
;; ;;  (defthm binary-op-elemp
;; ;;    (implies (and (elemp a) (elemp b))
;; ;;             (elemp (binary-op a b))))
;; ;;  (defthm binary-op-elempp
;; ;;    (implies (and (elempp a p) (elempp b p))
;; ;;             (elempp (binary-op a b) p)))
;;  (defcong equiv iff (elemp x) 1)
;;  (defcong equiv iff (elempp x p) 1))


(defun empty-guard (x)
  (declare (xargs :guard t)
           (ignore x))
  t)

(def-set-equiv defset-element-equiv :use-f-i nil
  :equiv-guard empty-guard)

;;(in-theory (disable defset-element-equiv-based-set-theory))

;; (def-set-equiv equal :prove-elem-congruences nil)

;; (defequiv =)

;; (def-set-equiv = :equiv-guard integerp)









(encapsulate
 (((deftypedset-element-p0 *) => *)
  ((deftypedset-element-equiv0 * *) => *))
 (local (defun deftypedset-element-p0 (x)
          (declare (xargs :guard t)
                   (ignore x))
          t))
 (local (defun deftypedset-element-equiv0 (a b)
          (declare (xargs :guard t))
          (equal a b)))
 (defequiv deftypedset-element-equiv0)
 (defcong deftypedset-element-equiv0 iff (deftypedset-element-p0 x) 1))

(def-set-equiv deftypedset-element-equiv0)

(def-typed-set deftypedset-element-p0 deftypedset-set-type-0
  :equiv deftypedset-element-equiv0 :use-f-i nil)


(encapsulate
 (((deftypedset-element-p1 * *) => *)
  ((deftypedset-element-equiv1 * *) => *))
 (local (defun deftypedset-element-p1 (x p)
          (declare (xargs :guard t)
                   (ignore x p))
          t))
 (local (defun deftypedset-element-equiv1 (a b)
          (declare (xargs :guard t))
          (equal a b)))
 (defequiv deftypedset-element-equiv1)
 (defcong deftypedset-element-equiv1 iff (deftypedset-element-p1 x p) 1))

(def-set-equiv deftypedset-element-equiv1)

(def-typed-set deftypedset-element-p1 deftypedset-set-type-1
  :equiv deftypedset-element-equiv1 :additional-param t :use-f-i nil)

;; (in-theory (disable deftypedset-element-equiv-based-set-theory ||#
;;                     deftypedset-set-type-0-typed-set-theory ||#
;;                     deftypedset-set-type-1-typed-set-theory)) ||#

;; (def-typed-set integerp intset :equiv =)

;; (defun lessp (x p)
;; (declare (xargs :guard t))
;; (and (rationalp x)
;;      (rationalp p)
;;      (< x p)))

;; (def-typed-set lessp less-than-r-set :additional-param t)














(encapsulate
 (((set-union-op-equiv0 * *) => *))
 (local (defun set-union-op-equiv0 (x y)
          (declare (xargs :guard t))
          (equal x y)))
 (defequiv set-union-op-equiv0))

(encapsulate
 (((set-union-op-f0 *) => *)
  ((elt-guard0 *) => *)
  ((bad-input-fn0) => *))
 (local (defun set-union-op-f0 (x) (declare (ignore x)) nil))
 (local (defun elt-guard0 (x) (declare (ignore x)) t))
 (local (defun bad-input-fn0 () nil))
 (def-set-equiv set-union-op-equiv0)
 (defcong set-union-op-equiv0 set-equiv-set-union-op-equiv0
   (set-union-op-f0 x) 1)
 (defcong set-union-op-equiv0 iff (elt-guard0 x) 1))



(def-typed-set elt-guard0 guard0-ok :equiv set-union-op-equiv0)

(prove-set-congruence-of-f set-union-op-f0 :use-f-i nil
                           :equiv set-union-op-equiv0
                           :elem-guard elt-guard0
                           :set-guard guard0-okp
                           :bad-input-fn bad-input-fn0
                           )

(encapsulate
 (((set-union-op-equiv1 * *) => *))
 (local (defun set-union-op-equiv1 (x y)
          (declare (xargs :guard t))
          (equal x y)))
 (defequiv set-union-op-equiv1))

(encapsulate
 (((set-union-op-f1 * *) => *)
  ((elt-guard1 * *) => *)
  ((bad-input-fn1) => *))
 (local (defun set-union-op-f1 (x p)
          (declare (ignore x p))
          nil))
 (local (defun elt-guard1 (x p) (declare (ignore x p)) t))
 (local (defun bad-input-fn1 () nil))
 (def-set-equiv set-union-op-equiv1)
 (defcong set-union-op-equiv1 set-equiv-set-union-op-equiv1
   (set-union-op-f1 x p) 1)
 (defcong set-union-op-equiv1 iff (elt-guard1 x p) 1))


(def-typed-set elt-guard1 guard1-ok :equiv set-union-op-equiv1
  :additional-param t)



(prove-set-congruence-of-f set-union-op-f1
                           :use-f-i nil
                           :additional-param t
                           :equiv set-union-op-equiv1
                           :elem-guard elt-guard1
                           :set-guard guard1-okp
                           :bad-input-fn bad-input-fn1)


