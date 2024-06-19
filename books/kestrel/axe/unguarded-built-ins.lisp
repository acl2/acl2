; Versions of built-in functions with guards of t
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2022 Kestrel Institute
; Copyright (C) 2016-2020 Kestrel Technology, LLC
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; This book defines functions that are equivalent to ACL2 built-in functions
;; but have guards of t (for use in evaluators).

;; Disable certification of this book in ACL2(r), due to differences in FLOOR:
; cert_param: (non-acl2r)

(include-book "unguarded-primitives")
(include-book "kestrel/arithmetic-light/unguarded-built-ins" :dir :system)

(defund mv-nth-unguarded (n x)
  (declare (xargs :guard t))
  (mv-nth (nfix n) x))

;supports the correctness of the evaluator
(defthm mv-nth-unguarded-correct
  (equal (mv-nth-unguarded n x)
         (mv-nth n x))
  :hints (("Goal" :in-theory (enable mv-nth
                                     mv-nth-unguarded))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund assoc-equal-unguarded (x alist)
  (declare (xargs :guard t))
  (cond ((atom alist) nil)
        ((equal x (car-unguarded (car-unguarded alist)))
         (car-unguarded alist))
        (t (assoc-equal-unguarded x (cdr-unguarded alist)))))

(defthm assoc-equal-unguarded-correct
  (equal (assoc-equal-unguarded x alist)
         (assoc-equal x alist))
  :hints (("Goal" :in-theory (enable assoc-equal
                                     assoc-equal-unguarded))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund symbol<-unguarded (x y)
  (declare (xargs :guard t))
  (let ((x1 (if (symbolp x) (symbol-name x) ""))
        (y1 (if (symbolp y) (symbol-name y) "")))
       (or (string< x1 y1)
           (and (equal x1 y1)
                (string< (if (symbolp x) (symbol-package-name x) "")
                         (if (symbolp y) (symbol-package-name y) ""))))))

(defthm symbol<-unguarded-correct
  (equal (symbol<-unguarded x y)
         (symbol< x y))
  :hints (("Goal" :in-theory (enable symbol<-unguarded symbol<))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund endp-unguarded (x)
  (declare (xargs :guard t))
  (atom x))

(defthm endp-unguarded-correct
  (equal (endp-unguarded x)
         (endp x)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; ;; We don't want to evaluate calls to return-last, because that will naturally evaluate the eager arg
;; (defund return-last-unguarded (fn eager-arg last-arg)
;;   (declare (xargs :guard t)
;;            (ignore fn eager-arg))
;;   last-arg)

;; (defthm return-last-unguarded-correct
;;   (equal (return-last-unguarded fn eager-arg last-arg)
;;          (return-last fn eager-arg last-arg))
;;   :hints (("Goal" :in-theory (enable return-last
;;                                      return-last-unguarded))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;no true-listp guard
(defund nth-unguarded-aux (n l)
  (declare (xargs :guard (natp n)
                  :split-types t)
           (type (integer 0 *) n) ; could even restrict to a fixtype
           )
  (if (atom l)
      nil
    (if (mbe :logic (zp n) :exec (= 0 n))
        (car l)
      (nth-unguarded-aux (- n 1) (cdr l)))))

(defund nth-unguarded (n l)
  (declare (xargs :guard t))
  (nth-unguarded-aux (nfix n) l))

(defthm nth-unguarded-correct
  (equal (nth-unguarded n l)
         (nth n l))
  :hints (("Goal" :in-theory (enable nth nth-unguarded nth-unguarded-aux))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund binary-append-unguarded (x y)
  (declare (xargs :guard t))
  (if (true-listp x)
      (append x y)
    (append (true-list-fix x) y)))

(defthm binary-append-unguarded-correct
  (equal (binary-append-unguarded x y)
         (binary-append x y))
  :hints (("Goal" :in-theory (enable binary-append-unguarded))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund acons-unguarded (key datum alist)
  (declare (xargs :guard t))
  (cons (cons key datum) alist))

(defthm acons-unguarded-correct
  (equal (acons-unguarded key datum alist)
         (acons key datum alist))
  :hints (("Goal" :in-theory (enable acons-unguarded))))
