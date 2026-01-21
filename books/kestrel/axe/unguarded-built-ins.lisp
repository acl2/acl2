; Versions of built-in functions with guards of t
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2025 Kestrel Institute
; Copyright (C) 2016-2020 Kestrel Technology, LLC
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; This book defines functions that are equivalent to ACL2 built-in functions
;; but have guards of t (for use in evaluators).

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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund nthcdr-unguarded (n l)
  (declare (xargs :guard t))
  (if (or (not (natp n))
          (<= n 0))
      l
    (if (consp l)
        (nthcdr-unguarded (+ n -1) (cdr l))
      nil)))

(defthm nthcdr-unguarded-correct
  (equal (nthcdr-unguarded n l)
         (nthcdr n l))
  :hints (("Goal" :in-theory (enable nthcdr-unguarded))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund take-unguarded (n lst)
  (declare (xargs :guard t))
  (if (true-listp lst)
      (take (nfix n) lst)
    (take (nfix n) (true-list-fix lst))))

(defthm take-unguarded-correct
  (equal (take-unguarded n lst)
         (take n lst))
  :hints (("Goal" :in-theory (enable take-unguarded take))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund eql-unguarded (x y)
  (declare (xargs :guard t))
  (equal x y))

(defthm eql-unguarded-correct
  (equal (eql-unguarded x y)
         (eql x y))
  :hints (("Goal" :in-theory (enable eql-unguarded eql))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund eq-unguarded (x y)
  (declare (xargs :guard t))
  (equal x y))

(defthm eq-unguarded-correct
  (equal (eq-unguarded x y)
         (eq x y))
  :hints (("Goal" :in-theory (enable eq-unguarded eq))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund member-equal-unguarded (x lst)
  (declare (xargs :guard t))
  (cond ((atom lst) nil)
        ((equal x (car lst)) lst)
        (t (member-equal-unguarded x (cdr lst)))))

(defthm member-equal-unguarded-correct
  (equal (member-equal-unguarded x y)
         (member-equal x y))
  :hints (("Goal" :in-theory (enable member-equal-unguarded member-equal))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund strip-cars-unguarded (x)
  (declare (xargs :guard t))
  (cond ((atom x) nil)
        (t (cons (car-unguarded (car-unguarded x))
                 (strip-cars-unguarded (cdr-unguarded x))))))

(defthm strip-cars-unguarded-correct
  (equal (strip-cars-unguarded x)
         (strip-cars x))
  :hints (("Goal" :in-theory (enable strip-cars-unguarded))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund strip-cdrs-unguarded (x)
  (declare (xargs :guard t))
  (cond ((atom x) nil)
        (t (cons (cdr-unguarded (car-unguarded x))
                 (strip-cdrs-unguarded (cdr-unguarded x))))))

(defthm strip-cdrs-unguarded-correct
  (equal (strip-cdrs-unguarded x)
         (strip-cdrs x))
  :hints (("Goal" :in-theory (enable strip-cdrs-unguarded))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund no-duplicatesp-equal-unguarded (l)
  (declare (xargs :guard t))
  (cond ((atom l) t)
        ((member-equal-unguarded (car l) (cdr l)) nil)
        (t (no-duplicatesp-equal-unguarded (cdr l)))))

(defthm no-duplicatesp-equal-unguarded-correct
  (equal (no-duplicatesp-equal-unguarded l)
         (no-duplicatesp-equal l))
  :hints (("Goal" :in-theory (enable no-duplicatesp-equal-unguarded
                                     no-duplicatesp-equal))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
