; ACL2 Version 8.4 -- A Computational Logic for Applicative Common Lisp
; Copyright (C) 2019, Regents of the University of Texas

; Events in this file are also in community book
; books/system/apply/loop-scions.lisp, but with defun$ in place of defun in
; that book.  The definitions are derived from the ACL2 sources.  We need the
; present book to support the verification of termination and guards for
; apply$-prim in #+acl2-devel executables.

(in-package "ACL2")

#+acl2-devel ; else not redundant
(defun tails-ac (lst ac)
  (declare (xargs :guard (and (true-listp lst)
                              (true-listp ac))))
  (cond ((endp lst) (revappend ac nil))
        (t (tails-ac (cdr lst) (cons lst ac)))))

#+acl2-devel ; else not redundant
(defun tails (lst)
  (declare (xargs :guard (true-listp lst)
                  :verify-guards nil))
  (mbe :logic
       (cond ((endp lst) nil)
             (t (cons lst (tails (cdr lst)))))
       :exec (tails-ac lst nil)))

(defthm tails-ac=tails
  (equal (tails-ac lst ac)
         (revappend ac (tails lst))))

(verify-guards tails)

; -----------------------------------------------------------------
; Loop$-as and Its Tail Recursive Counterpart

#+acl2-devel ; else not redundant
(defun empty-loop$-as-tuplep (tuple)
  (declare (xargs :guard (true-list-listp tuple)))
  (cond ((endp tuple) nil)
        ((endp (car tuple)) t)
        (t (empty-loop$-as-tuplep (cdr tuple)))))

#+acl2-devel ; else not redundant
(defun car-loop$-as-tuple (tuple)
  (declare (xargs :guard (true-list-listp tuple)))
  (cond ((endp tuple) nil)
        (t (cons (caar tuple) (car-loop$-as-tuple (cdr tuple))))))

#+acl2-devel ; else not redundant
(defun cdr-loop$-as-tuple (tuple)
  (declare (xargs :guard (true-list-listp tuple)))
  (cond ((endp tuple) nil)
        (t (cons (cdar tuple) (cdr-loop$-as-tuple (cdr tuple))))))

#+acl2-devel ; else not redundant
(defun loop$-as-ac (tuple ac)
  (declare (xargs :guard (and (true-list-listp tuple)
                              (true-listp ac))))
  (cond ((endp tuple) (revappend ac nil))
        ((empty-loop$-as-tuplep tuple) (revappend ac nil))
        (t (loop$-as-ac (cdr-loop$-as-tuple tuple)
                        (cons (car-loop$-as-tuple tuple)
                              ac)))))

#+acl2-devel ; else not redundant
(defun loop$-as (tuple)
  (declare (xargs :guard (true-list-listp tuple)
                  :verify-guards nil))
  (mbe :logic
       (cond ((endp tuple) nil)
             ((empty-loop$-as-tuplep tuple) nil)
             (t (cons (car-loop$-as-tuple tuple)
                      (loop$-as (cdr-loop$-as-tuple tuple)))))
       :exec
       (loop$-as-ac tuple nil)))

(defthm loop$-as-ac=loop$-as
  (equal (loop$-as-ac tuple ac)
         (revappend ac (loop$-as tuple))))

(verify-guards loop$-as)

; -----------------------------------------------------------------
; From-to-by and Its Tail Recursive Counterpart

(defun from-to-by-measure (i j)
  (if (and (integerp i)
           (integerp j)
           (<= i j))
      (+ 1 (- j i))
      0))

(defthm natp-from-to-by-measure
  (natp (from-to-by-measure i j))
  :rule-classes :type-prescription)

#+acl2-devel ; else not redundant
(defun from-to-by-ac (i j k ac)
  (declare (xargs :guard (and (integerp i)
                              (integerp j)
                              (integerp k)
                              (< 0 k)
                              (true-listp ac))
                  :measure (from-to-by-measure i j)))
  (cond ((mbt (and (integerp i)
                   (integerp j)
                   (integerp k)
                   (< 0 k)))
         (cond
          ((<= i j)
           (from-to-by-ac i (- j k) k (cons j ac)))
          (t ac)))
        (t nil)))

(defthm natp-from-to-by-measure
  (natp (from-to-by-measure i j))
  :rule-classes :type-prescription)

#+acl2-devel ; else not redundant
(defun from-to-by (i j k)
  (declare (xargs :guard (and (integerp i)
                              (integerp j)
                              (integerp k)
                              (< 0 k))
                  :measure (from-to-by-measure i j)
                  :verify-guards nil))
  (mbe :logic
       (cond ((mbt (and (integerp i)
                        (integerp j)
                        (integerp k)
                        (< 0 k)))
              (cond
               ((<= i j)
                (cons i (from-to-by (+ i k) j k)))
               (t nil)))
             (t nil))
       :exec (if (< j i)
                 nil
                 (from-to-by-ac i (+ i (* k (floor (- j i) k))) k nil))))

; But establishing the equivalence of the :logic and :exec branches under the
; guard is actually pretty subtle so we do it in the following encapsulate.
#+acl2-devel
(encapsulate
  nil

  #+acl2-devel  ;; for build machinery
  (local (include-book "arithmetic-5/top" :dir :system))

  (local
   (defthm alt-def-from-to-by
     (equal (from-to-by i j k)
            (cond ((and (integerp i)
                        (integerp j)
                        (integerp k)
                        (< 0 k))

                   (cond
                    ((<= i j)
                     (append (from-to-by i (- j k) k)
                             (list (+ i (* k (floor (- j i) k))))))
                    (t nil)))
                  (t nil)))
     :rule-classes ((:definition))))

  (local
   (defthm assoc-append
     (equal (append (append a b) c)
            (append a (append b c)))))

  (local
   (defthm len-append
     (equal (len (append a b)) (+ (len a) (len b)))))

  (local
   (defthm equal-len-0
     (equal (equal (len x) 0) (not (consp x)))))

  (local
   (defthm equal-lst-append-x-lst
     (iff (equal lst (append x lst))
          (not (consp x)))
     :hints (("Subgoal 1"
              :use (:instance (:theorem (implies (not (equal (len x) (len y)))
                                                 (not (equal x y))))
                              (x lst)
                              (y (append x lst)))))))

  (local
   (defthm consp-from-to-by
     (equal (consp (from-to-by i j k))
            (and (integerp i)
                 (integerp j)
                 (integerp k)
                 (< 0 k)
                 (<= i j)))))

  (local
   (defun alt-def-from-to-by-recursion (i j k lst)
     (declare (xargs :measure (from-to-by-measure i j)))
     (cond ((and (integerp i)
                 (integerp j)
                 (integerp k)
                 (< 0 k))

            (cond
             ((<= i j)
              (alt-def-from-to-by-recursion
               i (- j k) k (cons (+ i (* k (floor (- j i) k))) lst)))
             (t lst)))
           (t nil))))  

  (local
   (defthm from-to-by-ac-i-i
     (equal (from-to-by-ac i i k lst)
            (if (and (integerp i)
                     (integerp k)
                     (< 0 k))
                (cons i lst)
                nil))
     :hints (("Goal" :expand ((from-to-by-ac i i k lst))))))

  (local
   (defthm from-to-by-normalizer
     (implies (and (integerp i)
                   (integerp j)
                   (integerp k)
                   (< 0 k))
              (equal (from-to-by i j k)
                     (if (< j i)
                         nil
                         (from-to-by i (- j (mod (- j i) k)) k))))
     :rule-classes nil
     :hints (("Goal"
              :in-theory (disable from-to-by)
              :induct (alt-def-from-to-by-recursion i j k xxx)))))

  (local
   (defthm from-to-by-ac=from-to-by-lemma
     (implies (and (integerp i)
                   (integerp j)
                   (integerp k)
                   (< 0 k)
                   (equal (mod (- j i) k) 0))
              (equal (append (from-to-by i j k) lst)
                     (if (< j i)
                         lst
                         (from-to-by-ac i j k lst))))
     :rule-classes nil
     :hints (("Goal" :in-theory (disable from-to-by)
              :induct (alt-def-from-to-by-recursion i j k lst)))))

  (local
   (defthm from-to-by-ac=from-to-by
     (implies (and (integerp i)
                   (integerp j)
                   (integerp k)
                   (< 0 k))
              (equal (append (from-to-by i j k) lst)
                     (if (< j i)
                         lst
                         (from-to-by-ac i (+ i (* k (floor (- j i) k))) k
                                        lst))))
     :rule-classes nil
     :hints (("Goal" :in-theory (disable from-to-by)
              :use (from-to-by-normalizer
                    (:instance from-to-by-ac=from-to-by-lemma
                               (j (+ j (- (mod (+ j (- i)) k))))))))))

  (local
   (defthm append-nil
     (implies (true-listp x)
              (equal (append x nil) x))))

  (defthm from-to-by-ac=from-to-by-special-case
    (implies (and (integerp i)
                  (integerp j)
                  (integerp k)
                  (< 0 k)
                  (<= i j))
             (equal (from-to-by-ac i (+ i (* k (floor (- j i) k))) k nil)
                    (from-to-by i j k)))
    :hints (("Goal" :use (:instance from-to-by-ac=from-to-by
                                    (lst nil)))))
  )

(verify-guards from-to-by
  :hints (("Goal" :in-theory (disable floor)
                  :use from-to-by-ac=from-to-by-special-case)))

#+acl2-devel ; else not redundant
(defun revappend-true-list-fix (x ac)
  (declare (xargs :guard t))
  (if (atom x)
      ac
      (revappend-true-list-fix (cdr x) (cons (car x) ac))))

#+acl2-devel
(include-book "../top") ; includes ../meta-extract

#+acl2-devel
(verify-termination apply$-prim) ; and guards
