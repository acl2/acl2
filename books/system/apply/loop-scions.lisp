; ACL2 Version 8.1 -- A Computational Logic for Applicative Common Lisp
; Copyright (C) 2019, Regents of the University of Texas

; This version of ACL2 is a descendent of ACL2 Version 1.9, Copyright
; (C) 1997 Computational Logic, Inc.  See the documentation topic NOTE-2-0.

; This program is free software; you can redistribute it and/or modify
; it under the terms of the LICENSE file distributed with ACL2.

; This program is distributed in the hope that it will be useful,
; but WITHOUT ANY WARRANTY; without even the implied warranty of
; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
; LICENSE for more details.

; Written by:  Matt Kaufmann               and J Strother Moore
; email:       Kaufmann@cs.utexas.edu      and Moore@cs.utexas.edu
; Department of Computer Science
; University of Texas at Austin
; Austin, TX 78712 U.S.A.

; Many thanks to ForrestHunt, Inc. for supporting the preponderance of this
; work, and for permission to include it here.

; This book completes apply.lisp by defining loop$ scions.  As with apply.lisp,
; one way to think of this book is that it was derived by taking Section 12 of
; source file apply.lisp and sprinkling in the include-books, defthms,
; declarations, and hints to get the source file admitted in guard-verified,
; :logic mode fashion by a version of ACL2 in which these functions weren't
; already defined.  We supply minimal comments here except when discussing the
; termination/guard verification issues.  See the corresponding source files
; for explanations of the definitions below!

; -----------------------------------------------------------------
; 12. Loop$ Scions

(in-package "ACL2")          ; on /books/projects/apply/

(include-book "projects/apply/base" :dir :system)

#+acl2-devel ; else not redundant
(defun$ tails-ac (lst ac)
  (declare (xargs :guard (and (true-listp lst)
                              (true-listp ac))))
  (cond ((endp lst) (revappend ac nil))
        (t (tails-ac (cdr lst) (cons lst ac)))))

#+acl2-devel ; else not redundant
(defun$ tails (lst)
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
(defun$ empty-loop$-as-tuplep (tuple)
  (declare (xargs :guard (true-list-listp tuple)))
  (cond ((endp tuple) nil)
        ((endp (car tuple)) t)
        (t (empty-loop$-as-tuplep (cdr tuple)))))

#+acl2-devel ; else not redundant
(defun$ car-loop$-as-tuple (tuple)
  (declare (xargs :guard (true-list-listp tuple)))
  (cond ((endp tuple) nil)
        (t (cons (caar tuple) (car-loop$-as-tuple (cdr tuple))))))

#+acl2-devel ; else not redundant
(defun$ cdr-loop$-as-tuple (tuple)
  (declare (xargs :guard (true-list-listp tuple)))
  (cond ((endp tuple) nil)
        (t (cons (cdar tuple) (cdr-loop$-as-tuple (cdr tuple))))))

#+acl2-devel ; else not redundant
(defun$ loop$-as-ac (tuple ac)
  (declare (xargs :guard (and (true-list-listp tuple)
                              (true-listp ac))))
  (cond ((endp tuple) (revappend ac nil))
        ((empty-loop$-as-tuplep tuple) (revappend ac nil))
        (t (loop$-as-ac (cdr-loop$-as-tuple tuple)
                        (cons (car-loop$-as-tuple tuple)
                              ac)))))

#+acl2-devel ; else not redundant
(defun$ loop$-as (tuple)
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

; Note that from-to-by-measure is defined in ACL2 source file apply-prim.lisp.

(defthm natp-from-to-by-measure
  (natp (from-to-by-measure i j))
  :rule-classes :type-prescription)

#+acl2-devel ; else not redundant
(defun$ from-to-by-ac (i j k ac)
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
(defun$ from-to-by (i j k)
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
  #+acl2-devel
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
              (alt-def-from-to-by-recursion i (- j k) k (cons (+ i (* k (floor (- j i) k))) lst)))
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
                         (from-to-by-ac i (+ i (* k (floor (- j i) k))) k lst))))
     :rule-classes nil
     :hints (("Goal" :in-theory (disable from-to-by)
              :use (from-to-by-normalizer
                    (:instance from-to-by-ac=from-to-by-lemma
                               (j (+ J (- (MOD (+ J (- I)) K))))))))))

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

; -----------------------------------------------------------------
; Until$, Until$+, and Their Tail Recursive Counterparts

#+acl2-devel ; else not redundant
(defun$ until$-ac (fn lst ac)
  (declare (xargs :guard
                  (and (apply$-guard fn '(nil))
                       (true-listp lst)
                       (true-listp ac))))
  (cond
   ((endp lst) (revappend ac nil))
   ((apply$ fn (list (car lst))) (revappend ac nil))
   (t (until$-ac fn (cdr lst) (cons (car lst) ac)))))

#+acl2-devel ; else not redundant
(defun$ until$ (fn lst)
  (declare (xargs :guard
                  (and (apply$-guard fn '(nil))
                       (true-listp lst))
                  :verify-guards nil))
  (mbe :logic
       (if (endp lst)
           nil
           (if (apply$ fn (list (car lst)))
               nil
               (cons (car lst)
                     (until$ fn (cdr lst)))))
       :exec
       (until$-ac fn lst nil)))

(defthm until$-ac=until$
  (equal (until$-ac fn lst ac)
         (revappend ac (until$ fn lst))))

(verify-guards until$)

#+acl2-devel ; else not redundant
(defun$ until$+-ac (fn globals lst ac)
  (declare (xargs :guard
                  (and (apply$-guard fn '(nil nil))
                       (true-listp globals)
                       (true-list-listp lst)
                       (true-listp ac))))
  (cond
   ((endp lst) (revappend ac nil))
   ((apply$ fn (list globals (car lst))) (revappend ac nil))
   (t (until$+-ac fn globals (cdr lst) (cons (car lst) ac)))))

#+acl2-devel ; else not redundant
(defun$ until$+ (fn globals lst)
  (declare (xargs :guard
                  (and (apply$-guard fn '(nil nil))
                       (true-listp globals)
                       (true-list-listp lst))
                  :verify-guards nil))
  (mbe :logic
       (if (endp lst)
           nil
           (if (apply$ fn (list globals (car lst)))
               nil
               (cons (car lst)
                     (until$+ fn globals (cdr lst)))))
       :exec
       (until$+-ac fn globals lst nil)))

(defthm until$+-ac=until$+
  (equal (until$+-ac fn globals lst ac)
         (revappend ac (until$+ fn globals lst))))

(verify-guards until$+)

; -----------------------------------------------------------------
; When$, When$+, and Their Tail Recursive Counterparts

#+acl2-devel ; else not redundant
(defun$ when$-ac (fn lst ac)
  (declare (xargs :guard
                  (and (apply$-guard fn '(nil))
                       (true-listp lst)
                       (true-listp ac))))
  (if (endp lst)
      (revappend ac nil)
      (when$-ac fn (cdr lst)
                (if (apply$ fn (list (car lst)))
                    (cons (car lst) ac)
                    ac))))

#+acl2-devel ; else not redundant
(defun$ when$ (fn lst)
  (declare (xargs :guard
                  (and (apply$-guard fn '(nil))
                       (true-listp lst))
                  :verify-guards nil))
  (mbe :logic
       (if (endp lst)
           nil
           (if (apply$ fn (list (car lst)))
               (cons (car lst)
                     (when$ fn (cdr lst)))
               (when$ fn (cdr lst))))
       :exec (when$-ac fn lst nil)))

(defthm when$-ac=when$
  (equal (when$-ac fn lst ac)
         (revappend ac (when$ fn lst))))

(verify-guards when$)

#+acl2-devel ; else not redundant
(defun$ when$+-ac (fn globals lst ac)
  (declare (xargs :guard
                  (and (apply$-guard fn '(nil nil))
                       (true-listp globals)
                       (true-list-listp lst)
                       (true-listp ac))))
  (if (endp lst)
      (revappend ac nil)
      (when$+-ac fn globals
                 (cdr lst)
                 (if (apply$ fn (list globals (car lst)))
                     (cons (car lst) ac)
                     ac))))

#+acl2-devel ; else not redundant
(defun$ when$+ (fn globals lst)
  (declare (xargs :guard
                  (and (apply$-guard fn '(nil nil))
                       (true-listp globals)
                       (true-list-listp lst))
                  :verify-guards nil))
  (mbe :logic
       (if (endp lst)
           nil
           (if (apply$ fn (list globals (car lst)))
               (cons (car lst)
                     (when$+ fn globals (cdr lst)))
               (when$+ fn globals (cdr lst))))
       :exec (when$+-ac fn globals lst nil)))

(defthm when$+-ac=when$+
  (equal (when$+-ac fn globals lst ac)
         (revappend ac (when$+ fn globals lst))))

(verify-guards when$+)

; -----------------------------------------------------------------
; Sum$, Sum$+, and Their Tail Recursive Counterparts

#+acl2-devel ; else not redundant
(defun$ sum$-ac (fn lst ac)
  (declare (xargs :guard
                  (and (apply$-guard fn '(nil))
                       (true-listp lst)
                       (acl2-numberp ac))))
  (if (endp lst)
      ac
      (sum$-ac fn
               (cdr lst)
               (+ (fix (apply$ fn (list (car lst)))) ac))))

#+acl2-devel ; else not redundant
(defun$ sum$ (fn lst)
  (declare (xargs :guard
                  (and (apply$-guard fn '(nil))
                       (true-listp lst))
                  :verify-guards nil))
  (mbe :logic
       (if (endp lst)
           0
           (+ (fix (apply$ fn (list (car lst))))
              (sum$ fn (cdr lst))))
       :exec (sum$-ac fn lst 0)))

(defthm sum$-ac=sum$
  (implies (acl2-numberp ac)
           (equal (sum$-ac fn lst ac)
                  (+ ac (sum$ fn lst)))))

(verify-guards sum$)

#+acl2-devel ; else not redundant
(defun$ sum$+-ac (fn globals lst ac)
  (declare (xargs :guard
                  (and (apply$-guard fn '(nil nil))
                       (true-listp globals)
                       (true-list-listp lst)
                       (acl2-numberp ac))))
  (if (endp lst)
      ac
      (sum$+-ac fn globals
                (cdr lst)
                (+ (fix (apply$ fn (list globals (car lst)))) ac))))

#+acl2-devel ; else not redundant
(defun$ sum$+ (fn globals lst)
  (declare (xargs :guard
                  (and (apply$-guard fn '(nil nil))
                       (true-listp globals)
                       (true-list-listp lst))
                  :verify-guards nil))
  (mbe :logic
       (if (endp lst)
           0
           (+ (fix (apply$ fn (list globals (car lst))))
              (sum$+ fn globals (cdr lst))))
       :exec (sum$+-ac fn globals lst 0)))

(defthm sum$+-ac=sum$+
  (implies (acl2-numberp ac)
           (equal (sum$+-ac fn globals lst ac)
                  (+ ac (sum$+ fn globals lst)))))

(verify-guards sum$+)

; -----------------------------------------------------------------
; Always$ and Always$+

#+acl2-devel ; else not redundant
(defun$ always$ (fn lst)
  (declare (xargs :guard
                  (and (apply$-guard fn '(nil))
                       (true-listp lst))))
  (if (endp lst)
      t
      (if (apply$ fn (list (car lst)))
          (always$ fn (cdr lst))
          nil)))

#+acl2-devel ; else not redundant
(defun$ always$+ (fn globals lst)
  (declare (xargs :guard
                  (and (apply$-guard fn '(nil nil))
                       (true-listp globals)
                       (true-list-listp lst))))
  (if (endp lst)
      t
      (if (apply$ fn (list globals (car lst)))
          (always$+ fn globals (cdr lst))
          nil)))

; -----------------------------------------------------------------
; Thereis$ and Thereis$+

#+acl2-devel ; else not redundant
(defun$ thereis$ (fn lst)
  (declare (xargs :guard
                  (and (apply$-guard fn '(nil))
                       (true-listp lst))))
  (if (endp lst)
      nil
      (or (apply$ fn (list (car lst)))
          (thereis$ fn (cdr lst)))))

#+acl2-devel ; else not redundant
(defun$ thereis$+ (fn globals lst)
  (declare (xargs :guard
                  (and (apply$-guard fn '(nil nil))
                       (true-listp globals)
                       (true-list-listp lst))))
  (if (endp lst)
      nil
      (or (apply$ fn (list globals (car lst)))
          (thereis$+ fn globals (cdr lst)))))

; -----------------------------------------------------------------
; Collect$, Collect$+, and Their Tail Recursive Counterparts

#+acl2-devel ; else not redundant
(defun$ collect$-ac (fn lst ac)
  (declare (xargs :guard (and (apply$-guard fn '(nil))
                              (true-listp lst)
                              (true-listp ac))))
  (cond ((endp lst) (revappend ac nil))
        (t (collect$-ac fn (cdr lst)
                        (cons (apply$ fn (list (car lst))) ac)))))

#+acl2-devel ; else not redundant
(defun$ collect$ (fn lst)
  (declare (xargs :guard (and (apply$-guard fn '(nil))
                              (true-listp lst))
                  :verify-guards nil))
  (mbe :logic
       (if (endp lst)
           nil
           (cons (apply$ fn (list (car lst)))
                 (collect$ fn (cdr lst))))
       :exec (collect$-ac fn lst nil)))

(defthm collect$-ac=collect$
  (equal (collect$-ac fn lst ac)
         (revappend ac (collect$ fn lst))))

(verify-guards collect$)

#+acl2-devel ; else not redundant
(defun$ collect$+-ac (fn globals lst ac)
  (declare (xargs :guard (and (apply$-guard fn '(nil nil))
                              (true-listp globals)
                              (true-list-listp lst)
                              (true-listp ac))))
  (cond ((endp lst) (revappend ac nil))
        (t (collect$+-ac fn globals
                         (cdr lst)
                         (cons (apply$ fn (list globals (car lst))) ac)))))

#+acl2-devel ; else not redundant
(defun$ collect$+ (fn globals lst)
  (declare (xargs :guard (and (apply$-guard fn '(nil nil))
                              (true-listp globals)
                              (true-list-listp lst))
                  :verify-guards nil))
  (mbe :logic
       (if (endp lst)
           nil
           (cons (apply$ fn (list globals (car lst)))
                 (collect$+ fn globals (cdr lst))))
       :exec (collect$+-ac fn globals lst nil)))

(defthm collect$+-ac=collect$+
  (equal (collect$+-ac fn globals lst ac)
         (revappend ac (collect$+ fn globals lst))))

(verify-guards collect$+)

; -----------------------------------------------------------------
; Append$, Append$+, and Their Tail Recursive Counterparts

#+acl2-devel ; else not redundant
(defun$ revappend-true-list-fix (x ac)
  (declare (xargs :guard t))
  (if (atom x)
      ac
      (revappend-true-list-fix (cdr x) (cons (car x) ac))))

(defthm true-listp-revappend-true-list-fix
  (iff (true-listp (revappend-true-list-fix a b))
       (true-listp b)))

#+acl2-devel ; else not redundant
(defun$ append$-ac (fn lst ac)
  (declare (xargs :guard (and (apply$-guard fn '(nil))
                              (true-listp lst)
                              (true-listp ac))))
  (cond ((endp lst) (revappend ac nil))
        (t (append$-ac fn
                       (cdr lst)
                       (revappend-true-list-fix
                        (apply$ fn (list (car lst)))
                        ac)))))

#+acl2-devel ; else not redundant
(defun$ append$ (fn lst)
  (declare (xargs :guard (and (apply$-guard fn '(nil))
                              (true-listp lst))
                  :verify-guards nil))
  (mbe :logic
       (if (endp lst)
           nil
           (append
            (true-list-fix (apply$ fn (list (car lst))))
            (append$ fn (cdr lst))))
       :exec (append$-ac fn lst nil)))

(defthm append$-ac=append$
  (equal (append$-ac fn lst ac)
         (revappend ac (append$ fn lst))))

(verify-guards append$)

#+acl2-devel ; else not redundant
(defun$ append$+-ac (fn globals lst ac)
  (declare (xargs :guard (and (apply$-guard fn '(nil nil))
                              (true-listp globals)
                              (true-list-listp lst)
                              (true-listp ac))))
  (cond ((endp lst) (revappend ac nil))
        (t (append$+-ac fn
                        globals
                        (cdr lst)
                        (revappend-true-list-fix
                         (apply$ fn (list globals (car lst)))
                         ac)))))

#+acl2-devel ; else not redundant
(defun$ append$+ (fn globals lst)
  (declare (xargs :guard (and (apply$-guard fn '(nil nil))
                              (true-listp globals)
                              (true-list-listp lst))
                  :verify-guards nil))
  (mbe :logic
       (if (endp lst)
           nil
           (append
            (true-list-fix (apply$ fn (list globals (car lst))))
            (append$+ fn globals (cdr lst))))
       :exec (append$+-ac fn globals lst nil)))

(defthm append$+-ac=append$+
  (equal (append$+-ac fn globals lst ac)
         (revappend ac (append$+ fn globals lst))))

(verify-guards append$+)
