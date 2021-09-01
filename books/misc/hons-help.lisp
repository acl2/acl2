; Copyright (C) 2013, Regents of the University of Texas
; Written by Bob Boyer and Warren A. Hunt, Jr. (some years before that)
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

;   hons-help.lisp                                Boyer & Hunt

(in-package "ACL2")
(include-book "gentle")
(include-book "std/alists/worth-hashing" :dir :system)
(set-state-ok t)


; In this file one may find some helpful functions and lemmas in the "HONS
; School", but none of them require "under the hood" definitions.  That is, the
; "user" could do all this by himself.



(defmacro all-memoized-fns (&optional show-conditions)
  (if show-conditions
      '(table-alist 'memoize-table (w state))
    '(strip-cars (table-alist 'memoize-table (w state)))))



; FAST ALIST UTILITIES -----------------------------------------------------

(defsection make-fal
  :parents (fast-alists)
  :short "Make a fast alist out of an alist."
  :long "<p>Note: it is usually better to use @(see make-fast-alist).</p>

<p>@('(make-fal al name)') copies the alist AL with @(see hons-acons) to make a
fast alist that ends with NAME.</p>

<p>Typically @('name') is an atom, and it becomes the final @(see cdr) of the
new fast alist.  Some atoms have special meanings, e.g., they act as size
hints; see @(see hons-acons) for details.</p>

<p>However, @('name') can also be an existing fast alist.  In this case, this
fast alist is extended with the new pairs from @('al'), using @(see
hons-acons).  Note that @('name') will no longer be fast after the call of
@('make-fal').</p>

<p>There's nothing under-the-hood about @('make-fal'); it just repeatedly calls
@('hons-acons').  The built-in function @(see make-fast-alist) is generally
more efficient and can be nicer to reason about because logically it is just
the identity.  On the other hand, @('make-fast-alist') can't be used to extend
an existing fast alist like @('make-fal').</p>"

  (defn make-fal (al name)
    (cond ((atom al)
           name)
          ((atom (car al))
           (make-fal (cdr al) name))
          (t
           (hons-acons (caar al)
                       (cdar al)
                       (make-fal (cdr al) name))))))

(defmacro ansfl (x y)

  "(ANSFL x y) returns the single value X after first flushing
  the fast hash table backing for Y, if Y is a fast alist.  Thus

     (ANSFL X Y) = X

  X must be a form that returns a single value."

  `((lambda (ansfl-do-not-use-elsewhere1 ansfl-do-not-use-elsewhere2)
      (declare (ignore ansfl-do-not-use-elsewhere2))
      ansfl-do-not-use-elsewhere1)
    ,x
    (flush-hons-get-hash-table-link ,y)))


; [Jared]: Removing ansfl1 since I think we don't use it?

;; (defmacro ansfl1 (x)
;;   `((lambda (ansfl1-do-not-use-elsewhere1)
;;       ((lambda (ansfl1-do-not-use-elsewhere1
;;                 ansfl1-do-not-use-elsewhere2)
;;          (declare (ignore ansfl1-do-not-use-elsewhere2))
;;         ansfl1-do-not-use-elsewhere1)))
;;     ,x))

(defmacro ansfl-list (l x)

; (ansfl-list (a b c ...) x) -- frees a, b, c, ..., returns x

  (if (atom l)
      x
    `(ansfl (ansfl-list ,(cdr l) ,x)
            ,(car l))))


(defn ansfl-last-list (r bindings)

; [Jared]: BOZO please document this.  It's used in het*.

; bindings is an alist.  in het* the bindings are names being bound
; like in a let*.
;
; all of the names being bound are freed, then we return r.

  (if (atom bindings)
      r
    `(ansfl ,(ansfl-last-list r (gentle-cdr bindings))
            ,(gentle-caar bindings))))

(defmacro het* (bindings &rest r)

; This implementation of het* is somewhat defective in that it is
; incapable of returning multiple values.  We cannot see how to fix
; it.

; this is basically let*, but we try to fast-alist-free everything that gets
; bound.  which works out, in a weird kind of way, for anything that
; isn't a fast alist anyway, but is really pretty gross.

  `(let* ,bindings
     ,@(butlast r 1)
     ,(ansfl-last-list (car (last r)) bindings)))

(defmacro with-fast-list (var term name form)

; bind a variable to a fast-alist created by binding every element of term to t,
; with the final name name.  then run form and free var.

  `(let ((,var (hons-put-list
                ,term
                t
                ,name)))
     (ansfl ,form ,var)))


(defn hons-put-list (keys values l)

; If there are not enough values, the last atom of values is used for
; the remaining values.  If there are not as many keys as values, the
; extra values are ignored.

; Warnings: The pairs are consed onto l in what might seem to be the
; reverse order.  And redundant pairs are not even consed on to l at
; all.  Unless the old value of (hons-get key l) is nil, in which case
; we do cons, even if the new val is nil.

; So if you need to control the order and/or presence of the added
; pairs, write another function.

  (if (atom keys)
      l
    (let* ((cp          (consp values))
           (val         (if cp (car values) values))
           (next-values (if cp (cdr values) values))
           (old-pair    (hons-get (car keys) l))
           (redundant   (and old-pair (hons-equal val (cdr old-pair))))
           (next-l      (if redundant l (hons-acons (car keys) val l))))
      (hons-put-list (cdr keys) next-values next-l))))



(defund alist-keys (x)
  (declare (xargs :guard t))
  (cond ((atom x)
         nil)
        ((atom (car x))
         (alist-keys (cdr x)))
        (t
         (cons (caar x) (alist-keys (cdr x))))))

(defund alist-vals (x)
  (declare (xargs :guard t))
  (cond ((atom x)
         nil)
        ((atom (car x))
         (alist-vals (cdr x)))
        (t
         (cons (cdar x) (alist-vals (cdr x))))))








; LIST OPERATIONS USING HONS -----------------------------------------------

(defn hons-binary-append (x y)
  (mbe :logic (append x y)
       :exec (if (atom x)
                 y
               (hons (car x)
                     (hons-binary-append (cdr x) y)))))

(defmacro hons-append (x y &rest rst)
  "APPEND using HONS instead of CONS"
  (xxxjoin 'hons-binary-append (cons x (cons y rst))))

(defn hons-revappend (x y)
  "REVAPPEND using HONS instead of CONS"
  (mbe :logic (revappend x y)
       :exec (if (atom x)
                 y
               (hons-revappend (cdr x) (hons (car x) y)))))

(defn hons-reverse (x)
  "REVERSE using HONS instead of CONS"
  (mbe :logic (reverse x)
       :exec (if (stringp x)
                 (reverse x)
               (hons-revappend x nil))))

(defmacro hons-list (&rest x)
  "(LIST ...) using HONS instead of CONS"
  (if (atom x)
      nil
    (list 'hons (car x) (cons 'hons-list (cdr x)))))

(defmacro hons-list* (&rest x)
  "(LIST* ...) using HONS instead of CONS"
  (cond ((atom x)
         x)
        ((atom (cdr x))
         (car x))
        (t
         (list 'hons (car x) (cons 'hons-list* (cdr x))))))

(defsection hons-make-list
  :parents (fast-alists make-list)
  :short "Like @(see make-list), but produces honses."

  (defn hons-make-list-acc (n val ac)
    (mbe :logic (make-list-ac n val ac)
         :exec (if (not (posp n))
                   ac
                 (hons-make-list-acc (1- n) val (hons val ac)))))

  (defmacro hons-make-list (size &key initial-element)
    `(hons-make-list-acc ,size ,initial-element nil)))



; LIST OPERATIONS USING HONS-EQUAL -----------------------------------------

(defn hons-member-equal (x y)
  "MEMBER-EQUAL using HONS-EQUAL for each equality check"

; [Jared]: BOZO this is exactly the same as gentle-member-equal.  Why duplicate
; it?  Well, maybe gentle-member-equal should actually be changed to use equal,
; and this function should be left alone.

  (mbe :logic (member-equal x y)
       :exec (cond ((atom y) nil)
                   ((hons-equal x (car y)) y)
                   (t (hons-member-equal x (cdr y))))))




; FAST DUPLICATE CHECKING AND REMOVAL --------------------------------------

(defn hons-dups-p1 (l tab)
  "Basic duplicates check; table is a fast alist that associates already-seen
   elements with t."
  (cond ((atom l)
         (ansfl nil tab))
        ((hons-get (car l) tab)
         (ansfl l tab))
        (t
         (hons-dups-p1 (cdr l)
                       (hons-acons (car l) t tab)))))

(encapsulate nil
  (local (defthm hons-assoc-equal-hons-put-list-t
           (iff (hons-assoc-equal x (hons-put-list y t rest))
                (or (hons-assoc-equal x rest)
                    (member x y)))
           :hints (("goal" :induct (hons-put-list y t rest)))))
  (defthm hons-assoc-equal-hons-put-list
    (implies (atom a)
             (iff (hons-assoc-equal x (hons-put-list y t a))
                  (member x y)))))


(defn hons-dups-p (l)

; If L has no duplicate members, then (HONS-DUPS-P L) is NIL.  If L
; has equal members, then (HONS-DUPS-P l) returns the second tail of L
; whose CAR is the first member of L that occurs twice in L.

; [Jared]: BOZO stylistically, would it be better to free the table in this
; function, rather than in hons-dups-p1?

  (hons-dups-p1 l '*hons-dups-p*))

(local (in-theory (enable alist-keys)))
(local (defthm member-alist-keys
         (iff (member x (alist-keys y))
              (hons-assoc-equal x y))))

(encapsulate
  nil


  (local (defthm intersectp-cons-second
           (implies (intersectp x y)
                    (intersectp x (cons z y)))))

  (local (defthm intersectp-cons-second-2
           (implies (not (intersectp x y))
                    (iff (intersectp x (cons z y))
                         (member z x)))))

  (local (defthm intersectp-cons-member
           (implies (member z x)
                    (intersectp x (cons z y)))))

  (local (defthm hons-dups-p1-no-duplicatesp
           (iff (hons-dups-p1 x tab)
                (or (not (no-duplicatesp x))
                    (intersectp x (alist-keys tab))))
           :hints(("Goal" :induct (hons-dups-p1 x tab)))))

  (defthm hons-dups-p-no-duplicatesp
    (iff (hons-dups-p x)
         (not (no-duplicatesp x)))))


(local (in-theory (disable hons-dups-p)))

(defun fast-no-duplicatesp (x)
  (declare (xargs :guard (eqlable-listp x)))
  (mbe :logic (no-duplicatesp-equal x)
       :exec (if (< (length x) 400)
                 (no-duplicatesp x)
               (not (hons-dups-p x)))))

(defun fast-no-duplicatesp-equal (x)
  (declare (xargs :guard (true-listp x)))
  (mbe :logic (no-duplicatesp-equal x)
       :exec (if (< (length x) 400)
                 (no-duplicatesp-equal x)
               (not (hons-dups-p x)))))

(defun fast-no-duplicatesp-eq (x)
  (declare (xargs :guard (symbol-listp x)))
  (mbe :logic (no-duplicatesp-equal x)
       :exec (if (< (length x) 400)
                 (no-duplicatesp-eq x)
               (not (hons-dups-p x)))))





(defn hons-duplicates1 (l tab)
  (cond ((atom l) (ansfl nil tab))
        ((hons-get (car l) tab)
         (cons (car l) (hons-duplicates1 (cdr l) tab)))
        (t (hons-duplicates1 (cdr l) (hons-acons (car l) t tab)))))

(defn hons-duplicates (l)
  (hons-duplicates1 l nil))




; SUBLIS WITH FAST ALISTS AND MEMOIZATION ----------------------------------

(defsection hons-sublis-aux
  :parents (hons-sublis)
  :short "Memoized core of @(see hons-sublis)."

  (defun hons-sublis-aux (fal x)
    (declare (xargs :guard t))
    (if (atom x)
        (let ((pair (hons-get x fal)))
          (if pair (cdr pair) x))
      (cons (hons-sublis-aux fal (car x))
            (hons-sublis-aux fal (cdr x)))))

  (encapsulate
    ()
    (local (defthm lemma
             (implies (alistp x)
                      (equal (hons-assoc-equal a x)
                             (assoc a x)))
             :hints(("Goal" :induct (len x)))))

    (defthm hons-sublis-aux-removal
      (implies (alistp fal)
               (equal (hons-sublis-aux fal x)
                      (sublis fal x)))))

  (memoize 'hons-sublis-aux :condition '(consp x)))

(defsection hons-sublis
  :parents (hons sublis)
  :short "@(tsee memoize)d version of SUBLIS which uses @(see fast-alists)."
  :long "<p>@('(hons-sublis fal x)') is like @(see sublis), but may be faster
in two ways.</p>

<ol>

<li>It uses @(see hons-get) instead of @(see assoc), which may provide a
speedup when the alist in question is very long.  Note that for good
performance, the fast-alist argument, @('fal'), must be a valid
fast-alist.</li>

<li>It uses a memoized auxiliary function, which may provide a speedup when the
tree argument, @('x'), contains large, shared structures.</li>

</ol>"

  (defun hons-sublis (fal x)
    (declare (xargs :guard t))
    (let ((ret (hons-sublis-aux fal x)))
      (prog2$
       (clear-memoize-table 'hons-sublis-aux)
       ret)))

  (defthm hons-sublis-removal
    (implies (alistp fal)
             (equal (hons-sublis fal x)
                    (sublis fal x)))))




; SET OPERATIONS USING HONS ------------------------------------------------

; Some "fast" operations for "set" intersection, union, and set-diff
; intended for use on lists of ACL2 objects without duplications.

(defconst *magic-number-for-hashing*

  18

; Matt K. mod: Comment out doc string (disallowed after ACL2 8.3).
#|
  "Assoc is sometimes faster than gethash.~/

  Lisp folklore says it is faster to use ASSOC than GETHASH on a list
  if the list has length 18 or less.~/~/"
|#)


; [Jared] BOZO it would be nice to prove these equivalent to simple set
; operations with no fast alist stuff.

(defn hons-int1 (l1 al2)
  (cond ((atom l1)
         nil)
        ((hons-get (car l1) al2)
         (cons (car l1) (hons-int1 (cdr l1) al2)))
        (t
         (hons-int1 (cdr l1) al2))))

(defn hons-intersection2 (l1 l2)
  (cond ((atom l1)
         nil)
        ((hons-member-equal (car l1) l2)
         (cons (car l1) (hons-intersection2 (cdr l1) l2)))
        (t
         (hons-intersection2 (cdr l1) l2))))

(defn hons-intersection (l1 l2)  ; preserves order of members in l1
  (cond ((worth-hashing l2)
         (with-fast-list fl2 l2 '*hons-intersection-alist*
                         (hons-int1 l1 fl2)))
        (t
         (hons-intersection2 l1 l2))))

(encapsulate
  nil
  (local
   (defthm hons-int1-is-intersection-equal
     (implies (atom atom)
              (equal (hons-int1 x (hons-put-list y t atom))
                     (intersection-equal x y)))
     :hints(("Goal" :in-theory (enable intersection-equal)))))

  (local
   (defthm hons-intersection2-is-intersection-equal
     (equal (hons-intersection2 x y)
            (intersection-equal x y))
     :hints(("Goal" :in-theory (enable intersection-equal)))))

  (defthm hons-intersection-is-intersection-equal
    (equal (hons-intersection a b)
           (intersection-equal a b))))


(defn hons-intersect-p1 (l1 al2)
  (cond ((atom l1)
         nil)
        ((hons-get (car l1) al2)
         t)
        (t
         (hons-intersect-p1 (cdr l1) al2))))

(defn hons-intersect-p2 (l1 l2)
  (cond ((atom l1) nil)
        ((hons-member-equal (car l1) l2)
         t)
        (t
         (hons-intersect-p2 (cdr l1) l2))))

(defn hons-intersect-p (l1 l2) ; returns T or NIL
  (cond ((and (worth-hashing l1)
              (worth-hashing l2))
         (with-fast-list fl2 l2 '*hons-intersect-p-alist*
                         (hons-intersect-p1 l1 fl2)))
        (t
         (hons-intersect-p2 l1 l2))))

(encapsulate
  nil
  (local
   (defthm hons-intersect-p1-is-intersectp
     (implies (atom atom)
              (equal (hons-intersect-p1 x (hons-put-list y t atom))
                     (intersectp x y)))
     :hints(("Goal" :in-theory (enable intersectp)))))

  (local
   (defthm hons-intersect-p2-is-intersectp
     (equal (hons-intersect-p2 x y)
            (intersectp x y))
     :hints(("Goal" :in-theory (enable intersectp)))))

  (defthm hons-intersect-p-is-intersectp
    (equal (hons-intersect-p a b)
           (intersectp a b))))


(defn hons-sd1 (l1 al2)
  (cond ((atom l1) nil)
        ((hons-get (car l1) al2)
         (hons-sd1 (cdr l1) al2))
        (t (cons (car l1) (hons-sd1 (cdr l1) al2)))))

(defn hons-set-diff2 (l1 l2)
  (cond ((atom l1) nil)
        ((hons-member-equal (car l1) l2)
         (hons-set-diff2 (cdr l1) l2))
        (t (cons (car l1) (hons-set-diff2 (cdr l1) l2)))))

(defn hons-set-diff (l1 l2) ; preserves order of members in l1
  (cond ((worth-hashing l2)
         (with-fast-list fl2 l2 '*hons-set-diff-alist*
                         (hons-sd1 l1 fl2)))
        (t (hons-set-diff2 l1 l2))))

(encapsulate
  nil
  (local
   (defthm hons-sd1-is-set-difference$
     (implies (atom atom)
              (equal (hons-sd1 x (hons-put-list y t atom))
                     (set-difference$ x y)))
     :hints(("Goal" :in-theory (enable set-difference$)))))

  (local
   (defthm hons-set-diff2-is-set-difference$
     (equal (hons-set-diff2 x y)
            (set-difference$ x y))
     :hints(("Goal" :in-theory (enable set-difference$)))))

  (defthm hons-set-diff-is-set-difference$
    (equal (hons-set-diff a b)
           (set-difference$ a b))))


(defn hons-union1 (l1 al2 acc)
  (cond ((atom l1) acc)
        ((hons-get (car l1) al2)
         (hons-union1 (cdr l1) al2 acc))
        (t (hons-union1 (cdr l1) al2 (cons (car l1) acc)))))

(defn hons-union2 (l1 l2 acc)
  (cond ((atom l1) acc)
        ((hons-member-equal (car l1) l2)
         (hons-union2 (cdr l1) l2 acc))
        (t (hons-union2 (cdr l1) l2 (cons (car l1) acc)))))

;; variant like hons-sd1, hons-int1 where fl2 doubles as the accumulator,
;; and therefore does not collect duplicates; useful for unioning together many lists
(defn hons-un1 (l1 fl2)
  (cond ((atom l1) fl2)
        ((hons-get (car l1) fl2)
         (hons-un1 (cdr l1) fl2))
        (t (hons-un1 (cdr l1) (hons-acons (car l1) t fl2)))))

(defn hons-union (l1 l2)

; HONS-UNION may run faster if L1 and L2 are lists of atoms or honsps,
; since HONS-MEMBER-EQUAL and HONS-GET may be used.

; To prove someday:
; (defthm hons-union-thm
;  (equal (gentle-member x (hons-union l1 l2))
;         (or (gentle-member x l1)
;             (gentle-member x l2))))

  (cond ((atom l1) l2)
        ((atom l2) l1)
        ((atom (cdr l1))
         (if (hons-member-equal (car l1) l2)
             l2
           (cons (car l1) l2)))
        ((atom (cdr l2))
         (if (hons-member-equal (car l2) l1)
             l1
           (cons (car l2) l1)))
        (t
         ;; [Jared]: calling len on both lists seems inefficient; we could
         ;; write a cdr-both style function that determines which is longer

         ;; BOZO This is a very messy optimization, and the benchmarks below
         ;; suggest that it might be backward.  What is our goal?  If we want
         ;; to produce the shortest list containing the union of our elements,
         ;; then we're going about it all wrong in any case.  If we just want
         ;; any list containing the union, and we want to get it as fast as
         ;; possible, we're better off putting only the shorter list into the
         ;; fal; here we're using the longer list instead.
         (let ((len1 (len l1))
               (len2 (len l2)))
           (cond ((and (>= len2 len1)
                       (>= len1 *magic-number-for-hashing*))
                  (with-fast-list
                   fl2 l2 '*hons-union*
                   (hons-union1 l1 fl2 l2)))
                 ((and (>= len1 len2)
                       (>= len2 *magic-number-for-hashing*))
                  (with-fast-list
                   fl1 l1 '*hons-union*
                   (hons-union1 l2 fl1 l1)))
                 (t (hons-union2 l1 l2 l2)))))))

;; (let ((l1 (loop for i from 1 to 10 collect i))
;;       (l2 (loop for i from 1 to 1000 collect i)))
;;   (progn
;;     (time$ (loop for i from 1 to 1000 collect
;;                  (with-fast-list fl2 l2 '*hons-union*
;;                    (hons-union1 l1 fl2 l2))))
;;     nil)) ;; 0.43 seconds, 102 MB

;; (let ((l1 (loop for i from 1 to 10 collect i))
;;       (l2 (loop for i from 1 to 1000 collect i)))
;;   (progn
;;     (time$ (loop for i from 1 to 1000 collect
;;                  (with-fast-list fl1 l1 '*hons-union*
;;                    (hons-union1 l2 fl1 l1))))
;;     nil)) ;; 0.10 seconds, 18 MB (!!)

;; (let ((l1 (loop for i from 1 to 10 collect i))
;;       (l2 (loop for i from 1 to 1000 collect i)))
;;   (progn
;;     (time$ (loop for i from 1 to 1000 collect
;;                  (with-fast-list fl1 l1 '*hons-union*
;;                    (hons-un1 l2 fl1))))
;;     nil)) ;; 0.42 seconds, 101 MB

;; (let ((l1 (loop for i from 1 to 10 collect i))
;;       (l2 (loop for i from 1 to 1000 collect i)))
;;   (progn
;;     (time$ (loop for i from 1 to 1000 collect
;;                  (with-fast-list fl2 l2 '*hons-union*
;;                    (hons-un1 l1 fl2))))
;;     nil)) ;; 0.43 seconds, 102 MB

;; (let ((l1 (loop for i from 1 to 10 collect i))
;;       (l2 (loop for i from 1 to 20 nconc
;;                 (loop for i from 1 to 50 collect i))))
;;   (progn
;;     (time$ (loop for i from 1 to 1000 collect
;;                  (with-fast-list fl2 l2 '*hons-union*
;;                    (hons-union1 l1 fl2 l2))))
;;     nil)) ;; 0.11 seconds, 3.3 MB

;; (let ((l1 (loop for i from 1 to 10 collect i))
;;       (l2 (loop for i from 1 to 20 nconc
;;                 (loop for i from 1 to 50 collect i))))
;;   (progn
;;     (time$ (loop for i from 1 to 1000 collect
;;                  (with-fast-list fl1 l1 '*hons-union*
;;                    (hons-union1 l2 fl1 l1))))
;;     nil)) ;; 0.10 seconds, 15 MB


;; Note that because hons-union1 and 2 accumulate the first arg onto the second
;; arg in reverse order, it's not the same as union$.

(encapsulate nil
  (local (defthm hons-union1-revappend-set-difference
           (equal (hons-union1 x tab y)
                  (revappend (set-difference$ x (alist-keys tab)) y))))

  (local (defthm hons-union2-revappend-set-difference
           (equal (hons-union2 x l y)
                  (revappend (set-difference$ x l) y))))

  ;; bozo prove something about hons-union, but maybe fix it first
  )



(defn hons-union-list (l)
  (if (atom l)
      nil
    (hons-union (car l)
                (hons-union-list (cdr l)))))


(defn hons-subset1 (l al)
  (or (atom l)
      (and (hons-get (car l) al)
           (hons-subset1 (cdr l) al))))

(defn hons-subset2 (l1 l2)
  (cond ((atom l1) t)
        ((hons-member-equal (car l1) l2)
         (hons-subset2 (cdr l1) l2))))

(defn hons-subset (l1 l2)
  (cond ((worth-hashing l2)
         (with-fast-list fl2 l2 '*hons-subset-alist*
                         (hons-subset1 l1 fl2)))
        (t (hons-subset2 l1 l2))))

(defn hons-set-equal (l1 l2)
  (and (hons-subset l1 l2)
       (hons-subset l2 l1)))




; DEFHONST -----------------------------------------------------------------

;; [Jared]: bozo new hons means defhonst changes...

;; Defhonst is like defconst.

;; The record for all defhonst values is kept in the ACL2 global
;; 'defhonst.  To flush all defhonst records manually, one may:
;; (f-put-global 'defhonst nil state).


; [Jared]: if defhonst is really like defconst, then why have it?  What's the
; difference?  Why is it desirable?  We should have some documentation for it.
; It seems there are a couple of consequences of using defhonst, e.g.,
; persistent hons table, evisceration, etc.


;; [Jared]: removed this, but not sure what it was for.

;; (defmacro update-defhonst (f r)
;;   `(let ((f ,f) (r ,r))
;;      (pprogn
;;       (f-put-global
;;        'defhonst
;;        (hons (hons (cadr r)
;;                    (concatenate 'string "," (symbol-name f)))
;;              (if (boundp-global 'defhonst state)
;;                  (get-global 'defhonst state)
;;                nil))
;;        state)
;;       (value f))))



(defmacro defhonst (name form &key (evisc 'nil eviscp) check doc)

; From Matt Mon Sep 29 09:53:49 CDT 2008

  (declare (ignore doc))
  `(with-output
    :off summary
    (progn
      ;; [Jared]: switched to hons-copy-persistent
; Matt K. mod: Eliminate doc argument for defconst (disallowed after ACL2 8.3).
      (defconst ,name (hons-copy-persistent ,form))
      (table evisc-table
             ,name
             ,(if eviscp
                  evisc
                (let ((str (symbol-name name)))
                  (if (may-need-slashes str)
                      (concatenate 'string "#.|" str "|")
                    (concatenate 'string "#." str)))))

;; [Jared]: removed the table event
;;       (table persistent-hons-table
;;              (let ((x ,name))
;;                (if (or (consp x) (stringp x))

;; ; honsp-check without check

;;                    x
;;                  nil))
;;              t)
      ,@(and check
             `((assert-event ,check)))
      (value-triple ',name))))




; UNRELATED TO HONS --------------------------------------------------------

; [Jared]: BOZO why is this stuff in hons-help.lisp?  What does any of this
; have to do with hons?  Can we move this elsewhere?

; [Jared]: moved plev stuff to tools/plev.lisp


; [Jared] removing FAIL from the manual to discourage its use.  I generally
; think we should encourage the use of ER or IMPOSSIBLE instead.

  ;; "There are no axioms about FAIL except the equality axioms.

  ;;  One can prove:

  ;;         (thm (implies (and (equal x1 x2) (equal y1 y2))
  ;;                       (equal (fail x1 y1) (fail x2 y2))))

  ;;  However, if FAIL is called at run-time, an error occurs.

  ;;  FAIL can perhaps be understood in analogy with the notion of a
  ;;  'resource error'.  Though one can prove:

  ;;     (thm (implies (posp n) (consp (make-list n))))

  ;;  what will happen if one invokes (make-list (expt 2 2000))?  It is
  ;;  hard to predict, but eventually, something like an error will
  ;;  occur."

(defstub fail (x y)
; [Jared]: find a better place for this?
  t)

