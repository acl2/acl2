; In this file, we demonstrate a way to define a memory that uses fast records
; for its implementation but allows the user to define some extra properties
; about their implementation (for example, the types of the keys and/or
; values).

; The value in this file is that it provides a way of learning about one user's
; way of manipulating records that didn't require reasoning about low-level
; functions like ifrp.

; I forget at the moment what my aversion to using
; books/workshops/2003/greve-wilding_defrecord/support/defrecord.lisp was when
; writing this, but it provides similar functionality.

(in-package "ACL2")

(include-book "defexec/other-apps/records/records" :dir :system)

(include-book "std/util/defalist" :dir :system)
(include-book "misc/defun-plus" :dir :system)

(defn memory-val-p (x)
  (declare (ignore x))
  t)

(defn memory-p1 (lst)
  (cond ((atom lst)
         (null lst))
        (t (and (consp (car lst))
                (natp (caar lst))
                (memory-val-p (cdar lst))
                (memory-p1 (cdr lst))))))

(defn memory-p (x)
  (and (memory-p1 x)
       (good-map x)))

(defun+ empty-memory-p (mem)

; The use of this predicate is a little silly.

  (declare (xargs :guard (memory-p mem)))
  (null mem))

(defun+ empty-memory () ; initial empty memory
  (declare (xargs :guard t
                  :output (and (memory-p (empty-memory))
                               (empty-memory-p (empty-memory)))))
  nil)

(defun update-loc (i val mem)
  (declare (xargs :guard (and (memory-p mem)
                              (natp i)
                              (memory-val-p val))))
  (mset i val mem))

(in-theory (enable extensible-records))

(defun+ update-loc (i val mem)
  (declare (xargs :guard (and (memory-p mem)
                              (natp i)
                              (memory-val-p val))
                  :output (memory-p (update-loc i val mem))))
  (mset i val mem))

(defun+ lookup-loc (i mem)
  (declare (xargs :guard (and (memory-p mem)
                              (natp i))
                  :output (memory-val-p (lookup-loc i mem))))
  (mget i mem))

(in-theory (disable extensible-records))

(defthm read-of-write
  (equal (lookup-loc i (update-loc i val mem))
         val))

(defthm read-of-non-write
  (implies (not (equal i j))
           (equal (lookup-loc i (update-loc j val mem))
                  (lookup-loc i mem))))

(defthm write-of-write
  (equal (update-loc i val (update-loc i val2 mem))
         (update-loc i val mem)))


(defthm read-of-empty-mem
  (implies (empty-memory-p mem)
           (equal (lookup-loc i mem)
                  nil)))

(in-theory (disable update-loc lookup-loc empty-memory-p empty-memory))
