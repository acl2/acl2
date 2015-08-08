;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;
;;;;               Exercise 1.3
;;;;
;;;;   Load with (ld "Exercise1.3.lisp")
;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(in-package "ACL2")



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; Section 1: Memory definitions
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


;;;
;;; Memory accessor and constructor
;;;
;;; - (get-cell pos mem) : retrieves pos-th element of the mem memory list
;;; - (put-cell pos cell mem) : puts the cell at position pos in the mem memory list
;;;   (nil elements are inserted if necessary)
;;;


(defun put-cell (position cell typed-mem)
                (cons (cons position cell) typed-mem))

(defun get-cell (pos mem) (cdr (assoc-equal pos mem)))


;;;
;;; Some key properties of put-cell and get-cell
;;;
;;; - get-cell retrieves the value inserted by put-cell.
;;; - (put-cell var1 val mem) has no effect to variables other than var1.
;;; - put-cell is alistp-preserving.
;;;

(defthm get-retrieves-put-value
 (equal (get-cell position (put-cell position cell typed-mem)) cell))


(defthm put-cell-does-not-change-other-vars
 (implies
  (not (equal var1 var2))
  (equal (get-cell var1 (put-cell var2 val mem)) (get-cell var1 mem))))

(defthm put-keeps-alistp
 (implies
  (alistp mem)
  (alistp (put-cell position cell mem))))



;;;
;;; Definition of equality between memories
;;;
;;; - first we define equality w.r.t. the set of variables
;;;   contained in one memory. Namely:
;;;   (equal-wrt-vars mem mem1 mem2) holds T iff every variable of mem has the
;;;   same value in mem1 and mem2.
;;; - then we define equality between memories based on equal-wrt-vars
;;;

(defun equal-wrt-vars (mem mem1 mem2)
  (cond
   ( (endp mem)
     t )
   ( (equal
      (get-cell (caar mem) mem1)
      (get-cell (caar mem) mem2))
     (equal-wrt-vars (cdr mem) mem1 mem2))
   ( t
     nil)))

(defun equal-memories (mem1 mem2)
  (and
   (equal-wrt-vars mem1  mem1 mem2)
   (equal-wrt-vars mem2  mem1 mem2)))

;;;
;;; Proof of the first statement required by the exercise.
;;;
;;; We prove that, if mem1 and mem2 are equal in the sense
;;; of equal-memories, then every variable has the same value in
;;; mem1 and mem2.
;;; We reason by cases.
;;; First we prove it in the case where a
;;; variable belongs to one or both of mem1 and mem2.
;;; Then we prove it in the case where a variable
;;; does not belong to mem1 or mem2.
;;; Finally we put the cases together.
;;;

(defthm equality-wrt-vars-means-every-var-has-same-value
 (implies
  (and
   (assoc-equal v mem)
   (equal-wrt-vars mem mem1 mem2))
  (equal
      (get-cell v mem1)
      (get-cell v mem2))))




(defthm a-variable-of-either-memory-is-equal-if-memories-are-equal
 (implies
  (and
   (or
    (assoc-equal v mem1)
    (assoc-equal v mem2))
   (equal-memories mem1 mem2))
  (equal
      (get-cell v mem1)
      (get-cell v mem2)))
 :hints (("Goal" :use
	 ((:instance equality-wrt-vars-means-every-var-has-same-value (mem mem1))
	  (:instance equality-wrt-vars-means-every-var-has-same-value (mem mem2))))))


(defthm a-variable-of-neither-memory-is-equal-if-memories-are-equal
 (implies
  (and
   (not (assoc-equal v mem1))
   (not (assoc-equal v mem2))
   (equal-memories mem1 mem2))
  (equal
      (get-cell v mem1)
      (get-cell v mem2))))


(defthm equal-memories-means-all-possible-variables-match-no-matter-what
 (implies
  (equal-memories mem1 mem2)
   (equal
      (get-cell v mem1)
      (get-cell v mem2)))
 :hints (("Goal" :use (a-variable-of-neither-memory-is-equal-if-memories-are-equal
		       a-variable-of-either-memory-is-equal-if-memories-are-equal))))



;;;
;;; Proof of the second statement required by the exercise.
;;;
;;; We develop the proof as follows:
;;; - first we prove that equal-wrt-vars is an equivalence relation,
;;;   i.e. that it is reflexive, commutative and transitive.
;;; - then, we use the fact that equal-wrt-vars is an equivalence relation
;;;   to derive that equal-memories is an equivalence relation too.
;;;   We also use the fact that (equal-memories mem1 mem2) implies
;;;   (equal-wrt-vars mem3 mem1 mem2) for every possible mem3.
;;;


(defthm equal-wrt-vars-reflexive
 (equal-wrt-vars mem0 mem mem))

(defthm equal-wrt-vars-commutative
  (iff
   (equal-wrt-vars mem0 mem1 mem2)
   (equal-wrt-vars mem0 mem2 mem1)))

(defthm equal-wrt-vars-transitive
 (implies
  (and
   (equal-wrt-vars mem0 mem1 mem2)
   (equal-wrt-vars mem0 mem2 mem3))
  (equal-wrt-vars mem0 mem1 mem3)))




(defthm equal-memories-reflexive
 (equal-memories mem mem))


(defthm equal-memories-commutative
  (iff
   (equal-memories mem1 mem2)
   (equal-memories mem2 mem1)))




(defthm equal-memories-extends-to-all-vars
 (implies
  (equal-memories mem1 mem2)
 (equal-wrt-vars mem3 mem1 mem2))
 :hints (("Subgoal *1/3" :use
          (:instance equal-memories-means-all-possible-variables-match-no-matter-what
                     (v (caar mem3))))))







(defthm equal-memories-transitive
 (implies
  (and
   (equal-memories mem1 mem2)
   (equal-memories mem2 mem3))
  (equal-memories mem1 mem3))
 :hints (("Goal" :use
	  ((:instance equal-memories (mem1 mem1) (mem2 mem2))
	   (:instance equal-memories-extends-to-all-vars)
	   (:instance equal-wrt-vars-transitive (mem0 mem3))))))




