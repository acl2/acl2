

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; Section 2: Memory definitions
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;;
;;; Although actual Gem and Rtm memories are not typed, they contain values of typed
;;; variables (for Gem, booleans and 'long' integers; for Rtm, only 'short' integers).
;;; In order to simplify our proofs (by not to have to refer to variable declaration
;;; lists to recognize the types of variables into memories), we define memories as being
;;; typed.
;;;
;;; First we define the notion of (Gem or Rtm) typed memory cell, by providing a
;;; recognizer, a constructor and a set of accessors to the typed cell's elements.
;;;
;;; Then we define a (Gem or Rtm) typed memory as a list of typed cells:
;;; we provide an accessor, a constructor and a recognizer.
;;;
;;; Finally we define accessors that 'slice' memories, extracting only
;;; the types, the values or the attributes of the cells.
;;;


;;;
;;; Typed memory cell
;;;
;;; A typed memory cell is a three-elements list of the form < value attribute type >,
;;; where :
;;; - value is an integer
;;; - attribute is one of 'input, 'output
;;; - type is one of 'int, 'bool
;;;


(in-package "ACL2")

(defun make-cell (value attribute type-var)
 (list value attribute type-var))

(defun var-value (memcell)
 (car memcell))

(defun var-attribute (memcell)
 (cadr memcell))

(defun var-type (memcell)
 (caddr memcell))


(defthm var-attribute-retrieves-attribute
 (equal (var-attribute (make-cell value attribute type)) attribute))


(defun my-or-3 (a b c) (or a b c))

(defun my-or-2 (a b)   (or a b))


(defun is-mem-cell-p (memcell)
 (and
   (true-listp memcell)
   (equal (len memcell) 3)
   (integerp (var-value memcell))
   (my-or-3
    (equal (var-attribute memcell) 'input)
    (equal (var-attribute memcell) 'output)
    (equal (var-attribute memcell) 'internal))
   (my-or-2
    (equal (var-type memcell) 'int)
    (and
     (my-or-2
      (equal (var-value memcell) 0)
      (equal (var-value memcell) 1))
     (equal (var-type memcell) 'bool)))))


(defthm non-boolean-cell-is-integer
 (implies
  (and
   (is-mem-cell-p cell)
   (not (equal (var-type cell) 'bool)))
   (equal (var-type cell) 'int)))

(defthm non-integer-cell-is-boolean
 (implies
  (and
   (is-mem-cell-p cell)
   (not (equal (var-type cell) 'int)))
   (equal (var-type cell) 'bool)))




;;;
;;; Memory accessor, constructor, recognizer
;;;
;;; - (get-cell pos mem) : retrieves pos-th element of the mem memory list
;;; - (put-cell pos cell mem) : puts the cell at position pos in the mem memory list
;;;   (nil elements are inserted if necessary)
;;;


(defun put-cell (position cell typed-mem)
                (cons (cons position cell) typed-mem))


#|
(defun put-cell (position cell typed-mem)
  (cond
   ( (endp typed-mem)
     (cons (cons position cell) typed-mem) )
   ( (equal (caar typed-mem) position)
     (cons (cons position cell) (cdr typed-mem) ) )
   ( t
    (cons (car typed-mem) (put-cell position cell (cdr typed-mem))))))
|#


(defun get-cell (pos mem) (cdr (assoc-equal pos mem)))



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
;;;
;;; Memory slicing accessors: var-attributes, var-values and var-types
;;; They retrieve only the corresponding components of a list of memory cells.
;;;


(in-theory (disable var-attribute var-type var-value))

(defun var-attributes (vars mem)
 (if (endp vars)
     nil
     (cons
      (var-attribute (get-cell (car vars) mem))
      (var-attributes (cdr vars) mem))))


(defun var-values (vars typed-mem)
 (if
  (endp vars)
  nil
  (cons (var-value (get-cell (car vars) typed-mem))
        (var-values (cdr vars) typed-mem))))



(defthm var-values-of-1-variable-is-one-element-list-of-var-value
 (implies
  (and
   (true-listp vars)
   (equal (len vars) 1))
  (equal
   (var-values vars mem)
   (list (var-value (get-cell (car vars) mem)))))
 :hints (
 ("Subgoal *1/2.2" :use (:theorem
 (implies
  (and
   (true-listp vars)
   (equal (len vars) 1))
  (and
   (equal (len (cdr vars)) 0)
   (true-listp (cdr vars))))))))





(defun equal-wrt-vars (vars mem1 mem2)
  (cond
   ( (endp vars)
     t )
   ( (equal
      (get-cell (caar vars) mem1)
      (get-cell (caar vars) mem2))
     (equal-wrt-vars (cdr vars) mem1 mem2))
   ( t
     nil)))




(defthm equality-wrt-vars-means-every-var-has-same-value
 (implies
  (and
   (assoc-equal v vars)
   (equal-wrt-vars vars mem1 mem2))
  (equal
      (get-cell v mem1)
      (get-cell v mem2))))


(defun equal-memories (mem1 mem2)
  (and
   (equal-wrt-vars mem1  mem1 mem2)
   (equal-wrt-vars mem2  mem1 mem2)))



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
	 ((:instance equality-wrt-vars-means-every-var-has-same-value (vars mem1))
	  (:instance equality-wrt-vars-means-every-var-has-same-value (vars mem2))))))


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





(defthm equal-wrt-vars-reflexive
 (equal-wrt-vars vars mem mem))

(defthm equal-wrt-vars-commutative
  (iff
   (equal-wrt-vars vars mem1 mem2)
   (equal-wrt-vars vars mem2 mem1)))

(defthm equal-wrt-vars-transitive
 (implies
  (and
   (equal-wrt-vars vars mem1 mem2)
   (equal-wrt-vars vars mem2 mem3))
  (equal-wrt-vars vars mem1 mem3)))




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
:hints (("Subgoal *1/3" :use (:instance equal-memories-means-all-possible-variables-match-no-matter-what
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
	   (:instance equal-wrt-vars-transitive (vars mem3))))))






(defun retrieve-vars (vars mem)
  (if (endp vars)
      nil
    (put-cell (caar vars) (get-cell (caar vars) mem) (retrieve-vars (cdr vars) mem))))

(defthm retrieving-vars-has-equality
 (equal-wrt-vars vars (retrieve-vars vars mem) mem))

(defun same-caars-p (l1 l2)
  (if (or
       (endp l1)
       (endp l2))
      (and
       (endp l1)
       (endp l2))
    (and
     (equal (caar l1) (caar l2))
     (same-caars-p (cdr l1) (cdr l2)))))

(defthm same-caars-commutative
  (iff (same-caars-p l1 l2) (same-caars-p l2 l1)))


(defthm if-same-caars-same-equality-wrt-vars
 (implies
  (same-caars-p vars1 vars2)
  (iff
   (equal-wrt-vars vars1 mem1 mem2)
   (equal-wrt-vars vars2 mem1 mem2))))

(defthm retrieve-gets-same-vars
 (same-caars-p (retrieve-vars vars mem) vars))


(defthm equal-wrt-vars-of-retrieve-vars
 (equal-wrt-vars (retrieve-vars vars mem) (retrieve-vars vars mem) mem)
 :hints (("Goal"
	  :use ((:instance if-same-caars-same-equality-wrt-vars
			   (vars1 (retrieve-vars vars mem))
			   (vars2 vars)
			   (mem1 (retrieve-vars vars mem))
			   (mem2 mem))))))





(defun vars-inclusion (vars1 vars2)
  (if (endp vars1)
      t
    (and
     (assoc-equal (caar vars1) vars2)
     (vars-inclusion (cdr vars1) vars2))))


(defthm goal1-40
 (implies
  (and
   (not (endp vars2))
   (equal-wrt-vars vars1 mem1 mem2)
   (vars-inclusion vars2 vars1))
  (equal (get-cell (caar vars2) mem1)
	 (get-cell (caar vars2) mem2))))

(defthm vars-inclusion-keeps-equality
 (implies
  (and
   (equal-wrt-vars vars1 mem1 mem2)
   (vars-inclusion vars2 vars1))
  (equal-wrt-vars vars2 mem1 mem2))
 :hints (("Subgoal *1/4" :use goal1-40)))





(defthm vars-inclusio
 (implies
  (vars-inclusion mem vars)
  (equal-wrt-vars mem (retrieve-vars vars mem) mem))
:hints (("Goal" :use
	 (:instance vars-inclusion-keeps-equality
		    (vars1 vars)
		    (vars2 mem)
		    (mem1 (retrieve-vars vars mem))
		    (mem2 mem)))))


(defthm retrieving-keeps-equality
 (implies
  (and
   (vars-inclusion mem vars)
   (vars-inclusion vars mem))
  (equal-memories (retrieve-vars vars mem) mem))
:hints (("Subgoal 2" :use
	 (vars-inclusio
	  (:instance equal-wrt-vars-commutative
		     (vars mem)
		     (mem1 mem)
		     (mem2 (retrieve-vars vars mem)))))
	("Subgoal 1" :use
	 (equal-wrt-vars-of-retrieve-vars
	  (:instance equal-wrt-vars-commutative
		     (vars (retrieve-vars vars mem))
		     (mem1 mem)
		     (mem2 (retrieve-vars vars mem)))))))



(in-theory (disable
	            get-cell
		    equal-memories-extends-to-all-vars
		    goal1-40
		    vars-inclusio))

;;; cleanup things

(in-theory (disable
	    equality-wrt-vars-means-every-var-has-same-value
	    a-variable-of-either-memory-is-equal-if-memories-are-equal
	    a-variable-of-neither-memory-is-equal-if-memories-are-equal
	    equal-memories-means-all-possible-variables-match-no-matter-what
	    equal-wrt-vars-commutative
	    equal-wrt-vars-transitive
	    equal-memories-transitive
	    equal-memories-reflexive
	    equal-memories-commutative
	    equal-memories-extends-to-all-vars
	    retrieving-keeps-equality))


