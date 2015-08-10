(in-package "ACL2")

(include-book "defrecord")
(include-book "arithmetic/top-with-meta" :dir :system)

#|

  Access Guards for Address Enumeration

  This file demonstrates the use of "access guards" to enable address
enumeration reasoning for reflexive functions operating on a linear
address space.  Access guards play a role similar to what we find in
recursion guards. A recursion guard is an additional, natural number
argument added to the signature of a recursive function.  The
recursion guard is checked in each recursive call. If the guard is
zero, the function terminates. If not, the body of the function is
applied to the arguments and any recursive calls decrement the
recursion guard. The recursion guard provides a trivial measure by
which we can admit functions with arbitrarily complex measure
functions.  Additionally, once a suitable measure is established, one
can prove the equivalence of the guarded function and a version of the
same function without the recursion guard.

  An access guard, likewise, is an additional argument added to the
signature of a function. At the beginning of the function the access
guard is checked against all of the memory transactions that may be
performed by the body of the function. If any of the transactions are
not allowed according to the access guard, the function returns an
unmodified memory. If all of the transactions are allowed, the body of
the function is applied to its arguments and the access guard is
passed on to any recursive calls.

David Greve
8/24/2003

|#

;;
;; First, a few theorems about append ..
;;

(defthm len-append
  (equal (len (append x y))
	 (+ (len x) (len y))))

(defun len-len-induction (x y)
  (if (and (consp x) (consp y))
      (len-len-induction (cdr x) (cdr y))
    (cons x y)))

(defthm append-equality-reduction
  (implies
   (and
    (true-listp w)
    (true-listp y)
    (equal (len w) (len y)))
   (equal (equal (append w x)
		 (append y z))
	  (and (equal w y)
	       (equal x z))))
  :hints (("goal" :induct (len-len-induction w y))))

;; ===================================================================
;;
;; Here are some functions we use to describe relationships among
;; addresses.  It is essential to have a good library of functions
;; such as these in order to enable effective reasoning using address
;; enumeration.
;;
;; ===================================================================

(defun memberp (x list)
  (if (consp list)
      (or (equal x (car list))
	  (memberp x (cdr list)))
    nil))

(defun disjoint (list1 list2)
  (if (consp list1)
      (and (not (memberp (car list1) list2))
	   (disjoint (cdr list1) list2))
    t))

(defun subset (list1 list2)
  (if (consp list1)
      (and (memberp (car list1) list2)
	   (subset (cdr list1) list2))
    t))

;;
;; Here are some of the essential properties of these relational
;; functions.
;;

(defthm disjoint-commute
  (equal (disjoint a b)
	 (disjoint b a))
  :rule-classes ((:rewrite :loop-stopper ((b a)))))

(defthm subset-cdr
  (implies
   (and
    (consp y)
    (subset x (cdr y)))
   (subset x y)))

(defthm subset-x-x
  (subset x x))

(defthm subset-append
  (equal (subset (append x y) z)
	 (and (subset x z)
	      (subset y z))))

(defthm disjoint-append
  (equal (disjoint (append x y) z)
	 (and (disjoint x z)
	      (disjoint y z))))

(defthm disjoint-append-right
  (equal (disjoint z (append x y))
	 (and (disjoint z x)
	      (disjoint z y))))

(defthm disjoint-cons-right
  (implies
   (consp z)
   (equal (disjoint a z)
	  (and (not (memberp (car z) a))
	       (disjoint a (cdr z))))))

(defthm member-append
  (equal (memberp a (append x y))
	 (or (memberp a x)
	     (memberp a y))))

(defthm non-membership-from-disjoint-membership
  (implies
   (and
    (memberp a list)
    (disjoint x list))
   (not (memberp a x))))


(defthm inequality-from-membership
  (implies
   (and
    (memberp a defs)
    (not (memberp b defs)))
   (iff (equal a b) nil)))

(defthm inequality-from-membership-2
  (implies
   (and
    (not (memberp a defs))
    (memberp b defs))
   (iff (equal a b) nil)))

;; ===================================================================
;;
;; Here we define our function of interest: mark-raw
;;
;; ===================================================================


;;
;; Use a typed record to avoid "fixing" everything ..
;;

(defrecord ram
  :rd rd
  :wr wr
  :typep integerp
  :fix   ifix
  )


;; Here is some ASCII art that represents the data structure our
;; function will operate on.  Note that pointers are implemented as
;; addresses in the linear address space (the ram) containing this
;; data structure and not as "true" substructures.

;;        +--------+        +--------+
;; ptr -> |  ptr0  |------->|        |
;;        +--------+           ....
;;        |  val1  |        +--------+
;;        +--------+
;;        |  val2  |
;;        +--------+
;;        |  val3  |
;;        +--------+        +--------+
;;        |  ptr4  |------->|        |
;;        +--------+           ....
;;		            +--------+

;; Here is our function of interest.  This function follows all of the
;; pointers in our data structure (to a depth of n), overwriting the
;; val3 field of each node in the structure with the sum of the values
;; in the val1 and val2 slots. Notice that, because we are chasing two
;; pointers from each node, mark-raw must be reflexive.
;;

(defun mark-raw (n ptr ram)
  (if (zp n) ram
    (let ((val2 (rd (+ ptr 2) ram))
	  (val3 (rd (+ ptr 3) ram)))
      (let ((ram (wr (+ ptr 3) (+ val2 val3) ram)))
	(let ((ram (mark-raw (1- n) (rd ptr ram) ram)))
	  (mark-raw (1- n) (rd (+ ptr 4) ram) ram))))))

;; Sometimes ACL2 doesn't like to open reflexive functions ..

(defthm open-mark-raw
  (implies
   (not (zp n))
   (equal (mark-raw n ptr ram)
	  (let ((v2 (rd (+ ptr 2) ram))
		(v3 (rd (+ ptr 3) ram)))
	    (let ((ram (wr (+ ptr 3) (+ v2 v3) ram)))
	      (let ((ram (mark-raw (1- n) (rd ptr ram) ram)))
		(mark-raw (1- n) (rd (+ ptr 4) ram) ram)))))))

;; -------------------------------------------------------------------

;; The structure of the implicit data structure modified by mark-raw
;; can be characterized by the pointers stored at the following memory
;; locations (relative to ptr)

(defun mark-body-str (ptr)
  (list ptr (+ ptr 4)))

;; We write a function to enumerate all of the addresses in our memory
;; that are used to store pointers.  These addresses define the
;; "structure" of our data structure.

;; -------------------------------------------------------------------

(defun mark-str (n ptr ram)
  (if (zp n) nil
    (let ((list0 (mark-str (1- n) (rd ptr ram) ram)))
      (let ((list4 (mark-str (1- n) (rd (+ ptr 4) ram) ram)))
	(append (mark-body-str ptr)
		list0
		list4)))))

(defthm open-mark-str
  (implies
   (not (zp n))
   (equal (mark-str n ptr ram)
	  (let ((list0 (mark-str (1- n) (rd ptr ram) ram)))
	    (let ((list4 (mark-str (1- n) (rd (+ ptr 4) ram) ram)))
	      (append (mark-body-str ptr)
		      list0
		      list4))))))

(defthm true-listp-mark-str
  (true-listp (mark-str n ptr ram)))

(defun n-n-induction (n1 ptr1 ram1 n2 ptr2 ram2)
  (if (or (zp n1) (zp n2)) (list ptr1 ptr2)
    (+ (n-n-induction (1- n1) (rd ptr1 ram1) ram1
		      (1- n2) (rd ptr2 ram2) ram2)
       (n-n-induction (1- n1) (rd (+ ptr1 4) ram1) ram1
		      (1- n2) (rd (+ ptr2 4) ram2) ram2))))

(defthm len-mark-str
  (implies
   (equal (nfix n1) (nfix n2))
   (equal (equal (len (mark-str n1 ptr1 ram1))
		 (len (mark-str n2 ptr2 ram2)))
	  t))
  :hints (("goal" :induct (n-n-induction n1 ptr1 ram1 n2 ptr2 ram2))))

(defthm mark-str-over-wr
  (implies
   (not (memberp a (mark-str n ptr ram)))
   (equal (mark-str n ptr (wr a v ram))
	  (mark-str n ptr ram))))

;; -------------------------------------------------------------------
;;
;; The following memory locations (relative to ptr) are considered
;; "data fields", which mark-raw is free to modify ..

(defun mark-body-defs (ptr)
  (list (+ ptr 1) (+ ptr 2) (+ ptr 3)))

;;
;; We can also write a function to enumerate all of the addresses in
;; our memory space that are used to store data structure values.
;;
;; -------------------------------------------------------------------

(defun mark-defs (n ptr ram)
  (if (zp n) nil
    (let ((list0 (mark-defs (1- n) (rd ptr ram) ram)))
      (let ((list4 (mark-defs (1- n) (rd (+ ptr 4) ram) ram)))
	(append (mark-body-defs ptr)
		list0
		list4)))))


;; Note that the following is a pretty strong rule .. we usually
;; disable it.

(defthmd open-mark-defs
  (implies
   (syntaxp (symbolp n))
   (equal (mark-defs n ptr ram)
	  (if (zp n) nil
	    (let ((list0 (mark-defs (1- n) (rd ptr ram) ram)))
	      (let ((list4 (mark-defs (1- n) (rd (+ ptr 4) ram) ram)))
		(append (mark-body-defs ptr)
			list0
			list4)))))))

(defthm true-listp-mark-def
  (true-listp (mark-defs n ptr ram)))

(defthm len-mark-def
  (implies
   (equal (nfix n1) (nfix n2))
   (equal (equal (len (mark-defs n1 ptr1 ram1))
		 (len (mark-defs n2 ptr2 ram2)))
	  t))
  :hints (("goal" :induct (n-n-induction n1 ptr1 ram1 n2 ptr2 ram2))))

;; Note that mark-str is "more fundamental" than mark-defs .. which
;; is to say that mark-defs depends upon mark-str in the following
;; manner ..

(defthm mark-def-over-wr
  (implies
   (not (memberp a (mark-str n ptr ram)))
   (equal (mark-defs n ptr (wr a v ram))
	  (mark-defs n ptr ram))))

;; ===================================================================
;;
;; Here we define a guarded version of the function of interest
;;
;; ===================================================================


;; Note that on each iteration, mark-guard makes sure that it is OK
;; for it to write to the value fields of the data structure, based
;; on the "defs" parameter ..

(defun mark-guard (defs n ptr ram)
  (if (subset (mark-body-defs ptr) defs)
      (if (zp n) ram
	(let ((v2 (rd (+ ptr 2) ram))
	      (v3 (rd (+ ptr 3) ram)))
	  (let ((ram (wr (+ ptr 3) (+ v2 v3) ram)))
	    (let ((ram (mark-guard defs (1- n) (rd ptr ram) ram)))
	      (mark-guard defs (1- n) (rd (+ ptr 4) ram) ram)))))
    ram))

(defthm open-mark-guard
  (implies
   (not (zp n))
   (equal (mark-guard defs n ptr ram)
	  (if (subset (mark-body-defs ptr) defs)
	      (if (zp n) ram
		(let ((v2 (rd (+ ptr 2) ram))
		      (v3 (rd (+ ptr 3) ram)))
		  (let ((ram (wr (+ ptr 3) (+ v2 v3) ram)))
		    (let ((ram (mark-guard defs (1- n) (rd ptr ram) ram)))
		      (mark-guard defs (1- n) (rd (+ ptr 4) ram) ram)))))
	    ram))))

;; -------------------------------------------------------------------
;;
;; With the guarded function, it is easy to show the following,
;; essential read over write property ..
;;
;; -------------------------------------------------------------------

(defthm rd-over-mark-guard
  (implies
   (not (memberp a defs))
   (equal (rd a (mark-guard defs n ptr ram))
	  (rd a ram)))
  :hints (("goal" :in-theory (enable rd-of-wr-redux))))

;; With that fact in hand, we observe:

(defthm mark-str-over-mark-guard
  (implies
   (disjoint (mark-str m ptr ram) list)
   (equal (mark-str m ptr (mark-guard list n ptrx ram))
	  (mark-str m ptr ram)))
  :hints (("goal" :induct (mark-str m ptr ram))))

(defthm mark-defs-over-mark-guard
  (implies
   (disjoint (mark-str m ptr ram) list)
   (equal (mark-defs m ptr (mark-guard list n ptrx ram))
	  (mark-defs m ptr ram)))
  :hints (("goal" :induct (mark-defs m ptr ram))))

;; -------------------------------------------------------------------
;;
;; It is also possible to prove this essential commuting property ..
;;
;; -------------------------------------------------------------------

(defthm mark-guard-over-wr
  (implies
   (and
    (not (memberp a defs))
    (not (memberp a (mark-str n ptr ram)))
    (disjoint (mark-str n ptr ram) defs))
   (equal (mark-guard defs n ptr (wr a v ram))
	  (wr a v (mark-guard defs n ptr ram))))
  :hints (("goal" :induct (mark-guard defs n ptr ram))))

;;
;; It is frustrating that we have to do this to guide the theorem
;; prover into performing the correct substitutions during the
;; induction ..
;;

(defun rewrite= (x y)
  (equal x y))

(defthm equal-implies-rewrite=
  (implies
   (equal x y)
   (rewrite= x y)))

(defthmd equal-from-rewrite=
  (implies
   (rewrite= x y)
   (equal (equal x y) t)))

(defthm mark-guard-rewrite=-sub
  (implies
   (rewrite= x y)
   (equal (mark-guard list n ptr x)
	  (mark-guard list n ptr y))))

(defthm mark-raw-rewrite=-sub
  (implies
   (rewrite= x y)
   (equal (mark-raw n ptr x)
	  (mark-raw n ptr y))))

(defthm rd-rewrite=-sub
  (implies
   (rewrite= x y)
   (equal (rd a x)
	  (rd a y))))

(in-theory
 (disable
  rewrite=
  ))

;;
;; Here is the key, generalized theorem connecting mark-raw and
;; mark-guard
;;

(defthm mark-raw-to-mark-guard-reduction
  (implies
   (and
    (integerp ptr)
    (subset (mark-defs n ptr ram) list)
    (disjoint (mark-str n ptr ram) list))
   (iff (rewrite= (mark-raw n ptr ram)
		       (mark-guard list n ptr ram)) t))
  :hints (("goal" :in-theory (enable open-mark-defs rd-of-wr-redux)
	   :induct (mark-guard list n ptr ram))))

;;
;; This is how we do it in practice ..
;;

(defthmd mark-raw-to-mark-guard
  (implies
   (and
    (integerp ptr)
    (disjoint (mark-str n ptr ram)
	      (mark-defs n ptr ram)))
   (equal (mark-raw n ptr ram)
	  (mark-guard (mark-defs n ptr ram) n ptr ram)))
  :hints (("goal" :in-theory (enable equal-from-rewrite=))))

;; ===================================================================
;;
;; The following theorems are the key result lemmas and are essential
;; building blocks for other, more useful theorems involving mark-raw.
;;
;; Note that we were only able to prove these by first proving them
;; for mark-guard, the guarded version of mark-raw.
;;
;; ===================================================================

(defthm rd-over-mark-raw
  (implies
   (and
    (integerp ptr)
    (disjoint (mark-str n ptr ram)
	      (mark-defs n ptr ram))
    (not (memberp a (mark-defs n ptr ram))))
   (equal (rd a (mark-raw n ptr ram))
	  (rd a ram)))
  :hints (("goal" :in-theory (enable mark-raw-to-mark-guard))))

(defthm mark-raw-over-wr
  (implies
   (and
    (integerp ptr)
    (not (memberp a (mark-defs n ptr ram)))
    (not (memberp a (mark-str n ptr ram)))
    (disjoint (mark-str n ptr ram)
	      (mark-defs n ptr ram)))
   (equal (mark-raw n ptr (wr a v ram))
	  (wr a v (mark-raw n ptr ram))))
  :hints (("goal" :in-theory (enable mark-raw-to-mark-guard))))

