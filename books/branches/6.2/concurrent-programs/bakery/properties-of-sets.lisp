(in-package "ACL2")
(include-book "records")


#|

 properties-of-sets.lisp
 ~~~~~~~~~~~~~~~~~~~~~~~

In this book, we introduce several functions dealing with properties
of sets, like subsetp. (Note, we use a new function my-subsetp as
opposed to ACL2's subsetp, because I want to be uniform in the
membership test using the memberp function as opposed to the member
function used in subsetp.) We treat sets as ordered lists of base
elements for the purposes of this book, and always assume a total
order of the elements involved.

We make no claims with respect to the completeness of these functions and
theorems for flat sets. Still, our experience with bakery tells us that these
form a practical and good set of rules while dealing with sets.

|#

(defun my-subsetp (x y)
  (if (endp x) T
    (and (memberp (car x) y)
	 (my-subsetp (cdr x) y))))

(defthm proper-subset-is-subset
  (implies (my-subsetp x y) (my-subsetp x (cons a y))))

(defthm my-subsetp-is-reflexive
  (my-subsetp x x))

(in-theory (disable proper-subset-is-subset))

(defthm my-subsetp-is-transitive
  (implies (and (my-subsetp x y)
		(my-subsetp y z))
	   (my-subsetp x z)))

(defthm my-subsetp-insert-reduction
  (implies (my-subsetp indices keys)
	   (my-subsetp indices (insert in keys))))

;; We now treat the set as a queue and turn to properties of
;; queues. The key concept of a queue is that of a "previous element".

(defun previous (x i)
  (if (endp x) nil
   (if (equal i (first x)) nil
    (cons (first x)
	  (previous (rest x) i)))))

(defthm not-memberp-previous-reduction
  (implies (not (memberp curr queue))
		(not (memberp curr (previous queue in)))))

(defthm subsetp-memberp-reduction
  (implies (and (not (memberp (car k) queue))
		(my-subsetp queue k))
	   (my-subsetp queue (cdr k))))

(defthm my-subsetp-previous-reduction
  (implies (my-subsetp queue keys)
	   (my-subsetp (previous queue in) keys)))

(defthm not-subsetp-memberp-reduction
  (implies (and (not (memberp in keys))
		(my-subsetp queue keys))
	   (not (memberp in queue)))
  :rule-classes :forward-chaining)

(defthm memberp-append-reduction
  (iff (memberp in (append queue bucket))
       (or (memberp in queue)
	   (memberp in bucket))))

(defthm memberp-previous-append-reduction
  (implies (memberp a queue)
	   (equal (previous (append queue bucket) a)
		  (previous queue a))))

(defthm subset-consp-reduction
  (implies (and (my-subsetp a b)
                (not (consp b)))
           (not (consp a)))
  :rule-classes :forward-chaining)

(defthm previous-consp-reduction
  (implies (and (memberp in queue)
                (not (consp (previous queue in))))
           (equal (car queue) in))
  :hints (("Goal"
           :expand (previous queue in)))
  :rule-classes :forward-chaining)

(in-theory (disable my-subsetp previous))

;; We introduce now, functions defining the intersection of sets, and
;; the concept of disjoint sets, and prove some properties relating
;; the two concepts.

(defun intersect (x y)
  (if (endp x) nil
    (if (memberp (first x) y)
	(cons (first x) (intersect (rest x) y))
      (intersect (rest x) y))))

(defun disjoint (x y)
  (not (intersect x y)))

(defthm disjoint-implies-one-not-member
  (implies (and  (disjoint x y)
		 (memberp i x))
	   (not (memberp i y))))

(defthm disjoint-implies-one-not-member-symmetric
  (implies (and (disjoint x y)
		(memberp i y))
	   (not (memberp i x))))

(defthm intersect-null-consp
  (implies (not (intersect bucket queue))
	   (not (intersect bucket (cdr queue)))))

(defthm disjoint-implies-disjoint-cdr
  (implies (disjoint bucket queue)
	   (disjoint bucket (cdr queue))))

(defthm disjoint-cons-reduction
  (implies (not (disjoint bucket queue))
           (not (disjoint (cons e bucket) queue))))

(in-theory (disable disjoint intersect))

