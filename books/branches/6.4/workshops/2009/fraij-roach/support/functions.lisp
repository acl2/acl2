(in-package "ACL2")
;;(defun natp (x)
;;  (and (integerp x)
;;       (<= 0 x)))

;; (include-book "books/arithmetic/top")
#|
(ld ;; Newline to fool dependency scanner
  "c:/Program Files/ACL2-2.9.2/sources/supplementary/functions.lisp" :ld-pre-eval-print t)
 
function.lisp
-------------------------------
Author------------------: Fares Fraij
Email-------------------: fares@ahu.edu.jo
Date of last revision---: July 25, 2008
The used version of ACL2: 2.9

 Objective:
 ---------
The goal of this book is to construct the ACL2 model of a restricted Directed
Acyclic Graph (DAG) and supporting functions to model the application of a 
substitution rule to a DAG. The DAG represented in this book represents the 
model of the constant pool of Java.

A DAG is modeled by a list of entries. Each entry is modeled as an alist 
where its car is a natural number, referred to as an index, and its cdr is 
a data object, which informally may be an index, a string, or a structure 
consisting of indexes, strings, or a combination of both. The book also 
defines two crucial concepts: acyclicp and dref. The function acyclicp 
specifies whether an index is acyclic in a constant pool or not. An index is 
acyclic in a constant pool if there are no cycles in DAG of reachable indexes 
in its structure.  The function dref, however, can be thought of as a function 
that, when given a data object model p and a constant pool model cp, will 
directly try to resolve all indexes in p by repeatedly replacing indexes with 
the data found in the corresponding constant pool entry.

|#

;;-------------------------------------------------------------
;; *c1* is an example of a constant pool.
;;-------------------------------------------------------------
(defconst *c1* '((1 . (2 . 3))
                 (2 . (4 . 5))
                 (3 . (6 . 7))
                 (4 . "Four")
                 (5 . "Five")
                 (6 . "Six")
                 (7 . "Seven")))

;;-------------------------------------------------------------
;; lhs is a function that takes as an input a transformation 
;; rule, which consists of two components: 
;; ****** ADD EXAMPLE HERE ***
;;-------------------------------------------------------------
(defun lhs (rule)
  (car rule))

;;-------------------------------------------------------------
;; rhs is a function that takes as an input a transformation 
;; rule, and it returns the right-hand side of the rule.
;;-------------------------------------------------------------
(defun rhs (rule)
  (cdr rule))

;;-------------------------------------------------------------
;; valueOf is a function that takes as inputs the index x and
;; the constant pool cp. If x is an index (i.e., a natp), the 
;; the function returns the object associated with x in cp. 
;; If x is not an index or it is not the head of any entry in 
;; cp, then will return x.
;;-------------------------------------------------------------
(defun valueOf (x cp)
; Every natural has a "binding".
  (if (natp x)
      (if (assoc x cp)
          (cdr (assoc x cp))
        x)
    x))

;;-------------------------------------------------------------
;; put is a function that takes as inputs the index n1, the 
;; object (or the index) n2, and a CP. It finds n1 in cp and, if it is 
;; there, then the function inserts the entry (cons n1 n2) 
;; in its correct location and returns anew cp; otherwise the 
;; cp will not be changed.
;;-------------------------------------------------------------
(defun replaceValue (n1 n2 cp)
  (cond ((endp cp) nil)
        ((equal n1 (car (car cp)))
         (cons (cons n1 n2) (cdr cp)))
        (t (cons (car cp) (replaceValue n1 n2 (cdr cp))))))

;;-------------------------------------------------------------
;; matchIndexRulep is a predicate that takes as inputs the index rhs-entry 
;; and a transformation rule. It returns true if the rhs-entry 
;; and the (lhs rule), which represents the first components of 
;; the rule, are equal; nil otherwise.
;;-------------------------------------------------------------
; assuming that rhs-entry is an index
(defun matchIndexRulep (rhs-entry rule)
  (cond ((equal rhs-entry (lhs rule)) t)
	(t nil)))

;;-------------------------------------------------------------
;; matchValueRulep is a predicate that takes as inputs the object 
;; rhs-entry and a transformation rule. It returns true if there
;; is at least one match between any index of the object 
;; rhs-entry and the rule; nil otherwise.
;;-------------------------------------------------------------
;; the rhs-entry might be either an index or an object  
(defun matchValueRulep (rhs-entry rule)
  (cond ((atom rhs-entry) (matchIndexRulep rhs-entry rule))
	(t (or (matchValueRulep (car rhs-entry) rule)
	       (matchValueRulep (cdr rhs-entry) rule)))))


;;-------------------------------------------------------------
;; any-matchp is a predicate that takes as inputs a list of 
;; transformation rules rule-list, a position (pos), and 
;; constant pool cp. It returns true if there is at least one 
;; match between a rule in the rule-list and the entry of c at 
;; pos.
;;-------------------------------------------------------------
;; assuming that rule-list is ok-rule-listp and c is well-formed
(defun any-matchp (rule-list pos cp)
  (let ((rhs-entry (valueOf pos cp)))
    (if (endp rule-list)
        nil
      (or (matchValueRulep rhs-entry (car rule-list))
          (any-matchp (cdr rule-list) pos cp)))))
  
;;-------------------------------------------------------------
;; some-matchp is a predicate that takes as inputs the list of 
;; transformation rules rule-list, the constant pool tail, and 
;; the constant pool cp. It returns true if there is at least 
;; one match between a rule in the rule-list and any entry of 
;; cp.
;;-------------------------------------------------------------
;; assuming that rule-list is ok-rule-listp, cp is well-formed, 
;; and tail is a subsetp of cp
(defun some-matchp (rule-list tail cp)
  (let ((pos (car (car tail))))
    (cond ((endp tail) nil)
          (t (or (any-matchp rule-list pos cp)
                 (some-matchp rule-list (cdr tail) cp))))))

;;-------------------------------------------------------------
;; applySubstitution is a function that takes as inputs the object 
;; rhs-entry and a transformation rule. It searchs the rhs-entry 
;; looking for indexes that can be matched with the rule, if 
;; there are any, they will be replaced with (lhs rule).
;;-------------------------------------------------------------
(defun applySubstitution (rhs-entry rule)
  (cond ((atom rhs-entry)
         (if (matchIndexRulep rhs-entry rule) 
             (rhs rule)
           rhs-entry))
        (t (cons (applySubstitution (car rhs-entry)
                                rule)
                 (applySubstitution (cdr rhs-entry)
                                rule)))))

;;-------------------------------------------------------------
;; Another set of definitions (functions and predicates) that 
;; represents useful concepts in the proofs ahead (proofs of 
;; termination)
;;-------------------------------------------------------------
;;-------------------------------------------------------------
;; uniqueNodeIDp is a predicate that takes the constant pool 
;; cp as an input, and returns true if cp is a list of pairs, 
;; the first entry of each is a pair that has an index (i.e.,
;; a natural number) as its car. This natural number must NOT be 
;; reassigned anywhere else in the rest of cp.
;;-------------------------------------------------------------
(defun uniqueNodeIDp (cp)
  (cond
   ((atom cp) (equal cp nil))
   (t
    (and (consp (car cp))
         (natp (car (car cp)))
         (not (assoc (car (car cp)) (cdr cp)))
         (uniqueNodeIDp (cdr cp))))))

;;-------------------------------------------------------------
;; no-indexesp is a predicate that takes as an input the object 
;; obj, and returns true if the object obj contains no bounded 
;; indexes in the constant pool cp.
;;-------------------------------------------------------------
(defun no-indexesp (obj)
  (cond ((atom obj)
	 (not (natp obj)))
	(t (and (no-indexesp (car obj))
		(no-indexesp (cdr obj))))))

;;-------------------------------------------------------------
;; all-indexes-in-obj is a function that takes the 
;; object obj, and returns the list of indexes in this 
;; object.
;;-------------------------------------------------------------
(defun all-indexes-in-obj (obj)
  (cond ((atom obj)
         (if (natp obj)
             (list obj)
           nil))
        (t (union-equal (all-indexes-in-obj (car obj))
                        (all-indexes-in-obj (cdr obj))))))

;;-------------------------------------------------------------
;; all-indexes-in-cp is a function that takes the tables, c, 
;; and returns the list of indexes in this table.
;;-------------------------------------------------------------
(defun all-indexes-in-cp (cp)
  (cond ((endp cp) nil)
        (t (union-equal
            (add-to-set-equal (car (car cp))
                              (all-indexes-in-obj (cdr (car cp))))
            (all-indexes-in-cp (cdr cp))))))


;;-------------------------------------------------------------
;; A few simple theorems about sets.
;;-------------------------------------------------------------
(defthm member-union-equal
  (iff (member-equal e (union-equal a b))
       (or (member-equal e a) (member-equal e b))))

(defthm subsetp-union-equal-1
  (implies (subsetp a b) (subsetp a (union-equal b c))))

(defthm subsetp-union-equal-2
  (implies (subsetp a c) (subsetp a (union-equal b c))))

(defthm subsetp-cdr
  (implies (subsetp a (cdr b))
           (subsetp a b)))

(defthm subsetp-reflexive
  (subsetp a a))

;;-------------------------------------------------------------
;; The function setdiff takes two sets as inputs: x and y. It 
;; returns the elements that are in x but not in y.
;;-------------------------------------------------------------
(defun setdiff (x y)
  (cond ((endp x) nil)
        ((member-equal (car x) y) (setdiff (cdr x) y))
        (t (cons (car x) (setdiff (cdr x) y)))))

;;-------------------------------------------------------------
;; some theroems for the prove of termination of acyclicp1
;;-------------------------------------------------------------
(defthm seen-bounded
  (implies (and (member-equal p fixedset)
                (not (member-equal p seen)))
           (< (len (setdiff fixedset
                            (cons p seen)))
              (len (setdiff fixedset
                            seen))))
  :rule-classes :linear)

(defthm assoc-implies-member-all-indexes-in-cp
  (implies (and (natp p)
                (assoc p cp))
           (member-equal p (all-indexes-in-cp cp))))

;;-------------------------------------------------------------
;; This book is needed to prove the termination of the function 
;; acyclicp1. We mainly need to use "llist" and "l<"
;;-------------------------------------------------------------
(include-book "ordinals/lexicographic-ordering" :dir :system)






;;-------------------------------------------------------------
;; The predicate acyclicp1 is the workhorse for the acyclicity 
;; check.  It takes the object p, the constant pool cp, and 
;; a list of all the indexes seen thus far on the current 
;; branch through the object. To admit the predicate acyclicp1, 
;; we defined the measure as the list of length of the 
;; difference between all the indexes in the table cp and the 
;; indexes that has been seen so far and the acl2-count of the 
;; structure p.
;; =========
;; Note that llist is a macro that ensures that the input list 
;; contains naturals. l< expects as arguments lists of 
;; natural numbers or distinct natural numbers. If the arguments 
;; are natural numbers, then l< is the regular <. Otherwise, 
;; it will be t if the length of the first list is less than 
;; the length of the second list. If not, it will check to see
;; if the lists have the same length and the the first one is 
;; lexicographically less than the second one. 
;;-------------------------------------------------------------
(defun acyclicp1 (p dag visited)
  (declare (xargs :measure (llist
                            (len (setdiff (all-indexes-in-cp dag) visited))
                            (acl2-count p))
                  :well-founded-relation l<))
  (cond ((atom p)
         (cond ((natp p)
                (cond ((not (assoc p dag)) nil) ; p must be in the dag
                      ((member-equal p visited) nil) ; p has not been visited
                      (t  ; p is a bare index, get the value and recurse 
		        (acyclicp1 (valueOf p dag) dag (cons p visited)))))
               (t t)))
        (t (and (acyclicp1 (car p) dag visited)
                (acyclicp1 (cdr p) dag visited)))))

;;-------------------------------------------------------------
;; acyclicp is a predicate that takes the object p and the 
;; constant pool cp. It returns true if index p is acyclic in cp, nil 
;; otherwise. This predicate is considered as a wrapper for 
;; acyclicp1.
;;-------------------------------------------------------------
(defun acyclicp (p cp)
  (acyclicp1 p cp nil))



;;-------------------------------------------------------------
;; acount1 is a function that takes three inputs: the object p, 
;; the constant pool cp, and a list of seen indexes so far. It 
;; returns a natural number that represents the number of steps 
;; needed to completely resolve the object p, i.e., it contains
;; no indexes.
;;
;; This function defines a measure of an acyclic structure that
;; decreases as you recur through it.
;;-------------------------------------------------------------
(defun acount1 (p cp visited)
  (declare (xargs :measure (llist
                            (len (setdiff (all-indexes-in-cp cp) visited))
                            (acl2-count p))
                  :well-founded-relation l<))
  (cond ((atom p)
         (cond ((natp p)
                (cond ((not (assoc p cp)) 0)
                      ((member-equal p visited) 0) 
                      (t (+ 1 (acount1 (valueOf p cp) cp (cons p visited))))))
               (t 0)))
        (t (+ 1
              (acount1 (car p) cp visited)
              (acount1 (cdr p) cp visited)))))

;;-------------------------------------------------------------
;; The function acount takes as inputs the object p and the 
;; constant pool cp, and returns a natural number that 
;; represents the number of steps needed until the object p has
;; no indexes.  
;;-------------------------------------------------------------
(defun acount (p cp) 
  (acount1 p cp nil))

;;-------------------------------------------------------------
;; Next, I prove the theorems that establish that acount 
;; decreases as you apply valueOf, car, or cdr to the components of 
;; an appropriate acyclic constant pool.  Of course, I have to prove 
;; the main theorems about acyclic1 and acount1.  I then package 
;; everything up for acyclic and acount.
;;
;; To prove much about acyclic1 and acount1 I need to know that 
;; they treat the list of seen indexes as a set, i.e., they are 
;; insensitive to the order in which indexes are added to the 
;; set.  This is just a congruence theorem about acount1.
;;-------------------------------------------------------------
;;(include-book "/home2/fares/disseration-inverlochy/cf-final/v2/perm-1")
;; (include-book "/u/fares/perm/perm-1")
;;(include-book "c:/Program Files/ACL2-2.9.2/sources/perm/perm-1")

;; **************************************************************
;; The following theorems are imported from JS Moore proofs on 
;; graph theorem.
;; ***************

; [Removed by Matt K. to handle changes to member, assoc, etc. after ACL2 4.2.]
; (defthm member-is-member-equal
;   (equal (member i seen)
;          (member-equal i seen)))

(defun del (x y)
  (if (consp y)
      (if (equal x (car y))
          (cdr y)
        (cons (car y) (del x (cdr y))))
    y))

(defun perm (x y)
  (if (consp x)
      (and (member-equal (car x) y)
           (perm (cdr x) (del (car x) y)))
    (not (consp y))))
; The following could be proved right now.
; (local
;  (defthm perm-reflexive
;    (perm x x)))

(local
 (defthm perm-cons
     (implies (member-equal a x)
              (equal (perm x (cons a y))
                     (perm (del a x) y)))
   :hints (("Goal" :induct (perm x y)))))

;(local
; (defthm perm-symmetric
;     (implies (perm x y) (perm y x))))

(local
 (defthm member-del
     (implies (member-equal a (del b x)) (member-equal a x))))

(local
 (defthm perm-member
     (implies (and (perm x y)
                   (member-equal a x))
              (member-equal a y))))

(local
 (defthm comm-del
     (equal (del a (del b x)) (del b (del a x)))))

(local
 (defthm perm-del
     (implies (perm x y)
              (perm (del a x) (del a y)))))

; We now prove this because we give a hint.

;(local
; (defthm perm-transitive
;     (implies (and (perm x y) (perm y z)) (perm x z))
;   :hints (("Goal" :induct (and (perm x y) (perm x z))))))

(defequiv perm)

(defcong perm perm (cons x y) 2)

(defcong perm iff (member-equal e x) 2)

(defthm member-subsetp-lemma
    (implies (and (subsetp a b)
                  (member-equal v a))
             (member-equal v b)))

(defthm subsetp-del1
    (implies (subsetp a b)
             (subsetp (del e a) b)))

(defthm subsetp-del2
    (implies (and (subsetp (del e a) b)
                  (member-equal e b))
             (subsetp a b)))


(defcong perm iff (subsetp a b) 1)

(defcong perm iff (subsetp a b) 2)


;; **************************************************************
;; End of JS Moore proofs
;;**************************
(defthm acount1-perm-congruence
  (implies (perm seen1 seen2)
           (equal (acount1 p cp seen1) (acount1 p cp seen2)))
  :rule-classes :congruence)


;;-------------------------------------------------------------
;; This next theorem generates a rewrite rule that rewrites 
;; (list* u v seen) to (list* v u seen), when we know the 
;; congruence rule that allows us to rewrite maintaining perm.
;;-------------------------------------------------------------
(defthm perm-list*
  (perm (list* u v seen)
        (list* v u seen)))

;;-------------------------------------------------------------
;; The acount1 of a structure under (cons q seen) is never 
;; larger than that under seen.
;;-------------------------------------------------------------
(defthm acount1-cons-linear
  (<= (acount1 p cp (cons q seen))
      (acount1 p cp seen))
  :rule-classes :linear)

(defthm member-subsetp
  (implies (and (subsetp a b)
                (not (member-equal e b)))
           (not (member-equal e a))))

(defun acyclicp1-hint (p cp seen1 seen2)
  (declare (xargs :measure (llist
                            (len (setdiff (all-indexes-in-cp cp) seen1))
                            (acl2-count p))
                  :well-founded-relation l<
                  :guard (equal seen2 seen2)
                  :verify-guards nil))
  (cond ((atom p)
         (cond ((natp p)
                (cond ((not (assoc p cp)) nil)
                      ((member-equal p seen1) nil)
                      (t (acyclicp1-hint (valueOf p cp) cp
                                         (cons p seen1)
                                         (cons p seen2)))))
               (t t)))
        (t (cons (acyclicp1-hint (car p) cp seen1 seen2)
                 (acyclicp1-hint (cdr p) cp seen1 seen2)))))



;;-------------------------------------------------------------
;; Here are two crucial facts.  They are not very good rewrite 
;; rules -- because they have free variables in them -- and so 
;; I don't store them as rules.  Consider running acyclicp1 
;; under two different lists of visited indexes, a "little" list 
;; (visited1) and a "big" list (visited2). In particular, visited1 is a 
;; subset of visited2.  Then if a structure is acyclic under the 
;; big list, it is acyclic under the little one.
;;-------------------------------------------------------------
(defthm subsetp-acyclicp1
  (implies (and (subsetp visited1 visited2)
                (acyclicp1 p cp visited2))
           (acyclicp1 p cp visited1))
  :rule-classes nil
  :hints (("Goal" :induct (acyclicp1-hint p cp visited1 visited2))))

(defthm acyclicp1-cons
  (implies (acyclicp1 p cp (cons q visited))
           (acyclicp1 p cp visited))
  :hints (("Goal" :use (:instance subsetp-acyclicp1
                                  (visited1 visited)
                                  (visited2 (cons q visited))))))

;;-------------------------------------------------------------
;; Similarly, if a structure is acyclic under the big list, 
;; then its acount1 under the big list is the same as its 
;; acount1 under the little one.
;;-------------------------------------------------------------
(defthm subsetp-acount1
  (implies (and (subsetp seen1 seen2)
                (acyclicp1 p cp seen2))
           (equal (acount1 p cp seen2)
                  (acount1 p cp seen1)))
  :rule-classes nil
  :hints (("Goal" :induct (acyclicp1-hint p cp seen1 seen2))))

;;-------------------------------------------------------------
;; When trying to prove theorems further below I found that I 
;; needed only one special case of the theorem above, namely, 
;; when the big list has one more element than the little list.  
;; This is a good rewrite rule, because it doesn't have a free 
;; variable in it.
;;-------------------------------------------------------------
(defthm acount1-cons
  (implies (acyclicp1 p cp (cons q seen))
           (equal (acount1 p cp (cons q seen))
                  (acount1 p cp seen)))
  :hints (("Goal" :use (:instance subsetp-acount1
                                  (seen1 seen)
                                  (seen2 (cons q seen))))))



;;-------------------------------------------------------------
;; So here is a really nice fact: If p is an acyclic index, 
;; then chasing it one level (to the structure it points to) 
;; decreases the acount1.  
;;
;; I could have stated this in terms of valueOf (thus the use of valueOf 
;; in the name), but valueOf is non-recursive and had I used valueOf this 
;; wouldn't be a good rewrite rule.  In a moment, I'll 
;; permanently disable valueOf.
;;-------------------------------------------------------------
(defthm acount1-valueOf
  (implies (and (natp p)
                (acyclicp1 p cp seen))
           (< (acount1 (cdr (assoc p cp)) cp seen)
              (acount1 p cp seen)))
  :rule-classes :linear)

;;-------------------------------------------------------------
;; Finally, here are the three theorems I need to justify 
;; recursion through structures.  They are stated entirely in 
;; terms of the "top-level" concepts acyclicp, acount, and valueOf.  
;; After proving them, I disable those functions.
;;-------------------------------------------------------------
(defthm acount-valueOf
  (implies (and (natp p)
                (acyclicp p cp))
           (< (acount (valueOf p cp) cp)
              (acount p cp)))
  :rule-classes :linear)

(defthm acount-car
  (implies (consp p)
           (< (acount (car p) cp)
              (acount p cp)))
  :rule-classes :linear)

(defthm acount-cdr
  (implies (consp p)
           (< (acount (cdr p) cp)
              (acount p cp)))
  :rule-classes :linear)

(in-theory (disable acount valueOf acyclicp))

;;-------------------------------------------------------------
;; This concludes the justification of recursion through 
;; structures.
;;
;; Now I define the denotation of an acyclic structure.  Note 
;; that cyclic structures always "denote" nil.  This is an 
;; arbitrary convention.
;;-------------------------------------------------------------


;;-------------------------------------------------------------
;; dref is a function that takes the index p and the constant 
;; pool cp. If p is acyclic in cp, dref returns the result of 
;; resolving p in cp; otherwise dref returns nil.
;;-------------------------------------------------------------
(defun dref (p cp)
  (declare (xargs :measure (acount p cp)))
  (cond ((acyclicp p cp)
         (cond ((atom p)
                (if (natp p)
                    (dref (valueOf p cp) cp)
                  p))
               (t (cons (dref (car p) cp)
                        (dref (cdr p) cp)))))
        (t nil)))

;;-------------------------------------------------------------
;; So, here is a little test of dref on a constant pool that 
;; has some cyclic and acyclic structures in it.
;;-------------------------------------------------------------
#|
(let ((cp '((1 . (2 . 3))
           (2 . (4 . 5))
           (3 . (6 . 7))
           (4 . "Four")
           (5 . "Five")
           (6 . "Six")
           (7 . "Seven")
           (8 . (2 . 3))
           (9 . (2 . 10))
           (10 . (3 . 11))
           (11 . (4 . 9))
           (12 . (2 . 13)))))
  (list (dref 1 cp)
        (dref 8 cp)
        (dref 9 cp)
        (dref 13 cp)))
|#
;;-------------------------------------------------------------
;; indexes-from-obj is a function that takes as inputs the 
;; object obj and the constant pool cp. It returns the list of
;; indexes on the path from obj up to its ultimate resloved 
;; result.
;;-------------------------------------------------------------
(defun indexes-from-obj (obj cp)
  (declare (xargs :measure (acount obj cp)))
  (cond ((acyclicp obj cp)
	 (cond ((atom obj)
		(if (natp obj)
		    (union-equal (all-indexes-in-obj (valueOf obj cp))
				 (indexes-from-obj (valueOf obj cp) cp))
		  nil))
	       (t (union-equal (indexes-from-obj (car obj) cp)
			       (indexes-from-obj (cdr obj) cp)))))
	(t nil)))


;;-------------------------------------------------------------
;; ok-rulep is a predicate that takes as inputs a
;; transformation rule and the constant pool cp. It returns true
;; if the rule is well-formed with respect to the cp. A rule is 
;; well-formed if the following conditions hold.
;;(1) the rule is a cons pair
;;(2) the car of the rule appears as an index in the cp
;;(3) the car of the rules is acyclic in the cp
;;(4) the cdr of the rule is acyclic in the cp
;;(5) the number of steps needed to completely resolve the cdr 
;;    of the rule in cp is strictly less that that needed to 
;;    resolve the car of the rule in cp.  
;;(6) the result of resolving the car of the rule in cp is the
;;    same as resolving the cdr of the rule in cp.    
;;(7) the car of the rule is not equal to the cdr of the rule
;;(8) the set of all the indexes accumualted during resolving 
;;    cdr of the rule in cp is a subset of that of the car of
;;    the rule
;;-------------------------------------------------------------  

(defun ok-rulep (rule cp)
  (and (consp rule)
       (assoc (car rule) cp)
       (acyclicp (car rule) cp) 
       (acyclicp (cdr rule) cp) 
       (equal (dref (car rule) cp)
              (dref (cdr rule) cp))
       (not (member-equal (car rule) 
                          (all-indexes-in-obj (cdr
                                               rule)))) 
       (subsetp (indexes-from-obj (cdr rule) cp) 
                (indexes-from-obj (car rule) cp))))

;;-------------------------------------------------------------
;; ok-rule-listp is a predicate that takes a inputs a set of
;; transformation rules and the constant pool cp. It returns 
;; if every rule belongs to the rule-list is well-formed wrt 
;; cp; nil otherwise.
;;-------------------------------------------------------------
(defun ok-rule-listp (rule-list cp)
  (if (endp rule-list)
      (null rule-list)
    (and (ok-rulep (car rule-list) cp)
         (ok-rule-listp (cdr rule-list) cp))))



;;-------------------------------------------------------------
;; apply-rule-to-entry-1 is a function that takes as inputs 
;; a transformation rule, a position, and the constant pool
;; cp. If there a match between the rule and the entry at 
;; position, it applies the rule to the entry and returns 
;; a new cp; otherwise, the function returns the original cp. 
;;-------------------------------------------------------------
(defun apply-rule-to-entry-1 (rule position cp)
  (let ((rhs (valueOf position cp)))
    (cond ((matchValueRulep rhs rule)
           (replaceValue position 
                (applySubstitution rhs
                            rule)
                cp))
          (t cp))))

;;-------------------------------------------------------------
;; apply-rule-to-entry is a function that takes as inputs 
;; a transformation rule, a position, and the constant pool
;; cp. If the rule is well-formed in cp, then the function 
;; apply-rule-to-entry-1 is called; otherwise the cp 
;; is returned.
;;-------------------------------------------------------------
(defun apply-rule-to-entry (rule position cp) ;; changed
  (if (ok-rulep rule cp)
      (apply-rule-to-entry-1 rule position cp)
    cp))

#|
;; Eample (1)
(defthm example-1
  (let ((cp '((1 . (2 . 3))
              (2 . (4 . 5))
              (3 . (6 . 7))
              (4 . "Four")
              (5 . "Five")
              (6 . "Six")
              (7 . "Seven"))))
    (and
     (equal (apply-rule-to-entry '(2 . (4 . 5))
                                 1
                                 cp)
            '((1 (4 . 5) . 3)
              (2 4 . 5)
              (3 6 . 7)
              (4 . "Four")
              (5 . "Five")
              (6 . "Six")
              (7 . "Seven")))
     (equal (apply-rule-to-entry '(4 . "Four")
                                 2
                                 cp)
            '((1 2 . 3)
              (2 "Four" . 5)
              (3 6 . 7)
              (4 . "Four")
              (5 . "Five")
              (6 . "Six")
              (7 . "Seven")))
     (equal (apply-rule-to-entry '(7 . "Seven")
                                 3
                                 cp)
            '((1 2 . 3)
              (2 4 . 5)
              (3 6 . "Seven")
              (4 . "Four")
              (5 . "Five")
              (6 . "Six")
              (7 . "Seven")))))
  :rule-classes nil)
|#

;;-------------------------------------------------------------
;; member-objp is a predicate that takes as inputs the elemet e
;; and the object obj. It return true if the element e belongs
;; to the object obj; nil otherwise.
;;-------------------------------------------------------------
(defun member-objp (e obj)
  (cond ((atom obj) (equal e obj))
	(t (or (member-objp e (car obj) )
	       (member-objp e (cdr obj))))))

;;-------------------------------------------------------------
;; all-indexes-acyclicp is a predicate that takes as inputs 
;; the constant pool tail and the constant pool cp. It returns 
;; true if the first component of every entry in tail occurs 
;; as the first component of an entry in cp; nil otherwise.
;;-------------------------------------------------------------
(defun all-indexes-acyclicp (tail cp)
  (cond ((endp tail) (equal tail nil))
        (t (and (acyclicp (car (car tail)) cp)
                (all-indexes-acyclicp (cdr tail)
                                          cp)))))

;;-------------------------------------------------------------
;; acyclic-constant-pool is a predicate that takes as an input 
;; the constant pool cp. It returns t if the cp is an ok 
;; constant pool and all the indexes in cp are acyclic.
;;-------------------------------------------------------------
(defun acyclic-constant-poolp (cp)
  (and (uniqueNodeIDp cp)
       (all-indexes-acyclicp cp cp)))

