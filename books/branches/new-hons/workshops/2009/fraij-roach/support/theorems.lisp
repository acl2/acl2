(in-package "ACL2")
#|

(ld "theorems.lisp" :ld-pre-eval-print t)


theorems.lisp
 ------------------------------
Author------------------: Fares Fraij
Email-------------------: fares@ahu.edu.jo
Date of last revision---: July 25, 2008
The used version of ACL2: 2.9.2 (under WindowsXP)

 Objective:
 ---------
The goal of this book is to provide some proofs in directed acyclic graph 
(DAG) theory. First, we prove that given an acyclic directed graph, the 
replacement of any node within the graph with its siblings will NOT 
introduce cycles (i.e., the acyclicity of the graph is maintained). Second,
we prove that dereferencing a certain index, within such a graph, and 
dereferencing the same index after replacing an index with its sibling will
yield the same value.

 Background:
 ----------
The acyclic directed graph is modeled by a list. Each entry of the list
has two components: a node, which is a natural number referred to as index
henceforth, and a data object represents the nodes' direct siblings. 
This object may be an index, a string, or a structure consisting of 
indexes, strings, or a combination of both. The graph is assumed to have 
indexes as internal nodes and terminals (i.e., strings) as leafs.

This work proofs that applying certain substitutions (on the form of rules) 
to an acyclic graph maintains certain properties. A rule is a tuple 
consisting of two components: an index, which represents a node in the 
graph, and a data object which represents the nodes' direct siblings (or 
the transitive closure of the nodes' direct siblings). One of the properties 
that we are interested in is that applying such a rule to an acyclic graph
will maintain acyclicity. We are also interested in proving that dereferencing 
a certain index in the graph, before and after applying sucha rule, is the same.

|#

(include-book "./functions")
;; Lemma: assoc-replaceValue
;; This lemma describes the relation between the functions assoc and replaceValue.
(defthm assoc-replaceValue
  (implies (uniqueNodeIDp cp)
           (equal (assoc p (replaceValue i v cp))
                  (if (assoc i cp)
                      (if (equal p i) (cons p v) (assoc p cp))
                    (assoc p cp)))))


;; Lemma: uniqueNodeIDp-replaceValue
;; This lemma states that replaceValue preserves uniqueNodeIDp
(defthm uniqueNodeIDp-replaceValue
  (implies (uniqueNodeIDp cp)
           (uniqueNodeIDp (replaceValue i v cp))))

;; Lemma: acyclicp1-perm-congruence
;; This lemma states that given to lists, seen1 and seen2,
;; which are permutations of each others, then chasing 
;; an object in both of them leads to the same result. 
(defthm acyclicp1-perm-congruence
  (implies (perm seen1 seen2)
           (equal (acyclicp1 p cp seen1) (acyclicp1 p cp seen2)))
  :rule-classes :congruence)

;; Lemma: valueOf-replaceValue
;; This lemma describes the relation between the functions valueOf and replaceValue.
(defthm valueOf-replaceValue
  (implies (and (uniqueNodeIDp cp)
                (natp p))
           (equal (valueOf p (replaceValue i q cp))
                  (if (assoc i cp)
                      (if (equal p i)
                          q
                        (valueOf p cp))
                    (valueOf p cp))))
  :hints (("Goal" :in-theory (enable valueOf))))

;; Lemma: car-assoc
;; This lemma states that given the index x that exists as the car 
;; of an entry in the constant pool cp, then the car of that entry 
;; is x itself. 
(defthm car-assoc
  (implies (assoc x cp)
           (equal (car (assoc x cp)) x)))


;; Lemma: cdr-assoc
;; This lemma states that given a rule that belongs to the constant pool
;; cp, then the cdr of the result of looking up the car of rule in cp is
;; the cdr of rule itself.
(defthm cdr-assoc
  (implies (and (uniqueNodeIDp cp)
                (member-equal rule cp))
           (equal (cdr (assoc (car rule) cp)) (cdr rule))))

;; Lemma: assoc-natp
;; This lemma states that given an index i, which ocuurs as 
;; the car of an entry in cp and cp is well formed, then i is 
;; a natural number.
(defthm assoc-natp
  (implies (and (assoc i cp)
                (uniqueNodeIDp cp))
           (natp i))
  :rule-classes :forward-chaining)

;; Lemma: no-immediate-loops
;; This lemma states that given that the natural number index i and
;; that the object obj is acyclic in cp and the list that results
;; from adding i to seen, then there is no match between obj and
;; any entry that has i as its car. 
(defthm no-immediate-loops
  (implies (and (natp i)
                (acyclicp1 obj cp (cons i seen)))
           (not (matchValueRulep obj (cons i x))))
  :rule-classes nil)

;; Lemma: no-immediate-loops-useful
;; This lemma is a good rewrite rule version of the above lemma, 
;; namely no-immediate-loops since it does not contain free variables.
(defthm no-immediate-loops-useful
  (implies (and (uniqueNodeIDp cp)
                (assoc (car rule) cp) ;;
                (acyclicp1 (cdr rule)
                           cp (cons (car rule) seen)))
           (not (matchValueRulep (cdr rule)
                           rule)))
  :hints (("Goal" :use (:instance no-immediate-loops
                                  (i (car rule))
                                  (obj (cdr rule))
                                  (x (cdr rule))))))

(in-theory (enable acyclicp))

;; Lemma: acyclicp-car
;; This lemma states that given the acyclic object p in cp
;; and p is a cons, then the car of p is acyclic in cp.
(defthm acyclicp-car
  (implies (and (consp p)
                (acyclicp p cp))
           (acyclicp (car p) cp)))

;; Lemma: acyclicp-cdr
;; This lemma states that given the acyclic object p in cp
;; and p is a cons, then the cdr of p is acyclic in cp.
(defthm acyclicp-cdr
  (implies (and (consp p)
                (acyclicp p cp))
           (acyclicp (cdr p) cp)))

;; Lemma: acyclicp-valueOf
;; This next proof is a little more interesting: If p is 
;; acyclic, then (valueOf p c) is acyclic1 with respect to 
;; seen = (cons p nil).  But then by the acyclic1-cons theorem, 
;; (valueOf p c) is acyclic1 with respect to seen = nil, which means 
;; it is acyclic.
(defthm acyclicp-valueOf
  (implies (and (natp p)
                (acyclicp p cp))
           (acyclicp (valueOf p cp) cp))
  :hints
  (("Goal'" :expand (acyclicp1 p cp nil))))

;; Now I turn it back off...
(in-theory (disable acyclicp))

;; Lemma:  valueOf-apply-rule-to-entry-1
;; This lemma descibes the behavior of the functions valueOf and
;; apply-rule-to-entry-1: (valueOf p (apply-rule-to-entry-1 rule i c)).
(defthm valueOf-apply-rule-to-entry-1
  (implies (and (uniqueNodeIDp cp)
                (assoc i cp))
           (equal (valueOf p (apply-rule-to-entry-1 rule i cp))
                  (if (equal p i)
                      (if (matchValueRulep (valueOf p cp) rule)
                          (applySubstitution (valueOf p cp) rule)
                        (valueOf p cp))
                    (valueOf p cp))))
  :hints (("Goal" :in-theory (enable valueOf))))

;; Lemma: valueOf-apply-rule-to-entry
;; I prove a similar lemma of the above that describes the behavior of
;; the functions valueOf and apply-rule-entry: 
;; (valueOf p (apply-rule-to-entry rule i c)).
(defthm valueOf-apply-rule-to-entry
  (implies (and (uniqueNodeIDp cp)
                (assoc i cp))
           (equal (valueOf p (apply-rule-to-entry rule i cp))
                  (if (ok-rulep rule cp)
                      (valueOf p (apply-rule-to-entry-1 rule i cp))
                    (valueOf p cp))))
  :hints (("Goal" :in-theory (disable apply-rule-to-entry-1))))

;; Lemma: natp-car-assoc-i-c
;; This lemma states that if the car of looking up the index i in cp
;; is a natural number, then i exists as the car of an enry in cp. 
(defthm natp-car-assoc-i-c
  (implies (natp (car (assoc i cp)))
           (assoc i cp)))


;; The following Lemmas are two types:
;; (1) The first types states that given an index p that exists
;; as the car of an entry in cp, then this index also exists 
;; in cp after applying the following functions to it: 
;; apply-rule-to-entry-1, apply-rule-to-entry,  
;; apply-rule-list-to-entry, and once_tdl.
;; (2) The second types states that given a well formed cp,
;; then the cp will also be well fomed after applying 
;; apply-rule-to-entry-1, apply-rule-to-entry, 
;; apply-rule-list-to-entry, and once_tdl.

(defthm assoc-p-apply-rule-to-entry-1
  (implies (assoc p cp)
           (assoc p
                  (apply-rule-to-entry-1 rule i cp)))
  :hints (("Goal" :in-theory (enable valueOf))))

(defthm assoc-p-apply-rule-to-entry
  (implies (assoc p cp)
           (assoc p
                  (apply-rule-to-entry rule i cp)))
  :hints (("Goal" :in-theory (disable apply-rule-to-entry-1))))


(defthm uniqueNodeIDp-apply-rule-to-entry
  (implies (uniqueNodeIDp cp)
           (uniqueNodeIDp (apply-rule-to-entry rule 
                                                   i
                                                   cp))))

;; Theorem: acyclicp1-applySubstitution
;; This theorem states that given the well formed constant pool cp,
;; the object p, which is acyclic in cp given seen, and a rule that
;; has an acyclic cdr, then the object that results from replacing 
;; the occurences of (car rule) in p with (cdr rule) is also acyclic
;; in cp given the same seen.
(defthm acyclicp1-applySubstitution
  (implies (and (uniqueNodeIDp cp)
                (acyclicp1 p cp seen)
                (acyclicp1 (cdr rule) cp seen))
           (acyclicp1 (applySubstitution p rule) cp seen)))

;; Theorem: acyclicp-applySubstitution
;; This theorem states that given the well formed constant pool cp,
;; the object p, which is acyclic in cp, and a well fomed  rule in cp,
;; then the object that results from replacing the occurences of 
;; (car rule) in p with (cdr rule) is also acyclic in cp. Note that
;; this theorem serves as a wrapper for the previous theorem, namely
;; acyclicp1-applySubstitution
;; Main 1 
(defthm acyclicp-applySubstitution
  (implies (and (uniqueNodeIDp cp)
                (acyclicp p cp)
                (acyclicp (cdr rule) cp))
           (acyclicp (applySubstitution p rule) cp))
  :hints (("Goal" :in-theory (enable acyclicp))))

;; Lemma: acyclicp-assoc
;; This lemma states that given the natural number p that
;; is acyclic in cp, then p exists as the car of one of the
;; entries of cp.
(defthm acyclicp-assoc
  (implies (and (natp p)
                (acyclicp p cp))
           (assoc p cp))
  :hints (("Goal" :expand (acyclicp p cp))))

;; Lemma: assoc-acyclicp1-seen-acyclicp1-nil
;; This lemma states that given that natural number p
;; which occur as the car of one of the entries of cp and
;; the value bounded to p in cp is acyclic in cp given the
;; list (cons p seen), then p is acyclic in cp given the 
;; empty list, nil. 
(defthm assoc-acyclicp1-seen-acyclicp1-nil
  (implies (and (natp p)
		(assoc p cp)
		(acyclicp1 (valueOf p cp) cp (cons p seen)))
	   (acyclicp1 p cp nil))
  :hints (("goal" :expand (acyclicp1 p cp nil)
	   :use (:instance subsetp-acyclicp1
			   (p (valueOf p cp))
			   (visited1 (list p))
			   (visited2 (cons p seen))))))


;; Lemma: acyclicp1-seen-acyclicp1-nil
;; This lemma states that if the index p is acyclic
;; in cp given the list seen, the p is also acyclic
;; in cp given the empty list, nil.
(defthm acyclicp1-seen-acyclicp1-nil
  (implies (acyclicp1 p cp seen)
           (acyclicp1 p cp nil)))

;; Lemma: acyclicp1-p-acyclicp1-valueOf
;; This lemma states that if the index p is acyclic
;; in cp given the list seen, the (valueOf p cp) is also acyclic
;; in cp given seen = (cons p seen)
(defthm acyclicp1-seen-acyclicp1-valueOf-seen
  (implies (and (acyclicp1 p cp seen)
                (natp p))
           (acyclicp1 (valueOf p cp) cp seen))
  :rule-classes :forward-chaining)

;; Theorem: dref-applySubstitution
;; This theorem states that given the well formed cp, the well formed
;; rule in cp, and the acyclic object p in cp, then the result of dereferencing
;; p in cp is the same as dereferencing the modified p in cp. P is modified by 
;; replacing every ocuurence of the (car rule) in p with (cdr rule).
;; Main 2
(defthm dref-applySubstitution
  (implies (and (uniqueNodeIDp cp)
                (acyclicp p cp)
                (acyclicp (cdr rule) cp)
                (equal (dref (car rule) cp)
                       (dref (cdr rule) cp))) ;;
           (equal (dref (applySubstitution p rule) cp)
                  (dref p cp)))
  :hints (("Goal" :in-theory (enable acyclicp))))
; (i-am-here)
;; Lemma: subsetp-union-equal-or
;; This lemma states that if x is a subset of y
;; and a is a subset of x union y, then either 
;; a is subset of x or a is subset of y.
(defthm subsetp-union-equal-or
  (implies  (and (subsetp x y)
                 (subsetp a (union-equal x y)))
            (or (subsetp a x)
                (subsetp a y)))
  :rule-classes :forward-chaining)

;; Lemma: member-is-member-equal
;; This I developed since I wanted to 
;; consentarate on the use of member-equal 
;; instead of member. These two predicates are 
;; equivalent in the logic mode; however,
;; they are different in the programming mode. 
(defthm member-is-member-equal
  (equal (member i seen)
	 (member-equal i seen)))

;; Lemma(s): The following set of lemmas are general 
;; facts about set theory operations.
;; Begin of set general set theory lemmas
(defthm member-equal-intersectp
  (implies (member-equal i x)
	   (intersectp-equal x (cons i seen))))

(defthm intersectp-equal-x-y-seen
  (iff (intersectp-equal (union-equal x
				      y)
			 seen)
       (or (intersectp-equal x seen)
	   (intersectp-equal y seen))))

;; Lemma-1 
(defthm intersectp-equal-not-acyclicp1
  (implies (intersectp-equal (all-indexes-in-obj obj) seen)
           (not (acyclicp1 obj
                           cp seen))))
;; lemma-2
(defthm not-acyclicp-cons-any
  (implies (not (acyclicp1 obj cp seen))
           (not (acyclicp1 obj cp (cons any seen)))))

;; Lemma-3: needs Lemma-1 + Lemma-2
(defthm intersectp-equal-indexes-acyclicp1
  (implies (intersectp-equal (indexes-from-obj i cp)
			     seen)
	   (equal (acyclicp1 i cp seen) nil)))

(defthm member-intersectp-equal
  (implies (and (member-equal e x)
		(member-equal e y))
	   (intersectp-equal x y)))

(defthm member-equal-union-equal
  (iff  (member-equal i (union-equal y z))
	(or (member-equal i z)
	    (member-equal i y))))
;; End of set general set theory lemmas
;;--------------------------------------------------

;;--------------------------------------------------
;; Lemma: transitivity-of-member-equal
;; In this lemma I start to use the function 
;; indexes-from-obj, which takes as inputs the object p 
;; and a cp and returns all the indexes on the paths starting
;; from p.
;; This lemma states that given that the index i is member 
;; on the set of all indexes in cp strating from p and 
;; j is a member on the set of all indexes in cp starting 
;; from i, then j is a member on the set of all indexes in 
;; cp starting from p.
;; Another way to express the idea of this lemma is that:
;; if the index i is within the subtree of the indexes strating
;; from p and the index j is within the subtree of indexes 
;; starting from i, then j is within the subtree of indexes 
;; starting from p.

;; Lemma-1
(defthm  acyclicp-member-equal-all-indexes
  (implies (and (acyclicp obj cp)
                (member-equal i (all-indexes-in-obj obj))
                (member-equal j (indexes-from-obj i cp)))
           (member-equal j (indexes-from-obj obj cp))))

;; Lemma-2 needs Lemma-1
(defthm transitivity-of-member-equal
  (implies (and (member-equal i (indexes-from-obj p cp))
                (member-equal j (indexes-from-obj i cp)))
           (member-equal j (indexes-from-obj p cp))))


;;------------------------------------------------------------
;; Lemma: member-equal-subset-index-from-obj
;; This lemma states that if the index i is within the 
;; the subtree starting from p, then the set of indexes 
;; starting from i in cp is a subset from the set of
;; indexes strating from p in cp.
(defthm acyclicp-member-equal-all-indexes-from
  (implies (and (acyclicp obj cp)
                (member-equal i (all-indexes-in-obj obj)))
           (subsetp (indexes-from-obj i cp)
                    (indexes-from-obj obj cp))))

(defthm member-equal-subset-index-from-obj
  (implies (member-equal i (indexes-from-obj p cp))
           (subsetp (indexes-from-obj i cp)
                    (indexes-from-obj p cp))))


;;------------------------------------------------------------
;; Lemma: subsetp-member-equal-i-subsetp-cons-i
;; This lemma states that given the set of indexes
;; starting from i in cp is a subset from the set
;; of indexes strating from p in cp and i is 
;; within the subtree starting from p, then 
;; the set that results from adding the index i to 
;; the set of indexes starting from the index 
;; associated with i in cp is a subset from the set
;; of indexes strating from p.
;; The following lemmas are about the relation between 
;; subset, indexes-from-obj, and member.
;;---------------------------------------------------
;; Begin of lemmas that are about the relation between 
;; subset, indexes-from-obj, and member.
(defthm acyclicp-member-equal-all-indexes-fron-valueOf
  (implies (and (acyclicp obj cp)
                (member-equal i (all-indexes-in-obj obj)))
           (subsetp (indexes-from-obj (valueOf i cp) cp)
                    (indexes-from-obj obj cp))))

(defthm subsetp-member-equal-i-subsetp-cons-i
  (implies (and (subsetp (indexes-from-obj i cp) 
                         (indexes-from-obj p cp))
                (member-equal i (indexes-from-obj p cp)))
           (subsetp (cons i (indexes-from-obj (valueOf i cp) cp))
                    (indexes-from-obj p cp)))
  :rule-classes :forward-chaining)

(defthm subsetp-member-equal-i-subsetp-cons-i-1
  (implies (and (subsetp (indexes-from-obj i cp) 
                         (indexes-from-obj p cp))
                (member-equal i (indexes-from-obj p cp)))
           (subsetp (indexes-from-obj (valueOf i cp) cp)
                    (indexes-from-obj p cp)))
  :rule-classes :forward-chaining)

(defthm not-subsetp-pfo-valueOf-not-member-equal-pfo
  (implies (not (subsetp (indexes-from-obj (valueOf i cp) cp)
                         (indexes-from-obj p1 cp)))
           (not (member-equal i (indexes-from-obj p1 cp))))
  :rule-classes :forward-chaining)

(defthm not-subsetp-cons-pfo-valueOf-not-member-equal-pfo
  (implies (not (subsetp (cons i (indexes-from-obj (valueOf i cp) cp))
                         (indexes-from-obj p1 cp)))
           (not (member-equal i (indexes-from-obj p1 cp))))
  :rule-classes :forward-chaining)
;;---------------------------------------------------
;; End of lemmas that are about the relation between 
;; subset, indexes-from-obj, and member.
;;----------------------------------------------------

;; Lemma acyclicp1-car-cdr states that given an object p
;; in which its first and its second components are acyclic
;; in the constant pool cp, Then the object p itself is 
;; acyclic in cp.

(defthm acyclicp1-car-cdr
  (implies (and (consp p)
                (acyclicp1 (car p) cp seen)
                (acyclicp1 (cdr p) cp seen))
           (acyclicp p cp))
  :hints (("Goal" :in-theory (enable acyclicp))))

;; Lemma acyclicp1-valueOf-p-c-assoc-p-c states that given 
;; a natural number p for which the object associated 
;; with in cp is acyclic in cp with respect to list of 
;; encountered indexes so far, namely seen, then p 
;; itself is acyclic in cp with respect to seen.

(defthm acyclicp1-valueOf-p-c-assoc-p-c
  (implies (and (natp p)
                (acyclicp1 (valueOf p cp) cp (cons p seen)))
           (assoc p cp))
  :hints (("Goal" :in-theory (enable valueOf acyclicp))))

;; Lemma acyclicp1-valueOf-p-c-acyclicp1-p is a more
;; restricted version of the Lemma 
;; acyclicp1-valueOf-p-c-assoc-p-c (above).

(defthm acyclicp1-valueOf-p-c-acyclicp1-p
  (implies (and (natp p)
                (acyclicp1 (valueOf p cp) cp (cons p seen)))
           (acyclicp p cp))
  :hints (("Goal" :in-theory (enable acyclicp))))

;; Lemma assoc-p-c-assoc-p-replaceValue-i-x-c states that if 
;; an index is associated with a cp, then it is also 
;; associated with the cp that results from inserting
;; an index i in original cp.
(defthm assoc-p-c-assoc-p-replaceValue-i-x-c
  (implies (assoc p cp)
           (assoc p (replaceValue i x cp))))
           
;; Lemma acyclicp1-a-replaceValue-i-x-c-seen-1 states that given
;; an ok constant pool, an acyclic pointer, p, in the cp
;; wrt seen, and i is not reachable from p, then p is 
;; also acyclic wrt seen in the result of inserting 
;; an index i associated with object x in the original cp.
  
(encapsulate ()
             (local (in-theory (disable 
                                intersectp-equal-indexes-acyclicp1
                                natp-car-assoc-i-c
                                assoc
                                union-equal
                                intersectp-equal)))

             (defthm acyclicp1-a-replaceValue-i-x-c-seen-1
               (implies (and (uniqueNodeIDp cp)
                             (acyclicp1 p cp seen)
                             (or (and (consp p)
                                      (not (member-equal 
                                            i 
                                            (all-indexes-in-obj p))))
                                 (and (natp p)
                                      (not (equal p i))))
                             (not (member-equal i (indexes-from-obj p cp))))
                        (acyclicp1 p (replaceValue i x cp) seen))))


;; Lemma acyclicp-applySubstitution-replaceValue-1 is a more restricted 
;; version of Lemma acyclicp1-a-replaceValue-i-x-c-seen-1 (above)

(defthm acyclicp-applySubstitution-replaceValue-1
  (implies (and (uniqueNodeIDp cp)
		(acyclicp p cp)
                (or (and (consp p)
                         (not (member-equal i (all-indexes-in-obj p))))
                    (and (natp p)
                         (not (equal p i))))
                (not (member-equal i (indexes-from-obj p cp))))
	   (acyclicp p
                    (replaceValue i any cp)))
  :hints (("Goal" :in-theory (enable acyclicp))))

;; Lemma not-subsetp-not-member-equal-1 states that given
;; that the set of indexes starting from i in cp is not a subset 
;; of that from x in cp, then i does not belong to the set
;; of indexes from x in cp.
 
(defthm not-subsetp-not-member-equal-1
  (implies (not (subsetp (indexes-from-obj i cp)
			 (indexes-from-obj x cp)))
	   (not (member-equal i (indexes-from-obj x cp)))))

;; Lemma acyclicp1-subsetp-pfo-valueOf-pfo states that given an ok 
;; constant pool, cp, the index i is associated with an entry in cp, 
;; and i is acyclic in cp wrt seen, then the set of indexes 
;; starting from the object associated with i in cp is a subset 
;; of that from i in cp.

(defthm acyclicp1-subsetp-pfo-valueOf-pfo
  (implies (and (assoc i cp)
		(uniqueNodeIDp cp)
		(acyclicp1 i cp seen))
	   (subsetp (indexes-from-obj (valueOf i cp) cp)
		    (indexes-from-obj i cp)))
  :rule-classes :forward-chaining)

;; Lemma acyclicp-subsetp-pfo-valueOf-pfo is a more restrictive 
;; version of Lemma acyclicp1-subsetp-pfo-valueOf-pfo (above).
(defthm acyclicp-subsetp-pfo-valueOf-pfo
  (implies (and (assoc i cp)
		(uniqueNodeIDp cp)
		(acyclicp i cp))
	   (subsetp (indexes-from-obj (valueOf i cp) cp)
		    (indexes-from-obj i cp)))
  :rule-classes :forward-chaining)

;; Lemma acyclicp1-not-member-equal-pfo states that given an ok 
;; constant pool, cp, the index i is associated with an entry in cp, 
;; and i is acyclic in cp wrt seen, then i does not belong to 
;; the set of indexes starting from the object assocted with 
;; i in cp.

(defthm acyclicp1-not-member-equal-pfo
  (implies (and (assoc i cp)
		(uniqueNodeIDp cp)
		(acyclicp1 i cp seen))
	   (not (member-equal i (indexes-from-obj (valueOf i cp) cp))))
  :rule-classes (:rewrite :forward-chaining))

;; Lemma acyclicp-not-member-equal-pfo is a more restrictive 
;; version of Lemma acyclicp1-not-member-equal-pfo (above).
(defthm acyclicp-not-member-equal-pfo
  (implies (and (assoc i cp)
		(uniqueNodeIDp cp)
		(acyclicp i cp))
	   (not (member-equal i (indexes-from-obj (valueOf i cp) cp))))
  :hints (("Goal" :in-theory (enable acyclicp)))
  :rule-classes (:rewrite :forward-chaining))

;; Lemma subsetp-not-subsetp-member-equal states that
;; if x is subset of the list that results from adding 
;; the element i to y, and x is not a subset of y,
;; then i is equal to x.
(defthm subsetp-not-subsetp-member-equal
  (implies (and (subsetp x
			 (cons i y))
		(not (subsetp x
			      y)))
	   (member-equal i x))
  :rule-classes :forward-chaining)

;; Lemma perm-list-1 states that given the acyclic object (valueOf i cp), which represents
;; the object associated with i in cp, wrt to the list that consists of adding
;; i and p to seen, then the object (valueOf i cp) is also acyclic in cp wrt the
;; list that consists of adding p and i to seen. 
(defthm perm-list-1
  (implies (acyclicp1 (valueOf i cp) cp (list* p i seen))
	   (acyclicp1 (valueOf i cp) cp (list* i p seen)))
  :rule-classes :forward-chaining)

;; Lemma member-equal-subsetp-member-equal states that 
;; if the element i is member in the list x, and x is a subset 
;; of the list y, then i is belongs to y.
(defthm member-equal-subsetp-member-equal
  (implies (and (member-equal i x)
		(subsetp x y))
	   (member-equal i y)))

;; Lemma matchValueRulep-valueOf-rule-implies-member-objp-r1-valueOf states that 
;; if there is a match between the object valueOf and rule, then 
;; the first component of the rule belongs to valueOf.

(defthm matchValueRulep-valueOf-rule-implies-member-objp-r1-valueOf
  (implies (matchValueRulep valueOf rule)
	   (member-objp (car rule) valueOf)))
;;[x]

;; Lemma acyclicp1-obj-member-objp-i-acyclicp1-i states that given 
;; an acyclic object valueOf in cp wrt seen and the element i belongs to valueOf,
;; then i is also acyclic in cp wrt seen.

(defthm acyclicp1-obj-member-objp-i-acyclicp1-i
  (implies (and (acyclicp1 valueOf cp seen)
		(member-objp i valueOf))
	   (acyclicp1 i cp seen)))
;;[x]

;; Lemma acyclicp1-obj-member-objp-i-acyclicp1-i-1 is a restricted
;; version of Lemma acyclicp1-obj-member-objp-i-acyclicp1-i (above).

(defthm acyclicp1-obj-member-objp-i-acyclicp1-i-1
  (implies (and (acyclicp valueOf cp)
		(member-objp i valueOf))
	   (acyclicp i cp)))
;;[x]

(defthm matchValueRulep-member-i-valueOf-subsetp-pfo-i
  (implies (and (matchValueRulep valueOf rule)
		(acyclicp1 valueOf cp seen))
	   (subsetp (indexes-from-obj (car rule) cp)
		    (indexes-from-obj valueOf cp))))
;;[x]
		    
;; Lemma i-not-member-valueOf-subsetp-pfo-r1-valueOf states that
;; given that the index i is not reachable from the object valueOf in cp, 
;; there is a match between the index i and rule, and valueOf is acyclic
;; in cp wrt seen, then i is not reachable from the first 
;; component of rule. 
(defthm i-not-member-valueOf-subsetp-pfo-r1-valueOf
  (implies (and (not (member-equal i (indexes-from-obj valueOf cp)))
		(matchValueRulep valueOf rule)
		(acyclicp1 valueOf cp seen))
	   (not (member-equal i (indexes-from-obj (car rule) cp)))))
;;[x]

;; Lemma not-member-i-pfo-valueOf-matchValueRulep-valueOf-rule-not-member-i-pfo-cdr-rule
;; states that given that the index i is not reachable from object valueOf 
;; in cp, there is a match between valueOf and rule, valueOf is acyclic in cp 
;; wrt seen, and the set of indexes accumulated from the second 
;; component of rule in cp is a subset of that accumulated from the 
;; first component of rule in cp, then the index i is not reachable
;; from the second component of rule in cp.
(defthm not-member-i-pfo-valueOf-matchValueRulep-valueOf-rule-not-member-i-pfo-cdr-rule
  (implies (and (not (member-equal i (indexes-from-obj valueOf cp)))
		(matchValueRulep valueOf rule)
		(acyclicp1 valueOf cp seen)
		(subsetp (indexes-from-obj (cdr rule) cp)
			 (indexes-from-obj (car rule) cp)))
	   (not (member-equal i (indexes-from-obj (cdr rule) cp)))))
;;[x]

(encapsulate ()
             (local (in-theory (disable 
                                member-equal
                                intersectp-equal-not-acyclicp1
                                union-equal
                                intersectp-equal-indexes-acyclicp1
                                natp-car-assoc-i-c
                                intersectp-equal
                                assoc
                                member-objp
                                all-indexes-in-obj
                                not-subsetp-not-member-equal-1
                                not-acyclicp-cons-any
                                acyclicp1-obj-member-objp-i-acyclicp1-i-1
                                acyclicp-assoc
                                acyclicp-member-equal-all-indexes
                                uniqueNodeIDp)))

             ;; Lemma acyclicp1-not-member-equal-pfo-applySubstitution
             ;; states that given a rule that represent a cons, the first 
             ;; component of the rule appears as the first component of 
             ;; an entry in cp, an ok constant pool, cp, the set of indexes 
             ;; accumulated from the second component of rule in cp is 
             ;; a subset of that accumulated from the first component of 
             ;; rule in cp, the second component of the rule is acyclic 
             ;; in cp wrt seen, the object x is acyclic in cp wrt seen, 
             ;; and the index i is not reachable from object x in cp, 
             ;; then the index i is not reachable from the object that 
             ;; results from replacing every occurence of the rhs of 
             ;; the rule in x with the lhs of the rule. 

             (defthm acyclicp1-not-member-equal-pfo-applySubstitution
               (implies (and (consp rule)
                             (uniqueNodeIDp cp)
                             (assoc (car rule) cp)
                             (subsetp (indexes-from-obj (cdr rule) cp)
                                      (indexes-from-obj (car rule) cp))
                             (acyclicp1 (cdr rule) cp seen)
                             (acyclicp1 x cp seen)
                             (not (member-equal i (indexes-from-obj x cp))))
                        (not (member-equal i 
                                           (indexes-from-obj 
                                            (applySubstitution x rule) 
                                            cp))))))
;;[x]

;; Lemma not-assoc-i-cp-replaceValue-i-cp-is-cp states that 
;; given the ok constant pool cp and the index i 
;; does not belong to the domain of cp, then 
;; the result of inserting the object that associates 
;; the index i with the object any is actually cp itself. 
(defthm not-assoc-i-cp-replaceValue-i-cp-is-cp
  (implies (and (uniqueNodeIDp cp)
                (not (assoc i cp)))
           (equal (replaceValue i any cp)
                  cp)))
;;[x]

(encapsulate ()
             (local (in-theory (disable 
                                intersectp-equal-not-acyclicp1
                                union-equal
                                intersectp-equal-indexes-acyclicp1
                                natp-car-assoc-i-c
                                intersectp-equal
                                assoc
                                member-objp)))

             ;; Lemma acyclicp1-applySubstitution-replaceValue-1 states that
             ;; given an ok constant pool, cp, the index i is 
             ;; acyclic in cp wrt seen, the object p is acyclic 
             ;; in cp wrt seen, the index i is not reachable 
             ;; from the object p in cp, then the object p is 
             ;; acyclic in the new cp, which results from associating 
             ;; the index i with the bject any in the orignal cp,
             ;; wrt seen.
             (defthm acyclicp1-applySubstitution-replaceValue-1
               (implies (and (uniqueNodeIDp cp)
                             (acyclicp1 i cp seen)
                             (acyclicp1 p cp seen)
                             (not (member-equal i (all-indexes-in-obj p)))
                             (not (member-equal i (indexes-from-obj p cp))))
                        (acyclicp1 p
                                   (replaceValue i any cp)
                                   seen)))
             ;;[x]
             ;; Lemma acyclicp1-not-member-equal-pfo-acyclicp1
             ;; states that given an acyclic index, i, in cp
             ;; wrt seen and i is not reachable from the index p, 
             ;; i is not reachable from the index p, 
             ;; then the index i is acyclic in cp wrt to the new 
             ;; list that results from adding p to seen.
             (defthm acyclicp1-not-member-equal-pfo-acyclicp1
               (implies (and (acyclicp1 i cp seen)
                             (not (member-equal p (all-indexes-in-obj i)))
                             (not (member-equal p (indexes-from-obj i cp))))
                        (acyclicp1 i cp (cons p seen))))
             ;;[x]
             )

;; Lemma acyclicp1-assoc-acyclicp1-valueOf states that given
;; an ok constant pool, cp, an acyclic index i in cp 
;; wrt seen, and i appears as the first component of 
;; of an entry in cp, then the object associated with 
;; i in cp is also acyclic wrt seen.

(defthm acyclicp1-assoc-acyclicp1-valueOf 
  (implies (and (uniqueNodeIDp cp)
                (acyclicp1 i cp seen)
                (assoc i cp))
           (acyclicp1 (valueOf i cp) cp seen))
  :rule-classes :forward-chaining)
;;[x]

;; Lemma acyclicp-assoc-acyclicp1-valueOf  is a restricted
;; version of Lemma acyclicp1-assoc-acyclicp1-valueOf (above).
(defthm acyclicp-assoc-acyclicp1-valueOf 
  (implies (and (uniqueNodeIDp cp)
                (acyclicp i cp)
                (assoc i cp))
           (acyclicp (valueOf i cp) cp))
  :rule-classes :forward-chaining)
;;[x]

;; Lemma acyclicp1-obj-member-objp-i-acyclicp1-i-1-prime-1 
;; states that given an ok constant pool, cp, an acyclic 
;; index i in cp wrt seen, i appears as the first component of 
;; of an entry in cp, and the index x belongs to the object 
;; (valueOf i cp) that is associated with i in cp, then x 
;; is acyclic in cp wrt seen. 

(defthm acyclicp1-obj-member-objp-i-acyclicp1-i-1-prime-1
  (implies (and (uniqueNodeIDp cp)
                (acyclicp1 i cp seen)
                (assoc i cp)
                (member-objp x (valueOf i cp)))
	   (acyclicp1 x cp seen)))
;;[x]

;; Lemma acyclicp-obj-member-objp-i-acyclicp1-i-1-prime-1 
;; is a restricted version of Lemma
;; acyclicp1-obj-member-objp-i-acyclicp1-i-1-prime-1 (above).
(defthm acyclicp-obj-member-objp-i-acyclicp1-i-1-prime-1
  (implies (and (uniqueNodeIDp cp)
                (acyclicp i cp)
                (assoc i cp)
                (member-objp x (valueOf i cp)))
	   (acyclicp x cp)))
;;[x]

;; Lemma acyclicp1-obj-member-objp-i-acyclicp1-i-1-prime-2
;; states that given an ok constant pool, cp, an acyclic 
;; index i in cp wrt seen, i appears as the first component of 
;; of an entry in cp, and the index x is equal to i, then x 
;; is acyclic in cp wrt seen. 

(defthm acyclicp1-obj-member-objp-i-acyclicp1-i-1-prime-2
  (implies (and (uniqueNodeIDp cp)
                (acyclicp1 i cp seen)
                (assoc i cp)
                (member-equal x (all-indexes-in-obj i)))
	   (acyclicp1 x cp seen)))
;;[x]

;; Lemma acyclicp-obj-member-objp-i-acyclicp1-i-1-prime-2-1
;; is a restricted version of Lemma
;; acyclicp1-obj-member-objp-i-acyclicp1-i-1-prime-2 (above).
(defthm acyclicp-obj-member-objp-i-acyclicp1-i-1-prime-2-1
  (implies (and (uniqueNodeIDp cp)
                (acyclicp i cp)
                (assoc i cp)
                (member-equal x (all-indexes-in-obj i)))
	   (acyclicp x cp)))
;;[x]

;; Lemma matchValueRulep-member-i-valueOf-subsetp-pfo-i-1
;; states that given an ok constant pool, cp, an acyclic 
;; index i in cp wrt seen, i appears as the first component of 
;; of an entry in cp, and a match exists between 
;; the object (valueOf i cp), which represents the object
;; associated with i in cp, and rule, then
;; the set of indexes accumulated from the first component 
;; of rule in cp is a subset of that accumulated from i in cp.
(defthm matchValueRulep-member-i-valueOf-subsetp-pfo-i-1
  (implies (and (matchValueRulep (valueOf i cp) rule)
                (uniqueNodeIDp cp)
                (acyclicp1 i cp seen)
                (assoc i cp))
	   (subsetp (indexes-from-obj (car rule) cp)
		    (indexes-from-obj i cp))))
;;[x]

;; Lemma matchValueRulep-member-i-valueOf-subsetp-pfo-i-1-1
;; is a restricted version of Lemma
;; matchValueRulep-member-i-valueOf-subsetp-pfo-i-1 (above).
(defthm matchValueRulep-member-i-valueOf-subsetp-pfo-i-1-1
  (implies (and (matchValueRulep (valueOf i cp) rule)
                (uniqueNodeIDp cp)
                (acyclicp i cp)
                (assoc i cp))
	   (subsetp (indexes-from-obj (car rule) cp)
		    (indexes-from-obj i cp)))
  :hints (("Goal" :use ((:instance matchValueRulep-member-i-valueOf-subsetp-pfo-i-1
                                   (seen nil)))
           :in-theory (e/d (acyclicp) 
                           (matchValueRulep-member-i-valueOf-subsetp-pfo-i-1)))))
;;[x]

;;----------------------------------
(encapsulate ()
             (local (in-theory (disable 
                                intersectp-equal-not-acyclicp1
                                union-equal
                                intersectp-equal-indexes-acyclicp1
                                natp-car-assoc-i-c
                                intersectp-equal
                                assoc
                                member-objp)))
                    
              ;; Lemma i-not-member-valueOf-subsetp-pfo-r1-valueOf-1-	    
              ;; states that given the object p is not reachable 
              ;; from the index i, an ok constant pool, cp, 
              ;; an acyclic index i in cp wrt seen, i appears 
              ;; as the first component of of an entry in cp, 
              ;; and a match exists between the object (valueOf i cp), 
              ;; which represents the object associated with i 
              ;; in cp, and rule, then p is not reachable 
              ;; from the first component of rule.

              (defthm i-not-member-valueOf-subsetp-pfo-r1-valueOf-1-
                (implies (and (not (member-equal p (indexes-from-obj i cp)))
                              (uniqueNodeIDp cp)
                              (acyclicp1 i cp seen)
                              (assoc i cp)
                              (matchValueRulep (valueOf i cp) rule))
                         (not (member-equal p (indexes-from-obj (car rule) cp)))))
              ;;[x]

              ;; Lemma i-not-member-valueOf-subsetp-pfo-r1-valueOf-1-1- is 
              ;; a restricted version of Lemma 
              ;; i-not-member-valueOf-subsetp-pfo-r1-valueOf-1-	    
              (defthm i-not-member-valueOf-subsetp-pfo-r1-valueOf-1-1-
                (implies (and (not (member-equal p (indexes-from-obj i cp)))
                              (uniqueNodeIDp cp)
                              (acyclicp i cp)
                              (assoc i cp)
                              (matchValueRulep (valueOf i cp) rule))
                         (not (member-equal p (indexes-from-obj (car rule) cp))))
                :hints (("Goal" :in-theory (enable acyclicp))))
              ;;[x]

              ;; Lemma |(cdr rule) is not reachable from p| 
              ;; states that given that the object p is not reachable 
              ;; from the index i, a match exists between the object (valueOf i cp), 
              ;; which represents the object associated with i 
              ;; in cp, and rule, an acyclic index i in cp wrt seen,
              ;; an ok constant pool, cp, i appears as the first 
              ;; component of of an entry in cp, and the set of 
              ;; indexes accumulated from the second component of rule 
              ;; in cp is a subset of that accumulated from the 
              ;; first component of rule in cp, then p is not reachable 
              ;; from the second component of rule.
              (defthm |(cdr rule) is not reachable from p| 
                (implies (and (not (member-equal p (indexes-from-obj i cp)))
                              (matchValueRulep (valueOf i cp) rule)
                              (acyclicp1 i cp seen)
                              (uniqueNodeIDp cp)
                              (assoc i cp)
                              (subsetp (indexes-from-obj (cdr rule) cp)
                                       (indexes-from-obj (car rule) cp)))
                         (not (member-equal p (indexes-from-obj (cdr rule) cp))))
                :rule-classes :forward-chaining)
              ;;[x]
              
              ;; Lemma
              ;; |(cdr rule) is not reachable from p rst| 
              ;; is a restricted version of Lemma
              ;; |(cdr rule) is not reachable from p| 
              ;; (above).
              (defthm |(cdr rule) is not reachable from p rst| 
                (implies (and (not (member-equal p (indexes-from-obj i cp)))
                              (matchValueRulep (valueOf i cp) rule)
                              (acyclicp i cp)
                              (uniqueNodeIDp cp)
                              (assoc i cp)
                              (subsetp (indexes-from-obj (cdr rule) cp)
                                       (indexes-from-obj (car rule) cp)))
                         (not (member-equal p (indexes-from-obj (cdr rule) cp))))
                :hints (("Goal" :in-theory (enable acyclicp)))
                :rule-classes :forward-chaining)
              ;;[x]
              )

;; Lemma replaceValue-i-valueOf-i-cp-is-cp states that given an
;; ok constant pool cp, then the result of inseting 
;; i and the object (valueOf i cp), which represent the 
;; object associted with i in cp, back in the cp 
;; is equal to the original cp. 
(defthm replaceValue-i-valueOf-i-cp-is-cp
  (implies (uniqueNodeIDp cp)
           (equal (replaceValue i (valueOf i cp) cp)
                  cp))
  :hints (("Goal" :cases ((not (assoc i cp)))
           :in-theory (enable valueOf assoc))))
;;[x]

;; Lemma acyclicp1-replaceValue-i-i-x states that given an acyclic
;; index, i, in cp, and i appears as the first 
;; component of an entry in cp, and cp is an ok
;; constant pool, then i is also acyclic in 
;; the new cp that results from insering i with its associated
;; object in cp, (valueOf i cp), in the original cp wrt seen.

(defthm acyclicp1-replaceValue-i-i-x
  (implies (and (acyclicp1 i cp seen)
                (assoc i cp)
		(uniqueNodeIDp cp))
           (acyclicp1 i (replaceValue i (valueOf i cp) cp) seen)))
;;[x]

;; Lemma not-matchValueRulep-applySubstitution-does-not-chaged
;; states that if there is no match between an object
;; x and a rule, then the result of replacing every 
;; ocuurence of the lhs of rule in x with rhs of rule 
;; will be equal to the original x.
(defthm not-matchValueRulep-applySubstitution-does-not-chaged
  (implies (not (matchValueRulep x rule))
           (equal (applySubstitution x rule) 
                  x)))
;;[x]


;;---------------------------------------------------------------------------
;; Begin: acyclicp1-p-replaceValue-i-applySubstitution
;; this part is an attempt to proof (acyclicp1 p (replaceValue i (applySubstitution (valueOf i
;; cp) cp seen). I had first to split the main goal into two cases:
;; (1) (equal p i) and (2) (not (equal p i)). 
;; The first part seems to be straightforward; however, for the second
;; part I had to split it into two cases:
;; (2.1) (matchValueRulep (valueOf i cp) cp) (2.2) (not (matchValueRulep (valueOf i cp) cp))
;;---------------------------------------------------------------------------
;; replaceValue
;;---------------------------------------------------------------------------
(encapsulate ()
             (local (in-theory (disable 
                                intersectp-equal-not-acyclicp1
                                union-equal
                                intersectp-equal-indexes-acyclicp1
                                natp-car-assoc-i-c
                                intersectp-equal
                                assoc
                                member-objp)))

             (defthm not-member-ifo-applySubstitution
               (implies (and (consp rule)
                             (uniqueNodeIDp cp)
                             (assoc (car rule) cp)
                             (subsetp (indexes-from-obj (cdr rule) cp)
                                      (indexes-from-obj (car rule) cp))
                             (acyclicp1 (cdr rule) cp seen)
                             (acyclicp1 i cp seen)
                             (assoc i cp))
                        (not (member-equal i 
                                           (indexes-from-obj 
                                            (applySubstitution (valueOf i cp) rule) cp))))
               :hints (("Goal" :cases ((matchValueRulep (valueOf i cp) rule))))
               :rule-classes :forward-chaining)
             ;;[x]

             ;; acyclicp version
             (defthm not-member-ifo-applySubstitution-1
               (implies (and (consp rule)
                             (uniqueNodeIDp cp)
                             (assoc (car rule) cp)
                             (subsetp (indexes-from-obj (cdr rule) cp)
                                      (indexes-from-obj (car rule) cp))
                             (acyclicp (cdr rule) cp)
                             (acyclicp i cp)
                             (assoc i cp))
                        (not (member-equal i 
                                           (indexes-from-obj 
                                            (applySubstitution (valueOf i cp) rule) cp))))
               :hints (("Goal" :in-theory (enable acyclicp)))
               :rule-classes :forward-chaining)
             ;;[x]
             
             (defthm acyclicp1-obj-member-equal-1
               (implies (and (uniqueNodeIDp cp)
                             (assoc i cp)
                             (acyclicp1 i cp seen)
                             (acyclicp1 obj cp seen)
                             (not (member-equal i (all-indexes-in-obj obj)))
                             (not (member-equal i (indexes-from-obj obj cp))))
                        (acyclicp1 i (replaceValue i obj cp) seen))
               :hints (("Goal" :expand (acyclicp1 i (replaceValue i obj cp) seen))))
             ;;[x]
             
             (defthm acyclicp1-obj-member-equal-2
               (implies (and (uniqueNodeIDp cp)
                             (not (assoc i cp))
                             (acyclicp1 i cp seen)
                             (acyclicp1 obj cp seen)
                             (not (member-equal i (all-indexes-in-obj obj)))
                             (not (member-equal i (indexes-from-obj obj cp))))
                        (acyclicp1 i (replaceValue i obj cp) seen)))
             ;;[x]
             )

(defthm acyclicp1-obj-member-equal
  (implies (and (uniqueNodeIDp cp)
                (acyclicp1 i cp seen)
                (acyclicp1 obj cp seen)
                (not (member-equal i (all-indexes-in-obj obj)))
                (not (member-equal i (indexes-from-obj obj cp))))
           (acyclicp1 i (replaceValue i obj cp) seen))
  :hints (("Goal" :cases ((assoc i cp)))))
;  :rule-classes :forward-chaining)
;;[x]

(defthm acyclicp1-i-seen-acyclicp1-valueOf
  (implies (and (uniqueNodeIDp cp)
                (acyclicp1 i cp seen))
           (acyclicp1 (valueOf i cp) cp seen))
  :hints (("Goal" :cases ((assoc i cp)))
          ("Subgoal 2'" :in-theory (enable valueOf)))
  :rule-classes :forward-chaining)
;;[x]

(defthm matchValueRulep-obj-cons-r1-r2
  (implies (and (assoc r1 cp)
		(uniqueNodeIDp cp)
		(matchValueRulep obj (cons r1 r2))
		(atom obj))
	   (natp obj))
  :rule-classes :forward-chaining)
;;[x]

(defthm matchValueRulep-obj-member-equal
  (implies (and (matchValueRulep obj (cons r1 r2))
		(uniqueNodeIDp cp)
		(assoc r1 cp))
	   (member-equal r1 (all-indexes-in-obj obj))))
;;[x]	   

(encapsulate ()
             (local (in-theory (disable 
                                indexes-from-obj
                                not-subsetp-not-member-equal-1
                                assoc
                                acyclicp-member-equal-all-indexes
                                uniqueNodeIDp
                                natp-car-assoc-i-c
                                not-acyclicp-cons-any)))


             (defthm acyclicp1-obj-member-equal-all
               (implies (and (acyclicp1 obj cp seen)
                             (member-equal i (all-indexes-in-obj obj)))
                        (acyclicp1 i cp seen)))
             ;;[x]


             (defthm acyclicp-obj-member-equal
               (implies (and (acyclicp obj cp)
                             (member-equal i (all-indexes-in-obj obj)))
                        (acyclicp i cp))
               :hints (("Goal" :in-theory (enable acyclicp))))
             ;;[x]
             


             (defthm matchValueRulep-acyclicp1-indexes-from-obj
               (implies (and (matchValueRulep obj rule)
                             (acyclicp1 obj cp seen))
                        (subsetp (indexes-from-obj (car rule) cp)
                                 (indexes-from-obj obj cp))))
             ;;[x]

             (defthm matchValueRulep-acyclicp-indexes-from-obj
               (implies (and (matchValueRulep obj rule)
                             (acyclicp obj cp))
                        (subsetp (indexes-from-obj (car rule) cp)
                                 (indexes-from-obj obj cp)))
               :hints (("Goal" :in-theory (enable acyclicp))))
             ;;[x]

             (defthm not-member-equal-acyclicp1-all-indexes-from-obj-matchValueRulep
               (implies (and (not (member-equal i (all-indexes-in-obj obj)))
                             (matchValueRulep obj rule)
                             (acyclicp1 obj cp seen))
                        (not (member-equal i (all-indexes-in-obj (car rule))))))
             ;;[x]

             (defthm not-member-equal-acyclicp-all-indexes-from-obj-matchValueRulep
               (implies (and (not (member-equal i (all-indexes-in-obj obj)))
                             (matchValueRulep obj rule)
                             (acyclicp obj cp))
                        (not (member-equal i (all-indexes-in-obj (car rule)))))
               :hints (("Goal" :in-theory (enable acyclicp)))))
;;[x]
;;----------------------------------------------------
(defthm member-equal-matchValueRulep-acyclicp1-member-equal
  (implies (and (uniqueNodeIDp cp)
                (assoc i cp)
                (assoc r1 cp)
                (member-equal i (all-indexes-in-obj r2)) 
                (matchValueRulep  (valueOf i cp) (cons r1 r2))
                (acyclicp1 r2 cp seen))
           (member-equal r1 (indexes-from-obj r2 cp)))
  :rule-classes :forward-chaining)

(defthm member-equal-acyclicp1-assoc-r1
  (implies (and (uniqueNodeIDp cp)
                (assoc r1 cp)
                (acyclicp1 r1 cp seen))
           (not (member-equal r1 (indexes-from-obj r1 cp))))
  :rule-classes :forward-chaining)


(defthm not-member-equal-i-all-indexes-in-ob
  (implies (and (uniqueNodeIDp cp)
                (assoc i cp)
                (assoc r1 cp)
		(matchValueRulep  (valueOf i cp) (cons r1 r2))
		(acyclicp1 r1 cp seen)
                (acyclicp1 r2 cp seen)
		(not (member-equal r1 
                                   (all-indexes-in-obj r2)))
		(subsetp (indexes-from-obj r2 cp)
			 (indexes-from-obj r1 cp)))
	   (not (member-equal i (all-indexes-in-obj r2))))
  :rule-classes :forward-chaining
  :hints (("Goal" :use ((:instance member-equal-matchValueRulep-acyclicp1-member-equal)
                        (:instance member-equal-acyclicp1-assoc-r1))
           :in-theory (disable member-equal-matchValueRulep-acyclicp1-member-equal 
                               member-equal-acyclicp1-assoc-r1))))
                        


(defthm not-member-all-indexes-in-obj-replaced
  (implies (and	(not (member-equal i (all-indexes-in-obj (valueOf i cp))))
                (not (member-equal i (all-indexes-in-obj r2))))
           (not (member-equal i 
                              (all-indexes-in-obj 
                               (applySubstitution (valueOf i cp)
                                                (cons r1 r2)))))))
;; Main 2
(defthm not-member-all-indexes-in-obj-replaced-1
  (implies (and (uniqueNodeIDp cp)
                (assoc i cp)
                (assoc r1 cp)
                (matchValueRulep (valueOf i cp) (cons r1 r2))
                (acyclicp1 r1 cp seen)
                (acyclicp1 r2 cp seen)
                (not (member-equal r1 
                                   (all-indexes-in-obj r2)))
                (subsetp (indexes-from-obj r2 cp)
                         (indexes-from-obj r1 cp))
                (acyclicp1 i cp seen))
           (not (member-equal i 
                              (all-indexes-in-obj 
                               (applySubstitution (valueOf i cp)
                                                (cons r1 r2))))))
  :hints (("Goal" :use ((:instance not-member-equal-i-all-indexes-in-ob)
                        (:instance not-member-all-indexes-in-obj-replaced))
           :in-theory (disable not-member-equal-i-all-indexes-in-ob 
                               not-member-all-indexes-in-obj-replaced))))

;; Main 2
(defthm not-member-all-indexes-in-obj-replace
  (implies (and (uniqueNodeIDp cp)
                (assoc i cp)
                (assoc (car rule) cp)
                (matchValueRulep (valueOf i cp) rule)
                (acyclicp1 (car rule) cp seen)
                (acyclicp1 (cdr rule) cp seen)
                (not (member-equal (car rule) 
                                   (all-indexes-in-obj (cdr rule))))
                (subsetp (indexes-from-obj (cdr rule) cp)
                         (indexes-from-obj (car rule) cp))
                (acyclicp1 i cp seen))
           (not (member-equal i 
                              (all-indexes-in-obj (applySubstitution (valueOf i cp)
                                                                   rule)))))
  :hints (("Goal" :do-not-induct t
           :do-not '(generalize fertilize )
           :use ((:instance not-member-all-indexes-in-obj-replaced-1
                            (r1 (car rule))
                            (r2 (cdr rule))))
           
           :in-theory (disable
                       not-member-all-indexes-in-obj-replaced-1 
                       not-member-equal-i-all-indexes-in-ob))))


;;------------------------------------------
;; Main Theorem (Equal Part)
;;------------------------------------------
(defthm acyclicp1-i-replaceValue-i-applySubstitution-1
  (implies (and (consp rule)
                (matchValueRulep (valueOf i cp) rule)
                (uniqueNodeIDp cp)                        
                (assoc (car rule) cp)
                (not (member-equal (car rule) 
                                   (all-indexes-in-obj (cdr
                                                        rule)))) 
		(subsetp (indexes-from-obj (cdr rule) cp)
                         (indexes-from-obj (car rule) cp))
		(acyclicp1 (cdr rule) cp seen)
                (acyclicp1 i cp seen))                          
           (acyclicp1 i (replaceValue i (applySubstitution (valueOf i cp) rule) cp) seen))
  :hints (("Goal" :do-not-induct t
           :do-not '(generalize fertilize eliminate-destructors)
           :use ((:instance not-member-ifo-applySubstitution
                            )
                 (:instance not-member-all-indexes-in-obj-replace)
                 (:instance acyclicp1-obj-member-equal-all 
                            (obj (applySubstitution (valueOf i cp) rule)))
                 (:instance acyclicp1-applySubstitution
                            (p (valueOf i cp))))

           :in-theory (disable acyclicp1-obj-member-equal-all
                               not-member-ifo-applySubstitution
                               not-member-all-indexes-in-obj-replace
                               not-member-equal-i-all-indexes-in-ob
                               acyclicp1-applySubstitution
                               acyclicp1
                               indexes-from-obj
                               union-equal
                               intersectp-equal-indexes-acyclicp1
                               member-equal
                               not-subsetp-not-member-equal-1
                               acyclicp-member-equal-all-indexes
                               uniqueNodeIDp))))

(defthm acyclicp1-i-replaceValue-i-applySubstitution-2
  (implies (and (consp rule)
                (uniqueNodeIDp cp)                        
                (assoc (car rule) cp)
                (not (member-equal (car rule) 
                                   (all-indexes-in-obj (cdr
                                                        rule)))) 
		(subsetp (indexes-from-obj (cdr rule) cp)
                         (indexes-from-obj (car rule) cp))
		(acyclicp1 (cdr rule) cp seen)
                (acyclicp1 i cp seen))                          
           (acyclicp1 i (replaceValue i (applySubstitution (valueOf i cp) rule) cp) seen))
  :hints (("Goal" :cases ((matchValueRulep (valueOf i cp) rule))
           :in-theory (disable acyclicp1
                               indexes-from-obj
                               union-equal
                               intersectp-equal-indexes-acyclicp1
                               member-equal
                               not-subsetp-not-member-equal-1
                               acyclicp-member-equal-all-indexes
                               uniqueNodeIDp))))

;;------------------------------------------
;; Main Theorem (i is equal p)
;;------------------------------------------
(defthm acyclicp1-i-replaceValue-i-applySubstitution-3
  (implies (and (consp rule)
                (uniqueNodeIDp cp)                        
                (assoc (car rule) cp)
                (not (member-equal (car rule) 
                                   (all-indexes-in-obj (cdr
                                                        rule)))) 
		(subsetp (indexes-from-obj (cdr rule) cp)
                         (indexes-from-obj (car rule) cp))
		(acyclicp (cdr rule) cp)
                (acyclicp i cp))                          
           (acyclicp i (replaceValue i (applySubstitution (valueOf i cp) rule) cp)))
  :hints (("Goal" :in-theory (e/d (acyclicp)
                                  (acyclicp1
                                   indexes-from-obj
                                   union-equal
                                   intersectp-equal-indexes-acyclicp1
                                   member-equal
                                   not-subsetp-not-member-equal-1
                                   acyclicp-member-equal-all-indexes
                                   uniqueNodeIDp)))))
           

;;------------------------------------------
;; Main Theorem (i is not reachable from p)
;;------------------------------------------
(defthm acyclicp1-replaceValue-main-21
  (implies (and (uniqueNodeIDp cp)
                (acyclicp1 p cp seen)
                (not (member-equal i (all-indexes-in-obj p)))
                (not (member-equal i (indexes-from-obj p cp))))
           (acyclicp1 p (replaceValue i obj cp) seen))
  :hints (("Goal" :in-theory (disable 
                              union-equal
                              intersectp-equal-indexes-acyclicp1
                              not-subsetp-not-member-equal-1
                              acyclicp-member-equal-all-indexes
                              uniqueNodeIDp))))
  

(defthm acyclicp1-i-replaceValue-i-applySubstitution-A-1
  (implies (and (consp rule)
                (uniqueNodeIDp cp)                        
                (assoc (car rule) cp)
                (not (member-equal (car rule) 
                                   (all-indexes-in-obj (cdr
                                                        rule)))) 
		(subsetp (indexes-from-obj (cdr rule) cp)
                         (indexes-from-obj (car rule) cp))
		(member-equal i (all-indexes-in-obj p))
                (not (member-equal i (indexes-from-obj p cp)))
		(acyclicp1 (cdr rule) cp seen)
		(acyclicp1 p cp seen)
                (acyclicp1 i cp seen))                          
           (acyclicp1 p (replaceValue i (applySubstitution (valueOf i cp) rule) cp) seen))
  :hints (("Goal" :in-theory (e/d (acyclicp)
                                  (union-equal
                                   intersectp-equal-indexes-acyclicp1
                                   not-subsetp-not-member-equal-1
                                   acyclicp-member-equal-all-indexes
                                   uniqueNodeIDp
                                   union-equal
                                   intersectp-equal-indexes-acyclicp1
                                   assoc
                                   not-subsetp-not-member-equal-1
                                   natp-car-assoc-i-c
                                   acyclicp-member-equal-all-indexes
                                   uniqueNodeIDp)))))


;;general
(defthm acyclicp1-i-replaceValue-i-applySubstitution-A-2
  (implies (and (consp rule)
                (uniqueNodeIDp cp)                        
                (assoc (car rule) cp)
                (not (member-equal (car rule) 
                                   (all-indexes-in-obj (cdr
                                                        rule)))) 
		(subsetp (indexes-from-obj (cdr rule) cp)
                         (indexes-from-obj (car rule) cp))
                (not (member-equal i (indexes-from-obj p cp))) ;;;;;
		(acyclicp1 (cdr rule) cp seen)
		(acyclicp1 p cp seen)
                (acyclicp1 i cp seen))                          
           (acyclicp1 p (replaceValue i (applySubstitution (valueOf i cp) rule) cp) seen))
  :hints (("Goal" :in-theory (enable acyclicp)
	   :cases ((member-equal i (all-indexes-in-obj p))))))



;;------------------------------------------
;; Main Theorem (Not Equal Part)
;;------------------------------------------
(encapsulate ()
             (local (in-theory (disable union-equal
                                        intersectp-equal-indexes-acyclicp1
                                        not-subsetp-not-member-equal-1
                                        acyclicp-member-equal-all-indexes
                                        uniqueNodeIDp
                                        union-equal
                                        intersectp-equal-indexes-acyclicp1
                                        assoc
                                        not-subsetp-not-member-equal-1
                                        natp-car-assoc-i-c
                                        acyclicp-member-equal-all-indexes
                                        uniqueNodeIDp)))

             ;; Lemma acyclicp1-member-equal-pfo-not-member-equal
             ;; states that if p is a natural number, cp is an ok 
             ;; constant pool, p is acyclic in cp wrt seen,
             ;; and p is reachable from i, then i is NOT reachable
             ;; from p.
             (defthm acyclicp1-member-equal-pfo-not-member-equal
               (implies (and (natp p ) 
                             (uniqueNodeIDp cp)
                             (acyclicp1 p cp seen)
                             (member-equal i (indexes-from-obj p cp)))
                        (not (member-equal p (indexes-from-obj i cp))))
               :rule-classes :forward-chaining
               :hints (("Goal" :use ((:instance member-equal-acyclicp1-assoc-r1
                                                (r1 p)))
                        :in-theory (disable member-equal-acyclicp1-assoc-r1)))))
             

;; Lemma not-member-equal-p-indexes-i-cp states that
;; if cp is an ok constant pool, the object that is associated 
;; with p in cp, (valueOf p cp), is acyclic in cp wrt (cons p seen),
;; and the object (valueOf p cp) is reachable from i, then i is NOT reachable
;; from p.
(defthm not-member-equal-p-indexes-i-cp
  (implies (and (uniqueNodeIDp cp)
		(acyclicp1 (valueOf p cp) cp (cons p seen))
		(member-equal i (indexes-from-obj (valueOf p cp) cp)))
	   (not (member-equal p (indexes-from-obj i cp))))
  :rule-classes :forward-chaining)

;; Lemma acyclicp1-i-cp-cons-p-seen states that
;; given an an ok constant pool, cp, i is acyclic 
;; in cp wrt seen, i is not equal to p, i appears 
;; as the first component of one of the cp's entries,
;; the object that is associated with p in cp, 
;; (valueOf p cp), is acyclic in cp wrt (cons p seen), 
;; and the object (valueOf p cp) is reachable from i, 
;; then i is also acyclic in cp wrt (cons p seen). 

(defthm acyclicp1-i-cp-cons-p-seen
  (implies (and (uniqueNodeIDp cp)
                (acyclicp1 i cp seen)
		(not (equal i p))
		(assoc i cp)
		(acyclicp1 (valueOf p cp) cp (cons p seen))
		(member-equal i (indexes-from-obj (valueOf p cp) cp)))
	   (acyclicp1 i cp (cons p seen)))
  :rule-classes :forward-chaining)
			
;; Lemma acyclicp1-member-equal-pfo-not-member-equal-1 
;; states that given a natural number p, an an ok 
;; constant pool, cp, p is acyclic in cp wrt seen, 
;; i is not equal to p, and  p is reachable from i,
;; then i is not reachable from p. 

(defthm acyclicp1-member-equal-pfo-not-member-equal-1
  (implies (and (natp p)
                (uniqueNodeIDp cp)
		(acyclicp1 p cp seen)
		(not (member-equal i (all-indexes-in-obj p))) ;(not (equal p i))
		(member-equal i (indexes-from-obj p cp)))
	   (not (member-equal p (indexes-from-obj i cp))))
  :rule-classes :forward-chaining)
;;[x]

;; Lemma not-member-equal-p-indexes-cdr-rule states that 
;; if i is not reachable from p, there is a match between 
;; the object (valueOf i cp) and rule, i is acyclic in cp wrt seen,
;; cp is an ok constant pool, i apprears as the first components
;; in one of the cp's entries, the set of indexes collected in 
;; cp starting from (cdr rule) are subset of that of the (car rule),
;; then (cdr rule) is not reachable from p.
(defthm not-member-equal-p-indexes-cdr-rule 
  (implies (and (not (member-equal p (indexes-from-obj i cp)))
		(matchValueRulep (valueOf i cp) rule)
		(acyclicp1 i cp seen)
                (uniqueNodeIDp cp)
                (assoc i cp)
		(subsetp (indexes-from-obj (cdr rule) cp)
			 (indexes-from-obj (car rule) cp)))
	   (not (member-equal p (indexes-from-obj (cdr rule) cp))))
  :rule-classes :forward-chaining)
;;[x]

;(i-am-here)

(defthm p-is-not-reachable-from-cdr-rule
  (implies (and 
		(natp p)
		(matchValueRulep (valueOf i cp) rule)
		(not (member-equal i (all-indexes-in-obj p)))
		(member-equal i (indexes-from-obj p cp))
		(acyclicp1 i cp seen)
		(acyclicp1 p cp seen)
                (uniqueNodeIDp cp)
                (assoc i cp)
		(subsetp (indexes-from-obj (cdr rule) cp)
			 (indexes-from-obj (car rule) cp)))
	   (not (member-equal p (indexes-from-obj (cdr rule) cp))))
  :rule-classes :forward-chaining)
;;[x]

(defthm p-is-not-reachable-from-cdr-rule-1
  (implies (and 
		(natp p)
		(matchValueRulep (valueOf i cp) rule)
		(not (equal i p))
		(member-equal i (indexes-from-obj p cp))
		(acyclicp1 i cp seen)
		(acyclicp1 p cp seen)
                (uniqueNodeIDp cp)
                (assoc i cp)
		(subsetp (indexes-from-obj (cdr rule) cp)
			 (indexes-from-obj (car rule) cp)))
	   (not (member-equal p (indexes-from-obj (cdr rule) cp))))
  :rule-classes :forward-chaining)
;;[x]

(defthm p-is-not-reachable-from-p
  (implies (and (acyclicp1 p cp seen)
		(natp p))
	   (not (member-equal p (indexes-from-obj p cp))))
  :rule-classes :forward-chaining)

;;[x]		
		
(defthm p-is-not-reachable-from-i
  (implies (and (assoc i cp)
		(natp p) 
                (uniqueNodeIDp cp)
		(acyclicp1 p cp seen)
		(member-equal i (indexes-from-obj p cp)))
	   (not (member-equal p (indexes-from-obj i cp)))))
;;[x]

(defthm indexes-car-rule-subset-i
    (implies (and (assoc i cp)
		  (uniqueNodeIDp cp)
		  (acyclicp1 i cp seen)
		  (matchValueRulep (valueOf i cp) rule)
		  (member-equal i (indexes-from-obj p cp))
		  (subsetp (indexes-from-obj (cdr rule) cp)
			   (indexes-from-obj (car rule) cp)))
	     (subsetp (indexes-from-obj (car rule) cp)
		      (indexes-from-obj i cp)))
    :hints (("Goal" :in-theory (enable acyclicp))))
;;[x]

(defthm car-rule-is-reachable-from-p
  (implies (and (natp p)
		(assoc i cp)
		(uniqueNodeIDp cp)
		(acyclicp1 i cp seen)
		(acyclicp1 p cp seen)
		(matchValueRulep (valueOf i cp) rule)
		(member-equal i (indexes-from-obj p cp))
		(subsetp (indexes-from-obj (cdr rule) cp)
			 (indexes-from-obj (car rule) cp)))
	   (not (member-equal p (indexes-from-obj (car rule) cp)))))
;;[x]

(in-theory (disable 
	    uniqueNodeIDp
	    acyclicp-member-equal-all-indexes
	    union-equal
	    member-equal-subsetp-member-equal
	    natp-car-assoc-i-c
	    not-subsetp-not-member-equal-1
	    assoc
	    member-equal-subset-index-from-obj))


(defthm cdr-rule-is-reachable-from-i
  (implies (and	(acyclicp1 cdr-rule cp seen)
		(member-equal p (all-indexes-in-obj cdr-rule))
		(member-equal i (indexes-from-obj p cp)))
	   (member-equal i (indexes-from-obj cdr-rule cp))))

(defthm not-acyclicp1-i-cp-seen
  (implies (and (member-equal i (indexes-from-obj i cp))
		(natp i))
	   (equal (acyclicp1 i cp seen)
		  nil)))

(defthm not-member-p-in-object-cdr-rule
  (implies  (and (acyclicp1 (cdr rule) cp seen)
		 (uniqueNodeIDp cp)
		 (member-equal i (indexes-from-obj p cp))
		 (assoc i cp)
		 (acyclicp1 i cp seen)
		 (subsetp (indexes-from-obj (cdr rule) cp)
			  (indexes-from-obj (car rule) cp))
		 (matchValueRulep (valueOf i cp) rule))
	    (not (member-equal p (all-indexes-in-obj (cdr rule)))))
  :hints (("Goal" :use ((:instance cdr-rule-is-reachable-from-i
				   (cdr-rule (cdr rule)))
			(:instance not-acyclicp1-i-cp-seen))
	   :in-theory (disable cdr-rule-is-reachable-from-i 
			       not-acyclicp1-i-cp-seen)
	   :do-not-induct t)))


(encapsulate ()
             (defthm |lemma 1-Subgoal*1/3|
               (implies
                (and (natp p)
                     (member-equal i (indexes-from-obj p cp))
                     (uniqueNodeIDp cp)
                     (assoc i cp)
                     (assoc (car rule) cp)
                     (matchValueRulep (valueOf i cp) rule)
                     (acyclicp1 i cp seen)
                     (acyclicp1 p cp seen)
                     (not (member-equal (car rule)
                                        (all-indexes-in-obj (cdr rule))))
                     (subsetp (indexes-from-obj (cdr rule) cp)
                              (indexes-from-obj (car rule) cp))
                     (acyclicp1 (cdr rule) cp seen))
                (acyclicp1 i cp (cons p seen)))
               :hints (("Goal" :do-not-induct t
                        :use ((:instance acyclicp1-i-cp-cons-p-seen))
                        :in-theory (disable acyclicp1-i-cp-cons-p-seen))))

             (in-theory (disable acyclicp1))
             (in-theory (disable matchValueRulep all-indexes-in-obj indexes-from-obj))
             
             (defthm |Subgoal *1/3- p is not reachable from i|
               (implies
                (and (not (consp p))
                     (natp p)
                     (assoc p cp)
                     (member-equal i (indexes-from-obj p cp))
                     (not (member-equal p seen))
                     (implies (and (consp rule)
                                   (uniqueNodeIDp cp)
                                   (assoc i cp)
                                   (assoc (car rule) cp)
                                   (matchValueRulep (valueOf i cp) rule)
                                   (acyclicp1 i cp (cons p seen))
                                   (acyclicp1 (valueOf p cp) cp (cons p seen))
                                   (not (member-equal (car rule)
                                                      (all-indexes-in-obj (cdr rule))))
                                   (subsetp (indexes-from-obj (cdr rule) cp)
                                            (indexes-from-obj (car rule) cp))
                                   (acyclicp1 (cdr rule) cp (cons p seen)))
                              (acyclicp1 (valueOf p cp)
                                         (replaceValue i (applySubstitution (valueOf i cp) rule)
                                              cp)
                                         (cons p seen)))
                     (consp rule)
                     (uniqueNodeIDp cp)
                     (assoc i cp)
                     (assoc (car rule) cp)
                     (matchValueRulep (valueOf i cp) rule)
                     (acyclicp1 i cp seen)
                     (acyclicp1 p cp seen)
                     (not (member-equal (car rule)
                                        (all-indexes-in-obj (cdr rule))))
                     (subsetp (indexes-from-obj (cdr rule) cp)
                              (indexes-from-obj (car rule) cp))
                     (acyclicp1 (cdr rule) cp seen))
                (acyclicp1 p
                           (replaceValue i (applySubstitution (valueOf i cp) rule)
                                cp)
                           seen))
               :hints (("Subgoal 2" :in-theory (enable acyclicp1))
                       ("Subgoal 1" :expand 
                        (acyclicp1 p
                                   (replaceValue i 
                                        (applySubstitution (valueOf i cp) rule)
                                        cp)
                                   seen))))


             (in-theory (enable acyclicp1))
             (in-theory (enable matchValueRulep all-indexes-in-obj indexes-from-obj))

             (defthm acyclicp1-p-replaceValue-replace
               (implies (and (uniqueNodeIDp cp)              
                             (not (member-equal i (indexes-from-obj p cp)))
                             (assoc (car rule) cp) 
                             (acyclicp1 i cp seen) 
                             (acyclicp1 p cp seen)
                             (not (member-equal 
                                   (car rule) 
                                   (all-indexes-in-obj (cdr
                                                        rule)))) 
                             (subsetp (indexes-from-obj (cdr rule) cp)
                                      (indexes-from-obj (car rule) cp))
                             (acyclicp1 (cdr rule) cp seen))
                        (acyclicp1 p (replaceValue i 
                                          (applySubstitution (valueOf i cp) rule) 
                                          cp) seen)))
             
             (defthm acyclicp1-p-replaceValue-i-applySubstitution
               (implies (and (consp rule)
                             (uniqueNodeIDp cp)                        
                             (assoc i cp) 
                             (assoc (car rule) cp) 
                             (matchValueRulep (valueOf i cp) rule) 
                             (acyclicp1 i cp seen) 
                             (acyclicp1 p cp seen)
                             (not (member-equal (car rule) 
                                                (all-indexes-in-obj (cdr
                                                                     rule)))) 
                             (subsetp (indexes-from-obj (cdr rule) cp)
                                      (indexes-from-obj (car rule) cp))
                             (acyclicp1 (cdr rule) cp seen))
                        (acyclicp1 p (replaceValue i 
                                          (applySubstitution (valueOf i cp) rule) 
                                          cp) seen))
               :hints (("Subgoal *1/3" :cases 
                        ((not (member-equal i (indexes-from-obj p cp)))))
                       ("Subgoal *1/3.2" :use 
                        ((:instance |Subgoal *1/3- p is not reachable from i|))
                        :in-theory (disable |Subgoal *1/3- p is not reachable from i|))
                       ("Subgoal *1/3.1" :use ((:instance
                                                acyclicp1-p-replaceValue-replace))
                        :in-theory (disable acyclicp1-p-replaceValue-replace)))))


(defthm acyclicp1-i-replaceValue-i-applySubstitution-general
  (implies (and (consp rule)
                (uniqueNodeIDp cp)                        
                (assoc i cp) 
		(assoc (car rule) cp) 
		(acyclicp1 i cp seen) 
                (acyclicp1 p cp seen)
                (not (member-equal (car rule) 
                                   (all-indexes-in-obj (cdr
                                                        rule)))) 
		(subsetp (indexes-from-obj (cdr rule) cp)
                         (indexes-from-obj (car rule) cp))
		(acyclicp1 (cdr rule) cp seen))
           (acyclicp1 p (replaceValue i (applySubstitution (valueOf i cp) rule) cp) seen))
  :hints (("Goal" :cases ((matchValueRulep (valueOf i cp) rule)))))


(defthm acyclicp1-p-replaceValue-i-obj-cp
  (implies (and (acyclicp1 p cp seen)
                (uniqueNodeIDp cp)
                (not (assoc i cp)))
           (acyclicp1 p (replaceValue i obj cp) seen)))

(defthm acyclicp1-i-replaceValue-i-applySubstitution-general-*1
  (implies (and (uniqueNodeIDp cp)                        
		(assoc (car rule) cp) 
		(acyclicp1 i cp seen) 
                (acyclicp1 p cp seen)
                (not (member-equal (car rule) 
                                   (all-indexes-in-obj (cdr
                                                        rule)))) 
		(subsetp (indexes-from-obj (cdr rule) cp)
                         (indexes-from-obj (car rule) cp))
		(acyclicp1 (cdr rule) cp seen))
           (acyclicp1 p (replaceValue i (applySubstitution (valueOf i cp) rule) cp) seen))
  :hints (("Goal" :cases ((assoc i cp)))))

(defthm acyclicp-i-replaceValue-i-applySubstitution-general
  (implies (and (consp rule)
                (uniqueNodeIDp cp)                        
		(assoc (car rule) cp) ;; 
		(acyclicp i cp) ;;
                (acyclicp p cp)
                (not (member-equal (car rule) 
                                   (all-indexes-in-obj (cdr
                                                        rule)))) 
		(subsetp (indexes-from-obj (cdr rule) cp)
                         (indexes-from-obj (car rule) cp))
		(acyclicp (cdr rule) cp))
           (acyclicp p (replaceValue i (applySubstitution (valueOf i cp) rule) cp)))
  :hints (("Goal" :in-theory (enable acyclicp))))

;(i-am-here)
; lemma 6
(defthm acyclicp-i-replaceValue-i-applySubstitution-general-1
  (implies (and (ok-rulep rule cp)
                (acyclicp p cp)
                (acyclicp i cp)
                (uniqueNodeIDp cp))
           (acyclicp p (replaceValue i (applySubstitution (valueOf i cp) rule) cp))))

(defthm dref-replaceValue
  (implies (and 
            (uniqueNodeIDp cp)                        
            (equal (dref (car rule) cp)
                   (dref (cdr rule) cp)) ;; 
            (assoc (car rule) cp) ;; 
            (acyclicp i cp) ;;
            (acyclicp p cp)
            (acyclicp (cdr rule) cp)
           (not (member-equal (car rule) 
                              (all-indexes-in-obj (cdr
                                                   rule))))
           (subsetp (indexes-from-obj (cdr rule) cp)
                    (indexes-from-obj (car rule) cp)))
           (equal (dref p (replaceValue i (applySubstitution (valueOf i cp) rule) cp))
                  (dref p cp))))
		

(defthm dref-replaceValue-ok-rulep
  (implies (and (ok-rulep rule cp)
                (acyclicp p cp)
                (acyclicp i cp)
                (uniqueNodeIDp cp))
           (equal (dref p (replaceValue i (applySubstitution (valueOf i cp) rule) cp))
                  (dref p cp))))

(defthm acyclicp1-apply-rule-to-entry-1
  (implies (and (uniqueNodeIDp cp)                        
		(assoc (car rule) cp) ;; 
		(acyclicp1 i cp seen) ;;
                (acyclicp1 p cp seen)
                (not (member-equal (car rule) 
                                   (all-indexes-in-obj (cdr
                                                        rule)))) 
		(subsetp (indexes-from-obj (cdr rule) cp)
                         (indexes-from-obj (car rule) cp))
		(acyclicp1 (cdr rule) cp seen))
           (acyclicp1 p (apply-rule-to-entry-1 rule i cp) seen)))
           

(in-theory (disable apply-rule-to-entry-1))
           
(defthm acyclicp-apply-rule-to-entry-1
  (implies (and (uniqueNodeIDp cp)                        
		(assoc (car rule) cp) ;; 
		(acyclicp i cp) ;;
                (acyclicp p cp)
                (not (member-equal (car rule) 
                                   (all-indexes-in-obj (cdr
                                                        rule)))) 
		(subsetp (indexes-from-obj (cdr rule) cp)
                         (indexes-from-obj (car rule) cp))
		(acyclicp (cdr rule) cp))
           (acyclicp p (apply-rule-to-entry-1 rule i cp)))
  :hints (("Goal" :in-theory (enable acyclicp))))

;; Main
(defthm acyclicp-apply-rule-to-entry-1-new
  (implies (and (ok-rulep rule cp)
                (acyclicp p cp)
                (acyclicp i cp)
                (uniqueNodeIDp cp))
           (acyclicp p (apply-rule-to-entry-1 rule i cp))))


(defthm dref-apply-rule-to-entry-1
  (implies (and 
            (uniqueNodeIDp cp)                        
            (equal (dref (car rule) cp)
                   (dref (cdr rule) cp)) ;; 
            (assoc (car rule) cp) ;; 
            (acyclicp i cp) ;;
            (acyclicp p cp)
            (acyclicp (cdr rule) cp)
            (not (member-equal (car rule) 
                               (all-indexes-in-obj (cdr
                                                    rule))))
            (subsetp (indexes-from-obj (cdr rule) cp)
                     (indexes-from-obj (car rule) cp)))
           
           (equal (dref p (apply-rule-to-entry-1 rule i cp))
                  (dref p cp)))
  :hints (("Goal" :in-theory (enable acyclicp apply-rule-to-entry-1))))

;; Main
(defthm dref-apply-rule-to-entry-1-new
  (implies (and (ok-rulep rule dag)
                (uniqueNodeIDp dag)                        
                (acyclicp i dag);;
                (acyclicp p dag))
           (equal (dref p (apply-rule-to-entry-1 rule i dag))
                  (dref p dag)))
  :hints (("Goal" :in-theory (enable ok-rulep))))


;; Now we prove that given an all-indexes-acyclicp-cp, cp, and an acyclicp 
;; object p in cp, the result of dreferencing p in cp contains NO indexes.

(defthm no-pointersp-dref
  (implies (and (acyclic-constant-poolp cp)
                (acyclicp p cp))
           (no-indexesp (dref p cp))))

