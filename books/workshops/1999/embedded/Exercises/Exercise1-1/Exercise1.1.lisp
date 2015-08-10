
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;
;;;;              Exercise 1.1
;;;;
;;;;   Load with (ld "Exercise1.1.lisp")
;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(in-package "ACL2")

;;; Some basic arithmetics lemmas about ``+''.

(defthm constant-fold-+
  (implies (acl2::syntaxp (and (quotep x) (quotep y)))
           (equal (+ x (+ y z)) (+ (+ x y) z))))

(defthm commutativity2-of-+
  (equal (+ x y z) (+ y x z))
  :hints (("goal" :use ((:instance acl2::associativity-of-+
                                   (acl2::x y)
                                   (acl2::y x)
                                   (acl2::z z))
                        (:instance acl2::associativity-of-+
                                   (acl2::x x)
                                   (acl2::y y)
                                   (acl2::z z))
                        (:instance acl2::commutativity-of-+
                                   (acl2::x x)
                                   (acl2::y y)))
           :in-theory (disable acl2::associativity-of-+
                               acl2::commutativity-of-+))))


;;
;; Basic definitions:
;;
;; - (in-range idx l) : holds T iff idx is an integer  0 <= idx < (len l)
;;
;; - (member-equal-bool el l) : holds T iff el is equal to an element of the list l.
;;   The call (member-equal el l) returns the tail of the list
;;   l, starting from the el element (if any). Thus, one cannot compare
;;   member-equalities upon different lists. E.g.,
;;   (equal (member-equal el l) (member-equal el (append l l2)))
;;   does not hold - also when el belongs to l.
;;   This justifies our ``boolean'' redesign of the member-equal function.
;;
;; - (no-duplicates-p l) : holds T iff l does not contain duplicate entries.
;;
;; - (no-intersection-p l1 l2): holds T iff l1 and l2 characterize disjunct sets of values.
;;
;; - (firstn n l) : Function extracting the first n elements of a list
;;                  (taken from public Acl-2 list book)
;;

(defun in-range (idx l)
 (and
  (integerp idx)
  (>= idx 0)
  (< idx (len l))))

(defun member-equal-bool (el l)
 (declare (xargs :guard (true-listp l)))
 (cond ((endp l) nil)
       ((equal el (car l)) t)
       (t (member-equal-bool el (cdr l)))))


(defun no-duplicates-p (l)
 (if (endp l)
     t
     (and (not (member-equal-bool (car l) (cdr l)))
          (no-duplicates-p (cdr l)))))

(defun no-intersection-p (l1 l2)
 (no-duplicates-p (append l1 l2)))

(defun firstn (n l)
  (declare (xargs :measure (nfix n)
		  :guard (and (integerp n) (<= 0 n)
			      (true-listp l))))
  (cond ((endp l) nil)
	((zp n) nil)
	(t (cons (car l) (firstn (1- n) (cdr l))))))


;;
;; Some key properties of member-equal-bool:
;;
;; - if el does not belong to l according to member-equal-bool,
;;   then it is different from any idx-th element of l.
;;
;; - the idx-th element of l belongs to l according to member-equal-bool
;;

(defthm not-member-differs-from-any-element
 (implies
  (and
   (in-range idx l)
   (not (member-equal-bool el l)))
  (not (equal el (nth idx l)))))


(defthm in-range-is-member-eq-bool
 (implies
  (in-range idx l)
  (member-equal-bool (nth idx l) l)) )


;;
;; Some key properties for no-duplicates-p
;;
;; - if l has no duplicates according to no-duplicates-p, then
;;   the idx-th element of l is different from the idx2-th element of l
;;   (proviso that idx <> idx2).
;;
;;
;; Name      : no-duplicates-of-append-no-duplicates-incomponents
;; Statement : (no-duplicates-p (l1 * l2)) ---> (no-duplicates-p l1) ^ (no-duplicates-p l1)
;;
;;
;; Name      : no-duplicates-in-append-imply-different-elements-in-components
;; Statement : (no-duplicates-p (l1 * l2)) ^ (el1 in l1) ^ (el2 in l2) ---> el1 <> el2
;;
;;
;; Name      : no-duplicates-in-append-imply-different-elements-in-components-2
;; Statement : (no-duplicates-p (l1 * l2)) ^ (el in l1)  ---> (el not-in l2)
;;



(defthm no-duplicates-list-contains-different-entries
 (implies
  (and
   (in-range idx l)
   (in-range idx2 l)
   (not (equal idx idx2))
   (no-duplicates-p l))
  (not (equal (nth idx2 l) (nth idx l)))))

(defthm no-member-of-append-no-member-of-components
 (implies (not (member-equal-bool el (append l1 l2)))
          (and
           (not (member-equal-bool el l1))
           (not (member-equal-bool el l2)))))

(defthm no-duplicates-of-append-no-duplicates-incomponents
 (implies (no-duplicates-p (append l1 l2))
          (and
           (no-duplicates-p l1)
           (no-duplicates-p l2))))


(defthm no-duplicates-in-append-imply-different-elements-in-components-2
 (implies (and
           (no-duplicates-p (append l1 l2))
           (member-equal-bool el1 l1))
          (not (member-equal-bool el1 l2))))






;;
;; A key property of no-intersection-p:
;;
;;
;; Name      : disjoint-sets-have-no-common-elements
;; Statement : (no-intersection-p l1 l2) ^ (el in l2) ---> (el not-in l1)
;;



(defthm disjoint-sets-have-no-common-elements
 (implies
  (and
   (no-intersection-p l1 l2)
   (member-equal-bool el l2))
  (not (member-equal-bool el l1))))






;;
;; Generalized append function append-lists
;; It receives a list of lists, and return the append of the lists it contains.
;;
;; The main lemma states that whenever a generalized append of lists
;; contains no duplicates, each pair of lists is disjunct.
;;
;; The idea of the theorem is the following.
;; Consider the i-th and j-th lists contained into the ll list of lists. We assume i < j.
;; We first prove that the i-th list is contained within the generalized append of
;; the first i elements of ll, which we call append-first-i-of-ll.
;; But, since i < j, the i-th list is also contained within the generalized append of
;; the first j elements of ll, which we call append-first-j-of-ll.
;; We then prove that the j-th list is contained within the generalized append of
;; the last |ll|-j elements of ll, which we call append-last-ll-j-of-ll.
;; But the generalized append of ll, append-ll, results from appending append-first-j-of-ll and
;; append-last-ll-j-of-ll; thus, since append-ll is free of duplicates,
;; append-first-j-of-ll and append-last-ll-j-of-ll are disjoint -
;;;that is, they contain no common elements.
;; This implies that the i-th and j-th lists are disjoint as well.
;;
;;
;;
;;        append-first-i-of-ll                      append-last-ll-j-of-ll
;;                 |                                           |
;;                 |     append-first-j-of-ll                  V
;;            |----+-----------------------------------|----------------|
;;            |    |                                   |                |
;;            |    V                                   |                |
;;            |---------|                              |                |
;;            |         |                              |                |
;;            |         |                              |                |
;;            /---------------------------------------------------------\
;;            |       | |                              | |              |
;;            \---------------------------------------------------------/
;;                     ^                                ^
;;                     |                                |
;;                    i-th                             j-th
;;                    list                             list
;;

(defun append-lists (list-of-lists)
 (if (endp list-of-lists)
     nil
     (append (car list-of-lists)
             (append-lists (cdr list-of-lists)))))




;;
;; A key property of append-lists:
;;

;;
;; Name      : append-lists-firstn-nthcdr
;; Statement : (true-listp l) ---> (append-lists l) = (append-lists (firstn n l)) * (append-lists (nthcdr n l))
;;



(defthm append-lists-firstn-nthcdr
 (implies
  (true-listp l)
  (equal (append-lists l)
         (append (append-lists (firstn n l)) (append-lists (nthcdr n l))))))

(in-theory (disable append-lists-firstn-nthcdr))


;;
;; Lemmas to the proof
;;


;;
;; Name      : member-of-nth-entry-of-ll-is-member-of-append-of-first-n-entries-in-excess
;; Statement : (0 <= idx1 < idx2 < |l|) ^ (el1 in (nth idx1 ll)) ---> (el1 in (append-lists (firstn idx2 ll)))
;;

;;
;; Name      : member-of-nth-entry-of-ll-is-member-of-append-of-nthcdr-n-entries
;; Statement : (0 <= idx1 < |l|) ^ (el1 in (nth idx1 ll)) ---> (el1 in (append-lists (nthcdr idx1 ll)))
;;



(defthm member-of-nth-entry-of-ll-is-member-of-append-of-first-n-entries-in-excess
 (implies
  (and
   (in-range idx1 ll)
   (in-range idx2 ll)
   (< idx1 idx2)
   (member-equal-bool el1 (nth idx1 ll)))
  (member-equal-bool el1 (append-lists (firstn idx2 ll)))))

(defthm member-of-nth-entry-of-ll-is-member-of-append-of-nthcdr-n-entries
 (implies
  (and
   (in-range idx1 ll)
   (member-equal-bool el1 (nth idx1 ll)))
  (member-equal-bool el1 (append-lists (nthcdr idx1 ll)))))

(in-theory (disable member-of-nth-entry-of-ll-is-member-of-append-of-nthcdr-n-entries ))


(in-theory (disable no-intersection-p))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Main lemma
;;
;; - first we show that, if idx1<idx2 and (no-duplicates-p (append-lists ll)),
;;   then a generic element in (nth idx1 ll) does not belong to (nth idx2 ll)
;; - then we extend the statement to consider the more general case in which idx1<>idx2.
;; - finally we restate it in terms of the i-th element of (nth idx1 ll) and the j-th
;;   element of (nth idx2 ll):
;;   if idx1<>idx2 and (no-duplicates-p (append-lists ll)), then
;;   (nth i (nth idx1 ll)) <> (nth j (nth idx2 ll))
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;



;;
;; Name      : generalized-disjunctivity-on-elements
;; Statement : (no-duplicates-p (append-lists ll)) ^ (0 <= idx1 <= idx2 < |ll|) ^
;;             (el1 in (nth idx1 ll)) ---> (el1 not-in (nth idx2 ll))
;;



(defthm generalized-disjunctivity-on-elements
 (implies (and
           (true-listp ll)
           (no-duplicates-p (append-lists ll))
           (in-range idx1 ll)
           (in-range idx2 ll)
           (< idx1 idx2)
           (member-equal-bool el1 (nth idx1 ll)))
          (not (member-equal-bool el1 (nth idx2 ll))))
 :hints (("Goal" :use (
                       (:instance append-lists-firstn-nthcdr (l ll) (n idx2))
                       (:instance member-of-nth-entry-of-ll-is-member-of-append-of-nthcdr-n-entries (idx1 idx2))
                       member-of-nth-entry-of-ll-is-member-of-append-of-first-n-entries-in-excess))))




(defthm different-indexes-are-<>
 (implies
  (and
   (in-range idx1 ll)
   (in-range idx2 ll))
  (equal
   (not (equal idx1 idx2))
   (or
    (< idx1 idx2)
    (< idx2 idx1))))
 :hints (("Goal" :in-theory (enable in-range))))

(in-theory (disable in-range))


(defthm generalized-disjunctivity-on-unordered-elements
 (implies (and
           (true-listp ll)
           (no-duplicates-p (append-lists ll))
           (in-range idx1 ll)
           (in-range idx2 ll)
           (not (equal idx1 idx2))
           (member-equal-bool el1 (nth idx1 ll)))
          (not (member-equal-bool el1 (nth idx2 ll))))
 :hints (("Goal" :use (different-indexes-are-<>
                       generalized-disjunctivity-on-elements))))


(defthm generalized-disjunctivity-on-different-lists
 (implies (and
           (true-listp ll)
           (no-duplicates-p (append-lists ll))
           (in-range idx1 ll)
           (in-range idx2 ll)
           (in-range i (nth idx1 ll))
           (in-range j (nth idx2 ll))
           (not (equal idx1 idx2)))
          (not (equal (nth i (nth idx1 ll)) (nth j (nth idx2 ll)))))
 :hints (("Goal" :use ((:instance generalized-disjunctivity-on-unordered-elements
                                  (el1 (nth i (nth idx1 ll))))
                       (:instance in-range-is-member-eq-bool
                                  (idx i)
                                  (l (nth idx1 ll)))))))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; The required theorem
;;
;; - first we introduce a lemma, no-duplicates-all-implies-no-duplicates-one, stating that,
;;   if (append-lists ll) is duplicate-free, then every element of ll is duplicate-free.
;; - finally, we simply prove the theorem by case analysys. In the case where we consider
;;   different entries of the list of lists, then the generalized-disjunctivity-on-different-lists
;;   lemma is used. Otherwise, no-duplicates-all-implies-no-duplicates-one is used.
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(defthm no-duplicates-l1-l2-l3-means-no-duplicates-l2
 (implies
  (no-duplicates-p (append l1 (append l2 l3)))
  (no-duplicates-p l2))
 :hints (("Goal" :use
	          ((:instance no-duplicates-of-append-no-duplicates-incomponents (l1 l1) (l2 (append l2 l3)))
		   (:instance no-duplicates-of-append-no-duplicates-incomponents (l1 l2) (l2 l3))))))


(in-theory (enable in-range))

(defthm no-duplicates-all-implies-no-duplicates-one
 (implies (and
           (true-listp ll)
           (no-duplicates-p (append-lists ll))
           (in-range idx1 ll))
	  (no-duplicates-p (nth idx1 ll))))



(defthm theorem-exercise-1-1
 (implies (and
           (true-listp ll)
           (no-duplicates-p (append-lists ll))
           (in-range idx1 ll)
           (in-range idx2 ll)
           (in-range i (nth idx1 ll))
           (in-range j (nth idx2 ll))
           (or
            (not (equal idx1 idx2))
            (not (equal i j))))
          (not (equal (nth i (nth idx1 ll)) (nth j (nth idx2 ll)))))
 :hints (("Goal" :cases ((equal idx1 idx2)))
         ("Subgoal 1" :use (no-duplicates-all-implies-no-duplicates-one
                            (:instance no-duplicates-list-contains-different-entries
                                       (idx i) (idx2 j) (l (nth idx1 ll)))))))


