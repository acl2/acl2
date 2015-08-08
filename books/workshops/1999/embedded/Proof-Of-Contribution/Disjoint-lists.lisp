
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;
;;;;           Theorems about disjunctness of lists
;;;;
;;;;   Load with (ld "Disjoint-lists.lisp")
;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")


(include-book "Proof-Of-Equiv-From-M-Corr")

;;
;; Boolean version of member-equal function.
;;
;; The call (member-equal el l) returns the tail of the list
;; l, starting from the el element (if any). Thus, one cannot compare
;; member-equalities upon different lists. E.g.,
;; (equal (member-equal el l) (member-equal el (append l l2)))
;; does not hold - also when el belongs to l.
;; This justified our redesign of the member-equal function.
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


;;
;; Predicate for the absence of duplicates within a list.
;;

(defun no-duplicates-p (l)
 (if (endp l)
     t
     (and (not (member-equal-bool (car l) (cdr l)))
          (no-duplicates-p (cdr l)))))


(defthm no-dup-1
 (implies
  (and
   (in-range idx l)
   (not (member-equal-bool el l)))
  (not (equal el (nth idx l)))))


(defthm no-dup-3
 (implies
  (and
   (in-range idx l)
   (in-range idx2 l)
   (not (equal idx idx2))
   (no-duplicates-p l))
  (not (equal (nth idx2 l) (nth idx l)))))


;;
;; Main properties for the property of absence of duplicates
;;

;;
;; Name      : no-duplicates-of-append-no-duplicates-incomponents
;; Statement : (no-duplicates (l1 * l2)) ---> (no-duplicates-p l1) ^ (no-duplicates-p l1)
;;


;;
;; Name      : no-duplicates-in-append-imply-different-elements-in-components
;; Statement : (no-duplicates (l1 * l2)) ^ (el1 in l1) ^ (el2 in l2) ---> el1 <> el2
;;

;;
;; Name      : no-duplicates-in-append-imply-different-elements-in-components-2
;; Statement : (no-duplicates (l1 * l2)) ^ (el in l1)  ---> (el not-in l2)
;;



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
;; Disjunction property between lists.
;; Two list are defined disjunct if their append contains no duplicates.
;;


(defun no-intersection-p (l1 l2)
 (no-duplicates-p (append l1 l2)))


;;
;; Main properties of disjunction properties:
;;


;;
;; Name      : disjoint-sets-have-no-common-els-2
;; Statement : (no-intersection-p l1 l2) ^ (el in l2) ---> (el not-in l1)
;;



(defthm disjoint-sets-have-no-common-els-2
 (implies
  (and
   (no-intersection-p l1 l2)
   (member-equal-bool el l2))
  (not (member-equal-bool el l1))))






;;
;; Generalized append function.
;; It receives a list of lists, and return the append of the lists it contains.
;;
;; The main theorem we intend to prove is that, whenever a generalized append of lists
;; contains no duplicates, each pair of lists is disjunct.
;;
;; The idea of the theorem is the following.
;; Consider the i-th and j-th lists contained into the ll list of lists. We assume i < j.
;; We first that the i-th list is contained within the generalized append of
;; the first i elements of ll, which we call append-first-i-of-ll.
;; But, since i < j, the i-th list is also contained within the generalized append of
;; the first j elements of ll, which we call append-first-j-of-ll.
;; We then prove that the j-th list is contained within the generalized append of
;; the last |ll|-j elements of ll, which we call append-last-ll-j-of-ll.
;; But the generalized append of ll, append-ll, results from appending append-first-j-of-ll and
;; append-last-ll-j-of-ll; thus, since append-ll is free of duplicates,
;; append-first-j-of-ll and append-last-ll-j-of-ll are disjoint - that is, they contain no common elements.
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
;; Function extracting the first n elements of a list
;; (taken from public Acl-2 list book)
;;

(defun firstn (n l)
  (declare (xargs :measure (nfix n)
		  :guard (and (integerp n) (<= 0 n)
			      (true-listp l))))
  (cond ((endp l) nil)
	((zp n) nil)
	(t (cons (car l) (firstn (1- n) (cdr l))))))


;;
;; Main properties of function taking the first n elements of a list
;;

;;
;; Name      : append-lists-firstn-nthcdr, append-lists-firstn-nthcdr-2
;; Statement : (true-listp l) ---> (append-lists l) = (append-lists (firstn n l)) * (append-lists (nthcdr n l))
;;



(defthm append-lists-firstn-nthcdr
 (implies
  (true-listp l)
  (equal (append (append-lists (firstn n l)) (append-lists (nthcdr n l)))
         (append-lists l))))

(defthm append-lists-firstn-nthcdr-2
 (implies
  (true-listp l)
  (equal (append-lists l)
         (append (append-lists (firstn n l)) (append-lists (nthcdr n l))))))

(in-theory (disable append-lists-firstn-nthcdr-2))


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

;;
;; Name      :  no-duplicates-in-append-means-partitioning
;; Statement : (true-listp ll) ^ (0 <= idx2 < |l|) ^ (no-duplicates-p (append-lists ll)) --->
;;             (no-intersection-p (append-lists (firstn idx2 ll)) (append-lists (nthcdr idx2 ll))))
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

(in-theory (disable
            member-of-nth-entry-of-ll-is-member-of-append-of-nthcdr-n-entries
            ;member-of-nth-entry-of-ll-is-member-of-append-of-first-n-entries
            append-lists-firstn-nthcdr))


(defthm no-duplicates-in-append-means-partitioning
 (implies
  (and
   (true-listp ll)
   (no-duplicates-p (append-lists ll))
   (in-range idx2 ll))
  (no-intersection-p (append-lists (firstn idx2 ll))
                     (append-lists (nthcdr idx2 ll))))
 :hints (("Goal" :use (:instance append-lists-firstn-nthcdr-2 (l ll) (n idx2)))))

(in-theory (disable no-duplicates-in-append-means-partitioning no-intersection-p))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Main theorem (in four equivalent forms)
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;



;;
;; Name      : generalized-disjunctivity-of-els-2
;; Statement : (no-duplicates-p (append-lists ll)) ^ (0 <= idx1 <= idx2 < |ll|) ^
;;             (el1 in (nth idx1 ll)) ---> (el1 not-in (nth idx2 ll))
;;

;;
;; Name      : different-list-indexes-are-different
;; Statement : (no-duplicates-p (append-lists ll)) ^ (0 <= idx1 < |ll|) ^ (0 <= idx2 < |ll|) ^
;;             (idx1 <> idx2) ^ (el1 in (nth idx1 ll)) ^ (el2 in (nth idx2 ll)) ---> el1 <> el2
;;

;;
;; Name      : different-list-indexes-are-different-2
;; Statement : (no-duplicates-p (append-lists ll)) ^ (0 <= idx1 < |ll|) ^ (0 <= idx2 < |ll|) ^
;;             (el1 in (nth idx1 ll)) ---> (el2 not-in (nth idx2 ll))
;;



(defthm generalized-disjunctivity-of-els-2
 (implies (and
           (true-listp ll)
           (no-duplicates-p (append-lists ll))
           (in-range idx1 ll)
           (in-range idx2 ll)
           (< idx1 idx2)
           (member-equal-bool el1 (nth idx1 ll)))
          (not (member-equal-bool el1 (nth idx2 ll))))
 :hints (("Goal" :use ((:instance no-duplicates-in-append-means-partitioning (ll ll) (idx2 idx2))
                       (:instance member-of-nth-entry-of-ll-is-member-of-append-of-nthcdr-n-entries (el1 el1) (idx1 idx2) (ll ll))
                       (:instance member-of-nth-entry-of-ll-is-member-of-append-of-first-n-entries-in-excess
                                  (el1 el1) (idx1 idx1) (idx2 idx2) (ll ll))))))




(defthm different-list-indexes-are-different
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


(defthm generalized-disjunctivity-unordered-2
 (implies (and
           (true-listp ll)
           (no-duplicates-p (append-lists ll))
           (in-range idx1 ll)
           (in-range idx2 ll)
           (not (equal idx1 idx2))
           (member-equal-bool el1 (nth idx1 ll)))
          (not (member-equal-bool el1 (nth idx2 ll))))
 :hints (("Goal" :use ((:instance different-list-indexes-are-different
                                 (idx1 idx1) (idx2 idx2) (ll ll))
          (:instance generalized-disjunctivity-of-els-2
                                 (ll ll) (idx1 idx1) (idx2 idx2) (el1 el1))))))


(defthm in-range-is-member-eq-bool
 (implies
  (in-range idx l)
  (member-equal-bool (nth idx l) l))
 :hints (("Goal" :in-theory (enable in-range member-equal-bool))))



(defthm l1
 (implies
  (and
   (true-listp ll)
   (in-range idx1 ll))
  (and
   (true-listp (nthcdr idx1 ll))
   (equal (car (nthcdr idx1 ll)) (nth idx1 ll) )
   (equal (cdr (nthcdr idx1 ll)) (nthcdr (1+ idx1) ll))))
 :hints (("Goal" :in-theory (enable in-range))))

(defthm append-lists-car-cdr
 (implies
  (true-listp ll)
  (equal (append-lists ll)
	 (append
	  (car ll)
	  (append-lists (cdr ll))))))

(in-theory (disable append-lists-car-cdr))

(defthm append-lists-first-middle-end
 (implies
  (and
   (in-range idx1 ll)
   (true-listp ll))
  (equal (append-lists ll)
	 (append
	  (append-lists (firstn idx1 ll))
	  (append
	   (nth idx1 ll)
	   (append-lists (nthcdr (1+ idx1) ll))))))
:hints (("Goal" :use (l1
		      (:instance append-lists-firstn-nthcdr-2 (l ll) (n idx1))
		      (:instance append-lists-car-cdr (ll (nthcdr idx1 ll)))))))


(defthm no-duplicates-l1-l2-l3-means-no-duplicates-l2
 (implies
  (no-duplicates-p (append l1 (append l2 l3)))
  (no-duplicates-p l2))
 :hints (("Goal" :use
	          ((:instance no-duplicates-of-append-no-duplicates-incomponents (l1 l1) (l2 (append l2 l3)))
		   (:instance no-duplicates-of-append-no-duplicates-incomponents (l1 l2) (l2 l3))))))


(defthm no-duplicates-all-implies-no-duplicates-one
 (implies (and
           (true-listp ll)
           (no-duplicates-p (append-lists ll))
           (in-range idx1 ll))
	  (no-duplicates-p (nth idx1 ll))))


(in-theory (disable
		    no-dup-1
		    no-dup-3
		    no-member-of-append-no-member-of-components
		    no-duplicates-of-append-no-duplicates-incomponents
		    no-duplicates-in-append-imply-different-elements-in-components-2
		    disjoint-sets-have-no-common-els-2
		    append-lists-firstn-nthcdr
		    append-lists-firstn-nthcdr-2
		    member-of-nth-entry-of-ll-is-member-of-append-of-nthcdr-n-entries
		    member-of-nth-entry-of-ll-is-member-of-append-of-first-n-entries-in-excess
		    member-of-nth-entry-of-ll-is-member-of-append-of-nthcdr-n-entries
		    no-duplicates-in-append-means-partitioning
		    generalized-disjunctivity-of-els-2
		    different-list-indexes-are-different
		    in-range-is-member-eq-bool
		    l1
		    append-lists-car-cdr
		    append-lists-first-middle-end
		    no-duplicates-l1-l2-l3-means-no-duplicates-l2
		    no-duplicates-all-implies-no-duplicates-one))


(in-theory (enable in-range))

(defthm no-member-holds-on-firstn
 (implies
  (not (member-equal-bool el l))
  (not (member-equal-bool el (firstn idx l))))
 :rule-classes nil)

(defthm no-duplicates-means-an-element-not-before-neither-after
 (implies
  (and
   (in-range idx l)
   (no-duplicates-p l))
  (and
   (not (member-equal-bool (nth idx l) (nthcdr (1+ idx) l)))
   (not (member-equal-bool (nth idx l) (firstn idx l)))))
 :hints (("Goal" :in-theory (enable no-dup-1))))

(defthm firstns-do-not-contain-nth-el
 (implies
  (and
   (true-listp ll)
   (no-duplicates-p (append-lists ll))
   (in-range gem1 ll)
   (in-range gem2 ll)
   (in-range idx (nth gem1 ll))
   (in-range idx (nth gem2 ll)))
  (not (member-equal-bool (nth idx (nth gem2 ll)) (firstn idx (nth gem1 ll)))))
 :hints (("Goal"
	  :in-theory (enable in-range-is-member-eq-bool
			     no-duplicates-means-an-element-not-before-neither-after
			     no-duplicates-all-implies-no-duplicates-one)
	  :cases ( (equal gem1 gem2)))
	 ("Subgoal 2"
	  :use ((:instance no-member-holds-on-firstn
			   (el (nth idx (nth gem2 ll))) (l (nth gem1 ll)))
		(:instance generalized-disjunctivity-unordered-2
			  (idx1 gem1) (idx2 gem2) (el1 (nth idx (nth gem2 ll))))))))



(defthm no-duplicates-means-an-element-does-not-appear-after-its-position
 (implies
  (and
   (no-duplicates-p l)
   (in-range idx l))
  (not (member-equal-bool (nth idx l) (cdr (nthcdr idx l)))))
 :rule-classes nil)




