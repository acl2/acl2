; complexity-of-linear-search.lsp                     William D. Young

(in-package "ACL2")
(include-book "asymptotic-analysis-support")

(set-irrelevant-formals-ok t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;                                                                  ;;
;;                          BINARY SEARCH                           ;;
;;                                                                  ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Given a sorted list, return the largest element via binary search.

;; >>> Note that I needed to change the code here because the step counts
;;     differ depending on whether I go left or right. 

; def BinarySearch( lst, key ):
;     low = 0
;     high = len(lst) - 1
;     while (high >= low):
;         mid = (low + high) // 2
;         if key == lst[mid]:
;             return mid
;         elif key < lst[mid]:
;             high = mid - 1
;         else:
;             low = mid + 1
;     return -1

(defun bs-here ()
  t)

;; SORTED

;; >> Unlike linearsearch, we need for the values in the list to be 
;;    numbers because we're assuming that we can use < to compare them.
;;    This only works for numbers.  I could use a different comparator
;;    such as lexorder.

(defun sorted (lst)
  (if (endp lst)
      t
    (if (endp (cdr lst))
	t
      (and (<= (car lst) (cadr lst))
	   (sorted (cdr lst))))))

(defun sorted-lessp-ind (low high)
  (declare (xargs :measure (nfix (1+ (- high low)))))
  (if (or (< high low)
	  (not (natp low))
	  (not (natp high)))
      t
    (sorted-lessp-ind (1+ low) high)))

; (in-theory (disable  less-equal-transitive))

(defthm sorted-low
  (implies (and (sorted lst)
		(natp low)
		(< (1+ low) (len lst)))
	   (<= (nth low lst) (nth (1+ low) lst))))

(defthm sorted-lessp
  (implies (and (sorted lst)
		(< low (len lst))
		(< high (len lst))
		(natp low)
		(natp high)
		(<= low high))
	   (<= (nth low lst) (nth high lst)))
  :hints (("goal" :instructions ((:induct (sorted-lessp-ind low high))
                       (:casesplit (equal low high))
                       :bash (:demote 2)
                       (:dive 1 1)
                       (:= t)
                       :up
                       :s-prop :top :promote :promote (:dive 1)
                       (:rewrite less-equal-transitive
                                 ((y (nth (1+ low) lst))))
                       (:dive 1)
                       (:rewrite sorted-low)
                       :bash))))

;; >> Could combine the following two lemmas

(defthm sorted-lessp2
  (implies (and (sorted lst)
		(natp low)
		(natp high)
		(< high (len lst))
		(<= low high)
		(< (nth high lst) key))
	   (not (equal key (nth low lst)))))

(defthm sorted-lessp3
  (implies (and (sorted lst)
		(natp low)
		(natp high)
		(< high (len lst))
		(<= low high)
		(< key (nth low lst)))
	   (not (equal key (nth high lst)))))

(defthm sorted-cons
  (implies (consp lst)
	   (equal (sorted (cons x lst))
		  (and (<= x (car lst))
		       (sorted lst)))))

;; SLICE

;; >> I could use a different notion of slice, but this one works and I'm
;;    too lazy to re-do everything. 

(defun slice (low high lst)
  (declare (xargs :measure (nfix (1+ (- high low)))))
  (if (or (not (natp low))
	  (not (natp high))
	  (< high low)
	  (<= (len lst) low))
      nil
    (cons (nth low lst)
	  (slice (1+ low) high lst))))

(defthm len-slice
  (implies (and (natp low)
		(natp high)
		(< low (len lst))
		)
	   (equal (len (slice low high lst))
		  (if (< high low)
		      0
		    (if (<= (len lst) high)
			(- (len lst) low)
		      (1+ (- high low))))))
  :hints (("Goal" :induct (slice low high lst))))

;; Thanks to David Russinoff for showing me how to complete this
;; proof.

(defthmd cdr-nil-kludge
  (implies (and (true-listp l)
		(equal 0 (len (cdr l))))
	   (equal (cdr l) nil)))

(defthmd cdr-nil-kludge2
  (implies (and (consp l)
		(true-listp (cdr l))
		(equal 0 (len (cdr l))))
	   (equal (equal l (list (car l)))
		  t))
  :hints (("Goal" :in-theory (enable cdr-nil-kludge))))

(defthmd low-len-nthcdr
  (implies (and (true-listp l)
		(natp n)
		(equal (1+ n) (len l)))
	   (equal (nthcdr n l)
		  (list (nth n l))))
  :hints (("Goal" :in-theory (enable cdr-nil-kludge2))))

(defthmd car-cons-nthcdr
  (implies (and (< n (len l))
		(natp n))
	   (equal (cons (nth n l)
			(nthcdr (+ 1 n) l))
		  (nthcdr n l))))

(defthmd slice-nthcdr-lemma
 (implies (and (natp low)
	       (true-listp lst)
	       ;; do I need this hyp
	       (< low (len lst)))
	  (equal (slice low (1- (len lst)) lst)
		 (nthcdr low lst)))
 :hints (("Goal" :instructions ((:in-theory (enable low-len-nthcdr car-cons-nthcdr))
				:induct (:casesplit (equal (1+ low) (len lst)))
				:bash :promote (:demote 2) (:dive 1 1)
				(:= t) :up (:s :in-theory (theory 'minimal-theory))
				:top :promote (:dv 1) :x :top :s :bash))))

(defthm slice-whole-list
 (implies (and (natp low)
	       (true-listp lst))
	  (equal (slice 0 (1- (len lst)) lst)
		 lst))
 :INSTRUCTIONS (:PROMOTE (:CASESPLIT (NOT LST))
                                :BASH
                                (:USE (:INSTANCE SLICE-NTHCDR-LEMMA (LOW 0)))
                                :BASH))

(defthm slice-nil
  (implies (< high low)
	   (equal (slice low high lst)
		  nil)))

(defthm slice-singleton
  (implies (and (natp x)
		(< x (len lst)))
	   (equal (slice x x lst)
		  (list (nth x lst)))))

(defthm not-in-sorted-list
  (implies (and (natp low)
		(natp high)
		(< high (len lst))
		(sorted lst)
		(<= low high)
		(< (nth high lst) key))
	   (not (member-equal key (slice low high lst)))))

(defthm slice-bounds
  (implies (and (true-listp lst)
		(member-equal x (slice low high lst)))
	   (< low (len lst))))
 
(defthm slice-len-low
  (implies (<= (len lst) low)
	   (equal (slice low high lst)
		  nil)))

(defthm car-slice
  (implies (consp (slice low high lst))
	   (equal (car (slice low high lst))
		  (nth low lst))))

(defthmd slice-append1
  (implies (and (natp low)
		(natp high)
		(natp mid)
		(<= low mid)
		(<= mid high))
	   (equal (slice low high lst)
		  (append (slice low mid lst)
			  (slice (1+ mid) high lst)))))

(defthmd slice-append2
  (implies (and (natp low)
		(natp high)
		(natp mid)
		(<= low mid)
		(<= mid high))
	   (equal (slice low high lst)
		  (append (slice low (1- mid) lst)
			  (slice mid high lst)))))

;; >> I should see how many of these kludge lemmas I can eliminate, or move up.

(defthm flr-natp
  (implies (and (natp low)
		(natp high))
	   (and (<= 0 (flr (+ low high) 2))
		(integerp (flr (+ low high) 2))))
  :hints (("Goal" :in-theory (enable flr))))

(defthm high-low-kludge1
  (implies (and (natp high)
		(natp low)
		(equal low high))
	   (< high (1+ (flr (+ low high) 2))))
  :hints (("Goal" :in-theory (enable flr))))

;; >> Disable this one after I see where it's used.

(defthm high-low-kludge2
  (implies (and (natp high)
		(natp low)
		(< high (flr (+ low high) 2)))
	   (< high low))
  :hints (("Goal" :in-theory (enable flr))))

(defthm high-low-kludge3
  (implies (and (integerp high)
		(integerp low)
		(equal high low))
	   (equal (flr (+ low high) 2)
		  high))
  :hints (("Goal" :in-theory (enable flr))))

(defthm high-low-kludge3-corollary
  (implies (integerp x)
	   (equal (flr (* 2 x) 2)
		  x))
  :hints (("Goal" :in-theory (enable flr))))

(defthm high-low-kludge4
  (implies (and (natp high)
		(natp low)
		(<= low high))
	   (< low (1+ (flr (+ low high) 2))))
  :hints (("Goal" :in-theory (enable flr))))

(defthm high-low-kludge4-corollary
  (implies (and (natp high)
		(natp low)
		(<= low high))
	   (not (< (1+ (flr (+ low high) 2)) low)))
  :hints (("Goal" :use high-low-kludge4)))

(defthm high-low-kludge5
  (implies (and (natp high)
		(natp low)
		(< low high))
	   (< (flr (+ low high) 2) high))
  :hints (("Goal" :in-theory (enable flr))))

(defthm natp-less-kludge
  (implies (and (natp x)
		(natp y)
		(< x y))
	   (<= (1+ x) y)))

(defthm high-low-kludge6
  (implies (and (natp high)
		(natp low)
		(< low high))
	   (<= (1+ (flr (+ low high) 2)) high))
  :hints (("Goal" :use (:instance high-low-kludge5))))

(defthm flr-low-high-equal
  (implies (and (equal lowval highval)
		(natp lowval))
	   (equal (flr (+ lowval highval) 2)
		  lowval))
  :hints (("Goal" :in-theory (enable flr))))

(defthm flr-natp-corollary
  (implies (and (natp low)
		(natp high))
	   (and (<= 0 (1+ (flr (+ low high) 2)))
		(integerp (1+ (flr (+ low high) 2)))))
  :hints (("Goal" :use (:instance flr-natp)
	          :in-theory (disable flr-natp))))

(defthm flr-bounds
  (implies (and (natp low)
		(natp high)
		(<= low high))
	   (and (<= low (flr (+ low high) 2))
		(<= (flr (+ low high) 2) high)))
  :hints (("Goal" :in-theory (e/d (flr) (high-low-kludge2)))))

(defthm flr-x-x-plus-1
  (implies (natp x)
	   (equal (flr (1+ (* 2 x)) 2)
		  x))
  :hints (("Goal" :in-theory (enable flr))))

(defthm low-high-flr-kludge
  (implies (and (natp low)
		(natp high)
		(< (1+ low) high))
	   (< low (flr (+ low high) 2)))
  :hints (("Goal" :in-theory (e/d (flr) (high-low-kludge2)))))

(defthm slice-sorted
  (implies (sorted lst)
	   (sorted (slice low high lst)))
  :hints (("Goal" :INSTRUCTIONS (:INDUCT :PROMOTE (:DV 1) :X :UP
					 (:CASESPLIT (CONSP (SLICE (1+ LOW) HIGH LST)))
					 (:REWRITE SORTED-CONS) :S-PROP (:DV 2) (:= T)
					 :UP (:DV 1) (:DV 1) (:REWRITE CAR-SLICE)
					 :TOP (:DV 1) (:REWRITE SORTED-LESSP) :BASH :BASH :BASH :BASH))))

(defthm sorted-lessp4
  (implies (and (sorted lst)
		(< key (car lst)))
	   (not (member-equal key lst))))

(defthm not-in-sorted-list2
  (implies (and (natp low)
		(natp high)
		(< high (len lst))
		(sorted lst)
		(<= low high)
		(< key (nth low lst)))
	   (not (member-equal key (slice low high lst))))
  :hints (("Goal" :INSTRUCTIONS (:PROMOTE (:CASESPLIT (NOT (CONSP (SLICE LOW HIGH LST))))
					  :BASH (:DV 1) (:REWRITE SORTED-LESSP4) :BASH))))

(defthm sorted-in-upper
  (implies (and (member-equal key (slice low high lst))
		(natp low)
		(natp high)
		(< high (len lst))
		(natp mid)
		(<= low mid)
		(<= mid high)
		(sorted lst)
		(< (nth mid lst) key))
	   (member-equal key (slice (1+ mid) high lst)))
  :hints (("goal" :instructions (:promote (:casesplit (equal mid high))
					  :bash (:demote 1) (:dive 1 2)
					  (:rewrite slice-append2 ((mid (1+ mid))))
					  :top :bash :bash :bash))))

(defthm sorted-in-lower
  (implies (and (member-equal key (slice low high lst))
		(natp low)
		(natp high)
		(< high (len lst))
		(natp mid)
		(<= low mid)
		(<= mid high)
		(sorted lst)
		(< key (nth mid lst)))
	   (member-equal key (slice low (1- mid) lst)))
  :hints (("Goal" :use (:instance slice-append2))))

(defthm not-member-equal-slice
  (implies (and (not (member-equal x (slice low high lst)))
		(natp low)
		;; Could I replace this with integerp
		(natp mid)
		(natp high)
		(<= low mid))
	   (not (member-equal x (slice mid high lst)))))

(defthm not-member-equal-slice2
  (implies (and (not (member-equal x (slice low high lst)))
		(natp low)
		(integerp mid)
		(natp high)
		(<= mid high))
	   (not (member-equal x (slice low mid lst)))))

;; Since the current version of slice is recursive, I don't think
;; there's a need to disable it.
; (in-theory (disable slice))

;; >> I needed to change the order of the tests here.  Otherwise, the step counts
;;    are different depending on whether I go left or right. 

(defun binarysearch-if-else (key lst)
  ;; This takes 8 steps if key == lst[mid] and 16 otherwise
  `(if-else (== ,key (ind (var mid) ,lst))
	    (return (var mid))
	    (if-else (< ,key (ind (var mid) ,lst))
		   (assign (var high) (- (var mid) (lit . 1)))
		   (assign (var low) (+ (var mid) (lit . 1))))))

(defun binarysearch-while-body (key lst)
  ;; Take 14 steps if it hits the key, 22 otherwise, which is 6 for the assignment.
  `(seq (assign (var mid) (// (+ (var low) (var high)) (lit . 2)))
	,(binarysearch-if-else key lst)))

(defun binarysearch-while (key lst) 
  ;; If the test succeeds this takes 18 steps, else 26 +
 `(while (<= (var low) (var high))
     ,(binarysearch-while-body key lst)))

(in-theory (disable binarysearch-if-else binarysearch-while-body binarysearch-while))

(defun binarysearch (key lst)
  ;; The 2 lead assignments take 7 steps.  The return takes 2.
  `(seq (assign (var low) (lit . 0))
	(seq (assign (var high) (- (len ,lst) (lit . 1)))
	     (seq ,(binarysearch-while key lst)
		  (return (lit . -1))))))

(defun binarysearch-with-seqn (key lst)
  `(seqn (assign (var low) (lit . 0))
         (assign (var high) (- (len ,lst) (lit . 1)))
	 (while (<= (var low) (var high))
	   (seq (assign (var mid) (// (+ (var low) (var high)) (lit . 2)))
		(if-else (== ,key (ind (var mid) ,lst))
			 (return (var mid))
			 (if-else (< ,key (ind (var mid) ,lst))
				  (assign (var high) (- (var mid) (lit . 1)))
				  (assign (var low) (+ (var mid) (lit . 1)))))))
	 (return (lit . -1))))

; (thm (equal (binarysearch 'key 'lst) (expand-seqn (binarysearch-with-seqn 'key 'lst))))

(defthm binarysearch-while-body-lemma
  (let ((keyval (lookup (param1 key) vars))
	(lstval (lookup (param1 lst) vars))
	(lowval (lookup 'low vars))
	(highval (lookup 'high vars)))
    (implies (and (varp key)
		  (not (equal (param1 key) 'mid))
		  (acl2-numberp keyval)
		  (varp lst)
		  (number-listp lstval)
		  (not (equal (param1 lst) 'mid))
		  (natp lowval)
		  ;; >> is there any way to weaken or remove this hyp?
		  (< highval (len lstval))
		  (integerp highval)
		  (<= lowval highval)
		  (natp steps)
		  (not (zp count))
		  )
	     (equal (run (binarysearch-while-body key lst) 'ok vars steps count)
		    (let ((midval (flr (+ lowval highval) 2)))
					; Is key == lst[mid]
		      (if (equal keyval (nth midval lstval))
			  (list 'returned
				(store 'result midval
				       (store 'mid midval vars))
				(+ 14 steps))
					; Is key < lst[mid]
			(if (< keyval (nth midval lstval)) 
			    (list 'ok
				  (store 'high
					 (+ -1 midval)
					 (store 'mid midval vars))
				  (+ 22 steps))
					; key > lst[mid]
			  (list 'ok
				(store 'low
				       (+ 1 midval)
				       (store 'mid midval vars))
				(+ 22 steps))))))))
  :hints (("Goal" :in-theory (enable binarysearch-if-else binarysearch-while-body)
	   :do-not-induct t)))

(defthm binarysearch-while-test-fails
  (let ((lowval (lookup 'low vars))
	(highval (lookup 'high vars)))
    (implies (and (natp lowval)
		  (integerp highval)
		  ;; The while test succeeds
		  (< highval lowval)
		  (natp steps)
		  (not (zp count)))
	     (equal (run (binarysearch-while key lst) 'ok vars steps count)
		    (mv 'ok vars (+ 4 steps)))))
  :hints (("Goal" :in-theory (enable binarysearch-while))))

(defthm binarysearch-while-test-succeeds
  (let ((keyval (lookup (param1 key) vars))
	(lstval (lookup (param1 lst) vars))
	(lowval (lookup 'low vars))
	(highval (lookup 'high vars)))
    (implies (and (varp key)
		  (not (equal (param1 key) 'mid))
		  (acl2-numberp keyval)
		  (varp lst)
		  (number-listp lstval)
		  (not (equal (param1 lst) 'mid))
		  (natp lowval)
		  (integerp highval)
		  (<= lowval highval)
		  (natp steps)
		  (not (zp count)))
	     (equal (run (binarysearch-while key lst) 'ok vars steps count)
		    ;; >> Expand this using the three cases:
		    ;;    key < lst[mid]
		    ;;    key == lst[mid]
		    ;;    key > lst[mid]
		    (run (binarysearch-while key lst)
			 (mv-nth 0
				 (run (binarysearch-while-body key lst)
				      'ok
				      vars (+ 4 steps)
				      count))
			 (mv-nth 1
				 (run (binarysearch-while-body key lst)
				      'ok
				      vars (+ 4 steps)
				      count))
			 (mv-nth 2
				 (run (binarysearch-while-body key lst)
				      'ok
				      vars (+ 4 steps)
				      count))
			 (+ -1 count)))))
  :hints (("Goal" :in-theory (enable binarysearch-while))))

(defthm binarysearch-while-test-succeeds2
  (let ((keyval (lookup (param1 key) vars))
	(lstval (lookup (param1 lst) vars))
	(lowval (lookup 'low vars))
	(highval (lookup 'high vars)))
    (implies (and (varp key)
		  (not (equal (param1 key) 'mid))
		  (acl2-numberp keyval)
		  (varp lst)
		  (number-listp lstval)
		  (not (equal (param1 lst) 'mid))
		  (natp lowval)
		  ;; highval could be -1, if the lst is empty
		  (integerp highval)
		  ;; >> Can I get rid of this hyp
		  (< highval (len lstval))
		  (<= lowval highval)
		  (natp steps)
		  (not (zp count))
		  )
	     (equal (run (binarysearch-while key lst) 'ok vars steps count)
		    (let ((midval (flr (+ lowval highval) 2)))
					; Is key == lst[mid]
		      (if (equal keyval (nth midval lstval))
			  (mv 'returned 
			       (store 'result midval
				      (store 'mid midval vars))
			       (+ 18 steps))
					; Is key < lst[mid]
			(if (< keyval (nth midval lstval)) 
			    (run (binarysearch-while key lst)
				 'ok
				 (store 'high
					(+ -1 midval)
					(store 'mid midval vars))
				 (+ 26 steps)
				 (1- count))
					; key > lst[mid]
			  (run (binarysearch-while key lst)
			       'ok
			       (store 'low
				      (+ 1 midval)
				      (store 'mid midval vars))
			       (+ 26 steps)
			       (1- count))))))))
    :hints (("Goal" :in-theory (enable binarysearch-if-else
				       ;binarysearch-while-test-succeeds
				       binarysearch-while-body)
	            :use (:INSTANCE BINARYSEARCH-WHILE-BODY-LEMMA)
	            :do-not-induct t)))

(defthm binarysearch-while-test-succeeds2-corollary1
  ;; Here key < lst[mid]
  (let ((keyval (lookup (param1 key) vars))
	(lstval (lookup (param1 lst) vars))
	(lowval (lookup 'low vars))
	(highval (lookup 'high vars)))
    (let ((midval (flr (+ lowval highval) 2)))
      (implies (and (varp key)
		  (not (equal (param1 key) 'mid))
		  (acl2-numberp keyval)
		  (varp lst)
		  (number-listp lstval)
		  (not (equal (param1 lst) 'mid))
		  (natp lowval)
		  ;(<= lowval (len lstval))
		  ;; highval could be -1, if the lst is empty
		  (integerp highval)
		  (< highval (len lstval))
		  (<= lowval highval)
		  (natp steps)
		  (not (zp count))
		  (< keyval (nth midval lstval))
		  )
	     (equal (run (binarysearch-while key lst) 'ok vars steps count)
		    (run (binarysearch-while key lst)
			 'ok
			 (store 'high
				(+ -1 midval)
				(store 'mid midval vars))
			 (+ 26 steps)
			 (1- count)))))))

(defthm binarysearch-while-test-succeeds2-corollary2
  ;; This is the case where we find key at lst[mid]
  (let ((keyval (lookup (param1 key) vars))
	(lstval (lookup (param1 lst) vars))
	(lowval (lookup 'low vars))
	(highval (lookup 'high vars)))
    (let ((midval (flr (+ lowval highval) 2)))
      (implies (and (varp key)
		    (not (equal (param1 key) 'mid))
		    (acl2-numberp keyval)
		    (varp lst)
		    (number-listp lstval)
		    (not (equal (param1 lst) 'mid))
		    (natp lowval)
		    ;(<= lowval (len lstval))
		    ;; highval could be -1, if the lst is empty
		    (integerp highval)
		    (< highval (len lstval))
		    (<= lowval highval)
		    (natp steps)
		    (not (zp count))
		    (equal keyval (nth midval lstval))
		    )
	       (equal (run (binarysearch-while key lst) 'ok vars steps count)
		      (mv 'returned
			   (store 'result midval
				  (store 'mid midval vars))
			   (+ 18 steps)))))))

(defthm binarysearch-while-test-succeeds2-corollary3
  ;; Here key > lst[mid]
  (let ((keyval (lookup (param1 key) vars))
	(lstval (lookup (param1 lst) vars))
	(lowval (lookup 'low vars))
	(highval (lookup 'high vars)))
    (let ((midval (flr (+ lowval highval) 2)))
      (implies (and (varp key)
		    (not (equal (param1 key) 'mid))
		    (acl2-numberp keyval)
		    (varp lst)
		    (number-listp lstval)
		    (not (equal (param1 lst) 'mid))
		    (natp lowval)
		    ;(<= lowval (len lstval))
		    ;; highval could be -1, if the lst is empty
		    (integerp highval)
		    (< highval (len lstval))
		    (<= lowval highval)
		    (natp steps)
		    (not (zp count))
		    (> keyval (nth midval lstval)))
	       (equal (run (binarysearch-while key lst) 'ok vars steps count)
		      (run (binarysearch-while key lst)
			   'ok
			   (store 'low
				  (+ 1 midval)
				  (store 'mid midval vars))
			   (+ 26 steps)
			   (1- count)))))))

(defthmd lessp-transitive-kludge2
  (implies (and (<= lowval highval)
		(< highval keyval))
	   (< lowval keyval)))

(defthm sorted-lower-index-lower-value-lemma2
  (implies (and (sorted lst)
		(number-listp lst)
		(<= mid high)
		(natp mid)
		(natp high)
		(< high (len lst))
		(acl2-numberp key)
		(< (nth high lst) key))
	   (< (nth mid lst) key))
  :hints (("Goal" :use (:instance lessp-transitive-kludge2 (lowval (nth mid lst))
				  (highval (nth high lst)) (keyval key)))))

(defthm binarysearch-while-test-succeeds2-corollary4
  (let ((keyval (lookup (param1 key) vars))
	(lstval (lookup (param1 lst) vars))
	(lowval (lookup 'low vars))
	(highval (lookup 'high vars)))
    (implies (and (varp key)
		  (not (equal (param1 key) 'mid))
		  (acl2-numberp keyval)
		  (varp lst)
		  (number-listp lstval)
		  (sorted lstval)
		  (not (equal (param1 lst) 'mid))
		  (natp lowval)
		  (integerp highval)
		  (< highval (len lstval))
		  (<= lowval highval)
		  (natp steps)
		  (not (zp count))
		  (< (nth highval lstval) keyval)
		  )
	     (equal (run (binarysearch-while key lst) 'ok vars steps count)
		    (let ((midval (flr (+ lowval highval) 2)))
		      (run (binarysearch-while key lst)
			   'ok
			   (store 'low
				  (+ 1 midval)
				  (store 'mid midval vars))
			   (+ 26 steps)
			   (1- count))))))
  :hints (("Goal" :INSTRUCTIONS (:EXPAND :PROMOTE (:DV 1)
					 (:REWRITE BINARYSEARCH-WHILE-TEST-SUCCEEDS2-COROLLARY3)
					 :TOP :S
					 :BASH (:REWRITE SORTED-LOWER-INDEX-LOWER-VALUE-LEMMA2
							 ((HIGH (LOOKUP 'HIGH VARS))))
					 :BASH :BASH))))

(defthm binarysearch-while-low-high-equal
  ;; Here low and high are equal.  I needed this case for a lemma below.
  (let ((lowval (lookup 'low vars))
	(highval (lookup 'high vars))
	(keyval (lookup (cadr key) vars))
	(lstval (lookup (cadr lst) vars)))
    (implies (and (varp key)
		  (not (equal (cadr key) 'mid))
		  (acl2-numberp keyval)
		  (varp lst)
		  (number-listp lstval)
		  (not (equal (cadr lst) 'mid))
		  (natp lowval)
		  (< highval (len lstval))
		  (integerp highval)
		  (natp steps)
		  (natp count)
		  (< 1 count)
		  (equal lowval highval)
		  )
	     (equal (run (binarysearch-while key lst) 'ok vars steps count)
		    (if (equal keyval (nth lowval lstval))
			(list 'returned
			      (store 'result
				     (lookup 'low vars)
				     (store 'mid (lookup 'low vars) vars))
			      (+ 18 steps))
		      (if (< keyval (nth lowval lstval))
			  (list 'ok
				(store 'high
				       (1- (lookup 'low vars))
				       (store 'mid (lookup 'low vars) vars))
				(+ 30 steps))
			(list 'ok
			      (store 'low
				     (+ 1 (lookup 'low vars))
				     (store 'mid (lookup 'low vars) vars))
			      (+ 30 steps))))))))

(defthm low-high-differ-by-1-flr
  (implies (and (equal (1+ low) high)
		(natp low))
	   (equal (flr (+ low high) 2)
		  low))
  :hints (("Goal" :in-theory (enable flr))))

(defthmd lessp-transitive-kludge
  (implies (and (<= lowval highval)
		(<= highval keyval))
	   (<= lowval keyval)))

(defthm sorted-lower-index-lower-value
  (implies (and (sorted lst)
		(number-listp lst)
		(< low high)
		(natp low)
		(< low (len lst))
		(natp high)
		(< high (len lst))
		(acl2-numberp key)
		(<= (nth high lst) key))
	   (<= (nth low lst) key))
  :hints (("Goal" :use (:instance lessp-transitive-kludge (lowval (nth low lst))
				  (highval (nth high lst)) (keyval key)))))

(defthm sorted-lower-index-lower-value-corollary
  (implies (and (sorted (lookup lst vars))
		(number-listp (lookup lst vars))
		(< (lookup 'low vars) (lookup 'high vars))
		(natp (lookup 'low vars))
		(< (lookup 'low vars) (len (lookup lst vars)))
		(natp (lookup 'high vars))
		(< (lookup 'high vars) (len (lookup lst vars)))
		(acl2-numberp key)
		(<= (nth (lookup 'high vars) (lookup lst vars)) key))
	   (<= (nth (lookup 'low vars) (lookup lst vars)) key)))


(defthm binarysearch-while-low-high-differ-by-one-subcase1
  ;; Here low +1 = high, and keyval < lst[lowval]
  (let ((lowval (lookup 'low vars))
	(highval (lookup 'high vars))
	(keyval (lookup (cadr key) vars))
	(lstval (lookup (cadr lst) vars)))
    (implies (and (varp key)
		  (not (equal (cadr key) 'mid))
		  (not (equal (cadr key) 'low))
		  (not (equal (cadr key) 'high))
		  (acl2-numberp keyval)
		  (varp lst)
		  (number-listp lstval)
		  (not (equal (cadr lst) 'mid))
		  (natp lowval)
		  (< highval (len lstval))
		  (integerp highval)
		  (natp steps)
		  (natp count)
		  ;; count must be at least 2
		  (< 1 count)
		  (equal (1+ lowval) highval)
		  (not (member-equal keyval (slice lowval highval lstval)))
		  (< keyval (nth lowval lstval))
		  )
	     (equal (run (binarysearch-while key lst) 'ok vars steps count)
		    (list 'ok
			  (store 'high
				 (+ -1 (lookup 'low vars))
				 (store 'mid (lookup 'low vars) vars))
			  (+ 30 steps))))))

(defthm binarysearch-while-low-high-differ-by-one-subcase2
  ;; Here low +1 = high, and keyval > lst[highval]
  (let ((lowval (lookup 'low vars))
	(highval (lookup 'high vars))
	(keyval (lookup (cadr key) vars))
	(lstval (lookup (cadr lst) vars)))
    (implies (and (varp key)
		  (not (equal (cadr key) 'mid))
		  (not (equal (cadr key) 'low))
		  (not (equal (cadr key) 'high))
		  (acl2-numberp keyval)
		  (varp lst)
		  (number-listp lstval)
		  (sorted lstval)
		  (not (equal (cadr lst) 'mid))
		  (natp lowval)
		  (< highval (len lstval))
		  (integerp highval)
		  (natp steps)
		  (natp count)
		  ;; count must be at least 3
		  (< 2 count)
		  (equal (1+ lowval) highval)
		  (not (member-equal keyval (slice lowval highval lstval)))
		  (> keyval (nth highval lstval))
		  )
	     (equal (run (binarysearch-while key lst) 'ok vars steps count)
		    (list 'ok
			  (store 'low
				 (+ 1 (lookup 'high vars))
				 (store 'mid (lookup 'high vars) vars))
			  (+ 56 steps)))))
  :hints (("Goal" :INSTRUCTIONS (:EXPAND :PROMOTE :BASH (:DV 1)
					 (:REWRITE BINARYSEARCH-WHILE-TEST-SUCCEEDS2-COROLLARY4)
					 :TOP :BASH :BASH :BASH :BASH :BASH :BASH :BASH :BASH
					 :BASH :BASH :BASH :BASH))))

(defmacro rbsh-success (fivetuple)
  `(mv-nth 0 ,fivetuple))

(defmacro rbsh-low (fivetuple)
  `(mv-nth 1 ,fivetuple))

(defmacro rbsh-mid (fivetuple)
  `(mv-nth 2 ,fivetuple))

(defmacro rbsh-high (fivetuple)
  `(mv-nth 3 ,fivetuple))

(defmacro rbsh-calls (fivetuple)
  `(mv-nth 4 ,fivetuple))

;; >>> This is a pretty peculiar function because I needed
;;     it not to adjust mid in the case where (equal low high). 

(in-theory (disable high-low-kludge2))

(defun recursiveBS-helper (key lst low mid high calls)
  ;; This performs a recursive binary search for key in 
  ;; lst[low..high].  It returns a 5-tuple (success low mid high calls).
  ;; I need all of those values to do the recursive proof.
  (declare (xargs :measure (nfix (1+ (- high low)))
		  :hints (("Goal" :in-theory (e/d (flr) (HIGH-LOW-KLUDGE2))))))
  (if (or (< high low)
	  (not (natp low))
	  ;(not (natp high))
	  (not (integerp high))
	  )
      ;; This means that the item wasn't found
      (mv nil low mid high calls)
    (let ((newmid (flr (+ low high) 2)))
      (if (equal key (nth newmid lst))
	  (mv t low newmid high calls)
	(if (< key (nth newmid lst))
	    (recursiveBS-helper key lst low newmid (1- newmid) (1+ calls))
	  (recursiveBS-helper key lst (1+ newmid) newmid high (1+ calls)))))))

;; This is the recursive version of binary search

(defun recursiveBS (key lst)
  (mv-let (success low mid high calls)
	  (recursiveBS-helper key lst 0 nil (1- (len lst)) 0)
	  (declare (ignore low high calls))
	  (if success mid -1)))

;; >> replace this one with the stronger lemma below:
(defthm recursiveBS-helper-mid
  ;; If the item is there, then mid doesn't matter. 
  (implies (and (syntaxp (not (equal mid ''nil)))
		(member-equal key (slice low high lst)))
		;mid)
	   (equal (recursiveBS-helper key lst low mid high calls)
		  (recursiveBS-helper key lst low nil high calls)))
  :hints (("Goal" :induct (recursiveBS-helper key lst low mid high calls))))

(defthmd recursiveBS-helper-mid2
  (implies (and (syntaxp (not (equal mid ''nil)))
		(<= low high)
		(natp low)
		(natp high)
		(not (equal key (nth mid lst))))
	   (equal (recursiveBS-helper key lst low mid high calls)
		  (recursiveBS-helper key lst low nil high calls)))
  :hints (("Goal" :induct (recursiveBS-helper key lst low mid high calls))))

(defthmd recursiveBS-helper-mid2-version2
  (implies (and (syntaxp (not (equal mid ''nil)))
		(<= low high)
		(natp low)
		(integerp high)
		(not (equal key (nth mid lst))))
	   (equal (recursiveBS-helper key lst low mid high calls)
		  (recursiveBS-helper key lst low nil high calls)))
  :hints (("Goal" :induct (recursiveBS-helper key lst low mid high calls))))


(defthmd recursiveBS-helper-calls0
  (equal (mv-nth 0 (recursiveBS-helper key lst low mid high calls1))
	 (mv-nth 0 (recursiveBS-helper key lst low mid high calls2))))

(defthmd recursiveBS-helper-calls1
  (equal (mv-nth 1 (recursiveBS-helper key lst low mid high calls1))
	 (mv-nth 1 (recursiveBS-helper key lst low mid high calls2))))

(defthmd recursiveBS-helper-calls2
  (equal (mv-nth 2 (recursiveBS-helper key lst low mid high calls1))
	 (mv-nth 2 (recursiveBS-helper key lst low mid high calls2)))
  :hints (("Goal" :in-theory (disable flr-half-lemma ;high-low-kludge2
                                       simplify-products-gather-exponents-<))))

(defthmd recursiveBS-helper-calls3
  (equal (mv-nth 3 (recursiveBS-helper key lst low mid high calls1))
	 (mv-nth 3 (recursiveBS-helper key lst low mid high calls2)))
  :hints (("Goal" :in-theory (disable FLR-HALF-LEMMA ;HIGH-LOW-KLUDGE2
                                       SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))))

(defthmd recursiveBS-helper-calls
  (implies (syntaxp (not (equal calls ''0)))
	   (and (equal (mv-nth 0 (recursiveBS-helper key lst low mid high calls))
		       (mv-nth 0 (recursiveBS-helper key lst low mid high 0)))
		(equal (mv-nth 1 (recursiveBS-helper key lst low mid high calls))
		       (mv-nth 1 (recursiveBS-helper key lst low mid high 0)))
		(equal (mv-nth 2 (recursiveBS-helper key lst low mid high calls))
		       (mv-nth 2 (recursiveBS-helper key lst low mid high 0)))
		(equal (mv-nth 3 (recursiveBS-helper key lst low mid high calls))
		       (mv-nth 3 (recursiveBS-helper key lst low mid high 0)))))
  :hints (("Goal" :use ((:instance recursiveBS-helper-calls0 (calls1 calls) (calls2 0))
			(:instance recursiveBS-helper-calls1 (calls1 calls) (calls2 0))
			(:instance recursiveBS-helper-calls2 (calls1 calls) (calls2 0))
			(:instance recursiveBS-helper-calls3 (calls1 calls) (calls2 0))))))

(defthmd recursiveBS-helper-calls4
  (equal (mv-nth 4 (recursiveBS-helper key lst low mid high (+ calls1 calls2)))
	 (+ calls1 (mv-nth 4 (recursiveBS-helper key lst low mid high calls2))))
  :hints (("Goal" :in-theory (disable FLR-HALF-LEMMA 
                                       SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))))

(defthmd recursiveBS-helper-calls4-corollary
  (implies (not (zp calls))
	   (equal (mv-nth 4 (recursiveBS-helper key lst low mid high calls))
		  (+ calls (mv-nth 4 (recursiveBS-helper key lst low mid high 0)))))
  :hints (("Goal" :use (:instance recursiveBS-helper-calls4 (calls1 calls) (calls2 0))
	          :do-not-induct t)))

(defthmd recursiveBS-helper-calls4-corollary2
  (implies (natp calls)
	   (natp (mv-nth 4 (recursiveBS-helper key lst low mid high calls))))
  :rule-classes (:rewrite :type-prescription))

(defthm recursiveBS-helper-low-high-equal
  (implies (and (natp x)
		(number-listp lst)
		(acl2-numberp key)
		(acl2-numberp calls)
		)
	   (equal (recursivebs-helper key lst x mid x calls)
		  (if (equal key (nth x lst))
		      (mv t x x x calls)
		    (if (< key (nth x lst))
			 (list nil x x (1- x) (1+ calls))
		      (mv nil (1+ x) x x (1+ calls)))))))

(defthm recursiveBS-helper-low-high-differ-by-one
  (implies (and (natp x)
		(< (1+ x) (len lst))
		(number-listp lst)
		(sorted lst)
		(acl2-numberp key)
		(acl2-numberp calls)
		)
	   (equal (recursivebs-helper key lst x mid (1+ x) calls)
		  (if (equal key (nth x lst))
		      (list t x x (+ 1 x) calls)
		    (if (< key (nth x lst))
			(list nil x x (+ -1 x) (+ 1 calls))
		      (if (< (nth (1+ x) lst) key)
			  (list nil (+ 2 x) (1+ x) (1+ x) (+ 2 calls))
			(if (equal key (nth (1+ x) lst))
			    (list t (+ 1 x) (+ 1 x) (+ 1 x) (+ 1 calls))
			  (list nil (+ 1 x) (+ 1 x) x (+ 2 calls))))))))
  :hints (("Goal" :expand (recursivebs-helper key lst x mid (1+ x) calls)
	   :do-not-induct t)))

(defthm rbsh-calls-acl2-numberp
  (implies (acl2-numberp calls)
	   (acl2-numberp (rbsh-calls (recursiveBS-helper key lst low mid high calls)))))

(defthm not-member-equal-slice-corollary
  (implies (and (not (member-equal key (slice lowval highval lst)))
		(natp lowval)
		(natp highval)
		(<= lowval highval))
	   (not (member-equal key
			      (slice (+ 1 (flr (+ lowval highval) 2))
				     highval lst))))
  :hints (("Goal" :in-theory (disable high-low-kludge4-corollary)
	          :use (:instance high-low-kludge4-corollary (low lowval) (high highval)))))

;; The case where (< highval low) is covered by the lemma:
;;  binarysearch-while-test-fails

(defun bs-ind1 ( lst key vars steps count calls)
;   (declare (xargs :measure (acl2-count count)))
  (declare (xargs :measure (nfix (1+ (- (lookup 'high vars) (lookup 'low vars))))))
		  ;:hints (("Goal" :in-theory (enable flr)))))
  (if (or (< (lookup 'high vars) (lookup 'low vars))
	  (not (natp (lookup 'low vars)))
	  (not (natp (lookup 'high vars))))
      t
    (let ((mid (flr (+ (lookup 'low vars) (lookup 'high vars)) 2)))
      (if (equal key (nth mid lst))
	  t
	(if (< key (nth mid lst))
	    (bs-ind1 lst key
		     (store 'high (1- mid)
			    (store 'mid mid vars))
		     (+ 26 steps)
		     (1- count)
		     (1+ calls))
	  (bs-ind1 lst key
		   (store 'low (1+ mid)
			  (store 'mid mid vars))
		   (+ 26 steps)
		   (1- count)
		   (1+ calls)))))))

(defthm binarysearch-while-test-inductive-case1
  ;; This is the case where the key is in the list. 
  (let ((keyval (lookup (param1 key) vars))
	(lstval (lookup (param1 lst) vars))
	(lowval (lookup 'low vars))
	(highval (lookup 'high vars)))
    (implies (and (varp key)
		  (not (equal (param1 key) 'mid))
		  (not (equal (param1 key) 'low))
		  (not (equal (param1 key) 'high))
		  (acl2-numberp keyval)
		  (varp lst)
		  (number-listp lstval)
		  (sorted lstval)
		  (not (equal (param1 lst) 'mid))
		  (not (equal (param1 lst) 'high))
		  (not (equal (param1 lst) 'low))
		  (natp lowval)
		  (< highval (len lstval))
		  (integerp highval)
		  (member-equal keyval (slice lowval highval lstval))
		  (natp steps)
		  (not (timedoutp (run-status (run (binarysearch-while key lst) 'ok vars steps count))))
		  (equal lst1 lstval)
		  (equal key1 keyval)
		  )
	     (equal (run (binarysearch-while key lst) 'ok vars steps count)
		    (mv-let (success endlow endmid endhigh endcalls)
			    (recursiveBS-helper keyval lstval lowval nil highval 0)
			    (declare (ignore success))
			    (mv 'returned
				(store 'result endmid
				       (store 'high endhigh
					      (store 'low endlow
						     (store 'mid endmid vars))))
				(+ 18 (* 26 endcalls) steps))))))
  :hints (("Goal" :INSTRUCTIONS (:EXPAND :PROMOTE (:CLAIM (NOT (ZP COUNT)))
					 (:IN-THEORY (ENABLE RECURSIVEBS-HELPER-CALLS RE-ORDER-STORE
							     RECURSIVEBS-HELPER-CALLS4-COROLLARY))
					 (:INDUCT (BS-IND1 LST1 KEY1 VARS STEPS COUNT CALLS))
					 :BASH :BASH :BASH :BASH))))

(defthmd binarysearch-while-test-inductive-case2-subcase1
  ;; This is the case where low equals high;  I needed that for a lemma below.
  (let ((keyval (lookup (param1 key) vars))
	(lstval (lookup (param1 lst) vars))
	(lowval (lookup 'low vars))
	(highval (lookup 'high vars)))
    (implies (and (varp key)
		  (not (equal (param1 key) 'mid))
		  (not (equal (param1 key) 'low))
		  (not (equal (param1 key) 'high))
		  (acl2-numberp keyval)
		  (varp lst)
		  (number-listp lstval)
		  (sorted lstval)
		  (not (equal (param1 lst) 'mid))
		  (not (equal (param1 lst) 'high))
		  (not (equal (param1 lst) 'low))
		  (natp lowval)
		  (< highval (len lstval))
		  (integerp highval)
		  (not (member-equal keyval (slice lowval highval lstval)))
		  (natp steps)
		  (natp count)
		  (< 1 count)
		  ;(not (timedoutp (run-status (run (binarysearch-while key lst) 'ok vars steps count))))
		  (equal lst1 lstval)
		  (equal key1 keyval)
		  ;; need to consider this case separately
		  (equal lowval highval)
		  )
	     (equal (run (binarysearch-while key lst) 'ok vars steps count)
		    (mv-let (success endlow endmid endhigh endcalls)
			    (recursiveBS-helper keyval lstval lowval nil highval 0)
			    (declare (ignore success))
			    (mv 'ok
				(store 'high endhigh
				       (store 'low endlow
					      (store 'mid endmid vars)))
				(+ 4 (* 26 endcalls) steps)))))))

(defthmd binarysearch-while-test-inductive-case2-subcase2
  ;; This is the case where low equals high - 1
  (let ((keyval (lookup (param1 key) vars))
	(lstval (lookup (param1 lst) vars))
	(lowval (lookup 'low vars))
	(highval (lookup 'high vars)))
    (implies (and (varp key)
		  (not (equal (param1 key) 'mid))
		  (not (equal (param1 key) 'low))
		  (not (equal (param1 key) 'high))
		  (acl2-numberp keyval)
		  (varp lst)
		  (number-listp lstval)
		  (sorted lstval)
		  (not (equal (param1 lst) 'mid))
		  (not (equal (param1 lst) 'high))
		  (not (equal (param1 lst) 'low))
		  (natp lowval)
		  (< highval (len lstval))
		  (integerp highval)
		  (not (member-equal keyval (slice lowval highval lstval)))
		  (natp steps)
		  (natp count)
		  (if (< keyval (nth lowval lstval))
		      (< 1 count)
		    (< 2 count))
		  ;(not (timedoutp (run-status (run (binarysearch-while key lst) 'ok vars steps count))))
		  (equal lst1 lstval)
		  (equal key1 keyval)
		  ;; need to consider this case separately
		  (equal (1+ lowval) highval)
		  )
	     (equal (run (binarysearch-while key lst) 'ok vars steps count)
		    (mv-let (success endlow endmid endhigh endcalls)
			    (recursiveBS-helper keyval lstval lowval nil highval 0)
			    (declare (ignore success))
			    (mv 'ok
				(store 'high endhigh
				       (store 'low endlow
					      (store 'mid endmid vars)))
				(+ 4 (* 26 endcalls) steps)))))))

(defthm binarysearch-while-count-lemma
  ;; This is for the case where low = high
  (let ((keyval (lookup (param1 key) vars))
	(lstval (lookup (param1 lst) vars))
	(lowval (lookup 'low vars))
	(highval (lookup 'high vars)))
    (implies (and (varp key)
		  (not (equal (param1 key) 'mid))
		  (not (equal (param1 key) 'low))
		  (not (equal (param1 key) 'high))
		  (acl2-numberp keyval)
		  (varp lst)
		  (number-listp lstval)
		  (sorted lstval)
		  (not (equal (param1 lst) 'mid))
		  (not (equal (param1 lst) 'high))
		  (not (equal (param1 lst) 'low))
		  (natp lowval)
		  (< highval (len lstval))
		  (integerp highval)
		  (natp steps)
		  (not (timedoutp (run-status (run (binarysearch-while key lst) 'ok vars steps count))))
		  (equal lowval highval)
		  (not (equal keyval (nth lowval lstval)))
		  )
	     (< 1 count)))
  :hints (("Goal" :in-theory (enable binarysearch-while))
	  ("Subgoal 1" :expand (run (list 'while
					  '(<= (var low) (var high))
					  (binarysearch-while-body key lst))
				    'ok
				    vars steps count))))

;; Consider separately the case where low = high.

(defthm not-member-not-in-slice
  (implies (and (not (member-equal key (slice lowval highval lst)))
		(natp lowval)
		(natp highval)
		(natp midval)
		(<= lowval midval)
		(<= midval highval)
		(< highval (len lst))
		)
	   (not (equal key (nth midval lst)))))

;; >> Try to eliminate the instructions list from this one. 

(defthm not-member-not-in-slice-corollary
  (implies (and (not (member-equal key (slice lowval highval lst)))
		(natp lowval)
		(natp highval)
		(<= lowval highval)
		(< highval (len lst))
		)
	   (not (EQUAL key (nth (flr (+ lowval highval) 2) lst))))
  :hints (("Goal" :INSTRUCTIONS (:PROMOTE (:DV 1) (:REWRITE NOT-MEMBER-NOT-IN-SLICE)
                                :BASH :BASH :BASH :BASH :BASH (:CHANGE-GOAL NIL T)
                                :BASH :BASH :S (:USE (:INSTANCE FLR-BOUNDS (LOW LOWVAL)
								(HIGH HIGHVAL)))
                                :BASH))))

(defthm binarysearch-while-count-lemma2
  (let ((keyval (lookup (param1 key) vars))
	(lstval (lookup (param1 lst) vars))
	(lowval (lookup 'low vars))
	(highval (lookup 'high vars)))
    (implies (and (varp key)
		  (not (equal (param1 key) 'mid))
		  (not (equal (param1 key) 'low))
		  (not (equal (param1 key) 'high))
		  (acl2-numberp keyval)
		  (varp lst)
		  (number-listp lstval)
		  (sorted lstval)
		  (not (equal (param1 lst) 'mid))
		  (not (equal (param1 lst) 'high))
		  (not (equal (param1 lst) 'low))
		  (natp lowval)
		  (< highval (len lstval))
		  (integerp highval)
		  (natp steps)
		  (not (timedoutp (run-status (run (binarysearch-while key lst) 'ok vars steps count))))
		  (equal (1+ lowval) highval)
		  (not (equal keyval (nth lowval lstval)))
		  (not (equal keyval (nth highval lstval)))
		  )
	     (if (< keyval (nth lowval lstval))
		 (< 1 count)
	       (< 2 count))))
  :hints (("Goal" :in-theory (enable binarysearch-while
				     run-while-expander))))


(defun bs-ind2 ( lst key vars steps count calls)
;   (declare (xargs :measure (acl2-count count)))
  (declare (xargs :measure (nfix (1+ (- (lookup 'high vars) (lookup 'low vars))))))
		  ;:hints (("Goal" :in-theory (enable flr)))))
  (if (or (< (lookup 'high vars) (lookup 'low vars))
	  (not (natp (lookup 'low vars)))
	  (not (natp (lookup 'high vars))))
      t
    (let ((mid (flr (+ (lookup 'low vars) (lookup 'high vars)) 2)))
      (if (equal (lookup 'low vars) (lookup 'high vars))
	  t
	(if (equal (1+ (lookup 'low vars)) (lookup 'high vars))
	    t
	  (if (< key (nth mid lst))
	      (bs-ind2 lst key
		       (store 'high (1- mid)
			      (store 'mid mid vars))
		       (+ 26 steps)
		       (1- count)
		       (1+ calls))
	    (bs-ind2 lst key
		     (store 'low (1+ mid)
			    (store 'mid mid vars))
		     (+ 26 steps)
		     (1- count)
		     (1+ calls))))))))

;; >> I should be able to clean up the instruction list, at least to
;;    eliminate the add-abbreviations

(defthm binarysearch-while-test-inductive-case2
  ;; This is the case where the key is not in the list
  (let ((keyval (lookup (param1 key) vars))
	(lstval (lookup (param1 lst) vars))
	(lowval (lookup 'low vars))
	(highval (lookup 'high vars)))
    (implies (and (varp key)
		  (not (equal (param1 key) 'mid))
		  (not (equal (param1 key) 'low))
		  (not (equal (param1 key) 'high))
		  (acl2-numberp keyval)
		  (varp lst)
		  (number-listp lstval)
		  (sorted lstval)
		  (not (equal (param1 lst) 'mid))
		  (not (equal (param1 lst) 'high))
		  (not (equal (param1 lst) 'low))
		  (natp lowval)
		  (< highval (len lstval))
		  (integerp highval)
		  (not (member-equal keyval (slice lowval highval lstval)))
		  (natp steps)
		  (not (timedoutp (run-status (run (binarysearch-while key lst) 'ok vars steps count))))
		  (natp count)
		  (equal lst1 lstval)
		  (equal key1 keyval)
		  )
	     (equal (run (binarysearch-while key lst) 'ok vars steps count)
		    (mv-let (success endlow endmid endhigh endcalls)
			    (recursiveBS-helper keyval lstval lowval nil highval 0)
			    (declare (ignore success))
			    (mv 'ok
				(store 'high endhigh
				       (store 'low endlow
					      (if (< highval lowval)
						  vars
						(store 'mid endmid vars))))
				(+ 4 (* 26 endcalls) steps))))))
  :hints (("goal" :instructions
	   (:expand :promote (:claim (not (zp count)))
	    (:in-theory (enable recursivebs-helper-calls re-order-store
				recursivebs-helper-calls4-corollary))
	    (:induct (bs-ind2 lst1 key1 vars steps count calls))
	    (:change-goal (main . 6)) :bash (:change-goal (main . 5))
	    :promote
	    (:prove
	     :hints
	     (("goal"
	       :use binarysearch-while-test-inductive-case2-subcase1
	       :in-theory (disable binarysearch-while-test-inductive-case2-subcase1))))
	    (:change-goal (main . 4))
	    (:prove
	     :hints
	     (("goal"
	       :use (binarysearch-while-count-lemma2
		     binarysearch-while-test-inductive-case2-subcase2)
	       :in-theory (disable binarysearch-while-test-inductive-case2-subcase2
				   binarysearch-while-count-lemma2))))
	    (:in-theory (enable recursivebs-helper-calls
				recursivebs-helper-calls4-corollary
				;recursivebs-helper-mid3
				))
	    (:prove
	     :hints (("goal" :in-theory (enable recursivebs-helper-calls
						recursivebs-helper-calls4-corollary
						;recursivebs-helper-mid3
						recursivebs-helper-mid2))))
	    :bash (:dv 1) := (:drop 6) :top :bash
	    (:add-abbreviation mid
			       (flr (+ (lookup 'low vars)
				       (lookup 'high vars))
				    2))
	    (:add-abbreviation mid-1
			       (+ -1
				  (flr (+ (lookup 'low vars)
					  (lookup 'high vars))
				       2)))
	    (:= (recursivebs-helper (lookup (cadr key) vars)
				    (lookup (cadr lst) vars)
				    (lookup 'low vars)
				    (? mid)
				    (? mid-1)
				    0)
		(recursivebs-helper (lookup (cadr key) vars)
				    (lookup (cadr lst) vars)
				    (lookup 'low vars)
				    nil (? mid-1)
				    0)
		t)
	    (:add-abbreviation rb2
			       (recursivebs-helper (lookup (cadr key) vars)
						   (lookup (cadr lst) vars)
						   (lookup 'low vars)
						   nil (? mid-1)
						   0))
	    (:dv 1)
	    (:rewrite re-order-store)
	    :top :s :bash (:dv 1)
	    (:rewrite recursivebs-helper-mid2)
	    :top :s
	    :bash :bash
	    :bash
	    (:prove :hints (("goal" :in-theory (enable recursivebs-helper-mid2))))))))

(defthm binarysearch-while-test-induction
  ;; This is the actual proof of the binarysearch while
  (let ((keyval (lookup (param1 key) vars))
	(lstval (lookup (param1 lst) vars))
	(lowval (lookup 'low vars))
	(highval (lookup 'high vars)))
    (implies (and (varp key)
		  (not (equal (param1 key) 'mid))
		  (not (equal (param1 key) 'low))
		  (not (equal (param1 key) 'high))
		  (acl2-numberp keyval)
		  (varp lst)
		  (number-listp lstval)
		  (sorted lstval)
		  (not (equal (param1 lst) 'mid))
		  (not (equal (param1 lst) 'high))
		  (not (equal (param1 lst) 'low))
		  (natp lowval)
		  (< highval (len lstval))
		  (integerp highval)
		  (natp steps)
		  (not (timedoutp (run-status (run (binarysearch-while key lst) 'ok vars steps count))))
		  (natp count)
		  )
	     (equal (run (binarysearch-while key lst) 'ok vars steps count)
		    (if (member-equal keyval (slice lowval highval lstval))
			(mv-let (success endlow endmid endhigh endcalls)
				(recursiveBS-helper keyval lstval lowval nil highval 0)
				(declare (ignore success))
				(mv 'returned
				    (store 'result endmid
					   (store 'high endhigh
						  (store 'low endlow
							 (store 'mid endmid vars))))
				    (+ 18 (* 26 endcalls) steps)))
		      (mv-let (success endlow endmid endhigh endcalls)
			      (recursiveBS-helper keyval lstval lowval nil highval 0)
			      (declare (ignore success))
			      (mv 'ok
				  (store 'high endhigh
					 (store 'low endlow
						(if (< highval lowval)
						    vars
						  (store 'mid endmid vars))))
				  (+ 4 (* 26 endcalls) steps)))))))
  :hints (("Goal" :INSTRUCTIONS (:EXPAND :PROMOTE
					 (:CASESPLIT (MEMBER-EQUAL (LOOKUP (CADR KEY) VARS)
								   (SLICE (LOOKUP 'LOW VARS)
									  (LOOKUP 'HIGH VARS)
									  (LOOKUP (CADR LST) VARS))))
					 (:DV 1) (:REWRITE BINARYSEARCH-WHILE-TEST-INDUCTIVE-CASE1)
					 :TOP :BASH (:DV 1)
					 (:REWRITE BINARYSEARCH-WHILE-TEST-INDUCTIVE-CASE2) :TOP :S))))

;; >> See if this is used
; (defthm null-nthcdr
;   (implies (and (<= (len lst) k)
; 		(natp k)
; 		(true-listp lst))
; 	   (equal (nthcdr k lst)
; 		  nil)))

(defthm binarysearch-while-test-induction-corollary1
  ;; Use the binarysearch-while lemma wrt the state derived 
  ;; from the initial two assignments.  This is the case where
  ;; the key is in the list. 
  (let ((keyval (lookup (param1 key) vars))
	(lstval (lookup (param1 lst) vars)))
    (implies (and (varp key)
		  (not (equal (param1 key) 'mid))
		  (not (equal (param1 key) 'low))
		  (not (equal (param1 key) 'high))
		  (acl2-numberp keyval)
		  (varp lst)
		  (number-listp lstval)
		  (sorted lstval)
		  (not (equal (param1 lst) 'mid))
		  (not (equal (param1 lst) 'high))
		  (not (equal (param1 lst) 'low))
		  (natp steps)
		  (not (timedoutp (run-status (run (binarysearch key lst) 'ok vars steps count))))
		  (natp count)
		  ;; This is case where the key is in the list.
		  (member-equal keyval lstval)
		  )
	     (equal (run (binarysearch-while key lst)
			 'ok
			 (store 'high (+ -1 (len (lookup (cadr lst) vars))) (store 'low 0 vars))
			 (+ 7 steps)
			 count)
		    (mv-let (success endlow endmid endhigh endcalls)
			    (recursivebs-helper keyval lstval 0 nil (1- (len lstval)) 0)
			    (declare (ignore success))
			    (list 'returned
				  (store 'result
					 endmid
					 (store 'mid
						endmid
						(store 'high
						       endhigh
						       (store 'low endlow vars))))
				  (+ 25 steps (* 26 endcalls)))))))
 :INSTRUCTIONS (:EXPAND :PROMOTE (:DV 1)
                        (:REWRITE BINARYSEARCH-WHILE-TEST-INDUCTION)
                        (:S :IN-THEORY (THEORY 'MINIMAL-THEORY))
                        (:DIVE 1) :SL (:DIVE 2) (:REWRITE SLICE-WHOLE-LIST ((LOW 0)))
                        :TOP :S :S :BASH :BASH :BASH :BASH :BASH :BASH :BASH))

(defthm binarysearch-while-test-induction-corollary2
  ;; Use the binarysearch-while lemma wrt the state derived 
  ;; from the initial two assignments.  This is the case where
  ;; the key is not in the list, and the list is empty.
  (let ((keyval (lookup (param1 key) vars))
	(lstval (lookup (param1 lst) vars)))
    (implies (and (varp key)
		  (not (equal (param1 key) 'mid))
		  (not (equal (param1 key) 'low))
		  (not (equal (param1 key) 'high))
		  (acl2-numberp keyval)
		  (varp lst)
		  (number-listp lstval)
		  (sorted lstval)
		  (not (equal (param1 lst) 'mid))
		  (not (equal (param1 lst) 'high))
		  (not (equal (param1 lst) 'low))
		  (natp steps)
		  (not (timedoutp (run-status (run (binarysearch key lst) 'ok vars steps count))))
		  (natp count)
		  ;; The key is not in the list because the list is empty.
		  (not lstval)
		  )
	     (equal (run (binarysearch-while key lst)
			 'ok
			 (store 'high (+ -1 (len (lookup (cadr lst) vars))) (store 'low 0 vars))
			 (+ 7 steps)
			 count)
		    (list 'ok
			  (store 'high -1 (store 'low 0 vars))
			  (+ 11 steps)))))
     :INSTRUCTIONS (:EXPAND :PROMOTE (:DV 1)
                          (:REWRITE BINARYSEARCH-WHILE-TEST-INDUCTION)
                          :TOP :S :S :S :S :S :S :S :S :BASH))

(defthm binarysearch-while-test-induction-corollary2-version2
  ;; Use the binarysearch-while lemma wrt the state derived 
  ;; from the initial two assignments.  This is the case where
  ;; the key is not in the list, and the list is empty.
  (let ((keyval (lookup (param1 key) vars))
	(lstval (lookup (param1 lst) vars)))
    (implies (and (varp key)
		  (not (equal (param1 key) 'mid))
		  (not (equal (param1 key) 'low))
		  (not (equal (param1 key) 'high))
		  (acl2-numberp keyval)
		  (varp lst)
		  (number-listp lstval)
		  (sorted lstval)
		  (not (equal (param1 lst) 'mid))
		  (not (equal (param1 lst) 'high))
		  (not (equal (param1 lst) 'low))
		  (natp steps)
		  (not (timedoutp (run-status (run (binarysearch key lst) 'ok vars steps count))))
		  (natp count)
		  ;; The key is not in the list because the list is empty.
		  (not lstval)
		  )
	     (equal (run (binarysearch-while key lst)
			 'ok
			 ;; Since the list is empty, high is initially 0
			 (store 'high -1 (store 'low 0 vars))
			 (+ 7 steps)
			 count)
		    (list 'ok
			  (store 'high -1 (store 'low 0 vars))
			  (+ 11 steps)))))
  :INSTRUCTIONS (:EXPAND :PROMOTE (:USE BINARYSEARCH-WHILE-TEST-INDUCTION-COROLLARY2)
			 :PROMOTE (:DEMOTE 1) (:DIVE 1) :EXPAND
			 (:= (LEN (LOOKUP (CADR LST) VARS)) 0) :TOP :S))

(defthm binarysearch-while-test-induction-corollary2-version2-status
  ;; This just isolates the status; needed for some reason. 
  (let ((keyval (lookup (param1 key) vars))
	(lstval (lookup (param1 lst) vars)))
    (implies (and (varp key)
		  (not (equal (param1 key) 'mid))
		  (not (equal (param1 key) 'low))
		  (not (equal (param1 key) 'high))
		  (acl2-numberp keyval)
		  (varp lst)
		  (number-listp lstval)
		  (sorted lstval)
		  (not (equal (param1 lst) 'mid))
		  (not (equal (param1 lst) 'high))
		  (not (equal (param1 lst) 'low))
		  (natp steps)
		  (not (timedoutp (run-status (run (binarysearch key lst) 'ok vars steps count))))
		  (natp count)
		  ;; The key is not in the list because the list is empty.
		  (not lstval)
		  )
	     (equal (car (run (binarysearch-while key lst)
			      'ok
			      ;; Since the list is empty, high is initially 0
			      (store 'high -1 (store 'low 0 vars))
			      (+ 7 steps)
			      count))
		    'ok)))
   :INSTRUCTIONS (:EXPAND :PROMOTE (:DIVE 1 1)
			  (:REWRITE BINARYSEARCH-WHILE-TEST-INDUCTION-COROLLARY2-VERSION2)
			  :TOP :S))

(defthm binarysearch-while-test-induction-corollary3
  ;; Use the binarysearch-while lemma wrt the state derived 
  ;; from the initial two assignments.  This is the case where
  ;; the key is not in the list, and the list is non-empty.
  (let ((keyval (lookup (param1 key) vars))
	(lstval (lookup (param1 lst) vars)))
    (implies (and (varp key)
		  (not (equal (param1 key) 'mid))
		  (not (equal (param1 key) 'low))
		  (not (equal (param1 key) 'high))
		  (acl2-numberp keyval)
		  (varp lst)
		  (number-listp lstval)
		  (sorted lstval)
		  (not (equal (param1 lst) 'mid))
		  (not (equal (param1 lst) 'high))
		  (not (equal (param1 lst) 'low))
		  (natp steps)
		  (not (timedoutp (run-status (run (binarysearch key lst) 'ok vars steps count))))
		  (natp count)
		  ;; This is case where the key is not in the list.
		  (not (member-equal keyval lstval))
		  ;; The list is not empty
		  lstval
		  )
	     (equal (run (binarysearch-while key lst)
			 'ok
			 (store 'high (+ -1 (len (lookup (cadr lst) vars))) (store 'low 0 vars))
			 (+ 7 steps)
			 count)
		    (mv-let (success endlow endmid endhigh endcalls)
			    (recursivebs-helper keyval lstval 0 nil (1- (len lstval)) 0)
			    (declare (ignore success))
			    (mv 'ok
				(store 'mid endmid
				       (store 'high endhigh
					      (store 'low endlow vars)))
				(+ 11 (* 26 endcalls) steps))))))
    :instructions (:expand :promote (:dv 1) (:rewrite binarysearch-while-test-induction)
			   :top (:dive 1 1) :s (:change-goal nil t)
			   :s :s :s :s :s :s :s (:= t) (:dive 2)
			   (:rewrite slice-whole-list ((low 0)))
			   :top :s (:dive 1) (:rewrite non-empty-len)
			   :top :s :bash :bash (:rewrite non-empty-len) :bash))

(defthm binarysearch-while-test-induction-corollary3-corollary
  ;; Use the binarysearch-while lemma wrt the state derived 
  ;; from the initial two assignments.  This is the case where
  ;; the key is not in the list, and the list is non-empty.
  (let ((keyval (lookup (param1 key) vars))
	(lstval (lookup (param1 lst) vars)))
    (implies (and (varp key)
		  (not (equal (param1 key) 'mid))
		  (not (equal (param1 key) 'low))
		  (not (equal (param1 key) 'high))
		  (acl2-numberp keyval)
		  (varp lst)
		  (number-listp lstval)
		  (sorted lstval)
		  (not (equal (param1 lst) 'mid))
		  (not (equal (param1 lst) 'high))
		  (not (equal (param1 lst) 'low))
		  (natp steps)
		  (not (timedoutp (run-status (run (binarysearch key lst) 'ok vars steps count))))
		  (natp count)
		  ;; This is case where the key is not in the list.
		  (not (member-equal keyval lstval))
		  ;; The list is not empty
		  lstval
		  )
	     (equal (car (run (binarysearch-while key lst)
			      'ok
			      (store 'high (+ -1 (len (lookup (cadr lst) vars))) (store 'low 0 vars))
			      (+ 7 steps)
			      count))
		    'ok)))
    :hints (("Goal" :use binarysearch-while-test-induction-corollary3
	            :in-theory (disable binarysearch-while-test-induction-corollary3))))

(defthm binarysearch-correctness-lemma-setup
  ;; This characterizes the functional behavior of the two initial
  ;; assignments of binarysearch.  These happen whether key is 
  ;; present or not.
  (let ((keyval (lookup (param1 key) vars))
	(lstval (lookup (param1 lst) vars)))
    (implies (and (varp key)
		  (not (equal (param1 key) 'mid))
		  (not (equal (param1 key) 'low))
		  (not (equal (param1 key) 'high))
		  (acl2-numberp keyval)
		  (varp lst)
		  (definedp (cadr lst) vars)
		  (number-listp lstval)
		  (sorted lstval)
		  (not (equal (param1 lst) 'mid))
		  (not (equal (param1 lst) 'high))
		  (not (equal (param1 lst) 'low))
		  (natp steps)
		  (not (timedoutp (run-status (run (binarysearch key lst) 'ok vars steps count))))
		  (natp count)
		  )
	     (equal (run (list 'seq '(assign (var low) (lit . 0))
			       (list 'seq (list 'assign '(var high)
						(list* '- (list 'len lst) '((lit . 1))))
				     statement))
			 'ok vars steps count)
		    (RUN STATEMENT 'OK
			 (STORE 'HIGH (+ -1 (LEN (LOOKUP (CADR LST) VARS)))
				(STORE 'LOW 0 VARS))
			 (+ 7 STEPS)
			 COUNT)))))

(in-theory (disable binarysearch-while-body-lemma
		    binarysearch-while-test-fails
		    binarysearch-while-test-succeeds
		    binarysearch-while-test-succeeds2
		    binarysearch-while-test-succeeds2-corollary1
		    binarysearch-while-test-succeeds2-corollary2
		    binarysearch-while-test-succeeds2-corollary3
		    binarysearch-while-test-succeeds2-corollary4
		    binarysearch-while-low-high-equal
		    binarysearch-while-low-high-differ-by-one-subcase1
		    binarysearch-while-low-high-differ-by-one-subcase2
		    ;binarysearch-while-low-high-differ-by-one-subcase3
		    binarysearch-while-test-inductive-case1
		    binarysearch-while-test-inductive-case2-subcase1
		    binarysearch-while-test-inductive-case2-subcase2
		    binarysearch-while-count-lemma
		    binarysearch-while-count-lemma2
		    binarysearch-while-test-inductive-case2
		    binarysearch-while-test-induction
		    binarysearch-while-test-induction-corollary1
		    binarysearch-while-test-induction-corollary2
		    binarysearch-while-test-induction-corollary3))

(defthm binarysearch-correctness-lemma-list-empty
  ;; This characterizes the functional behavior of binarysearch.
  ;; There are three cases: lst is empty, lst contains key, and
  ;; lst does not contain key.  This is for the case where lst is empty.
  (let ((keyval (lookup (param1 key) vars))
	(lstval (lookup (param1 lst) vars)))
    (implies (and (varp key)
		  (not (equal (param1 key) 'mid))
		  (not (equal (param1 key) 'low))
		  (not (equal (param1 key) 'high))
		  (acl2-numberp keyval)
		  (varp lst)
		  (definedp (cadr lst) vars)
		  (number-listp lstval)
		  (sorted lstval)
		  (not (equal (param1 lst) 'mid))
		  (not (equal (param1 lst) 'high))
		  (not (equal (param1 lst) 'low))
		  (natp steps)
		  (not (timedoutp (run-status (run (binarysearch key lst) 'ok vars 0 count))))
		  (natp count)
		  ;; lst is empty
		  (not lstval)
		  )
	     (equal (run (binarysearch key lst) 'ok vars 0 count)
		    (mv 'returned
			(store 'result
				-1 (store 'high -1 (store 'low 0 vars)))
			13))))
   :INSTRUCTIONS (:EXPAND :PROMOTE
			  (:CLAIM (EQUAL (CAR (RUN (BINARYSEARCH-WHILE KEY LST)
						   'OK
						   (STORE 'HIGH -1 (STORE 'LOW 0 VARS))
						   7 COUNT))
					 'OK)
				  T)
			  :BASH (:DV 1) (:REWRITE BINARYSEARCH-WHILE-TEST-INDUCTION-COROLLARY2-VERSION2-STATUS)))

(defthm binarysearch-correctness-lemma-key-not-present
  ;; This characterizes the functional behavior of binarysearch.
  ;; There are three cases: lst is empty, lst contains key, and
  ;; lst does not contain key. This is the case where key is 
  ;; not present.
  (let ((keyval (lookup (param1 key) vars))
	(lstval (lookup (param1 lst) vars)))
    (implies (and (varp key)
		  (not (equal (param1 key) 'mid))
		  (not (equal (param1 key) 'low))
		  (not (equal (param1 key) 'high))
		  (acl2-numberp keyval)
		  (varp lst)
		  (number-listp lstval)
		  (sorted lstval)
		  (not (equal (param1 lst) 'mid))
		  (not (equal (param1 lst) 'high))
		  (not (equal (param1 lst) 'low))
		  (natp steps)
		  (not (timedoutp (run-status (run (binarysearch key lst) 'ok vars 0 count))))
		  (natp count)
		  ;; List is not empty
		  lstval
		  ;; but key is not present
		  (not (member-equal keyval lstval))
		  )
	     (equal (run (binarysearch key lst) 'ok vars 0 count)
		    (mv-let (success endlow endmid endhigh endcalls)
			    (recursivebs-helper keyval lstval 0 nil (1- (len lstval)) 0)
			    (declare (ignore success))
			    (mv 'returned
				(store 'result -1
				       (store 'mid endmid
					      (store 'high endhigh
						     (store 'low endlow vars))))
				(+ 13 (* 26 endcalls)))))))
  :INSTRUCTIONS (:EXPAND :PROMOTE
			 (:CLAIM (EQUAL (CAR (RUN (BINARYSEARCH-WHILE KEY LST)
						  'OK
						  (STORE 'HIGH
							 (+ -1 (LEN (LOOKUP (CADR LST) VARS)))
							 (STORE 'LOW 0 VARS))
						  7 COUNT))
					'OK)
				 T)
			 (:IN-THEORY (ENABLE BINARYSEARCH-WHILE-TEST-INDUCTION-COROLLARY3))
			 :BASH (:DIVE 1 1) (:REWRITE BINARYSEARCH-WHILE-TEST-INDUCTION-COROLLARY3) :TOP :S))

(defthm binarysearch-correctness-lemma-key-present
  ;; This characterizes the functional behavior of binarysearch.
  ;; There are three cases: lst is empty, lst contains key, and
  ;; lst does not contain key. This is the case where key is 
  ;; in list.
  (let ((keyval (lookup (param1 key) vars))
	(lstval (lookup (param1 lst) vars)))
    (implies (and (varp key)
		  (not (equal (param1 key) 'mid))
		  (not (equal (param1 key) 'low))
		  (not (equal (param1 key) 'high))
		  (acl2-numberp keyval)
		  (varp lst)
		  (definedp (cadr lst) vars)
		  (number-listp lstval)
		  (sorted lstval)
		  (not (equal (param1 lst) 'mid))
		  (not (equal (param1 lst) 'high))
		  (not (equal (param1 lst) 'low))
		  (natp steps)
		  (not (timedoutp (run-status (run (binarysearch key lst) 'ok vars 0 count))))
		  (natp count)
		  ;; Key is present in the list.
		  (member-equal keyval lstval)
		  )
	     (equal (run (binarysearch key lst) 'ok vars 0 count)
		    (mv-let (success endlow endmid endhigh endcalls)
			    (recursivebs-helper keyval lstval 0 nil (1- (len lstval)) 0)
			    (declare (ignore success))
			    (mv 'returned
				(store 'result
				       endmid
				       (store 'mid
					      endmid
					      (store 'high
						     endhigh
						     (store 'low endlow vars))))
				(+ 25 (* 26 endcalls)))))))
  :INSTRUCTIONS (:EXPAND :PROMOTE
			 (:CLAIM (EQUAL (CAR (RUN (BINARYSEARCH-WHILE KEY LST)
						  'OK
						  (STORE 'HIGH
							 (+ -1 (LEN (LOOKUP (CADR LST) VARS)))
							 (STORE 'LOW 0 VARS))
						  7 COUNT))
					'RETURNED)
				 T)
			 (:IN-THEORY (ENABLE BINARYSEARCH-WHILE-TEST-INDUCTION-COROLLARY1))
			 :BASH (:DIVE 1 1) (:REWRITE BINARYSEARCH-WHILE-TEST-INDUCTION-COROLLARY1)
			 :TOP :S))

(defthm binarysearch-correctness-lemma
  ;; This characterizes the functional behavior of binarysearch.
  ;; There are three cases: lst is empty, lst contains key, and
  ;; lst does not contain key. 
  (let ((keyval (lookup (param1 key) vars))
	(lstval (lookup (param1 lst) vars)))
    (implies (and (varp key)
		  (not (equal (param1 key) 'mid))
		  (not (equal (param1 key) 'low))
		  (not (equal (param1 key) 'high))
		  (acl2-numberp keyval)
		  (varp lst)
		  (definedp (cadr lst) vars)
		  (number-listp lstval)
		  (sorted lstval)
		  (not (equal (param1 lst) 'mid))
		  (not (equal (param1 lst) 'high))
		  (not (equal (param1 lst) 'low))
		  (natp steps)
		  (not (timedoutp (run-status (run (binarysearch key lst) 'ok vars 0 count))))
		  (natp count)
		  )
	     (equal (run (binarysearch key lst) 'ok vars 0 count)
		    (if (not lstval)
			(mv 'returned
			    (store 'result -1 (store 'high -1 (store 'low 0 vars)))
			    13)
		      (if (not (member-equal keyval lstval))
			  (mv-let (success endlow endmid endhigh endcalls)
				  (recursivebs-helper keyval lstval 0 nil (1- (len lstval)) 0)
				  (declare (ignore success))
				  (mv 'returned
				      (store 'result -1
					     (store 'mid endmid
						    (store 'high endhigh
							   (store 'low endlow vars))))
				      (+ 13 (* 26 endcalls))))
			(mv-let (success endlow endmid endhigh endcalls)
				(recursivebs-helper keyval lstval 0 nil (1- (len lstval)) 0)
				(declare (ignore success))
				(mv 'returned
				    (store 'result endmid
					   (store 'mid endmid
						  (store 'high endhigh
							 (store 'low endlow vars))))
				    (+ 25 (* 26 endcalls)))))))))
  :INSTRUCTIONS (:EXPAND :PROMOTE
			 (:CASESPLIT (NOT (LOOKUP (CADR LST) VARS)))
			 (:S :IN-THEORY (THEORY 'MINIMAL-THEORY)) (:DV 1)
			 (:REWRITE BINARYSEARCH-CORRECTNESS-LEMMA-LIST-EMPTY)
			 :TOP :S (:S :IN-THEORY (THEORY 'MINIMAL-THEORY))
			 (:CASESPLIT (MEMBER-EQUAL (LOOKUP (CADR KEY) VARS)
						   (LOOKUP (CADR LST) VARS)))
			 (:S :IN-THEORY (THEORY 'MINIMAL-THEORY)) (:DV 1)
			 (:REWRITE BINARYSEARCH-CORRECTNESS-LEMMA-KEY-PRESENT)
			 :TOP :S (:S :IN-THEORY (THEORY 'MINIMAL-THEORY)) (:DV 1)
			 (:REWRITE BINARYSEARCH-CORRECTNESS-LEMMA-KEY-NOT-PRESENT) :TOP :S))

(defthm binarysearch-correctness-lemma-steps-corollary
  ;; This characterizes the functional behavior of binarysearch.
  ;; There are three cases: lst is empty, lst contains key, and
  ;; lst does not contain key.  This captures how many steps.
  (let ((keyval (lookup (param1 key) vars))
	(lstval (lookup (param1 lst) vars)))
    (implies (and (varp key)
		  (not (equal (param1 key) 'mid))
		  (not (equal (param1 key) 'low))
		  (not (equal (param1 key) 'high))
		  (acl2-numberp keyval)
		  (varp lst)
		  (definedp (cadr lst) vars)
		  (number-listp lstval)
		  (sorted lstval)
		  (not (equal (param1 lst) 'mid))
		  (not (equal (param1 lst) 'high))
		  (not (equal (param1 lst) 'low))
		  (natp steps)
		  (not (timedoutp (run-status (run (binarysearch key lst) 'ok vars 0 count))))
		  (natp count)
		  )
	     (equal (run-steps (run (binarysearch key lst) 'ok vars 0 count))
		    (if (not lstval)
			13
		      (mv-let (success endlow endmid endhigh endcalls)
			      (recursivebs-helper keyval lstval 0 nil (1- (len lstval)) 0)
			      (declare (ignore success endlow endmid endhigh))
			      (if (not (member-equal keyval lstval))
				  (+ 13 (* 26 endcalls))
				(+ 25 (* 26 endcalls))))))))
  :instructions (:expand :promote (:dive 1 2)
			 (:rewrite binarysearch-correctness-lemma)
			 :top :s))

(defthm binarysearch-correctness-lemma-steps-bound
  ;; This characterizes the functional behavior of binarysearch.
  ;; There are three cases: lst is empty, lst contains key, and
  ;; lst does not contain key. This bounds the steps count.
  (let ((keyval (lookup (param1 key) vars))
	(lstval (lookup (param1 lst) vars)))
    (implies (and (varp key)
		  (not (equal (param1 key) 'mid))
		  (not (equal (param1 key) 'low))
		  (not (equal (param1 key) 'high))
		  (acl2-numberp keyval)
		  (varp lst)
		  (definedp (cadr lst) vars)
		  (number-listp lstval)
		  (sorted lstval)
		  (not (equal (param1 lst) 'mid))
		  (not (equal (param1 lst) 'high))
		  (not (equal (param1 lst) 'low))
		  (natp steps)
		  (not (timedoutp (run-status (run (binarysearch key lst) 'ok vars 0 count))))
		  (natp count)
		  )
	     (<= (run-steps (run (binarysearch key lst) 'ok vars 0 count))
		 (mv-let (success endlow endmid endhigh endcalls)
			 (recursivebs-helper keyval lstval 0 nil (1- (len lstval)) 0)
			 (declare (ignore success endlow endmid endhigh))
			 (+ 25 (* 26 endcalls))))))
  :instructions
  (:expand :promote (:dive 1 2)
	   (:rewrite binarysearch-correctness-lemma-steps-corollary)
	   :top :bash))

(in-theory (disable binarysearch-correctness-lemma-list-empty
	            binarysearch-correctness-lemma-key-not-present
                    binarysearch-correctness-lemma-key-present
		    binarysearch-correctness-lemma))

;----------------------------------------------------------------------

(defun recursiveBS2-helper (key lst low high)
  ;; This is the recursive version of binary search without the 
  ;; extraneous parameters that I needed to do the proof of the 
  ;; procedural version.
  (declare (xargs :measure (nfix (1+ (- high low)))
		  :hints (("Goal" :in-theory (e/d (flr) (HIGH-LOW-KLUDGE2))))))
  (if (or (< high low)
	  (not (natp low))
	  (not (integerp high))
	  )
      -1
    (let ((newmid (flr (+ low high) 2)))
      (if (equal key (nth newmid lst))
	  newmid
	(if (< key (nth newmid lst))
	    (recursiveBS2-helper key lst low (1- newmid))
	  (recursiveBS2-helper key lst (1+ newmid) high))))))

;; This is the recursive version of binary search

(defun recursiveBS2 (key lst)
  (recursiveBS2-helper key lst 0 (1- (len lst))))

;; >> Now I need to prove that the more complicated versions are
;;    the same as these. 

(defthmd recursiveBS-helper-versions
  ;; This shows the recursiveBS-helper and 
  ;; recursiveBS2-helper are really equivalent.
  (implies (and (natp low)
		(integerp high)
		(number-listp lst)
		(acl2-numberp key))
	   (mv-let (success endlow endmid endhigh endcalls)
		   ;; Notice that calls doesn't matter here, but I
		   ;; really need it to be 0.  Fix this.
		   (recursivebs-helper key lst low mid high calls)
		   (declare (ignore endlow endhigh endcalls))
		   (equal (recursiveBS2-helper key lst low high)
			  (if success endmid -1)))))

(defthmd recursiveBS-helper-versions-corollary
  ;; This shows the recursiveBS-helper and 
  ;; recursiveBS2-helper are really equivalent.
  (implies (and (natp low)
		(integerp high)
		(number-listp lst)
		(acl2-numberp key))
	   (mv-let (success endlow endmid endhigh endcalls)
		   ;; Notice that calls doesn't matter here, but I
		   ;; really need it to be 0.  Fix this.
		   (recursivebs-helper key lst low nil high 0)
		   (declare (ignore endlow endhigh endcalls))
		   (equal (recursiveBS2-helper key lst low high)
			  (if success endmid -1))))
  :hints (("Goal" :use (:instance recursiveBS-helper-versions (mid nil) (calls 0)))))

;; >> I don't think this is actually used, but it shows that the two versions 
;;    compute the same function. 

(defthm recursiveBS-versions-equivalent
  (implies (and (number-listp lst)
		(acl2-numberp key))
	   (equal (recursiveBS key lst)
		  (recursiveBS2 key lst)))
  :hints (("Goal" :cases (not lst)
	          :in-theory (enable RECURSIVEBS-HELPER-VERSIONS-COROLLARY))))

(in-theory (disable recursiveBS-helper-versions
		    recursiveBS-helper-versions-corollary
		    recursiveBS-versions-equivalent))

;----------------------------------------------------------------------

;; Since there's no native log function in ACL2, we just defined the log2
;; to be the number of times you can cut a list in half. 

;; >> There's actually a flaw in this.  The base case should include 
;;    (equal n 1).

(defun log2 (n)
  (declare (xargs :hints (("Goal" :in-theory (enable flr)))))
  (if (zp n)
      0
    (1+ (log2 (flr n 2)))))

(defthmd flr-natp2
  (implies (natp x)
	   (natp (flr x 2)))
  :hints (("Goal" :in-theory (enable flr))))

(defthm flr-natp2-corollary1
  (implies (natp x)
	   (<= 0 (flr x 2)))
  :hints (("Goal" :use flr-natp2))
  :rule-classes :linear)

(defthm flr-arg-lessp
  (implies (and (integerp x)
		(integerp y)
		(<= x y))
	   (<= (flr x 2) (flr y 2)))
  :hints (("goal" :in-theory (enable flr))))

(defun flr-ind (x y)
  (declare (xargs :hints (("Goal" :in-theory (enable flr)))))
  (if (or (zp x)
	  (zp y))
      t
    (flr-ind (flr x 2) (flr y 2))))

(defthm log2-less
  (implies (and (natp x)
		(natp y)
		(<= x y))
	   (<= (log2 x) (log2 y)))
  :hints (("Goal" :induct (flr-ind x y))))

(defun bs-count-calls (low high key lst)
  ;; This counts the number of recursive calls made by recursiveBS-helper.
  (declare (xargs :measure (nfix (1+ (- high low)))
		  :hints (("Goal" :in-theory (e/d (flr) (HIGH-LOW-KLUDGE2))))))
  (if (or (< high low)
	  (not (natp low))
	  (not (integerp high)))
      0
    (let ((mid (flr (+ low high) 2)))
      (if (equal key (nth mid lst))
	  0
	(if (< key (nth mid lst))
	    (1+ (bs-count-calls low (1- mid) key lst))
	  (1+ (bs-count-calls (1+ mid) high key lst)))))))

(defthm flr-high-low-kludge
  (implies (and (natp low)
		(natp high)
		(< low high))
	   (< (flr (+ high low) 2) high))
  :rule-classes (:rewrite :linear)
  :hints (("Goal" :in-theory (enable flr))))

(defthm nth-in-number-listp
  (implies (and (natp i)
		(< i (len lst))
		(number-listp lst))
	   (acl2-numberp (nth i lst))))

(defthm nth-mid-acl2-numberp
  (implies (and (natp low)
		(natp high)
		(< high (len lst))
		(<= low high)
		(number-listp lst))
	   (acl2-numberp (nth (flr (+ high low) 2) lst))))

(defthmd high-low-kludge
  (implies (and (natp low)
		(natp high)
		(< low high))
	   (<= (+ high (- (flr (+ high low) 2)))
	       (flr (+ 1 high (- low)) 2)))
  :hints (("Goal" :in-theory (enable flr))))

(defthmd high-low-kludge9
  (implies (and (natp low)
		(natp high)
		(< low high))
	   (<= (FLR (+ HIGH LOW) 2)
	       (+ LOW (FLR (+ 1 HIGH (- LOW)) 2))))
  :hints (("goal" :in-theory (enable flr))))

(defthm log2-bs-count-calls-induction-subcase1
  (implies (and (<= low high)
		(not (equal key (nth (flr (+ high low) 2) lst)))
		(<= (nth (flr (+ high low) 2) lst) key)
		(<= (bs-count-calls (+ 1 (flr (+ high low) 2))
			    high key lst)
		    (log2 (+ high (- (flr (+ high low) 2)))))
		(< high (len lst))
		(integerp low)
		(<= 0 low)
		(integerp high)
		(acl2-numberp key)
		(number-listp lst))
	   (<= (+ 1 (bs-count-calls (+ 1 (flr (+ high low) 2)) high key lst))
	       (log2 (+ 1 high (- low)))))
     :INSTRUCTIONS
     (:PROMOTE (:CASESPLIT (EQUAL LOW HIGH)) :BASH (:DIVE 1 1) :X :TOP :BASH
               (:USE (:INSTANCE LESS-EQUAL-TRANSITIVE
                                (X (BS-COUNT-CALLS (+ 1 (FLR (+ HIGH LOW) 2))
                                           HIGH KEY LST))
                                (Y (LOG2 (+ HIGH (- (FLR (+ HIGH LOW) 2)))))
                                (Z (LOG2 (FLR (+ 1 HIGH (- LOW)) 2)))))
               :PROMOTE (:DEMOTE 1) (:DIVE 1 1) (:S :IN-THEORY (THEORY 'MINIMAL-THEORY))
               (:= & T :HINTS (("Goal" :IN-THEORY (ENABLE HIGH-LOW-KLUDGE)))) :TOP :S))

(defthm log2-bs-count-calls-induction-subcase2
  (implies (and (<= low high)
		(not (equal key (nth (flr (+ high low) 2) lst)))
		(< key (nth (flr (+ high low) 2) lst))
		(<= (bs-count-calls low (+ -1 (flr (+ high low) 2))
			    key lst)
		    (log2 (+ (- low) (flr (+ high low) 2))))
		(< high (len lst))
		(integerp low)
		(<= 0 low)
		(integerp high)
		(acl2-numberp key)
		(number-listp lst))
	   (<= (+ 1 (bs-count-calls low (+ -1 (flr (+ high low) 2)) key lst))
	       (log2 (+ 1 high (- low)))))
     :INSTRUCTIONS
     (:PROMOTE (:CASESPLIT (EQUAL LOW HIGH)) :BASH (:DIVE 1 1) :X :UP :TOP :BASH
               (:USE (:INSTANCE LESS-EQUAL-TRANSITIVE (X (BS-COUNT-CALLS LOW (+ -1 (FLR (+ HIGH LOW) 2)) KEY LST))
                                (Y (LOG2 (+ (- LOW) (FLR (+ HIGH LOW) 2))))
                                (Z (LOG2 (FLR (+ 1 HIGH (- LOW)) 2)))))
               :PROMOTE (:DEMOTE 1) (:DIVE 1 1) :S (:= & T T) :TOP :S
               (:S :IN-THEORY (THEORY 'MINIMAL-THEORY)) :BASH (:DIVE 1) (:REWRITE LOG2-LESS)
               :BASH :BASH :BASH (:PROVE :HINTS (("goal" :IN-THEORY (ENABLE high-low-kludge9))))))

(defthm log2-bs-count-calls-relation1
  (implies (and (< high (len lst))
		(natp low)
		(integerp high)
		(acl2-numberp key)
		(number-listp lst))
	   (<= (bs-count-calls low high key lst)
	       (log2 (1+ (- high low)))))
  :hints (("Goal" :induct (bs-count-calls low high key lst)
	          :in-theory (enable high-low-kludge))))

(defthm log2-bs-count-calls-relation
  (implies (and (< high (len lst))
		(natp low)
		(integerp high)
		(acl2-numberp key)
		(number-listp lst))
	   (<= (bs-count-calls low high key lst)
	       (log2 (len (slice low high lst)))))
  :instructions (:promote (:casesplit (< high low)) :bash :bash))

(defthm log2-bs-count-calls-relation-corollary
  (implies (and (acl2-numberp key)
		(number-listp lst))
	   (<= (bs-count-calls 0 (1- (len lst)) key lst)
	       (log2 (len lst))))
   :instructions (:promote (:casesplit (not lst)) :bash
                                (:in-theory (disable log2-bs-count-calls-relation))
                                (:use (:instance log2-bs-count-calls-relation (low 0)
                                                 (high (1- (len lst)))))
                                :bash))

;; Note that the maximum number of calls is when the item is not in the list.

(defthmd recursiveBS-helper-count-calls-bs-count-calls
  ;; This characterizes the number of recursive calls made by recursiveBS-helper
  (implies (acl2-numberp calls)
	   (equal (rbsh-calls (recursiveBS-helper key lst low mid high calls))
	          (+ calls (bs-count-calls low high key lst)))))

;; Now define log2 and show that recursivebs-helper makes log2 calls.

(defthmd recursiveBS-helper-count-calls
  (implies (and (natp low)
		(integerp high)
		(number-listp lst)
		(acl2-numberp key)
		(< high (len lst))
		(acl2-numberp calls)
		)
	   (<= (rbsh-calls (recursiveBS-helper key lst low mid high calls))
	       (+ calls (log2 (len (slice low high lst))))))
  :hints (("Goal" :do-not-induct t
	          :in-theory (enable recursivebs-helper-count-calls-bs-count-calls))))

(defthmd recursiveBS-helper-count-calls-corollary
  ;; This is a key lemma.  It shows that the number of recursive calls is bounded by
  ;; log2 of the length of the list.
  (implies (and (number-listp lst)
		(acl2-numberp key)
		)
	   (<= (rbsh-calls (recursiveBS-helper key lst 0 mid (1- (len lst)) 0))
	       (log2 (len lst))))
  :hints (("Goal" :do-not-induct t
                  :in-theory (enable recursivebs-helper-count-calls-bs-count-calls))))

;; BINARYSEARCH LOGARITHMIC

;; >> Can I redo this so that it's parameterized by the code rather than 
;;    specific to BS. 


; (defun binarysearch (key lst)
;   ;; The 2 lead assignments take 7 steps.  The return takes 2.
;   `(seq (assign (var low) (lit . 0))
; 	(seq (assign (var high) (- (len ,lst) (lit . 1)))
; 	     (seq ,(binarysearch-while key lst)
; 		  (return (lit . -1))))))

(defun-sk binarysearch-logarithmic-def1 (c n0 key lst vars count)
  (forall (n)
	  (implies (and (equal n (len (lookup (param1 lst) vars)))
			(<= n0 n))
		   (mv-let (run-stat run-vars run-steps)
			   (run (binarysearch key lst) 'ok vars 0 count)
			   (declare (ignore run-stat run-vars))
			   (and (<= 0 run-steps)
				(<= run-steps (* c (log2 n))))))))

(defun-sk binarysearch-logarithmic-def2 (key lst vars count)
  (exists (c n0)
	  (and (posp c)
	       (posp n0)
	       (binarysearch-logarithmic-def1 c n0 key lst vars count))))

(defthm log2-posp
  (implies (posp n)
	   (posp (log2 n)))
  :rule-classes (:type-prescription :rewrite))

(defthm less-equal-kludge
  (implies (and (<= rbsh lg2-len)
		(natp rbsh)
		(posp lg2-len)
		(natp n)
		(<= n 25))
	   (<= (+ n (* 26 rbsh))
	       (* 51 lg2-len))))

(defthm binarysearch-logarithmic
  (let ((keyval (lookup (param1 key) vars))
	(lstval (lookup (param1 lst) vars)))
    (implies (and (varp lst)
		  (true-listp lstval)
		  (varp key)
		  (not (equal (param1 key) 'mid))
		  (not (equal (param1 key) 'low))
		  (not (equal (param1 key) 'high))
		  (acl2-numberp keyval)
		  (not (equal (param1 lst) 'mid))
		  (not (equal (param1 lst) 'low))
		  (not (equal (param1 lst) 'high))
		  (number-listp (lookup (cadr lst) vars))
		  (sorted (lookup (cadr lst) vars))
		  (integerp count)
		  (not (timedoutp (run-status (run (binarysearch key lst) 'ok vars 0 count))))
		  )
	     (binarysearch-logarithmic-def2 key lst vars count)))
   :INSTRUCTIONS
   (:EXPAND :PROMOTE (:IN-THEORY (DISABLE BINARYSEARCH))
            (:CASESPLIT (NOT (LOOKUP (CADR LST) VARS)))
            (:REWRITE BINARYSEARCH-LOGARITHMIC-DEF2-SUFF ((C 51) (N0 26)))
            (:REWRITE BINARYSEARCH-LOGARITHMIC-DEF1)
            :BASH
            (:REWRITE BINARYSEARCH-LOGARITHMIC-DEF2-SUFF ((C 51) (N0 26)))
            (:REWRITE BINARYSEARCH-LOGARITHMIC-DEF1) :BASH (:DIVE 1 1)
            (:REWRITE BINARYSEARCH-CORRECTNESS-LEMMA-STEPS-COROLLARY ((STEPS 0)))
            :TOP :BASH :S :S :S :S :BASH (:DIVE 1 2)
            (:REWRITE BINARYSEARCH-CORRECTNESS-LEMMA-STEPS-COROLLARY ((STEPS 0)))
            :TOP :BASH (:DIVE 1)
            (:IN-THEORY (ENABLE RECURSIVEBS-HELPER-COUNT-CALLS-COROLLARY
                                RECURSIVEBS-HELPER-CALLS4-COROLLARY2))
            (:REWRITE LESS-EQUAL-KLUDGE) (:DIVE 1)
            (:REWRITE RECURSIVEBS-HELPER-COUNT-CALLS-COROLLARY)
            :BASH :BASH :S :S (:RETAIN 21) (:DIVE 1) (:EXPAND T) :EXPAND :TOP
            (:PROVE :HINTS (("Goal" :HANDS-OFF RUN))) :BASH))

(defthm binarysearch-logarithmic2
  ;; This is a version of the asymptotic complexity lemmas that assumes
  ;; that the key and list are passed in specific variables.  That's not
  ;; necessary, but eliminates a bunch of flaky hyps. 
  (let ((keyval (lookup 'key vars))
	(lstval (lookup 'lst vars)))
    (implies (and (acl2-numberp keyval)
		  (number-listp lstval)
		  (sorted lstval)
		  (integerp count)
		  (not (timedoutp (run-status (run (binarysearch '(var key) '(var lst)) 'ok vars 0 count))))
		  )
	     (binarysearch-logarithmic-def2 '(var key) '(var lst) vars count)))
  :INSTRUCTIONS (:EXPAND :PROMOTE (:REWRITE BINARYSEARCH-LOGARITHMIC) :BASH :S :S))


;----------------------------------------------------------------------

(defun binarysearch2 ()
  ;; This version assumes that binarysearch uses two explicit
  ;; variables to store the key and list.
  (binarysearch '(var key) '(var lst)))

(defun-sk function-logarithmic1 (program log-of c n0 vars count)
  ;; This says that program (which is just a literal) can be run
  ;; against the variable-alist vars with count.  It says that 
  ;; the number of steps taken to run the program are logarithmic
  ;; in the size of parameter log-of.  Params c and n0 are the two
  ;; variables of the definition of asymptotic complexity.
  (forall (n)
	  (implies (and (equal n (len log-of))
			(<= n0 n))
		   (mv-let (run-stat run-vars run-steps)
			   (run program 'ok vars 0 count)
			   (declare (ignore run-stat run-vars))
			   (and (<= 0 run-steps)
				(<= run-steps (* c (log2 n))))))))

(defun-sk function-logarithmic2 (program log-of vars count)
  (exists (c n0)
	  (and (posp c)
	       (posp n0)
	       (function-logarithmic1 program log-of c n0 vars count))))


(defun binarysearch2-logarithmic (vars count)
  (function-logarithmic2 (binarysearch2) (lookup 'lst vars) vars count))

(defthm binarysearch2-logarithmic-lemma
  (let ((keyval (lookup 'key vars))
	(lstval (lookup 'lst vars)))
    (implies (and (acl2-numberp keyval)
		  (number-listp lstval)
		  (sorted lstval)
		  (integerp count)
		  (not (timedoutp (run-status (run (binarysearch '(var key) '(var lst)) 'ok vars 0 count))))
		  )
	     (binarysearch2-logarithmic vars count)))
  :INSTRUCTIONS (:expand :promote :x-dumb :expand (:rewrite function-logarithmic2-suff ((c 51) (n0 26)))
		 (:in-theory (disable binarysearch)) (:rewrite function-logarithmic1) :expand
		 :promote (:dive 3) :expand :expand (:in-theory (disable binarysearch (binarysearch)))
		 :top (:s :in-theory (theory 'minimal-theory))
		 (:= (binarysearch2) (binarysearch '(var key) '(var lst)) t)
		 (:bash ("goal" :hands-off binarysearch)) (:dive 1 1)
		 (:rewrite binarysearch-correctness-lemma-steps-corollary ((steps 0)))
		 :top :bash :s :s :s :s :bash (:dive 1 2)
		 (:rewrite binarysearch-correctness-lemma-steps-corollary ((steps 0))) :top
		 (:claim
		  (equal (mv-nth 4
				 (recursivebs-helper (lookup 'key vars)
						     (lookup 'lst vars)
						     0 nil (+ -1 (len (lookup 'lst vars)))
						     0))
			 (bs-count-calls 0 (+ -1 (len (lookup 'lst vars)))
					 (lookup 'key vars)
					 (lookup 'lst vars)))
		  t)
		 :bash (:dv 1) (:rewrite recursivebs-helper-count-calls-bs-count-calls)
		 :top :s :s :s :s :s :bash (:dv 1) :x :top :s))


