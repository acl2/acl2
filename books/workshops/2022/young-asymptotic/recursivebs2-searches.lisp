; complexity-of-linear-search.lsp                     William D. Young
;; This establishes that the function recursiveBS2 correctly performs
;; search.  I'd like to say that it performs binary search, but am not
;; sure how I'd specify that independent of the definition. 

(in-package "ACL2")
(include-book "complexity-of-binary-search")

(set-irrelevant-formals-ok t)

;; CASE1: (not (member-equal key lst))

(defthm flr-lessp2
  (implies (not (zp x))
	   (<= (flr x 2) x))
  :rule-classes (:linear)
  :hints (("Goal" :in-theory (enable flr))))

(defthm flr-less-eq-kludge
  (implies (and (natp low)
		(natp high)
		(<= low high))
	   (<= LOW (FLR (+ HIGH LOW) 2)))
  :rule-classes :linear
  :hints (("goal" :in-theory (enable flr))))

(defthm not-member-equal-sub-slice
  (implies (and (member-equal key (slice low1 high lst))
		(<= low low1)
		(natp low)
		(natp high)
		(natp low1))
	   (member-equal key (slice low high lst)))
  :hints (("Goal" :use (:instance not-member-equal-slice (mid low1)))))

(defthm member-equal-nth-slice
  (implies (and (natp low)
		(natp high)
		(natp k)
		(< high (len lst))
		(<= low k)
		(<= k high))
	   (member-equal (nth k lst)
			 (slice low high lst))))

(defthm member-equal-mid-slice
  (implies (and (natp low)
		(natp high)
		(< low (len lst))
		(<= low high)
		(< high (len lst))
		(number-listp lst))
	   (member-equal (nth (flr (+ high low) 2) lst)
			 (slice low high lst)))
  :INSTRUCTIONS (:PROMOTE (:USE (:INSTANCE MEMBER-EQUAL-NTH-SLICE (K (FLR (+ HIGH LOW) 2))))
			  :PROMOTE (:IN-THEORY (DISABLE MEMBER-EQUAL-NTH-SLICE))
			  (:DEMOTE 1) (:DIVE 1 1) (:= T) :TOP :S))

(defthm recursiveBS2-helper-searches1
  (implies (and (natp low)
		(natp high)
		(< low (len lst))
		(<= low high)
		(< high (len lst))
		(acl2-numberp key)
		(number-listp lst)
		(not (member-equal key (slice low high lst))))
	   (equal (recursiveBS2-helper key lst low high)
		  -1))
  :hints (("goal" :induct (recursiveBS2-helper key lst low high))))

(defthm number-listp-true-listp2
  (implies (number-listp lst)
	   (true-listp lst))
  :rule-classes :forward-chaining)

(defthm non-empty-true-listp-len
  (implies (and (true-listp lst)
		lst)
	   (< 0 (len lst)))
  :rule-classes :linear)

(defthm recursiveBS2-searches1-case1
  (implies (and (not (member-equal key lst))
		(acl2-numberp key)
		(number-listp lst)
		(not lst))
	   (equal (recursiveBS2 key lst) -1)))

(defthm recursiveBS2-searches1-case2
  (implies (and (not (member-equal key lst))
		(acl2-numberp key)
		(number-listp lst)
		lst)
	   (equal (recursiveBS2 key lst) -1))
  :instructions (:bash (:dv 1)
		       (:rewrite recursivebs2-helper-searches1)
		       :bash :bash :bash :bash (:dive 1 2)
		       (:rewrite slice-whole-list ((low 0)))
		       :top :s))

(defthm recursiveBS2-searches1
  (implies (and (not (member-equal key lst))
		(acl2-numberp key)
		(number-listp lst))
	   (equal (recursiveBS2 key lst) -1))
  :hints (("Goal" :cases (lst))))

;; CASE2: (member-equal key lst)

(defthm flr-high-kludge
  (implies (and (equal (len lst) (+ 1 (flr (+ high low) 2)))
		(natp low)
	        (natp high)
		(<= low high)
		(< high (len lst))
		)
	   (equal (flr (+ high low) 2)
		  high))
  :hints (("Goal" :in-theory (enable flr))))

(defthm member-equal-slice-upper2
  (implies (and (< (nth (flr (+ high low) 2) lst) key)
		(natp low)
		(natp high)
		(<= low high)
		(< high (len lst))
		(acl2-numberp key)
		(number-listp lst)
		(sorted lst)
		(member-equal key (slice low high lst)))
	   (member-equal key (slice (+ 1 (flr (+ high low) 2)) high lst)))
  :INSTRUCTIONS ((:USE (:INSTANCE SORTED-IN-UPPER
				  (MID (FLR (+ HIGH LOW) 2))))
		 :PROMOTE (:DEMOTE 1) (:DIVE 1 1) (:= T) :TOP :S))

(defthm lessp-high-key
  (implies (and (< (nth mid lst) key)
		(<= high mid)
		(natp low)
		(natp high)
		(natp mid)
		(< mid (len lst))
		(< high (len lst))
		(acl2-numberp key)
		(number-listp lst)
		(sorted lst)
		)
	   (< (nth high lst) key))
  :rule-classes :linear)

(defthm not-in-sorted-list3
  (implies (and (<(nth mid lst) key)
		(<= high mid)
		(natp low)
		(natp high)
		(natp mid)
		(< mid (len lst))
		(<= low high)
		(< high (len lst))
		(acl2-numberp key)
		(number-listp lst)
		(sorted lst))
	   (not (member-equal key (slice low high lst)))))

(defthm recursiveBS2-helper-searches2
  (implies (and (natp low)
		(natp high)
		(< low (len lst))
		(<= low high)
		(< high (len lst))
		(acl2-numberp key)
		(number-listp lst)
		(sorted lst)
		(member-equal key (slice low high lst)))
	   (let ((index (recursiveBS2-helper key lst low high)))
	     (equal (nth index lst) key)))
  :hints (("goal" :induct (recursiveBS2-helper key lst low high))
          ("Subgoal *1/4" :use (:instance not-in-sorted-list3 (mid (flr (+ high low) 2))))))

(defthm recursiveBS2-searches2
  (implies (and (member-equal key lst)
		(acl2-numberp key)
		(number-listp lst)
		(sorted lst))
	   (let ((index (recursiveBS2 key lst)))
	     (equal (nth index lst) key)))
  :instructions (:bash (:dv 1)
		       (:rewrite recursivebs2-helper-searches2)
		       :top
		       :s :bash :bash :bash :bash (:dive 2)
		       (:rewrite slice-whole-list ((low 0)))
		       :top :s))

(defthm recursiveBS2-searches
  ;; This is the key lemma.  It shows that recursiveBS2 searches 
  ;; for key in lst. It returns -1 if the key is not present and
  ;; returns an index of key if it is.  As is characteristic of
  ;; binary search, there are no guarantees that the index is any
  ;; specific instance of key in lst.  
  (implies (and (acl2-numberp key)
		(number-listp lst)
		(sorted lst))
	   (let ((index (recursiveBS2 key lst)))
	     (and (implies (member-equal key lst)
			   (equal (nth index lst) key))
		  (implies (not (member-equal key lst))
			   (equal index -1)))))
  :hints (("Goal" :in-theory (disable recursiveBS2))))
