(in-package "DM")

(local (include-book "rtl/rel11/lib/top" :dir :system))

(include-book "actions")

;; Given a subgroup h of a quotient group g/n, we construct a corresponding subgroup (lift h n g) of g.
;; Its element list is constructed by appending the elements of h:

(defund append-elts (h)
  (append-list (elts h)))

(defthm car-append-elts
  (implies (and (normalp n g)
                (subgroupp h (quotient g n)))
	   (and (consp (append-elts h))
	        (equal (car (append-elts h))
		       (e g))))
  :hints (("Goal" :in-theory (e/d (e append-elts) (non-nil-elts))
                  :expand ((APPEND-LIST (CAR H))
		           (APPEND (CAR (CAR H)) (APPEND-LIST (CDR (CAR H)))))
		  :use (non-nil-elts in-e-g order-pos
		        (:instance subgroup-e (g (quotient g n)))
		        (:instance car-qe (h n))))))

;; Move to lists.lisp:

(defthmd sublistp-append-list
  (implies (and (sublistp l m)
                (sublistp (append-list m) n))
           (sublistp (append-list l) n)))

(defthmd sublistp-dlistp-list
  (implies (and (dlistp-list m)
                (sublistp l m))
	   (dlistp-list l)))

(local-defthm sublistp-append-elts
  (implies (and (normalp n g)
                (subgroupp h (quotient g n)))
	   (sublistp (append-elts h) (elts g)))
  :hints (("Goal" :in-theory (enable append-elts)
                  :use (sublistp-subgroup-lcosets
                        (:instance sublistp-append-list (l (elts h)) (m (lcosets n g)) (n (elts g)))
                        (:instance sublistp-lcosets-elts (h n))))))

(defthm dlistp-append-elts
  (implies (and (normalp n g)
                (subgroupp h (quotient g n)))
	   (dlistp (append-elts h)))
  :hints (("Goal" :in-theory (enable append-elts)
                  :use (sublistp-subgroup-lcosets
                        (:instance disjointp-pairwise-sublistp (l (elts h)) (m (lcosets n g)))
			(:instance sublistp-dlistp-list (l (elts h)) (m (lcosets n g)))
			(:instance dlistp-append-list (l (elts h)))))))

(defthm member-append
  (implies (or (member-equal x l) (member-equal x m))
           (member-equal x (append l m))))

(local-defthmd member-append-elts-1
  (implies (and (normalp n g)
                (sublistp l (lcosets n g))
		(in x g)
		(member-equal (lcoset x n g) l))
	   (member x (append-list l)))
  :hints (("Subgoal *1/2" :use ((:instance member-self-lcoset (h n))))))

(defthmd member-append-iff
  (iff (or (member-equal x l) (member-equal x m))
       (member-equal x (append l m))))

(local-defthmd member-append-elts-2
  (implies (and (normalp n g)
                (sublistp l (lcosets n g))
		(in x g)
		(member x (append-list l)))
	   (member-equal (lcoset x n g) l))	   
  :hints (("Subgoal *1/3" :use ((:instance lcosets-cars (c (car l)) (h n))
                                (:instance equal-lcoset (y x) (h n) (x (caar l)))
				(:instance member-append-iff (l (car l)) (m (append-list (cdr l))))))))

(local-defthmd member-append-elts
  (implies (and (normalp n g)
                (subgroupp h (quotient g n))
		(in x g))
           (iff (member x (append-elts h))
	        (member-equal (lcoset x n g) (elts h))))	   
  :hints (("Goal" :in-theory (enable append-elts)
                  :use (sublistp-subgroup-lcosets
		        (:instance member-append-elts-1 (l (elts h)))
                        (:instance member-append-elts-2 (l (elts h)))))))

(local-defthmd append-elts-closed-1
  (implies (and (normalp n g)
                (subgroupp h (quotient g n))
		(member-equal x (append-elts h))
		(member-equal y (append-elts h)))
           (in (qop (lcoset x n g) (lcoset y n g) n g) h))
  :hints (("Goal" :in-theory (disable lcoset-member-lcoset group-closure)
                  :use (member-append-elts sublistp-subgroup-lcosets sublistp-append-elts
                        (:instance member-append-elts (x y))
			(:instance member-self-lcoset (h n))
			(:instance member-self-lcoset (h n) (x y))
			(:instance group-closure (g h) (x (lcoset x n g)) (y (lcoset y n g)))))))

(defthm append-elts-closed
  (implies (and (normalp n g)
                (subgroupp h (quotient g n))
		(member-equal x (append-elts h))
		(member-equal y (append-elts h)))
           (member-equal (op x y g) (append-elts h)))
  :hints (("Goal" :use (append-elts-closed-1 member-append-elts sublistp-append-elts
                        (:instance member-append-elts (x y))
                        (:instance member-append-elts (x (op x y g)))
			(:instance op-quotient-lcoset (h n) (x (lcoset x n g)) (y (lcoset y n g)) (a x) (b y))))))

(local-defthmd append-elts-inv-1
  (implies (and (normalp n g)
                (subgroupp h (quotient g n))
		(member-equal x (append-elts h)))
           (in (qinv (lcoset x n g) n g) h))
  :hints (("Goal" :in-theory (disable lcoset-member-lcoset group-left-inverse)
                  :use (member-append-elts sublistp-subgroup-lcosets sublistp-append-elts
			(:instance member-self-lcoset (h n))
			(:instance group-left-inverse (g h) (x (lcoset x n g)))))))

(defthm append-elts-inv
  (implies (and (normalp n g)
                (subgroupp h (quotient g n))
		(member-equal x (append-elts h)))
           (member-equal (inv x g) (append-elts h)))
  :hints (("Goal" :use (append-elts-inv-1 member-append-elts sublistp-append-elts
                        (:instance member-append-elts (x (inv x g)))
			(:instance inv-quotient-lcoset (h n) (x (lcoset x n g)) (a x))))))

(defthm append-elts-non-nil
  (implies (and (normalp n g)
                (subgroupp h (quotient g n)))
	   (not (member-equal () (append-elts h))))
  :hints (("Goal" :in-theory (disable non-nil-elts)
                  :use (non-nil-elts sublistp-append-elts))))                        

(local (in-theory (enable sublistp-append-elts)))

(defsubgroup lift (h n) g
  (and (normalp n g)
       (subgroupp h (quotient g n)))
  (append-elts h))

(defthmd car-elts-h
  (implies (and (normalp n g)
                (subgroupp h (quotient g n)))
	   (equal (e h) (lcoset (e g) n g))))

(local-defthmd sublistp-n-append-elts-1
  (implies (and (normalp n g)
                (subgroupp h (quotient g n))
		(sublistp l (elts n)))
	   (sublistp l (lcoset (e g) n g)))
  :hints (("Subgoal *1/2" :use ((:instance member-lcoset-iff (h n) (y (car l)) (x (e g)))))))

(local-defthmd sublistp-n-append-elts-2
  (implies (and (normalp n g)
                (subgroupp h (quotient g n)))
	   (sublistp (elts n) (lcoset (e g) n g)))
  :hints (("Goal" :in-theory (enable sublistp-n-append-elts-1))))

(defthmd sublistp-append-2
  (implies (sublistp l m)
           (sublistp l (append m n))))

(defthmd sublistp-n-append-elts
  (implies (and (normalp n g)
                (subgroupp h (quotient g n)))
	   (sublistp (elts n) (append-elts h)))
  :hints (("Goal" :in-theory (e/d (e append-elts) (QUOTIENT-E))
                  :use (sublistp-n-append-elts-2 car-elts-h
                        (:instance sublistp-append-2 (l (elts n)) (m (car (elts h))) (n (append-list (cdr (elts h)))))))))

(defthmd lift-subgroup
  (implies (and (normalp n g)
                (subgroupp h (quotient g n)))
	   (subgroupp n (lift h n g)))
  :hints (("Goal" :use (sublistp-n-append-elts
                        (:instance subgroup-subgroup (h n) (k (lift h n g)))))))

(local-defthmd lift-order-1
  (implies (and (normalp n g)
                (subgroupp h (quotient g n))
		(sublistp l (elts h)))
	   (equal (len (append-list l))
		  (* (len l) (order n))))
  :hints (("Subgoal *1/1" :use (sublistp-subgroup-lcosets
                                (:instance lcosets-cars (c (car l)) (h n))
				(:instance len-lcoset (x (caar l)) (h n))))))

(defthmd lift-order
  (implies (and (normalp n g)
                (subgroupp h (quotient g n)))
	   (equal (order (lift h n g))
		  (* (order h) (order n))))
  :hints (("Goal" :use ((:instance lift-order-1 (l (elts h))))
                  :in-theory (enable append-elts))))


;;------------------------------------------------------------------------------------------------------------------

;; Recognizer of powers of an integer greater than 1:

(in-theory (enable divides))

(defun powerp (n p)
  (if (and (natp p) (> p 1) (posp n) (divides p n))
      (powerp (/ n p) p)
    (equal n 1)))

(defun log (n p)
  (if (and (natp p) (> p 1) (posp n) (integerp (/ n p)))
      (1+ (log (/ n p) p))
    0))

(defthmd powerp-log
  (implies (and (natp p) (> p 1) (powerp n p))
           (equal (expt p (log n p)) n)))

(defthm powerp*p
  (implies (and (natp p) (> p 1) (powerp n p))
           (powerp (* p n) p))
  :hints (("Goal" :in-theory (enable powerp))))

(defthm powerp-power
  (implies (and (natp p) (> p 1) (natp n))
           (powerp (expt p n) p))
  :hints (("Goal" :induct (fact n))))

(local-defthmd divides-power-1
  (implies (and (primep p) (posp k) (posp m) (divides m (expt p k)))
           (or (divides p m)
	       (divides m (expt p (1- k)))))
  :hints (("Goal" :use ((:instance euclid (a m) (b (/ (expt p k) m)))))))

(local-defun divides-power-induct (p m k)
  (if (and (primep p) (posp m) (posp k))
      (list (divides-power-induct p m (1- k))
            (divides-power-induct p (/ m p) (1- k)))
    ()))

(defthmd divides-power
  (implies (and (primep p) (natp k) (posp m) (divides m (expt p k)))
           (powerp m p))	   
  :hints (("Goal" :induct (divides-power-induct p m k))
          ("Subgoal *1/1" :use (divides-power-1))))

(defthmd powerp-divides
  (implies (and (primep p) (powerp n p) (posp m) (divides m n))
           (powerp m p))
  :hints (("Goal" :use (powerp-log (:instance divides-power (k (log n p)))))))

;; Recognizer of p-groups:

(defund p-groupp (g p)
  (and (primep p)
       (groupp g)
       (powerp (order g) p)))

(defthmd p-groupp-ord-powerp
  (implies (and (p-groupp g p)
		(in x g))
	   (powerp (ord x g) p))
  :hints (("Goal" :in-theory (enable p-groupp)
                  :use (ord-divides-order (:instance powerp-divides (m (ord x g)) (n (order g)))))))


;;------------------------------------------------------------------------------------------------------------------

;; If h is a p-subgroup of g and p divides (subgroup-index p (normalizer h g)), then h is a proper
;; subgroup of a p-subgroup of g, which may be constructed by first applying cauchy's theorem
;; to construct a subgroup of (quotient (normalizer h g) h) or order p and then lifting it to g:

(defund extend-p-subgroup (h g p)
  (lift (cyclic (elt-of-ord p (quotient (normalizer h g) h))
		(quotient (normalizer h g) h))
	h
	(normalizer h g)))

(local-defthmd order-extend-p-subgroup-1
  (implies (and (subgroupp h g)
		(posp n)
		(elt-of-ord n (quotient (normalizer h g) h)))
           (let ((cyc (cyclic (elt-of-ord n (quotient (normalizer h g) h)) (quotient (normalizer h g) h))))
	     (and (subgroupp cyc (quotient (normalizer h g) h))
	          (equal (order cyc) n))))
  :hints (("Goal" :use (normalizer-normp (:instance elt-of-ord-ord (g (quotient (normalizer h g) h)))))))

(defthmd order-extend-p-subgroup
  (implies (and (subgroupp h g)
		(posp n)
		(elt-of-ord n (quotient (normalizer h g) h)))
	   (let ((k (extend-p-subgroup h g n)))
	     (and (subgroupp h k)
	          (subgroupp k g)
		  (equal (order k) (* n (order h))))))
  :hints (("Goal" :in-theory (e/d (extend-p-subgroup) (subgroupp-lift))
                  :use (order-extend-p-subgroup-1 normalizer-normp
		        (:instance subgroupp-transitive (h (extend-p-subgroup h g n)) (k (normalizer h g)))
                        (:instance lift-subgroup (g (normalizer h g))
			                         (n h)
			                         (h (cyclic (elt-of-ord n (quotient (normalizer h g) h)) (quotient (normalizer h g) h))))
                        (:instance subgroupp-lift (g (normalizer h g))
			                          (n h)
			                          (h (cyclic (elt-of-ord n (quotient (normalizer h g) h)) (quotient (normalizer h g) h))))
                        (:instance lift-order (g (normalizer h g))
			                      (n h)
			                      (h (cyclic (elt-of-ord n (quotient (normalizer h g) h)) (quotient (normalizer h g) h))))))))


;; We recursively define a p-subgroup m of g such that p does not divide the index of m in its
;; normalizer.  We shall eventually show that p does not divide the index of m in g:

(local-defthmd sylow-measure-decreases
  (implies (and (subgroupp h g) (primep p) (divides p (subgroup-index h (normalizer h g))))
           (and (< 0 (order h))
	        (< (order h) (order g))
	        (< (order h) (order (extend-p-subgroup h g p)))))
  :hints (("Goal" :nonlinearp t
		  :use (normalizer-normp
                        (:instance order-pos (g h))
			(:instance order-extend-p-subgroup (n p))
                        (:instance cauchy (g (quotient (normalizer h g) h)))
			(:instance subgroup-order-<= (h (extend-p-subgroup h g p)))))))

(defun sylow-subgroup-aux (h g p)
  (declare (xargs :measure (nfix (- (order g) (order h))) :hints (("Goal" :use (sylow-measure-decreases)))))
  (if (and (subgroupp h g) (primep p) (divides p (subgroup-index h (normalizer h g))))
      (sylow-subgroup-aux (extend-p-subgroup h g p) g p)
    h))

(defund sylow-subgroup(g p)
  (sylow-subgroup-aux (trivial-subgroup g) g p))

(local-defthmd index-sylow-subgroup-aux
  (implies (and (groupp g)
                (subgroupp h g)
		(p-groupp h p)
                (primep p))
	   (let ((m (sylow-subgroup-aux h g p)))
	     (and (subgroupp m g)
		  (p-groupp m p)
		  (not (divides p (subgroup-index m (normalizer m g)))))))
  :hints (("Subgoal *1/1" :in-theory (enable p-groupp)
                          :use (normalizer-normp
			        (:instance order-extend-p-subgroup (n p))
                                (:instance cauchy (g (quotient (normalizer h g) h)))
				(:instance powerp*p (n (order h)))))))

(defthm trivial-p-groupp
  (implies (and (groupp g)
                (primep p))
	   (p-groupp (trivial-subgroup g) p))
  :hints (("Goal" :in-theory (enable p-groupp powerp))))

(defthm index-sylow-subgroup
  (implies (and (groupp g)
                (primep p))
	   (let ((m (sylow-subgroup g p)))
	     (and (subgroupp m g)
		  (p-groupp m p)
		  (not (divides p (subgroup-index m (normalizer m g)))))))
  :hints (("Goal" :in-theory (enable sylow-subgroup)
                  :use ((:instance index-sylow-subgroup-aux (h (trivial-subgroup g)))))))


;;------------------------------------------------------------------------------------------------------------------

;; Consider the action of g on the list of conjugates of m.  This action has one orbit, the order of
;; which is the index of the normalizer of m.  We shall show that this index is congruent to 1 mod p,
;; and therefore not divisible by p.

;; To this end, consider the restriction of this action to some p-subgroup h of g.  An orbit of an 
;; element of the domain is a singleton iff h is a subgroup of that element:

(defthmd equal-indices-1
  (implies (and (subgroupp m g)
		(in c (conj-sub-act m g)))
	   (equal (order (normalizer c g))
	          (order (normalizer m g))))
  :hints (("Goal" :use (normalizer-conj-sub
			(:instance conjs-sub-conjer (h m) (k c))
			(:instance subgroupp-normalizer (h m))			
			(:instance order-conj-sub (h (normalizer m g)) (a (conjer-sub c m g)))))))

(defthmd equal-indices-2
  (implies (and (subgroupp m g)
		(in c (conj-sub-act m g)))
           (equal (* (len (car c))
                     (len (lcosets c (normalizer c g))))
                  (* (len (car c))
                     (len (lcosets m (normalizer m g))))))
  :hints (("goal" :use (equal-indices-1
			(:instance conjs-sub-conjer (h m) (k c))
			(:instance order-conj-sub (h m) (a (conjer-sub c m g)))			
                        (:instance subgroup-of-normalizer (h c))
                        (:instance subgroup-of-normalizer (h m))			
			(:instance lagrange (h c) (g (normalizer c g)))
			(:instance lagrange (h m) (g (normalizer m g)))))))

(defthmd equal-indices
  (implies (and (subgroupp m g)
		(in c (conj-sub-act m g)))
	   (equal (subgroup-index c (normalizer c g))
	          (subgroup-index m (normalizer m g))))
  :hints (("Goal" :in-theory (enable subgroup-index)
                  :use (equal-indices-1 equal-indices-2
                        (:instance subgroup-of-normalizer (h c))
                        (:instance subgroup-of-normalizer (h m))			
			(:instance conjs-sub-conjer (h m) (k c))
			(:instance order-pos (g c))))))

(defthmd in-normalizer-in-c-1
  (implies (and (subgroupp m g)
		(in c (conj-sub-act m g))
	        (in x c))
	   (in x (normalizer c g)))
  :hints (("Goal" :use ((:instance subgroup-of-normalizer (h c))))))

(defthmd in-normalizer-in-c-2
  (implies (and (subgroupp h g)
		(primep p)		
		(p-groupp h p)
		(in x h)
		(in c (conj-sub-act m g))
		(in x h)
	        (not (in x c)))
	    (powerp (ord x g) p))
  :hints (("Goal" :in-theory (enable p-groupp)
                  :use ((:instance ord-divides-order (g h))
                        (:instance powerp-divides (m (ord x h)) (n (order h)))))))

(defthmd in-normalizer-in-c-3
  (implies (and (subgroupp m g)
		(primep p)
		(p-groupp m p)
		(subgroupp h g)
		(p-groupp h p)
		(in c (conj-sub-act m g))
		(in x h)
	        (in x (normalizer c g))
	        (not (in x c)))
	    (powerp (ord (lcoset x c (normalizer c g)) (quotient (normalizer c g) c)) p))
  :hints (("Goal" :use (in-normalizer-in-c-2
			(:instance normalizer-normp (h c))
			(:instance subgroupp-normalizer (h c))
			(:instance powerp-divides (m (ord (lcoset x c (normalizer c g)) (quotient (normalizer c g) c))) (n (ord x g)))
			(:instance ord-lcoset-divides (a x) (x (lcoset x c (normalizer c g))) (h c) (g (normalizer c g)))))))

(defthmd in-normalizer-in-c-4
  (implies (and (subgroupp m g)
		(primep p)
		(p-groupp m p)
		(subgroupp h g)
		(p-groupp h p)
		(in c (conj-sub-act m g))
		(in x h)
	        (in x (normalizer c g))
	        (not (in x c)))
	    (not (equal (ord (lcoset x c (normalizer c g)) (quotient (normalizer c g) c))
	                1)))
  :hints (("Goal" :expand ((power (lcoset x c (normalizer c g)) 1 (quotient (normalizer c G) C)))
                  :use ((:instance normalizer-normp (h c))
			(:instance equal-lcoset-lcoset-e (h c) (g (normalizer c g)))
			(:instance ord-power (a (lcoset x c (normalizer c g))) (g (quotient (normalizer c g) c)))
			(:instance subgroupp-normalizer (h c))))))

(defthmd in-normalizer-in-c-5
  (implies (and (subgroupp m g)
		(primep p)
		(p-groupp m p)
		(subgroupp h g)
		(p-groupp h p)
		(in c (conj-sub-act m g))
		(in x h)
	        (in x (normalizer c g))
	        (not (in x c)))
	    (divides p (ord (lcoset x c (normalizer c g)) (quotient (normalizer c g) c))))
  :hints (("Goal" :use (in-normalizer-in-c-3 in-normalizer-in-c-4
			(:instance normalizer-normp (h c))
			(:instance subgroupp-normalizer (h c))
			(:instance powerp-divides (m (ord (lcoset x c (normalizer c g)) (quotient (normalizer c g) c))) (n (ord x g)))))))

(defthmd in-normalizer-in-c-6
  (implies (and (subgroupp m g)
		(primep p)
		(p-groupp m p)
		(subgroupp h g)
		(p-groupp h p)
		(in c (conj-sub-act m g))
		(in x h)
	        (in x (normalizer c g))
	        (not (in x c)))
           (divides (ord (lcoset x c (normalizer c g)) (quotient (normalizer c g) c))
	                  (order (quotient (normalizer c g) c))))
  :hints (("Goal" :use ((:instance normalizer-normp (h c))
			(:instance subgroupp-normalizer (h c))
			(:instance ord-divides-order (x (lcoset x c (normalizer c g))) (g (quotient (normalizer c g) c)))))))

(defthmd in-normalizer-in-c
  (implies (and (subgroupp m g)
		(primep p)
		(p-groupp m p)
		(not (divides p (subgroup-index m (normalizer m g))))
		(subgroupp h g)
		(p-groupp h p)
		(in c (conj-sub-act m g))
		(in x h)
	        (in x (normalizer c g)))
	   (in x c))
  :hints (("Goal" :in-theory (disable divides)
                  :use (in-normalizer-in-c-5 in-normalizer-in-c-6 equal-indices
		        (:instance divides-transitive (x p)
			                              (y (ord (lcoset x c (normalizer c g)) (quotient (normalizer c g) c)))
	                                              (z (order (quotient (normalizer c g) c))))
                        (:instance normalizer-normp (h c))
		        (:instance order-quotient (h c) (g (normalizer c g)))))))

(defthmd member-stab-subaction-1
  (implies (and (subgroupp m g)
		(subgroupp h g)
		(in c (conj-sub-act m g))
		(in x h))
	   (iff (in x (stabilizer c (subaction (conj-sub-act m g) g h) h))
	        (in x (normalizer c g))))
  :hints (("Goal" :in-theory (enable normalizer)
                  :use (member-conjs-sub-self
		        (:instance member-stab-elts (a (subaction (conj-sub-act m g) g h)) (g h) (s c))
                        (:instance member-stab-elts (a (conj-sub-act c g)) (s c))
                        (:instance member-stab-elts (a (conj-sub-act m g)) (s c))
			(:instance permp-conjs-sub (h m) (x (conjer-sub c h g)))
			(:instance conjs-sub-conjer (k c))))))

(defthmd member-stab-subaction
  (implies (and (subgroupp m g)
		(primep p)
		(p-groupp m p)
		(not (divides p (subgroup-index m (normalizer m g))))
		(subgroupp h g)
		(p-groupp h p)
		(in c (conj-sub-act m g))
		(in x h))
	   (iff (in x (stabilizer c (subaction (conj-sub-act m g) g h) h))
	        (in x c)))
  :hints (("Goal" :use (equal-indices in-normalizer-in-c member-stab-subaction-1
		       (:instance normalizer-normp (h c))))))

(defthmd orbit-subaction-len-1-1
  (implies (and (subgroupp m g)
		(primep p)
		(p-groupp m p)
		(not (divides p (subgroup-index m (normalizer m g))))
		(subgroupp h g)
		(p-groupp h p)
		(in c (conj-sub-act m g)))
	   (iff (equal (len (orbit c (subaction (conj-sub-act m g) g h) h)) 1)
	        (equal (order h)
		       (order (stabilizer c (subaction (conj-sub-act m g) g h) h)))))
  :hints (("Goal" :use ((:instance stabilizer-orbit (a (subaction (conj-sub-act m g) g h)) (s c) (g h))
                        (:instance order-pos (g h))))))

(defthmd orbit-subaction-len-1-2
  (implies (and (subgroupp m g)
		(primep p)
		(p-groupp m p)
		(not (divides p (subgroup-index m (normalizer m g))))
		(subgroupp h g)
		(p-groupp h p)
		(in c (conj-sub-act m g)))
	   (iff (equal (order h)
		       (order (stabilizer c (subaction (conj-sub-act m g) g h) h)))
		(sublistp (elts h)
		          (elts (stabilizer c (subaction (conj-sub-act m g) g h) h)))))
  :hints (("Goal" :in-theory (enable permp)
                  :use ((:instance permp-eq-len (l (elts (stabilizer c (subaction (conj-sub-act m g) g h) h))) (m (elts h)))
			(:instance ordp-equal (x (elts (stabilizer c (subaction (conj-sub-act m g) g h) h))) (y (elts h)) (g h))))))

(defthmd orbit-subaction-len-1-3
  (implies (and (subgroupp m g)
		(primep p)
		(p-groupp m p)
		(not (divides p (subgroup-index m (normalizer m g))))
		(subgroupp h g)
		(p-groupp h p)
		(in c (conj-sub-act m g))
	        (sublistp (elts h)
		          (elts (stabilizer c (subaction (conj-sub-act m g) g h) h))))
	   (sublistp (elts h) (elts c)))
  :hints (("Goal" :use ((:instance scex1-lemma (l (elts h)) (m (elts c)))
                        (:instance member-stab-subaction (x (scex1 (elts h) (elts c))))))))

(defthmd orbit-subaction-len-1-4
  (implies (and (subgroupp m g)
		(primep p)
		(p-groupp m p)
		(not (divides p (subgroup-index m (normalizer m g))))
		(subgroupp h g)
		(p-groupp h p)
		(in c (conj-sub-act m g))
	        (sublistp (elts h) (elts c)))
           (sublistp (elts h)
		     (elts (stabilizer c (subaction (conj-sub-act m g) g h) h))))
  :hints (("Goal" :use ((:instance scex1-lemma (l (elts h)) (m (elts (stabilizer c (subaction (conj-sub-act m g) g h) h))))
                        (:instance member-stab-subaction (x (scex1 (elts h) (elts (stabilizer c (subaction (conj-sub-act m g) g h) h)))))))))

(defthmd orbit-subaction-len-1
  (implies (and (subgroupp m g)
		(primep p)
		(p-groupp m p)
		(not (divides p (subgroup-index m (normalizer m g))))
		(subgroupp h g)
		(p-groupp h p)
		(in c (conj-sub-act m g)))
	   (iff (equal (len (orbit c (subaction (conj-sub-act m g) g h) h)) 1)
	        (subgroupp h c)))
  :hints (("Goal" :use (orbit-subaction-len-1-1 orbit-subaction-len-1-2 orbit-subaction-len-1-3 orbit-subaction-len-1-4
                        (:instance subgroup-subgroup (k c))))))

(defthmd orbit-subaction-div-p
  (implies (and (subgroupp m g)
		(primep p)
		(p-groupp m p)
		(not (divides p (subgroup-index m (normalizer m g))))
		(subgroupp h g)
		(p-groupp h p)
		(in c (conj-sub-act m g)))
	   (if (subgroupp h c)
	       (equal (len (orbit c (subaction (conj-sub-act m g) g h) h)) 1)
	     (divides p (len (orbit c (subaction (conj-sub-act m g) g h) h)))))
  :hints (("Goal" :in-theory (enable p-groupp)
                  :use (orbit-subaction-len-1
                        (:instance len-orbit-divides (a (subaction (conj-sub-act m g) g h)) (g h) (s c))
			(:instance powerp-divides (m (len (orbit c (subaction (conj-sub-act m g) g h) h))) (n (order h)))))))


;;------------------------------------------------------------------------------------------------------------------

;; We apply the above result to the case h = m.  By conjs-sub-subgroup, m is a subgroup of exactly 1 conjugate of m,
;; which implies there is exactly 1 orbit of length 1 and all others have length divisible by p:

(defthmd orbit-subaction-m-len-1
  (implies (and (subgroupp m g)
		(primep p)
		(p-groupp m p)
		(not (divides p (subgroup-index m (normalizer m g))))
		(in c (conj-sub-act m g)))
	   (if (equal c (conj-sub m (e g) g))
	       (equal (len (orbit c (subaction (conj-sub-act m g) g m) m)) 1)
	     (divides p (len (orbit c (subaction (conj-sub-act m g) g m) m)))))
  :hints (("Goal" :use ((:instance orbit-subaction-div-p (h m))
                        (:instance conjs-sub-subgroup (h m) (k c))))))

(defthmd len-member-orbits
  (implies (and (subgroupp m g)
		(primep p)
		(p-groupp m p)
		(not (divides p (subgroup-index m (normalizer m g))))
		(member-equal x (orbits (subaction (conj-sub-act m g) g m) m)))
	   (if (member-equal (conj-sub m (e g) g) x)
	       (equal (len x) 1)
	     (divides p (len x))))
  :hints (("Goal" :use ((:instance member-orbits-orbit (a (subaction (conj-sub-act m g) g m)) (g m))
                        (:instance orbit-subaction-m-len-1 (c (car x)))
                        (:instance orbit-subaction-m-len-1 (c (conj-sub m (e g) g)))
			(:instance equal-orbits (r (conj-sub m (e g) g)) (s (car x)) (a (subaction (conj-sub-act m g) g m)) (g m))))))

(defthmd disjointp-pairwise-disjointp-car
  (implies (and (disjointp-pairwise m)
                (sublistp l m)
		(dlistp l)
		(member-equal x (car l)))
	   (not (member-list x (cdr l))))
  :hints (("Goal" :use (disjointp-pairwise-sublistp))))

(defthmd mod-len-orbits-subaction-sublist
  (implies (and (subgroupp m g)
		(primep p)
		(p-groupp m p)
		(not (divides p (subgroup-index m (normalizer m g))))
		(sublistp l (orbits (subaction (conj-sub-act m g) g m) m))
		(dlistp l))
	   (equal (mod (len (append-list l)) p)
	          (if (member-list (conj-sub m (e g) g) l)
		      1
		    0)))
  :hints (("Goal" :induct (len l))
          ("Subgoal *1/2" :in-theory (disable ACL2::|(equal (mod a n) (mod b n))|)
                          :use ((:instance len-member-orbits (x (car l)))
                                (:instance rtl::mod-mult (n p) (m (len (append-list (cdr l)))) (a (/ (len (car l)) p)))))
          ("Subgoal *1/1" :in-theory (disable ACL2::|(equal (mod (+ x y) z) x)| ACL2::|(mod (+ 1 x) y)| ACL2::MOD-X-Y-=-X
	                                      ACL2::|(equal (mod a n) (mod b n))|)
                          :use ((:instance len-member-orbits (x (car l)))
			        (:instance disjointp-pairwise-disjointp-car (m (orbits (subaction (conj-sub-act m g) g m) m))
				                                            (x (conj-sub m (e g) g)))
                                (:instance rtl::mod-mult (n p) (m (len (append-list (cdr l)))) (a (/ (len (car l)) p)))
                                (:instance rtl::mod-mult (n p) (a (/ (len (append-list (cdr l))) p)) (m (len (car l))))))))

(defthmd mod-len-orbits-subaction
  (implies (and (subgroupp m g)
		(primep p)
		(p-groupp m p)
		(not (divides p (subgroup-index m (normalizer m g)))))
	   (equal (mod (len (append-list (orbits (subaction (conj-sub-act m g) g m) m))) p)
	          1))
  :hints (("Goal" :use ((:instance mod-len-orbits-subaction-sublist (l (orbits (subaction (conj-sub-act m g) g m) m)))))))

(defthmd mod-len-conjs-sub
  (implies (and (subgroupp m g)
		(primep p)
		(p-groupp m p)
		(not (divides p (subgroup-index m (normalizer m g)))))
	   (equal (mod (len (conjs-sub m g)) p)
	          1))
  :hints (("Goal" :use (mod-len-orbits-subaction
                        (:instance eq-len-permp (l (append-list (orbits (subaction (conj-sub-act m g) g m) m))) (m (conjs-sub m g)))
                        (:instance append-list-orbits (a (subaction (conj-sub-act m g) g m)) (g m))))))

(defthmd not-divides-p-index-normalizer
  (implies (and (subgroupp m g)
		(primep p)
		(p-groupp m p)
		(not (divides p (subgroup-index m (normalizer m g)))))
	   (not (divides p (subgroup-index (normalizer m g) g))))
  :hints (("Goal" :use (mod-len-conjs-sub
                        (:instance index-normalizer (h m))))))

(defthmd divides-len-conjs-sub
  (implies (and (subgroupp m g)
		(primep p)
		(p-groupp m p)
		(not (divides p (subgroup-index m (normalizer m g)))))
	   (divides (len (conjs-sub m g))
	            (subgroup-index m g)))
  :hints (("Goal" :use ((:instance index-normalizer (h m))
                        (:instance subgroup-of-normalizer (h m))
			(:instance subgroup-index-pos (h (normalizer m g)))
			(:instance subgroup-index-pos (h m) (g (normalizer m g)))
                        (:instance prod-indices (h m) (k (normalizer m g)))))))

(defthmd not-divides-p-index-m
  (implies (and (subgroupp m g)
		(primep p)
		(p-groupp m p)
		(not (divides p (subgroup-index m (normalizer m g)))))
	   (not (divides p (subgroup-index m g))))
  :hints (("Goal" :use (not-divides-p-index-normalizer
                        (:instance subgroup-of-normalizer (h m))
			(:instance euclid (a (subgroup-index m (normalizer m g))) (b (subgroup-index (normalizer m g) g)))
                        (:instance prod-indices (h m) (k (normalizer m g)))))))

(defthmd sylow-1
  (implies (and (groupp g)
		(primep p))
	   (let ((m (sylow-subgroup g p)))
	     (equal (mod (len (conjs-sub m g)) p)
	            1)))
  :hints (("Goal" :use (index-sylow-subgroup
                        (:instance mod-len-conjs-sub (m (sylow-subgroup g p)))))))

(defthmd sylow-2
  (implies (and (groupp g)
		(primep p))
	   (let ((m (sylow-subgroup g p)))
	     (divides (len (conjs-sub m g))
	              (subgroup-index m g))))
  :hints (("Goal" :use (index-sylow-subgroup
                        (:instance divides-len-conjs-sub (m (sylow-subgroup g p)))))))

(defthmd sylow-3
  (implies (and (groupp g)
		(primep p))
	   (not (divides p (subgroup-index (sylow-subgroup g p) g))))
  :hints (("Goal" :use (index-sylow-subgroup
                        (:instance not-divides-p-index-m (m (sylow-subgroup g p)))))))


;;------------------------------------------------------------------------------------------------------------------

;; Another consequence of orbit-subaction-div-p is that every p-subgroup of g is a subgroup of
;; some conjugate of m:

(defun find-supergroup (h l)
  (if (consp l)
      (if (subgroupp h (car l))
          (car l)
	(find-supergroup h (cdr l)))
    ()))

(defthmd find-supergroup-supergroup
  (let ((k (find-supergroup h l)))
    (or (null k)
        (and (member-equal k l)
	     (subgroupp h k)))))

(defthm not-subgroupp-nil
  (not (subgroupp h ()))
  :hints (("Goal" :in-theory (enable subgroupp)
                  :use ((:instance order-pos (g ()))))))

(defthmd not-find-supergroup-not-supergroup
  (implies (and (not (find-supergroup h l))
                (member-equal k l))
	   (not (subgroupp h k))))

(defthmd find-subgroupp-conjs-sub-1
  (implies (and (subgroupp m g)
		(primep p)
		(p-groupp m p)
		(not (divides p (subgroup-index m (normalizer m g))))
		(subgroupp h g)
		(p-groupp h p)
	        (not (find-supergroup h (conjs-sub m g)))
		(in c (conj-sub-act m g)))
	   (divides p (len (orbit c (subaction (conj-sub-act m g) g h) h))))
  :hints (("Goal" :use (orbit-subaction-div-p
                        (:instance not-find-supergroup-not-supergroup (l (conjs-sub m g)) (k c))))))

(defthmd find-subgroupp-conjs-sub-2
  (implies (and (subgroupp m g)
		(primep p)
		(p-groupp m p)
		(not (divides p (subgroup-index m (normalizer m g))))
		(subgroupp h g)
		(p-groupp h p)
	        (not (find-supergroup h (conjs-sub m g)))
		(member-equal x (orbits (subaction (conj-sub-act m g) g h) h)))
	   (divides p (len x)))
  :hints (("Goal" :use ((:instance member-orbits-orbit (a (subaction (conj-sub-act m g) g h)) (g h))
                        (:instance find-subgroupp-conjs-sub-1 (c (car x)))))))

(defthmd find-subgroupp-conjs-sub-3
  (implies (and (subgroupp m g)
		(primep p)
		(p-groupp m p)
		(not (divides p (subgroup-index m (normalizer m g))))
		(subgroupp h g)
		(p-groupp h p)
	        (not (find-supergroup h (conjs-sub m g)))
		(sublistp l (orbits (subaction (conj-sub-act m g) g h) h))
		(dlistp l))
	   (divides p (len (append-list l))))
  :hints (("Goal" :induct (len l))
          ("Subgoal *1/2" :use ((:instance find-subgroupp-conjs-sub-2 (x (car l)))))
          ("Subgoal *1/1" :use ((:instance find-subgroupp-conjs-sub-2 (x (car l)))))))

(defthmd find-subgroupp-conjs-sub-4
  (implies (and (subgroupp m g)
		(primep p)
		(p-groupp m p)
		(not (divides p (subgroup-index m (normalizer m g))))
		(subgroupp h g)
		(p-groupp h p)
	        (not (find-supergroup h (conjs-sub m g))))
	   (divides p (len (append-list (orbits (subaction (conj-sub-act m g) g h) h)))))
  :hints (("Goal" :use ((:instance find-subgroupp-conjs-sub-3 (l (orbits (subaction (conj-sub-act m g) g h) h)))))))

(defthmd not-find-supergroup-divides-p
  (implies (and (subgroupp m g)
		(primep p)
		(p-groupp m p)
		(not (divides p (subgroup-index m (normalizer m g))))
		(subgroupp h g)
		(p-groupp h p)
	        (not (find-supergroup h (conjs-sub m g))))
	   (divides p (len (conjs-sub m g))))
  :hints (("Goal" :use (find-subgroupp-conjs-sub-4
                        (:instance eq-len-permp (l (append-list (orbits (subaction (conj-sub-act m g) g h) h))) (m (conjs-sub m g)))
                        (:instance append-list-orbits (a (subaction (conj-sub-act m g) g h)) (g h))))))

(defthmd find-subgroupp-conjs-sub-6
  (implies (and (subgroupp m g)
		(primep p)
		(p-groupp m p)
		(not (divides p (subgroup-index m (normalizer m g))))
		(subgroupp h g)
		(p-groupp h p))
	   (find-supergroup h (conjs-sub m g)))
  :hints (("Goal" :use (not-find-supergroup-divides-p mod-len-conjs-sub))))

(defthmd find-subgroupp-conjs-sub
  (implies (and (subgroupp m g)
		(primep p)
		(p-groupp m p)
		(not (divides p (subgroup-index m (normalizer m g))))
		(subgroupp h g)
		(p-groupp h p))
	   (let ((k (find-supergroup h (conjs-sub m g))))
	     (and (member-equal k (conjs-sub m g))
	          (subgroupp h k))))
  :hints (("Goal" :use (find-subgroupp-conjs-sub-6
                        (:instance find-supergroup-supergroup (l (conjs-sub m g)))))))

(defthmd sylow-4
  (implies (and (groupp g)
                (primep p)
		(subgroupp h g)
		(p-groupp h p))
	   (let* ((m (sylow-subgroup g p))
	          (k (find-supergroup h (conjs-sub m g))))
	     (and (member-equal k (conjs-sub m g))
	          (subgroupp h k))))
  :hints (("Goal" :use (index-sylow-subgroup
                        (:instance find-subgroupp-conjs-sub (m (sylow-subgroup g p)))))))

	
