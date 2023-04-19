;; David M. Russinoff
;; david@russinoff.com
;; http://www.russinoff.com

(in-package "DM")

(local (include-book "support/sylow"))

(include-book "actions")

;;------------------------------------------------------------------------------------------------------
;; P-Sylow Subgroups
;;------------------------------------------------------------------------------------------------------

;; If h is a p-subgroup of g and p divides (subgroup-index p (normalizer h g)), then h is a proper
;; subgroup of a p-subgroup of g, which may be constructed by first applying cauchy's theorem
;; to construct a subgroup of (quotient (normalizer h g) h) of order p and then lifting it to g:

(defund extend-p-subgroup (h g p)
  (lift (cyclic (elt-of-ord p (quotient (normalizer h g) h))
		(quotient (normalizer h g) h))
	h
	(normalizer h g)))

(defthmd order-extend-p-subgroup
  (implies (and (subgroupp h g)
		(posp n)
		(elt-of-ord n (quotient (normalizer h g) h)))
	   (let ((k (extend-p-subgroup h g n)))
	     (and (subgroupp h k)
	          (subgroupp k g)
		  (equal (order k) (* n (order h)))))))

;; We recursively define a p-subgroup m of g such that p does not divide the index of m in its
;; normalizer.  We shall eventually show that p does not divide the index of m in g:

(defun sylow-subgroup-aux (h g p)
  (declare (xargs :measure (nfix (- (order g) (order h)))))
  (if (and (subgroupp h g) (primep p) (divides p (subgroup-index h (normalizer h g))))
      (sylow-subgroup-aux (extend-p-subgroup h g p) g p)
    h))

(defund sylow-subgroup(g p)
  (sylow-subgroup-aux (trivial-subgroup g) g p))

(defthm index-sylow-subgroup
  (implies (and (groupp g)
                (primep p))
	   (let ((m (sylow-subgroup g p)))
	     (and (subgroupp m g)
		  (p-groupp m p)
		  (not (divides p (subgroup-index m (normalizer m g))))))))


;;------------------------------------------------------------------------------------------------------
;; Conjugation of P-Sylow Subgroups
;;------------------------------------------------------------------------------------------------------

;; Consider the action of g on the list of conjugates of a p-sylow subgroup m.  This action has one 
;; orbit, the order of which is the index of the normalizer of m.  We shall show that this index is 
;; congruent to 1 mod p, and therefore not divisible by p.

;; To this end, consider the restriction of this action to some p-subgroup h of g.  Let c be a conjugate
;; of m.  We shall show that the orbit of c under this subaction is a singleton iff h is a subgroup
;; of c.

;; By normalizer-conj-sub, the normalizer of c is a conjugate of the normalizer of m.  The following
;; is a consequence of this observation and order-conj-sub:

(defthmd equal-indices
  (implies (and (subgroupp m g)
		(in c (conj-sub-act m g)))
	   (equal (subgroup-index c (normalizer c g))
	          (subgroup-index m (normalizer m g)))))

;; Thus, p does not divide (subgroup-index c (normalizer c g)).  Now suppose x is an element of both
;; h and (normalizer c g), but not an element of c.  Since the order of x is a power of p, the order
;; of the coset of x in (quotient (normalizer c g) c) is also a power of p, and p must divide
;; (subgroup-index c (normalizer c g)), a contradiction.  Thus, we have the following:

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
	   (in x c)))

;; By stabilizer-orbit, the length of the orbit of c under (subaction (conj-sub-act m g) g h) h) 
;; is 1 if (stabilizer c (subaction (conj-sub-act m g) g h) h) = h, and otherwise is divisible by p.

;; If x is in h, then by stabilizer-subaction, x in is (stabilizer c (subaction (conj-sub-act m g) g h) h) 
;; iff x is in (normalizer c g), and by in-normalizer-in-c, this holds iff x is in c.  Thus, 
;; (stabilizer c (subaction (conj-sub-act m g) g h) h) = h iff h is a subgroup of c:

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
	     (divides p (len (orbit c (subaction (conj-sub-act m g) g h) h))))))


;;------------------------------------------------------------------------------------------------------
;; Sylow Theorems
;;------------------------------------------------------------------------------------------------------

;; We apply the above result to the case h = m.  By conjs-sub-subgroup, m is a subgroup of exactly 
;; 1 conjugate of m, which implies there is exactly 1 orbit of length 1 and all others have length
;; divisible by p:

(defthmd orbit-subaction-m-len-1
  (implies (and (subgroupp m g)
		(primep p)
		(p-groupp m p)
		(not (divides p (subgroup-index m (normalizer m g))))
		(in c (conj-sub-act m g)))
	   (if (equal c (conj-sub m (e g) g))
	       (equal (len (orbit c (subaction (conj-sub-act m g) g m) m)) 1)
	     (divides p (len (orbit c (subaction (conj-sub-act m g) g m) m))))))

;; Appending all orbits yields the following:

(defthmd mod-len-conjs-sub
  (implies (and (subgroupp m g)
		(primep p)
		(p-groupp m p)
		(not (divides p (subgroup-index m (normalizer m g)))))
	   (equal (mod (len (conjs-sub m g)) p)
	          1)))

;; Since (len (conjs-sub m g)) = (subgroup-index (normalizer m g) g), it divides
;; (subgroup-index m g):

(defthmd divides-len-conjs-sub
  (implies (and (subgroupp m g)
		(primep p)
		(p-groupp m p)
		(not (divides p (subgroup-index m (normalizer m g)))))
	   (divides (len (conjs-sub m g))
	            (subgroup-index m g))))

;; Since (len (conjs-sub m g)) = (subgroup-index (normalizer m g) g) is not divisible by p,
;; neither is (subgroup-index m g):

(defthmd not-divides-p-index-m
  (implies (and (subgroupp m g)
		(primep p)
		(p-groupp m p)
		(not (divides p (subgroup-index m (normalizer m g)))))
	   (not (divides p (subgroup-index m g)))))

;; The first 3 Sylow theorems are derived by combining each of the last 3 results with
;; index-sylow-subgroup:

(defthmd sylow-1
  (implies (and (groupp g)
		(primep p))
	   (let ((m (sylow-subgroup g p)))
	     (equal (mod (len (conjs-sub m g)) p)
	            1))))

(defthmd sylow-2
  (implies (and (groupp g)
		(primep p))
	   (let ((m (sylow-subgroup g p)))
	     (divides (len (conjs-sub m g))
	              (subgroup-index m g)))))

(defthmd sylow-3
  (implies (and (groupp g)
		(primep p))
	   (not (divides p (subgroup-index (sylow-subgroup g p) g)))))

;; As a consequence of Sylow-3, the order of a p-Sylow subgroup of g is the largest power of p
;; dividing (order g):

(defthmd order-sylow-subgroup
  (implies (and (groupp g)
                (primep p))
	   (let ((m (sylow-subgroup g p)))
             (and (subgroupp m g)
	          (equal (order m)
	                 (expt p (log (order g) p)))))))


;;----------------------------------

;; The final Sylow theorem states that every p-subgroup of g is a subgroup of some conjugate of m.
;; This is derived as another consequence of orbit-subaction-div-p.

;; If some member of the list l is a group of which h is a subgroup, then the following function
;; returns such a group, and otherwise it returns nil:

(defun find-supergroup (h l)
  (if (consp l)
      (if (subgroupp h (car l))
          (car l)
	(find-supergroup h (cdr l)))
    ()))

;; Let h be a p-subgroup of g.  If h is not a subgroup of any conjugate of m, then according to
;; orbit-subaction-div-p, the length of every orbit of h is divisible by p, which implies the
;; following:

(defthmd not-find-supergroup-divides-p
  (implies (and (subgroupp m g)
		(primep p)
		(p-groupp m p)
		(not (divides p (subgroup-index m (normalizer m g))))
		(subgroupp h g)
		(p-groupp h p)
	        (not (find-supergroup h (conjs-sub m g))))
	   (divides p (len (conjs-sub m g)))))

;; But since this contradicts mod-len-conjs-sub, h must be a subgroup of some element of
;; (conjs-sub m g):

(defthmd find-subgroupp-conjs-sub
  (implies (and (subgroupp m g)
		(primep p)
		(p-groupp m p)
		(not (divides p (subgroup-index m (normalizer m g))))
		(subgroupp h g)
		(p-groupp h p))
	   (let ((k (find-supergroup h (conjs-sub m g))))
	     (and (member-equal k (conjs-sub m g))
	          (subgroupp h k)))))

;; Combine the last result with index-sylow-subgroup:

(defthmd sylow-4
  (implies (and (groupp g)
                (primep p)
		(subgroupp h g)
		(p-groupp h p))
	   (let* ((m (sylow-subgroup g p))
	          (k (find-supergroup h (conjs-sub m g))))
	     (and (member-equal k (conjs-sub m g))
	          (subgroupp h k)))))


