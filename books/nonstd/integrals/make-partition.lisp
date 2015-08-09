(in-package "ACL2")

(include-book "nonstd/integrals/integrable-functions" :dir :system)

(local (include-book "arithmetic-5/top" :dir :system))
(local (include-book "nonstd/nsa/nsa" :dir :system))


(defun make-partition-rec (a delta n)
  (if (zp n)
      (list a)
    (cons a
          (make-partition-rec (+ a delta) delta (1- n)))))

(defun make-partition (a b n)
  (make-partition-rec a (/ (- b a) n) n))

(defun make-small-partition (a b)
  (make-partition a b (i-large-integer)))

(defthm partitionp-append
  (implies (and (partitionp p1)
		(partitionp p2)
		(equal (car (last p1)) (car p2)))
	   (partitionp (append p1 (cdr p2)))))

(local
 (defthm deltas-append
   (implies (and (partitionp p1)
		 (partitionp p2)
		 (equal (car (last p1)) (car p2)))
	    (equal (deltas (append p1 (cdr p2)))
		   (append (deltas p1)
			   (deltas p2))))))

(local
 (defthm maxlist-non-negative
   (implies (real-listp x)
	    (and (realp (maxlist x))
		 (<= 0 (maxlist x))))))

(local
 (defthm maxlist-append
   (implies (and (real-listp x1)
		 (real-listp x2)
		 )
	    (equal (maxlist (append x1 x2))
		   (max (maxlist x1)
			(maxlist x2))))))

(local
 (defthm real-listp-deltas
   (implies (partitionp p)
	    (real-listp (deltas p)))))

(local
 (defthm maxlist-deltas-append
   (implies (and (partitionp p1)
		 (partitionp p2)
		 (equal (car (last p1)) (car p2)))
	    (equal (maxlist (deltas (append p1 (cdr p2))))
		   (max (maxlist (deltas p1))
			(maxlist (deltas p2)))))
   :hints (("Goal" :do-not-induct t))
   ))



(defthm mesh-append
  (implies (and (partitionp p1)
		(partitionp p2)
		(equal (car (last p1)) (car p2)))
	   (equal (mesh (append p1 (cdr p2)))
		  (max (mesh p1)
		       (mesh p2)))))

(local
 (defthm mesh-append
   (implies (and (partitionp p1)
		 (partitionp p2)
		 (equal (car (last p1)) (car p2)))
	    (equal (mesh (append p1 (cdr p2)))
		   (max (mesh p1)
			(mesh p2))))))


(local
 (defthmd i-close-plus
  (implies (and (i-close x1 x2)
		(i-close y1 y2))
	   (i-close (+ x1 y1)
		    (+ x2 y2)))
  :hints (("Goal"
	   :in-theory (enable i-close i-small)))))

(local
 (defthm car-make-partition-rec
   (equal (car (make-partition-rec a delta n))
	  a)))

(local
 (defthm car-make-partition
   (equal (car (make-partition a b n))
	  a)))


(local
 (defthm car-last-make-partition-rec
   (implies (and (acl2-numberp a)
		 (acl2-numberp delta)
		 (natp n))
	    (equal (car (last (make-partition-rec a delta n)))
		   (+ a (* n delta))))))

(local
 (defthm car-last-make-partition
   (implies (and (acl2-numberp a)
		 (acl2-numberp b)
		 (posp n))
	    (equal (car (last (make-partition a b n)))
		   b))))

(local
 (defthm partitionp-make-partition-rec
   (implies (and (realp a)
		 (realp delta)
		 (< 0 delta)
		 (natp n)
		 )
	    (partitionp (make-partition-rec a delta n)))))

(local
 (defthm partitionp-make-partition
   (implies (and (realp a)
		 (realp b)
		 (< a b)
		 (natp n)
		 )
	    (partitionp (make-partition a b n)))))

(local
 (defthm maxlist-deltas-make-partition-rec
   (implies (and (acl2-numberp a)
		 (acl2-numberp delta)
		 (<= 0 delta))
	    (equal (maxlist (deltas (make-partition-rec a delta n)))
		   (if (zp n)
		       0
		     delta)))))

(local
 (defthm maxlist-deltas-make-partition
   (implies (and (acl2-numberp a)
		 (acl2-numberp b)
		 (< a b)
		 (posp n))
	    (equal (maxlist (deltas (make-partition a b n)))
		   (/ (- b a) n)))))

(local
 (defthm consp-cdr-make-partition-rec-2
   (consp (cdr (make-partition-rec a delta 2)))
   :hints (("Goal"
	    :expand ((make-partition-rec a delta 2))))
   ))

(local
 (defthm consp-cdr-make-partition-rec-1
   (consp (cdr (make-partition-rec a delta 1)))
   :hints (("Goal"
	    :expand ((make-partition-rec a delta 1))))
   ))




(local
 (defthm consp-cdr-make-partition-rec
   (implies (posp n)
	    (consp (cdr (make-partition-rec a delta n))))))

(local
 (defthm consp-cdr-make-partition
   (implies (posp n)
	    (consp (cdr (make-partition a b n))))))

(defthm partitionp-make-small-partition
  (implies (and (realp a)
		(realp b)
		(< a b))
	   (partitionp (make-small-partition a b))))



(defthm car-make-small-partition
  (equal (car (make-small-partition a b))
	 a))

(defthm car-last-make-small-partition
  (implies (and (acl2-numberp a)
		(acl2-numberp b))
	   (equal (car (last (make-small-partition a b)))
		  b)))

(defthm car-last-cdr-make-small-partition
  (implies (and (acl2-numberp a)
		(acl2-numberp b)
		(< a b))
	   (equal (car (last (cdr (make-small-partition a b))))
		  b))
  :hints (("Goal"
	   :use ((:instance car-last-make-small-partition))
	   :in-theory (disable car-last-make-small-partition
			       make-small-partition))))

(local
 (defthm maxlist-deltas-make-small-partition
   (implies (and (acl2-numberp a)
		 (acl2-numberp b)
		 (< a b))
	    (equal (maxlist (deltas (make-small-partition a b)))
		   (/ (- b a) (i-large-integer))))))

(local
 (defthm mesh-make-small-partition
   (implies (and (acl2-numberp a)
		 (acl2-numberp b)
		 (< a b))
	    (equal (mesh (make-small-partition a b))
		   (/ (- b a) (i-large-integer))))))

(defthm small-mesh-make-small-partition
  (implies (and (acl2-numberp a) (standardp a)
		(acl2-numberp b) (standardp b)
		(< a b))
	   (i-small (mesh (make-small-partition a b)))))

(defthm consp-cdr-make-small-partition
  (implies (and (acl2-numberp a)
		(acl2-numberp b)
		(< a b))
	   (consp (cdr (make-small-partition a b)))))

(in-theory (disable make-small-partition))
