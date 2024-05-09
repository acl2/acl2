(in-package "DM")

(include-book "maps")

;;-----------------------------------------------------------------------------------------------------------
;; Direct Products
;;-----------------------------------------------------------------------------------------------------------

;; Direct product of a list of groups:

(defun group-list-p (l)
  (if (consp l)
      (and (groupp (car l))
           (group-list-p (cdr l)))
    (null l)))

(defun group-tuples-aux (l m)
  (if (consp l)
      (append (conses (car l) m)
              (group-tuples-aux (cdr l) m))
    ()))

(defun group-tuples (l)
  (if (consp l)
      (group-tuples-aux (elts (car l)) (group-tuples (cdr l)))
    (list ())))

(local-defun all-len (l n)
  (if (consp l)
      (and (equal (len (car l)) n)
           (all-len (cdr l) n))
    t))

(local-defthm all-len-conses
  (implies (all-len m n)
           (all-len (conses x m) (1+ n))))

(local-defthm all-len-append
  (implies (and (all-len l n) (all-len m n))
           (all-len (append l m) n)))

(local-defthm all-len-group-tuples-aux
  (implies (all-len m n)
	   (all-len (group-tuples-aux l m) (1+ n))))

(local-defthmd all-len-group-tuples
  (all-len (group-tuples l)
           (len l)))

(local-defthm all-len-len
  (implies (and (all-len l n)
                (member-equal x l))
	   (equal (len x) n)))

(defthmd len-group-tuple
  (implies (member-equal x (group-tuples l))
           (equal (len x) (len l)))
  :hints (("Goal" :use (all-len-group-tuples))))

(defun product-orders (l)
  (if (consp l)
      (* (order (car l)) (product-orders (cdr l)))
    1))

(local-defthm len-group-tuples-aux
  (equal (len (group-tuples-aux l m))
         (* (len l) (len m))))

(defthm len-group-tuples
  (implies (group-list-p l)
           (equal (len (group-tuples l))
                  (product-orders l))))

(local-defthm group-tuples-aux-non-nil
  (not (member-equal () (group-tuples-aux l m))))

(defthm group-tuples-non-nil
  (implies (consp l)
           (not (member-equal () (group-tuples l)))))

(local-defthm consp-group-tuples-aux
  (implies (and (consp l) (consp m))
	   (consp (group-tuples-aux l m))))

(defthm consp-group-tuples
  (implies (group-list-p l)
	   (consp (group-tuples l))))

(local-defun in-list (x l)
  (if (consp l)
      (and (consp x) (in (car x) (car l)) (in-list (cdr x) (cdr l)))
    (null x)))

(local-defthm group-tuples-in-list-aux
  (iff (member-equal x (group-tuples-aux l m))
       (and (consp x)
           (member-equal (car x) l)
           (member-equal (cdr x) m))))

(local-defthm group-tuples-in-list
  (implies (group-list-p l)
	   (iff (member-equal x (group-tuples l))
		(in-list x l))))

(local-defthm dlistp-group-tuples-aux
  (implies (and (dlistp l) (dlistp m))
	   (dlistp (group-tuples-aux l m)))
  :hints (("Subgoal *1/2" :use ((:instance dlistp-append (l (conses (car l) m)) (m (group-tuples-aux (cdr l) m)))
				(:instance common-member-shared (l (conses (car l) m)) (m (group-tuples-aux (cdr l) m)))
				(:instance group-tuples-in-list-aux (x (common-member (conses (car l) m) (group-tuples-aux (cdr l) m)))
					                      (l (conses (car l) m)) (m (group-tuples-aux (cdr l) m)))))))

(defthm dlistp-group-tuples
  (implies (group-list-p l)
	   (dlistp (group-tuples l))))

(defun e-list (l)
  (if (consp l)
      (cons (e (car l)) (e-list (cdr l)))
    ()))

(local-defthm car-group-tuples-aux
  (implies (and (consp l) (consp m))
           (equal (car (group-tuples-aux l m))
	          (cons (car l) (car m)))))

(defthm car-group-tuples
  (implies (group-list-p l)
           (equal (car (group-tuples l))
		  (e-list l)))
  :hints (("Goal" :in-theory (enable e))))

(defthm member-e-list--group-tuples
  (implies (group-list-p l)
           (member-equal (e-list l) (group-tuples l))))

(defun dp-op (x y l)
  (if (consp l)
      (cons (op (car x) (car y) (car l))
            (dp-op (cdr x) (cdr y) (cdr l)))
    ()))

(defthm e-group-tuples
  (implies (and (group-list-p l)
                (member-equal x (group-tuples l)))
	   (equal (dp-op (e-list l) x l)
	          x)))

(defthm group-tuples-closed
  (implies (and (group-list-p l)
                (member-equal x (group-tuples l))
                (member-equal y (group-tuples l)))
	   (member-equal (dp-op x y l) (group-tuples l))))

(defthm group-tuples-assoc
  (implies (and (group-list-p l)
                (member-equal x (group-tuples l))
                (member-equal y (group-tuples l))
                (member-equal z (group-tuples l)))
	   (equal (dp-op (dp-op x y l) z l)
	          (dp-op x (dp-op y z l) l)))
  :hints (("Subgoal *1/5" :use ((:instance group-assoc (g (car l)) (x (car x)) (y (car y)) (z (car z)))))))

(defun dp-inv (x l)
  (if (consp l)
      (cons (inv (car x) (car l))
            (dp-inv (cdr x) (cdr l)))
    ()))

(defthm group-tuples-inv
  (implies (and (group-list-p l)
                (member-equal x (group-tuples l)))
	   (and (member-equal (dp-inv x l) (group-tuples l))
	        (equal (dp-op (dp-inv x l) x l)
	               (e-list l)))))

(defgroup direct-product (gl)
  (and (group-list-p gl) (consp gl))
  (group-tuples gl)
  (dp-op x y gl)
  (dp-inv x gl))

;; Order of a direct-product:

(local-defthm len-group-tuples-aux
  (equal (len (group-tuples-aux l m))
         (* (len l) (len m))))

(defthm len-group-tuples
  (implies (group-list-p l)
           (equal (len (group-tuples l))
                  (product-orders l))))

(defthmd order-of-dp
  (implies (group-list-p l)
	   (equal (order (direct-product l))
		  (product-orders l))))


(defthm e-dp
  (implies (and (group-list-p l)
                (consp l))
	   (equal (e (direct-product l))
	          (e-list l)))
  :hints (("Goal" :in-theory (enable e))))


(defthmd in-dp
  (implies (and (group-list-p l) (consp l))
	   (iff (in x (direct-product l))
		(and (consp x)
		     (in (car x) (car l))
		     (if (cdr l)
			 (in (cdr x) (direct-product (cdr l)))
		       (null (cdr x))))))		       
  :hints (("Goal" :expand ((in-list x l))
                          :use (group-tuples-in-list
			        (:instance group-tuples-in-list (x (cdr x)) (l (cdr l)))
				(:instance direct-product-elts (gl (cdr l)))))))

(defthmd member-group-tuples
  (implies (and (group-list-p l) (consp l))
	   (iff (member-equal x (group-tuples l))
		(and (consp x)
		     (in (car x) (car l))
		     (if (cdr l)
			 (member-equal (cdr x) (group-tuples (cdr l)))
		       (null (cdr x))))))
  :hints (("Goal" :use (in-dp (:instance in-dp (x (cdr x)) (l (cdr l)))))))

;; Index of an element of a direct product:

(local-defthm index-group-tuples-aux-1
  (implies (and (consp x)
                (member-equal (car x) l)
		(member-equal (cdr x) m))
	   (equal (index x (group-tuples-aux l m))
	          (+ (* (index (car x) l) (len m))
		     (index (cdr x) m)))))

(local-defthmd index-group-tuples-aux-2
  (implies (member-equal x (group-tuples-aux l m))
           (and (consp x)
	        (member-equal (car x) l)
		(member-equal (cdr x) m))))

(local-defthm index-group-tuples-aux
  (implies (member-equal x (group-tuples-aux l m))
           (equal (index x (group-tuples-aux l m))
	          (+ (* (index (car x) l) (len m))
		     (index (cdr x) m))))
  :hints (("Goal" :use (index-group-tuples-aux-2))))

(local-defthm group-tuples-aux-non-nil
  (not (member-equal () (group-tuples-aux l m))))

(local-defun conses-nil (l)
  (if (consp l)
      (cons (list (car l)) (conses-nil (cdr l)))
    ()))

(local-defthm len-conses-nil
  (equal (len (conses-nil l))
         (len l)))

(local-defthm group-tuples-aux-list-nil
  (equal (group-tuples-aux l '(()))
         (conses-nil l)))

(local-defthm index-conses-nil
  (implies (member-equal x (conses-nil l))
           (equal (index x (conses-nil l))
	          (index (car x) l))))

(defun cdrs-induct (x l)
  (if (consp l)
      (list (cdrs-induct (cdr x) (cdr l)))
    x))

(defthmd ind-dp
  (implies (and (group-list-p l)
                (consp l)
                (in x (direct-product l)))
	   (equal (ind x (direct-product l))
	          (if (cdr l)
	              (+ (* (ind (car x) (car l))
		            (order (direct-product (cdr l))))
		         (ind (cdr x) (direct-product (cdr l))))
		    (ind (car x) (car l)))))
  :hints (("Goal" :in-theory (enable order order-of-dp) :induct (cdrs-induct x l))))

(in-theory (disable group-tuples))

(local-defthmd idp-dp-hack
  (implies (and (natp x1) (natp x2) (natp y1) (natp y2) (posp p)
                (< x2 p) (< y2 p) (< x1 y1))
	   (< (+ x2 (* p x1)) (+ y2 (* p y1))))
  :hints (("Goal" :nonlinearp t)))

(defthmd ind-dp-compare
  (implies (and (group-list-p l)
                (consp l)
                (in x (direct-product l))
                (in y (direct-product l)))
	   (iff (< (ind x (direct-product l))
	           (ind y (direct-product l)))
		(or (< (ind (car x) (car l))
		       (ind (car y) (car l)))
		    (and (consp (cdr l))
		         (equal (car x) (car y))
			 (< (ind (cdr x) (direct-product (cdr l)))
			    (ind (cdr y) (direct-product (cdr l))))))))
  :hints (("Goal" :in-theory (e/d (order) (len-group-tuples ind<len))
                  :nonlinearp t
                  :use (ind-dp
		        (:instance ind-dp (x y))
			(:instance idp-dp-hack (p (product-orders (cdr l))) (x1 (ind (car x) (car l))) (x2 (index (cdr x) (group-tuples (cdr l))))
			                                                    (y1 (ind (car y) (car l))) (y2 (index (cdr y) (group-tuples (cdr l)))))
			(:instance idp-dp-hack (p (product-orders (cdr l))) (y1 (ind (car x) (car l))) (y2 (index (cdr x) (group-tuples (cdr l))))
			                                                    (x1 (ind (car y) (car l))) (x2 (index (cdr y) (group-tuples (cdr l)))))
			(:instance len-group-tuples (l (cdr l)))
			(:instance index-1-to-1 (x (car x)) (y (car y)) (l (caar l)))
			(:instance ind<len (x (cdr x)) (l (group-tuples (cdr l))))
			(:instance ind<len (x (cdr y)) (l (group-tuples (cdr l))))
			(:instance direct-product-elts (gl (cdr l)))))))

;; Power of an element of a direct-product:

(defun dp-power (x n l)
  (if (consp l)
      (cons (power (car x) n (car l))
            (dp-power (cdr x) n (cdr l)))
    ()))

(local-defthm dp-power-in-dp
  (implies (and (group-list-p l)
                (consp l)
                (in x (direct-product l))
		(natp n))
	   (in-list (dp-power x n l) l)))

(local-defthm power-dp-n+1
  (implies (and (group-list-p l)
                (consp l)
                (in x (direct-product l))
		(natp n))
	   (equal (dp-op x (dp-power x n l) l)
		  (dp-power x (1+ n) l))))

(defthmd power-dp
  (implies (and (group-list-p l)
                (consp l)
                (in x (direct-product l)))
	   (equal (power x n (direct-product l))
		  (dp-power x n l)))
  :hints (("Goal" :induct (fact n))))


;;-----------------------------------------------------------------------------------------------------------
;; List of Products of Two Subgroups
;;-----------------------------------------------------------------------------------------------------------

;; The ordered list of products of subgroups h and k of g:

(defun products-aux (l g)
  (if (consp l)
      (insert (op (caar l) (cadar l) g)
              (products-aux (cdr l) g)
	      g)
    ()))

(defund products (h k g)
  (products-aux (group-tuples (list h k)) g))

(local-defthm ordp-products-aux
  (implies (and (subgroupp h g)
                (subgroupp k g)
		(sublistp l (group-tuples (list h k))))
           (ordp (products-aux l g) g)))

(defthm ordp-products
  (implies (and (subgroupp h g)
                (subgroupp k g))
           (ordp (products h k g) g))
  :hints (("Goal" :in-theory (enable products))))

(defthm dlistp-products
  (implies (and (subgroupp h g)
                (subgroupp k g))
           (dlistp (products h k g)))	   
  :hints (("Goal" :in-theory (disable ordp-products) :use (ordp-products))))

(local-defthmd product-in-products-aux
  (implies (and (subgroupp h g)
                (subgroupp k g)
                (sublistp l (group-tuples (list h k)))
		(member-equal p l))
	   (member-equal (op (car p) (cadr p) g) (products-aux l g))))

(defthmd product-in-products
  (implies (and (subgroupp h g)
                (subgroupp k g)
                (in x h)
		(in y k))
	   (member-equal (op x y g) (products h k g)))
  :hints (("Goal" :in-theory (enable products)
                  :use ((:instance product-in-products-aux (p (list x y)) (l (group-tuples (list h k))))))))

(defun factor-elt-aux (x l g)
  (if (consp l)
      (if (equal x (op (caar l) (cadar l) g))
          (car l)
	(factor-elt-aux x (cdr l) g))
    ()))

(defund factor-elt (x h k g)
  (factor-elt-aux x (group-tuples (list h k)) g))

(local-defthm product-in-products-converse-aux
  (implies (and (subgroupp h g)
                (subgroupp k g)
                (sublistp l (group-tuples (list h k)))
		(member-equal x (products-aux l g)))
	   (let ((p (factor-elt-aux x l g)))
	     (and (in (car p) h)
	          (in (cadr p) k)
		  (equal (op (car p) (cadr p) g) x)))))

(defthmd product-in-products-converse
  (implies (and (subgroupp h g)
                (subgroupp k g)
		(member-equal x (products h k g)))
	   (let ((p (factor-elt x h k g)))
	     (and (in (car p) h)
	          (in (cadr p) k)
		  (equal (op (car p) (cadr p) g) x))))
  :hints (("Goal" :in-theory (enable factor-elt products)
                  :use ((:instance product-in-products-converse-aux (l (group-tuples (list h k))))))))

;; If either subgroup is normal, then the product is a subgroup:

(defthmd in-e-subgroup
  (implies (subgroupp h g)
           (in (e g) h))
  :hints (("Goal" :in-theory (disable consp-groupp)
                  :use ((:instance e (g h))
                        (:instance consp-groupp (g h))))))

(defthm member-e--products
  (implies (and (subgroupp h g)
                (subgroupp k g))
           (member-equal (e g) (products h k g)))
  :hints (("Goal" :use (in-e-subgroup
		        (:instance in-e-subgroup (h k))
			(:instance product-in-products (x (e h)) (y (e k)))))))

(defthm car-products
  (implies (and (subgroupp h g)
                (subgroupp k g))
           (equal (car (products h k g))
	          (e g)))
  :hints (("Goal" :in-theory (enable e)
                  :use (member-e--products
                        (:instance car-ordp-minimal (x (e g)) (l (products h k g)))))))

(defthm consp-products
  (implies (and (subgroupp h g)
                (subgroupp k g))
           (consp (products h k g)))	   
  :hints (("Goal" :use (member-e--products))))

(defthm sublistp-products
  (implies (and (subgroupp h g)
                (subgroupp k g))
	   (sublistp (products h k g) (elts g)))
  :hints (("Goal" :use ((:instance scex1-lemma (l (products h k g)) (m (elts g)))
                        (:instance product-in-products-converse (x (scex1 (products h k g) (elts g))))))))

(local-defthmd products-closed-1
  (implies (and (subgroupp h g)
                (subgroupp k g)
		(in h1 h)
		(in k1 k)
		(in h2 h)
		(in k2 k))
	   (equal (op (op h1 k1 g) (op h2 k2 g) g)
	          (op (op h1 k1 g)
		      (op h2
		          (op (op (inv k1 g) k1 g)
			      k2
			      g)
			  g)
		      g))))

(local-defthmd products-closed-2
  (implies (and (subgroupp h g)
                (subgroupp k g)
		(in h1 h)
		(in k1 k)
		(in h2 h)
		(in k2 k))
	   (equal (op (op h1 k1 g) (op h2 k2 g) g)
	          (op (op h1 (conj h2 k1 g) g) (op k1 k2 g) g)))
  :hints (("Goal" :in-theory (e/d (conj group-assoc) (group-left-inverse))
                  :use (products-closed-1))))

(local-defthm products-closed-3
  (implies (and (subgroupp h g) (in x h) (in y h))
           (in (op x y g) h))
  :hints (("Goal" :in-theory (disable group-closure)
                  :use ((:instance group-closure (g h))))))

(local-defthmd products-closed-4
  (implies (and (normalp h g)
                (subgroupp k g)
		(in h1 h)
		(in k1 k)
		(in h2 h)
		(in k2 k))
	   (member-equal (op (op h1 k1 g) (op h2 k2 g) g)
	                 (products h k g)))
  :hints (("Goal" :in-theory (e/d (products-closed-2) (normalp-conj))
                  :use (products-closed-2
		        (:instance product-in-products (x (op h1 (conj h2 k1 g) g)) (y (op k1 k2 g)))
		        (:instance normalp-conj (x h2) (y k1))))))

(local-defthmd products-closed-5
  (implies (and (normalp h g)
                (subgroupp k g)
		(member-equal x (products h k g))
		(member-equal y (products h k g)))
	   (member-equal (op x y g)
	                 (products h k g)))
  :hints (("Goal" :use (product-in-products-converse
                        (:instance product-in-products-converse (x y))
			(:instance products-closed-4 (h1 (car (factor-elt x h k g)))
			                             (k1 (cadr (factor-elt x h k g)))
						     (h2 (car (factor-elt y h k g)))
			                             (k2 (cadr (factor-elt y h k g))))))))

(local-defthmd products-closed-6
  (implies (and (subgroupp h g)
                (subgroupp k g)
		(in h1 h)
		(in k1 k)
		(in h2 h)
		(in k2 k))
	   (equal (op (op h1 k1 g) (op h2 k2 g) g)
	          (op (op h1
		          (op (op h2 (inv h2 g) g) k1 g)
			  g)
		      (op h2 k2 g)
		      g))))

(local-defthmd products-closed-7
  (implies (and (subgroupp h g)
                (subgroupp k g)
		(in h1 h)
		(in k1 k)
		(in h2 h)
		(in k2 k))
	   (equal (op (op h1 k1 g) (op h2 k2 g) g)
	          (op (op h1 h2 g)
		      (op (conj k1 (inv h2 g) g) k2 g)
		      g)))
  :hints (("Goal" :in-theory (e/d (conj group-assoc) (group-right-inverse))
                  :use (products-closed-6))))

(local-defthmd products-closed-8
  (implies (and (normalp k g)
                (subgroupp h g)
		(in h1 h)
		(in k1 k)
		(in h2 h)
		(in k2 k))
	   (member-equal (op (op h1 k1 g) (op h2 k2 g) g)
	                 (products h k g)))
  :hints (("Goal" :in-theory (disable normalp-conj)
                  :use (products-closed-7
		        (:instance product-in-products (x (op h1 h2 g)) (y (op (conj k1 (inv h2 g) g) k2 g)))
		        (:instance normalp-conj (h k) (x k1) (y (inv h2 g)))))))

(local-defthmd products-closed-9
  (implies (and (normalp k g)
                (subgroupp h g)
		(member-equal x (products h k g))
		(member-equal y (products h k g)))
	   (member-equal (op x y g)
	                 (products h k g)))
  :hints (("Goal" :use (product-in-products-converse
                        (:instance product-in-products-converse (x y))
			(:instance products-closed-8 (h1 (car (factor-elt x h k g)))
			                             (k1 (cadr (factor-elt x h k g)))
						     (h2 (car (factor-elt y h k g)))
			                             (k2 (cadr (factor-elt y h k g))))))))

(defthm products-closed
  (implies (and (subgroupp h g)
                (subgroupp k g)
                (or (normalp h g) (normalp k g))
		(member-equal x (products h k g))
		(member-equal y (products h k g)))
	   (member-equal (op x y g)
	                 (products h k g)))
  :hints (("Goal" :use (products-closed-5 products-closed-9))))

(local-defthmd products-inv-1
  (implies (and (subgroupp h g)
                (subgroupp k g)
		(in h1 h)
		(in k1 k))
	   (equal (op (inv k1 g) (inv h1 g) g)
	          (op (op (inv k1 g) (inv h1 g) g)
		      (op k1 (inv k1 g) g)
		      g))))

(local-defthmd products-inv-2
  (implies (and (subgroupp h g)
                (subgroupp k g)
		(in h1 h)
		(in k1 k))
	   (equal (op (inv k1 g) (inv h1 g) g)
	          (op (conj (inv h1 g) (inv k1 g) g)
		      (inv k1 g)
		      g)))
  :hints (("Goal" :in-theory (e/d (conj group-assoc) (group-right-inverse))
                  :use (products-inv-1))))

(local-defthm products-inv-3
  (implies (and (subgroupp h g) (in x h))
           (in (inv x g) h))
  :hints (("Goal" :in-theory (disable group-left-inverse)
                  :use ((:instance group-left-inverse (g h))))))

(local-defthmd products-inv-4
  (implies (and (normalp h g)
                (subgroupp k g)
		(in h1 h)
		(in k1 k))
	   (member-equal (inv (op h1 k1 g) g)
	                 (products h k g)))
  :hints (("Goal" :in-theory (e/d (prod-inv) (normalp-conj))
                  :use (products-inv-2
		        (:instance product-in-products (x (conj (inv h1 g) (inv k1 g) g)) (y (inv k1 g)))
		        (:instance normalp-conj (x (inv h1 g)) (y (inv k1 g)))))))

(local-defthmd products-inv-5
  (implies (and (normalp h g)
                (subgroupp k g)
		(member-equal x (products h k g)))
	   (member-equal (inv x g)
	                 (products h k g)))
  :hints (("Goal" :use (product-in-products-converse
			(:instance products-inv-4 (h1 (car (factor-elt x h k g)))
			                             (k1 (cadr (factor-elt x h k g))))))))

(local-defthmd products-inv-6
  (implies (and (subgroupp h g)
                (subgroupp k g)
		(in h1 h)
		(in k1 k))
	   (equal (op (inv k1 g) (inv h1 g) g)
	          (op (op (inv h1 g) h1 g)
		      (op (inv k1 g) (inv h1 g) g)
		      g))))

(local-defthmd products-inv-7
  (implies (and (subgroupp h g)
                (subgroupp k g)
		(in h1 h)
		(in k1 k))
	   (equal (op (inv k1 g) (inv h1 g) g)
	          (op (inv h1 g)
		      (conj (inv k1 g) h1 g)
		      g)))
  :hints (("Goal" :in-theory (e/d (conj group-assoc) (group-left-inverse))
                  :use (products-inv-6))))

(local-defthmd products-inv-8
  (implies (and (normalp k g)
                (subgroupp h g)
		(in h1 h)
		(in k1 k))
	   (member-equal (inv (op h1 k1 g) g)
	                 (products h k g)))
  :hints (("Goal" :in-theory (e/d (prod-inv) (normalp-conj))
                  :use (products-inv-7
		        (:instance product-in-products (x (inv h1 g)) (y (conj (inv k1 g) h1 g)))
		        (:instance normalp-conj (h k) (x (inv k1 g)) (y h1))))))

(local-defthmd products-inv-9
  (implies (and (normalp k g)
                (subgroupp h g)
		(member-equal x (products h k g)))
	   (member-equal (inv x g)
	                 (products h k g)))
  :hints (("Goal" :use (product-in-products-converse
			(:instance products-inv-8 (h1 (car (factor-elt x h k g)))
			                          (k1 (cadr (factor-elt x h k g))))))))

(defthm products-inv
  (implies (and (subgroupp h g)
                (subgroupp k g)
                (or (normalp h g) (normalp k g))
		(member-equal x (products h k g)))
	   (member-equal (inv x g)
	                 (products h k g)))
  :hints (("Goal" :use (products-inv-5 products-inv-9))))

(defsubgroup product-group (h k) g
  (and (subgroupp h g)
       (subgroupp k g)
       (or (normalp h g) (normalp k g)))
  (products h k g))

;; If both subgroups are normal, then the product is a normal subgroup:

(local-defthmd normalp-product-1
  (implies (and (normalp h g)
                (normalp k g)
		(in h1 h)
		(in k1 k)
		(in x g))
	   (equal (conj (op h1 k1 g) x g)
	          (conj (op (op h1 (op (inv x g) x g) g) k1 g) x g))))

(local-defthmd normalp-product-2
  (implies (and (normalp h g)
                (normalp k g)
		(in h1 h)
		(in k1 k)
		(in x g))
	   (equal (conj (op h1 k1 g) x g)
	          (op (conj h1 x g)
		      (conj k1 x g)
		      g)))
  :hints (("Goal" :in-theory (e/d (conj group-assoc) (group-left-inverse))
                  :use (normalp-product-1))))

(local-defthmd normalp-product-3
  (implies (and (normalp h g)
                (normalp k g)
		(in h1 h)
		(in k1 k)
		(in x g))
	   (member-equal (conj (op h1 k1 g) x g)
	                 (products h k g)))
  :hints (("Goal" :in-theory (disable normalp-conj)
                  :use (normalp-product-2
		        (:instance product-in-products (x (conj h1 x g)) (y (conj k1 x g)))
		        (:instance normalp-conj (x h1) (y x))
			(:instance normalp-conj (h k) (x k1) (y x))))))

(local-defthmd normalp-product-4
  (implies (and (normalp h g)
                (normalp k g)
		(in y g)
		(member-equal x (products h k g)))
	   (member-equal (conj x y g)
	                 (products h k g)))
  :hints (("Goal" :use (product-in-products-converse
			(:instance normalp-product-3 (x y)
			                             (h1 (car (factor-elt x h k g)))
			                             (k1 (cadr (factor-elt x h k g))))))))

(defthmd normalp-product-group
  (implies (and (normalp h g)
                (normalp k g))
           (normalp (product-group h k g)
		    g))
  :hints (("Goal" :use ((:instance not-normalp-cex (h (product-group h k g)))
                        (:instance normalp-product-4 (x (car (normalp-cex (product-group h k g) g)))
			                             (y (cadr (normalp-cex (product-group h k g) g))))))))

(local-defthmd product-group-assoc-1
  (implies (and (normalp h1 g)
                (normalp h2 g)
                (normalp h3 g)
	        (in x (product-group (product-group h1 h2 g) h3 g)))
	   (in x (product-group h1 (product-group h2 h3 g) g)))
  :hints (("Goal" :in-theory (enable group-assoc)
                  :use ((:instance product-in-products-converse (h (product-group h1 h2 g)) (k h3))
                        (:instance product-in-products-converse (h h1) (k h2) (x (car (factor-elt x (product-group h1 h2 g) h3 g))))
			(:instance product-in-products (x (cadr (factor-elt (car (factor-elt x (product-group h1 h2 g) h3 g))
                                                                            h1 h2 g)))
						       (y (cadr (factor-elt x (product-group h1 h2 g) h3 g)))
						       (h h2)
						       (k h3))
			(:instance product-in-products (x (car (factor-elt (car (factor-elt x (product-group h1 h2 g) h3 g))
                                                               h1 h2 g)))
						       (y (op (cadr (factor-elt (car (factor-elt x (product-group h1 h2 g) h3 g))
                                                                                h1 h2 g))
							      (cadr (factor-elt x (product-group h1 h2 g) h3 g))
							      g))
						       (h h1)
						       (k (product-group h2 h3 g)))))))

(local-defthmd product-group-assoc-2
  (implies (and (normalp h1 g)
                (normalp h2 g)
                (normalp h3 g)
	        (in x (product-group h1 (product-group h2 h3 g) g)))
	   (in x (product-group (product-group h1 h2 g) h3 g)))
  :hints (("Goal" :use ((:instance product-in-products-converse (h h1) (k (product-group h2 h3 g)))
                        (:instance product-in-products-converse (h h2) (k h3) (x (cadr (factor-elt x h1 (product-group h2 h3 g) g))))
			(:instance product-in-products (x (car (factor-elt x h1 (product-group h2 h3 g) g)))
						       (y (car (factor-elt (cadr (factor-elt x h1 (product-group h2 h3 g) g)) h2 h3 g)))
						       (h h1)
						       (k h2))
			(:instance product-in-products (x (op (car (factor-elt x h1 (product-group h2 h3 g) g))
                                                              (car (factor-elt (cadr (factor-elt x h1 (product-group h2 h3 g) g)) h2 h3 g))
                                                              g))                                                           
						       (y (cadr (factor-elt (cadr (factor-elt x h1 (product-group h2 h3 g) g)) h2 h3 g)))
						       (h (product-group h1 h2 g))
						       (k h3))
			(:instance group-assoc (x (car (factor-elt x h1 (product-group h2 h3 g) g)))
			                       (y (car (factor-elt (cadr (factor-elt x h1 (product-group h2 h3 g) g)) h2 h3 g)))
					       (z (cadr (factor-elt (cadr (factor-elt x h1 (product-group h2 h3 g) g)) h2 h3 g))))))))

(local-defthmd product-group-assoc-3
  (implies (and (normalp h1 g)
                (normalp h2 g)
                (normalp h3 g))
	   (equal (products h1 (product-group h2 h3 g) g)
	          (products (product-group h1 h2 g) h3 g)))
  :hints (("Goal" :use ((:instance product-group-assoc-1 (x (scex1 (products (product-group h1 h2 g) h3 g)
                                                                   (products h1 (product-group h2 h3 g) g))))
                        (:instance product-group-assoc-2 (x (scex1 (products h1 (product-group h2 h3 g) g)
                                                                   (products (product-group h1 h2 g) h3 g))))
                        (:instance ordp-equal (x (products h1 (product-group h2 h3 g) g))
			                      (y (products (product-group h1 h2 g) h3 g)))
			(:instance scex1-lemma (l (products h1 (product-group h2 h3 g) g))
			                       (m (products (product-group h1 h2 g) h3 g)))
			(:instance scex1-lemma (m (products h1 (product-group h2 h3 g) g))
			                       (l (products (product-group h1 h2 g) h3 g)))))))

(defthmd product-group-assoc
  (implies (and (normalp h1 g)
                (normalp h2 g)
                (normalp h3 g))
	   (equal (product-group h1 (product-group h2 h3 g) g)
	          (product-group (product-group h1 h2 g) h3 g)))
  :hints (("Goal" :use (product-group-assoc-3
                        (:instance subgroups-equal-elts (h (product-group h1 (product-group h2 h3 g) g))
			                                (k (product-group (product-group h1 h2 g) h3 g)))))))

(local-defthmd product-trivial-group-1
  (implies (normalp h g)
           (iff (in x (product-group h (trivial-subgroup g) g))
	        (in x h)))
  :hints (("Goal" :use ((:instance product-in-products (k (trivial-subgroup g)) (y (e g)))
                        (:instance product-in-products-converse (k (trivial-subgroup g)))))))

(local-defthmd product-trivial-group-2
  (implies (normalp h g)
           (iff (in x (product-group (trivial-subgroup g) h g))
	        (in x h)))
  :hints (("Goal" :use ((:instance product-in-products (k h) (h (trivial-subgroup g)) (x (e g)) (y x))
                        (:instance product-in-products-converse (k h) (h (trivial-subgroup g)))))))

(defthmd product-trivial-group-permp-1
  (implies (normalp h g)
           (permp (elts (product-group h (trivial-subgroup g) g))
	          (elts h)))
  :hints (("Goal" :in-theory (enable permp)
                  :use ((:instance product-trivial-group-1 (x (scex1 (elts (product-group h (trivial-subgroup g) g)) (elts h))))
		        (:instance product-trivial-group-1 (x (scex1 (elts h) (elts (product-group h (trivial-subgroup g) g)))))
		        (:instance scex1-lemma (l (elts (product-group h (trivial-subgroup g) g))) (m (elts h)))
		        (:instance scex1-lemma (m (elts (product-group h (trivial-subgroup g) g))) (l (elts h)))))))

(defthmd product-trivial-group-permp-2
  (implies (normalp h g)
           (permp (elts (product-group (trivial-subgroup g) h g))
	          (elts h)))
  :hints (("Goal" :in-theory (enable permp)
                  :use ((:instance product-trivial-group-2 (x (scex1 (elts (product-group (trivial-subgroup g) h g)) (elts h))))
		        (:instance product-trivial-group-2 (x (scex1 (elts h) (elts (product-group (trivial-subgroup g) h g)))))
		        (:instance scex1-lemma (l (elts (product-group (trivial-subgroup g) h g))) (m (elts h)))
		        (:instance scex1-lemma (m (elts (product-group (trivial-subgroup g) h g))) (l (elts h)))))))

(defthmd product-trivial-group-order
  (implies (normalp h g)
           (and (equal (order (product-group (trivial-subgroup g) h g))
	               (order h))
		(equal (order (product-group h (trivial-subgroup g) g))
	               (order h))))
  :hints (("Goal" :use (product-trivial-group-permp-1 product-trivial-group-permp-2
                        (:instance eq-len-permp (l (elts (product-group (trivial-subgroup g) h g))) (m (elts h)))
                        (:instance eq-len-permp (l (elts (product-group h (trivial-subgroup g) g))) (m (elts h)))))))

(local-defthmd product-trivial-group-3
  (implies (and (normalp h g) (ordp (elts h) g))
           (equal (products h (trivial-subgroup g) g)
	          (elts h)))
  :hints (("Goal" :use ((:instance product-trivial-group-1 (x (scex1 (products h (trivial-subgroup g) g) (elts h))))
                        (:instance product-trivial-group-1 (x (scex1 (elts h) (products h (trivial-subgroup g) g))))
                        (:instance ordp-equal (x (elts h)) (y (products h (trivial-subgroup g) g)))
			(:instance scex1-lemma (l (products h (trivial-subgroup g) g)) (m (elts h)))
			(:instance scex1-lemma (m (products h (trivial-subgroup g) g)) (l (elts h)))))))

(local-defthmd product-trivial-group-4
  (implies (and (normalp h g) (ordp (elts h) g))
           (equal (products (trivial-subgroup g) h g)
	          (elts h)))
  :hints (("Goal" :use ((:instance product-trivial-group-2 (x (scex1 (products (trivial-subgroup g) h g) (elts h))))
                        (:instance product-trivial-group-2 (x (scex1 (elts h) (products (trivial-subgroup g) h g))))
                        (:instance ordp-equal (x (elts h)) (y (products (trivial-subgroup g) h g)))
			(:instance scex1-lemma (l (products (trivial-subgroup g) h g)) (m (elts h)))
			(:instance scex1-lemma (m (products (trivial-subgroup g) h g)) (l (elts h)))))))

(defthmd product-trivial-group-ordp
  (implies (and (normalp h g) (ordp (elts h) g))
           (and (equal (product-group (trivial-subgroup g) h g)
	               h)
		(equal (product-group h (trivial-subgroup g) g)
                       h)))
  :hints (("Goal" :use (product-trivial-group-3 product-trivial-group-4
                        (:instance subgroups-equal-elts (k (product-group (trivial-subgroup g) h g)))
                        (:instance subgroups-equal-elts (k (product-group h (trivial-subgroup g) g)))))))


;;-----------------------------------------------------------------------------------------------------------
;; Length of the List of Products
;;-----------------------------------------------------------------------------------------------------------

;; We shall derive the following formula for the number of products:
	      
;; (defthmd len-products
;;   (implies (and (subgroupp h g)
;;                 (subgroupp k g))
;;           (equal (len (products h k g))
;;                  (/ (* (order h) (order k))
;;                     (order (intersect-groups h k g))))))

;; Given a list l of elements of (lcosets (group-intersection h k g) h), convert it to
;; a list of elements of (lcosets k g) by replacing each member c of l with
;; (lcoset (car c) k g):

(defun lift-cosets-aux (l k g)
  (if (consp l)
      (cons (lcoset (caar l) k g)
	    (lift-cosets-aux (cdr l) k g))
    ()))

;; Apply lift-cosets-aux to the full list (lcosets (group-intersection h k g) g):

(defund lift-cosets (h k g)
  (lift-cosets-aux (lcosets (group-intersection h k g) h) k g))

;; The result is a list of distinct elements of (lcosets k g):

(local-defthm sublistp-lift-cosets-aux
  (implies (and (subgroupp h g)
                (subgroupp k g)
		(sublistp l (lcosets (group-intersection h k g) h))
		(dlistp l))
	   (sublistp (lift-cosets-aux l k g) (lcosets k g)))
  :hints (("Subgoal *1/3" :use ((:instance lcoset-car (x (caar l)) (h (group-intersection h k g)) (g h))
                                (:instance lcosets-cars (c (car l)) (h (group-intersection h k g)) (g h))
                                (:instance member-lcoset-cosets (h k) (x (caar l)))))))

(local-defthm dlistp-lift-cosets-aux-1
  (implies (and (subgroupp h g) (in x h) (in y h))
           (and (in (op (inv x g) y h) h)
		(equal (op (inv x g) y h) (op (inv x g) y g))))
  :rule-classes ()
  :hints (("Goal" :in-theory (disable group-closure group-left-inverse subgroup-inv subgroup-op)
                  :use (subgroup-inv
                        (:instance subgroup-op (x (inv x g)))
			(:instance group-left-inverse (g h))
			(:instance group-closure (x (inv x h)) (g h))))))

(local-defthm dlistp-lift-cosets-aux-2
  (implies (and (subgroupp h g)
                (subgroupp k g)
		(member-equal c (lcosets (group-intersection h k g) h))
		(member-equal d (lcosets (group-intersection h k g) h))
		(equal (lcoset (car c) k g) (lcoset (car d) k g)))
	   (equal c d))
  :rule-classes ()
  :hints (("Goal" :use ((:instance lcosets-cars (h (group-intersection h k g)) (g h))
                        (:instance lcosets-cars (h (group-intersection h k g)) (g h) (c d))
			(:instance equal-lcosets-iff (x (car c)) (y (car d)) (h k))
			(:instance equal-lcosets-iff (x (car c)) (y (car d)) (h (group-intersection h k g)) (g h))
			(:instance lcosets-cars (h (group-intersection h k g)) (g h))
			(:instance lcosets-cars (h (group-intersection h k g)) (g h) (c d))
			(:instance dlistp-lift-cosets-aux-1 (x (car c)) (y (car d)))))))

(local-defthmd dlistp-lift-cosets-aux-3
  (implies (and (subgroupp h g)
                (subgroupp k g)
		(sublistp l (lcosets (group-intersection h k g) h))
		(member-equal c (lcosets (group-intersection h k g) h)))
	   (iff (member-equal (lcoset (car c) k g)  (lift-cosets-aux l k g))
	        (member-equal c l)))		
  :hints (("Subgoal *1/3" :use ((:instance dlistp-lift-cosets-aux-2 (d (car l)))))))

(local-defthm dlistp-lift-cosets-aux
  (implies (and (subgroupp h g)
                (subgroupp k g)
		(sublistp l (lcosets (group-intersection h k g) h))
		(dlistp l))
	   (dlistp (lift-cosets-aux l k g)))	   
  :hints (("Subgoal *1/3" :use ((:instance dlistp-lift-cosets-aux-3 (c (car l)) (l (cdr l)))))))

(defthmd dlistp-lift-cosets
  (implies (and (subgroupp h g)
                (subgroupp k g))
	   (and (sublistp (lift-cosets h k g) (lcosets k g))
	        (dlistp (lift-cosets h k g))))
  :hints (("Goal" :in-theory (enable lift-cosets))))

;; Appending these lists yields a dlist. This follows from lcosets-disjointp-pairwise, dlistp-list-lcosets,
;; dlistp-list-sublist, disjointp-pairwise-sublistp, and dlistp-append-list:

(defthm dlistp-append-list-lift-cosets
  (implies (and (subgroupp h g)
                (subgroupp k g))
	   (dlistp (append-list (lift-cosets h k g))))
  :hints (("Goal" :use (dlistp-lift-cosets))))

;; The length of (lift-cosets h k g) is the length of (lcosets (group-intersection h k g) h),
;; which is (/ (order h) (order (intersect-groups h k g)))  Since the length of each member 
;; of the list is (order k), we have the following expression for the length of the appended
;; list:

(local-defthm len-append-list-lift-cosets-aux
  (implies (and (subgroupp h g)
                (subgroupp k g)
		(sublistp l (lcosets (group-intersection h k g) h)))
           (equal (len (append-list (lift-cosets-aux l k g)))
	          (* (len l) (order k))))	   
  :hints (("Subgoal *1/1" :in-theory (enable len-lcoset)
                          :use ((:instance lcosets-cars (h (group-intersection h k g)) (g h) (c (car l)))))))

(defthm len-append-list-lift-cosets
  (implies (and (subgroupp h g)
                (subgroupp k g))
           (equal (len (append-list (lift-cosets h k g)))
	          (/ (* (order h) (order k))
		     (order (group-intersection h k g)))))
  :hints (("Goal" :in-theory (e/d (lift-cosets) (order))
	          :use ((:instance lagrange (h (group-intersection h k g)) (g h))
		        (:instance order-pos (g (group-intersection h k g)))))))

;; It is easy to show that (lift-cosets h k g)) is a sublist of (products h k g):

(local-defthmd member-append-list-products-aux
  (implies (and (subgroupp h g)
                (subgroupp k g)
		(sublistp l (lcosets (group-intersection h k g) h))
		(member-equal x (append-list (lift-cosets-aux l k g))))
           (member-equal x (products h k g)))
  :hints (("Subgoal *1/2" :use ((:instance lcosets-cars (c (car l)) (h (group-intersection h k g)) (g h))
                                (:instance member-lcoset-iff (y x) (x (caar l)) (h k))
				(:instance group-assoc (x (caar l)) (y (inv (caar l) g)) (z x))
				(:instance product-in-products (x (caar l)) (y (op (inv (caar l) g) x g)))))))

(local-defthm member-append-list-products
  (implies (and (subgroupp h g)
                (subgroupp k g)
		(member-equal x (append-list (lift-cosets h k g))))
           (member-equal x (products h k g)))
  :hints (("Goal" :in-theory (enable lift-cosets)
                  :use ((:instance member-append-list-products-aux (l (lcosets (group-intersection h k g) h)))))))

(defthm sublistp-lift-cosets-product
  (implies (and (subgroupp h g)
                (subgroupp k g))
           (sublistp (append-list (lift-cosets h k g))
	             (products h k g)))
  :hints (("Goal" :use ((:instance scex1-lemma (l (append-list (lift-cosets h k g))) (m (products h k g)))))))

;; On the other hand, if x is an element of (products h k g), then x = (op a b g),
;; where a is in h and b is in k. Some member of (lcosets (group-intersection h k g) h)
;; contains a, as does the corresponding member of (lift-cosets h k g), which therefore
;; contains x.  Thus, we have the converse:

(local-defthmd in-h-append-list-aux
  (implies (and (subgroupp h g)
                (subgroupp k g)
		(sublistp l (lcosets (group-intersection h k g) h))
		(in a h)
		(in b k)
		(member-equal (lcoset a (group-intersection h k g) h) l))
	   (member-equal (op a b g) (append-list (lift-cosets-aux l k g))))
  :hints (("Subgoal *1/1" :in-theory (disable member-self-lcoset)
                          :use ((:instance lcosets-cars (c (car l)) (h (group-intersection h k g)) (g h))
                                (:instance member-self-lcoset (x a) (h (group-intersection h k g)) (g h))
                                (:instance member-lcoset-iff (y a) (x (caar l)) (h (group-intersection h k g)) (g h))
				(:instance group-assoc (x (inv (caar l) g)) (y a) (z b))
                                (:instance member-lcoset-iff (y (op a b g)) (x (caar l)) (h k))
				(:instance group-closure (x (op (inv (caar l) g) a g)) (y b) (g k))				
				(:instance dlistp-lift-cosets-aux-1 (x (caar l)) (y a))))))

(local-defthmd in-h-append-list
  (implies (and (subgroupp h g)
                (subgroupp k g)
		(in a h)
		(in b k))
	   (member-equal (op a b g) (append-list (lift-cosets h k g))))
  :hints (("Goal" :in-theory (enable member-lcoset-cosets lift-cosets)
                  :use ((:instance in-h-append-list-aux (l (lcosets (group-intersection h k g) h)))))))

(local-defthm member-product-append-list
  (implies (and (subgroupp h g)
                (subgroupp k g)
		(member-equal x (products h k g)))
	   (member-equal x (append-list (lift-cosets h k g))))
  :hints (("Goal" :use (product-in-products-converse
                        (:instance in-h-append-list (a (car (factor-elt x h k g)))
			                            (b (cadr (factor-elt x h k g))))))))

(defthm sublistp-product-append-list
  (implies (and (subgroupp h g)
                (subgroupp k g))
	   (sublistp (products h k g)
	             (append-list (lift-cosets h k g))))
  :hints (("Goal" :use ((:instance member-product-append-list (x (scex1 (products h k g) (append-list (lift-cosets h k g)))))
                        (:instance scex1-lemma (l (products h k g)) (m (append-list (lift-cosets h k g))))))))

;; It follows that (products h k g) and (append-list (lift-cosets h k g)) have the
;; same length, and the desired result follows:

(defthmd len-products
  (implies (and (subgroupp h g)
                (subgroupp k g))
           (equal (len (products h k g))
                  (/ (* (order h) (order k))
                     (order (group-intersection h k g)))))
  :hints (("Goal" :in-theory (enable permp)
                  :use ((:instance eq-len-permp (l (products h k g)) (m (append-list (lift-cosets h k g))))))))


;;-----------------------------------------------------------------------------------------------------------
;; Internal Direct Products
;;-----------------------------------------------------------------------------------------------------------

;; The product of a list of normal subgroups of g:

(defun product-group-list (l g)
  (if (consp l)
      (product-group (car l) (product-group-list (cdr l) g) g)
    (trivial-subgroup g)))

(defun normal-list-p (l g)
  (if (consp l)
      (and (normalp (car l) g)
           (normal-list-p (cdr l) g))
    (null l)))

(defthm normal-list-group-list
  (implies (normal-list-p l g)
           (group-list-p l)))

(defthm normalp-product-group-list
  (implies (and (groupp g)
                (normal-list-p l g))
           (normalp (product-group-list l g) g))
  :hints (("Subgoal *1/2" :in-theory (enable normalp-product-group))))

(defthm ordp-product-group-list
  (implies (and (groupp g)
                (normal-list-p l g))
           (ordp (elts (product-group-list l g)) g)))

(defthm product-group-append-list
  (implies (and (groupp g)
                (normal-list-p l g)
                (normal-list-p m g))
	   (equal (product-group-list (append l m) g)
	          (product-group (product-group-list l g)
		                 (product-group-list m g)
				 g)))				 
  :hints (("Subgoal *1/3" :use ((:instance product-group-assoc (h1 (car l))
                                                               (h2 (product-group-list (cdr l) g))
							       (h3 (product-group-list m g)))))
	  ("Subgoal *1/1" :in-theory (enable product-trivial-group-ordp))))

;; Given a non-nil list l of subgroups of g, (direct-product l) is isomorphic to (product-group-list l g)
;; if l satisfies the following predicate:

(defun internal-direct-product-p (l g)
  (if (consp l)
      (and (internal-direct-product-p (cdr l) g)
           (normalp (car l) g)
	   (equal (group-intersection (car l) (product-group-list (cdr l) g) g)
	          (trivial-subgroup g)))
    (null l)))

(defthm normalp-idp
  (implies (internal-direct-product-p l g)
           (normal-list-p l g)))

(defthm group-list-p-idp
  (implies (internal-direct-product-p l g)
           (group-list-p l)))

;;; The isomorphism is defined as follows:

(defun product-list-val (x g)
  (if (consp x)
      (if (consp (cdr x))
          (op (car x) (product-list-val (cdr x) g) g)
	(car x))
    ()))

(defmap product-list-map (gl g)
  (group-tuples gl)
  (product-list-val x g))

(defun double-cdr-induct (l x)
  (if (consp l)
      (list (double-cdr-induct (cdr l) (cdr x)))
    x))

(defthmd product-list-val-in-product-group-list
  (implies (and (consp l)
                (normal-list-p l g)
		(in x (direct-product l)))
	   (in (product-list-val x g)
	       (product-group-list l g)))
  :hints (("Goal" :induct (double-cdr-induct l x))  
          ("Subgoal *1/3" :use (:instance product-trivial-group-1 (h (car l)) (x (car x))))
          ("Subgoal *1/1" :use (:instance product-trivial-group-1 (h (car l)) (x (car x))))
	  ("Subgoal *1/2" :use (:instance product-in-products (h (car l))
	                                                      (k (PRODUCT-GROUP-LIST (CDR L) G))
						              (x (car x))
							      (y (PRODUCT-LIST-VAL (CDR X) G))))))

(local-defthmd normalp-op-commutes-1
  (implies (and (normalp h g)
                (normalp k g)
		(in x h)
		(in y k))
	   (in (op (op (op x y g) (inv x g) g) (inv y g) g)
	       k))
  :hints (("Goal" :in-theory (enable conj)
                  :use ((:instance normalp-conj (h k) (x y) (y x))))))

(local-defthmd normalp-op-commutes-2
  (implies (and (normalp h g)
                (normalp k g)
		(in x h)
		(in y k))
	   (equal (op (op (op x y g) (inv x g) g) (inv y g) g)
	          (op x (op (op y (inv x g) g) (inv y g) g) g)))
  :hints (("Goal" :in-theory (enable group-assoc))))

(local-defthmd normalp-op-commutes-3
  (implies (and (normalp h g)
                (normalp k g)
		(in x h)
		(in y k))
	   (in (op (op (op x y g) (inv x g) g) (inv y g) g)
	       h))
  :hints (("Goal" :in-theory (enable conj)
                  :use (normalp-op-commutes-2
		       (:instance normalp-conj (x (inv x g)))))))

(local-defthmd normalp-op-commutes-4
  (implies (and (normalp h g)
                (normalp k g)
		(in x h)
		(in y k))
	   (in (op (op (op x y g) (inv x g) g) (inv y g) g)
	       (group-intersection h k g)))
  :hints (("Goal" :use (normalp-op-commutes-1 normalp-op-commutes-3))))

(local-defthmd normalp-op-commutes-5
  (implies (and (normalp h g)
                (normalp k g)
		(equal (group-intersection h k g)
		       (trivial-subgroup g))
		(in x h)
		(in y k))
	   (equal (op (op (op x y g) (inv x g) g) (inv y g) g)
	          (e g)))
  :hints (("Goal" :use (normalp-op-commutes-4))))

(defthmd internal-dp-lemma
  (implies (and (normalp h g)
                (normalp k g)
		(equal (group-intersection h k g)
		       (trivial-subgroup g))
		(in x h)
		(in y k))
	   (equal (op x y g) (op y x g)))
  :hints (("Goal" :use (normalp-op-commutes-5
                        (:instance right-cancel (a (inv y g)) (x y) (y (op (op x y g) (inv x g) g)))
			(:instance right-cancel (a (inv x g)) (x (op y x g)) (y (op x y g)))
			(:instance group-assoc (x y) (y x) (z (inv x g)))))))

(local-defthm internal-dp-e-1
  (implies (and (normalp h g)
                (normalp k g)
		(in x h)
		(in y k)
		(equal (op x y g) (e g)))
	   (in x (group-intersection h k g)))
  :rule-classes ()
  :hints (("Goal" :use ((:instance right-cancel (a y) (y (inv y g)))))))

(defthm internal-dp-e
  (implies (and (normalp h g)
                (normalp k g)
		(equal (group-intersection h k g)
		       (trivial-subgroup g))
		(in x h)
		(in y k)
		(equal (op x y g) (e g)))
	   (and (equal x (e g)) (equal y (e g))))
  :rule-classes ()
  :hints (("Goal" :use (internal-dp-e-1))))

(local-defthmd product-list-map-op-1
  (IMPLIES (AND (CONSP Y)
                (CONSP (CDR Y))
                (CONSP X)
                (CONSP (CDR X))
                (CONSP L)
                (INTERNAL-DIRECT-PRODUCT-P (CDR L) G)
                (NORMALP (CAR L) G)
                (MEMBER-EQUAL (CAR X) (CAR (CAR L)))
                (IN-LIST (CDR X) (CDR L))
                (MEMBER-EQUAL (CAR Y) (CAR (CAR L)))
                (IN-LIST (CDR Y) (CDR L)))
	   (and (in (PRODUCT-LIST-VAL (CDR X) G) (PRODUCT-GROUP-LIST (CDR L) G))
	        (in (PRODUCT-LIST-VAL (CDR y) G) (PRODUCT-GROUP-LIST (CDR L) G))
		(normalp (PRODUCT-GROUP-LIST (CDR L) G) g)))
:hints (("Goal" :use ((:instance product-list-val-in-product-group-list (x (cdr x)) (l (cdr l)))
                      (:instance product-list-val-in-product-group-list (x (cdr y)) (l (cdr l)))))))

(local-defthmd product-list-map-op-2
  (implies (and (normalp h g) (in x1 h) (in y1 h)
                (normalp k g) (in x2 k) (in y2 k)
		(equal (group-intersection h k g) (trivial-subgroup g)))
	   (equal (op (op x1 y1 h) (op x2 y2 g) g)
	          (op (op x1 x2 g) (op y1 y2 g) g)))
  :hints (("Goal" :in-theory (disable subgroup-op)
                  :use ((:instance subgroup-op (x x1) (y y1))
		        (:instance group-assoc (x x1) (y y1) (z (op x2 y2 g)))
			(:instance group-assoc (x y1) (y x2) (z y2))
			(:instance internal-dp-lemma (x y1) (y x2))
			(:instance group-assoc (x x2) (y y1) (z y2))
			(:instance group-assoc (x x1) (y x2) (z (op y1 y2 g)))))))
                
(defthm product-list-map-op
  (implies (and (consp l)
                (internal-direct-product-p l g)
		(in x (direct-product l))
		(in y (direct-product l)))
	   (equal (product-list-val (dp-op x y l) g)
	          (op (product-list-val x g)
		      (product-list-val y g)
		      g)))
  :hints (("Subgoal *1/7" :use (len-group-tuple (:instance len-group-tuple (x y))))
          ("Subgoal *1/6" :in-theory (disable subgroup-op) :use ((:instance subgroup-op (h (car l)) (x (car x)) (y (car y)))))	  
          ("Subgoal *1/5" :use (product-list-map-op-1
	                        (:instance product-list-map-op-2 (h (car l)) (x1 (car x)) (y1 (car y))
				                                 (k (PRODUCT-GROUP-LIST (CDR L) G))
								 (x2 (PRODUCT-LIST-VAL (CDR X) G))
								 (y2 (PRODUCT-LIST-VAL (CDR y) G)))))))

(defthm product-list-map-e
  (implies (and (consp l)
                (internal-direct-product-p l g))
	   (equal (product-list-val (e-list l) g)
	          (e g)))
  :hints (("Subgoal *1/1" :in-theory (enable normalp))
          ("Subgoal *1/3" :in-theory (enable normalp))))


(defthm groupp-product-group-list
  (implies (and (groupp g)
                (internal-direct-product-p l g))
           (groupp (product-group-list l g)))
  :hints (("Goal" :in-theory (e/d (normalp) (NORMALP-GROUPP normalp-idp normalp-product-group-list normal-list-group-list))
                  :use (normalp-product-group-list normalp-idp normal-list-group-list))))

(defthm subgroupp-product-group-list
  (implies (and (groupp g)
                (internal-direct-product-p l g))
           (subgroupp (product-group-list l g) g))
  :hints (("Goal" :in-theory (e/d (normalp) (NORMALP-GROUPP normalp-idp normalp-product-group-list normal-list-group-list))
                  :use (normalp-product-group-list normalp-idp normal-list-group-list))))

(local-defthm homomorphismp-product-list-map
  (implies (and (groupp g)
                (consp l)
                (internal-direct-product-p l g))
           (homomorphismp (product-list-map l g)
                          (direct-product l)
                          (product-group-list l g)))
  :hints (("Goal" :in-theory (enable product-list-val-in-product-group-list)
                  :use ((:instance homomorphismp (map (product-list-map l g)) (g (direct-product l)) (h (product-group-list l g)))
                        (:instance codomain-cex-lemma (map (product-list-map l g)) (g (direct-product l)) (h (product-group-list l g)))
                        (:instance homomorphismp-cex-lemma (map (product-list-map l g)) (g (direct-product l)) (h (product-group-list l g)))))
	  ("Subgoal 3" :in-theory (e/d (product-list-val-in-product-group-list) (subgroup-op))
	               :use ((:instance subgroup-op (x (PRODUCT-LIST-VAL (CAR (HOMOMORPHISM-CEX (PRODUCT-LIST-MAP L G)
                                                                         (DIRECT-PRODUCT L)
                                                                         (PRODUCT-GROUP-LIST L G)))
                                                                         G))
						    (y (PRODUCT-LIST-VAL (CdR (HOMOMORPHISM-CEX (PRODUCT-LIST-MAP L G)
                                                                         (DIRECT-PRODUCT L)
                                                                         (PRODUCT-GROUP-LIST L G)))
                                                                         G))
						    (h (PRODUCT-GROUP-LIST L G)))))
	  ("Subgoal 2" :in-theory (disable subgroup-e)
	               :use ((:instance subgroup-e (h (PRODUCT-GROUP-LIST L G)))))
	  ("Subgoal 1" :in-theory (disable subgroup-e)
	               :use ((:instance subgroup-e (h (PRODUCT-GROUP-LIST L G)))))))

(local-defthmd endomorphismp-product-list-map-1
  (implies (and (groupp g)
                (consp l)
                (internal-direct-product-p l g)
		(member-equal x (group-tuples l))
		(equal (product-list-val x g) (e g)))
	   (equal (e-list l) x))
  :hints (("Subgoal *1/6" :in-theory (enable normalp))
          ("Subgoal *1/5" :use ((:instance normalp (h (car l)))
			        (:instance internal-dp-e (x (car x)) (y (PRODUCT-LIST-VAL (CDR X) G)) (h (car l)) (k (PRODUCT-GROUP-LIST (CDR L) G)))
	                        (:instance product-list-val-in-product-group-list (x (cdr x)) (l (cdr l)))))
	  ("Subgoal *1/4" :use ((:instance internal-dp-e (x (car x)) (y (PRODUCT-LIST-VAL (CDR X) G)) (h (car l)) (k (PRODUCT-GROUP-LIST (CDR L) G)))
	                        (:instance product-list-val-in-product-group-list (x (cdr x)) (l (cdr l)))))))

(local-defthmd endomorphismp-product-list-map
  (implies (and (groupp g)
                (consp l)
                (internal-direct-product-p l g))
           (endomorphismp (product-list-map l g)
                          (direct-product l)
                          (product-group-list l g)))
  :hints (("Goal" :use ((:instance homomorphism-endomorphism (map (product-list-map l g)) (g (direct-product l)) (h (product-group-list l g)))
                        (:instance subgroup-e (h (PRODUCT-GROUP-LIST L G)))
                        (:instance endomorphismp-product-list-map-1 (x (cadr (kelts (product-list-map l g) (direct-product l) (product-group-list l g)))))))))

(defthmd order-product-group-list
  (implies (and (groupp g)
                (consp l)
                (internal-direct-product-p l g))
           (equal (order (product-group-list l g))
	          (product-orders l)))
  :hints (("Subgoal *1/3" :use ((:instance len-products (h (car l)) (k (PRODUCT-GROUP-LIST (CDR L) G)))))
          ("Subgoal *1/1" :use ((:instance product-trivial-group-order (h (car l)))))))

(defthmd isomorphismp-dp-product-list
  (implies (and (groupp g)
                (consp l)
                (internal-direct-product-p l g))
           (isomorphismp (product-list-map l g)
	                 (direct-product l)
			 (product-group-list l g)))
  :hints (("Goal" :use (order-product-group-list order-of-dp endomorphismp-product-list-map 
                        (:instance equal-orders-isomorphism (map (product-list-map l g)) (g (direct-product l)) (h (product-group-list l g)))))))

;; When the product of the orders is the order of g, the product group is g:

(defthmd isomorphismp-dp-idp
  (implies (and (groupp g)
                (consp l)
		(internal-direct-product-p l g)
                (= (product-orders l) (order g)))
           (isomorphismp (product-list-map l g)
	                 (direct-product l)
			 g))
  :hints (("Goal" :use (isomorphismp-dp-product-list order-product-group-list
                        (:instance ordp-subgroup-equal (h (product-group-list l g)))))))

; In the proof of the Fundamental Theorem of Finite Abelian Groups, we shall also need the following:

(local-defthmd internal-direct-product-append-1
  (implies (and (normalp h1 g)
                (normalp h2 g)
		(normalp k g)
		;(equal (group-intersection h1 h2 g) (trivial-subgroup g))
		;(equal (group-intersection (product-group h1 h2 g) k g) (trivial-subgroup g))
                (in x (group-intersection h1 (product-group h2 k g) g)))
	   (and (in (car (factor-elt x h2 k g)) h2)
	        (in (cadr (factor-elt x h2 k g)) k)
		(equal (op (inv (car (factor-elt x h2 k g)) g) x g)
		       (cadr (factor-elt x h2 k g)))))
  :hints (("Goal" :use ((:instance product-in-products-converse (h h2))
                        (:instance left-cancel (a (car (factor-elt x h2 k g)))
			                       (x (op (inv (car (factor-elt x h2 k g)) g) x g))
					       (y (cadr (factor-elt x h2 k g))))
			(:instance group-assoc (x (car (factor-elt x h2 k g))) (y (inv (car (factor-elt x h2 k g)) g)) (z x))))))

(local-defthmd internal-direct-product-append-2
  (implies (and (normalp h1 g)
                (normalp h2 g)
		(normalp k g)
		;(equal (group-intersection h1 h2 g) (trivial-subgroup g))
                (in x (group-intersection h1 (product-group h2 k g) g)))
	   (and (in (car (factor-elt x h2 k g)) h2)
	        ;(in (cadr (factor-elt x h2 k g)) k)
		;(equal (op (inv (car (factor-elt x h2 k g)) g) x g)
		;       (cadr (factor-elt x h2 k g)))
		(in (op (inv x g) (car (factor-elt x h2 k g)) g)
		    (product-group h1 h2 g))))
  :hints (("Goal" :use (internal-direct-product-append-1
                        (:instance product-in-products (x (inv x g)) (y (car (factor-elt x h2 k g))) (h h1) (k h2))))))

(local-defthmd internal-direct-product-append-3
  (implies (and (normalp h1 g)
                (normalp h2 g)
		(normalp k g)
		;(equal (group-intersection h1 h2 g) (trivial-subgroup g))
                (in x (group-intersection h1 (product-group h2 k g) g)))
           (in (op (inv (car (factor-elt x h2 k g)) g) x g)
	       (product-group h1 h2 g)))
  :hints (("Goal" :in-theory (disable group-left-inverse)
                  :use (internal-direct-product-append-2
                        (:instance group-left-inverse (x (op (inv x g) (car (factor-elt x h2 k g)) g)) (g (product-group h1 h2 g)))
			(:instance prod-inv (x (inv x g)) (y (car (factor-elt x h2 k g))))))))

(local-defthmd internal-direct-product-append-4
  (implies (and (normalp h1 g)
                (normalp h2 g)
		(normalp k g)
		;(equal (group-intersection h1 h2 g) (trivial-subgroup g))
                (in x (group-intersection h1 (product-group h2 k g) g)))
           (in (op (inv (car (factor-elt x h2 k g)) g) x g)
	       (group-intersection (product-group h1 h2 g) k g)))
  :hints (("Goal" :use (internal-direct-product-append-1 internal-direct-product-append-3))))

(local-defthmd internal-direct-product-append-5
  (implies (and (normalp h1 g)
                (normalp h2 g)
		(normalp k g)
		;(equal (group-intersection h1 h2 g) (trivial-subgroup g))
		(equal (group-intersection (product-group h1 h2 g) k g) (trivial-subgroup g))
                (in x (group-intersection h1 (product-group h2 k g) g)))
           (equal (op (inv (car (factor-elt x h2 k g)) g) x g)
	          (e g)))
  :hints (("Goal" :use (internal-direct-product-append-4))))

(local-defthmd internal-direct-product-append-6
  (implies (and (normalp h1 g)
                (normalp h2 g)
		(normalp k g)
		;(equal (group-intersection h1 h2 g) (trivial-subgroup g))
		(equal (group-intersection (product-group h1 h2 g) k g) (trivial-subgroup g))
                (in x (group-intersection h1 (product-group h2 k g) g)))
           (equal (car (factor-elt x h2 k g))
	          x))
  :hints (("Goal" :use (internal-direct-product-append-1 internal-direct-product-append-5
                        (:instance left-cancel (a (inv (car (factor-elt x h2 k g)) g)) (y (car (factor-elt x h2 k g))))))))

(local-defthmd internal-direct-product-append-7
  (implies (and (normalp h1 g)
                (normalp h2 g)
		(normalp k g)
		;(equal (group-intersection h1 h2 g) (trivial-subgroup g))
		(equal (group-intersection (product-group h1 h2 g) k g) (trivial-subgroup g))
                (in x (group-intersection h1 (product-group h2 k g) g)))
	   (in x (group-intersection h1 h2 g)))
  :hints (("Goal" :use (internal-direct-product-append-1 internal-direct-product-append-6))))

(local-defthmd internal-direct-product-append-8
  (implies (and (normalp h1 g)
                (normalp h2 g)
		(normalp k g)
		(equal (group-intersection h1 h2 g) (trivial-subgroup g))
		(equal (group-intersection (product-group h1 h2 g) k g) (trivial-subgroup g))
                (in x (group-intersection h1 (product-group h2 k g) g)))
	   (equal (e g) x))
  :hints (("Goal" :use (internal-direct-product-append-1 internal-direct-product-append-7))))

(local-defthmd internal-direct-product-append-9
  (implies (and (normalp h1 g)
                (normalp h2 g)
		(normalp k g)
		(equal (group-intersection h1 h2 g) (trivial-subgroup g))
		(equal (group-intersection (product-group h1 h2 g) k g) (trivial-subgroup g)))
           (equal (group-intersection h1 (product-group h2 k g) g)
	          (trivial-subgroup g)))
  :hints (("Goal" :use ((:instance internal-direct-product-append-8 (x (cadr (elts (group-intersection h1 (product-group h2 k g) g)))))
                        (:instance not-trivial-elt (h (group-intersection h1 (product-group h2 k g) g)))))))

(local-defthmd internal-direct-product-append-10
  (implies (and (normalp h1 g)
                (normalp h2 g)
		(normalp k g)
		(in x (group-intersection h2 k g)))
	   (in x (group-intersection (product-group h1 h2 g) k g)))
  :hints (("Goal" :in-theory (disable in-e-g subgroup-e)
                  :use ((:instance product-in-products (x (e g)) (y x) (h h1) (k h2))
		        (:instance in-e-g (g h1))
                        (:instance subgroup-e (h h1))))))

(local-defthmd internal-direct-product-append-11
  (implies (and (normalp h1 g)
                (normalp h2 g)
		(normalp k g)
		(equal (group-intersection (product-group h1 h2 g) k g)
		       (trivial-subgroup g)))
	   (equal (group-intersection h2 k g)
	          (trivial-subgroup g)))
  :hints (("Goal" :use ((:instance not-trivial-elt (h (group-intersection h2 k g)))
                        (:instance internal-direct-product-append-10 (x (cadr (elts (group-intersection h2 k g)))))))))

(defthmd internal-direct-product-append
  (implies (and (internal-direct-product-p l g)
		(internal-direct-product-p m g)
		(equal (group-intersection (product-group-list l g)
		                           (product-group-list m g)
					   g)
		       (trivial-subgroup g)))                
           (internal-direct-product-p (append l m) g))
  :hints (("Subgoal *1/4" :use ((:instance internal-direct-product-append-9 (h1 (car l))
                                                                            (h2 (PRODUCT-GROUP-LIST (CDR L) G))
									    (k (PRODUCT-GROUP-LIST m g)))))
          ("Subgoal *1/3" :use ((:instance internal-direct-product-append-11 (h1 (car l))
                                                                             (h2 (PRODUCT-GROUP-LIST (CDR L) G))
									     (k (PRODUCT-GROUP-LIST m g)))))))


;;-----------------------------------------------------------------------------------------------------------
#|
;; I was thinking about a better proof of len-products, based on the lemma len-1-1-equal.  I started on this, 
;; but got distracted.  Maybe I'll finish it later.

;;  we construct a list of all cosets of k in g generated by elements of h:

(defun prod-lcosets-aux (l k g)
  (if (consp l)
      (let ((cosets (prod-lcosets-aux (cdr l) k g))
            (coset (lcoset (car l) k g)))
	(if (member-equal coset cosets)
	    cosets
	  (cons coset cosets)))
    ()))

(defund prod-lcosets (h k g)
  (prod-lcosets-aux (elts h) k g))

;; (prod-lcosets h k g) is a dlist of cosets of k in g:

(defthm sublistp-prod-lcosets-aux
  (implies (and (subgroupp h g)
                (subgroupp k g)
		(sublistp l (elts h)))
	   (sublistp (prod-lcosets-aux l k g)
	             (lcosets k g))))

(defthmd sublistp-prod-lcosets
  (implies (and (subgroupp h g)
                (subgroupp k g))
	   (sublistp (prod-lcosets h k g)
	             (lcosets k g)))
  :hints (("Goal" :in-theory (enable prod-lcosets))))

(defthm dlistp-prod-lcosets-aux
  (implies (and (subgroupp h g)
                (subgroupp k g)
		(sublistp l (elts h)))
	   (dlistp (prod-lcosets-aux l k g))))

(defthm member-prod-lcosets-aux
  (implies (and (subgroupp h g)
                (subgroupp k g)
	        (sublistp l (elts h))
		(member-equal x l))
	   (member-equal (lcoset x k g)
	                 (prod-lcosets-aux l k g))))

(defthm member-prod-lcosets
  (implies (and (subgroupp h g)
                (subgroupp k g)
	        (in x h))
	   (member-equal (lcoset x k g)
	                 (prod-lcosets h k g)))
  :hints (("Goal" :in-theory (enable prod-lcosets))))

(defthm dlistp-prod-lcosets
  (implies (and (subgroupp h g)
                (subgroupp k g))
	   (dlistp (prod-lcosets h k g)))
  :hints (("Goal" :in-theory (enable prod-lcosets))))

;; Appending these cosets produces a dlist:

(defthm dlistp-append-list-prod-lcosets
  (implies (and (subgroupp h g)
                (subgroupp k g))
           (dlistp (append-list (prod-lcosets h k g))))
  :hints (("Goal" :use (sublistp-prod-lcosets))))
        
;; A function from (lcosets (group-intersection h k g) h) to (prod-lcosets h k g):

(defund lift-lcoset (c k g)
  (lcoset (car c) k g))

;; The inverse function:

(defund lower-lcoset (c h)
  (intersection-equal (elts h) c))

;; The plan is to prove that these functions are indeed inverses:

(defthm lower-lift
  (implies (member-equal c (lcosets (group-intersection h k g) h))
           (and (member-equal (lift-lcoset c k g)
	                      (prod-lcosets h k g))
	        (equal (lower-lcoset (lift-lcoset c k g) h)
		       c))))

(defthm lift-lower
  (implies (member-equal c (prod-lcosets h k g))
           (and (member-equal (lower-lcoset c h)
	                      (lcosets (group-intersection h k g) h))
	        (equal (lift-lcoset (lower-lcoset c h) k g)
		       c))))

;; Then apply len-1-1-equal to conclude that they have the same length:

(defthm len-prod-lcosets
  (iimplies (and (subgroupp h g)
                 (subgroupp k g))
            (equal (len (prod-lcosets h k g))
	           (/ (order h) (order (group-intersection h k g))))))

;; Since the length of each member of (prod-lcosets h k g) is (order k), this gives us the following:

(defthm len-append-list-prod-lcosets
  (iimplies (and (subgroupp h g)
                 (subgroupp k g))
            (equal (len (append-list (prod-lcosets h k g)))
	           (/ (* (order h) (order k))
		      (order (group-intersection h k g))))))

;; It remains to show that (append-list (prod-lcosets h k g) is a permutation of (products h k g).

(defthm member-append-list-products
  (iimplies (and (subgroupp h g)
                 (subgroupp k g)
                 (member-equal x (append-list (prod-lcosets h k g))))
	    (member-equal x (products h k g))))

(defthm member-append-list-products
  (implies (and (subgroupp h g)
                (subgroupp k g))
           (sublistp (append-list (prod-lcosets h k g))
	             (products h k g))))

(defthm member-products-append-list
  (iimplies (and (subgroupp h g)
                 (subgroupp k g)
                 (member-equal x (products h k g)))
	    (member-equal x (append-list (prod-lcosets h k g)))))

(defthm member-products-append-list
  (implies (and (subgroupp h g)
                (subgroupp k g))
           (sublistp (products h k g)
	             (append-list (prod-lcosets h k g)))))
	             
(defthmd len-products
  (implies (and (subgroupp h g)
                (subgroupp k g))
           (equal (len (products h k g))
                  (/ (* (order h) (order k))
                     (order (intersect-groups h k g))))))
|#
