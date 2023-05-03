(in-package "DM")

(include-book "maps")
(local (include-book "support/products"))

;;-----------------------------------------------------------------------------------------------------------
;; Direct Products
;;-----------------------------------------------------------------------------------------------------------

;; The elements of the direct product of a list of groups:

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

(defthm dlistp-group-tuples
  (implies (group-list-p l)
	   (dlistp (group-tuples l))))

;; Each element is a list, the length of which is the length of l:

(defthmd len-group-tuple
  (implies (member-equal x (group-tuples l))
           (equal (len x) (len l))))

;; The number of elements is the product of the orders of the groups:

(defun product-orders (l)
  (if (consp l)
      (* (order (car l)) (product-orders (cdr l)))
    1))

(defthm len-group-tuples
  (implies (group-list-p l)
           (equal (len (group-tuples l))
                  (product-orders l))))

(defun e-list (l)
  (if (consp l)
      (cons (e (car l)) (e-list (cdr l)))
    ()))

(defthm car-group-tuples
  (implies (group-list-p l)
           (equal (car (group-tuples l))
		  (e-list l))))

(defthm member-e-list--group-tuples
  (implies (group-list-p l)
           (member-equal (e-list l) (group-tuples l))))

;; Group operation:

(defun dp-op (x y l)
  (if (consp l)
      (cons (op (car x) (car y) (car l))
            (dp-op (cdr x) (cdr y) (cdr l)))
    ()))

;; Inverse operator

(defun dp-inv (x l)
  (if (consp l)
      (cons (inv (car x) (car l))
            (dp-inv (cdr x) (cdr l)))
    ()))

(defgroup direct-product (gl)
  (and (group-list-p gl) (consp gl))
  (group-tuples gl)
  (dp-op x y gl)
  (dp-inv x gl))

;; Order of a direct-product:

(defthmd order-of-dp
  (implies (group-list-p l)
	   (equal (order (direct-product l))
		  (product-orders l))))

;; Identity element:

(defthm e-dp
  (implies (and (group-list-p l)
                (consp l))
	   (equal (e (direct-product l))
	          (e-list l))))


;; Test for membership:

(defthmd in-dp
  (implies (and (group-list-p l) (consp l))
	   (iff (in x (direct-product l))
		(and (consp x)
		     (in (car x) (car l))
		     (if (cdr l)
			 (in (cdr x) (direct-product (cdr l)))
		       (null (cdr x)))))))

(defthm member-group-tuples
  (implies (and (group-list-p l) (consp l))
	   (iff (member-equal x (group-tuples l))
		(and (consp x)
		     (in (car x) (car l))
		     (if (cdr l)
			 (member-equal (cdr x) (group-tuples (cdr l)))
		       (null (cdr x)))))))

;; Index of an element of a direct product:

(defthmd ind-dp
  (implies (and (group-list-p l)
                (consp l)
                (in x (direct-product l)))
	   (equal (ind x (direct-product l))
	          (if (cdr l)
	              (+ (* (ind (car x) (car l))
		            (order (direct-product (cdr l))))
		         (ind (cdr x) (direct-product (cdr l))))
		    (ind (car x) (car l))))))

;; Comparison of the indices of 2 elements of a direct product:

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
			    (ind (cdr y) (direct-product (cdr l)))))))))

;; Power of an element of a direct-product:

(defun dp-power (x n l)
  (if (consp l)
      (cons (power (car x) n (car l))
            (dp-power (cdr x) n (cdr l)))
    ()))

(defthmd power-dp
  (implies (and (group-list-p l)
                (consp l)
                (in x (direct-product l)))
	   (equal (power x n (direct-product l))
		  (dp-power x n l))))


;;-----------------------------------------------------------------------------------------------------------
;; List of Products of Two Subgroups
;;-----------------------------------------------------------------------------------------------------------

;; The ordered list of products of elements of subgroups h and k of g:

(defun products-aux (l g)
  (if (consp l)
      (insert (op (caar l) (cadar l) g)
              (products-aux (cdr l) g)
	      g)
    ()))

(defund products (h k g)
  (products-aux (group-tuples (list h k)) g))

(defthm ordp-products
  (implies (and (subgroupp h g)
                (subgroupp k g))
           (ordp (products h k g) g)))

(defthm dlistp-products
  (implies (and (subgroupp h g)
                (subgroupp k g))
           (dlistp (products h k g))))

;; (products h k g) contains every product:

(defthmd product-in-products
  (implies (and (subgroupp h g)
                (subgroupp k g)
                (in x h)
		(in y k))
	   (member-equal (op x y g) (products h k g))))

;; Every element of (products h k g) is a product and can be factored:

(defun factor-elt-aux (x l g)
  (if (consp l)
      (if (equal x (op (caar l) (cadar l) g))
          (car l)
	(factor-elt-aux x (cdr l) g))
    ()))

(defund factor-elt (x h k g)
  (factor-elt-aux x (group-tuples (list h k)) g))

(defthmd product-in-products-converse
  (implies (and (subgroupp h g)
                (subgroupp k g)
		(member-equal x (products h k g)))
	   (let ((p (factor-elt x h k g)))
	     (and (in (car p) h)
	          (in (cadr p) k)
		  (equal (op (car p) (cadr p) g) x)))))

;; If either subgroup is normal, then the product is a subgroup:

(defsubgroup product-group (h k) g
  (and (subgroupp h g)
       (subgroupp k g)
       (or (normalp h g) (normalp k g)))
  (products h k g))

;; If both subgroups are normal, then the product is a normal subgroup:

(defthmd normalp-product-group
  (implies (and (normalp h g)
                (normalp k g))
           (normalp (product-group h k g)
		    g)))

;; Subgroup product is an associative operation:

(defthmd product-group-assoc
  (implies (and (normalp h1 g)
                (normalp h2 g)
                (normalp h3 g))
	   (equal (product-group h1 (product-group h2 h3 g) g)
	          (product-group (product-group h1 h2 g) h3 g))))

;; The product of a subgroup h with the trivial subgrouyp is a permutation of h:

(defthmd product-trivial-group-order
  (implies (normalp h g)
           (and (equal (order (product-group (trivial-subgroup g) h g))
	               (order h))
		(equal (order (product-group h (trivial-subgroup g) g))
	               (order h)))))

(defthmd product-trivial-group-ordp
  (implies (and (normalp h g) (ordp (elts h) g))
           (and (equal (product-group (trivial-subgroup g) h g)
	               h)
		(equal (product-group h (trivial-subgroup g) g)
                       h))))


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

;; Given a list l of elements of (lcosets (group-intersection h k g) h), convert it to a list of elements of 
;; (lcosets k g) by replacing each member c of l with (lcoset (car c) k g):

(defun lift-cosets-aux (l k g)
  (if (consp l)
      (cons (lcoset (caar l) k g)
	    (lift-cosets-aux (cdr l) k g))
    ()))

;; Apply lift-cosets-aux to the full list (lcosets (group-intersection h k g) g):

(defund lift-cosets (h k g)
  (lift-cosets-aux (lcosets (group-intersection h k g) h) k g))

;; The result is a list of distinct elements of (lcosets k g):

(defthmd dlistp-lift-cosets
  (implies (and (subgroupp h g)
                (subgroupp k g))
	   (and (sublistp (lift-cosets h k g) (lcosets k g))
	        (dlistp (lift-cosets h k g)))))

;; Appending these lists yields a dlist. This follows from lcosets-disjointp-pairwise, dlistp-list-lcosets,
;; dlistp-list-sublist, disjointp-pairwise-sublistp, and dlistp-append-list:

(defthm dlistp-append-list-lift-cosets
  (implies (and (subgroupp h g)
                (subgroupp k g))
	   (dlistp (append-list (lift-cosets h k g)))))

;; The length of (lift-cosets h k g) is the length of (lcosets (group-intersection h k g) h),
;; which is (/ (order h) (order (intersect-groups h k g)))  Since the length of each member 
;; of the list is (order k), we have the following expression for the length of the appended
;; list:

(defthm len-append-list-lift-cosets
  (implies (and (subgroupp h g)
                (subgroupp k g))
           (equal (len (append-list (lift-cosets h k g)))
	          (/ (* (order h) (order k))
		     (order (group-intersection h k g))))))

;; It is easy to show that each member of (lift-cosets h k g) is a sublist of (products h k g):

(defthm sublistp-lift-cosets-product
  (implies (and (subgroupp h g)
                (subgroupp k g))
           (sublistp (append-list (lift-cosets h k g))
	             (products h k g))))

;; On the other hand, if x is an element of (products h k g), then x = (op a b g),
;; where a is in h and b is in k. Some member of (lcosets (group-intersection h k g) h)
;; contains a, as does the corresponding member of (lift-cosets h k g), which therefore
;; contains x.  Thus, we have the converse:

(defthm sublistp-product-append-list
  (implies (and (subgroupp h g)
                (subgroupp k g))
	   (sublistp (products h k g)
	             (append-list (lift-cosets h k g)))))

;; It follows that (products h k g) and (append-list (lift-cosets h k g)) have the
;; same length, and the desired result follows:

(defthmd len-products
  (implies (and (subgroupp h g)
                (subgroupp k g))
           (equal (len (products h k g))
                  (/ (* (order h) (order k))
                     (order (group-intersection h k g))))))


;;-----------------------------------------------------------------------------------------------------------
;; Internal Direct Products
;;-----------------------------------------------------------------------------------------------------------

;; The product of a list of normal subgroups of g is a normal subgroup of g:

(defun normal-list-p (l g)
  (if (consp l)
      (and (normalp (car l) g)
           (normal-list-p (cdr l) g))
    (null l)))

(defthm normal-list-group-list
  (implies (normal-list-p l g)
           (group-list-p l)))

(defun product-group-list (l g)
  (if (consp l)
      (product-group (car l) (product-group-list (cdr l) g) g)
    (trivial-subgroup g)))

(defthm normalp-product-group-list
  (implies (and (groupp g)
                (normal-list-p l g))
           (normalp (product-group-list l g) g)))

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
				 g))))

;; Given a non-nil list l of subgroups of g that satisfies the following predicate, we shall show
;; that (direct-product l) is isomorphic to (product-group-list l g):

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

(defthm groupp-product-group-list
  (implies (and (groupp g)
                (internal-direct-product-p l g))
           (groupp (product-group-list l g))))

(defthm subgroupp-product-group-list
  (implies (and (groupp g)
                (internal-direct-product-p l g))
           (subgroupp (product-group-list l g) g)))

;; a consequence of len-products:

(defthmd order-product-group-list
  (implies (and (groupp g)
                (consp l)
                (internal-direct-product-p l g))
           (equal (order (product-group-list l g))
	          (product-orders l))))

; The product of 2 non-intersecting internal direct products is an internal direct product:

(defthmd internal-direct-product-append
  (implies (and (internal-direct-product-p l g)
		(internal-direct-product-p m g)
		(equal (group-intersection (product-group-list l g)
		                           (product-group-list m g)
					   g)
		       (trivial-subgroup g)))                
           (internal-direct-product-p (append l m) g)))

;; The isomorphism is defined as follows:

(defun product-list-val (x g)
  (if (consp x)
      (if (consp (cdr x))
          (op (car x) (product-list-val (cdr x) g) g)
	(car x))
    ()))

(defmap product-list-map (gl g)
  (group-tuples gl)
  (product-list-val x g))

(defthmd isomorphismp-dp-product-list
  (implies (and (groupp g)
                (consp l)
                (internal-direct-product-p l g))
           (isomorphismp (product-list-map l g)
	                 (direct-product l)
			 (product-group-list l g))))

;; When the product of the orders is the order of g, the product group is g:

(defthmd isomorphismp-dp-idp
  (implies (and (groupp g)
                (consp l)
		(internal-direct-product-p l g)
                (= (product-orders l) (order g)))
           (isomorphismp (product-list-map l g)
	                 (direct-product l)
			 g)))

