(in-package "DM")

(include-book "quotients")
(local (include-book "support/maps"))

;;---------------------------------------------------------------------------------------------------------------
;; Maps
;;---------------------------------------------------------------------------------------------------------------

;; We define the notion of a map in order to introduce group homomorphisms into our theory.
;; A list m of conses is a map if (dlistp (strip-cars m)).  A map m may be viewed as a function
;; with domain (strip-cars m):

(defun cons-listp (m)
  (if (consp m)
      (and (consp (car m)) (cons-listp (cdr m)))
    (null m)))

(defund domain (m) (strip-cars m))

(defund mapp (m)
  (and (cons-listp m)
       (dlistp (domain m))))

;; The function mapply applies a map to an element of its domain:

(defund mapply (map x) (cdr (assoc-equal x map)))

;; The macro defmap provides a convenient method of defining maps.  The macro call
;;   (defmap name args domain val)
;; defines a family of maps parametrized by args with given domain, which must be a dlist.
;; The parameter val is the value that the map assigns to an element x of its domain:

(defmacro defmap (name args domain val)
  (let ((name-aux (intern$ (concatenate 'string (symbol-name name) "-AUX") "DM"))
        (mapp-name (intern$ (concatenate 'string "MAPP-" (symbol-name name)) "DM"))
        (cons-listp-name-aux (intern$ (concatenate 'string "CONS-LISTP-" (symbol-name name) "-AUX") "DM"))
        (domain-name (intern$ (concatenate 'string "DOMAIN-" (symbol-name name)) "DM"))
        (domain-name-aux (intern$ (concatenate 'string "DOMAIN-" (symbol-name name) "-AUX") "DM"))
        (name-val (intern$ (concatenate 'string (symbol-name name) "-VAL") "DM"))
        (name-aux-val (intern$ (concatenate 'string (symbol-name name) "-AUX-VAL") "DM")))
    `(encapsulate ()
       (set-ignore-ok t)
       (set-irrelevant-formals-ok t)
       (defun ,name-aux (l ,@args)
         (if (consp l)
	     (let ((x (car l)))
	       (cons (cons x ,val) (,name-aux (cdr l) ,@args)))
	   ()))
      (defund ,name ,args
        (,name-aux ,domain ,@args))
      (local-defthm ,cons-listp-name-aux
	(cons-listp (,name-aux l ,@args)))
      (local-defthm ,domain-name-aux
	(implies (dlistp l) (equal (domain (,name-aux l ,@args)) l))
	:hints (("Goal" :in-theory (enable domain))))
      (defthm ,domain-name
	(implies (dlistp ,domain) (equal (domain (,name ,@args)) ,domain))
	:hints (("Goal" :in-theory (enable ,name))))
      (defthm ,mapp-name
	(implies (dlistp ,domain) (mapp (,name ,@args)))
	:hints (("Goal" :in-theory (enable mapp ,name))))
      (local-defthm ,name-aux-val
        (implies (member-equal x l)
	         (equal (mapply (,name-aux l ,@args) x)
		        ,val))
        :hints (("Goal" :in-theory (enable mapply))))
      (defthm ,name-val
        (implies (member-equal x ,domain)
	         (equal (mapply (,name ,@args) x)
		        ,val))
        :hints (("Goal" :in-theory (enable ,name)))))))

;; For example, the projection of a group on the left cosets of a subgroup:

(defmap project-lcosets (h g)
  (elts g)
  (lcoset x h g))

;; The identity map on a dlist:

(defmap identity-map (d) d x)


;;---------------------------------------------------------------------------------------------------------------
;; Homomorphisms
;;---------------------------------------------------------------------------------------------------------------

;; A map is m is a homomorphism from a group g to a group h if the following conditions hold:
;;   (a) (sublistp (elts g) (domain map))
;;   (b) (implies (in x g) (in (mapply m x) h))
;;   (c) (equal (mapply m (e g)) (e h))
;;   (d) (implies (and (in x g) (in y g))
;;                (equal (mapply (op x y g)) (op (mapply m x) (mapply m y) h)))

;; The function codomain-cex searches the elements of g for a counter-example of (b):

(defun codomain-cex-aux (map l h)
  (if (consp l)
      (if (in (mapply map (car l)) h)
	  (codomain-cex-aux map (cdr l) h)
	(car l))
    ()))

(defund codomain-cex (map g h)
  (codomain-cex-aux map (elts g) h))

(defthm not-codomain-cex
  (implies (and (groupp g)
		(not (codomain-cex map g h))
		(in x g))
	   (in (mapply map x) h)))

;; This is useful in proving (not (codomain-cex map g h)):

(defthmd codomain-cex-lemma
  (let ((x (codomain-cex map g h)))
    (implies x
	     (and (in x g)
		  (not (in (mapply map x) h))))))

;; The function homomorphism-cex searches the elements of g for a counter-example of (d):

(defun homomorphism-cex-aux-1 (x l map g h)
  (if (consp l)
      (if (equal (op (mapply map x) (mapply map (car l)) h)
                 (mapply map (op x (car l) g)))
         (homomorphism-cex-aux-1 x (cdr l) map g h)
        (cons x (car l)))
    ()))

(defun homomorphism-cex-aux-2 (l map g h)
  (if (consp l)
      (or (homomorphism-cex-aux-1 (car l) (elts g) map g h)
          (homomorphism-cex-aux-2 (cdr l) map g h))
    ()))

(defund homomorphism-cex (map g h)
  (homomorphism-cex-aux-2 (elts g) map g h))

(defthm not-homomorphism-cex
  (implies (and (not (homomorphism-cex map g h))
		(in x g) (in y g))
	   (equal (mapply map (op x y g))
		  (op (mapply map x) (mapply map y) h))))

;; This is useful in proving (not (homomorphism-cex map g h)):

(defthmd homomorphismp-cex-lemma
  (let ((cex (homomorphism-cex map g h)))
    (implies cex
	     (and (in (car cex) g) (in (cdr cex) g)
	          (not (equal (op (mapply map (car cex)) (mapply map (cdr cex)) h)
                              (mapply map (op (car cex) (cdr cex) g))))))))

(defund homomorphismp (map g h)
  (and (groupp g)
       (groupp h)
       (sublistp (elts g) (domain map))
       (mapp map)
       (not (codomain-cex map g h))
       (equal (mapply map (e g)) (e h))
       (not (homomorphism-cex map g h))))

(defthm homomorphism-groupp
  (implies (homomorphismp map g h)
	   (and (groupp g)
		(groupp h))))

(defthm homomorphism-e
  (implies (homomorphismp map g h)
	   (equal (mapply map (e g)) (e h))))

(defthm homomorphism-op
  (implies (and (homomorphismp map g h)
	        (in x g)
	        (in y g))
	   (equal (mapply map (op x y g))
		  (op (mapply map x) (mapply map y) h))))

(defthm homomorphism-power
  (implies (and (homomorphismp map g h)
                (in x g)
		(natp n))
	   (equal (mapply map (power x n g))
	          (power (mapply map x) n h))))

(defthm homomorphism-codomain
  (implies (and (homomorphismp map g h)
	        (in x g))
	   (in (mapply map x) h)))

(defthm homomorphism-inv
  (implies (and (homomorphismp map g h)
	        (in x g))
	   (equal (mapply map (inv x g))
		  (inv (mapply map x) h))))

;; Composition of homomorphisms:

(defmap compose-maps (map2 map1)
  (domain map1)
  (mapply map2 (mapply map1 x)))

(defthm homomorphismp-compose-maps
  (implies (and (homomorphismp map1 g h)
                (homomorphismp map2 h k))
           (homomorphismp (compose-maps map2 map1) g k)))

;; The following macro saves us the trouble of explicitly invoking codomain-cex-lemma and homomorphismp-cex-lemma
;; to prove that a map is a homomorphism.  Before calling the macro, we must prove any rewrite rule needed to
;; establish each conjunct of the definition of homomorphismp.  Suppose we know that (mapply map x) will be rewritten
;; as some term (val x).  Then instead of proving (not (codomain-cex map g h)) and (not (homomorphism-cex map g h)),
;; we need only prove
;;   (implies (in x g) (in (val x) h)
;; and
;;   (implies (and (in x g) (in y g)) (equal (val (op x y g)) (op (val x) (val y) h)))
;; where 

(defmacro prove-homomorphismp (name map g h cond)
  `(defthm ,(intern$ (concatenate 'string "HOMOMORPHISMP-" (symbol-name name)) "DM")
     (implies ,cond (homomorphismp ,map ,g ,h))
     :hints (("Goal" :use ((:instance homomorphismp (map ,map) (g ,g) (h ,h))
		           (:instance codomain-cex-lemma (map ,map) (g ,g) (h ,h))
		  	   (:instance homomorphismp-cex-lemma (map ,map) (g ,g) (h ,h)))))))

;; In the first example, only one rewrite rule is required:

(defthm sublistp-subgroup-domain
  (implies (and (homomorphismp map g h)
                (subgroupp k g))
	   (sublistp (elts k) (domain map))))

(prove-homomorphismp subgroup map k h
  (and (homomorphismp map g h)
       (subgroupp k g)))

;; This results in the following:

(DEFTHMD HOMOMORPHISMP-SUBGROUP
  (IMPLIES (AND (HOMOMORPHISMP MAP G H)
                (SUBGROUPP K G))
           (HOMOMORPHISMP MAP K H)))

;; The next example, is even simpler, requiring no rewrite rules:

(prove-homomorphismp identity (identity-map (elts g)) g g
  (groupp g))

;; This results in the following, which says that the identity map on the element list of a group g ia a
;; homomorphism from g to g:

(DEFTHM HOMOMORPHISMP-IDENTITY
  (IMPLIES (GROUPP G)
	   (HOMOMORPHISMP (IDENTITY-MAP (ELTS G)) G G)))


;;---------------------------------------------------------------------------------------------------------------
;; Image of a Homomorphisms
;;---------------------------------------------------------------------------------------------------------------

;; The ordered list of values of a homomorphism:

(defun ielts-aux (map l h)
  (if (consp l)
      (insert (mapply map (car l))
	      (ielts-aux map (cdr l) h)
	      h)
    ()))

(defund ielts (map g h)
  (ielts-aux map (elts g) h))

(defthm ordp-ielts
  (implies (homomorphismp map g h)
	   (ordp (ielts map g h) h)))

(defthm dlistp-ielts
  (implies (homomorphismp map g h)
	   (dlistp (ielts map g h))))

;; This list forms a subgroup of the codomain:

(defthm sublistp-ielts
  (implies (homomorphismp map g h)
	   (sublistp (ielts map g h) (elts h))))

(defthm consp-ielts
  (implies (groupp g)
	   (consp (ielts map g h))))

(defthmd member-ielts
  (implies (and (homomorphismp map g h)
		(in x g))
	   (member-equal (mapply map x) (ielts map g h))))

(defthm ielts-identity
  (implies (homomorphismp map g h)
           (equal (car (ielts map g h))
		  (e h))))

(defun preimage-aux (x map l)
  (if (consp l)
      (if (equal x (mapply map (car l)))
	  (car l)
	(preimage-aux x map (cdr l)))
    ()))

(defund preimage (x map g)
  (preimage-aux x map (elts g)))

(defthmd image-preimage
  (implies (and (homomorphismp map g h)
	        (member-equal x (ielts map g h)))
	   (and (in (preimage x map g) g)
		(equal (mapply map (preimage x map g)) x))))

(defthm ielts-closed
  (implies (and (homomorphismp map g h)
	        (member-equal x (ielts map g h))
	        (member-equal y (ielts map g h)))
           (member-equal (op x y h) (ielts map g h))))

(defthm ielts-inverse
  (implies (and (homomorphismp map g h)
	        (member-equal x (ielts map g h)))
           (member-equal (inv x h) (ielts map g h))))

(defsubgroup image (map g) h
  (homomorphismp map g h)
  (ielts map g h))

(defthmd image-subgroup
  (implies (and (homomorphismp map g h)
                (subgroupp k g))
	   (subgroupp (image map k h) (image map g h))))

(defthmd homomorphismp-abelianp-image
  (implies (and (homomorphismp map g h)
                (abelianp g))
	   (abelianp (image map g h))))

;;---------------------------------------------------------------------------------------------------------------
;; Kernel of a Homomorphisms
;;---------------------------------------------------------------------------------------------------------------

;; The ordered list of element of the domain of a homomorphism that map to the identity:

(defun kelts-aux (map l h)
  (if (consp l)
      (if (equal (mapply map (car l)) (e h))
	  (cons (car l) (kelts-aux map (cdr l) h))
	(kelts-aux map (cdr l) h))
    ()))

(defund kelts (map g h)
  (kelts-aux map (elts g) h))

(defthm sublistp-kelts
  (sublistp (kelts map g h) (elts g)))

(defthm ordp-kelts
  (implies (groupp g)
	   (ordp (kelts map g h) g)))

(defthm dlistp-kelts
  (implies (groupp g)
           (dlistp (kelts map g h))))

;; This list forms a normal subgroup of the domain:

(defthm car-kelts
  (implies (homomorphismp map g h)
           (and (consp (kelts map g h))
	        (equal (car (kelts map g h))
		       (e g)))))

(defthmd member-kelts
  (iff (member-equal x (kelts map g h))
       (and (in x g) (equal (mapply map x) (e h)))))

(defthm kelts-closed
  (implies (and (homomorphismp map g h)
                (member-equal x (kelts map g h))
                (member-equal y (kelts map g h)))
	   (member-equal (op x y g) (kelts map g h))))

(defthm kelts-inv
  (implies (and (homomorphismp map g h)
                (member-equal x (kelts map g h)))
	   (member-equal (inv x g) (kelts map g h))))
  
(defsubgroup kernel (map h) g
  (homomorphismp map g h)
  (kelts map g h))

(defthm normalp-kernel
  (implies (homomorphismp map g h)
	   (normalp (kernel map h g) g)))

(defthmd kernel-iff
  (implies (and (homomorphismp map g h)
                (in x g)
		(in y g))
	   (iff (equal (mapply map x) (mapply map y))
	        (in (op (inv x g) y g) (kernel map h g)))))

;; Kernel of the restriction of a homomorphism to a subgroup of the domain:

(defthmd kernel-subgroup
  (implies (and (homomorphismp map g h)
                (subgroupp k g))
           (equal (kernel map h k)
	          (group-intersection k (kernel map h g) g))))

	   
;;---------------------------------------------------------------------------------------------------------------
;; Epimorphisms
;;---------------------------------------------------------------------------------------------------------------

;; An epimorphism is a surjective homomorphism:

(defund epimorphismp (map g h)
  (and (homomorphismp map g h)
       (equal (image map g h) h)))

(defthm epimorphism-homomorphism
  (implies (epimorphismp map g h)
           (homomorphismp map g h)))

;; Given a homomorphism map from g to h, suppose we can prove the following for some function foo:
;;   (implies (in x h)
;;            (and (in (foo x g h) g)
;;                 (equal (mapply map (foo x g h))
;;                        x)))
;; The we can prove that map is an epimorphism by combining member-ielts with the following:              

(defthmd homomorphism-epimorphism
  (implies (and (homomorphismp map g h)
                (sublistp (elts h) (ielts map g h)))
	   (epimorphismp map g h)))

;; The identity map is an epimorphism:

(defthm identity-epimorphism
  (implies (groupp g)
	   (epimorphismp (identity-map (elts g)) g g)))

;; Any homomorphism is an epimorphism onto its image:

(defthmd epimorphism-image
  (implies (homomorphismp map g h)
	   (epimorphismp map g (image map g h))))

(defthm kernel-image
  (implies (homomorphismp map g h)
           (equal (kernel map (image map g h) g)
	          (kernel map h g))))

;; The projection of g on the quotient of a normal subgroup is an epimorphism:

(defthm epimorphismp-project-normalp
  (implies (normalp h g)
	   (epimorphismp (project-lcosets h g) g (quotient g h))))


;;---------------------------------------------------------------------------------------------------------------
;; Endomorphisms
;;---------------------------------------------------------------------------------------------------------------

;; An endomorphism is an injective homomorphism:

(defund endomorphismp (map g h)
  (and (homomorphismp map g h)
       (equal (kernel map h g) (trivial-subgroup g))))

(defthm endomorphism-homomorphism
  (implies (endomorphismp map g h)
           (homomorphismp map g h)))

(defthmd endomorphismp-subgroup
  (implies (and (endomorphismp map g h)
                (subgroupp k g))
	   (endomorphismp map k h)))

(defthm endomorphism-1-1
  (implies (and (endomorphismp map g h)
		(in x g)
		(in y g)
		(equal (mapply map x) (mapply map y)))
	   (equal x y))
  :rule-classes ())

(defthm endomorphism-kernel-e
  (implies (and (endomorphismp map g h)
		(in x g)
		(equal (mapply map x) (e h)))
	   (equal x (e g)))
  :rule-classes ())

;; This is useful in proving that a homomorphism is an endomorphism:

(defthmd homomorphism-endomorphism
  (implies (and (homomorphismp map g h)
                (not (endomorphismp map g h)))
	   (and (in (cadr (kelts map g h)) g)
	        (equal (mapply map (cadr (kelts map g h)))
	               (e h))
	        (not (equal (cadr (kelts map g h)) (e g))))))

;; The identity map is an endomorphism:

(defthm identity-endomorphism
  (implies (groupp g)
	   (endomorphismp (identity-map (elts g)) g g)))

;; A composition of endomorphisms is an endomorphism:

(defthm endomorphismp-compose-maps
  (implies (and (endomorphismp map1 g h)
                (endomorphismp map2 h k))
	   (endomorphismp (compose-maps map2 map1) g k)))
  
;; Every homomorphism induces an endomorphism on the quotient of its kernel:

(defmap quotient-map (map g h)
  (lcosets (kernel map h g) g)
  (mapply map (car x)))

(defthmd endomorphismp-quotient-map
  (implies (homomorphismp map g h)
	   (endomorphismp (quotient-map map g h) (quotient g (kernel map h g)) h)))


;;---------------------------------------------------------------------------------------------------------------
;; Isomorphisms
;;---------------------------------------------------------------------------------------------------------------

;; An isomorphism is a bijective homomorphism:

(defund isomorphismp (map g h)
  (and (epimorphismp map g h)
       (endomorphismp map g h)))

(defthm isomorphism-homomorphism
  (implies (isomorphismp map g h)
           (homomorphismp map g h)))

(defthm isomorphism-epimorphism
  (implies (isomorphismp map g h)
           (epimorphismp map g h)))

(defthm isomorphism-groupp
  (implies (isomorphismp map g h)
           (and (groupp g)
	        (groupp h))))

(defthm isomorphism-endomorphism
  (implies (isomorphismp map g h)
           (endomorphismp map g h)))

(defthmd endomorphismp-isomorphismp
  (implies (endomorphismp map g h)
           (isomorphismp map g (image map g h))))

;; An endomorphism from g to h is an isomorphism iff (order g) = (order h): 

(defthmd isomorphism-equal-orders
  (implies (isomorphismp map g h)
	   (equal (order g) (order h))))

(defthmd equal-orders-isomorphism
  (implies (and (endomorphismp map g h)
	        (equal (order g) (order h)))
	   (isomorphismp map g h)))

;; An isomorphism has an inverse:

(defmap inv-isomorphism (map g h) (elts h) (preimage x map g))

(defthm map-inv
  (implies (and (isomorphismp map g h)
                (in x h))
	   (and (in (mapply (inv-isomorphism map g h) x) g)
	        (equal (mapply map (mapply (inv-isomorphism map g h) x))
		       x))))

(defthm inv-map
  (implies (and (isomorphismp map g h)
                (in x g))
	   (and (in (mapply map x) h)
	        (equal (mapply (inv-isomorphism map g h) (mapply map x))
		       x))))

(defthm isomorphismp-inv-e
  (implies (isomorphismp map g h)
           (equal (mapply (inv-isomorphism map g h) (e h))
	          (e g))))

(defthmd isomorphismp-inv
  (implies (isomorphismp map g h)
           (isomorphismp (inv-isomorphism map g h) h g)))

;; A consequence of endomorphismp-compose-maps, isomorphism-equal-orders, and equal-orders-isomorphism:

(defthm isomorphismp-compose-maps
  (implies (and (isomorphismp map1 g h)
                (isomorphismp map2 h k))
	   (isomorphismp (compose-maps map2 map1) g k)))
     
;; An automorphism is an isomorphism from a group to itself:

(defund automorphismp (map g)
  (isomorphismp map g g))

;; The identity map on (elts g) is an automorphism:

(defthmd identity-automorphism
  (implies (groupp g)
	   (automorphismp (identity-map (elts g)) g)))

;; If h is a subgroup of g of the same order as g (i.e., a reordering of g), then the identity map
;; is an isomorphism from g to h:

(defthm subgroup-isomorphism
  (implies (and (subgroupp h g)
                (equal (order h) (order g)))
	   (isomorphismp (identity-map (elts g)) g h)))

;; In particular, a cyclic group is isomorphic to the cyclic subgroup generated by a generator of the group:

(defthmd cyclicp-isomorphism
  (implies (cyclicp g)
           (isomorphismp (identity-map (elts g))
	                 g
			 (cyclic (group-gen g) g))))

;; It follows from homomorphismp-abelianp-image that a cyclic group is abelian:

(defthm cyclicp-abelianp
  (implies (cyclicp g)
           (abelianp g)))
