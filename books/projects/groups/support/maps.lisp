(in-package "DM")

(include-book "groups")

;; A list m of conses is a map if (dlistp (strip-cars m).  A map m may be viewed as a function
;; with domain (strip-cars m):

(defun cons-listp (m)
  (if (consp m)
      (and (consp (car m)) (cons-listp (cdr m)))
    (null m)))

(defund domain (m) (strip-cars m))

(defund mapp (m)
  (and (cons-listp m)
       (dlistp (domain m))))

(defthm mapp-dlistp
  (implies (mapp map) (dlistp (domain map)))
  :hints (("Goal" :in-theory (enable mapp))))

;; The function mapply applies a map to an element of its domain:

(defund mapply (map x) (cdr (assoc-equal x map)))

;; The macro call
;;   (defmap name args domain val)
;; defines a family of maps parametrized by args with given domain, which must  be a dlist.
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

(local-defthm not-c-c-a
  (implies (and (not (member-equal () l))
		(not (codomain-cex-aux map l h))
		(member-equal x l))
	   (in (mapply map x) h)))

(defthm not-codomain-cex
  (implies (and (groupp g)
		(not (codomain-cex map g h))
		(in x g))
	   (in (mapply map x) h))
  :hints (("Goal" :in-theory (enable codomain-cex)
	          :use ((:instance not-c-c-a (l (elts g)))))))

(local-defthmd codomain-cex-aux-lemma
  (let ((x (codomain-cex-aux map l h)))
    (implies x
	     (and (member-equal x l)
		  (not (in (mapply map x) h)))))
  :hints (("Goal" :in-theory (enable domain mapply))))

;; This is useful in proving (not (codomain-cex map g h)):

(defthmd codomain-cex-lemma
  (let ((x (codomain-cex map g h)))
    (implies x
	     (and (in x g)
		  (not (in (mapply map x) h)))))
  :hints (("Goal" :in-theory (enable codomain-cex)
	   :use ((:instance codomain-cex-aux-lemma (l (elts g)))))))

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

(local-defthm not-h-c-a-1
  (implies (and (not (homomorphism-cex-aux-1 x l map g h))
		(member-equal y l))
	   (equal (op (mapply map x) (mapply map y) h)
                  (mapply map (op x y g)))))

(local-defthm not-h-c-a-2
  (implies (and (not (homomorphism-cex-aux-2 l map g h))
		(member-equal x l) (in y g))
	   (equal (op (mapply map x) (mapply map y) h)
                  (mapply map (op x y g)))))

(defthm not-homomorphism-cex
  (implies (and (not (homomorphism-cex map g h))
		(in x g) (in y g))
	   (equal (mapply map (op x y g))
		  (op (mapply map x) (mapply map y) h)))
  :hints (("Goal" :in-theory (enable homomorphism-cex)
	          :use ((:instance not-h-c-a-2 (l (elts g)))))))

(local-defthmd h-c-a-1
  (let ((cex (homomorphism-cex-aux-1 x l map g h)))
    (implies cex
	     (and (member (cdr cex) l)
		  (equal (car cex) x)
	          (not (equal (op (mapply map (car cex)) (mapply map (cdr cex)) h)
                              (mapply map (op (car cex) (cdr cex) g))))))))

(local-defthmd h-c-a-2
  (let ((cex (homomorphism-cex-aux-2 l map g h)))
    (implies cex
	     (and (member (car cex) l)
		  (in (cdr cex) g)
	          (not (equal (op (mapply map (car cex)) (mapply map (cdr cex)) h)
                              (mapply map (op (car cex) (cdr cex) g)))))))
  :hints (("Subgoal *1/1" :use ((:instance h-c-a-1 (x (car l)) (l (elts g)))))))

;; This is useful in proving (not (homomorphism-cex map g h)):

(defthmd homomorphismp-cex-lemma
  (let ((cex (homomorphism-cex map g h)))
    (implies cex
	     (and (in (car cex) g) (in (cdr cex) g)
	          (not (equal (op (mapply map (car cex)) (mapply map (cdr cex)) h)
                              (mapply map (op (car cex) (cdr cex) g)))))))
  :hints (("Goal" :in-theory (enable homomorphism-cex)
	          :use ((:instance h-c-a-2 (l (elts g)))))))

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
		(groupp h)))
  :hints (("Goal" :in-theory (enable homomorphismp))))

(defthm homomorphism-mapp
  (implies (homomorphismp map g h)
	   (mapp map))
  :hints (("Goal" :in-theory (enable homomorphismp))))

(defthm homomorphism-e
  (implies (homomorphismp map g h)
	   (equal (mapply map (e g)) (e h)))
  :hints (("Goal" :in-theory (enable homomorphismp))))

(defthm homomorphism-op
  (implies (and (homomorphismp map g h)
	        (in x g)
	        (in y g))
	   (equal (mapply map (op x y g))
		  (op (mapply map x) (mapply map y) h)))
  :hints (("Goal" :in-theory (enable homomorphismp))))

(defthm homomorphism-power
  (implies (and (homomorphismp map g h)
                (in x g)
		(natp n))
	   (equal (mapply map (power x n g))
	          (power (mapply map x) n h))))

(defthm homomorphism-codomain
  (implies (and (homomorphismp map g h)
	        (in x g))
	   (in (mapply map x) h))
  :hints (("Goal" :in-theory (enable homomorphismp))))

(defthm homomorphism-inv
  (implies (and (homomorphismp map g h)
	        (in x g))
	   (equal (mapply map (inv x g))
		  (inv (mapply map x) h)))
  :hints (("Goal" :use ((:instance homomorphism-op (x (inv x g)) (y x))
			(:instance inv-unique (g h) (y (mapply map (inv x g))) (x (mapply map x)))))))

;; The following macro saves us the trouble of explicitly invoking codomain-cex-lemma and homomorphismp-cex-lemma
;; to prove that a map is a homomorphism:

(defmacro prove-homomorphismp (name map g h cond)
  `(defthm ,(intern$ (concatenate 'string "HOMOMORPHISMP-" (symbol-name name)) "DM")
     (implies ,cond (homomorphismp ,map ,g ,h))
     :hints (("Goal" :use ((:instance homomorphismp (map ,map) (g ,g) (h ,h))
		           (:instance codomain-cex-lemma (map ,map) (g ,g) (h ,h))
		  	   (:instance homomorphismp-cex-lemma (map ,map) (g ,g) (h ,h)))))))

(defthm sublistp-subgroup-domain
  (implies (and (homomorphismp map g h)
                (subgroupp k g))
	   (sublistp (elts k) (domain map)))
  :hints (("Goal" :in-theory (enable homomorphismp)
                  :use ((:instance sublistp-sublistp (l (elts k)) (m (elts g)) (n (domain map)))))))

(prove-homomorphismp subgroup map k h
  (and (homomorphismp map g h)
       (subgroupp k g)))

(prove-homomorphismp identity (identity-map (elts g)) g g
  (groupp g))

(defmap compose-maps (map2 map1)
  (domain map1)
  (mapply map2 (mapply map1 x)))

(defthm homomorphismp-compose-maps
  (implies (and (homomorphismp map1 g h)
                (homomorphismp map2 h k))
           (homomorphismp (compose-maps map2 map1) g k))
  :hints (("goal" :in-theory (e/d (homomorphismp) (member-sublist))
                  :use (;(:instance homomorphismp (map (compose-maps map2 map1)) (h k))
                        (:instance codomain-cex-lemma (map (compose-maps map2 map1)) (h k))
                        (:instance homomorphismp-cex-lemma (map (compose-maps map2 map1)) (h k))
			(:instance member-sublist (x (e g)) (l (elts g)) (m (domain map1)))
			(:instance member-sublist (x (codomain-cex (compose-maps map2 map1) g k)) (l (elts g)) (m (domain map1)))
			(:instance member-sublist (x (car (homomorphism-cex (compose-maps map2 map1) g k))) (l (elts g)) (m (domain map1)))
			(:instance member-sublist (x (cdr (homomorphism-cex (compose-maps map2 map1) g k))) (l (elts g)) (m (domain map1)))
			(:instance member-sublist (x (op (car (homomorphism-cex (compose-maps map2 map1) g k))
			                             (cdr (homomorphism-cex (compose-maps map2 map1) g k))
						     g))
						  (l (elts g)) (m (domain map1)))))))

;; Image of a homomorphism:

(defun ielts-aux (map l h)
  (if (consp l)
      (insert (mapply map (car l))
	      (ielts-aux map (cdr l) h)
	      h)
    ()))

(defund ielts (map g h)
  (ielts-aux map (elts g) h))

(local-defthmd ordp-ielts-aux
  (implies (and (homomorphismp map g h)
		(sublistp l (elts g)))
	   (ordp (ielts-aux map l h) h)))

(defthm ordp-ielts
  (implies (homomorphismp map g h)
	   (ordp (ielts map g h) h))
  :hints (("Goal" :in-theory (enable ielts)
	   :use ((:instance ordp-ielts-aux (l (elts g)))))))

(defthm dlistp-ielts
  (implies (homomorphismp map g h)
	   (dlistp (ielts map g h)))
  :hints (("Goal" :in-theory (enable ielts)
	          :use ((:instance ordp-ielts-aux (l (elts g)))))))

(local-defthmd sublistp-ielts-aux
  (implies (and (homomorphismp map g h)
		(sublistp l (elts g)))
	   (sublistp (ielts-aux map l h) (elts h))))

(defthm sublistp-ielts
  (implies (homomorphismp map g h)
	   (sublistp (ielts map g h) (elts h)))
  :hints (("Goal" :in-theory (enable ielts)
	   :use ((:instance sublistp-ielts-aux (l (elts g)))))))

(local-defthmd consp-ielts-aux
  (implies (and (consp l)
		(sublistp l (elts g)))
	   (consp (ielts-aux map l h))))

(defthm consp-ielts
  (implies (groupp g)
	   (consp (ielts map g h)))
  :hints (("Goal" :in-theory (enable ielts)
	   :use ((:instance consp-ielts-aux (l (elts g)))))))

(local-defthmd member-ielts-aux
  (implies (and (homomorphismp map g h)
		(sublistp l (elts g))
		(member-equal x l))
	   (member-equal (mapply map x) (ielts-aux map l h))))

(defthmd member-ielts
  (implies (and (homomorphismp map g h)
		(in x g))
	   (member-equal (mapply map x) (ielts map g h)))
  :hints (("Goal" :in-theory (enable ielts)
	   :use ((:instance member-ielts-aux (l (elts g)))))))

(defthm ielts-identity
  (implies (homomorphismp map g h)
           (equal (car (ielts map g h))
		  (e h)))
  :hints (("Goal" :in-theory (enable e)
                  :use (homomorphism-e
		        (:instance member-ielts (x (e g)))
                        (:instance car-ordp-minimal (g h) (x (e h)) (l (ielts map g h))))
	          :expand ((ielts-aux map (car g) h)))))

(defun preimage-aux (x map l)
  (if (consp l)
      (if (equal x (mapply map (car l)))
	  (car l)
	(preimage-aux x map (cdr l)))
    ()))

(defund preimage (x map g)
  (preimage-aux x map (elts g)))

(local-defthmd image-preimage-aux
  (implies (and (homomorphismp map g h)
	        (member-equal x (ielts-aux map l h)))
	   (and (member-equal (preimage-aux x map l) l)
		(equal (mapply map (preimage-aux x map l)) x))))

(defthmd image-preimage
  (implies (and (homomorphismp map g h)
	        (member-equal x (ielts map g h)))
	   (and (in (preimage x map g) g)
		(equal (mapply map (preimage x map g)) x)))
  :hints (("Goal" :in-theory (enable ielts preimage)
	   :use ((:instance image-preimage-aux (l (elts g)))))))

(defthm ielts-closed
  (implies (and (homomorphismp map g h)
	        (member-equal x (ielts map g h))
	        (member-equal y (ielts map g h)))
           (member-equal (op x y h) (ielts map g h)))
  :hints (("Goal" :use (image-preimage
			(:instance image-preimage (x y))
			(:instance member-ielts (x (op (preimage x map g) (preimage y map g) g)))
			(:instance homomorphism-op (x (preimage x map g)) (y (preimage y map g)))))))

(defthm ielts-inverse
  (implies (and (homomorphismp map g h)
	        (member-equal x (ielts map g h)))
           (member-equal (inv x h) (ielts map g h)))
  :hints (("Goal" :use (image-preimage
			(:instance image-preimage (x y))
			(:instance member-ielts (x (inv (preimage x map g) g)))
			(:instance homomorphism-op (x (inv (preimage x map g) g)) (y (preimage x map g)))))))

(defsubgroup image (map g) h
  (homomorphismp map g h)
  (ielts map g h))

(local-defthm sublistp-ielts-subgroup
  (implies (and (homomorphismp map g h)
                (subgroupp k g)
		(sublistp l (ielts map k h)))
	   (sublistp l (ielts map g h)))
  :hints (("Subgoal *1/3" :use ((:instance image-preimage (g k) (x (car l)))
                                (:instance member-ielts (x (preimage (car l) map k)))))))

(defthmd image-subgroup
  (implies (and (homomorphismp map g h)
                (subgroupp k g))
	   (subgroupp (image map k h) (image map g h)))
  :hints (("Goal" :use ((:instance subgroup-subgroup (g h) (h (image map k h)) (k (image map g h)))))))

(defthmd homomorphismp-abelianp-image
  (implies (and (homomorphismp map g h)
                (abelianp g))
	   (abelianp (image map g h)))
  :hints (("Goal" :in-theory (disable group-abelianp homomorphism-op)
                  :use ((:instance not-abelianp-cex (g (image map g h)))
                        (:instance image-preimage (x (car (abelianp-cex (image map g h)))))
                        (:instance image-preimage (x (cadr (abelianp-cex (image map g h)))))
			(:instance group-abelianp (x (preimage (car (abelianp-cex (image map g h))) map g))
			                          (y (preimage (cadr (abelianp-cex (image map g h))) map g)))
			(:instance homomorphism-op (x (preimage (car (abelianp-cex (image map g h))) map g))
			                           (y (preimage (cadr (abelianp-cex (image map g h))) map g)))
			(:instance homomorphism-op (x (preimage (cadr (abelianp-cex (image map g h))) map g))
			                           (y (preimage (car (abelianp-cex (image map g h))) map g)))))))

;; Kernel of a homomorphism:

(defun kelts-aux (map l h)
  (if (consp l)
      (if (equal (mapply map (car l)) (e h))
	  (cons (car l) (kelts-aux map (cdr l) h))
	(kelts-aux map (cdr l) h))
    ()))

(defund kelts (map g h)
  (kelts-aux map (elts g) h))

(local-defthm sublistp-kelts-aux
  (sublistp (kelts-aux map l h) l))

(defthm sublistp-kelts
  (sublistp (kelts map g h) (elts g))
  :hints (("Goal" :in-theory (enable kelts))))

(local-defthm dlistp-kelts-aux
  (implies (dlistp l)
           (dlistp (kelts-aux map l h))))

(defthm dlistp-kelts
  (implies (groupp g)
           (dlistp (kelts map g h)))
  :hints (("Goal" :in-theory (enable kelts))))

(defthm car-kelts
  (implies (homomorphismp map g h)
           (and (consp (kelts map g h))
	        (equal (car (kelts map g h))
		       (e g))))
  :hints (("Goal" :in-theory (enable e kelts)
                  :use (homomorphism-e)
	          :expand ((kelts-aux map (car g) h)))))

(local-defthm member-kelts-aux
  (iff (member-equal x (kelts-aux map l h))
       (and (member x l) (equal (mapply map x) (e h)))))

(defthmd member-kelts
  (iff (member-equal x (kelts map g h))
       (and (in x g) (equal (mapply map x) (e h))))
  :hints (("Goal" :in-theory (enable kelts))))

(defthm kelts-closed
  (implies (and (homomorphismp map g h)
                (member-equal x (kelts map g h))
                (member-equal y (kelts map g h)))
	   (member-equal (op x y g) (kelts map g h)))
  :hints (("Goal" :use (member-kelts
                        (:instance member-kelts (x y))
                        (:instance member-kelts (x (op x y g)))))))

(defthm kelts-inv
  (implies (and (homomorphismp map g h)
                (member-equal x (kelts map g h)))
	   (member-equal (inv x g) (kelts map g h)))
  :hints (("Goal" :use (member-kelts
                        (:instance member-kelts (x (inv x g)))))))
  
(defsubgroup kernel (map h) g
  (homomorphismp map g h)
  (kelts map g h))

(local-defthmd conj-kernel
  (implies (and (homomorphismp map g h)
                (in x (kernel map h g))
		(in y g))
	   (in (conj x y g) (kernel map h g)))
  :hints (("Goal" :in-theory (enable conj)
                  :use (member-kelts
		        (:instance member-kelts (x (conj x y g)))))))

(defthm normalp-kernel
  (implies (homomorphismp map g h)
	   (normalp (kernel map h g) g))
  :hints (("Goal" :use ((:instance not-normalp-cex (h (kernel map h g)))
                        (:instance conj-kernel (x (car (normalp-cex (kernel map h g) g)))
			                       (y (cadr (normalp-cex (kernel map h g) g))))))))

(defthmd kernel-iff-1
  (implies (and (homomorphismp map g h)
                (in x g)
		(in y g))
	   (equal (mapply map (op (inv x g) y g))
	          (op (inv (mapply map x) h)
		      (mapply map y)
		      h))))

(defthmd kernel-iff
  (implies (and (homomorphismp map g h)
                (in x g)
		(in y g))
	   (iff (equal (mapply map x) (mapply map y))
	        (in (op (inv x g) y g) (kernel map h g))))
  :hints (("Goal" :in-theory (disable homomorphism-op homomorphism-inv)
                  :use (kernel-iff-1
                        (:instance member-kelts (x (op (inv x g) y g)))
			(:instance group-assoc (g h) (x (mapply map x)) (y (inv (mapply map x) h)) (z (mapply map y)))
                        (:instance left-cancel (a (mapply map x))
			                       (x (op (inv (mapply map x) h) (mapply map y) h))
					       (y (e h))
					       (g h))))))

(local-defthm ordp-kelts-aux
  (implies (and (sublistp l (elts g)) (ordp l g))
	   (and (ordp (kelts-aux map l h) g)
	        (or (endp (kelts-aux map l h))
		    (<= (ind (car l) g) (ind (car (kelts-aux map l h)) g))))))

(defthm ordp-kelts
  (implies (groupp g)
	   (ordp (kelts map g h) g))
  :hints (("Goal" :in-theory (enable kelts))))
 

(defthmd member-kelts-int
  (implies (and (homomorphismp map g h)
                (subgroupp k g))
	   (iff (member-equal x (kelts map k h))
	        (member-equal x (intersection-equal (elts k) (kelts map g h)))))
  :hints (("Goal" :use (member-kelts
                        (:instance member-kelts (g k))))))

(defthmd sublistp-kelts-int
  (implies (and (homomorphismp map g h)
                (subgroupp k g))
	   (and (sublistp (kelts map k h) (intersection-equal (elts k) (kelts map g h)))
	        (sublistp (intersection-equal (elts k) (kelts map g h)) (kelts map k h))))
  :hints (("Goal" :use ((:instance scex1-lemma (l (kelts map k h)) (m (intersection-equal (elts k) (kelts map g h))))
                        (:instance scex1-lemma (m (kelts map k h)) (l (intersection-equal (elts k) (kelts map g h))))
			(:instance member-kelts-int (x (scex1 (kelts map k h) (intersection-equal (elts k) (kelts map g h)))))
			(:instance member-kelts-int (x (scex1 (intersection-equal (elts k) (kelts map g h)) (kelts map k h)))))))) 

(defthmd equal-kelts-int
  (implies (and (homomorphismp map g h)
                (subgroupp k g))
           (equal (kelts map k h) (intersection-equal (elts k) (kelts map g h))))
  :hints (("Goal" :use (sublistp-kelts-int
                        (:instance ordp-equal (g k) (x (kelts map k h)) (y (intersection-equal (elts k) (kelts map g h))))
			(:instance ordp-int-elts (h k) (l (kelts map g h)))))))

(defthmd kernel-subgroup
  (implies (and (homomorphismp map g h)
                (subgroupp k g))
           (equal (kernel map h k)
	          (group-intersection k (kernel map h g) g)))
  :hints (("Goal" :in-theory (disable subgroupp-group-intersection)
                  :use (equal-kelts-int
			(:instance subgroupp-group-intersection (h k) (k (kernel map h g)))
			(:instance subgroupp-transitive (h (kernel map h k)))
			(:instance subgroups-equal-elts (h (kernel map h k)) (k (group-intersection k (kernel map h g) g)))))))

;; An epimorphism is a surjective homomorphism:

(defund epimorphismp (map g h)
  (and (homomorphismp map g h)
       (equal (image map g h) h)))

(defthm epimorphism-homomorphism
  (implies (epimorphismp map g h)
           (homomorphismp map g h))
  :hints (("Goal" :in-theory (enable epimorphismp))))

(defthmd equal-ielts-elts
  (implies (and (homomorphismp map g h)
                (sublistp (elts h) (ielts map g h)))
	   (equal (ielts map g h)
	          (elts h)))
  :hints (("Goal" :use ((:instance equal-l-elts (g h) (l (ielts map g h)))))))

(defthmd homomorphism-epimorphism
  (implies (and (homomorphismp map g h)
                (sublistp (elts h) (ielts map g h)))
	   (epimorphismp map g h))
  :hints (("Goal" :in-theory (enable epimorphismp)
                  :use (equal-ielts-elts
                        (:instance subgroups-equal-elts (g h) (k (image map g h)))))))

(local-defthm ielts-aux-identity
  (implies (sublistp l (elts g))
           (sublistp l (ielts-aux (identity-map (elts g)) l g))))

(local-defthm sublistp-ielts-identity
  (sublistp (elts g) (ielts (identity-map (elts g)) g g))
  :hints (("Goal" :in-theory (enable ielts))))

(defthm identity-epimorphism
  (implies (groupp g)
	   (epimorphismp (identity-map (elts g)) g g))
  :hints (("Goal" :use ((:instance homomorphism-epimorphism (map (identity-map (elts g))) (h g))))))

(local-defthm ordp-car
  (implies (and (ordp l g)
		(member y (cdr l)))
	   (< (ind (car l) g) (ind y g))))

(local-defthmd ordp-ind-<
  (implies (and (ordp l g)
		(member x l)
		(member y l)
	        (< (index x l) (index y l)))
	   (< (ind x g) (ind y g))))

(local-defthmd ordp-ind-=
  (implies (and (ordp l g)
		(dlistp (car g))
		(member x l)
		(member y l)
	        (equal (index x l) (index y l)))
	   (equal (ind x g) (ind y g))))

(local-defthmd ordp-ind-iff
  (implies (and (ordp l g)
		(dlistp (car g))
		(member x l)
		(member y l))
	   (and (iff (equal (index x l) (index y l))
	             (equal (ind x g) (ind y g)))
		(iff (< (index x l) (index y l))
	             (< (ind x g) (ind y g)))))
  :hints (("Goal" :use (ordp-ind-< ordp-ind-=
			(:instance ordp-ind-< (x y) (y x))
			(:instance ordp-ind-= (x y) (y x))))))		

(local-defthmd ordp-insert-equal
  (implies (and (groupp h)
		(ordp (elts k) h)
		(dlistp l)
		(sublistp l (car k))
		(ordp l h)
		(in x k))
	   (equal (insert x l k)
		  (insert x l h)))
  :hints (("Subgoal *1/3" :use((:instance ordp-ind-iff (l (elts k)) (g h) (y (car l)))))
	  ("Subgoal *1/2" :use((:instance ordp-ind-iff (l (elts k)) (g h) (y (car l)))))))

(local-defthmd sublistp-ielts-aux-ielts
  (implies (and (homomorphismp map g h)
                (sublistp l (elts g)))
           (sublistp (ielts-aux map l h) (ielts map g h)))
  :hints (("Goal" :in-theory (enable ielts))
          ("Subgoal *1/1" :use ((:instance member-ielts (x (car l)))))))

(local-defthmd ielts-aux-image
  (implies (and (homomorphismp map g h)
		(sublistp l (elts g)))
	   (equal (ielts-aux map l (image map g h))
		  (ielts-aux map l h)))
  :hints (("Subgoal *1/1" :use ((:instance ordp-ielts-aux (l (cdr l)))
                                (:instance member-ielts (x (car l)))
				(:instance sublistp-ielts-aux-ielts (l (cdr l)))
				(:instance ordp-insert-equal (l (ielts-aux map (cdr l) h))
					                     (k (image map g h))
							     (x (mapply map (car l))))))))

(defthmd ielts-image
  (implies (homomorphismp map g h)
	   (equal (ielts map g (image map g h))
		  (ielts map g h)))
  :hints (("Goal" :in-theory (enable ielts)
                  :use ((:instance ielts-aux-image (l (elts g)))))))

(local-defthm not-codomain-cex-image
  (implies (homomorphismp map g h)
           (not (codomain-cex map g (image map g h))))
  :hints (("Goal" :use (ielts-image
                        (:instance codomain-cex-lemma (h (image map g h)))
		        (:instance member-ielts (x (codomain-cex map g (image map g h))))))))

(local-defthm not-homomorphism-cex-image
  (implies (homomorphismp map g h)
           (not (homomorphism-cex map g (image map g h))))
  :hints (("Goal" :in-theory (enable homomorphismp)
                  :use (ielts-image
                        (:instance homomorphismp-cex-lemma (h (image map g h)))
			(:instance not-homomorphism-cex (x (car (homomorphism-cex map g (image map g h))))
			                                (y (cdr (homomorphism-cex map g (image map g h)))))							
		        (:instance member-ielts (x (car (homomorphism-cex map g (image map g h)))))
		        (:instance member-ielts (x (cdr (homomorphism-cex map g (image map g h)))))))))

(defthm homomorphismp-image
  (implies (homomorphismp map g h)
           (homomorphismp map g (image map g h)))
  :hints (("Goal" :in-theory (e/d (homomorphismp) (subgroupp-image))
                  :use (subgroupp-image))))
			                        
(defthm image-image
  (implies (homomorphismp map g h)
	   (equal (image map g (image map g h))
		  (image map g h)))
  :hints (("Goal" :use (ielts-image
                        (:instance subgroupp-transitive (g h) (h (image map g (image map g h))) (k (image map g h)))
                        (:instance subgroups-equal-elts (g h)
			                                (h (image map g (image map g h)))
			                                (k (image map g h)))))))

(defthmd epimorphism-image
  (implies (homomorphismp map g h)
	   (epimorphismp map g (image map g h)))
  :hints (("Goal" :in-theory (enable epimorphismp))))

(local-defthm kelts-aux-image
  (implies (subgroupp i h)
           (equal (kelts-aux map l i)
	          (kelts-aux map l h))))

(defthmd kelts-image
  (implies (subgroupp i h)
           (equal (kelts map g i)
	          (kelts map g h)))
  :hints (("Goal" :in-theory (enable kelts))))

(defthm kernel-image
  (implies (homomorphismp map g h)
           (equal (kernel map (image map g h) g)
	          (kernel map h g)))
  :hints (("Goal" :in-theory (disable subgroupp-kernel homomorphismp-image)
                  :use (homomorphismp-image subgroupp-kernel
                        (:instance kelts-image (i (image map g h)))			
			(:instance subgroupp-kernel (h (image map g h)))
                        (:instance subgroups-equal-elts (h (kernel map (image map g h) g)) (k (kernel map h g)))))))

;; The projection of g on the quotient of a normal subgroup is an epimorphism:

(defthmd in-lcoset-quotient
  (implies (and (normalp h g)
	        (in x g))
	   (in (lcoset x h g)
	       (quotient g h)))
  :hints (("Goal" :use ((:instance member-lcoset-qlist-iff (x (lcoset x h g)))))))

(defthm codomain-cex-project-normalp
  (implies (normalp h g)
           (not (codomain-cex (project-lcosets h g) g (quotient g h))))
  :hints (("Goal" :use ((:instance codomain-cex-lemma (map (project-lcosets h g)) (h (quotient g h)))
                        (:instance in-lcoset-quotient (x (codomain-cex (project-lcosets h g) g (quotient g h))))))))

(defthmd lcoset-x-y
  (implies (and (normalp h g)
                (in x g)
		(in y g))
	   (equal (lcoset (op x y g) h g)
	          (op (lcoset x h g) (lcoset y h g) (quotient g h))))
  :hints (("Goal" :use ((:instance op-quotient-lcoset (x (lcoset x h g)) (y (lcoset y h g)) (a x) (b y))))))

(defthm homomorphism-cex-project-normalp
  (implies (normalp h g)
           (not (homomorphism-cex (project-lcosets h g) g (quotient g h))))
  :hints (("Goal" :use ((:instance homomorphismp-cex-lemma (map (project-lcosets h g)) (h (quotient g h)))
                        (:instance lcoset-x-y (x (car (homomorphism-cex (project-lcosets h g) g (quotient g h))))
			                      (y (cdr (homomorphism-cex (project-lcosets h g) g (quotient g h)))))))))

(defthm homomorphismp-project-normalp
  (implies (normalp h g)
	   (homomorphismp (project-lcosets h g) g (quotient g h)))
  :hints (("Goal" :in-theory (enable homomorphismp))))

(defthm epimorphismp-project-normalp-1
  (implies (and (normalp h g)
                (in x (quotient g h)))
	   (member-equal x (ielts (project-lcosets h g) g (quotient g h))))
  :hints (("Goal" :use (member-lcoset-qlist-iff
                        (:instance member-ielts (x (car x)) (map (project-lcosets h g)) (h (quotient g h)))
                        (:instance lcosets-cars (c x))))))

(defthmd epimorphismp-project-normalp-2
  (implies (normalp h g)
           (sublistp (elts (quotient g h))
	             (ielts (project-lcosets h g) g (quotient g h))))
  :hints (("Goal" :use ((:instance scex1-lemma (l (elts (quotient g h))) (m (ielts (project-lcosets h g) g (quotient g h))))))))

(defthm epimorphismp-project-normalp
  (implies (normalp h g)
	   (epimorphismp (project-lcosets h g) g (quotient g h)))
  :hints (("Goal" :use (epimorphismp-project-normalp-2
                        (:instance homomorphism-epimorphism (map (project-lcosets h g)) (h (quotient g h)))))))


;; An endomorphism is a homomorphism with trivial kernel:

(defund endomorphismp (map g h)
  (and (homomorphismp map g h)
       (equal (kernel map h g) (trivial-subgroup g))))

(defthm endomorphism-homomorphism
  (implies (endomorphismp map g h)
           (homomorphismp map g h))
  :hints (("Goal" :in-theory (enable endomorphismp))))

(defthmd endomorphismp-subgroup
  (implies (and (endomorphismp map g h)
                (subgroupp k g))
	   (endomorphismp map k h))
  :hints (("Goal" :in-theory (enable endomorphismp homomorphismp-subgroup)
                  :use (kernel-subgroup))))

(local-defthmd endo-1
  (implies (and (homomorphismp map g h)
                (in x g)
		(in y g)
		(equal (mapply map x) (mapply map y)))
	   (equal (mapply map (op (inv x g) y g))
	          (e h))))

(local-defthmd endo-2
  (implies (and (homomorphismp map g h)
                (in x g)
		(in y g)
		(equal (mapply map x) (mapply map y)))
	   (in (op (inv x g) y g)
	       (kernel map h g)))
  :hints (("Goal" :use (endo-1
                        (:instance member-kelts (x (op (inv x g) y g)))))))

(defthm endomorphism-1-1
  (implies (and (endomorphismp map g h)
		(in x g)
		(in y g)
		(equal (mapply map x) (mapply map y)))
	   (equal x y))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable endomorphismp trivial-subgroup)
                  :use (endo-2
		        (:instance left-cancel (a (inv x g)))))))

(defthm endomorphism-kernel-e
  (implies (and (endomorphismp map g h)
		(in x g)
		(equal (mapply map x) (e h)))
	   (equal x (e g)))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable e)
                  :use (homomorphism-e (:instance endomorphism-1-1 (y (e g)))))))

;; This is useful in proving that a homomorphism is an endomorphism:

(defthmd homomorphism-endomorphism
  (implies (and (homomorphismp map g h)
                (not (endomorphismp map g h)))
	   (and (in (cadr (kelts map g h)) g)
	        (equal (mapply map (cadr (kelts map g h)))
	               (e h))
	        (not (equal (cadr (kelts map g h)) (e g)))))
  :hints (("Goal" :in-theory (enable endomorphismp)
                  :use ((:instance not-trivial-elt (h (kernel map h g)))
		        (:instance member-kelts (x (cadr (kelts map g h))))))))

(defthm identity-endomorphism
  (implies (groupp g)
	   (endomorphismp (identity-map (elts g)) g g))
  :hints (("Goal" :use ((:instance homomorphism-endomorphism (map (identity-map (elts g))) (h g))))))

(defthm endomorphismp-compose-maps
  (implies (and (endomorphismp map1 g h)
                (endomorphismp map2 h k))
	   (endomorphismp (compose-maps map2 map1) g k))
  :hints (("Goal" :in-theory (enable endomorphismp)
                  :use ((:instance homomorphism-endomorphism (h k) (map (compose-maps map2 map1)))
                        (:instance endomorphism-1-1 (map map1) (x (cadr (kelts (compose-maps map2 map1) g k))) (y (e g)))
			(:instance endomorphism-1-1 (map map2) (g h) (h k)
			                            (x (mapply map1 (cadr (kelts (compose-maps map2 map1) g k))))
						    (y (e h)))))))

;; Every homomorphism induces an endomorphism on the quotient of its kernel:

(defmap quotient-map (map g h)
  (lcosets (kernel map h g) g)
  (mapply map (car x)))

(local-defthm quotient-map-x-in-h
  (implies (and (homomorphismp map g h)
                (in x (quotient g (kernel map h g))))
	   (in (mapply map (car x)) h))
  :hints (("Goal" :in-theory (enable member-lcoset-qlist-iff)
                  :use ((:instance lcosets-cars (c x) (h (kernel map h g)))))))

(local-defthm quotient-map-codomain-cex
  (implies (homomorphismp map g h)
           (not (codomain-cex (quotient-map map g h) (quotient g (kernel map h g)) h)))
  :hints (("Goal" :in-theory (enable member-lcoset-qlist-iff)
                  :use ((:instance codomain-cex-lemma (map (quotient-map map g h)) (g (quotient g (kernel map h g))))))))

(defthmd inv-car-lcoset
  (implies (and (subgroupp h g)
                (in x g))
	   (in (op (inv x g) (car (lcoset x h g)) g) h))
  :hints (("Goal" :use ((:instance equal-lcosets-iff (y (car (lcoset x h g))))
                        (:instance lcosets-cars (c (lcoset x h g)))))))

(local-defthm quotient-map-op
  (implies (and (homomorphismp map g h)
                (in x (quotient g (kernel map h g)))
                (in y (quotient g (kernel map h g))))
	   (equal (mapply (quotient-map map g h) (lcoset (op (car x) (car y) g) (kernel map h g) g))
	          (op (mapply map (car x)) (mapply map (car y)) h)))
  :hints (("Goal" :in-theory (enable member-lcoset-qlist-iff)
                  :use ((:instance kernel-iff (x (op (car x) (car y) g))
                                              (y (car (lcoset (op (car x) (car y) g) (kernel map h g) g))))
			(:instance inv-car-lcoset (h (kernel map h g)) (x (op (car x) (car y) g)))
			(:instance lcosets-cars (h (kernel map h g)) (c x))
			(:instance lcosets-cars (h (kernel map h g)) (c y))
			(:instance lcosets-cars (h (kernel map h g)) (c (lcoset (op (car x) (car y) g) (kernel map h g) g)))))))

(local-defthm quotient-map-homomorphismp-cex
  (implies (homomorphismp map g h)
           (not (homomorphism-cex (quotient-map map g h) (quotient g (kernel map h g)) h)))
  :hints (("Goal" :in-theory (enable lcosets-cars member-lcoset-cosets member-lcoset-qlist-iff)
                  :use ((:instance homomorphismp-cex-lemma (map (quotient-map map g h)) (g (quotient g (kernel map h g))))))))

(local-defthm homomorphismp-quotient-map
  (implies (homomorphismp map g h)
	   (homomorphismp (quotient-map map g h) (quotient g (kernel map h g)) h))
  :hints (("Goal" :in-theory (enable member-lcoset-qlist-iff homomorphismp)
                  :use ((:instance scex1-lemma (l (qlist (kernel map h g) g)) (m (lcosets (kernel map h g) g)))))))

(local-defthm quotient-map-e-1
  (implies (and (homomorphismp map g h)
                (in x (quotient g (kernel map h g)))
	        (equal (mapply (quotient-map map g h) x) (e h)))
	   (equal (lcoset (e g) (kernel map h g) g)
	          x))
  :hints (("Goal" :in-theory (enable member-lcoset-qlist-iff)
                  :use ((:instance equal-lcosets-iff (y (car x)) (x (e g)) (h (kernel map h g)))
		        (:instance member-kelts (x (car x)))			
			(:instance lcosets-cars (h (kernel map h g)) (c x))
			(:instance lcosets-cars (h (kernel map h g)) (c (lcoset (e g) (kernel map h g) g)))))))

(defthmd e-quotient
  (implies (normalp h g)
           (equal (e (quotient g h))
	          (lcoset (e g) h g)))
  :hints (("Goal" :in-theory (enable e))))

(local-defthmd quotient-map-e
  (implies (homomorphismp map g h)
	   (equal (e (quotient g (kernel map h g)))
	          (lcoset (e g) (kernel map h g) g)))
  :hints (("Goal" :in-theory (enable e-quotient))))

(defthmd endomorphismp-quotient-map
  (implies (homomorphismp map g h)
	   (endomorphismp (quotient-map map g h) (quotient g (kernel map h g)) h))
  :hints (("Goal" :in-theory (disable normalp-kernel)
                  :use (quotient-map-e
                        (:instance homomorphism-endomorphism (map (quotient-map map g h)) (g (quotient g (kernel map h g))))))))
			

;; An isomorphism is a bijective homomorphism:

(defund isomorphismp (map g h)
  (and (epimorphismp map g h)
       (endomorphismp map g h)))

(defthm isomorphism-homomorphism
  (implies (isomorphismp map g h)
           (homomorphismp map g h))
  :hints (("Goal" :in-theory (enable endomorphismp isomorphismp))))

(defthm isomorphism-epimorphism
  (implies (isomorphismp map g h)
           (epimorphismp map g h))
  :hints (("Goal" :in-theory (enable isomorphismp))))

(defthm isomorphism-groupp
  (implies (isomorphismp map g h)
           (and (groupp g)
	        (groupp h)))
  :hints (("Goal" :in-theory (enable epimorphismp endomorphismp isomorphismp))))

(defthm isomorphism-endomorphism
  (implies (isomorphismp map g h)
           (endomorphismp map g h))
  :hints (("Goal" :in-theory (enable isomorphismp))))

(defthmd endomorphismp-isomorphismp
  (implies (endomorphismp map g h)
           (isomorphismp map g (image map g h)))
  :hints (("Goal" :in-theory (enable epimorphism-image endomorphismp isomorphismp))))

;; An isomorphism has an inverse:

(defmap inv-isomorphism (map g h) (elts h) (preimage x map g))

(defthm map-inv
  (implies (and (isomorphismp map g h)
                (in x h))
	   (and (in (mapply (inv-isomorphism map g h) x) g)
	        (equal (mapply map (mapply (inv-isomorphism map g h) x))
		       x)))
  :hints (("Goal" :in-theory (enable isomorphismp epimorphismp)
                  :use (image-elts image-preimage))))

(defthm inv-map
  (implies (and (isomorphismp map g h)
                (in x g))
	   (and (in (mapply map x) h)
	        (equal (mapply (inv-isomorphism map g h) (mapply map x))
		       x)))
  :hints (("Goal" ;:in-theory (enable isomorphismp)
                  :use (homomorphism-codomain member-ielts
		        (:instance image-preimage (x (mapply map x)))
		        (:instance endomorphism-1-1 (y (mapply (inv-isomorphism map g h) (mapply map x))))))))

(defthmd isomorphism-equal-orders
  (implies (isomorphismp map g h)
	   (equal (order g) (order h)))
  :hints (("Goal" :in-theory (disable inv-isomorphism-val)
                  :use ((:functional-instance len-1-1-equal
                         (x (lambda () (if (isomorphismp map g h) (car g) (x))))
                         (y (lambda () (if (isomorphismp map g h) (car h) (y))))
			 (xy (lambda (a) (if (isomorphismp map g h) (mapply map a) (xy a))))
			 (yx (lambda (a) (if (isomorphismp map g h) (mapply (inv-isomorphism map g h) a) (yx a)))))))))

(defthmd equal-orders-isomorphism
  (implies (and (endomorphismp map g h)
	        (equal (order g) (order h)))
	   (isomorphismp map g h))
  :hints (("Goal" :in-theory (e/d (permp endomorphismp isomorphismp) (permp-eq-len))
	          :use (epimorphism-image homomorphism-epimorphism
			(:instance isomorphism-equal-orders (h (image map g h)))
			(:instance permp-eq-len (l (ielts map g h)) (m (elts h)))))))

(defthm isomorphismp-inv-e
  (implies (isomorphismp map g h)
           (equal (mapply (inv-isomorphism map g h) (e h))
	          (e g)))
  :hints (("Goal" :in-theory (e/d (isomorphismp epimorphismp) (inv-isomorphism-val))
                  :use ((:instance map-inv (x (e h)))
		        (:instance endomorphism-1-1 (x (mapply (inv-isomorphism map g h) (e h))) (y (e g)))))))

(local-defthm isomorphismp-inv-codomain-cex
  (implies (isomorphismp map g h)
           (not (codomain-cex (inv-isomorphism map g h) h g)))
  :hints (("Goal" :in-theory (disable inv-isomorphism-val)
                  :use ((:instance codomain-cex-lemma (map (inv-isomorphism map g h)) (h g) (g h))))))

(local-defthm isomorphismp-inv-op
  (implies (and (isomorphismp map g h) (groupp h) (groupp g)
                (in x h)
		(in y h))
	   (equal (op (mapply (inv-isomorphism map g h) x)
	              (mapply (inv-isomorphism map g h) y)
		      g)
		  (mapply (inv-isomorphism map g h) (op x y h))))
  :hints (("Goal" :in-theory (disable homomorphism-op map-inv inv-isomorphism-val)
                  :use (map-inv
		        (:instance map-inv (x y))
		        (:instance map-inv (x (op x y h)))
			(:instance endomorphism-1-1 (x (op (mapply (inv-isomorphism map g h) x)
                                                           (mapply (inv-isomorphism map g h) y)
                                                           G))
					            (y (MAPPLY (INV-ISOMORPHISM MAP G H) (OP X Y H))))
		        (:instance homomorphism-op (x (mapply (inv-isomorphism map g h) x))
			                           (y (mapply (inv-isomorphism map g h) y)))))))

(local-defthm isomorphismp-inv-homomorphism-cex
  (implies (isomorphismp map g h)
           (not (homomorphism-cex (inv-isomorphism map g h) h g)))
  :hints (("Goal" :in-theory (enable isomorphismp endomorphismp)
                  :use ((:instance homomorphismp-cex-lemma (map (inv-isomorphism map g h)) (h g) (g h))
		        (:instance isomorphismp-inv-op (x (car (homomorphism-cex (inv-isomorphism map g h) h g)))
			                               (y (cdr (homomorphism-cex (inv-isomorphism map g h) h g))))))))

(local-defthm isomorphismp-inv-homomorphism
  (implies (isomorphismp map g h)
           (homomorphismp (inv-isomorphism map g h) h g))
  :hints (("Goal" :in-theory (enable homomorphismp))))
			
(local-defthm sublistp-ielts-inv-isomorphism
  (implies (and (isomorphismp map g h)
                (sublistp l (elts g)))
           (sublistp l (ielts (inv-isomorphism map g h) h g)))
  :hints (("Subgoal *1/2" :use ((:instance member-ielts (g h) (h g) (map (inv-isomorphism map g h)) (x (mapply map (car l))))))))

(local-defthmd epimorphismp-inv
  (implies (isomorphismp map g h)
           (epimorphismp (inv-isomorphism map g h) h g))
  :hints (("Goal" :in-theory (enable epimorphismp)
                  :use ((:instance homomorphism-epimorphism (map (inv-isomorphism map g h)) (g h) (h g))))))

(local-defthmd in-kernel-inv-isomorphism
  (implies (and (isomorphismp map g h)
                (in x h)
                (equal (mapply (inv-isomorphism map g h) x) (e g)))
	   (equal (e h) x))
  :hints (("Goal" :use (homomorphism-e map-inv))))

(local-defthmd endmorphismp-inv
  (implies (isomorphismp map g h)
           (endomorphismp (inv-isomorphism map g h) h g))
  :hints (("Goal" :use ((:instance homomorphism-endomorphism (map (inv-isomorphism map g h)) (g h) (h g))
                        (:instance in-kernel-inv-isomorphism (x (cadr (kelts (inv-isomorphism map g h) h g))))))))

(defthmd isomorphismp-inv
  (implies (isomorphismp map g h)
           (isomorphismp (inv-isomorphism map g h) h g))
  :hints (("Goal" :in-theory (enable isomorphismp)
                  :use (endmorphismp-inv epimorphismp-inv))))

(defthm isomorphismp-compose-maps
  (implies (and (isomorphismp map1 g h)
                (isomorphismp map2 h k))
	   (isomorphismp (compose-maps map2 map1) g k))
  :hints (("Goal" :in-theory (enable isomorphismp)
                  :use ((:instance isomorphism-equal-orders (map map1))
		        (:instance isomorphism-equal-orders (map map2) (g h) (h k))
			(:instance equal-orders-isomorphism (map (compose-maps map2 map1)) (h k))))))
     
;; An automorphism of is an isomorphism from g to g:

(defund automorphismp (map g)
  (isomorphismp map g g))

;; The identity map on (elts g) is a trivial automorphism:

(defthmd identity-automorphism
  (implies (groupp g)
	   (automorphismp (identity-map (elts g)) g))
  :hints (("Goal" :in-theory (enable automorphismp isomorphismp))))

;; If h is a subgroup of g of the same order as g, then the identity map is also an isomorphism from g to h:

(local-defthm subgroup-identity-homomorphism
  (implies (and (subgroupp h g) (sublistp (elts g) (elts h)))
	   (homomorphismp (identity-map (elts g)) g h))
  :hints (("Goal" :in-theory (enable homomorphismp)
                  :use ((:instance homomorphismp-cex-lemma (map (identity-map (elts g))))
		        (:instance codomain-cex-lemma (map (identity-map (elts g))))))))

(local-defthm subgroup-identity-endomorphism
  (implies (and (subgroupp h g) (sublistp (elts g) (elts h)))
	   (endomorphismp (identity-map (elts g)) g h))
  :hints (("Goal" :use ((:instance homomorphism-endomorphism (map (identity-map (elts g))))))))

(local-defthm subgroup-ielts-aux-identity
  (implies (and (sublistp (elts g) (elts h))
                (sublistp l (elts g)))
           (sublistp l (ielts-aux (identity-map (elts g)) l h))))

(local-defthm subgroup-sublistp-ielts-identity
  (implies (sublistp (elts g) (elts h))
           (sublistp (elts g) (ielts (identity-map (elts g)) g h)))
  :hints (("Goal" :in-theory (enable ielts))))

(local-defthm subgroup-identity-epimorphism
  (implies (and (subgroupp h g) (sublistp (elts g) (elts h)))
	   (epimorphismp (identity-map (elts g)) g h))
  :hints (("Goal" :use ((:instance homomorphism-epimorphism (map (identity-map (elts g))))
                        (:instance sublistp-sublistp (l (elts h)) (m (elts g)) (n (ielts (identity-map (elts g)) g h)))))))

(defthm subgroup-isomorphism
  (implies (and (subgroupp h g)
                (equal (order h) (order g)))
	   (isomorphismp (identity-map (elts g)) g h))
  :hints (("Goal" :in-theory (e/d (permp isomorphismp) (permp-eq-len))
                  :use ((:instance permp-eq-len (l (elts h)) (m (elts g)))))))

(defthmd cyclicp-isomorphism
  (implies (cyclicp g)
           (isomorphismp (identity-map (elts g))
	                 g
			 (cyclic (group-gen g) g)))
  :hints (("Goal" :use (cyclicp-order order-group-gen
                        (:instance subgroup-isomorphism (h (cyclic (group-gen g) g)))))))

(defthm cyclicp-abelianp
  (implies (cyclicp g)
           (abelianp g))
  :hints (("Goal" :in-theory (enable abelianp-cyclic isomorphismp epimorphismp)
                  :use (cyclicp-isomorphism order-group-gen
		        (:instance homomorphismp-abelianp-image (map (inv-isomorphism (identity-map (elts g)) g (cyclic (group-gen g) g)))
			                                        (g (cyclic (group-gen g) g))
								(h g))								
			(:instance isomorphismp-inv (map (identity-map (elts g))) (h (cyclic (group-gen g) g)))))))
