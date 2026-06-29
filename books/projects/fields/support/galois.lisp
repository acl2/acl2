(in-package "DM")

(include-book "embeddings")
(include-book "projects/groups/actions" :dir :system)

;;----------------------------------------------------------------------------------------------------------
;;                                      Automorphisms of an Extension Field
;;----------------------------------------------------------------------------------------------------------

;; Automorphism of e over f:

(defund autop (a e f)
  (embeddingp a e e f))

(defthm autop-embeddingp
  (implies (autop a e f)
           (embeddingp a e e f))
  :hints (("Goal" :in-theory (enable autop))))

(defthm auto-image
  (implies (and (autop a e f) (extensionp e f)
                (feltp x e))
           (feltp (embed x a e f) e))
  :hints (("Goal" :use ((:instance embed-image (k e) (phi a))))))

;; A handy version of embed-cex-lemma:

(defthmd auto-cex-lemma
  (implies (and (extensionp e f)
                (autop a e f) (autop b e f)
		(not (equal a b)))
	   (let ((x (embed-cex a b e f)))
	     (and (feltp x e)
	          (not (equal (embed x a e f) (embed x b e f))))))
  :hints (("Goal" :use ((:instance embed-cex-lemma (k e) (phi a) (psi b))))))

;; Identity automorphism:

(defund id-auto (e f)
  (id-embedding e f))

(defthm autop-id-auto
  (implies (and (fieldp f) (fieldp e) (extensionp e f))
           (autop (id-auto e f) e f))
  :hints (("Goal" :in-theory (enable autop id-auto)
                  :use (id-embedding-id))))

(defthm embed-auto-id
  (implies (and (fieldp f) (fieldp e) (extensionp e f)
                (feltp x e))
	   (equal (embed x (id-auto e f) e f)
	          x))
  :hints (("Goal" :in-theory (enable autop id-auto)
                  :use (id-embedding-id))))

;; Composition of automorphisms:

(defund comp-auto (a b e f)
  (comp-embedding a b e e f))

(defthm autop-comp-auto
  (implies (and (extensionp e f) (autop a e f) (autop b e f))
           (autop (comp-auto a b e f) e f))
  :hints (("Goal" :in-theory (enable autop comp-auto)
                  :use ((:instance embeddingp-comp-embedding (psi a) (phi b) (g e) (k e))))))

(defthm embed-comp-auto
  (implies (and (extensionp e f) (autop a e f) (autop b e f) (feltp x e))
           (equal (embed x (comp-auto a b e f) e f)
	          (embed (embed x b e f) a e f)))
  :hints (("Goal" :in-theory (enable autop comp-auto)
                  :use ((:instance embeddingp-comp-embedding (psi a) (phi b) (g e) (k e))))))

;; Associativity:

(defthmd comp-auto-assoc-1
  (implies (and (extensionp e f)
                (autop a e f) (autop b e f) (autop c e f)
		(feltp x e))
	   (equal (embed x (comp-auto (comp-auto a b e f) c e f) e f)
	          (embed x (comp-auto a (comp-auto b c e f) e f) e f))))

(defthm comp-auto-assoc
  (implies (and (extensionp e f)
                (autop a e f) (autop b e f) (autop c e f))
	   (equal (comp-auto (comp-auto a b e f) c e f)
	          (comp-auto a (comp-auto b c e f) e f)))
  :hints (("Goal" :use ((:instance auto-cex-lemma (a (comp-auto (comp-auto a b e f) c e f))
                                                  (b (comp-auto a (comp-auto b c e f) e f)))
			(:instance comp-auto-assoc-1
			  (x (embed-cex (comp-auto (comp-auto a b e f) c e f) (comp-auto a (comp-auto b c e f) e f) e f)))))))

;; id-auto is a left identity:

(defthm id-auto-id
  (implies (and (extensionp e f)
                (autop a e f))
	   (equal (comp-auto (id-auto e f) a e f)
	          a))
  :hints (("Goal" :use ((:instance auto-cex-lemma (b (comp-auto (id-auto e f) a e f)))))))

;; The inverse of an automorphism:
          
(defund inv-auto (a e f)
  (inv-embedding a e e f))

(in-theory (disable inv-embedding))

(defthm autop-inv-auto
  (implies (and (extensionp e f)
                (autop a e f))
	   (autop (inv-auto a e f) e f))
  :hints (("Goal" :in-theory (enable comp-inv-embedding inv-auto autop))))

(defthm comp-inv-auto
  (implies (and (extensionp e f)
                (autop a e f))
	   (equal (comp-auto (inv-auto a e f) a e f)
	          (id-auto e f)))
  :hints (("Goal" :in-theory (enable comp-inv-embedding comp-auto id-auto inv-auto autop))))

;; The automorphisms of e over f form a group, but we must reorder its elements so that the identity is the
;; car:

(defund auto-list (e f)
  (cons (id-auto e f)
        (remove1 (id-auto e f) (embeddings e e f))))

(defthm dlistp-auto-list
  (implies (extensionp e f)
           (dlistp (auto-list e f)))
  :hints (("Goal" :in-theory (enable auto-list)
                  :use ((:instance dlistp-remove1 (l (embeddings e e f)) (x (id-auto e f)))))))

(local-defthmd member-auto-list-1
  (implies (extensionp e f)
           (iff (member a (embeddings e e f))
	        (autop a e f)))
  :hints (("Goal" :in-theory (enable autop)
                  :use ((:instance all-embeddings (phi a) (k e))))))

(defthm member-auto-list
  (implies (extensionp e f)
           (iff (member a (auto-list e f))
	        (autop a e f)))
  :hints (("Goal" :in-theory (enable auto-list)
                  :use (member-auto-list-1))))

(defthm car-auto-list
  (equal (car (auto-list e f))
         (id-auto e f))
  :hints (("Goal" :in-theory (enable auto-list))))

(defthm len-auto-list
  (implies (extensionp e f)
           (equal (len (auto-list e f))
	          (len (embeddings e e f))))
  :hints (("Goal" :in-theory (enable auto-list)
                  :use ((:instance member-auto-list-1 (a (id-auto e f)))))))

(defthm not-autop-nil
  (implies (not (equal e f))
           (not (autop () e f)))
  :hints (("Goal" :in-theory (enable embeddingp autop))))
    
(defgroup autos (e f)
  (extensionp e f)
  (auto-list e f)
  (comp-auto x y e f)
  (inv-auto x e f))

;; The order of the group is bounded by the degree of the extension:

(defthmd ord-autos-bound
  (implies (extensionp e f)
           (<= (order (autos e f))
	       (edegree e f)))
  :hints (("Goal" :in-theory (enable order)
                  :use ((:instance len-embeddings (k e))))))

;; Let e be an extension of d and d an extension of f.  Let phi be a automorphism of e over f.
;; If the restriction of phi to d is the trivial embedding of d in e, then phi naturally corresponds 
;; to an automorphism of e over d:

(defun trunc-embedding (phi e d)
  (firstn (- (len e) (len d)) phi))

(local-defun firstn-auto-induct (e phi d)
  (declare (irrelevant phi))
  (if (and (consp e) (not (equal e d)))
      (firstn-auto-induct (cdr e) (cdr phi) d)
    ()))

(local (defun-sk firstn-embedding-cond (e d f k phi)
  (forall (x)
    (implies (feltp x e)
             (equal (embed x (firstn (- (len e) (len d)) phi) k d)
	            (embed x phi k f))))))

(local-defthmd firstn-embedding-cond-lemma
  (implies (and (firstn-embedding-cond e d f k phi)
                (feltp x e))
	   (equal (embed x (firstn (- (len e) (len d)) phi) k d)
	          (embed x phi k f)))
  :hints (("Goal" :use (firstn-embedding-cond-necc))))

(local-defthmd firstn-embedding-cond-witness-lemma
  (let ((x (firstn-embedding-cond-witness e d f k phi)))
    (implies (implies (feltp x e)
                      (equal (embed x (firstn (- (len e) (len d)) phi) k d)
	                     (embed x phi k f)))
	     (firstn-embedding-cond e d f k phi))))

(local (in-theory (disable firstn-embedding-cond)))

(local-defthmd firstn-embedding-base
  (implies (and (extensionp d f) (extensionp k d))
           (and (embeddingp (trivial-embedding d k f) d k f)
	        (firstn-embedding-cond d d f k (trivial-embedding d k f))))
  :hints (("Goal" :in-theory (enable embed embeddingp)
	          :use ((:instance firstn-embedding-cond-witness-lemma (e d) (phi (trivial-embedding d k f)))
		        (:instance trivial-embedding-flift (e d) (x (firstn-embedding-cond-witness d d f k (trivial-embedding d k f))))))))

(local-defthmd firstn-embedding-step-1
  (implies (and (extensionp e d) (extensionp d f) (extensionp k d) (embeddingp phi e k f)
	        (firstn-embedding-cond e d f k phi)
		(feltsp p e))
	   (equal (pembed p (firstn (- (len e) (len d)) phi) k d)
	          (pembed p phi k f)))
  :hints (("Goal" :induct (len p))
          ("Subgoal *1/1" :expand ((:free (phi d) (pembed p phi k d)))
	                  :use ((:instance firstn-embedding-cond-lemma (x (car p)))))))

(local-defthmd firstn-embedding-step-2
  (let ((n (- (len e) (len d))))
    (implies (and (extensionp e d) (extensionp d f) (extensionp k d) (embeddingp phi e k f)
                  (equal (nthcdr n phi) (trivial-embedding d k f))
		  (not (equal e d))
		  (embeddingp (firstn (1- n) (cdr phi)) (cdr e) k d)
	          (firstn-embedding-cond (cdr e) d f k (cdr phi)))
             (embeddingp (firstn n phi) e k d)))
  :hints (("Goal" :in-theory (enable embeddingp)
                  :use ((:instance len-extends (e (cdr e))(f d))		  
		        (:instance len-extends (e d) (f e))
			(:instance firstn-embedding-step-1 (p (car e)) (e (cdr e)) (phi (cdr phi)))))))

(local-defthmd firstn-embedding-step-3
  (let ((n (- (len e) (len d))))
    (implies (and (extensionp e d) (extensionp d f) (extensionp k d) (embeddingp phi e k f)
                  (equal (nthcdr n phi) (trivial-embedding d k f))
		  (not (equal e d))
		  (embeddingp (firstn (1- n) (cdr phi)) (cdr e) k d)
	          (firstn-embedding-cond (cdr e) d f k (cdr phi))
		  (feltp x e))
             (equal (embed x (firstn n phi) k d)
	            (embed x phi k f))))
  :hints (("Goal" :in-theory (enable feltp embed embeddingp)
                  :use ((:instance len-extends (e (cdr e))(f d))		  
		        (:instance len-extends (e d) (f e))
			(:instance firstn-embedding-step-1 (p x) (phi (cdr phi)) (e (cdr e)))))))

(local-defthmd firstn-embedding-step-4
  (let ((n (- (len e) (len d))))
    (implies (and (extensionp e d) (extensionp d f) (extensionp k d) (embeddingp phi e k f)
                  (equal (nthcdr n phi) (trivial-embedding d k f))
		  (not (equal e d))
		  (embeddingp (firstn (1- n) (cdr phi)) (cdr e) k d)
	          (firstn-embedding-cond (cdr e) d f k (cdr phi)))
             (firstn-embedding-cond e d f k phi)))
  :hints (("Goal" :use (firstn-embedding-cond-witness-lemma
                        (:instance firstn-embedding-step-3 (x (firstn-embedding-cond-witness e d f k phi)))))))

(local-defthmd firstn-embedding-step
  (let ((n (- (len e) (len d))))
    (implies (and (extensionp e d) (extensionp d f) (extensionp k d) (embeddingp phi e k f)
                  (equal (nthcdr n phi) (trivial-embedding d k f))
		  (not (equal e d))
		  (embeddingp (firstn (1- n) (cdr phi)) (cdr e) k d)
	          (firstn-embedding-cond (cdr e) d f k (cdr phi)))
             (and (embeddingp (firstn n phi) e k d)
	          (firstn-embedding-cond e d f k phi))))
  :hints (("Goal" :use (firstn-embedding-step-2 firstn-embedding-step-4))))

(local-defthmd firstn-embedding
  (let ((n (- (len e) (len d))))
    (implies (and (extensionp e d) (extensionp d f) (extensionp k d) (embeddingp phi e k f)
                  (equal (nthcdr n phi) (trivial-embedding d k f)))
	     (and (embeddingp (firstn n phi) e k d)
	          (firstn-embedding-cond e d f k phi))))
  :hints (("Goal" :induct (firstn-auto-induct e phi d))
          ("Subgoal *1/2" :in-theory (enable embeddingp) :use (firstn-embedding-base))
	  ("Subgoal *1/1" :in-theory (enable embeddingp)
	                  :use (firstn-embedding-step
	                        (:instance len-extends (e d) (f e))
	                        (:instance len-extends (e (cdr e)) (f d))))))

;; We shall require the following generalization:

(in-theory (enable restrict-embedding))

(defthmd embeddingp-trunc-embedding
  (implies (and (extensionp e d) (extensionp d f) (extensionp k d) (embeddingp phi e k f)
                (equal (restrict-embedding phi e d) (trivial-embedding d k f)))
           (let ((psi (trunc-embedding phi e d)))
	     (and (embeddingp psi e k d)
	          (implies (feltp x e)
		           (equal (embed x psi k d)
			          (embed x phi k f))))))
  :hints (("Goal" :in-theory (enable autop)
                  :use (firstn-embedding firstn-embedding-cond-lemma))))

(local-defthmd pembed-trunc-embedding-1
  (implies (and (extensionp e d) (extensionp d f) (extensionp k d) (embeddingp phi e k f)
                (equal (restrict-embedding phi e d) (trivial-embedding d k f))
		(feltsp p e))
           (equal (pembed p (trunc-embedding phi e d) k d)
	          (pembed p phi k f)))
  :hints (("Goal" :induct (len p))
          ("Subgoal *1/1" :use ((:instance embeddingp-trunc-embedding (x (car p)))))))

(defthmd pembed-trunc-embedding
  (implies (and (extensionp e d) (extensionp d f) (extensionp k d) (embeddingp phi e k f)
                (equal (restrict-embedding phi e d) (trivial-embedding d k f))
		(polyp p e))
           (equal (pembed p (trunc-embedding phi e d) k d)
	          (pembed p phi k f)))
  :hints (("Goal" :use (pembed-trunc-embedding-1))))

;; The case k = e:

(defthmd autop-trunc-embedding
  (implies (and (extensionp e d) (extensionp d f) (autop phi e f)
                (equal (restrict-embedding phi e d) (trivial-embedding d e f)))
           (let ((psi (trunc-embedding phi e d)))
	     (and (autop psi e d)
	          (implies (feltp x e)
		           (equal (embed x psi e d)
			          (embed x phi e f))))))
  :hints (("Goal" :in-theory (enable autop)
                  :use ((:instance firstn-embedding (k e))
		        (:instance firstn-embedding-cond-lemma (k e))))))

;; Given an isomorphism from e to k over f, we define a group isomorphism from (autos e f) to (autos k f):

(defun auto-map-image (x phi e k f)
  (comp-embedding phi (comp-embedding x (inv-embedding phi e k f) k e f) k k f))
  
(defmap auto-map (phi e k f)
  (auto-list e f)
  (auto-map-image x phi e k f))

(local-defthmd homomorphismp-auto-map-1
  (implies (and (extensionp e f) (extensionp k f) (embeddingp phi e k f) (equal (edegree e f) (edegree k f))
                (in x (autos e f)))
	   (autop (auto-map-image x phi e k f) k f))
  :hints (("Goal" :in-theory (enable autop)
                  :use (embeddingp-inv-embedding
                        (:instance embeddingp-comp-embedding (e k) (g e) (k e) (phi (inv-embedding phi e k f)) (psi x))
                        (:instance embeddingp-comp-embedding (e k) (g e) (phi (comp-embedding x (inv-embedding phi e k f) k e f)) (psi phi))))))

(local-defthmd homomorphismp-auto-map-2
  (implies (and (extensionp e f) (extensionp k f) (embeddingp phi e k f) (equal (edegree e f) (edegree k f))
                (in x (autos e f)) (in y (autos e f)))
	   (equal (comp-auto (mapply (auto-map phi e k f) x) (mapply (auto-map phi e k f) y) k f)
	          (comp-embedding (comp-embedding (comp-embedding phi x e k f) (inv-embedding phi e k f) k k f)
		                  (mapply (auto-map phi e k f) y)
				  k k f)))
  :hints (("Goal" :in-theory (enable comp-auto autop)
                  :use (embeddingp-inv-embedding
                        (:instance comp-embedding-assoc (phi1 (inv-embedding phi e k f)) (phi2 x) (phi3 phi) (e1 k) (e2 e) (e3 e) (e4 k))))))

(local-defthmd homomorphismp-auto-map-3
  (implies (and (extensionp e f) (extensionp k f) (embeddingp phi e k f) (equal (edegree e f) (edegree k f))
                (in x (autos e f)) (in y (autos e f)))
	   (equal (comp-embedding (comp-embedding (comp-embedding phi x e k f) (inv-embedding phi e k f) k k f)
		                  (mapply (auto-map phi e k f) y)
				  k k f)
		  (comp-embedding (comp-embedding phi x e k f)
		                  (comp-embedding (inv-embedding phi e k f) (mapply (auto-map phi e k f) y) k e f)
				  k k f)))
  :hints (("Goal" :in-theory (enable comp-auto autop)
                  :use (embeddingp-inv-embedding
		        (:instance homomorphismp-auto-map-1 (x y))
			(:instance embeddingp-comp-embedding (phi x) (psi phi) (g e))
                        (:instance comp-embedding-assoc (phi1 (mapply (auto-map phi e k f) y))
			                                (phi2 (inv-embedding phi e k f))
							(phi3 (comp-embedding phi x e k f))
							(e1 k) (e2 k) (e3 e) (e4 k))))))

(local-defthmd homomorphismp-auto-map-4
  (implies (and (extensionp e f) (extensionp k f) (embeddingp phi e k f) (equal (edegree e f) (edegree k f))
                (in x (autos e f)) (in y (autos e f)))
	   (equal (comp-embedding (inv-embedding phi e k f) (mapply (auto-map phi e k f) y) k e f)
	          (comp-embedding y (inv-embedding phi e k f) k e f)))
  :hints (("Goal" :in-theory (enable comp-auto autop)
                  :use (comp-inv-embedding embeddingp-inv-embedding
		        (:instance comp-id-embedding (e k) (k e) (phi (comp-embedding y (inv-embedding phi e k f) k e f)))
			(:instance embeddingp-comp-embedding (phi (inv-embedding phi e k f)) (psi y) (e k) (g e) (k e))
                        (:instance comp-embedding-assoc (phi1 (comp-embedding y (inv-embedding phi e k f) k e f)) (phi2 phi) (phi3 (inv-embedding phi e k f)) (e1 k) (e2 e) (e3 k) (e4 e))))))

(local-defthmd homomorphismp-auto-map-5
  (implies (and (extensionp e f) (extensionp k f) (embeddingp phi e k f) (equal (edegree e f) (edegree k f))
                (in x (autos e f)) (in y (autos e f)))
	   (equal (comp-auto (mapply (auto-map phi e k f) x) (mapply (auto-map phi e k f) y) k f)
	          (comp-embedding (comp-embedding phi x e k f)
		                  (comp-embedding y (inv-embedding phi e k f) k e f)
				  k k f)))
  :hints (("Goal" :use (homomorphismp-auto-map-2 homomorphismp-auto-map-3 homomorphismp-auto-map-4))))

(local-defthmd homomorphismp-auto-map-6
  (implies (and (extensionp e f) (extensionp k f) (embeddingp phi e k f) (equal (edegree e f) (edegree k f))
                (in x (autos e f)) (in y (autos e f)))
	   (equal (comp-embedding (comp-embedding phi x e k f)
		                  (comp-embedding y (inv-embedding phi e k f) k e f)
				  k k f)
		  (comp-embedding phi (comp-embedding x (comp-embedding y (inv-embedding phi e k f) k e f) k e f) k k f)))
  :hints (("Goal" :use (embeddingp-inv-embedding
                        (:instance embeddingp-comp-embedding (phi (inv-embedding phi e k f)) (psi y) (e k) (g e) (k e))
                        (:instance comp-embedding-assoc (phi1 (comp-embedding y (inv-embedding phi e k f) k e f)) (phi2 x) (phi3 phi) (e1 k) (e2 e) (e3 e) (e4 k))))))

(local-defthmd homomorphismp-auto-map-7
  (implies (and (extensionp e f) (extensionp k f) (embeddingp phi e k f) (equal (edegree e f) (edegree k f))
                (in x (autos e f)) (in y (autos e f)))
	   (equal (comp-embedding phi (comp-embedding x (comp-embedding y (inv-embedding phi e k f) k e f) k e f) k k f)
	          (mapply (auto-map phi e k f) (comp-auto x y e f))))
  :hints (("Goal" :in-theory (enable comp-auto autop)
                  :use (embeddingp-inv-embedding
		        (:instance embeddingp-comp-embedding (phi y) (psi x) (g e) (k e))
                        (:instance comp-embedding-assoc (phi1 (inv-embedding phi e k f)) (phi2 y) (phi3 x) (e1 k) (e2 e) (e3 e) (e4 e))))))

(local-defthmd homomorphismp-auto-map-8
  (implies (and (extensionp e f) (extensionp k f) (embeddingp phi e k f) (equal (edegree e f) (edegree k f))
                (in x (autos e f)) (in y (autos e f)))
	   (equal (comp-auto (auto-map-image x phi e k f) (auto-map-image y phi e k f) k f)
	          (auto-map-image (comp-auto x y e f) phi e k f)))
  :hints (("Goal" :use (homomorphismp-auto-map-5 homomorphismp-auto-map-6 homomorphismp-auto-map-7))))

(local-defthmd homomorphismp-auto-map-9
  (implies (and (extensionp e f) (extensionp k f) (embeddingp phi e k f) (equal (edegree e f) (edegree k f)))
	   (equal (auto-map-image (id-auto e f) phi e k f)
	          (id-auto k f)))
  :hints (("Goal" :in-theory (enable id-auto e)
                  :use (comp-inv-embedding
                        (:instance comp-id-embedding (e k) (k e) (phi (inv-embedding phi e k f)))))))

(in-theory (disable auto-map-image))

(local (in-theory (enable e homomorphismp-auto-map-1 homomorphismp-auto-map-8 homomorphismp-auto-map-9)))

(prove-homomorphismp auto-map
  (auto-map phi e k f)
  (autos e f) (autos k f)
  (and (extensionp e f) (extensionp k f) (embeddingp phi e k f) (equal (edegree e f) (edegree k f))))

(DEFTHM HOMOMORPHISMP-AUTO-MAP
  (IMPLIES (AND (EXTENSIONP E F)
                (EXTENSIONP K F)
                (EMBEDDINGP PHI E K F)
                (EQUAL (EDEGREE E F) (EDEGREE K F)))
           (HOMOMORPHISMP (AUTO-MAP PHI E K F)
                          (AUTOS E F)
                          (AUTOS K F))))

(local-defthmd endomorphismp-auto-map-1
  (implies (and (extensionp e f) (extensionp k f) (embeddingp phi e k f) (equal (edegree e f) (edegree k f))
                (in x (autos e f)) (equal (auto-map-image x phi e k f) (id-auto k f)))
           (equal (comp-embedding x (inv-embedding phi e k f) k e f)
	          (inv-embedding phi e k f)))
  :hints (("Goal" :in-theory (enable id-auto auto-map-image)
                  :use (comp-inv-embedding
                        (:instance comp-embedding-assoc (phi3 (inv-embedding phi e k f)) (phi2 phi) (phi1 (comp-embedding x (inv-embedding phi e k f) k e f))
                                                        (e1 k) (e2 e) (e3 k) (e4 e))
			(:instance embeddingp-comp-embedding (phi (inv-embedding phi e k f)) (psi x) (e k) (g e) (k e))
			(:instance comp-id-embedding (phi (inv-embedding phi e k f)) (e k) (k e))
			(:instance comp-id-embedding (e k) (k e) (phi (comp-embedding x (inv-embedding phi e k f) k e f)))))))

(local-defthmd endomorphismp-auto-map-2
  (implies (and (extensionp e f) (extensionp k f) (embeddingp phi e k f) (equal (edegree e f) (edegree k f))
                (in x (autos e f)) (equal (auto-map-image x phi e k f) (id-auto k f)))
           (equal (id-auto e f) x))
  :hints (("Goal" :in-theory (enable id-auto auto-map-image)
                  :use (endomorphismp-auto-map-1 comp-inv-embedding
                        (:instance comp-embedding-assoc (phi1 phi) (phi2 (inv-embedding phi e k f)) (phi3 x) (e1 e) (e2 k) (e3 e) (e4 e))
			(:instance embeddingp-comp-embedding (phi (inv-embedding phi e k f)) (psi x) (e k) (g e) (k e))
			(:instance comp-id-embedding (phi x) (k e))))))

(local-defthmd endomorphismp-auto-map
  (implies (and (extensionp e f) (extensionp k f) (embeddingp phi e k f) (equal (edegree e f) (edegree k f)))
                (endomorphismp (auto-map phi e k f)
                               (autos e f)
                               (autos k f)))
  :hints (("goal" :in-theory (enable id-auto auto-map-image)
                  :use ((:instance homomorphism-endomorphism (map (auto-map phi e k f)) (g (autos e f)) (h (autos k f)))
                        (:instance endomorphismp-auto-map-2 (x (cadr (kelts (auto-map phi e k f) (autos e f) (autos k f)))))))))

(local-defthmd epimorphismp-auto-map-1
  (implies (and (extensionp e f) (extensionp k f) (embeddingp phi e k f) (equal (edegree e f) (edegree k f))
                (in x (autos k f)))
	   (equal (auto-map-image (auto-map-image x (inv-embedding phi e k f) k e f) phi e k f)
	          (comp-embedding phi
		                  (comp-embedding (comp-embedding (comp-embedding (inv-embedding phi e k f) x k e f)
				                                  phi
								  e e f)
				                  (inv-embedding phi e k f)
				                  k e f)
				  k k f)))
  :hints (("Goal" :in-theory (enable auto-map-image)
                  :use (comp-inv-embedding inv-inv-embedding
                        (:instance comp-embedding-assoc (phi1 phi) (phi2 x) (phi3 (inv-embedding phi e k f)) (e1 e) (e2 k) (e3 k) (e4 e))))))

(local-defthmd epimorphismp-auto-map-2
  (implies (and (extensionp e f) (extensionp k f) (embeddingp phi e k f) (equal (edegree e f) (edegree k f))
                (in x (autos k f)))
	   (equal (comp-embedding (comp-embedding (comp-embedding (inv-embedding phi e k f) x k e f)
				                  phi
						  e e f)
				  (inv-embedding phi e k f)
				  k e f)
		  (comp-embedding (inv-embedding phi e k f) x k e f)))
  :hints (("Goal" :in-theory (enable auto-map-image)
                  :use (comp-inv-embedding
		        (:instance embeddingp-comp-embedding (phi x) (psi (inv-embedding phi e k f)) (e k) (g k) (k e))
			(:instance comp-id-embedding (phi (comp-embedding (inv-embedding phi e k f) x k e f)) (e k) (k e))
                        (:instance comp-embedding-assoc (phi1 (inv-embedding phi e k f)) (phi2 phi) (phi3 (comp-embedding (inv-embedding phi e k f) x k e f))
			                                (e1 k) (e2 e) (e3 k) (e4 e))))))

(local-defthmd epimorphismp-auto-map-3
  (implies (and (extensionp e f) (extensionp k f) (embeddingp phi e k f) (equal (edegree e f) (edegree k f))
                (in x (autos k f)))
	   (equal (auto-map-image (auto-map-image x (inv-embedding phi e k f) k e f) phi e k f)
	          x))
  :hints (("Goal" :use (comp-inv-embedding epimorphismp-auto-map-1 epimorphismp-auto-map-2
			(:instance comp-id-embedding (phi x) (e k))
                        (:instance comp-embedding-assoc (phi1 x) (phi2 (inv-embedding phi e k f)) (phi3 phi) (e1 k) (e2 k) (e3 e) (e4 k))))))

(local-defthmd epimorphismp-auto-map-4
  (implies (and (extensionp e f) (extensionp k f) (embeddingp phi e k f) (equal (edegree e f) (edegree k f))
                (in x (autos k f)))
	   (autop (auto-map-image x (inv-embedding phi e k f) k e f) e f))
  :hints (("Goal" :in-theory (disable homomorphismp-auto-map-1 homomorphismp-auto-map) :use (comp-inv-embedding
                        (:instance homomorphismp-auto-map-1 (e k) (k e) (phi (inv-embedding phi e k f)))
			(:instance homomorphismp-auto-map (phi (inv-embedding phi e k f)) (e k) (k e))))))

(local-defthmd epimorphismp-auto-map-5
  (implies (and (extensionp e f) (extensionp k f) (embeddingp phi e k f) (equal (edegree e f) (edegree k f))
                (in x (autos k f)))
	   (member x (ielts (auto-map phi e k f) (autos e f) (autos k f))))
  :hints (("Goal" :use (epimorphismp-auto-map-3 epimorphismp-auto-map-4 homomorphismp-auto-map
			(:instance member-ielts (map (auto-map phi e k f)) (g (autos e f)) (h (autos k f)) (x (auto-map-image x (inv-embedding phi e k f) k e f)))))))

(local-defthmd epimorphismp-auto-map-6
  (implies (and (extensionp e f) (extensionp k f) (embeddingp phi e k f) (equal (edegree e f) (edegree k f)))
	   (sublistp (auto-list k f) (ielts (auto-map phi e k f) (autos e f) (autos k f))))
  :hints (("Goal" :use ((:instance scex1-lemma (l (auto-list k f)) (m (ielts (auto-map phi e k f) (autos e f) (autos k f))))
                        (:instance epimorphismp-auto-map-5 (x (scex1 (auto-list k f) (ielts (auto-map phi e k f) (autos e f) (autos k f)))))))))

(local-defthmd epimorphismp-auto-map
  (implies (and (extensionp e f) (extensionp k f) (embeddingp phi e k f) (equal (edegree e f) (edegree k f)))
	   (epimorphismp (auto-map phi e k f) (autos e f) (autos k f)))
  :hints (("Goal" :use (epimorphismp-auto-map-6 homomorphismp-auto-map
                        (:instance homomorphism-epimorphism (map (auto-map phi e k f)) (g (autos e f)) (h (autos k f)))))))

(defthmd isomorphismp-auto-map
  (implies (and (extensionp e f) (extensionp k f) (embeddingp phi e k f) (equal (edegree e f) (edegree k f)))
	   (isomorphismp (auto-map phi e k f) (autos e f) (autos k f)))
  :hints (("Goal" :in-theory (enable isomorphismp)
                  :use (epimorphismp-auto-map homomorphismp-auto-map endomorphismp-auto-map))))

(defthmd inv-auto-map
  (implies (and (extensionp e f) (extensionp k f) (embeddingp phi e k f) (equal (edegree e f) (edegree k f))
                (in x (autos e f)))
	   (equal (mapply (auto-map (inv-embedding phi e k f) k e f)
	                  (mapply (auto-map phi e k f)
			          x))
	          x))
  :hints (("Goal" :use (inv-inv-embedding embeddingp-inv-embedding
                        (:instance epimorphismp-auto-map-3 (e k) (k e) (phi (inv-embedding phi e k f)))))))

(in-theory (disable e))


;;----------------------------------------------------------------------------------------------------------
;;                                           Splitting Fields
;;----------------------------------------------------------------------------------------------------------

;; A polynomial over a field f splits in f if it is a product of linear factors:

(defund splits (p f)
  (equal (len (factorization p f))
         (degree p)))

;; A linear polynomial splits:

(defthmd linear-splits
  (implies (equal (degree p) 1)
           (splits p f))
  :hints (("Goal" :in-theory (enable splits))))

;; A non-linear irreducible polynomial does not split:

(defthmd irreducible-not-splits
  (implies (and (> (degree p) 1) (irreduciblep p f))
           (not (splits p f)))
  :hints (("Goal" :in-theory (enable irreduciblep splits))))

;; We shall show that p splits in f iff p has no nonlinear irreducible factor over f.  First we define a
;; function that searches for such a factor:

(defun find-nonlinear-poly (l)
  (if (consp l)
      (if (> (degree (car l)) 1)
          (car l)
	(find-nonlinear-poly (cdr l)))
    ()))

(defund nonlinear-irred-factor (p f)
  (find-nonlinear-poly (factorization p f)))

(local-defthmd find-nonlinear-poly-nonlinear
  (let ((p (find-nonlinear-poly l)))
    (implies p (and (member p l) (> (degree p) 1)))))

(defthmd nonlinear-irred-factor-nonlinear
  (implies (and (fieldp f) (polyp p f) (monicp p f) (>= (degree p) 1))
           (let ((q (nonlinear-irred-factor p f)))
             (implies q
                      (and (polyp q f) (monicp q f) (irreduciblep q f)
	                   (pdivides q p f) (> (degree q) 1)))))
  :hints (("Goal" :in-theory (enable nonlinear-irred-factor)
                  :use ((:instance find-nonlinear-poly-nonlinear (l (factorization p f)))
		        (:instance member-factorization (q p) (p (nonlinear-irred-factor p f)))))))

(local-defthmd nonlinear-find-nonlinear-poly
  (implies (and (member p l) (> (degree p) 1))
           (find-nonlinear-poly l)))

(defthmd nonlinear-divisor-nonlinear-irred-factor
  (implies (and (fieldp f) (polyp p f) (monicp p f) (>= (degree p) 1)
                (polyp q f) (monicp q f) (> (degree q) 1) (irreduciblep q f)
		(pdivides q p f))
           (nonlinear-irred-factor p f))
  :hints (("Goal" :in-theory (enable nonlinear-irred-factor)
                  :use ((:instance nonlinear-find-nonlinear-poly (p q) (l (factorization p f)))
		        (:instance pdivides-member-factorization (q p) (p q))))))

(local-defthmd not-find-nonlinear-poly
  (implies (and (member p l) (> (degree p) 1))
           (find-nonlinear-poly l)))

(defthmd not-nonlinear-irred-factor-nonlinear
  (implies (and (member q (factorization p f)) (> (degree q) 1))
           (nonlinear-irred-factor p f))
  :hints (("Goal" :in-theory (enable nonlinear-irred-factor)
                  :use ((:instance not-find-nonlinear-poly (p q) (l (factorization p f)))))))

(local-defthmd find-nonlinear-degree-prod
  (implies (and (fieldp f) (monicp-irreduciblep-listp l f))
           (if (find-nonlinear-poly l)
	       (> (degree (pmul-list l f)) (len l))
	     (= (degree (pmul-list l f)) (len l))))
  :hints (("Goal" :induct (len l))
          ("Subgoal *1/2" :in-theory (enable pone))
          ("Subgoal *1/1" :use ((:instance degree-pmul (x (car l)) (y (pmul-list (cdr l) f)))))))

;; An equivalent condition:

(defthmd splits-nonlinear-irred-factor
  (implies (and (fieldp f) (polyp p f) (monicp p f) (>= (degree p) 1))
           (iff (splits p f)
	        (not (nonlinear-irred-factor p f))))
  :hints (("Goal" :in-theory (enable splits nonlinear-irred-factor)
                  :use (pmul-list-irreduciblep-factorization
                        (:instance find-nonlinear-degree-prod (l (factorization p f)))))))

;; If p splits, then so does any divisor of p:

(defthmd pdivides-splits
  (implies (and (fieldp f) (polyp p f) (monicp p f) (>= (degree p) 1) (splits p f)
                (polyp q f) (monicp q f) (>= (degree q) 1) (pdivides q p f))
           (splits q f))
  :hints (("Goal" :use (splits-nonlinear-irred-factor
                        (:instance splits-nonlinear-irred-factor (p q))
                        (:instance nonlinear-irred-factor-nonlinear (p q))
			(:instance pdivides-transitive (x (nonlinear-irred-factor q f)) (y q) (z p))
			(:instance nonlinear-divisor-nonlinear-irred-factor (q (nonlinear-irred-factor q f)))))))

;; If p and q both split, then so does p * q:

(defthmd splits-pmul
  (implies (and (fieldp f)
                (polyp p f) (monicp p f) (>= (degree p) 1) (splits p f)
                (polyp q f) (monicp q f) (>= (degree q) 1) (splits q f))
	   (splits (pmul p q f) f))
  :hints (("Goal" :in-theory (enable monicp)
                  :use (splits-nonlinear-irred-factor
                        (:instance splits-nonlinear-irred-factor (p q))
                        (:instance splits-nonlinear-irred-factor (p (pmul p q f) ))
			(:instance nonlinear-irred-factor-nonlinear (p (pmul p q f)))
			(:instance peuclid (x p) (y q) (p (nonlinear-irred-factor (pmul p q f) f)))
			(:instance nonlinear-divisor-nonlinear-irred-factor (q (nonlinear-irred-factor (pmul p q f) f)))
			(:instance nonlinear-divisor-nonlinear-irred-factor (p q) (q (nonlinear-irred-factor (pmul p q f) f)))
			(:instance degree-pmul (x p) (y q))
			(:instance car-pmul (x p) (y q))))))

;; Let phi be an embedding of e in k over f and let p be a polynomial over e.  If p splits
;; in e, then (pembed p phi k f) splits in k.  The proof os by induction on (degree p).
;; If p is irreducible, then p is linear and (embed p phi k f) is linear and therefore
;; splits.  Otherwise, let q = (pfactor p e) and r = (pquot p q e).  Then p = q * r and
;; by pdivides-splits, q and r split in e.  By induction, we may assume (embed q phi k f)
;; and (embed r phi k f) both split in k.  But then by splits-pmul and pembed-pmul,

;;    (pembed p phi k f) = (embed q phi k f) * (embed r phi k f)

;; also splits in k.

(local-defun separablep-pembed-induct (p f)
  (declare (xargs :measure (len p) :hints (("Goal" :use (reduciblep-product)))))
  (if (and (fieldp f) (polyp p f) (monicp p f) (reduciblep p f))
      (let ((q (pfactor p f)))
	(list (separablep-pembed-induct q f)
	      (separablep-pembed-induct (pquot p q f) f)))
    t))


(defthmd splits-pembed
  (implies (and (extensionp e f) (extensionp k f) (embeddingp phi e k f)
                (polyp p e) (monicp p e) (>= (degree p) 1) (splits p e))
	   (splits (pembed p phi k f) k))
  :hints (("Goal" :induct (separablep-pembed-induct p e))
          ("Subgoal *1/2" :in-theory (enable irreduciblep)
	                  :use ((:instance irreducible-not-splits (f e))
	                        (:instance linear-splits (f k) (p (pembed p phi k f)))))
          ("Subgoal *1/1" :use ((:instance reduciblep-product (f e))
	                        (:instance pdivides-multiple (f e) (x (pfactor p e)) (y (pquot p (pfactor p e) e)))
	                        (:instance pdivides-multiple (f e) (y (pfactor p e)) (x (pquot p (pfactor p e) e)))
				(:instance pmul-comm (f e) (x (pfactor p e)) (y (pquot p (pfactor p e) e)))
				(:instance pdivides-splits (f e) (q (pfactor p e)))
				(:instance pdivides-splits (f e) (q (pquot p (pfactor p e) e)))
				(:instance polyp-pembed (p (pfactor p e)))
				(:instance polyp-pembed (p (pquot p (pfactor p e) e)))
				(:instance monicp-pembed (p (pfactor p e)))
				(:instance monicp-pembed (p (pquot p (pfactor p e) e)))
				(:instance pembed-pmul (p (pfactor p e)) (q (pquot p (pfactor p e) e)))
				(:instance splits-pmul (f k) (p (pembed (pfactor p e) phi k f)) (q (pembed (pquot p (pfactor p e) e) phi k f)))))))


;;----------------------------------------------------------------------------

(local-defun find-dup (l)
  (if (consp l)
      (if (member (car l) (cdr l))
          (car l)
	(find-dup (cdr l)))
    ()))

(local-defthmd not-find-dup-len-1
  (implies (and (fieldp f) (feltsp p f) (equal (degree p) 1))
           (equal (list (car p) (cadr p))
	          p))
  :hints (("Goal" :expand ((len p) (LEN (CDR P)) (LEN (CDDR P)) (FELTSP P F) (feltsp (cdr p) f)))))
  
(local-defthmd not-find-dup-len-2
  (implies (and (fieldp f) (feltp x f)
                (polyp p f) (monicp p f))
	   (iff (equal p (list (fone f) (fneg x f)))
	        (and (equal (degree p) 1)
		     (equal x (fneg (cadr p) f)))))
  :hints (("Goal" :in-theory (enable monicp polyp)
                  :use (not-find-dup-len-1 (:instance fneg-fneg (x (cadr p)))))))

(local-defthm not-find-dup-len-3
  (implies (and (fieldp f)
                (polyp p f) (monicp p f) (equal (degree p) 1)
                (polyp q f) (monicp q f) (equal (degree q) 1)
		(equal (fneg (cadr p) f) (fneg (cadr q) f)))
	   (equal p q))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable polyp)
                  :use ((:instance not-find-dup-len-2 (x (fneg (cadr p) f)))
                        (:instance not-find-dup-len-2 (x (fneg (cadr p) f)) (p q))))))
                        
(local-defthmd not-find-dup-len-4
  (implies (and (fieldp f)
                (monicp-irreduciblep-listp l f)
		(polyp p f)
		(= (degree p) 1)
		(monicp p f)
		(member (fneg (cadr p) f) (proots-aux l f)))
	   (member p l))
  :hints (("Goal" :induct (len l))
          ("Subgoal *1/1" :use ((:instance not-find-dup-len-3 (q (car l)))))))

(local-defthmd not-find-dup-len
  (implies (and (fieldp f)
                (monicp-irreduciblep-listp l f)
	        (not (find-nonlinear-poly l))
	        (not (find-dup l)))
	   (equal (len (proots-aux l f))
	          (len l)))
  :hints (("Goal" :induct (len l))
          ("Subgoal *1/1" :use ((:instance not-find-dup-len-4 (l (cdr l)) (p (car l)))))))

(defthmd pdivides-pmul-pmul
  (implies (and (fieldp f) (polyp x f) (polyp y f) (polyp z f) (pdivides y z f))
           (pdivides (pmul x y f) (pmul x z f) f))
  :hints (("Goal" :use ((:instance pdivides-pquot (x y) (y z))
                        (:instance pmul-assoc (z (pquot z y f)))
			(:instance polyp-pquot-prem (x z))
			(:instance pdivides-multiple (x (pmul x y f)) (y (pquot z y f)))))))
 
(local-defthm find-dup-multiple-prootp-1
  (implies (and (fieldp f)
                (monicp-irreduciblep-listp l f)
		(find-dup l))
	   (polyp (find-dup l) f)))

(local-defthmd find-dup-multiple-prootp-2
  (implies (and (fieldp f)
                (monicp-irreduciblep-listp l f)
		(find-dup l))
	   (pdivides (pmul (find-dup l) (find-dup l) f)
	             (pmul-list l f)
		     f))
  :hints (("Goal" :induct (len l))
          ("Subgoal *1/1" :use ((:instance pdivides-pmul-listp (p (car l)) (l (cdr l)))
	                        (:instance pdivides-pmul-pmul (x (car l)) (y (car l)) (z (pmul-list (cdr l) f)))
				(:instance pdivides-pmul (x (pmul (find-dup (cdr l)) (find-dup (cdr l)) f)) (y (pmul-list (cdr l) f)) (z (car l)))
				(:instance pmul-comm (x (car l)) (y (pmul-list (cdr l) f)))))))

(local-defthmd find-dup-multiple-prootp-3
  (implies (and (fieldp f)
                (polyp p f)
		(monicp p f)
		(= (degree p) 1))
	   (and (feltp (fneg (cadr p) f) f)
	        (equal (root-poly (fneg (cadr p) f) f)
		       p)))
  :hints (("Goal" :in-theory (enable root-poly polyp)
                  :use ((:instance not-find-dup-len-2 (x (fneg (cadr p) f)))))))

(local-defthmd find-dup-multiple-prootp-4
  (let ((p (find-dup l)))
    (implies (and (fieldp f)
                  (monicp-irreduciblep-listp l f)
                  (not (find-nonlinear-poly l))
		  p)
	     (and (polyp p f)
	  	  (monicp p f)
		  (= (degree p) 1)))))

(local-defthmd find-dup-multiple-prootp
  (let* ((p (find-dup l))
         (r (fneg (cadr p) f)))
    (implies (and (fieldp f)
                  (monicp-irreduciblep-listp l f)
	          (not (find-nonlinear-poly l))
	          p)
	     (and (feltp r f)
	          (multiple-prootp r (pmul-list l f) f))))
  :hints (("Goal" :in-theory (enable multiple-prootp)
                  :expand ((PPOWER (FIND-DUP L) 1 F))
                  :use (find-dup-multiple-prootp-2 find-dup-multiple-prootp-4
                        (:instance find-dup-multiple-prootp-3 (p (find-dup l)))))))

(local-defthmd separablep-find-dup
  (implies (and (fieldp f) (polyp p f) (monicp p f) (>= (degree p) 1) (splits p f) (separablep p f))
           (not (find-dup (factorization p f))))
  :hints (("Goal" :in-theory (enable nonlinear-irred-factor)
                  :use (splits-nonlinear-irred-factor pmul-list-irreduciblep-factorization
                        (:instance find-dup-multiple-prootp-4 (l (factorization p f)))
                        (:instance find-dup-multiple-prootp (l (factorization p f)))
                        (:instance separable-no-multiple-root (x (fneg (cadr (find-dup (factorization p f))) f)))))))
	   
(defthmd len-proots-max
  (implies (and (fieldp f) (polyp p f) (monicp p f) (>= (degree p) 1)
                (splits p f) (separablep p f))
           (equal (len (proots p f))
	          (degree p)))
  :hints (("Goal" :in-theory (enable splits proots nonlinear-irred-factor)
                  :use (separablep-find-dup pmul-list-irreduciblep-factorization splits-nonlinear-irred-factor
                        (:instance not-find-dup-len (l (factorization p f)))))))

;;----------------------------------------------------------------------------

;; Let p be a polynomial over f.  An extension e of f is an extension by roots of p if e is constructed by successively
;; adjoining roots of p:

(defun extension-by-roots-p (p e f)
  (if (extensionp e f)
      (if (equal e f)
          t
	(and (extension-by-roots-p p (cdr e) f)
	     (pdivides (car e) (plift p f (cdr e)) (cdr e))))
    ()))

;; Let p be a polynomial over f and let e and k be extensions of f. If e is an extension by roots of p and p splits in k, then
;; we can construct an embedding of e in k over f:

(defun embedding-of-extension-by-roots (e k f)
  (if (equal e f)
      ()
    (and (consp e)
         (let ((phi (embedding-of-extension-by-roots (cdr e) k f)))
           (cons (car (proots (pembed (car e) phi k f) k))
	         phi)))))

;; Let phi = embedding-of-extension-by-roots e k f).  To prove that phi is indeed an embedding of e, we assume that (cdr phi) is an embedding of (cdr e),
;; and we must show that (pembed (car e) (cdr phi) k f) has a root in k.  Since (car e) divides (plift p f (cdr e)), (pembed (car e) (cdr phi) k f)
;; divides (pembed (plift p f (cdr e)) (cdr phi) k f), which, according to pembed fixes, is (plift p f k).  Since (plift p f k) splits in k, so does its
;; divisor (pembed (car e) (cdr phi) k f), which must therefore have at least 1 root.

(in-theory (enable monicp-plift polyp-plift))

(defthmd pembed-splits
  (implies (and (extensionp e f) (extensionp k f) (embeddingp phi e k f)
                (polyp p f) (monicp p f) (>= (degree p) 1) (splits (plift p f k) k)
		(polyp q e) (monicp q e) (>= (degree q) 1) (pdivides q (plift p f e) e))
	   (let ((s (pembed q phi k f)))
	     (and (polyp s k)
	          (monicp s k)
		  (>= (degree s) 1)
		  (pdivides s (plift p f k) k)
		  (splits s k))))
  :hints (("Goal" :use (pembed-fixes
                        (:instance pdivides-pquot (x q) (y (plift p f e)) (f e))
			(:instance pembed-pmul (p q) (q (pquot (plift p f e) q e)))
			(:instance polyp-pquot-prem (x (plift p f e)) (y q) (f e))
			(:instance polyp-pembed (p q))
			(:instance polyp-pembed (p (pquot (plift p f e) q e)))
			(:instance monicp-pembed (p q))
			(:instance pdivides-multiple (x (pembed q phi k f)) (y (pembed (pquot (plift p f e) q e) phi k f)) (f k))
			(:instance pdivides-splits (q (pembed q phi k f)) (p (plift p f k)) (f k))))))

(defthmd proot-pembed
  (implies (and (extensionp e f) (extensionp k f) (embeddingp phi e k f)
                (polyp p f) (monicp p f) (>= (degree p) 1) (splits (plift p f k) k)
		(polyp q e) (monicp q e) (>= (degree q) 1) (pdivides q (plift p f e) e))
	   (consp (proots (pembed q phi k f) k)))
  :hints (("Goal" :use (pembed-splits
                        (:instance find-dup-multiple-prootp-3 (f k) (p (car (factorization (pembed q phi k f) k))))
			(:instance splits-nonlinear-irred-factor (p (pembed q phi k f)) (f k))
			(:instance member-proots (x (fneg (cadr (car (factorization (pembed q phi k f) k))) k)) (p (pembed q phi k f)) (f k))
			(:instance not-nonlinear-irred-factor-nonlinear (p (pembed q phi k f)) (q (car (factorization (pembed q phi k f) k))) (f k))
			(:instance pdivides-member-factorization (q (pembed q phi k f)) (p (car (factorization (pembed q phi k f) k))) (f k))
			(:instance prootp-member-factorization (x (fneg (cadr (car (factorization (pembed q phi k f) k))) k)) (p (pembed q phi k f)) (f k))
			(:instance member-factorization (q (pembed q phi k f)) (p (car (factorization (pembed q phi k f) k))) (f k))))))

(defthmd embeddingp-embedding-of-extension-by-roots
  (implies (and (fieldp f) (polyp p f) (monicp p f) (>= (degree p) 1)
                (extension-by-roots-p p e f)
                (extensionp k f) (splits (plift p f k) k))
	   (embeddingp (embedding-of-extension-by-roots e k f) e k f))
  :hints (("Goal" :induct (extension-by-roots-p p e f))
          ("Subgoal *1/1" :in-theory (enable embeddingp) :expand ((EMBEDDING-OF-EXTENSION-BY-ROOTS E K E)))
	  ("Subgoal *1/2" :in-theory (enable embeddingp)
	                  :use ((:instance fieldp (f e))
	                        (:instance proot-pembed (e (cdr e)) (phi (embedding-of-extension-by-roots (cdr e) k f)) (q (car e)))
				(:instance feltsp-proots (p (pembed (car e) (embedding-of-extension-by-roots (cdr e) k f) k f)) (f k))
				(:instance polyp-pembed (p (car e)) (e (cdr e)) (phi (embedding-of-extension-by-roots (cdr e) k f)))
				(:instance monicp-pembed (p (car e)) (e (cdr e)) (phi (embedding-of-extension-by-roots (cdr e) k f)))
	                        (:instance member-proots (x (car (proots (pembed (car e) (embedding-of-extension-by-roots (cdr e) k f) k f) k)))
							 (f k)
							 (p (pembed (car e) (embedding-of-extension-by-roots (cdr e) k f) k f)))))))


;;----------------------------------------------------------------------------

;; If the hypothesis of embeddingp-embedding-of-extension-by-roots is extended with the assumption that p is separable, then 
;; the number of such embeddings is the degree of e over f.  (Note that this is the maximum  number allowed by the lemma
;; len-embeddings.)

(defthmd proots-pembed-separablep
  (implies (and (extensionp e f) (extensionp k f) (embeddingp phi e k f)
                (polyp p f) (monicp p f) (>= (degree p) 1) (splits (plift p f k) k) (separablep p f)
		(polyp q e) (monicp q e) (>= (degree q) 1) (pdivides q (plift p f e) e))
	   (equal (len (proots (pembed q phi k f) k))
	          (degree q)))
  :hints (("Goal" :in-theory (disable len-plift len-pembed)
                  :use (pembed-splits
                        (:instance pdivides-separablep (f k) (q (pembed q phi k f)) (p (plift p f k)))
                        (:instance separablep-extension (e k))
			(:instance len-proots-max (p (pembed q phi k f)) (f k))
			(:instance len-plift (e k))
			(:instance len-pembed (p q))))))

(local-defthm len-consl
  (equal (len (consl r x))
         (len r)))

(local-defthmd len-embeddings-separablep-1
  (implies (and (extensionp e f) (extensionp k f) (not (equal e f)) (embeddingp phi (cdr e) k f)
                (polyp p f) (monicp p f) (>= (degree p) 1) (splits (plift p f k) k) (separablep p f)
		(pdivides (car e) (plift p f (cdr e)) (cdr e)))
	   (equal (len (simple-embedding-extensions phi e k f))
	          (degree (car e))))
  :hints (("Goal" :in-theory (enable simple-embedding-extensions fieldp)
                  :use ((:instance proots-pembed-separablep (e (cdr e)) (q (car e)))))))

(local-defthmd len-embeddings-separablep-2
  (implies (and (extensionp e f) (extensionp k f) (not (equal e f))
                (sublistp l (embeddings (cdr e) k f))
		(polyp p f) (monicp p f) (>= (degree p) 1) (splits (plift p f k) k) (separablep p f)
		(pdivides (car e) (plift p f (cdr e)) (cdr e)))
           (equal (len (simple-embeddings-extensions l e k f))
	          (* (len l) (degree (car e)))))
  :hints (("Subgoal *1/1" :use ((:instance all-embeddings (e (cdr e)) (phi (car l)))
                                (:instance len-embeddings-separablep-1 (phi (car l)))))))

(local-defthmd len-embeddings-separablep-3
  (implies (and (extensionp e f) (extensionp k f) (not (equal e f))
		(polyp p f) (monicp p f) (>= (degree p) 1) (splits (plift p f k) k) (separablep p f)
		(pdivides (car e) (plift p f (cdr e)) (cdr e))
                (equal (len (embeddings (cdr e) k f))
		       (edegree (cdr e) f)))
	   (equal (len (embeddings e k f))
	          (edegree e f)))
  :hints (("Goal" :expand ((fieldp e) (embeddings e k f) (edegree e f))
                  :nonlinearp t
                  :use ((:instance len-embeddings-separablep-2 (l (embeddings (cdr e) k f)))))))

(in-theory (enable embeddings))

(defthmd len-embeddings-separablep
  (implies (and (extensionp e f) (extensionp k f)
                (polyp p f) (monicp p f) (>= (degree p) 1) (separablep p f)
		(extension-by-roots-p p e f) (splits (plift p f k) k))
	   (equal (len (embeddings e k f))
	          (edegree e f)))
  :hints (("Goal" :induct (embeddings e k f))
          ("Subgoal *1/1" :use (len-embeddings-separablep-3))))


;;----------------------------------------------------------------------------

;; We shall prove that the degree of an extension by roots of p over f is at most the factorial of the degree of p.
;; This requires a couple of lemmas.  This is the first:

;; Let p be a non-constant monic polynomial over f and suppose p does not split in f.  Let q be a nonlinear irreducible factot
;; of p,  let e be the simple extension field (q . f), and let p' = (plift p f e) and q' = (plift q f e).  The number of roots
;; of p' in e is greater than the number of roots of p in f.

;; First note that each root of p in f lifts to a unique root of p' in e:

(defthmd prootp-flift
  (implies (and (extensionp e f) (feltp x f) (polyp p f) (prootp x p f))
           (prootp (flift x f e) (plift p f e) e))
  :hints (("Goal" :in-theory (enable prootp)  
                  :use (flift-peval ))))

(local-defthmd dlistp-plift-1
  (implies (and (extensionp e f) (feltsp l f) (feltp x f) (not (member x l)))
           (not (member (flift x f e)
	                (plift l f e))))
  :hints (("Subgoal *1/3" :in-theory (enable flift-1-1))))

(defthmd dlistp-plift
  (implies (and (extensionp e f) (feltsp l f) (dlistp l))
           (dlistp (plift l f e)))
  :hints (("Subgoal *1/3" :in-theory (enable dlistp-plift-1))))

(defthmd dlistp-plift-proots
  (implies (and (extensionp e f) (polyp p f) (monicp p f) (>= (degree p) 1))
           (dlistp (plift (proots p f) f e)))
  :hints (("Goal" :use (dlistp-proots feltsp-proots
                        (:instance dlistp-plift (l (proots p f)))))))

(local-defthmd sublistp-plift-proots-1
  (implies (and (extensionp e f) (polyp p f) (monicp p f) (>= (degree p) 1)
                 (feltsp l f) (sublistp l (proots p f)))
           (sublistp (plift l f e)
	             (proots (plift p f e) e)))		     
  :hints (("Goal" :induct (len l))
          ("Subgoal *1/1" :use ((:instance member-proots (x (flift (car l) f e)) (p (plift p f e)) (f e))
	                        (:instance member-proots (x (car l))))
	                  :in-theory (enable prootp-flift polyp-plift))))

(defthmd sublistp-plift-proots
  (implies (and (extensionp e f) (polyp p f) (monicp p f) (>= (degree p) 1))
           (sublistp (plift (proots p f) f e)
	             (proots (plift p f e) e)))		     
  :hints (("Goal" :use (feltsp-proots (:instance sublistp-plift-proots-1 (l (proots p f)))))))

;; Now (primitive e) is a root of p', since it is a root of q' and q' divides p:

(defthmd pdivides-prootp
  (implies (and (fieldp f) (polyp p f) (not (equal p (pzero f)))
                (polyp q f) (pdivides p q f)
                (feltp x f) (prootp x p f))
	   (prootp x q f))
  :hints (("Goal" :use (prootp-pdivides
                        (:instance prootp-pdivides (p q))
			(:instance pdivides-transitive (x (root-poly x f)) (y p) (z q))))))

(defthmd prootp-primitive-plift
  (implies (and (fieldp f) (polyp p f) (monicp p f) (>= (degree p) 1)
                (polyp q f) (monicp q f) (irreduciblep q f) (> (degree q) 1) (pdivides q p f))
           (let ((e (cons q f)))
	     (and (fieldp e)
	          (member (primitive e) (proots (plift p f e) e)))))
  :hints (("Goal" :in-theory (enable fieldp)
                  :use ((:instance prootp-primitive (f (cons q f)))
			(:instance pdivides-plift (y q) (x p) (e (cons q f)))
			(:instance polyp-plift (e (cons q f)))
			(:instance polyp-plift (p q) (e (cons q f)))
			(:instance monicp-plift (e (cons q f)))
			(:instance monicp-plift (p q) (e (cons q f)))
			(:instance plift-pzero (p q) (e (cons q f)))
			(:instance pdivides-prootp (x (primitive (cons q f))) (f (cons q f))
			                           (p (plift q f (cons q f)))
						   (q (plift p f (cons q f))))
			(:instance member-proots (x (primitive (cons q f)))
			                         (p (plift p f (cons q f)))
			                         (f (cons q f)))))))

;; Furthermore,  (primitive e) is not lifted from f, since its minimal polynomial p is nonlinear:
 
(defthmd primitive-not-lifted
  (implies (and (fieldp f) (consp f) (feltsp l (cdr f)))
           (not (member (primitive f) (plift l (cdr f) f))))
  :hints (("Goal" :induct (len l))
          ("Subgoal *1/1" :in-theory (enable root-poly)
	                  :use (min-poly-primitive fieldp
	                        (:instance min-poly-flift (x (car l)) (f (cdr f)) (e f))))))

(defthmd not-member-primitive-plift-proots
  (implies (and (fieldp f) (consp f) (polyp p (cdr f)) (monicp p (cdr f)) (>= (degree p) 1))
           (not (member (primitive f) (plift (proots p (cdr f)) (cdr f) f))))
  :hints (("Goal" :use ((:instance primitive-not-lifted (l (proots p (cdr f))))
                        (:instance feltsp-proots (f (cdr f)))))))

;; Thus, we have the following:

(defthmd len-proots-increases
  (implies (and (fieldp f) (polyp p f) (monicp p f) (>= (degree p) 1)
                (polyp q f) (monicp q f) (irreduciblep q f) (> (degree q) 1) (pdivides q p f))
	   (let ((e (cons q f)))
	     (> (len (proots (plift p f e) e))
	        (len (proots p f)))))
  :hints (("Goal" :in-theory (enable polyp-plift)
                  :use (prootp-primitive-plift
                        (:instance sublistp-plift-proots (e (cons q f)))
			(:instance dlistp-plift-proots (e (cons q f)))
                        (:instance len-proper-sublist (l (plift (proots p f) f (cons q f)))
			                              (m (proots (plift p f (cons q f)) (cons q f)))
						      (x (primitive (cons q f))))
			(:instance not-member-primitive-plift-proots (f (cons q f)))))))

;; Now let e be an extension by roots of p over f.  let d = (degree p) and n = (len e) - (len f).  It follows from
;; len-proots-increases by induction that n <= (len (proots (plift p f e) e):

(defthmd len-proots-extension-by-roots
  (implies (and (extensionp e f)
                (polyp p f)  (monicp p f) (>= (degree p) 1)
		(extension-by-roots-p p e f))
	   (<= (- (len e) (len f)) (len (proots (plift p f e) e))))
  :hints (("Goal" :induct (extension-by-roots-p p e f))
          ("Subgoal *1/2" :use ((:instance len-proots-increases (f (cdr e)) (q (car e)) (p (plift p f (cdr e))))
	                        (:instance fieldp (f e))))))

;; We also need the following:

(local-defthmd degree-irreducible-factor-bound-1
  (implies (and (fieldp f) (monicp-irreduciblep-listp l f) (not (equal (pmul-list l f) (pzero f))) (> (degree q) 1))
           (if (member q l)
	       (<= (+ (len (proots-aux l f)) (degree q))
	           (degree (pmul-list l f)))
	     (<= (len (proots-aux l f))
	         (degree (pmul-list l f)))))
  :hints (("Goal" :induct (len l))
          ("Subgoal *1/1" :use ((:instance degree-pmul (x (car l)) (y (pmul-list (cdr l) f)))))
	  ("Subgoal *1/2" :in-theory (enable pone))))
                
(defthmd degree-irreducible-factor-bound
  (implies (and (fieldp f) (polyp p f) (monicp p f) (>= (degree p) 1)
                (polyp q f) (monicp q f) (irreduciblep q f) (> (degree q) 1) (pdivides q p f))
           (<= (degree q) (- (degree p) (len (proots p f)))))
  :hints (("Goal" :in-theory (enable proots)
                  :use (pmul-list-irreduciblep-factorization
		        (:instance degree-irreducible-factor-bound-1 (l (factorization p f)))
		        (:instance pdivides-member-factorization (p q) (q p))))))

;; It follows from the last 2 results by induction that (edegree e f) <= d * (d - 1) * ... * (d - n) = d!/(d - n - 1)!,
;; which is a strong version of the desired result:

(local-defun fact-quot (d n)
  (if (zp n)
      1
    (* (fact-quot d (1- n))
       (- d (1- n)))))

(local-defthmd natp-fact-quot
  (implies (and (natp d) (natp n) (>= d (1- n)))
           (natp (fact-quot d n))))

(local-defthmd hack-1
  (implies (and (natp a) (posp b) (natp c) (natp d) (natp e) (natp f) (natp g)
                (<= a (+ f c))
		(<= (+ b c) e)
		(<= d g))
	   (<= (+ (* b d) g (* a g))
	       (+ d (* f g) (* e g))))	       
  :hints (("Goal" :nonlinearp t)))

(local-defthmd degree-extension-by-roots-bound-induction-1
  (implies (and (extensionp e f)
                (polyp p f) (monicp p f) (>= (degree p) 1)
		(extension-by-roots-p p e f))
	   (<= (edegree e f)
	       (fact-quot (degree p) (- (len e) (len f)))))
  :hints (("Goal" :induct (extension-by-roots-p p e f))
          ("Subgoal *1/2" :in-theory (e/d (polyp-plift)
	                                  (len-flist flistnp len-vlistnp vlistnp flistnp fp-member consp-groupp cyclicp len-fmatp cyclicp-groupp subgroupp-groupp))
	                  :use ((:instance len-proots-extension-by-roots (e (cdr e)))
	                        (:instance degree-irreducible-factor-bound (f (cdr e)) (q (car e)) (p (plift p f (cdr e))))
				(:instance len-extends (e (cdr e)))
				;(:instance len-proots-bound (f (cdr e)) (p (plift p f (cdr e))))
	                        (:instance fieldp (f e))
				(:instance posp-edegree (e (cdr e)))
				(:instance natp-fact-quot (d (1- (len p))) (n (- (len (cdr e)) (len f))))
				(:instance hack-1 (a (len (cdr e))) (b (len (car e))) (c (LEN (PROOTS (PLIFT P F (CDR E)) (CDR E))))
				                  (d (edegree (cdr e) f)) (e (len p)) (f (len f)) (g (FACT-QUOT (+ -1 (LEN P)) (+ (- (LEN F)) (LEN (CDR E))))))))))


(local-defthmd hack-2
  (implies (and (natp fact-quot) (posp f) (posp f1) (natp d) (natp n) (>= d n) (equal fact-quot (/ f (* (1+ (- d n)) f1))))
           (equal (* fact-quot (1+ (- d n))) (/ f f1))))

(local-defthmd fact-quot-rewrite
  (implies (and (natp d) (natp n) (>= d n))
           (equal (fact-quot d n)
	          (/ (fact d) (fact (- d n)))))		  
  :hints (("Subgoal *1/5" :use ((:instance hack-2 (fact-quot (fact-quot d (1- n))) (f (fact d)) (f1 (fact (- d n))))
                                (:instance natp-fact-quot (n (1- n)))))))

(defthmd degree-extension-by-roots-bound-induction
  (implies (and (extensionp e f)
                (polyp p f) (monicp p f) (>= (degree p) 1)
		(extension-by-roots-p p e f))
	   (<= (edegree e f)
	       (/ (fact (degree p))
	          (fact (- (degree p) (- (len e) (len f)))))))
  :hints (("Goal" :use (degree-extension-by-roots-bound-induction-1 len-proots-extension-by-roots len-extends
                        (:instance fact-quot-rewrite (d (degree p)) (n (- (len e) (len f))))
			(:instance len-proots-bound (f e) (p (plift p f e)))))))

(defthmd posp-fact
  (implies (natp n)
           (posp (fact n))))

(local-defthmd fact-quot-bound
  (implies (and (extensionp e f)
                (polyp p f) (monicp p f) (>= (degree p) 1)
		(extension-by-roots-p p e f))
	   (and (rationalp (/ (fact (degree p))
	                      (fact (- (degree p) (- (len e) (len f))))))
	        (<= (/ (fact (degree p))
	               (fact (- (degree p) (- (len e) (len f)))))
	            (fact (degree p)))))
  :hints (("Goal" :use (degree-extension-by-roots-bound-induction len-proots-extension-by-roots len-extends
			(:instance len-proots-bound (f e) (p (plift p f e)))
			(:instance posp-fact (n (degree p)))
			(:instance posp-fact (n (- (degree p) (- (len e) (len f)))))))))

(defthmd degree-extension-by-roots-bound
  (implies (and (extensionp e f)
                (polyp p f) (monicp p f) (>= (degree p) 1)
		(extension-by-roots-p p e f))
	   (<= (edegree e f)
	       (fact (degree p))))
  :hints (("Goal" :in-theory (theory 'minimal-theory)
                  :use (degree-extension-by-roots-bound-induction fact-quot-bound))))

;;----------------------------------------------------------------------------

;; An extension e of f is a splitting field of p if e is an extension by roots of p and p splits in e:

(defund splitting-field-p (p e f)
  (and (extension-by-roots-p p e f)
       (splits (plift p f e) e)))

;; Every polynomial has a splitting field, as constructed by the function splitting-field, defined below.
;; The admissibility of this function depends on the lemma len-proots-increases, which guarantees that the declared measure
;; decreases on the recursive call:

(local-defthmd prootp-primitive-plift-2
  (implies (and (fieldp f) (polyp p f) (monicp p f) (>= (degree p) 1) (not (splits p f)))
           (let* ((q (nonlinear-irred-factor p f))
	          (e (cons q f)))
	     (and (fieldp e)
	          (member (primitive e) (proots (plift p f e) e)))))
  :hints (("Goal" :in-theory (enable fieldp)
                  :use (splits-nonlinear-irred-factor nonlinear-irred-factor-nonlinear
                        (:instance prootp-primitive (f (cons (nonlinear-irred-factor p f) f)))
			(:instance pdivides-plift (y (nonlinear-irred-factor p f)) (x p) (e (cons (nonlinear-irred-factor p f) f)))
			(:instance polyp-plift (e (cons (nonlinear-irred-factor p f) f)))
			(:instance polyp-plift (p (nonlinear-irred-factor p f)) (e (cons (nonlinear-irred-factor p f) f)))
			(:instance monicp-plift (e (cons (nonlinear-irred-factor p f) f)))
			(:instance monicp-plift (p (nonlinear-irred-factor p f)) (e (cons (nonlinear-irred-factor p f) f)))
			(:instance plift-pzero (p (nonlinear-irred-factor p f)) (e (cons (nonlinear-irred-factor p f) f)))
			(:instance pdivides-prootp (x (primitive (cons (nonlinear-irred-factor p f) f))) (f (cons (nonlinear-irred-factor p f) f))
			                           (p (plift (nonlinear-irred-factor p f) f (cons (nonlinear-irred-factor p f) f)))
						   (q (plift p f (cons (nonlinear-irred-factor p f) f))))
			(:instance member-proots (x (primitive (cons (nonlinear-irred-factor p f) f)))
			                         (p (plift p f (cons (nonlinear-irred-factor p f) f)))
			                         (f (cons (nonlinear-irred-factor p f) f)))))))

(defthmd splitting-field-measure-decreases
  (implies (and (fieldp f) (polyp p f) (monicp p f) (>= (degree p) 1) (not (splits p f)))
           (let* ((q (nonlinear-irred-factor p f))
	          (e (cons q f)))
	     (< (nfix (- (degree (plift p f e)) (len (proots (plift p f e) e))))
	        (nfix (- (degree p) (len (proots p f)))))))	        
  :hints (("Goal" :in-theory (enable polyp-plift)
                  :use (prootp-primitive-plift-2 len-proots-bound 
                        (:instance len-proots-bound (p (plift p f (cons (nonlinear-irred-factor p f) f))) (f (cons (nonlinear-irred-factor p f) f)))
                        (:instance sublistp-plift-proots (e (cons (nonlinear-irred-factor p f) f)))
			(:instance dlistp-plift-proots (e (cons (nonlinear-irred-factor p f) f)))
                        (:instance len-proper-sublist (l (plift (proots p f) f (cons (nonlinear-irred-factor p f) f)))
			                              (m (proots (plift p f (cons (nonlinear-irred-factor p f) f)) (cons (nonlinear-irred-factor p f) f)))
						      (x (primitive (cons (nonlinear-irred-factor p f) f))))
			(:instance not-member-primitive-plift-proots (f (cons (nonlinear-irred-factor p f) f)))))))

(defun splitting-field (p f)
  (declare (xargs :measure (nfix (- (degree p) (len (proots p f))))
                  :hints (("Goal" :use (splitting-field-measure-decreases)))))
  (if (and (fieldp f) (polyp p f) (monicp p f) (>= (degree p) 1))
      (if (splits p f)
          f
	(let* ((q (nonlinear-irred-factor p f))
	       (e (cons q f)))
	  (splitting-field (plift p f e) e)))
    ()))

(defthmd extensionp-splitting-field
  (implies (and (fieldp f) (polyp p f) (monicp p f) (>= (degree p) 1))
           (extensionp (splitting-field p f) f))
  :hints (("Goal" :induct (splitting-field p f))
          ("Subgoal *1/2" :in-theory (enable polyp-plift)
	                  :use (prootp-primitive-plift-2))))

(defthmd splits-splitting-field
  (implies (and (fieldp f) (polyp p f) (monicp p f) (>= (degree p) 1))
           (let ((e (splitting-field p f)))
             (splits (plift p f e) e)))
  :hints (("Goal" :induct (splitting-field p f))
          ("Subgoal *1/2" :in-theory (enable polyp-plift)
	                  :use (prootp-primitive-plift-2
			        (:instance extensionp-splitting-field (f (cons (nonlinear-irred-factor p f) f))
				                                      (p (plift p f (cons (nonlinear-irred-factor p f) f))))
			        (:instance plift-comp (x p) (e (splitting-field p f)) (d (cons (nonlinear-irred-factor p f) f)))))))

(defthmd extension-by-roots-transitive
  (implies (and (extensionp d f) (extension-by-roots-p p d f)
                (extensionp e d) (extension-by-roots-p (plift p f d) e d))
	   (extension-by-roots-p p e f))
  :hints (("Subgoal *1/6" :use (extends-trans))))

(defthmd extension-by-roots-p-splitting-field
  (implies (and (fieldp f) (polyp p f) (monicp p f) (>= (degree p) 1))
           (extension-by-roots-p p (splitting-field p f) f))
  :hints (("Goal" :induct (splitting-field p f))
          ("Subgoal *1/2" :in-theory (enable polyp-plift)
	                  :use (prootp-primitive-plift-2 nonlinear-irred-factor-nonlinear splits-nonlinear-irred-factor
			        (:instance extensionp-splitting-field (f (cons (nonlinear-irred-factor p f) f))
				                                      (p (plift p f (cons (nonlinear-irred-factor p f) f))))
			        (:instance plift-comp (x p) (e (splitting-field p f)) (d (cons (nonlinear-irred-factor p f) f)))
				(:instance extension-by-roots-transitive (e (splitting-field p f))
				                                         (d (cons (nonlinear-irred-factor p f) f)))))))

(defthmd splitting-field-p-splitting-field
  (implies (and (fieldp f) (polyp p f) (monicp p f) (>= (degree p) 1))
           (splitting-field-p p (splitting-field p f) f))
  :hints (("Goal" :in-theory (enable splitting-field-p)
                  :use (splits-splitting-field extension-by-roots-p-splitting-field))))


;;----------------------------------------------------------------------------------------------------------
;;                                             Galois Extensions
;;----------------------------------------------------------------------------------------------------------

;; e is a galois extension of f if e is a splitting field of a separable polynomial over f:

(defun-sk galoisp (e f)
  (exists (p)
    (and (polyp p f)
         (monicp p f)
	 (>= (degree p) 1)
         (separablep p f)
	 (splitting-field-p p e f))))

;; In the trivial case, f is a splitting field of the separable polynomial (root-poly (fone f) f):

(local-defthmd galoisp-trivial-1
  (implies (fieldp f)
           (let ((p (root-poly (fone f) f)))
	     (and (polyp p f)
	          (monicp p f)
		  (= (degree p) 1)
		  (separablep p f))))
  :hints (("Goal" :in-theory (enable monicp root-poly)
                  :use ((:instance polyp-root-poly (x (fone f)))
		        (:instance separablep-linear (p (root-poly (fone f) f)))))))

(local-defthmd galoisp-trivial-2
  (implies (fieldp f)
           (splitting-field-p (root-poly (fone f) f) f f))
  :hints (("Goal" :in-theory (enable splitting-field)
                  :use (galoisp-trivial-1
		        (:instance linear-splits  (p (root-poly (fone f) f)))
		        (:instance splitting-field-p-splitting-field (p (root-poly (fone f) f))))
		  :expand ((SPLITTING-FIELD (ROOT-POLY (FONE F) F) f)))))

(defthmd galoisp-trivial
  (implies (fieldp f)
           (galoisp f f))
  :hints (("Goal" :use (galoisp-trivial-1 galoisp-trivial-2
                        (:instance galoisp-suff (e f) (p (root-poly (fone f) f)))))))

;; In this case, the automorphism group is called the galois group:

(defund galois (e f) (autos e f))

;; The order of the galois group is the degree of the extension:

(defthmd order-galois-group
  (implies (and (extensionp e f) (galoisp e f))
           (equal (order (galois e f))
	          (edegree e f)))
  :hints (("Goal" :in-theory (enable galoisp galois splitting-field-p order)
                  :use ((:instance len-embeddings-separablep (k e) (p (galoisp-witness e f)))))))

;;--------------------------------------

;; Let e be a splitting field of a polynomial p over f.  Let a be an element of e that is not lifted from f
;; and let m = (min-poly a e f).  Let s = (m . f) be the simple extension of f generated by m.  Note that
;; (list a) is an embeddingp of s in e over f:

(local-defthmd pembed-nil
  (implies (feltsp p f)
           (equal (pembed p () k f)
	          (plift p f k)))
  :hints (("Subgoal *1/2" :expand ((embed (car p) nil k f)))))

(defthmd embeddingp-list-a
  (implies (and (extensionp e f) (not (equal e f)) (feltp a e) (not (fliftedp a f e)))
	   (embeddingp (list a) (cons (min-poly a e f) f) e f))
  :hints (("Goal" :in-theory (enable pembed-nil embeddingp fliftedp)
                  :use ((:instance prootp-min-poly (x a))))))

;; Let k = (splitting-field (plift p f s) s).  Let phi = (embedding-of-extension-by-roots e k f).  We
;; have shown that phi is an embedding of e in k over f.  We can also construct an embedding psi of k in
;; e over f:

(defun psi (a k e f)
  (if (equal k (cons (min-poly a e f) f))
      (list a)
    (and (consp k)
         (cons (car (proots (pembed (car k) (psi a (cdr k) e f) e f) e))
	       (psi a (cdr k) e f)))))

;; The proof of the following is essentially the same as that of embeddingp-embedding-of-extension-by-roots:

(defthmd embeddingp-psi
  (let ((s (cons (min-poly a e f) f)))
    (implies (and (extensionp e f) (not (equal e f))
                  (polyp p f) (monicp p f) (>= (degree p) 1)
		  (splitting-field-p p e f)
		  (feltp a e) (not (fliftedp a f e))
		  (extension-by-roots-p (plift p f s) k s))
	     (embeddingp (psi a k e f) k e f)))
  :hints (("Goal" :induct (extension-by-roots-p p k (cons (min-poly a e f) f)))
          ("Subgoal *1/1" :use (embeddingp-list-a))
	  ("Subgoal *1/2" :in-theory (e/d (splitting-field-p embeddingp) (plift-comp))
	                  :use ((:instance len-extends (e (cdr f)))
			        (:instance fieldp (f k))
				(:instance plift-comp (x p) (e (cdr k)) (d (cons (min-poly a e f) f)))
	                        (:instance extends-trans (e (cdr k)) (d (cons (min-poly a e f) f)))
	                        (:instance extends (e (cons (min-poly a e f) f)))
	                        (:instance proot-pembed (k e) (e (cdr k)) (phi (psi a (cdr k) e f)) (q (car k)))
				(:instance feltsp-proots (p (pembed (car k) (psi a (cdr k) e f) e f)) (f e))
				(:instance polyp-pembed (k e) (p (car k)) (e (cdr k)) (phi (psi a (cdr k) e f)))
				(:instance monicp-pembed (k e) (p (car k)) (e (cdr k)) (phi (psi a (cdr k) e f)))
	                        (:instance member-proots (x (car (proots (pembed (car k) (psi a (cdr k) e f) e f) e)))
							 (f e)
							 (p (pembed (car k) (psi a (cdr k) e f) e f)))))))

;; Let b = (flift (primitive s) s k).  Since a is fixed by (comp-embedding psi phi e e f),

;;   a = (embed a (comp-embedding psi phi e e f) e f) = (embed (embed a phi k f) psi e f).

(defun s% (a e f) (cons (min-poly a e f) f))

(defun k% (a e f p) (splitting-field (plift p f (s% a e f)) (s% a e f)))

(defun phi% (a e f p) (embedding-of-extension-by-roots e (k% a e f p) f))

(defun psi% (a e f p) (psi a (k% a e f p) e f))

(defun b% (a e f p) (flift (primitive (s% a e f)) (s% a e f) (k% a e f p)))

(defun inv% (a e f p) (inv-embedding (phi% a e f p) e (k% a e f p) f))

(local-defthmd embeddingp-phi-psi
  (implies (and (extensionp e f) (not (equal e f))
                (polyp p f) (monicp p f) (>= (degree p) 1)
		(splitting-field-p p e f)
		(feltp a e) (not (fliftedp a f e)))
	   (let* ((s (s% a e f))
	          (k (k% a e f p))
		  (phi (phi% a e f p))
		  (psi (psi% a e f p)))
	     (and (extensionp s f)
	          (extensionp k s)
	          (extensionp k f)
	          (embeddingp phi e k f)
	          (embeddingp psi k e f)
		  (equal (edegree e f)
	                 (edegree k f)))))
  :hints (("Goal" :in-theory (enable fliftedp splitting-field-p)
                  :use ((:instance embeddingp-embedding-of-extension-by-roots (k (k% a e f p)))
			(:instance plift-comp (x p) (d (s% a e f)) (e (k% a e f p)))
			(:instance prootp-min-poly (x a))
			(:instance extends-trans (d (s% a e f)) (e (k% a e f p)))
			(:instance fieldp (f (s% a e f)))
			(:instance embedding-surjective (phi (phi% a e f p)) (k (k% a e f p))) 
			(:instance splitting-field-p-splitting-field (p (plift p f (s% a e f))) (f (s% a e f)))
			(:instance embeddingp-psi (k (k% a e f p)))
                        (:instance embedding-degree-<= (k (k% a e f p)) (phi (phi% a e f p)))
                        (:instance embedding-degree-<= (k e) (e (k% a e f p)) (phi (psi% a e f p)))))))

;; By embed-flift-gen and embed-primitive,

;;   (embed b psi e f) = (embed (flift (primitive s) s k) psi e f)
;;                     = (embed (primitive s) (restrict-embedding psi k s) e f)
;;		       = (embed (primitive s) (list a) e f)
;;		       = a

(local-defthmd embed-b-psi-1
  (implies (and (extensionp e f) (not (equal e f))
                (polyp p f) (monicp p f) (>= (degree p) 1)
		(splitting-field-p p e f)
		(feltp a e) (not (fliftedp a f e)))
	   (let* ((s (s% a e f))
		  (k (k% a e f p))
		  (psi (psi% a e f p))
		  (b (b% a e f p)))
	     (equal (embed b psi e f)
	            (embed (primitive s) (restrict-embedding psi k s) e f))))
  :hints (("Goal" :in-theory (enable autop fliftedp galois)
                  :use (embeddingp-phi-psi
			(:instance embed-flift-gen (x (primitive (s% a e f)))
			                           (d (s% a e f))
						   (e (k% a e f p))
						   (phi (psi% a e f p))
						   (k e))))))

(local-defthmd restrict-embedding-psi
  (implies (extensionp k (cons (min-poly a e f) f))
           (equal (restrict-embedding (psi a k e f) k (cons (min-poly a e f) f))
                  (list a)))
  :hints (("Subgoal *1/4" :use ((:instance restrict-embedding-cdr
                                  (phi (cons (car (proots (pembed (car k) (psi a (cdr k) e f) e f) e)) (psi a (cdr k) e f)))
                                  (e k)
				  (d (cons (min-poly a e f) f)))))))

(local-defthmd embed-b-psi-2
  (implies (and (extensionp e f) (not (equal e f))
                (polyp p f) (monicp p f) (>= (degree p) 1)
		(splitting-field-p p e f)
		(feltp a e) (not (fliftedp a f e)))
           (equal (embed (primitive (s% a e f)) (list a) e f)
                  a))
  :hints (("Goal" :in-theory (enable pembed-nil embeddingp fliftedp)
                  :use ((:instance prootp-min-poly (x a))
			(:instance fieldp (f (s% a e f)))
			(:instance embed-primitive (phi (list a)) (e (s% a e f)) (k e))))))

(local-defthmd embed-b-psi
  (implies (and (extensionp e f) (not (equal e f))
                (polyp p f) (monicp p f) (>= (degree p) 1)
		(splitting-field-p p e f)
		(feltp a e) (not (fliftedp a f e)))
	   (let* ((psi (psi% a e f p))
		  (b (b% a e f p)))
	     (equal (embed b psi e f)
	            a)))
  :hints (("Goal" :in-theory (enable fliftedp)
                  :use (embed-b-psi-1 embed-b-psi-2 embeddingp-phi-psi
                        (:instance restrict-embedding-psi (k (k% a e f p)))))))

;; Let a' be an element of e with (min-poly a' e f) = (min-poly a e f) = m.
;; Then psi' = (psi a' k e f) is an embedding of k in e over f and (embed b psi' e f) = a'.
;; Composing psi' with the inverse of psi, we have an automorphism of e that maps a to a':

(defund roots-auto (a a1 p e f)
  (let* ((m (min-poly a e f))
         (s (cons m f))
	 (k (splitting-field (plift p f s) s)))         
    (comp-embedding (psi a1 k e f) (inv-embedding (psi a k e f) k e f) e e f)))

(local-defthmd roots-auto-lemma-1
  (implies (and (extensionp e f) (not (equal e f)) (polyp p f)
                (monicp p f) (>= (degree p) 1) (splitting-field-p p e f)
                (feltp a e) (not (fliftedp a f e)))
	   (let ((inv (inv-embedding (psi% a e f p) (k% a e f p) e f)))
	     (embeddingp inv e (k% a e f p) f)))
  :hints (("Goal" :in-theory (disable embedding-surjective)
                  :use (embeddingp-phi-psi embed-b-psi
			(:instance embedding-surjective (phi (phi% a e f p)) (k (k% a e f p))) 
			(:instance embedding-surjective (phi (psi% a e f p)) (k e) (e (k% a e f p)))
                        (:instance embeddingp-inv-embedding (phi (psi% a e f p)) (e (k% a e f p)) (k e))))))

(local-defthmd roots-auto-lemma-2
  (implies (and (extensionp e f) (not (equal e f)) (polyp p f)
                (monicp p f) (>= (degree p) 1) (splitting-field-p p e f)
                (feltp a e) (not (fliftedp a f e)))
	   (let ((inv (inv-embedding (psi% a e f p) (k% a e f p) e f)))
	     (and (embeddingp inv e (k% a e f p) f)
	          (equal (embed a inv (k% a e f p) f)
		         (b% a e f p)))))
  :hints (("Goal" :in-theory (disable embedding-surjective)
                  :use (roots-auto-lemma-1 embeddingp-phi-psi embed-b-psi
			(:instance embedding-surjective (phi (phi% a e f p)) (k (k% a e f p))) 
			(:instance embedding-surjective (phi (psi% a e f p)) (k e) (e (k% a e f p)))
                        (:instance embed-embedding-inv (phi (psi% a e f p)) (e (k% a e f p)) (k e) (x (b% a e f p)))))))

(defthmd roots-auto-lemma
  (implies (and (extensionp e f) (not (equal e f)) (polyp p f)
                (monicp p f) (>= (degree p) 1) (splitting-field-p p e f)
                (feltp a e) (feltp a1 e) (not (fliftedp a f e))
		(equal (min-poly a e f) (min-poly a1 e f)))
	   (and (autop (roots-auto a a1 p e f) e f)
	        (equal (embed a (roots-auto a a1 p e f) e f)
		       a1)))
  :hints (("Goal" :in-theory (enable fliftedp roots-auto autop)
                  :use (roots-auto-lemma-2
		        (:instance embeddingp-phi-psi (a a1))
		        (:instance embed-b-psi (a a1))
			(:instance embeddingp-comp-embedding (phi (inv-embedding (psi% a e f p) (k% a e f p) e f))
			                                     (psi (psi% a1 e f p))
							     (x a)
							     (g (k% a e f p))
							     (k e))))))
							     
;;---------------------------------------------------

;; This predicate recognizes elements of e that are fixed by a subgroup h of (galois e f):

(defun fixedp-aux (x l e f)
  (if (consp l)
      (and (equal x (embed x (car l) e f))
           (fixedp-aux x (cdr l) e f))
    t))

(defun fixedp (x h e f)
  (fixedp-aux x (elts h) e f))

(local-defthm fixedp-aux-embed
  (implies (and (fixedp-aux x l e f) (member phi l))
           (equal (embed x phi e f) x)))

(defthm fixedp-embed
  (implies (and (fixedp x h e f) (in phi h))
           (equal (embed x phi e f) x))
  :hints (("Goal" :in-theory (enable fixedp))))

(defun fixedp-aux-cex (x l e f)
  (if (consp l)
      (if (equal x (embed x (car l) e f))
          (fixedp-aux-cex x (cdr l) e f)
	(car l))
    ()))

(defund fixedp-cex (x h e f)
  (fixedp-aux-cex x (elts h) e f))

(local-defthmd fixedp-aux-cex-lemma
  (implies (not (fixedp-aux x l e f))
           (let ((phi (fixedp-aux-cex x l e f)))
	     (and (member phi l)
	          (not (equal x (embed x phi e f)))))))

(defthmd fixedp-cex-lemma
  (implies (not (fixedp x h e f))
           (let ((phi (fixedp-cex x h e f)))
	     (and (in phi h)
                  (not (equal x (embed x phi e f))))))
  :hints (("Goal" :in-theory (enable fixedp fixedp-cex)
                  :use ((:instance fixedp-aux-cex-lemma (l (elts h)))))))

(local-defthmd embed-a-phi-psi
  (implies (and (extensionp e f) (not (equal e f))
                (polyp p f) (monicp p f) (>= (degree p) 1)
		(splitting-field-p p e f)
		(feltp a e) (not (fliftedp a f e)) (fixedp a (galois e f) e f))
	   (let* ((k (k% a e f p))
		  (phi (phi% a e f p))
		  (psi (psi% a e f p)))
	     (equal (embed (embed a phi k f) psi e f)
	            a)))
  :hints (("Goal" :in-theory (enable autop fliftedp galois)
                  :use (embeddingp-phi-psi
			(:instance prootp-min-poly (x a))
		        (:instance extensionp-splitting-field (p (plift p f (s% a e f))) (f (s% a e f)))
			(:instance embeddingp-comp-embedding (k e) (x a) (g (k% a e f p)) (phi (phi% a e f p)) (psi (psi% a e f p)))
			(:instance fixedp-embed (x a) (h (galois e f)) (phi (comp-embedding (psi% a e f p) (phi% a e f p) e e f)))))))


;; Since psi is injective, it follows that (embed a phi k f) = b.  Let inv = (inv-embedding phi e k f).  
;; Then (embed b inv e f) = a.

(local-defthmd equal-embed-a-b
  (implies (and (extensionp e f) (not (equal e f))
                (polyp p f) (monicp p f) (>= (degree p) 1)
		(splitting-field-p p e f)
		(feltp a e) (not (fliftedp a f e)) (fixedp a (galois e f) e f))
	   (let* ((k (k% a e f p))
		  (phi (phi% a e f p))
		  (b (b% a e f p)))
	     (and (feltp b k)
	          (equal (embed a phi k f)
	                 b))))
  :hints (("Goal" :use (embeddingp-phi-psi embed-a-phi-psi embed-b-psi
                        (:instance feltp-primitive (f (s% a e f)))
                        (:instance embedding-1-1 (e (k% a e f p))
			                         (k e)
						 (x (b% a e f p))
						 (y (embed a (phi% a e f p) (k% a e f p) f))
						 (phi (psi% a e f p)))))))

(local-defthmd equal-embed-b-a
  (implies (and (extensionp e f) (not (equal e f))
                (polyp p f) (monicp p f) (>= (degree p) 1)
		(splitting-field-p p e f)
		(feltp a e) (not (fliftedp a f e)) (fixedp a (galois e f) e f))
	   (let* ((k (k% a e f p))
	          (inv (inv% a e f p))
		  (b (b% a e f p)))
	     (and (embeddingp inv k e f)
	          (equal (embed b inv e f)
	                 a))))
  :hints (("Goal" :use (embeddingp-phi-psi equal-embed-a-b
                        (:instance id-embedding-id (x a))
			(:instance comp-inv-embedding (k (k% a e f p)) (phi (phi% a e f p)))
			(:instance embeddingp-comp-embedding (g (k% a e f p)) (k e) (phi (phi% a e f p)) (psi (inv% a e f p)) (x a))))))

;; Since (edegree e f) = (edegree k f) > (edegree k s), (order (galois e f)) > (order (galois k s)).
;; However, we shall construct an injection of (galois e f) into (galois k s), a contradiction.

;; First we define a map from (galois e f) into (galois k f).  Given x in (galois e f), let

;;    y = (galois-map x a e f p) = (comp-embedding phi (comp-embedding x inv k e f) k k f).

(defund galois-map (x a e f p)
  (let* ((k (k% a e f p))
	 (phi (phi% a e f p))
	 (inv (inv% a e f p)))
    (comp-embedding phi (comp-embedding x inv k e f) k k f)))

;; Then y is in (galois k f) and

;;    (embed b y k f) = (embed (embed (embed b inv e f) x k f) phi k f)
;;                    = (embed (embed a x k f) phi k f)
;;                    = (embed a phi k f)
;;                    = b.

(local-defthmd embed-b-galois-map
  (implies (and (extensionp e f) (not (equal e f))
                (polyp p f) (monicp p f) (>= (degree p) 1)
		(splitting-field-p p e f)
		(feltp a e) (not (fliftedp a f e)) (fixedp a (galois e f) e f)
		(in x (galois e f)))
	   (let* ((k (k% a e f p))
		  (b (b% a e f p))
		  (y (galois-map x a e f p)))
	     (and (in y (galois k f))
	          (equal (embed b y k f)
		         b))))
  :hints (("Goal" :in-theory (enable galois-map galois autop)
                  :use (embeddingp-phi-psi equal-embed-a-b equal-embed-b-a
		        (:instance fixedp-embed (x a) (h (galois e f)) (phi x))
		        (:instance embeddingp-comp-embedding (phi (inv% a e f p))
		                                             (psi x)
							     (e (k% a e f p))
							     (g e)
							     (k e)
							     (x (b% a e f p)))
		        (:instance embeddingp-comp-embedding (phi (comp-embedding x (inv% a e f p) (k% a e f p) e f))
			                                     (psi (phi% a e f p))
							     (e (k% a e f p))
							     (g e)
							     (k (k% a e f p))
							     (x (b% a e f p)))))))

;; Let n = (len k) - (len s) and y' = (nthcdr n y) = (restrict-embedding y k s).  By embeddingp-restrict-embedding, y' 
;; is an embedding of s in k over f.  Thus, y' = (list (car y'), where

;;    (car y') = (embed (primitive s) y' k f)             [embed-primitive]
;;             = (embed (flift (primitive s) s k) y k f)  [embed-flift-gen]
;;             = (embed b y k f)
;;             = b

;; and hence y' = (list b) = (list (flift (primitive s) s k)) = (trivial-embedding s k f).

(local-defthmd embeddingp-restrict-embedding-y
  (implies (and (extensionp e f) (not (equal e f))
                (polyp p f) (monicp p f) (>= (degree p) 1)
		(splitting-field-p p e f)
		(feltp a e) (not (fliftedp a f e)) (fixedp a (galois e f) e f)
		(in x (galois e f)))
	   (let* ((s (s% a e f))
	          (k (k% a e f p))
		  (b (b% a e f p))
		  (y (galois-map x a e f p)))
	     (and (embeddingp (restrict-embedding y k s) s k f)
	          (equal (car (restrict-embedding y k s))
		         b))))
  :hints (("Goal" :in-theory (enable galois autop)
                  :use (embeddingp-phi-psi embed-b-galois-map
		        (:instance embeddingp-restrict-embedding (e (k% a e f p))
			                           (d (s% a e f))
						   (k (k% a e f p))
						   (phi (galois-map x a e f p)))
			(:instance embed-primitive (e (s% a e f))
			                           (k (k% a e f p))
						   (phi (restrict-embedding (galois-map x a e f p) (k% a e f p) (s% a e f))))
			(:instance embed-flift-gen (x (primitive (s% a e f)))
			                           (d (s% a e f))
						   (e (k% a e f p))
						   (k (k% a e f p))
						   (phi (galois-map x a e f p)))
			(:instance feltp-primitive (f (s% a e f)))))))

(local-defthmd restrict-embedding-y-trivial-1
  (implies (embeddingp phi (cons p f) k f)
           (equal (list (car phi)) phi))
  :hints (("Goal" :in-theory (enable embeddingp))))

(local-defthmd restrict-embedding-y-trivial
  (implies (and (extensionp e f) (not (equal e f))
                (polyp p f) (monicp p f) (>= (degree p) 1)
		(splitting-field-p p e f)
		(feltp a e) (not (fliftedp a f e)) (fixedp a (galois e f) e f)
		(in x (galois e f)))
	   (let* ((s (s% a e f))
	          (k (k% a e f p))
		  (y (galois-map x a e f p)))
	     (equal (restrict-embedding y k s)
	            (trivial-embedding s k f))))
  :hints (("Goal" :use (embeddingp-phi-psi embeddingp-restrict-embedding-y
		        (:instance restrict-embedding-y-trivial-1 (p (min-poly a e f))
			                            (k (k% a e f p))
						    (phi (restrict-embedding (galois-map x a e f p) (k% a e f p) (s% a e f))))))))

;; Let y" = (galois-inj x a e f) = (firstn n y):

(defund galois-inj (x a e f p)
  (firstn (- (len (k% a e f p)) (len (s% a e f)))
          (galois-map x a e f p)))

;; By autop-trunc-embedding, y" is in (galois k s) and for all c in k, (embed c y" k s)
;; = (embed c y k f).  To see that galois-inj is an injection, let x1 and x2 be in (galois e f),
;; let

;;    y1 = (galois-map x1 a e f p)
;;    y2 = (galois-map x2 a e f p)
;;    y1" = (galois-inj x1 a e f p)
;;    y2" = (galois-inj x2 a e f p)

;; and suppose y1" = y2".  Then for all c in k,

;;    (embed c y1 k f) = (embed c y1" k s) = (embed c y2" k s) = (embed c y2 k f).

;; By embed-cex-lemma, y1 = y2, and it follows from the properties of comp-embedding
;; (comp-embedding-assoc, comp-inv-embedding, and comp-id-embedding) that x1 = x2.
	 
(local-defthmd galois-inj-galois-map
  (implies (and (extensionp e f) (not (equal e f))
                (polyp p f) (monicp p f) (>= (degree p) 1)
		(splitting-field-p p e f)
		(feltp a e) (not (fliftedp a f e)) (fixedp a (galois e f) e f)
		(in x (galois e f)))
	   (let* ((s (s% a e f))
	          (k (k% a e f p))
		  (y (galois-map x a e f p))
		  (yp (galois-inj x a e f p)))
	     (and (in yp (galois k s))
	          (implies (feltp c k)
		           (equal (embed c yp k s)
			          (embed c y k f))))))
  :hints (("Goal" :in-theory (enable restrict-embedding autop galois galois-inj galois-map)
                  :use (embeddingp-phi-psi embeddingp-restrict-embedding-y restrict-embedding-y-trivial embed-b-galois-map
		        (:instance autop-trunc-embedding (e (k% a e f p)) (d (s% a e f)) (phi (galois-map x a e f p)) (x c))))))

(local-defthmd galois-inj-injective-1
  (implies (and (extensionp e f) (not (equal e f))
                (polyp p f) (monicp p f) (>= (degree p) 1)
		(splitting-field-p p e f)
		(feltp a e) (not (fliftedp a f e)) (fixedp a (galois e f) e f)
		(in x1 (galois e f))
		(in x2 (galois e f)))
	   (let* ((k (k% a e f p))
		  (y1 (galois-map x1 a e f p))
		  (yp1 (galois-inj x1 a e f p))
		  (y2 (galois-map x2 a e f p))
		  (yp2 (galois-inj x2 a e f p)))
             (implies (and (equal yp1 yp2)
		           (feltp c k))
	              (equal (embed c y1 k f)
		             (embed c y2 k f)))))
  :hints (("Goal" :use ((:instance galois-inj-galois-map (x x1))
                        (:instance galois-inj-galois-map (x x2))))))

(local-defthmd galois-inj-injective-2
  (implies (and (extensionp e f) (not (equal e f))
                (polyp p f) (monicp p f) (>= (degree p) 1)
		(splitting-field-p p e f)
		(feltp a e) (not (fliftedp a f e)) (fixedp a (galois e f) e f)
		(in x1 (galois e f))
		(in x2 (galois e f)))
	   (let* ((y1 (galois-map x1 a e f p))
		  (yp1 (galois-inj x1 a e f p))
		  (y2 (galois-map x2 a e f p))
		  (yp2 (galois-inj x2 a e f p)))
             (implies (equal yp1 yp2)
	              (equal y1 y2))))
  :hints (("Goal" :in-theory (enable autop galois)
                  :use (embeddingp-phi-psi
                        (:instance embed-b-galois-map (x x1))
                        (:instance embed-b-galois-map (x x2))
                        (:instance galois-inj-injective-1 (c (embed-cex (galois-map x1 a e f p) (galois-map x2 a e f p) (k% a e f p) f)))
                        (:instance galois-inj-galois-map (x x2))
			(:instance embed-cex-lemma (e (k% a e f p)) (k (k% a e f p)) (phi (galois-map x1 a e f p)) (psi (galois-map x2 a e f p)))))))

(local-defthmd galois-inj-injective-3
  (implies (and (extensionp e f) (not (equal e f))
                (polyp p f) (monicp p f) (>= (degree p) 1)
		(splitting-field-p p e f)
		(feltp a e) (not (fliftedp a f e)) (fixedp a (galois e f) e f)
		(in x1 (galois e f))
		(in x2 (galois e f)))
 	   (let* ((k (k% a e f p))
	          (inv (inv% a e f p))
		  (y1 (galois-map x1 a e f p))
		  (y2 (galois-map x2 a e f p)))
             (implies (equal y1 y2)
	              (equal (comp-embedding x1 inv k e f)
		             (comp-embedding x2 inv k e f)))))
  :hints (("Goal" :in-theory (enable autop galois galois-map)
                  :use (embeddingp-phi-psi
                        (:instance comp-embedding-assoc (phi1 (comp-embedding x1 (inv% a e f p) (k% a e f p) e f))
			                                (phi2 (phi% a e f p))
							(phi3 (inv% a e f p))
			                                (e1 (k% a e f p)) (e2 e) (e3 (k% a e f p)) (e4 e))
                        (:instance comp-embedding-assoc (phi1 (comp-embedding x2 (inv% a e f p) (k% a e f p) e f))
			                                (phi2 (phi% a e f p))
							(phi3 (inv% a e f p))
			                                (e1 (k% a e f p)) (e2 e) (e3 (k% a e f p)) (e4 e))
			(:instance embeddingp-comp-embedding (e (k% a e f p)) (g e) (k e) (phi (inv% a e f p)) (psi x1))
			(:instance embeddingp-comp-embedding (e (k% a e f p)) (g e) (k e) (phi (inv% a e f p)) (psi x2))
                        (:instance comp-inv-embedding (phi (phi% a e f p)) (k (k% a e f p)))
                        (:instance comp-id-embedding (phi (comp-embedding x1 (inv% a e f p) (k% a e f p) e f)) (k e) (e (k% a e f p)))
                        (:instance comp-id-embedding (phi (comp-embedding x2 (inv% a e f p) (k% a e f p) e f)) (k e) (e (k% a e f p)))))))

(local-defthm galois-inj-injective-4
  (implies (and (extensionp e f) (not (equal e f))
                (polyp p f) (monicp p f) (>= (degree p) 1)
		(splitting-field-p p e f)
		(feltp a e) (not (fliftedp a f e)) (fixedp a (galois e f) e f)
		(in x1 (galois e f))
		(in x2 (galois e f)))
 	   (let* ((k (k% a e f p))
	          (inv (inv% a e f p)))
             (implies (equal (comp-embedding x1 inv k e f)
		             (comp-embedding x2 inv k e f))
		      (equal x1 x2))))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable autop galois)
                  :use (embeddingp-phi-psi
                        (:instance comp-embedding-assoc (phi1 (phi% a e f p))
			                                (phi2 (inv% a e f p))
							(phi3 x1)
			                                (e1 e) (e2 (k% a e f p)) (e3 e) (e4 e))
                        (:instance comp-embedding-assoc (phi1 (phi% a e f p))
			                                (phi2 (inv% a e f p))
							(phi3 x2)
			                                (e1 e) (e2 (k% a e f p)) (e3 e) (e4 e))
                        (:instance comp-inv-embedding (phi (phi% a e f p)) (k (k% a e f p)))
                        (:instance comp-id-embedding (phi x1) (k e))
                        (:instance comp-id-embedding (phi x2) (k e))))))

(defthm galois-inj-injective
  (implies (and (extensionp e f) (not (equal e f))
                (polyp p f) (monicp p f) (>= (degree p) 1)
		(splitting-field-p p e f)
		(feltp a e) (not (fliftedp a f e)) (fixedp a (galois e f) e f)
		(in x1 (galois e f))
		(in x2 (galois e f))
		(equal (galois-inj x1 a e f p)
		       (galois-inj x2 a e f p)))
 	   (equal x1 x2))
  :rule-classes ()
  :hints (("Goal" :use (galois-inj-injective-2 galois-inj-injective-3 galois-inj-injective-4))))

;;-------------------------------

;;  I really thought I had done this in groups/lists.lisp.  I guess I should move it there:

(encapsulate (((l1) => *) ((l2) => *) ((inj *) => *))
  (local (defun l1 () ()))
  (local (defun l2 () ()))
  (local (defun inj (x) x))
  (defthmd dlistp-l1 (dlistp (l1)))
  (defthm inj-l1-l2
    (implies (member x (l1))
             (member (inj x) (l2))))
  (defthmd inj-1-1
    (implies (and (member x (l1)) (member y (l1)) (not (equal x y)))
             (not (equal (inj x) (inj y))))))

(local-defun inj-image (l)
  (if (consp l)
      (cons (inj (car l))
            (inj-image (cdr l)))
    ()))

(local-defthm not-member-inj-image
  (implies (and (sublistp l (l1)) (member x (l1)) (not (member x l)))
           (not (member (inj x) (inj-image l))))
  :hints (("Subgoal *1/5" :use ((:instance inj-1-1 (y (car l)))))
          ("Subgoal *1/3" :use ((:instance inj-1-1 (y (car l)))))))

(local-defthmd dlistp-inj-image
  (implies (and (sublistp l (l1)) (dlistp l))
           (let ((m (inj-image l)))
	     (and (dlistp m)
	          (sublistp m (l2))
		  (equal (len m) (len l))))))

(defthmd len-l1-len-l2
  (<= (len (l1)) (len (l2)))
  :hints (("Goal" :use ((:instance dlistp-inj-image (l (l1)))
                        (:instance sublistp-<=-len (l (inj-image (l1))) (m (l2)))))))

;;-------------------------------

(local-defun galois-inj-image (l a e f p)
  (if (consp l)
      (cons (galois-inj (car l) a e f p)
            (galois-inj-image (cdr l) a e f p))
    ()))

(local-defthm not-member-galois-inj-image
  (implies (and (extensionp e f) (not (equal e f))
                (polyp p f) (monicp p f) (>= (degree p) 1)
		(splitting-field-p p e f)
		(feltp a e) (not (fliftedp a f e)) (fixedp a (galois e f) e f)
                (sublistp l (auto-list e f))
		(member x (auto-list e f))
		(not (member x l)))
           (not (member (galois-inj x a e f p) (galois-inj-image l a e f p))))
  :hints (("Goal" :induct (len l))
          ("Subgoal *1/1" :in-theory (enable galois) :use ((:instance galois-inj-injective (x1 x) (x2 (car l)))))))

(local-defthmd dlistp-galois-inj-image
  (implies (and (extensionp e f) (not (equal e f))
                (polyp p f) (monicp p f) (>= (degree p) 1)
		(splitting-field-p p e f)
		(feltp a e) (not (fliftedp a f e)) (fixedp a (galois e f) e f)
		(sublistp l (auto-list e f)) (dlistp l))
           (let ((m (galois-inj-image l a e f p)))
	     (and (dlistp m)
	          (sublistp m (auto-list (k% a e f p) (s% a e f)))
		  (equal (len m) (len l)))))
  :hints (("Goal" :induct (len l))
          ("Subgoal *1/1" :in-theory (enable galois)
	                  :use (embeddingp-phi-psi
			        (:instance galois-inj-galois-map (x (car l)))))))

(local-defthm galois-inj-order
  (implies (and (extensionp e f) (not (equal e f))
                (polyp p f) (monicp p f) (>= (degree p) 1)
		(splitting-field-p p e f)
		(feltp a e) (not (fliftedp a f e)) (fixedp a (galois e f) e f))
	   (<= (order (galois e f))
	       (order (galois (k% a e f p) (s% a e f)))))
  :hints (("Goal" :in-theory (enable order galois)
                  :use (embeddingp-phi-psi
		        (:instance dlistp-galois-inj-image (l (auto-list e f)))
                        (:instance sublistp-<=-len (l (galois-inj-image (auto-list e f) a e f p))
			                           (m (auto-list (k% a e f p) (s% a e f))))))))

(local-defthmd galoisp-e-f
  (implies (and (extensionp e f) (not (equal e f))
                (polyp p f) (monicp p f) (>= (degree p) 1)
                (separablep p f) (splitting-field-p p e f)
		(feltp a e) (not (fliftedp a f e)) (fixedp a (galois e f) e f))
	   (galoisp e f)))

(local-defthmd galoisp-k-s
  (implies (and (extensionp e f) (not (equal e f))
                (polyp p f) (monicp p f) (>= (degree p) 1)
                (separablep p f) (splitting-field-p p e f)
		(feltp a e) (not (fliftedp a f e)) (fixedp a (galois e f) e f))
	   (galoisp (k% a e f p) (s% a e f)))
  :hints (("Goal" :use (embeddingp-phi-psi
                        (:instance splitting-field-p-splitting-field (p (plift p f (s% a e f))) (f (s% a e f)))
			(:instance separablep-extension (e (s% a e f)))
                        (:instance galoisp-suff (e (k% a e f p)) (f (s% a e f)) (p (plift p f (s% a e f))))))))

(local-defthm galois-inj-edegree
  (implies (and (extensionp e f) (not (equal e f))
                (polyp p f) (monicp p f) (>= (degree p) 1)
                (separablep p f) (splitting-field-p p e f)
		(feltp a e) (not (fliftedp a f e)) (fixedp a (galois e f) e f))
	   (<= (edegree (k% a e f p) f)
	       (edegree (k% a e f p) (s% a e f))))
  :hints (("Goal" :in-theory (e/d (order galois) (embedding-surjective))
                  :use (embeddingp-phi-psi galois-inj-order galoisp-e-f galoisp-k-s order-galois-group
			(:instance order-galois-group (e (k% a e f p)) (f (s% a e f)))
			(:instance embedding-surjective (phi (phi% a e f p)) (k (k% a e f p))) 
			(:instance embedding-surjective (phi (psi% a e f p)) (k e) (e (k% a e f p)))
		        (:instance dlistp-galois-inj-image (l (auto-list e f)))
                        (:instance sublistp-<=-len (l (galois-inj-image (auto-list e f) a e f p))
			                           (m (auto-list (k% a e f p) (s% a e f))))))))

(local-defthmd edegree-prod
  (implies (and (extensionp e d) (extensionp d f))
           (equal (edegree e f)
	          (* (edegree e d)
		     (edegree d f))))
  :hints (("Subgoal *1/2" :use ((:instance len-extends (e d) (f e))
                                (:instance len-extends (e (cdr e)) (f d))))))

(local-defthmd pos-edegree-prod
  (implies (extensionp e f)
           (posp (edegree e f))))

(local-defthm edegree-k-s-1
  (implies (and (extensionp e f) (not (equal e f))
                (polyp p f) (monicp p f) (>= (degree p) 1)
                (separablep p f) (splitting-field-p p e f)
		(feltp a e) (not (fliftedp a f e)) (fixedp a (galois e f) e f))
	   (and (equal (edegree (k% a e f p) f)
	               (* (edegree (k% a e f p) (s% a e f))
		          (edegree (s% a e f) f)))
		(posp (edegree (k% a e f p) (s% a e f)))
		(posp (edegree (s% a e f) f))
		(> (edegree (s% a e f) f) 1)))
  :hints (("Goal" :in-theory (e/d (fliftedp edegree) (embedding-surjective))
                  :use (embeddingp-phi-psi
			(:instance embedding-surjective (phi (phi% a e f p)) (k (k% a e f p))) 
		        (:instance pos-edegree-prod (e (k% a e f p)) (f (s% a e f)))
			(:instance prootp-min-poly (x a))
		        (:instance edegree-prod (e (k% a e f p)) (d (s% a e f)))))))

(local-defthmd hack-3
  (implies (and (posp a) (posp b) (> b 1))
           (> (* a b) a)))
 
(local-defthm edegree-k-s-2
  (implies (and (extensionp e f) (not (equal e f))
                (polyp p f) (monicp p f) (>= (degree p) 1)
                (separablep p f) (splitting-field-p p e f)
		(feltp a e) (not (fliftedp a f e)) (fixedp a (galois e f) e f))
	   (> (edegree (k% a e f p) f)
	      (edegree (k% a e f p) (s% a e f))))
  :hints (("Goal" :use (edegree-k-s-1
                        (:instance hack-3 (a (edegree (k% a e f p) (s% a e f)))
			                  (b (edegree (s% a e f) f)))))))

(local-defthmd fixed-fliftedp
  (implies (and (extensionp e f) (not (equal e f))
                (polyp p f) (monicp p f) (>= (degree p) 1)
                (separablep p f) (splitting-field-p p e f)
		(feltp a e) (fixedp a (galois e f) e f))
	   (fliftedp a f e))
  :hints (("Goal" :use (galois-inj-edegree edegree-k-s-2))))

(defthmd galois-no-fixed-elt
  (implies (and (extensionp e f) (galoisp e f)
                (feltp a e) (fixedp a (galois e f) e f))
	   (fliftedp a f e))
  :hints (("Goal" :in-theory (enable fliftedp)
                  :use ((:instance fixed-fliftedp (p (galoisp-witness e f)))
                        (:instance min-poly-trivial (x a))
                        (:instance degree-root-poly (x a))))))

;;-----------------------------------------------------------------------

;; Let e be an extension of f.  We shall say that the extension is normal if the minimal polynomial of every 
;; element of e splits in e:

(defun-sk normal-extension-p (e f)
  (forall (x)
    (implies (feltp x e)
             (splits (plift (min-poly x e f) f e) e))))

(defthmd normal-extension-p-lemma
  (implies (and (normal-extension-p e f)
                (feltp x e))
	   (splits (plift (min-poly x e f) f e) e))
  :hints (("Goal" :use (normal-extension-p-necc))))

(defthmd normal-extension-p-witness-lemma
  (let ((x (normal-extension-p-witness e f)))
    (implies (implies (feltp x e)
                      (splits (plift (min-poly x e f) f e) e))
	     (normal-extension-p e f))))

;; The extension is separable if the minimal polynomial of every element of e is separable:

(defun-sk separable-extension-p (e f)
  (forall (x)
    (implies (feltp x e)
             (separablep (min-poly x e f) f))))
	    
 (defthmd separable-extension-p-lemma
  (implies (and (separable-extension-p e f)
                (feltp x e))
	   (separablep (min-poly x e f) f))
  :hints (("Goal" :use (separable-extension-p-necc))))

(defthmd separable-extension-p-witness-lemma
  (let ((x (separable-extension-p-witness e f)))
    (implies (implies (feltp x e)
                      (separablep (min-poly x e f) f))
	     (separable-extension-p e f))))

(local-defthmd normal-separable-trivial-1
  (implies (and (fieldp f) (feltp x f))
           (let ((p (root-poly x f)))
	     (and (splits (plift p f f) f)
		  (separablep p f))))
  :hints (("Goal" :use (degree-root-poly
                        (:instance linear-splits (p (root-poly x f)))
		        (:instance separablep-linear (p (root-poly x f)))))))

(defthmd normal-separable-trivial
  (implies (fieldp f)
           (and (normal-extension-p f f)
	        (separable-extension-p f f)))
  :hints (("Goal" :use (normal-extension-p-witness-lemma separable-extension-p-witness-lemma
                        (:instance min-poly-trivial (x (normal-extension-p-witness f f)))
                        (:instance min-poly-trivial (x (separable-extension-p-witness f f)))
                        (:instance normal-separable-trivial-1 (x (normal-extension-p-witness f f)))
                        (:instance normal-separable-trivial-1 (x (separable-extension-p-witness f f)))))))

;; We shall prove that every galois extension is separable and separable.
;; The proof is adapted from page 45 of J. S. Milne, "Fields and Galois Theory".

;; Let z be an element of e with p = (min-poly z e f), p' = (plift p f e), d = (proots p' e), and
;; g = (galois e f).  It is easily verified that if x is an element of g and s is a member of d, then
;; (embed s x e e) is also a member of d.  In fact, embed may be viewed as a group action of g on d:

(in-theory (enable comp-auto autop galois))

(local-defthmd feltp-member-proots-min-poly
  (implies (and (extensionp e f)
                (feltp z e)
		(member s (proots (plift (min-poly z e f) f e) e)))
	   (feltp s e))
  :hints (("Goal" :use ((:instance prootp-min-poly (x z))
		        (:instance feltp-member-proots (x s) (p (plift (min-poly z e f) f e)) (f e))))))

(local-defthm perm-proots-1
  (IMPLIES (AND (extensionp e f)
                (embeddingp x e e f)
                (embeddingp y e e f)
                (member-equal s (proots (plift (min-poly z e f) f e) e))
                (feltp z e))
           (equal (embed s (comp-embedding x y e e f) e f)
	          (embed (embed s y e f) x e f)))
  :hints (("goal" :use (feltp-member-proots-min-poly
                        (:instance embeddingp-comp-embedding (x s) (psi x) (phi y) (g e) (k e))))))

(local-defthm perm-proots-2
  (implies (and (extensionp e f)
                (feltp z e)
                (embeddingp x e e f)
                (member-equal s (proots (plift (min-poly z e f) f e) e)))
         (member-equal (embed s x e f)
                       (proots (plift (min-poly z e f) f e) e)))
  :hints (("Goal" :in-theory (enable prootp)
                  :use ((:instance peval-pembed (k e) (phi x) (p (plift (min-poly z e f) f e)) (x s))
		        (:instance member-proots (x s) (f e) (p (plift (min-poly z e f) f e)))
		        (:instance member-proots (x (embed s x e f))  (f e) (p (plift (min-poly z e f) f e)))
			(:instance pembed-fixes (k e) (p (min-poly z e f)) (phi x))
			(:instance prootp-min-poly (x z))))))

(local-defthm perm-proots-3
  (implies (and (extensionp e f)
                (feltp z e)
                (member-equal s (proots (plift (min-poly z e f) f e) e)))
           (equal (embed s (e (autos e f)) e f) s))
  :hints (("Goal" :in-theory (enable id-auto e)
                  :use (feltp-member-proots-min-poly (:instance id-embedding-id (x s))))))

(local-defthm perm-proots-4
  (implies (and (extensionp e f)
                (feltp z e))
           (consp (proots (plift (min-poly z e f) f e) e)))
  :hints (("Goal" :use ((:instance prootp-min-poly (x z))
		        (:instance member-proots (x z) (f e) (p (plift (min-poly z e f) f e)))))))                        

(defaction perm-proots
  ;; parameters:
  (e f z)
  ;; acting group:
  (galois e f)
  ;; parameter conditions:
  (and (extensionp e f) (galoisp e f) (feltp z e))
  ;; domain:
  (proots (plift (min-poly z e f) f e) e)
  ;; action of group element x on domain element s:
  (embed s x e f))

;; Let a denote this action, i.e., a = (perm-proots e f z).  For x in g and s in d, (act x s a g) = (embed s x e f).

;; Let (orbit z a g) = (z1 z2 .. zk).

(defthmd sublistp-orbit-perm-roots
  (implies (and (extensionp e f) (galoisp e f) (feltp z e))
           (let ((l (orbit z (perm-proots e f z) (galois e f))))
	     (and (dlistp l)
	          (sublistp l (proots (plift (min-poly z e f) f e) e))
		  (member z l))))
  :hints (("Goal" :use (actionp-perm-proots
                        (:instance prootp-min-poly (x z))
			(:instance member-proots (x z) (p (plift (min-poly z e f) f e)) (f e))
                        (:instance dlistp-orbit (s z) (a (perm-proots e f z)) (g (galois e f)))
                        (:instance member-self-orbit (s z) (a (perm-proots e f z)) (g (galois e f)))
                        (:instance sublistp-orbit (s z) (a (perm-proots e f z)) (g (galois e f)))))))

(local-defthmd feltsp-orbit-1
  (implies (and (extensionp e f) (galoisp e f) (feltp z e) (dlistp l) (sublistp l (orbit z (perm-proots e f z) (galois e f))))
           (feltsp l e))
  :hints (("Goal" :induct (len l))
          ("subgoal *1/1" :in-theory (enable prootp)
	                  :use (sublistp-orbit-perm-roots
	                        (:instance member-proots (x (car l)) (p (plift (min-poly z e f) f e)) (f e))
				(:instance prootp-min-poly (x z))))))

(defthmd feltsp-orbit-perm-proots
  (implies (and (extensionp e f) (galoisp e f) (feltp z e))
           (feltsp (orbit z (perm-proots e f z) (galois e f)) e))
  :hints (("Goal" :use (sublistp-orbit-perm-roots
                        (:instance feltsp-orbit-1 (l (orbit z (perm-proots e f z) (galois e f))))))))
 
;; We shall compute the polynomial product (root-poly z1 e) * ... * (root-poly zk e).

(defun root-poly-list (l e)
  (if (consp l)
      (cons (root-poly (car l) e)
            (root-poly-list (cdr l) e))
    ()))

(defund root-orbit-poly-list (z e f)
  (root-poly-list (orbit z (perm-proots e f z) (galois e f)) e))

(defund root-orbit-poly (z e f)
  (pmul-list (root-orbit-poly-list z e f) e))

;; Let l = (orbit z a g), r = (root-poly-list l e) = (root-orbit-poly-list z e f), and 
;; q = (pmul-list r e) = (root-orbit-poly z e f).

(defthmd monic-irreducible-listp-root-poly-list
  (implies (and (fieldp e) (feltsp l e))
           (monicp-irreduciblep-listp (root-poly-list l e) e))
  :hints (("Goal" :induct (len l))
          ("Subgoal *1/1" :in-theory (enable monicp-irreduciblep-root-poly))))

(defthm polyp-root-orbit-poly
  (implies (and (extensionp e f) (galoisp e f) (feltp z e))
           (and (polyp (root-orbit-poly z e f) e)
	        (monicp (root-orbit-poly z e f) e)))
  :hints (("Goal" :in-theory (enable root-orbit-poly root-orbit-poly-list)
                  :use (feltsp-orbit-perm-proots
                        (:instance monic-irreducible-listp-root-poly-list (l (orbit z (perm-proots e f z) (galois e f))))))))

;; If (feltsp m e), then by induction, (pmul-list (root-poly-list m e) e) has no monic irreducible factor 
;; of degree > 1.  It follows that q splits in e:

(local-defthmd splits-q-1
  (implies (and (fieldp e) (feltsp m e) (polyp p e) (monicp p e) (irreduciblep p e) (> (degree p) 1))
           (not (pdivides p (pmul-list (root-poly-list m e) e) e)))
  :hints (("Goal" :induct (len m))
          ("Subgoal *1/1" :use ((:instance peuclid (f e) (x (root-poly (car m) e)) (y (pmul-list (root-poly-list (cdr m) e) e)))
	                        (:instance pdivides-degree (f e) (x p) (y (root-poly (car m) e)))
				(:instance monic-irreducible-listp-root-poly-list (l (cdr m)))
				(:instance monicp-irreduciblep-root-poly (f e) (x (car m)))))
	  ("Subgoal *1/2" :in-theory (e/d (pzero pone) (polyp-pone))
	                  :use ((:instance pdivides-degree (f e) (x p) (y (pone e)))
			        (:instance fone-fzero (f e))
	                        (:instance polyp-pone (f e))))))

(local-defthmd splits-q-2
  (implies (and (fieldp e) (feltsp m e))
           (and (polyp (pmul-list (root-poly-list m e) e) e)
	        (equal (degree (pmul-list (root-poly-list m e) e))
	               (len m))))
  :hints (("Goal" :induct (len m))
          ("Subgoal *1/1" :use ((:instance degree-pmul (f e) (x (root-poly (car m) e)) (y (pmul-list (root-poly-list (cdr m) e) e)))))
	  ("Subgoal *1/1.2" :in-theory (enable root-poly))
          ("Subgoal *1/2" :in-theory (enable pone) :use ((:instance polyp-pone (f e))))))

(local-defthmd hack-4
  (implies (member x l) (> (len l) 0)))

(local-defthmd splits-q-3
  (implies (and (extensionp e f) (galoisp e f) (feltp z e))
           (>= (degree (root-orbit-poly z e f)) 1))
  :hints (("Goal" :in-theory (enable root-orbit-poly root-orbit-poly-list)
                  :use (sublistp-orbit-perm-roots feltsp-orbit-perm-proots
		        (:instance hack-4 (x z) (l (orbit z (perm-proots e f z) (galois e f))))
		        (:instance splits-q-2 (m (orbit z (perm-proots e f z) (galois e f))))))))

(defthmd splits-root-orbit-poly
  (implies (and (extensionp e f) (galoisp e f) (feltp z e))
           (splits (root-orbit-poly z e f) e))
  :hints (("Goal" :in-theory (enable root-orbit-poly root-orbit-poly-list)
                  :use (feltsp-orbit-perm-proots polyp-root-orbit-poly splits-q-3
                        (:instance splits-q-1 (m (orbit z (perm-proots e f z) (galois e f)))
			                      (p (nonlinear-irred-factor (root-orbit-poly z e f) e)))
                        (:instance splits-nonlinear-irred-factor (f e) (p (root-orbit-poly z e f)))
			(:instance nonlinear-irred-factor-nonlinear (f e) (p (root-orbit-poly z e f)))))))

;; If (feltsp m e) and (dlistp m), then by separablep-pmul and induction, (pmul-list (root-poly-list m e) e) 
;; is separable.  In particular, q is separable:

(local-defthm separablep-root-orbit-poly-1
  (implies (and (fieldp e) (feltp y e) (feltp x e) (equal (root-poly x e) (root-poly y e)))
           (equal x y))
  :rule-classes ()
  :hints (("Goal" :in-theory (e/d (root-poly) (fneg-fneg-* fneg-fneg))
                  :use ((:instance fneg-fneg (f e))
		        (:instance fneg-fneg (f e) (x y))))))

(local-defthmd separablep-root-orbit-poly-2
  (implies (and (fieldp e) (feltsp m e) (feltp x e) (not (member x m)))
           (not (pdivides (root-poly x e) (pmul-list (root-poly-list m e) e) e)))
  :hints (("Goal" :induct (len m))
          ("Subgoal *1/1" :use ((:instance splits-q-2 (m (cdr m)))
	                        (:instance monicp-irreduciblep-root-poly (f e))
	                        (:instance monicp-irreduciblep-root-poly (f e) (x (car m)))
				(:instance pdivides-equal-degree (x (root-poly x e)) (y (root-poly (car m) e)) (f e))
				(:instance separablep-root-orbit-poly-1 (y (car m)))
	                        (:instance peuclid (f e) (p (root-poly x e)) (x (root-poly (car m) e)) (y (pmul-list (root-poly-list (cdr m) e) e)))
				(:instance pdivides-monic-equal (x (root-poly x e)) (y (root-poly (car m) e)) (f e))))
	  ("Subgoal *1/2" :in-theory (enable pzero pone)
	                  :use ((:instance polyp-pone (f e))
			        (:instance monicp-irreduciblep-root-poly (f e))
			        (:instance pdivides-degree (f e) (x (root-poly x e)) (y (pone e)))))))

(local-defthmd separablep-root-orbit-poly-3
  (implies (and (fieldp e) (feltsp m e) (feltp x e) (not (member x m)))
           (equal (pgcd (root-poly x e) (pmul-list (root-poly-list m e) e) e)
	          (pone e)))
  :hints (("Goal" :use (separablep-root-orbit-poly-2 splits-q-2
                        (:instance monicp-irreduciblep-root-poly (f e))
			(:instance pgcd-irreduciblep (f e) (p (root-poly x e)) (x (pmul-list (root-poly-list m e) e)))))))

(local-defthmd separablep-root-orbit-poly-4
  (implies (and (fieldp e) (feltsp m e) (dlistp m))
           (separablep (pmul-list (root-poly-list m e) e) e))
  :hints (("Goal" :induct (len m))
          ("Subgoal *1/1" :use ((:instance splits-q-2 (m (cdr m)))
	                        (:instance separablep-root-orbit-poly-3 (x (car m)) (m (cdr m)))
                                (:instance monicp-irreduciblep-root-poly (x (car m)) (f e))
	                        (:instance separablep-pmul (f e) (p (root-poly (car m) e)) (q (pmul-list (root-poly-list (cdr m) e) e)))
				(:instance separablep-linear (f e) (p (root-poly (car m) e)))))
	  ("Subgoal *1/2" :in-theory (enable pconstp pzero pone)
	                  :use ((:instance polyp-pone (f e))
			        (:instance pconstp-separablep (f e) (p (pone e)))))))

(defthmd separablep-root-orbit-poly
  (implies (and (extensionp e f) (galoisp e f) (feltp z e))
           (separablep (root-orbit-poly z e f) e))
  :hints (("Goal" :in-theory (enable root-orbit-poly root-orbit-poly-list)
                  :use (feltsp-orbit-perm-proots sublistp-orbit-perm-roots
		        (:instance separablep-root-orbit-poly-4 (m (orbit z (perm-proots e f z) (galois e f))))))))
		        
;; Since z is in l, (root-poly z e) is in r, which implies (root-poly z e) divides q and z is a root of q:

(local-defthmd member-z-root-orbit-poly-list-1
  (implies (member z l)
           (member (root-poly z e) (root-poly-list l e))))

(defthmd member-z-root-orbit-poly-list
  (implies (and (extensionp e f) (galoisp e f) (feltp z e))
           (member (root-poly z e) (root-orbit-poly-list z e f)))
  :hints (("Goal" :in-theory (enable root-orbit-poly-list)
                  :use (sublistp-orbit-perm-roots
                        (:instance member-z-root-orbit-poly-list-1 (l (orbit z (perm-proots e f z) (galois e f))))))))

(defthmd pdivides-root-poly-root-orbit-poly
  (implies (and (extensionp e f) (galoisp e f) (feltp z e))
           (pdivides (root-poly z e) (root-orbit-poly z e f) e))
  :hints (("Goal" :in-theory (enable root-orbit-poly-list root-orbit-poly)
                  :use (feltsp-orbit-perm-proots member-z-root-orbit-poly-list
		        (:instance monic-irreducible-listp-root-poly-list (l (orbit z (perm-proots e f z) (galois e f))))
		        (:instance monicp-irreduciblep-root-poly (f e) (x z))
		        (:instance pdivides-pmul-listp (f e) (p (root-poly z e)) (l (root-orbit-poly-list z e f)))))))

(defthmd prootp-root-orbit-poly
  (implies (and (extensionp e f) (galoisp e f) (feltp z e))
           (prootp z (root-orbit-poly z e f) e))
  :hints (("Goal" :use (pdivides-root-poly-root-orbit-poly polyp-root-orbit-poly
                        (:instance prootp-pdivides (x z) (p (root-orbit-poly z e f)) (f e))))))

;; Let x be an element of (galois e f).  We shall show that (pembed q x e f) = q.  Let r' be the result of applying x
;; to each member of r.  Let p be a member of r'.  Then p = (list (fone e) (cadr p)), where (cadr p) is the image under
;; x of some member of l, which implies (cadr p) is a member of l, amd therefore p is a member of r.  Thus, r' is a
;; sublist of r:  

(defthmd member-root-poly-list
  (implies (and (fieldp e) (feltsp l e))
           (iff (member x (root-poly-list l e))
                (and (equal x (root-poly (fneg (cadr x) e) e))
		     (feltp (cadr x) e)
		     (member (fneg (cadr x) e) l))))
  :hints (("Goal" :induct (len l))
          ("Subgoal *1/1" :in-theory (enable root-poly))))

(defun pembed-list (l x e f)
  (if (consp l)
      (cons (pembed (car l) x e f)
            (pembed-list (cdr l) x e f))
    ()))

(defthmd member-pembed-root-poly-list
  (implies (and (extensionp e f) (feltsp l e) (in x (galois e f)))
           (iff (member p (pembed-list (root-poly-list l e) x e f))
	        (and (feltp (cadr p) e)
		     (equal p (root-poly (fneg (cadr p) e) e))		     
		     (member (embed (fneg (cadr p) e) (inv-auto x e f) e f) l))))
  :hints (("Goal" :induct (len l))
          ("Subgoal *1/1" :in-theory (enable embed-fneg inv-auto root-poly)
	                  :use ((:instance embed-embedding-inv (phi x) (k e) (x (car l)))
			        (:instance embed-inv-embedding (phi x) (k e) (x (cadr p)))
				(:instance embeddingp-inv-embedding (phi x) (k e))
			        (:instance embed-fneg (phi (inv-embedding x e e f)) (k e) (x (fneg (cadr p) e)))))))

(local-defthmd sublistp-pembed-root-poly-list-1
  (implies (and (extensionp e f)  (galoisp e f) (feltp z e) (in x (galois e f))
                (member c (orbit z (perm-proots e f z) (galois e f))))
	   (member (embed c x e f) (orbit z (perm-proots e f z) (galois e f))))
  :hints (("Goal" :use (actionp-perm-proots
		        (:instance perm-proots-act-rewrite (s c))
			(:instance sublistp-orbit (s z) (a (perm-proots e f z)) (g (galois e f)))
                        (:instance prootp-min-poly (x z))
			(:instance member-proots (x z) (p (plift (min-poly z e f) f e)) (f e))
                        (:instance member-orbit-member-act-orbit (a (perm-proots e f z)) (s z) (r c) (g (galois e f)))))))

(local-defthmd sublistp-pembed-root-poly-list-2
  (implies (and (extensionp e f)  (galoisp e f) (feltp z e) (in x (galois e f))
                (member p (pembed-list (root-orbit-poly-list z e f) x e f)))
	   (member p (root-orbit-poly-list z e f)))
  :hints (("Goal" :in-theory (enable inv-auto root-orbit-poly-list)
                  :use (feltsp-orbit-perm-proots
		        (:instance member-pembed-root-poly-list (l (orbit z (perm-proots e f z) (galois e f))))
		        (:instance member-root-poly-list (x p) (l (orbit z (perm-proots e f z) (galois e f))))
			(:instance embed-inv-embedding (phi x) (k e) (x (fneg (cadr p) e)))
			(:instance sublistp-pembed-root-poly-list-1 (c (embed (fneg (cadr p) e) (inv-auto x e f) e f)))))))

(defthmd sublistp-pembed-root-poly-list
  (implies (and (extensionp e f) (galoisp e f) (feltp z e) (in x (galois e f)))
           (sublistp (pembed-list (root-orbit-poly-list z e f) x e f)
	             (root-orbit-poly-list z e f)))
  :hints (("Goal" :use ((:instance scex1-lemma (l (pembed-list (root-orbit-poly-list z e f) x e f)) (m (root-orbit-poly-list z e f)))
                        (:instance sublistp-pembed-root-poly-list-2 (p (scex1 (pembed-list (root-orbit-poly-list z e f) x e f) (root-orbit-poly-list z e f))))))))

;; r and r' are dlists of the same length, and therefore r' is a permutation of r:

(defthmd dlistp-root-poly-list
  (implies (and (fieldp e) (feltsp l e) (dlistp l))
           (dlistp (root-poly-list l e)))
  :hints (("Goal" :induct (len l))  
          ("Subgoal *1/1" :in-theory (enable root-poly)
	                  :use ((:instance member-root-poly-list (x (root-poly (car l) e)) (l (cdr l)))))))

(defthmd dlistp-pembed-root-poly-list
  (implies (and (extensionp e f) (feltsp l e) (dlistp l) (in x (galois e f)))
           (dlistp (pembed-list (root-poly-list l e) x e f)))
  :hints (("Goal" :induct (len l))  
          ("Subgoal *1/1" :in-theory (e/d (inv-auto root-poly) (fneg-fneg))
	                  :use ((:instance member-pembed-root-poly-list (p (pembed (root-poly (car l) e) x e f)) (l (cdr l)))
			        (:instance embed-embedding-inv (phi x) (k e) (x (car l)))
				(:instance embed-fneg (phi x) (x (car l)) (k e))
				(:instance fneg-fneg (f e) (x (embed (car l) x e f)))))))

(defthm len-pembed-list
  (equal (len (pembed-list l phi k f))
         (len l)))

(defthmd permp-pembed-root-poly-list
  (implies (and (extensionp e f) (galoisp e f) (feltp z e) (in x (galois e f)))
           (permp (pembed-list (root-orbit-poly-list z e f) x e f)
	          (root-orbit-poly-list z e f)))
  :hints (("Goal" :in-theory (enable root-orbit-poly-list)
                  :use (sublistp-pembed-root-poly-list sublistp-orbit-perm-roots feltsp-orbit-perm-proots
		        (:instance dlistp-root-poly-list (l (orbit z (perm-proots e f z) (galois e f))))
			(:instance dlistp-pembed-root-poly-list (l (orbit z (perm-proots e f z) (galois e f))))
                        (:instance len-pembed-list (phi x) (k e) (l (root-orbit-poly-list z e f)))
			(:instance permp-eq-len (l (pembed-list (root-orbit-poly-list z e f) x e f)) (m (root-orbit-poly-list z e f)))))))

;; It follows that (pmul-list r' e) = q:

(local-defthmd monicp-irreduciblep-listp-sublist
  (implies (and (dlistp m) (monicp-irreduciblep-listp l f) (sublistp m l))
           (monicp-irreduciblep-listp m f))
  :hints (("Goal" :induct (len m))
          ("Subgoal *1/1" :use ((:instance member-monicp-irreduciblep-listp (p (car m)))))))

(defthmd monicp-irreduciblep-listp-perm
  (implies (and (dlistp m) (monicp-irreduciblep-listp l f) (permp m l))
           (monicp-irreduciblep-listp m f))
  :hints (("Goal" :in-theory (enable permp) :use (monicp-irreduciblep-listp-sublist))))

(local-defthm pmul-list-perm-1
  (implies (and (fieldp f) (monicp-irreduciblep-listp l f) (member p l))
           (monicp-irreduciblep-listp (remove1 p l) f)))

(local-defthmd pmul-list-perm-2
  (implies (and (fieldp f) (monicp-irreduciblep-listp l f) (member p l))
           (equal (pmul-list l f)
	          (pmul p (pmul-list (remove1 p l) f) f)))
  :hints (("Subgoal *1/5" :use (member-monicp-irreduciblep-listp
                                (:instance pmul-assoc (x p) (y (car l)) (z (PMUL-LIST (REMOVE1-EQUAL P (CDR L)) F)))
                                (:instance pmul-assoc (y p) (x (car l)) (z (PMUL-LIST (REMOVE1-EQUAL P (CDR L)) F)))
                                (:instance pmul-comm (x p) (y (car l)))))))

(defthmd pmul-list-perm
  (implies (and (fieldp f) (monicp-irreduciblep-listp l f) (permutationp m l))
           (equal (pmul-list m f)
	          (pmul-list l f)))
  :hints (("Subgoal *1/1" :use ((:instance pmul-list-perm-1 (p (car m)))))
          ("Subgoal *1/3" :use ((:instance pmul-list-perm-2 (p (car m)))))))

;; It follows from pembed-pmul that (pmul-list r' e) = (pembed (pmul-list r e) x e f) = (pembed q e f):

(defthmd pmul-list-pembed-list
  (implies (and (extensionp e f) (monicp-irreduciblep-listp r e) (in x (galois e f)))
           (equal (pembed (pmul-list r e) x e f)
	          (pmul-list (pembed-list r x e f) e)))
  :hints (("Goal" :induct (len r))
          ("Subgoal *1/1" :use ((:instance pembed-pmul (phi x) (p (car r)) (q (pmul-list (cdr r) e)) (k e))))	  
	  ("Subgoal *1/2" :use ((:instance pembed-id (phi x) (k e))))))

;; Combining pmul-list-pembed-list with pmul-list-perm and permp-pembed-root-poly-list, we have (pembed q x e f) = q:

(defthmd pembed-root-orbit-poly
  (implies (and (extensionp e f) (galoisp e f) (feltp z e) (in x (galois e f)))
           (equal (pembed (root-orbit-poly z e f) x e f)
	          (root-orbit-poly z e f)))
  :hints (("Goal" :in-theory (enable root-orbit-poly-list root-orbit-poly)
                  :use (permp-pembed-root-poly-list feltsp-orbit-perm-proots
		        (:instance dlistp-root-poly-list (l (orbit z (perm-proots e f z) (galois e f))))
			(:instance dlistp-pembed-root-poly-list (l (orbit z (perm-proots e f z) (galois e f))))
			(:instance monic-irreducible-listp-root-poly-list (l (orbit z (perm-proots e f z) (galois e f))))
		        (:instance pmul-list-pembed-list (r (root-orbit-poly-list z e f)))
			(:instance permp-permutationp (l (pembed-list (root-orbit-poly-list z e f) x e f))
	                                              (m (root-orbit-poly-list z e f)))
			(:instance pmul-list-perm (m (pembed-list (root-orbit-poly-list z e f) x e f))
	                                          (l (root-orbit-poly-list z e f))
						  (f e))))))

;; As a consequence of pembed-root-orbit-poly, we shall show that q is lifted from f.  It will suffice to
;; show that q satisfies the following:

(defun pfixedp (p e f)
  (if (consp p)
      (and (fixedp (car p) (galois e f) e f)
           (pfixedp (cdr p) e f))
    t))

;; The desired result will then follow from galois-no-fixed-elt:

(defthmd pfixedp-pliftedp
  (implies (and (extensionp e f) (galoisp e f)
                (feltsp p e) (pfixedp p e f))
	   (pliftedp p f e))
  :hints (("Goal" :induct (len p))
          ("Subgoal *1/1" :use ((:instance galois-no-fixed-elt (a (car p)))))))

;; The proof requires 2 additional definitions.  First we define

(defun fixedp-aux-list (p l e f)
  (if (consp p)
      (and (fixedp-aux (car p) l e f)
           (fixedp-aux-list (cdr p) l e f))
    t))

;; and note the following trivial relation:

(defthmd fixedp-aux-list-pfixedp
  (implies (and (extensionp e f)
                (feltsp p e)
                (fixedp-aux-list p (auto-list e f) e f))
           (pfixedp p e f))
  :hints (("Goal" :in-theory (enable fixedp))))

;; Next, we define

(defun pfixedp-list (p l e f)
  (if (consp l)
      (and (equal (pembed p (car l) e f) p)
           (pfixedp-list p (cdr l) e f))
    t))

;; and note the following consequence of pembed-root-orbit-poly:

(defthmd pfixedp-list-root-orbit-poly
  (implies (and (extensionp e f) (galoisp e f) (feltp z e)
                (sublistp l (auto-list e f)))
           (pfixedp-list (root-orbit-poly z e f) l e f))
  :hints (("Goal" :induct (len l))
          ("Subgoal *1/1" :use ((:instance pembed-root-orbit-poly (x (car l)))))))

;; The following is proved by double induction on the lengths of p and l:

(local-defthmd pfixedp-fixedp-1
  (implies (and (extensionp e f)
                (feltsp p e)
	        (not (consp l)))
           (fixedp-aux-list p l e f))
  :hints (("goal" :induct (len p))))

(local-defthmd pfixedp-fixedp-2
  (implies (and (extensionp e f)
                (feltsp p e)
		(consp p)
                (pfixedp-list p l e f))
           (pfixedp-list (cdr p) l e f))
  :hints (("goal" :induct (len l))))

(local-defthmd pfixedp-fixedp-3
  (implies (and (extensionp e f)
                (feltsp p e)
		(consp l)
                (fixedp-aux-list p (cdr l) e f)
                (embeddingp (car l) e e f)
                (equal (pembed p (car l) e f) p)
                (pfixedp-list p (cdr l) e f))
           (fixedp-aux-list p l e f))
  :hints (("goal" :induct (len p))
          ("subgoal *1/1" :use ((:instance pfixedp-fixedp-2 (l (cdr l)))))))

(defthmd pfixedp-fixed-fixedp-aux-list
  (implies (and (extensionp e f)
                (feltsp p e)
                (sublistp l (auto-list e f))
		(pfixedp-list p l e f))
 	   (fixedp-aux-list p l e f))
  :hints (("Goal" :induct (len l))
          ("Subgoal *1/2" :use (pfixedp-fixedp-1))
          ("Subgoal *1/1" :use (pfixedp-fixedp-3))))

;; Combining the above lemmas, we have the desired result:

(defthmd pliftedp-root-orbit-poly
  (implies (and (extensionp e f) (galoisp e f)
                (feltp z e))
           (pliftedp (root-orbit-poly z e f) f e))
  :hints (("Goal" :use (polyp-root-orbit-poly
                        (:instance pfixedp-list-root-orbit-poly (l (auto-list e f)))
                        (:instance pfixedp-pliftedp (p (root-orbit-poly z e f)))
                        (:instance fixedp-aux-list-pfixedp (p (root-orbit-poly z e f)))
			(:instance pfixedp-fixed-fixedp-aux-list (p (root-orbit-poly z e f)) (l (auto-list e f)))))))  

;; Let p = (min-poly z e f).  Since z is a root of q = (plift (pdrop q e f) f e), p divides (pdrop q e f) by min-poly-divides:

(defthmd pdivides-min-poly-root-orbit-poly
  (implies (and (extensionp e f) (galoisp e f)
                (feltp z e))
           (pdivides (min-poly z e f) (pdrop (root-orbit-poly z e f) e f) f))
  :hints (("Goal" :use (pliftedp-root-orbit-poly polyp-root-orbit-poly prootp-root-orbit-poly
                        (:instance plift-pdrop (p (root-orbit-poly z e f)))
			(:instance min-poly-pdivides (x z) (q (pdrop (root-orbit-poly z e f) e f)))))))

;; Since p divides (pdrop q e f), (plift p f e) divides q by pdivides-plift.  Since q splits in e, it follows from pdivides-splits
;; (plift p f e) splits in e:

(defthmd splits-min-poly
  (implies (and (extensionp e f) (galoisp e f)
                (feltp z e))
           (splits (plift (min-poly z e f) f e) e))
  :hints (("Goal" :in-theory (enable pzero)
                  :use (pdivides-min-poly-root-orbit-poly splits-root-orbit-poly splits-q-3 pliftedp-root-orbit-poly
                        (:instance plift-pdrop (p (root-orbit-poly z e f)))
			(:instance prootp-min-poly (x z))
			(:instance pdivides-plift (y (min-poly z e f)) (x (pdrop (root-orbit-poly z e f) e f)))
			(:instance pdivides-splits (f e) (q (plift (min-poly z e f) f e)) (p (root-orbit-poly z e f)))))))

;; Since q is separable in e, (pdrop q e f) is separable in f by separablep-extension.  Since p divides (pdrop q e f), p splits
;; in f by pdivides-separablep:

(defthmd separablep-min-poly
  (implies (and (extensionp e f) (galoisp e f)
                (feltp z e))
           (separablep (min-poly z e f) f))
  :hints (("Goal" :in-theory (enable pzero)
                  :use (pdivides-min-poly-root-orbit-poly separablep-root-orbit-poly splits-q-3 pliftedp-root-orbit-poly
                        (:instance plift-pdrop (p (root-orbit-poly z e f)))
			(:instance prootp-min-poly (x z))
			(:instance separablep-extension (p (pdrop (root-orbit-poly z e f) e f)))
			(:instance pdivides-separablep (q (min-poly z e f)) (p (pdrop (root-orbit-poly z e f) e f)))))))

;; Since z is an arbitrary element of e, e is a noraml and separable extension of f:

(defthmd galois-normal-separable
  (implies (and (extensionp e f) (galoisp e f))
           (and (normal-extension-p e f)
	        (separable-extension-p e f)))
  :hints (("Goal" :use ((:instance splits-min-poly (z (normal-extension-p-witness e f)))
                        (:instance separablep-min-poly (z (separable-extension-p-witness e f)))))))


;;---------------------------------------------------------

;; Conversely, let e be a normal and separable extension of f.  The following function computes the lcm of
;; the minimal polynomials over f of the primitive elements of e:

(defun generating-poly (e f)
  (if (and (extensionp e f) (not (equal e f)))
      (let ((p (generating-poly (cdr e) f))
            (q (min-poly (primitive e) e f)))
	(if (pdivides q p f)
	    p
	  (pmul q p f)))
    (pone f)))

;; Let p = (generating-poly e f).  We shall prove that p is separable and e is a splitting field of p.
;; It is easily proved by induction on e that p is a monic polynomial over f:

(defthm polyp-generating-poly
  (implies (extensionp e f)
           (let ((p (generating-poly e f)))
             (and (polyp p f)
	          (monicp p f)
	          (not (equal p (pzero f))))))
  :hints (("Goal" :induct (len e))
          ("Subgoal *1/2" :in-theory (enable polyp pzero monicp pone))
          ("Subgoal *1/1" :in-theory (enable monicp pzero pone polyp)
	                  :use ((:instance prootp-min-poly (x (primitive e)))
			        (:instance car-pmul (x (MIN-POLY (PRIMITIVE E) E F)) (y (GENERATING-POLY (CDR E) F)))
	                        (:instance degree-pmul (x (MIN-POLY (PRIMITIVE E) E F)) (y (GENERATING-POLY (CDR E) F)))))))

(local-defun e-not-f-induct (e f)
  (if (and (consp e) (not (equal (cdr e) f)))
      (e-not-f-induct (cdr e) f)
    t))

(local-defthmd not-divides-pone
  (implies (and (fieldp f) (polyp p f) (>= (degree p) 1))
           (and (not (equal p (pzero f)))
	        (not (pdivides p (pone f) f))))
  :hints (("Goal" :in-theory (enable pone pzero polyp)
                  :use (polyp-pone (:instance pdivides-degree (x p) (y (pone f)))))))

;; If e != f, then p is not a constant:

(defthm generating-poly-not-constant
  (implies (and (extensionp e f) (not (equal e f)))
           (>= (degree (generating-poly e f))
	       1))
  :hints (("Goal" :induct (e-not-f-induct e f))  
          ("Subgoal *1/2" :use ((:instance not-divides-pone (p (min-poly (primitive e) e f)))
	                        (:instance prootp-min-poly (x (primitive e)))))
          ("Subgoal *1/1" :use ((:instance prootp-min-poly (x (primitive e)))
	                        (:instance degree-pmul (x (MIN-POLY (PRIMITIVE E) E F)) (y (GENERATING-POLY (CDR E) F)))))))

;; Note that as a consequence of min-poly-flift-min-poly, if k is an intermediate field between e and f, then k is a separable extension of f:

(defthmd separable-extension-p-intermediate
  (implies (and (extensionp e k) (extensionp k f) (separable-extension-p e f))
           (separable-extension-p k f))
  :hints (("Goal" :use ((:instance separable-extension-p-necc (x (flift (separable-extension-p-witness k f) k e)))
                        (:instance min-poly-flift-min-poly (x (separable-extension-p-witness k f)) (d k))))))

;; We shall use this result to prove by induction on e that p is separable over f.  Assume that e != f.  Then by (cdr e) is a separable 
;; extension of f.  Let m = (min-poly (primitive e) e f) and p' = (generating-poly (cdr e) f) f).  By induction, p' is separable, and
;; by hypothesis, so is m.  If m divides p', then p = p'.  Otherwise, by pgcd-irreduciblep, (pgcd m p') = 1 and by separablep-pmul, p is
;; separable:

(defthm separablep-generating-poly
  (implies (and (extensionp e f) (separable-extension-p e f))
           (separablep (generating-poly e f) f))
  :hints (("Goal" :induct (len e))
          ("Subgoal *1/2" :in-theory (enable pone pzero pconstp)
	                  :use ((:instance polyp-pone (f e))
			        (:instance pconstp-separablep (p (pone e)) (f e))))				
          ("Subgoal *1/1" :in-theory (enable pone pzero pconstp)
	                  :use ((:instance polyp-pone (f e))
			        (:instance pconstp-separablep (p (pone e)) (f e))
				(:instance separable-extension-p-intermediate (k (cdr e)))
				(:instance SEPARABLE-EXTENSION-P-NECC (x (primitive e)))
				(:instance polyp-generating-poly (e (cdr e)))
				(:instance prootp-min-poly (x (primitive e)))
				(:instance pgcd-irreduciblep (p (MIN-POLY (PRIMITIVE E) E F)) (x (GENERATING-POLY (CDR E) F)))
				(:instance separablep-pmul (p (MIN-POLY (PRIMITIVE E) E F)) (q (GENERATING-POLY (CDR E) F)))))))

 ;; Let k be an intermediate field between e and f.  It is easily proved by induction on e that (generating-poly k f) divides p:

(defthmd pdivides-generating-poly
  (implies (and (extensionp e k) (extensionp k f))
           (pdivides (generating-poly k f)
	             (generating-poly e f)
		     f))
  :hints (("Goal" :induct (len e))
          ("Subgoal *1/2" :use ((:instance pdivides-self (x (pone e)) (f e))))
          ("Subgoal *1/1" :use ((:instance pdivides-self (x (pone e)) (f e))
	                        (:instance pdivides-self (x (generating-poly e f)))
				(:instance prootp-min-poly (x (primitive e)))
				(:instance len-extends (f k))
				(:instance len-extends (e (cdr e)) (f k))
				(:instance len-extends (e k) (f e))
				(:instance pdivides-pmul (x (GENERATING-POLY K F))
				                         (y (GENERATING-POLY (CDR E) F))
							 (z (MIN-POLY (PRIMITIVE E) E F)))
				(:instance pmul-comm (x (GENERATING-POLY (CDR E) F))
				                     (y (MIN-POLY (PRIMITIVE E) E F)))))))

;; We shall also prove, by induction on k, that (generating-poly k f) splits in e.
;; Assume that k != f and (generating-poly (cdr k) f) splits in e.  We need only show that (min-poly (primitive k) k f) splits
;; in e.  But by min-poly-flift-min-poly, (min-poly (primitive k) k f) = (min-poly (flift (primitive k) k e) e f), which splits in e
;; since e is a normal extension of f:

(defthm splits-generating-poly
  (implies (and (extensionp e k) (extensionp k f) (not (equal k f)) (normal-extension-p e f))
           (splits (plift (generating-poly k f) f e) e))
  :hints (("Goal" :induct (e-not-f-induct k f))
          ("Subgoal *1/2" :in-theory (enable pzero pone)
	                  :use ((:instance prootp-min-poly (x (primitive k)) (e k))
			        (:instance polyp-pone)
				(:instance pone-id-2 (x (min-poly (primitive k) k f)))
				(:instance normal-extension-p-necc (x (flift (primitive k) k e)))
				(:instance min-poly-flift-min-poly (x (primitive k)) (d k))
	                        (:instance pdivides-degree (x (min-poly (primitive k) k f)) (y (pone f)))))
          ("Subgoal *1/1" :in-theory (enable polyp-plift)
	                  :use ((:instance extends-trans (d k) (f (cdr k)))
			        (:instance extends-trans (d k))
				(:instance generating-poly-not-constant (e (cdr k)))
				(:instance normal-extension-p-necc (x (flift (primitive k) k e)))
				(:instance min-poly-flift-min-poly (x (primitive k)) (d k))
	                        (:instance plift-pmul (p (min-poly (primitive k) k f)) (q (generating-poly (cdr k) f)))
				(:instance prootp-min-poly (x (primitive k)) (e k))
				(:instance splits-pmul (f e) (p (plift (min-poly (primitive k) k f) f e)) (q (plift (generating-poly (cdr k) f) f e)))))))

;; To complete the proof that e is a splitting field of p, we shall prove by induction on k that k is an extension of f by roots of p.
;; Suppose k != f and that (cdr k) is an extension of f by roots of p.  We must show that (car k) divides (plift p f (cdr k)).  By
;; pdivides-generating-poly,

;;   (generating-poly e k) divides (generating-poly e f) = p

;; and by definition, 

;;   (min-poly (primitive k) k f) divides (generating-poly e k).

;;   It follows that (min-poly (primitive k) k f) divides p, which implies

;;   (plift (min-poly (primitive k) k f) f (cdr k)) divides (plift p f (cdr k)).

;; Therefore, it suffices to show that

;;   (car k) divides (plift (min-poly (primitive k) k f) f (cdr k)).

;; By min-poly-primitive,

;;    (car k) = (min-poly (primitive k) k (cdr k)).

;; By prootp-min-poly, (primitive k) is a root of

;;    (plift (min-poly (primitive k) k f) f k)
;;      = (plift (plift (min-poly (primitive k) k f) f (cdr k)) (cdr k) k).

;; Thus, by min-poly-pdivides,

;;    (car k) divides (plift (min-poly (primitive k) k f) f (cdr k))

;; as required.

(local-defthmd by-roots-p-gen-poly-1
  (implies (and (extensionp e k) (extensionp k f) (not (equal k f)))
           (pdivides (min-poly (primitive k) k f)
	             (generating-poly k f)
		     f))
  :hints (("Goal" :use ((:instance prootp-min-poly (x (primitive k)) (e k))
                        (:instance pdivides-multiple (x (min-poly (primitive k) k f)) (y (generating-poly (cdr k) f)))))))

(local-defthmd by-roots-p-gen-poly-2
  (implies (and (extensionp e k) (extensionp k f) (not (equal k f)))
           (pdivides (min-poly (primitive k) k f)
	             (generating-poly e f)
		     f))
  :hints (("Goal" :expand ((extends k f))
                  :use (pdivides-generating-poly by-roots-p-gen-poly-1
                        (:instance prootp-min-poly (x (primitive k)) (e k))
			(:instance extends-trans (d k))
			(:instance pdivides-transitive (x (min-poly (primitive k) k f)) (y (generating-poly k f)) (z (generating-poly e f)))))))

(local-defthmd by-roots-p-gen-poly-3
  (implies (and (extensionp e k) (extensionp k f) (not (equal k f)))
           (pdivides (plift (min-poly (primitive k) k f) f (cdr k))
	             (plift (generating-poly e f) f (cdr k))
		     (cdr k)))
  :hints (("Goal" :expand ((extends k f))
                  :use (by-roots-p-gen-poly-2
		        (:instance pdivides-plift (e (cdr k)) (y (min-poly (primitive k) k f)) (x (generating-poly e f)))
                        (:instance prootp-min-poly (x (primitive k)) (e k))
			(:instance extends-trans (d k))))))

(local-defthmd by-roots-p-gen-poly-4
  (implies (and (extensionp e k) (extensionp k f) (not (equal k f)))
           (equal (car k)
	          (min-poly (primitive k) k (cdr k))))
  :hints (("Goal" :use ((:instance min-poly-primitive (f k))))))

(local-defthmd by-roots-p-gen-poly-5
  (implies (and (extensionp e k) (extensionp k f) (not (equal k f)))
           (prootp (primitive k)
	           (plift (plift (min-poly (primitive k) k f) f (cdr k)) (cdr k) k)
		   k))
  :hints (("Goal" :expand ((extends k f))
                  :use ((:instance extends-trans (d k))
                        (:instance prootp-min-poly (x (primitive k)) (e k))))))

(local-defthmd by-roots-p-gen-poly-6
  (implies (and (extensionp e k) (extensionp k f) (not (equal k f)))
           (pdivides (car k)
	             (plift (min-poly (primitive k) k f) f (cdr k))
		     (cdr k)))
  :hints (("Goal" :use (by-roots-p-gen-poly-4
                         (:instance prootp-min-poly (x (primitive k)) (e k))
			 (:instance min-poly-pdivides (x (primitive k)) (e k) (f (cdr k)) (q (plift (min-poly (primitive k) k f) f (cdr k))))))))

(local-defthmd by-roots-p-gen-poly-7
  (implies (and (extensionp e k) (extensionp k f) (not (equal k f)))
           (pdivides (car k)
	             (plift (generating-poly e f) f (cdr k))
		     (cdr k)))
  :hints (("Goal" :expand ((extends k f))
                  :use (by-roots-p-gen-poly-3 by-roots-p-gen-poly-4 by-roots-p-gen-poly-6
                         (:instance extends-trans (d k))
			 (:instance prootp-min-poly (x (primitive k)) (e k))
			 (:instance plift-pzero (e (cdr k)) (p (min-poly (primitive k) k f)))
			 (:instance pdivides-transitive (f (cdr k)) (x (car k)) (y  (plift (min-poly (primitive k) k f) f (cdr k))) (z (plift (generating-poly e f) f (cdr k))))))))

(defthmd extension-by-roots-p-generating-poly
  (implies (and (extensionp e k) (extensionp k f))
           (extension-by-roots-p (generating-poly e f) k f))
  :hints (("Goal" :induct (len k))
          ("Subgoal *1/1" :use (by-roots-p-gen-poly-7))))

;; Thus, e is a galois extension of f and we have the following equivalence:

(defthmd galois-equivalence
  (implies (extensionp e f)
           (iff (galoisp e f)
	        (and (normal-extension-p e f)
		     (separable-extension-p e f))))
  :hints (("Goal" :in-theory (enable splitting-field-p)
                  :use (galoisp-trivial galois-normal-separable separablep-generating-poly generating-poly-not-constant
                        (:instance extension-by-roots-p-generating-poly (k e))
			(:instance splits-generating-poly (k e))
			(:instance galoisp-suff (p (generating-poly e f)))))))
			
;;----------------------------------------------------------------------------------------------------------

;; I thought I needed separablep-pembed for the proof of galoisp-isomorphic, but what I need instead is
;; pembed-min-poly (below).  So I'll just leave this here for now:

(local-defthmd not-divides-pone
  (implies (and (fieldp f) (polyp p f) (>= (degree p) 1))
           (and (not (equal p (pzero f)))
	        (not (pdivides p (pone f) f)))))

(local-defthmd pgcd-monic-better
  (implies (and (fieldp f) 
                (polyp x f) (polyp y f)
                (not (equal x (pzero f))))
           (monicp (pgcd x y f) f))
  :hints (("Goal" :use (pgcd-monic pgcd-comm monicp-make-monic
                        (:instance pgcd-pzero (p x))))))

(local-defthmd monicp-not-pone
  (implies (and (polyp p f) (monicp p f) (equal (degree p) 0))
           (equal (pone f) p))
  :hints (("Goal" :in-theory (enable polyp pone monicp)
                  :expand ((len p) (len (cdr p))))))

(local-defthmd polyp-len-pos
  (implies (polyp p f) (> (len p) 0))
  :hints (("Goal" :in-theory (enable polyp))))

(local-defthmd separablep-pembed-1
  (implies (and (extensionp e f) (extensionp k f) (embeddingp phi e k f)
                (polyp p e) (>= (degree p) 1) (separablep p e) (not (separablep (pembed p phi k f) k)))
	   (let* ((p1 (pembed p phi k f))
	          (d1 (derivative p1 k))
		  (g1 (pgcd p1 d1 k)))
	     (and (polyp g1 k)
	          (polyp p1 k)
	          (polyp d1 k)
		  (not (equal p1 (pzero k)))
		  (not (equal d1 (pzero k)))
	          (>= (degree g1) 1)
		  (pdivides g1 p1 k)
		  (pdivides g1 d1 k))))
  :hints (("Goal" :in-theory (enable polyp-derivative separablep)
                  :use (derivative-pembed polyp-pembed pembed-pzero
		        (:instance monicp-not-pone (f k) (p (pgcd (pembed p phi k f) (derivative (pembed p phi k f) k) k)))
			(:instance pembed-pzero (p (derivative p e)))
			(:instance derivative-pzero-not-separablep (f e))
			(:instance polyp-len-pos (f k) (p (pgcd (pembed p phi k f) (derivative (pembed p phi k f) k) k)))
			(:instance pgcd-monic (f k) (x (pembed p phi k f)) (y (derivative (pembed p phi k f) k)))
			(:instance pgcd-divides (f k) (x (pembed p phi k f)) (y (derivative (pembed p phi k f) k)))))))

(local-defthmd separablep-pembed-2
  (implies (and (extensionp e f) (extensionp k f) (embeddingp inv k e f)
		(polyp p1 k) (not (equal p1 (pzero k)))
                (polyp g1 k) (>= (degree g1) 1)
		(pdivides g1 p1 k) (pdivides g1 (derivative p1 k) k))
	   (not (separablep (pembed p1 inv e f) e))) 
  :hints (("Goal" :in-theory (enable polyp-derivative separablep)
                  :use ((:instance derivative-pembed (p p1) (phi inv) (e k) (k e))
		        (:instance polyp-pembed (p p1) (phi inv) (e k) (k e))
		        (:instance polyp-pembed (p g1) (phi inv) (e k) (k e))
			(:instance pembed-pzero (p p1) (phi inv) (e k) (k e))
			(:instance pembed-pzero (p (derivative p1 k)) (phi inv) (e k) (k e))
			(:instance pdivides-pembed (y g1) (x p1) (phi inv) (e k) (k e))
			(:instance pdivides-pembed (y g1) (x (derivative p1 k)) (phi inv) (e k) (k e))
			(:instance not-divides-pone (f e) (p (pembed g1 inv e f)))
			(:instance divides-pgcd (f e) (z (pembed g1 inv e f)) (x (pembed p1 inv e f)) (y (derivative (pembed p1 inv e f) e)))))))

(defthmd separablep-pembed
  (implies (and (extensionp e f) (extensionp k f)
                (equal (edegree e f) (edegree k f)) (embeddingp phi e k f)
                (polyp p e) (>= (degree p) 1) (separablep p e))
	   (separablep (pembed p phi k f) k))
  :hints (("Goal" :use (pembed-embedding-inv embeddingp-inv-embedding separablep-pembed-1
                        (:instance separablep-pembed-2 (inv (inv-embedding phi e k f))
			                               (p1 (pembed p phi k f))
						       (g1 (pgcd (pembed p phi k f) (derivative (pembed p phi k f) k) k)))))))

;;--------------------------

;; This belongs in the section on minimal polynomials in ../galois.lisp:

;; Let x be in e, m = (min-poly x e), and x' = (embed x phi k f).  Then m = (min-poly x' k).

;;    (peval (plift m f k) x' k) = (peval (pembed (plift m f k) phi k f) x' k)  [pembed-fixes]
;;                               = (embed (peval (plift m f k) x e) phi k f)    [peval-pembed]
;;                               = (embed (fzero e) phi k f)                    [prootp-min-poly]
;;                               = (fzero k)                                    [embed-fzero-fone]

;; By min-poly-pdivides, (min-poly x' k f) divides m, and by pdivides-monic-equal, (min-poly x' k f) = m.

(defthmd pembed-min-poly
  (implies (and (extensionp e f) (extensionp k f) (embeddingp phi e k f)
                (feltp x e))
	   (equal (min-poly (embed x phi k f) k f)
	          (min-poly x e f)))
  :hints (("Goal" :in-theory (enable prootp)
                  :use (prootp-min-poly embed-fzero-fone
		        (:instance peval-pembed (p (plift (min-poly x e f) f e)))
		        (:instance pembed-fixes (p (min-poly x e f)))
			(:instance prootp-min-poly (x (embed x phi k f)) (e k))
			(:instance min-poly-pdivides (e k) (x (embed x phi k f)) (q (min-poly x e f)))
			(:instance irreduciblep-pdivides-monic-equal (x (min-poly (embed x phi k f) k f)) (y (min-poly x e f)))))))
			
;;--------------------------

;; Let e and k be isomorphic extensions of f.  We shall show that if e galois over over f, then so is k.
;; Let phi be an embedding of e in k over f.  Let x be an element of k and y = (embed x (inv-embedding phi e k f) e f).
;; Then x = (embed y phi k f).  Since e is a separable and normal extension of f, (min-poly x e k) is separable and
;; (plift (min-poly x e k) f e) splits in e.  By pembed-min-poly, (min-poly x e k) = (min-poly y e f), and we need only
;; show that (plift (min-poly x k f) f k) splits in k.   But by pembed-fixes,

;;    (plift (min-poly x k f) f k) = (plift (min-poly y e f) f k) = (pembed (plift (min-poly y e f) f e) phi k f),

;; which splits in k by splits-pembed.

(in-theory (disable normal-extension-p separable-extension-p))

(local-defthmd galoisp-isomorphic-1
  (implies (and (extensionp e f) (extensionp k f)
                (embeddingp phi e k f) (equal (edegree e f) (edegree k f))
		(normal-extension-p e f) (separable-extension-p e f)
		(feltp x k))
	   (let ((y (embed x (inv-embedding phi e k f) e f)))
	     (and (feltp y e)
	          (equal (embed y phi k f) x)
	          (separablep (min-poly y e f) f)
	          (splits (plift (min-poly y e f) f e) e))))
  :hints (("Goal" :use (comp-inv-embedding embed-inv-embedding
                        (:instance embed-image (phi (inv-embedding phi e k f)) (k e) (e k))
			(:instance normal-extension-p-lemma (x (embed x (inv-embedding phi e k f) e f)))
			(:instance separable-extension-p-lemma (x (embed x (inv-embedding phi e k f) e f)))))))

(local-defthmd galoisp-isomorphic-2
  (implies (and (extensionp e f) (extensionp k f) (embeddingp phi e k f)
		(feltp y e)
		(separablep (min-poly y e f) f)
	        (splits (plift (min-poly y e f) f e) e))
	   (let ((x (embed y phi k f)))
	     (and (separablep (min-poly x k f) f)
	          (splits (plift (min-poly x k f) f k) k))))
  :hints (("Goal" :use ((:instance pembed-min-poly (x y))
                        (:instance pembed-fixes (p (min-poly y e f)))
			(:instance splits-pembed (p (plift (min-poly y e f) f e)))
			(:instance prootp-min-poly (x y))))))

(local-defthmd galoisp-isomorphic-3
  (implies (and (extensionp e f) (extensionp k f)
                (embeddingp phi e k f) (equal (edegree e f) (edegree k f))
		(normal-extension-p e f) (separable-extension-p e f)
		(feltp x k))
	   (and (separablep (min-poly x k f) f)
	        (splits (plift (min-poly x k f) f k) k)))
  :hints (("Goal" :use (galoisp-isomorphic-1
                        (:instance galoisp-isomorphic-2 (y (embed x (inv-embedding phi e k f) e f)))))))

(local-defthmd galoisp-isomorphic-4
  (implies (and (extensionp e f) (extensionp k f)
                (embeddingp phi e k f) (equal (edegree e f) (edegree k f))
		(normal-extension-p e f) (separable-extension-p e f))
	   (and (normal-extension-p k f) (separable-extension-p k f)))
  :hints (("Goal" :use ((:instance galoisp-isomorphic-3 (x (normal-extension-p-witness k f)))
                        (:instance galoisp-isomorphic-3 (x (separable-extension-p-witness k f)))
			(:instance normal-extension-p-witness-lemma (e k))
			(:instance separable-extension-p-witness-lemma (e k))))))

(in-theory (disable galoisp))

(defthmd edegree>1
  (implies (and (extensionp e f)
                (not (equal e f)))
	   (> (edegree e f) 1))
  :hints (("Subgoal *1/1" :nonlinearp t :expand ((fieldp e)))))

(defthmd galoisp-isomorphic
  (implies (and (extensionp e f) (extensionp k f)
                (embeddingp phi e k f) (equal (edegree e f) (edegree k f))
		(galoisp e f))
	   (galoisp k f))
  :hints (("Goal" :use (galoisp-isomorphic-4 galois-equivalence edegree>1
                        (:instance edegree>1 (e k))
                        (:instance galois-equivalence (e k))))))
	   
;;---------------------------------------------------

;; I thought I needed this, but maybe not:

(defthmd reduciblep-pembed-isomorphic
  (implies (and (extensionp e f) (extensionp k f)
                (embeddingp phi e k f) (equal (edegree e f) (edegree k f))
                (polyp x e))
	   (iff (reduciblep x e)
	        (reduciblep (pembed x phi k f) k)))
  :hints (("Goal" :use (reduciblep-pembed embeddingp-inv-embedding
                        (:instance pembed-embedding-inv (p x))
                        (:instance polyp-pembed (p x))
                        (:instance reduciblep-pembed (e k) (k e) (x (pembed x phi k f)) (phi (inv-embedding phi e k f)))))))


;;----------------------------------------------------------------------------------------------------------
;;                                   Fundamental Theorem of Galois Theory
;;----------------------------------------------------------------------------------------------------------

;; Suppose k is an extension of f, e is an extension of k, and e is galois over f.  Let x be an element of e
;; with m = (min-poly x e f) and m' = (min-poly x e k).  Then m is separable and splits in e, and m' divides
;; m by min-poly-divides-min-poly-plift.  By pdivides-splits, m' splits in e, and by separablep-extension and
;; pdivides-separablep, m' is separable over k.  Thus, e is galois over k:

(local-defthmd galoisp-subfield-1
  (implies (and (extensionp e f) (galoisp e f) (feltp x e))
           (and (separablep (min-poly x e f) f)
	        (splits (plift (min-poly x e f) f e) e)))
  :hints (("Goal" :use (galois-equivalence separable-extension-p-lemma normal-extension-p-lemma))))

(local-defthmd galoisp-subfield-2
  (implies (and (extensionp e k) (extensionp k f) (galoisp e f) (feltp x e))
           (and (separablep (min-poly x e k) k)
	        (splits (plift (min-poly x e k) k e) e)))
  :hints (("Goal" :use (galoisp-subfield-1 prootp-min-poly
                        (:instance min-poly-divides-min-poly-plift (d k))
                        (:instance extends-trans (d k))
			(:instance pdivides-plift (f k) (y (min-poly x e k)) (x (plift (min-poly x e f) f k)))
			(:instance pdivides-splits (f e) (q (plift (min-poly x e k) k e)) (p (plift (min-poly x e f) f e)))
			(:instance pdivides-separablep (f k) (q (min-poly x e k)) (p (plift (min-poly x e f) f k)))
			(:instance separablep-extension (e k) (p (min-poly x e f)))
			(:instance plift-pzero (e k) (p (min-poly x e f)))
			(:instance prootp-min-poly (f k))))))

(defthmd galoisp-subfield
  (implies (and (extensionp e k) (extensionp k f) (galoisp e f))
           (galoisp e k))
  :hints (("Goal" :use ((:instance normal-extension-p-witness-lemma (f k))
                        (:instance separable-extension-p-witness-lemma (f k))
			(:instance galoisp-subfield-2 (x (normal-extension-p-witness e k)))
			(:instance galoisp-subfield-2 (x (separable-extension-p-witness e k)))
			(:instance galois-equivalence (f k))))))

;; On the other hand, let x be an element of k.  By min-poly-flift-min-poly, (min-poly x k f) =
;; (min-poly (flift x k e) e f), which is separable since e is a separable extension of f.
;; Thus, k is a separable extension of f:

(local-defthmd separable-extension-p-subfield-1
  (implies (and (extensionp e k) (extensionp k f) (separable-extension-p e f) (feltp x k))
           (separablep (min-poly x k f) f))
  :hints (("Goal" :use ((:instance separable-extension-p-lemma (x (flift x k e)))
                        (:instance min-poly-flift-min-poly (d k))
			(:instance extends-trans (d k))))))

(defthmd separable-extension-p-subfield
  (implies (and (extensionp e k) (extensionp k f) (separable-extension-p e f))
           (separable-extension-p k f))
  :hints (("Goal" :use ((:instance separable-extension-p-witness-lemma (e k))
                        (:instance separable-extension-p-subfield-1 (x (separable-extension-p-witness k f)))))))

;; Thus, if k is a normal extension of f, then k is galois over f:

(defthmd normal-extension-p-subfield
  (implies (and (extensionp e k) (extensionp k f) (galoisp e f) (normal-extension-p k f))
           (galoisp k f))
  :hints (("Goal" :use (separable-extension-p-subfield galois-equivalence
                        (:instance galois-equivalence (e k))
			(:instance extends-trans (d k))))))


;; Let g = (galois e f) and let k be an intermediate field of the extension.  We shall define a subgroup of
;; g, (galois-subgroup k e f), consisting of those automorphisms of e over f that fix k, or more precisely,
;; that lift each element of k to e.  We shall show that this subgroup is isomorphic to (galois e k).

;; The element list of (galois-subgroup k e f) is defined as follows:

(defun fixing-autos-aux (l k e f)
  (if (consp l)
      (if (equal (restrict-embedding (car l) e k)
                 (trivial-embedding k e f))
          (cons (car l) (fixing-autos-aux (cdr l) k e f))
	(fixing-autos-aux (cdr l) k e f))
    ()))

(defund fixing-autos (k e f)
  (fixing-autos-aux (auto-list e f) k e f))

(local-defthmd member-fixing-autos-aux
  (iff (member x (fixing-autos-aux l k e f))
       (and (member x l)
            (equal (restrict-embedding x e k)
                   (trivial-embedding k e f)))))

(defthmd member-fixing-autos
  (iff (member x (fixing-autos k e f))
       (and (member x (auto-list e f))
            (equal (restrict-embedding x e k)
                   (trivial-embedding k e f))))
  :hints (("Goal" :in-theory (enable fixing-autos)
                  :use ((:instance member-fixing-autos-aux (l (auto-list e f)))))))

(in-theory (disable restrict-embedding trunc-embedding))

;; If phi is a member of (fixing-autos k e f) and x is an element of e lifted from k, then

;;    (embed x phi e f) = x.

;; We shall prove the following generalization:

;; Let d be an intermediate field between e and k and let phi be an embedding of d in e over 
;; f such that (restrict-embedding phi d k) = (trivial-embedding k e f).  Let x be an element 
;; of k.  Then (embed (flift x k d) phi e f) = (flift x k e).

;; Proof: If d = k, then phi = (trivial-embedding k e f) and the claim follows from
;; trivial-embedding-flift.  If d != k, then by induction and embed-flift,

;;    (embed (flift x k d) phi e f) = (embed (flift (flift x k (cdr d)) (cdr d) d) phi e f)
;;                                  = (embed (flift x k (cdr d)) (cdr phi) e f)
;;				    = (flift x k e).

(local-defun fixing-auto-fixes-induct (d phi k)
  (declare (irrelevant phi))
  (if (and (consp d) (not (equal d k)))
      (fixing-auto-fixes-induct (cdr d) (cdr phi) k)
    t))

(local-defthmd fixing-auto-fixes-1
  (implies (and (extensionp e k) (extensionp k f) (extensionp e d) (extensionp d k)
                (embeddingp phi d e f)
		(equal (restrict-embedding phi d k)
                       (trivial-embedding k e f))
		(feltp x k))
	   (equal (embed (flift x k d) phi e f)
	          (flift x k e)))
  :hints (("Goal" :induct (fixing-auto-fixes-induct d phi k))
          ("Subgoal *1/2" :expand ((restrict-embedding phi d d))
	                  :use ((:instance trivial-embedding-flift (e d) (k e))))
	  ("Subgoal *1/1" :in-theory (enable embeddingp restrict-embedding)
	                  :use ((:instance extends-trans (f (cdr d)))
	                        (:instance extends-trans (d (cdr d)))
	                        (:instance extends-trans (e (cdr d)) (d k))
	                        (:instance embed-flift (x (flift x k (cdr d))) (k e) (e d))
				(:instance len-extends (e k) (f d))
				(:instance len-extends (e (cdr d)) (f k))))))

;; Substituting e for d yields the following:

(defthmd fixing-auto-fixes
  (implies (and (extensionp e k) (extensionp k f)
		(member phi (fixing-autos k e f))
		(feltp x k))
	   (equal (embed (flift x k e) phi e f)
	          (flift x k e)))
  :hints (("Goal" :in-theory (enable autop)
                  :use ((:instance fixing-auto-fixes-1 (d e))
                        (:instance member-fixing-autos (x phi))
			(:instance extends-trans (d k))))))

;; To prove that (fixing-autos k e f) forms a subgroup of g, we must prove the appropriate instance of the 6 lemmas
;; listed in the comment preceding the definition of defsubgroup ("../groups/groups.lisp").  The first 4 are trivial:

(local-defthmd restrict-trivial-embedding
  (implies (and (extensionp e k) (extensionp k f))
           (equal (restrict-embedding (trivial-embedding e d f) e k)
	          (trivial-embedding k d f)))
  :hints (("Goal" :induct (len e))
          ("Subgoal *1/2" :in-theory (enable restrict-embedding))
          ("Subgoal *1/1" :in-theory (enable cdr-nthcdr restrict-embedding)
	                  :use ((:instance len-extends (e k) (f e))
			        (:instance len-extends (e (cdr e)) (f k))))))

(defthm restrict-id-auto
  (implies (and (extensionp e k) (extensionp k f))
           (equal (restrict-embedding (id-auto e f) e k)
	          (trivial-embedding k e f)))
  :hints (("Goal" :in-theory (enable id-auto id-embedding)
                  :use ((:instance restrict-trivial-embedding (d e))))))

(defthm car-fixing-autos
  (implies (and (extensionp e k) (extensionp k f))
           (equal (car (fixing-autos k e f))
	          (id-auto e f)))
  :hints (("Goal" :in-theory (enable fixing-autos)
                  :expand ((fixing-autos-aux (auto-list e f) k e f)))))

(defthm consp-fixing-autos
  (implies (and (extensionp e k) (extensionp k f))
           (consp (fixing-autos k e f)))
  :hints (("Goal" :in-theory (enable fixing-autos)
                  :expand ((fixing-autos-aux (auto-list e f) k e f)))))

(local-defthmd dlistp-fixing-autos-aux
  (implies (dlistp l)
           (dlistp (fixing-autos-aux l k e f)))
  :hints (("Subgoal *1/2" :use ((:instance member-fixing-autos-aux (x (car l)) (l (cdr l)))))))

(defthm dlistp-fixing-autos
  (implies (and (extensionp e k) (extensionp k f))
           (dlistp (fixing-autos k e f)))
  :hints (("Goal" :in-theory (enable fixing-autos)
                  :use ((:instance dlistp-fixing-autos-aux (l (auto-list e f)))
		        (:instance extends-trans (d k))))))

(local-defthmd sublistp-fixing-autos-aux
  (implies (and (extensionp e k) (extensionp k f))
           (sublistp (fixing-autos-aux l k e f) l))
  :hints (("Subgoal *1/2" :use ((:instance member-fixing-autos-aux (x (car l)) (l (cdr l)))))))

(defthm sublistp-fixing-autos
  (implies (and (extensionp e k) (extensionp k f))
           (sublistp (fixing-autos k e f) (auto-list e f)))
  :hints (("Goal" :in-theory (enable fixing-autos)
                  :use ((:instance sublistp-fixing-autos-aux (l (auto-list e f)))
		        (:instance extends-trans (d k))))))

;; The proof of closure under the group operation requires 2 induction.  Let x be a member of (fixing-autos k e f).
;; First we show, using fixing-auto-fixes, that if d is an intermediate field between k and f, then

;;    (comp-embedding x (trivial-embedding d e f) d e f) = (trivial-embedding d e f).

;; Using this result for the case d = k, we then show that if d is an intermediate field between e and k and y is an
;; embedding of d in e over f such that (restrict-embedding y d k) = (trivial-embedding k e f), then the same is true
;; of (comp-embedding x y d e f).  The desired result is the case d = e:

(local-defthmd comp-fixing-autos-1
  (implies (and (extensionp e k) (extensionp k f) (extensionp k d) (extensionp d f)
                (member x (fixing-autos k e f)))
           (equal (comp-embedding x (trivial-embedding d e f) d e f)
	          (trivial-embedding d e f)))
  :hints (("Goal" :induct (len d))
          ("Subgoal *1/1" :use ((:instance extends-trans (e k) (f (cdr d)))
	                        (:instance fixing-auto-fixes (phi x) (x (flift (primitive d) d k)))))))
                        
(local-defthmd comp-fixing-autos-2
  (implies (and (extensionp e k) (extensionp k f)
                (member x (fixing-autos k e f)))
           (equal (comp-embedding x (trivial-embedding k e f) k e f)
	          (trivial-embedding k e f)))
  :hints (("Goal" :use ((:instance comp-fixing-autos-1 (d k))))))

(local-defthmd comp-fixing-autos-3
  (implies (and (extensionp e k) (extensionp k f) (extensionp e d) (extensionp d k)
                (member x (fixing-autos k e f))
		(embeddingp y d e f)
		(equal (restrict-embedding y d k)
                       (trivial-embedding k e f)))
           (equal (restrict-embedding (comp-embedding x y d e f) d k)
	          (trivial-embedding k e f)))
  :hints (("Goal" :induct (fixing-auto-fixes-induct d y k))
          ("Subgoal *1/2" :in-theory (enable restrict-embedding)
	                  :use (comp-fixing-autos-2))
          ("Subgoal *1/1" :in-theory (enable cdr-nthcdr embeddingp restrict-embedding)
	                  :use ((:instance len-extends (e k) (f d))
			        (:instance len-extends (e (cdr d)) (f k))
			        (:instance extends-trans (f (cdr d)))))))

(defthm comp-fixing-autos
  (implies (and (extensionp e k) (extensionp k f)
                (member x (fixing-autos k e f))
                (member y (fixing-autos k e f)))
           (member (comp-auto x y e f) (fixing-autos k e f)))
  :hints (("Goal" :in-theory (e/d (comp-auto) (sublistp-fixing-autos))
                  :use (member-fixing-autos
		        (:instance comp-fixing-autos-3 (d e))
		        (:instance extends-trans (d k))
			(:instance embeddingp-comp-embedding (phi y) (psi x) (g e) (k e))
                        (:instance member-fixing-autos (x y))
                        (:instance member-fixing-autos (x (comp-auto x y e f)))))))

;; The proof of closure under the inverse operator similary requires 2 inductions.  Let x be a member of (fixing-autos k e f).
;; First we show, using fixing-auto-fixes, that if d is an intermediate field between k and f, then

;;     (inv-embedding-aux x e e d f) = (trivial-embedding d e f).

;; Using this result for the case d = k, we then show that if d is an intermediate field between e and k, then

;;    (restrict-embedding (inv-embedding-aux x e e d f) d k) = (trivial-embedding k e f).

;; The desired result is the case d = e:
                        
(defthmd inv-fixing-autos-1
  (implies (and (extensionp e k) (extensionp k f) (extensionp k d) (extensionp d f)
                (member x (fixing-autos k e f)))
           (equal (inv-embedding-aux x e e d f)
	          (trivial-embedding d e f)))
  :hints (("Goal" :induct (len d))
          ("Subgoal *1/1" :in-theory (e/d (autop) (SUBLISTP-FIXING-AUTOS))
	                  :use (member-fixing-autos
	                        (:instance extends-trans (e k) (f (cdr d)))
	                        (:instance extends-trans (d k) (f d))
	                        (:instance extends-trans (d k))
				(:instance preembed-embed (x (flift (primitive d) d e)) (phi x) (k e))
	                        (:instance fixing-auto-fixes (phi x) (x (flift (primitive d) d k)))))))

(local-defthmd inv-fixing-autos-2
  (implies (and (extensionp e k) (extensionp k f)
                (member x (fixing-autos k e f)))
           (equal (inv-embedding-aux x e e k f)
	          (trivial-embedding k e f)))
  :hints (("Goal" :use ((:instance inv-fixing-autos-1 (d k))))))

(local-defthmd inv-fixing-autos-3
  (implies (and (extensionp e k) (extensionp k f) (extensionp e d) (extensionp d k)
                (member x (fixing-autos k e f)))
	   (equal (restrict-embedding (inv-embedding-aux x e e d f) d k)
	          (trivial-embedding k e f)))
  :hints (("Goal" :induct (len d))
          ("Subgoal *1/2" :in-theory (enable restrict-embedding))
          ("Subgoal *1/1" :in-theory (enable cdr-nthcdr restrict-embedding)
	                  :use (inv-fixing-autos-2
			        (:instance len-extends (e k) (f d))
			        (:instance len-extends (e (cdr d)) (f k))
			        (:instance extends-trans (f (cdr d)))))))

(local-defthmd inv-fixing-autos-4
  (implies (and (extensionp e k) (extensionp k f)
                (member x (fixing-autos k e f)))
	   (equal (restrict-embedding (inv-auto x e f) e k)
	          (trivial-embedding k e f)))
  :hints (("Goal" :in-theory (enable inv-auto inv-embedding)
                  :use ((:instance inv-fixing-autos-3 (d e))))))

(defthm inv-fixing-autos
  (implies (and (extensionp e k) (extensionp k f)
                (member x (fixing-autos k e f)))
	   (member (inv-auto x e f) (fixing-autos k e f)))
  :hints (("Goal" :in-theory (disable SUBLISTP-FIXING-AUTOS)
                  :use (inv-fixing-autos-4 member-fixing-autos
		        (:instance extends-trans (d k))
                        (:instance member-fixing-autos (x (inv-auto x e f)))))))
			
(defthm member-fixing-autos-auto-list
  (implies (and (extensionp e f) (member x (fixing-autos k e f)))
           (and (autop x e f)
	        (member x (auto-list e f))))
  :hints (("Goal" :use (member-fixing-autos))))

(in-theory (disable comp-auto))

;; The following now succeeds automatically:

(defsubgroup galois-subgroup (k e f) (galois e f)
  (and (extensionp e k) (extensionp k f) (extensionp e f) (galoisp e f))
  (fixing-autos k e f))

;;----------------------------------------------------

;; Let h = (galois-subgroup k e f).  According to the lemma autop-trunc-embedding, we have a
;; map from h to (galois e k):

(defmap galois-subgroup-map (k e f)
  (fixing-autos k e f)
  (trunc-embedding x e k))

;; To prove that this is a homomorphism, we first observe that (id-auto e f) is mapped to (id-auto e k):

(local-defthmd trunc-trivial-embedding
  (implies (and (extensionp e k) (extensionp k f) (extensionp e d) (extensionp d k))
           (equal (trunc-embedding (trivial-embedding d e f) d k)
	          (trivial-embedding d e k)))
  :hints (("Goal" :induct (len d))
          ("Subgoal *1/2" :expand ((TRUNC-EMBEDDING NIL D D)))
	  ("Subgoal *1/1" :in-theory (enable trunc-embedding)
	                  :use ((:instance extends-trans (f (cdr d)))
			        (:instance extends-trans (e (cdr d)) (d k))
			        (:instance len-extends (e k) (f d))
			        (:instance len-extends (e (cdr d)) (f k))))))

(defthm trunc-embedding-id-auto
  (implies (and (extensionp e k) (extensionp k f))
           (equal (trunc-embedding (id-auto e f) e k)
	          (id-auto e k)))
  :hints (("Goal" :in-theory (enable id-auto id-embedding)
                  :use ((:instance trunc-trivial-embedding (d e))))))

;; To prove that the group operation is preserved, we note first that if x and y are in h and a is an
;; element of e, then by autop-trunc-embedding and embeddingp-comp-embedding,

;;    (embed a (comp-embedding (trunc-embedding x e k) (trunc-embedding y e k) e e k) e k)
;;      = (embed (embed a (trunc-embedding y e k) e k) (trunc-embedding x e k) e k)
;;      = (embed (embed a y e f) (trunc-embedding x e k) e k)
;;      = (embed (embed a y e f) x e f)
;;      = (embed a (comp-embedding x y e e f) e f)
;;      = (embed a (trunc-embedding (comp-embedding x y e e f) e k) e k)

(in-theory (disable sublistp-fixing-autos))

(local-defthmd trunc-embedding-comp-auto-1
  (implies (and (extensionp e k) (extensionp k f)
                (member x (fixing-autos k e f))
                (member y (fixing-autos k e f)))
	   (and (embeddingp (comp-embedding (trunc-embedding x e k) (trunc-embedding y e k) e e k) e e k)
	        (embeddingp (trunc-embedding (comp-embedding x y e e f) e k) e e k)))
  :hints (("Goal" :in-theory (e/d (comp-auto) (comp-fixing-autos))
                  :use (member-fixing-autos comp-fixing-autos
                        (:instance member-fixing-autos (x y))
                        (:instance member-fixing-autos (x (comp-embedding x y e e f)))
			(:instance extends-trans (d k))
			(:instance autop-trunc-embedding (x (embed a y e f)) (d k) (phi x))
			(:instance autop-trunc-embedding (x a) (d k) (phi y))
			(:instance autop-trunc-embedding (x a) (d k) (phi (comp-embedding x y e e f)))
			(:instance embeddingp-comp-embedding (psi x) (phi y) (x a) (g e) (k e))
			(:instance embeddingp-comp-embedding (psi (trunc-embedding x e k)) (phi (trunc-embedding y e k))
			                                     (x a) (g e) (k e) (f k))))))

(local-defthmd trunc-embedding-comp-auto-2
  (implies (and (extensionp e k) (extensionp k f)
                (member x (fixing-autos k e f))
                (member y (fixing-autos k e f))
		(feltp a e))
	   (equal (embed a (comp-embedding (trunc-embedding x e k) (trunc-embedding y e k) e e k) e k)
	          (embed a (trunc-embedding (comp-embedding x y e e f) e k) e k)))
  :hints (("Goal" :in-theory (e/d (comp-auto) (comp-fixing-autos))
                  :use (member-fixing-autos comp-fixing-autos
                        (:instance member-fixing-autos (x y))
                        (:instance member-fixing-autos (x (comp-embedding x y e e f)))
			(:instance extends-trans (d k))
			(:instance autop-trunc-embedding (x (embed a y e f)) (d k) (phi x))
			(:instance autop-trunc-embedding (x a) (d k) (phi y))
			(:instance autop-trunc-embedding (x a) (d k) (phi (comp-embedding x y e e f)))
			(:instance embeddingp-comp-embedding (psi x) (phi y) (x a) (g e) (k e))
			(:instance embeddingp-comp-embedding (psi (trunc-embedding x e k)) (phi (trunc-embedding y e k))
			                                     (x a) (g e) (k e) (f k))))))

;; and we appeal to embed-cex-lemma:

(defthm trunc-embedding-comp-auto
  (implies (and (extensionp e k) (extensionp k f)
                (member x (fixing-autos k e f))
                (member y (fixing-autos k e f)))
	   (equal (trunc-embedding (comp-auto x y e f) e k)
	          (comp-auto (trunc-embedding x e k) (trunc-embedding y e k) e k)))
  :hints (("Goal" :in-theory (enable comp-auto)
                  :use (trunc-embedding-comp-auto-1
                        (:instance embed-cex-lemma (phi (comp-embedding (trunc-embedding x e k) (trunc-embedding y e k) e e k))
                                                   (psi (trunc-embedding (comp-embedding x y e e f) e k))
						   (k e) (f k))
			(:instance trunc-embedding-comp-auto-2
			  (a (embed-cex (comp-embedding (trunc-embedding x e k) (trunc-embedding y e k) e e k)
			                (trunc-embedding (comp-embedding x y e e f) e k)
					e k)))))))

;; Similarly,

;;    (embed a (comp-auto (trunc-embedding (inv-auto x e f) e k) (trunc-embedding x e k) e k) e k)
;;      = (embed (embed a (trunc-embedding x e k) e k) (trunc-embedding (inv-auto x e f) e k) e k)
;;      = (embed (embed a x e f) (trunc-embedding (inv-auto x e f) e k) e k)
;;      = (embed (embed a x e f) (inv-auto x e f) e f)
;;      = (embed a (comp-auto x (inv-auto x e f) e f) e f)
;;      = (embed a (id-auto e f) e f)
;;      = a

;; which implies

;;    (comp-auto (trunc-embedding (inv-auto x e f) e k) (trunc-embedding x e k) e k) = (id-auto e k),

;; and therefore (trunc-embedding (inv-auto x e f) e k) = (inv-auto (trunc-embedding x e k) e k):

(local-defthmd trunc-embedding-inv-auto-1
  (implies (and (extensionp e k) (extensionp k f)
                (member x (fixing-autos k e f)))
	   (embeddingp (comp-auto (trunc-embedding (inv-auto x e f) e k)
	                          (trunc-embedding x e k)
				  e k)
		       e e k))
  :hints (("Goal" :in-theory (e/d (comp-auto) (comp-inv-auto comp-fixing-autos inv-fixing-autos))
                  :use (member-fixing-autos inv-fixing-autos
		        (:instance member-fixing-autos (x (inv-auto x e f)))
			(:instance extends-trans (d k))
			(:instance comp-inv-auto (a x))
			(:instance autop-trunc-embedding (x (embed a x e f)) (d k) (phi (inv-auto x e f)))
			(:instance autop-trunc-embedding (x a) (d k) (phi x))
			(:instance embeddingp-comp-embedding (x a) (psi (inv-auto x e f)) (phi x) (g e) (k e))
			(:instance embeddingp-comp-embedding (psi (trunc-embedding (inv-auto x e f) e k))
			                                     (phi (trunc-embedding x e k))
			                                     (x a) (g e) (k e) (f k))))))

(local-defthmd trunc-embedding-inv-auto-2
  (implies (and (extensionp e k) (extensionp k f)
                (member x (fixing-autos k e f))
		(feltp a e))
	   (equal (embed a (comp-auto (trunc-embedding (inv-auto x e f) e k)
	                              (trunc-embedding x e k)
				      e k)
		           e k)
		  a))
  :hints (("Goal" :in-theory (e/d (comp-auto) (comp-inv-auto comp-fixing-autos inv-fixing-autos))
                  :use (member-fixing-autos inv-fixing-autos
		        (:instance member-fixing-autos (x (inv-auto x e f)))
			(:instance extends-trans (d k))
			(:instance comp-inv-auto (a x))
			(:instance autop-trunc-embedding (x (embed a x e f)) (d k) (phi (inv-auto x e f)))
			(:instance autop-trunc-embedding (x a) (d k) (phi x))
			(:instance embeddingp-comp-embedding (x a) (psi (inv-auto x e f)) (phi x) (g e) (k e))
			(:instance embeddingp-comp-embedding (psi (trunc-embedding (inv-auto x e f) e k))
			                                     (phi (trunc-embedding x e k))
			                                     (x a) (g e) (k e) (f k))))))

(local-defthmd trunc-embedding-inv-auto-3
  (implies (and (extensionp e k) (extensionp k f)
                (member x (fixing-autos k e f)))
	   (equal (comp-auto (trunc-embedding (inv-auto x e f) e k)
	                     (trunc-embedding x e k)
		             e k)
		  (id-auto e k)))
  :hints (("Goal" :in-theory (enable comp-auto)
                  :use (trunc-embedding-inv-auto-1
                        (:instance embed-cex-lemma (phi (comp-auto (trunc-embedding (inv-auto x e f) e k)
			                                           (trunc-embedding x e k)
								   e k))
                                                   (psi (id-auto e k))
						   (k e) (f k))
			(:instance trunc-embedding-inv-auto-2
			  (a (embed-cex (comp-auto (trunc-embedding (inv-auto x e f) e k)
			                           (trunc-embedding x e k)
				                   e k)
					(id-auto e k)			                
					e k)))))))

(defthm trunc-embedding-inv-auto
  (implies (and (extensionp e k) (extensionp k f)
                (member x (fixing-autos k e f)))
           (equal (trunc-embedding (inv-auto x e f) e k)
	          (inv-auto (trunc-embedding x e k) e k)))
  :hints (("Goal" :in-theory (enable e)
                  :use (trunc-embedding-inv-auto-3 member-fixing-autos
                        (:instance member-fixing-autos (x (inv-auto x e f)))
                        (:instance autop-trunc-embedding (d k) (phi x))
                        (:instance autop-trunc-embedding (d k) (phi (INV-AUTO X E F)))
			(:instance extends-trans (d k))
                        (:instance inv-unique (g (autos e k))
			                      (x (trunc-embedding x e k))
					      (y (TRUNC-EMBEDDING (INV-AUTO X E F) E K)))))))

(in-theory (disable autop))

(in-theory (enable e))

(defthm autop-trunc-embedding-rewrite
  (implies (and (member x (fixing-autos k e f))
                (extensionp e k) (extensionp k f))                
	   (autop (trunc-embedding x e k) e k))
  :hints (("Goal" :use (member-fixing-autos
                        (:instance extends-trans (d k))
                        (:instance autop-trunc-embedding (d k) (phi x))))))

(defthm member-id-auto-fixing-autos
  (implies (and (extensionp e k) (extensionp k f))
           (member (id-auto e f) (fixing-autos k e f)))
  :hints (("Goal" :use ((:instance member-fixing-autos (x (id-auto e f)))))))

;; The following is now proved automatically:

(prove-homomorphismp galois-subgroup-map
  (galois-subgroup-map k e f)
  (galois-subgroup k e f)
  (galois e k)
  (and (extensionp e k) (extensionp k f) (extensionp e f) (galoisp e f)))

(DEFTHM HOMOMORPHISMP-GALOIS-SUBGROUP-MAP
  (IMPLIES (AND (EXTENSIONP E K)
                (EXTENSIONP K F)
                (EXTENSIONP E F)
                (GALOISP E F))
           (HOMOMORPHISMP (GALOIS-SUBGROUP-MAP K E F)
                          (GALOIS-SUBGROUP K E F)
                          (GALOIS E K))))

;; If x is in (fixing-autos k e f) and (trunc-embedding x d k) = (trivial-embedding d e k), then
;; x = (trivial-embedding d e f).  Thus, galois-subgroup-map is an endomorphism:

(local-defthmd galois-subgroup-map-1
  (implies (and (extensionp e k) (extensionp k f)
                (extensionp e d) (extensionp d k)
		(embeddingp x d e f)
		(equal (restrict-embedding x d k)
		       (trivial-embedding k e f))
		(equal (trunc-embedding x d k)
		       (trivial-embedding d e k)))
	   (equal (trivial-embedding d e f)
	          x))
  :hints (("Goal" :induct (fixing-auto-fixes-induct d x k))
          ("Subgoal *1/2" :expand ((EMBEDDINGP X D E D) (RESTRICT-EMBEDDING X D D)))
	  ("Subgoal *1/1" :expand ((EMBEDDINGP X D E F) (RESTRICT-EMBEDDING X D K) (TRUNC-EMBEDDING X D K)
	                           (RESTRICT-EMBEDDING (CDR X) (CDR D) K) (TRUNC-EMBEDDING (CDR X) (CDR D) K))
	                  :use ((:instance extends-trans (f (cdr d)))
			        (:instance len-extends (e (cdr d)) (f k))
			        (:instance extends-trans (e (cdr d)) (d k))))))

(local-defthmd galois-subgroup-map-2
  (implies (and (extensionp e k) (extensionp k f)
		(member x (fixing-autos k e f))
		(equal (trunc-embedding x e k)
		       (id-auto e k)))
	   (equal (id-auto e f)
	          x))
  :hints (("Goal" :in-theory (enable id-embedding id-auto)
                  :use (member-fixing-autos
		        (:instance extends-trans (d k))
		        (:instance galois-subgroup-map-1 (d e))))))

(defthmd endomorphismp-galois-subgroup-map
  (implies (and (extensionp e k) (extensionp k f) (extensionp e f) (galoisp e f))
           (endomorphismp (galois-subgroup-map k e f)
                          (galois-subgroup k e f)
                          (galois e k)))
  :hints (("Goal" :use (homomorphismp-galois-subgroup-map
                        (:instance homomorphism-endomorphism (map (galois-subgroup-map k e f)) (g (galois-subgroup k e f)) (h (galois e k)))
			(:instance galois-subgroup-map-2 (x (cadr (kelts (galois-subgroup-map k e f) (galois-subgroup k e f) (galois e k)))))))))

;; To prove that galois-subgroup-map is an epimorphism, we need an inverse:

(defund extend-embedding (x k e f)
  (append x (trivial-embedding k e f)))

;; The following is a consequence of pembed-trunc-embedding:

(defthmd embeddingp-extend-embedding
  (implies (and (extensionp e k) (extensionp k f)
                (extensionp e d) (extensionp d k)
		(embeddingp x d e k))
           (and (embeddingp (extend-embedding x k e f) d e f)
	        (equal (restrict-embedding (extend-embedding x k e f) d k)
		       (trivial-embedding k e f))
		(equal (trunc-embedding (extend-embedding x k e f) d k)
		       x)))
  :hints (("Goal" :induct (fixing-auto-fixes-induct d x k))
          ("Subgoal *1/2" :in-theory (enable extend-embedding embeddingp restrict-embedding trunc-embedding)
		          :use ((:instance trivial-embedding-flift (e k) (k e))))	  
	  ("Subgoal *1/1" :in-theory (enable extend-embedding embeddingp restrict-embedding trunc-embedding)
	                  :use ((:instance extends-trans (f (cdr d)))
			        (:instance len-extends (e (cdr d)) (f k))
			        (:instance len-extends (e (cdr d)) (f d))
			        (:instance extends-trans (e (cdr d)) (d k))				
				(:instance pembed-trunc-embedding (phi (append (cdr x) (trivial-embedding k e f)))
				                                  (e (cdr d)) (p (car d)) (d k) (k e))))))

;; It follows from the case d = e that galois-subgroup-map is an epimorphism, and therefore an isomorphism:

(defthmd trunc-extend-embedding
  (implies (and (extensionp e k) (extensionp k f)
		(autop x e k))
           (and (member (extend-embedding x k e f) (fixing-autos k e f))
	        (equal (trunc-embedding (extend-embedding x k e f) e k)
	               x)))
  :hints (("Goal" :in-theory (enable autop)
                  :use ((:instance member-fixing-autos (x (extend-embedding x k e f)))
		        (:instance extends-trans (d k))
		        (:instance embeddingp-extend-embedding (d e))))))
  
(local-defthmd extend-embedding-3
  (implies (and (extensionp e k) (extensionp k f) (galoisp e f)
		(autop x e k))
	   (member x (ielts (galois-subgroup-map k e f) (galois-subgroup k e f) (galois e k))))
  :hints (("Goal" :use (trunc-extend-embedding homomorphismp-galois-subgroup-map member-fixing-autos
                        (:instance extends-trans (d k))
                        (:instance member-ielts (x (extend-embedding x k e f))
			                        (map (galois-subgroup-map k e f))
						(g (galois-subgroup k e f)) (h (galois e k)))))))

(local-defthmd extend-embedding-4
  (implies (and (extensionp e k) (extensionp k f) (galoisp e f))
	   (sublistp (auto-list e k)
	             (ielts (galois-subgroup-map k e f) (galois-subgroup k e f) (galois e k))))
  :hints (("Goal" :use ((:instance extends-trans (d k))
                        (:instance scex1-lemma (l (auto-list e k))
                                               (m (ielts (galois-subgroup-map k e f) (galois-subgroup k e f) (galois e k))))
                        (:instance extend-embedding-3
			            (x (scex1 (auto-list e k) (ielts (galois-subgroup-map k e f) (galois-subgroup k e f) (galois e k)))))))))

(defthmd epimorphismp-galois-subgroup-map
  (implies (and (extensionp e k) (extensionp k f) (galoisp e f))
           (epimorphismp (galois-subgroup-map k e f) (galois-subgroup k e f) (galois e k)))
  :hints (("Goal" :use (homomorphismp-galois-subgroup-map extend-embedding-4
                        (:instance extends-trans (d k))
			(:instance homomorphism-epimorphism (map (galois-subgroup-map k e f))
						            (g (galois-subgroup k e f)) (h (galois e k)))))))

(defthmd isomorphismp-galois-subgroup-map
  (implies (and (extensionp e k) (extensionp k f) (galoisp e f))
           (isomorphismp (galois-subgroup-map k e f)
			 (galois-subgroup k e f)
	                 (galois e k)))
  :hints (("Goal" :in-theory (enable isomorphismp)
                  :use (endomorphismp-galois-subgroup-map epimorphismp-galois-subgroup-map
		        (:instance extends-trans (d k))))))

;;----------------------------------------------------

;; A trivial consequence of the last result:

(defthmd order-galois-subgroup
  (implies (and (extensionp e k) (extensionp k f) (galoisp e f))
           (equal (order (galois-subgroup k e f))
	          (order (galois e k))))
  :hints (("Goal" :use (isomorphismp-galois-subgroup-map
                        (:instance isomorphism-equal-orders (map (galois-subgroup-map k e f)) (g (galois-subgroup k e f)) (h (galois e k)))))))

;; By lagrange, edegree-mult, and order-galois-group,

;;    (subgroup-index (galois-subgroup-map k e f) (galois e f)) = (order (galois e f)) / (order (galois e k))
;;                                                              = (edegree e f) / (edegree e k)
;;                                                              = (edegree e k).

(local-defthmd index-galois-subgroup-1
  (implies (and (extensionp e k) (extensionp k f) (galoisp e f))
           (equal (* (edegree e k) (subgroup-index (galois-subgroup k e f) (galois e f)))
	           (* (edegree e k) (edegree k f))))
  :hints (("Goal" :use (order-galois-subgroup edegree-mult subgroupp-galois-subgroup galoisp-subfield order-galois-group
                        (:instance lagrange (h (galois-subgroup k e f)) (g (galois e f)))
			(:instance extends-trans (d k))
			(:instance posp-edegree (f k))
			(:instance posp-edegree (e k))
			(:instance order-galois-group (f k))))))

(defthmd index-galois-subgroup
  (implies (and (extensionp e k) (extensionp k f) (galoisp e f))
           (equal (subgroup-index (galois-subgroup k e f) (galois e f))
	          (edegree k f)))
  :hints (("Goal" :in-theory (disable posp-edegree)
                  :use (index-galois-subgroup-1
			(:instance posp-edegree (e k))
			(:instance posp-edegree (f k))))))

;;----------------------------------------------------

;; Let x be an element of e.  Suppose x is lifted from k, i.e, x = (flift z k e), where z is in k.  Let phi be in 
;; (galois-subgroup k e f).  By autop-trunc-embedding and embed-fixes, (autop (trunc-embedding phi e k) e k) and

;;    (embed x phi e f) = (embed (fift z k e) (trunc-embedding phi e k) e k) = (flift x k e) = x.

(local-defthmd fixedp-galois-subgroup-1
  (implies (and (extensionp e k) (extensionp k f) (galoisp e f)
                (feltp z k) (member phi (fixing-autos k e f)))
	   (equal (embed (flift z k e) phi e f)
	          (flift z k e)))
  :hints (("Goal" :in-theory (enable autop)
                  :use ((:instance member-fixing-autos (x phi))
		        (:instance extends-trans (d k))
                        (:instance autop-trunc-embedding (d k) (x (flift z k e)))
			(:instance embed-fixes (k e) (f k) (phi (trunc-embedding phi e k)) (x z))))))

(local-defthmd fixedp-galois-subgroup-2
  (implies (and (extensionp e k) (extensionp k f) (galoisp e f)
                (feltp x e) (fliftedp x k e) (member phi (fixing-autos k e f)))
	   (equal (embed x phi e f)
	          x))
  :hints (("Goal" :use ((:instance flift-fdrop (f k))
                        (:instance fixedp-galois-subgroup-1 (z (fdrop x e k)))))))

(local-defthmd fixedp-galois-subgroup-3
  (implies (and (extensionp e k) (extensionp k f) (galoisp e f)
                (feltp x e) (fliftedp x k e) (sublistp l (fixing-autos k e f)))
	   (fixedp-aux x l e f))
  :hints (("Subgoal *1/3" :use ((:instance fixedp-galois-subgroup-2 (phi (car l)))))))

(local-defthmd fixedp-galois-subgroup-4
  (implies (and (extensionp e k) (extensionp k f) (galoisp e f)
                (feltp x e) (fliftedp x k e))
	   (fixedp x (galois-subgroup k e f) e f))
  :hints (("Goal" :in-theory (enable fixedp)
                  :use ((:instance extends-trans (d k))
		        (:instance fixedp-galois-subgroup-3 (l (fixing-autos k e f)))))))

;; Thus, (fixedp x (galois-subgroup k e f) e f).  On the other hand, suppose (fixedp x (galois-subgroup k e f) e f).
;; Given psi be in (galois e k), phi = (extend-embedding psi k e f).  By trunc-extend-embedding, autop-trunc-embedding,
;; and fixedp-embed

;;   (embed x psi e k) = (embed x (trunc-embedding phi e k) e f) = x.

;; Therefore, (fixedp x (galois e k) e k) and by galois-no-fixed-elt, x is lifted from k.  Thus, k is the fixed field 
;; of h in the following sense:

(in-theory (disable fixedp))

(local-defthmd fixedp-galois-subgroup-5
  (implies (and (extensionp e k) (extensionp k f) (galoisp e f) 
                (feltp x e) (fixedp x (galois-subgroup k e f) e f)
		(autop psi e k))
	   (equal (embed x psi e k) x))
  :hints (("Goal" :use ((:instance extends-trans (d k))
                        (:instance trunc-extend-embedding (x psi))
			(:instance member-fixing-autos (x (extend-embedding psi k e f)))
			(:instance autop-trunc-embedding (d k) (phi (extend-embedding psi k e f)))
			(:instance fixedp-embed (h (galois-subgroup k e f)) (phi (extend-embedding psi k e f)))))))

(local-defthmd fixedp-galois-subgroup-6
  (implies (and (extensionp e k) (extensionp k f) (galoisp e f) 
                (feltp x e) (fixedp x (galois-subgroup k e f) e f)
		(sublistp l (auto-list e k)))
	   (fixedp-aux x l e k))	   
  :hints (("Subgoal *1/3" :use ((:instance fixedp-galois-subgroup-5 (psi (car l)))))))

(local-defthmd fixedp-galois-subgroup-7
  (implies (and (extensionp e k) (extensionp k f) (galoisp e f) 
                 (feltp x e) (fixedp x (galois-subgroup k e f) e f))
	   (fixedp x (galois e k) e k))
  :hints (("Goal" :in-theory (enable fixedp)
                  :use ((:instance extends-trans (d k))
		        (:instance fixedp-galois-subgroup-6 (l (auto-list e k)))))))

(local-defthmd fixedp-galois-subgroup-8
  (implies (and (extensionp e k) (extensionp k f) (galoisp e f) 
                (feltp x e) (fixedp x (galois-subgroup k e f) e f))
	   (fliftedp x k e))
  :hints (("Goal" :use (fixedp-galois-subgroup-7 galoisp-subfield
                        (:instance galois-no-fixed-elt (a x) (f k))))))

(local-defthmd fixedp-galois-subgroup-9
  (implies (and (extensionp e k) (extensionp k f) (galoisp e f) 
                (feltp x e))
	   (iff (fixedp x (galois-subgroup k e f) e f)
	       (fliftedp x k e)))
  :hints (("Goal" :use (fixedp-galois-subgroup-4 fixedp-galois-subgroup-8))))

(defun-sk fixed-field-p (k h e f)
  (forall (x)
    (implies (feltp x e)
             (iff (fixedp x h e f)
	          (fliftedp x k e)))))

(defthmd fixed-field-p-lemma
  (implies (and (fixed-field-p k h e f) (feltp x e))
           (iff (fixedp x h e f)
	        (fliftedp x k e)))
  :hints (("Goal" :use (fixed-field-p-necc))))

(defthmd galois-subgroup-fixed-field-p
  (implies (and (extensionp e k) (extensionp k f) (galoisp e f))
           (fixed-field-p k (galois-subgroup k e f) e f))
  :hints (("Goal" :use ((:instance fixedp-galois-subgroup-9 (x (fixed-field-p-witness k (galois-subgroup k e f) e f)))))))

;;---------------------------------------------------

;; We shall show that h is a normal subgroup of g <=> k is a normal extension of f and that in the normal
;; case, (galois k f) is isomorphic to the quotient group of h in (galois e f).

;; First we assume that k is not a normal extension and show that h is not a normal subgroup. There exists 
;; an element x of k such that (plift (min-poly x k f) f k) does not split in k.  Let m = (min-poly x k f) 
;; and m' = (plift m f k).  By len-proots-<=-len-factorization and len-factorization-bound, 

;;    (len (proots m' k)) <= (len (factorization m' k)) < (degree m') = (degree m).

;; Let x' = (flift x k e).  By min-poly-flift-min-poly, m = (min-poly x' e f).  Let m" = (plift m' k e) =
;; (plift m f e).  Since e is normal over f, m" splits in e.  By len-proots-max,

;;    (len (proots m" e)) = (degree m) > (len (proots m' k)).

;; It follows that m" has a root that is not flifted from k.  To prove this, let y be a member of (proots m" e)
;; that is not a member of (plift (proots m' k) k e).  If y = (flift z k e), then we have

;;    (prootp (flift z k e) m" e) => (peval m" (flift z k e) e) = 0
;;                                => (flift (peval m' z k) k e) = 0
;;                                => (peval m' z k) = 0
;;                                => (prootp z m' k)
;;                                => z is a member of (proots m' k)
;;                                => (flift z k e) is a member of (plift (proots m' k) k e)

;; a contradiction.

;; By galois-no-fixed-elt, y is not fixed by (galois e k).  It follows from autop-trunc-embedding that there
;; exists an element phi of h such that (embed y phi e f) != y.

;; By roots-auto-lemma, there exists an element psi of g such that (embed y psi e f) = x'.
;; Let rho be the conjugate of phi by psi:

;;    rho = (conj phi psi g) = (comp-auto (comp-auto psi phi e f) (inv-auto psi e f) e f).

;; Let z = (embed y phi e f).  Since z != y, (embed z psi e f) != x' and hence

;;    (embed x' rho e f) = (embed (embed (embed x' (inv-auto psi e f) e f) phi e f) psi e f)
;;                       = (embed (embed y phi e f) psi e f)
;;                       = (embed z psi e f)
;;                      != x'.

;; By fixing-auto-fixes, rho is not in h, and therefore h is not normal in g.

(local-defthmd ngsne-1
  (implies (and (extensionp e k) (extensionp k f) (galoisp e f) (not (normal-extension-p k f)))
           (let ((x (normal-extension-p-witness k f)))
             (and (feltp x k)
	          (not (splits (plift (min-poly x k f) f k) k)))))
  :hints (("Goal" :use ((:instance normal-extension-p-witness-lemma (e k))))))

(local-defthmd ngsne-2
  (implies (and (extensionp e k) (extensionp k f) (galoisp e f) (not (normal-extension-p k f)))
           (let* ((x (normal-extension-p-witness k f))
	          (m (min-poly x k f))
		  (m1 (plift m f k)))
             (and (feltp x k)
	          (< (len (proots m1 k)) (degree m)))))
  :hints (("Goal" :in-theory (enable splits)
                  :use (ngsne-1
                        (:instance len-factorization-bound (p (plift (min-poly (normal-extension-p-witness k f) k f) f k)) (f k))
			(:instance prootp-min-poly (x (normal-extension-p-witness k f)) (e k))
			(:instance len-proots-<=-len-factorization (p (plift (min-poly (normal-extension-p-witness k f) k f) f k)) (f k))))))

(local-defthmd ngsne-3
  (implies (and (extensionp e k) (extensionp k f) (galoisp e f) (not (normal-extension-p k f)))
           (let* ((x (normal-extension-p-witness k f))
	          (x1 (flift x k e))
	          (m (min-poly x k f))
		  (m1 (plift m f k))
		  (m2 (plift m1 k e)))
	     (and (feltp x1 e)
	          (equal m (min-poly x1 e f))
		  (equal m2 (plift m f e))
                  (splits m2 e))))
  :hints (("Goal" :use (ngsne-2 galois-normal-separable
                        (:instance extends-trans (d k))
                        (:instance min-poly-flift-min-poly (d k) (x (normal-extension-p-witness k f)))
			(:instance normal-extension-p-lemma (x (flift (normal-extension-p-witness k f) k e)))))))

(local-defthmd ngsne-4
  (implies (and (extensionp e k) (extensionp k f) (galoisp e f) (not (normal-extension-p k f)))
           (let* ((x (normal-extension-p-witness k f))
	          (m (min-poly x k f))
		  (m1 (plift m f k))
		  (m2 (plift m1 k e)))
	     (> (len (proots m2 e)) 
                (len (proots m1 k)))))
  :hints (("Goal" :use (ngsne-2 ngsne-3 galois-normal-separable
                        (:instance extends-trans (d k))
			(:instance prootp-min-poly (x (normal-extension-p-witness k f)) (e k))
			(:instance separable-extension-p-lemma (x (flift (normal-extension-p-witness k f) k e)))
			(:instance separablep-extension (p (min-poly (normal-extension-p-witness k f) k f)))
                        (:instance len-proots-max (p (plift (min-poly (normal-extension-p-witness k f) k f) f e)) (f e))))))

(local-defthmd ngsne-5
  (implies (and (extensionp e k) (extensionp k f) (galoisp e f) (not (normal-extension-p k f)))
           (let* ((x (normal-extension-p-witness k f))
	          (m (min-poly x k f))
		  (m1 (plift m f k))
		  (m2 (plift m1 k e)))
	     (implies (and (feltp z k) (prootp (flift z k e) m2 e))
	              (prootp z m1 k))))
  :hints (("Goal" :in-theory (enable prootp)
                  :use (ngsne-1
		        (:instance flift-peval (x z) (f k) (p (plift (min-poly (normal-extension-p-witness k f) k f) f k)))
                        (:instance extends-trans (d k))
			(:instance prootp-min-poly (x (normal-extension-p-witness k f)) (e k))
                        (:instance flift-fzero (f k) (x (peval (plift (min-poly (normal-extension-p-witness k f) k f) f k) z k)))))))

(local-defthmd ngsne-6
  (implies (and (extensionp e k) (extensionp k f) (galoisp e f) (not (normal-extension-p k f)))
           (let* ((x (normal-extension-p-witness k f))
	          (m (min-poly x k f))
		  (m1 (plift m f k))
		  (m2 (plift m1 k e)))
	     (implies (and (feltp z k) (member (flift z k e) (proots m2 e)))
	              (member z (proots m1 k)))))
  :hints (("Goal" :in-theory (enable prootp)
                  :use (ngsne-1 ngsne-5
		        (:instance member-proots (x z) (f k) (p (plift (min-poly (normal-extension-p-witness k f) k f) f k)))
		        (:instance member-proots (x (flift z k e)) (f e) (p (plift (min-poly (normal-extension-p-witness k f) k f) f e)))
                        (:instance extends-trans (d k))
			(:instance prootp-min-poly (x (normal-extension-p-witness k f)) (e k))))))

(local-defthmd ngsne-7
  (implies (member z l)
           (member (flift z k e) (plift l k e))))

(local-defthmd ngsne-8
  (implies (and (extensionp e k) (extensionp k f) (galoisp e f) (not (normal-extension-p k f)))
           (let* ((x (normal-extension-p-witness k f))
	          (m (min-poly x k f))
		  (m1 (plift m f k))
		  (m2 (plift m1 k e)))
	     (implies (and (feltp z k) (member (flift z k e) (proots m2 e)))
	              (member (flift z k e) (plift (proots m1 k) k e)))))
  :hints (("Goal" :use (ngsne-6 (:instance ngsne-7 (l (proots (plift (min-poly (normal-extension-p-witness k f) k f) f k) k)))))))

(local-defthmd ngsne-9
  (implies (and (extensionp e k) (extensionp k f) (galoisp e f) (not (normal-extension-p k f)))
           (let* ((x (normal-extension-p-witness k f))
	          (m (min-poly x k f))
		  (m1 (plift m f k))
		  (m2 (plift m1 k e))
		  (y (scex1 (proots m2 e) (plift (proots m1 k) k e))))
	     (and (member y (proots m2 e))
	          (not (member y (plift (proots m1 k) k e))))))
  :hints (("Goal" :use (ngsne-4
                        (:instance scex1-lemma (l (proots (plift (min-poly (normal-extension-p-witness k f) k f) f e) e))
			                       (m (plift (proots (plift (min-poly (normal-extension-p-witness k f) k f) f k) k) k e)))
                        (:instance sublistp-<=-len (l (proots (plift (min-poly (normal-extension-p-witness k f) k f) f e) e))
			                           (m (plift (proots (plift (min-poly (normal-extension-p-witness k f) k f) f k) k) k e)))))))

(local-defthmd ngsne-10
  (implies (and (extensionp e k) (extensionp k f) (galoisp e f) (not (normal-extension-p k f)))
           (let* ((x (normal-extension-p-witness k f))
	          (m (min-poly x k f))
		  (m1 (plift m f k))
		  (m2 (plift m1 k e))
		  (y (scex1 (proots m2 e) (plift (proots m1 k) k e))))
	     (and (prootp y m2 e)
	          (feltp y e))))
  :hints (("Goal" :in-theory (enable prootp)
                  :use (ngsne-9 ngsne-1
                        (:instance extends-trans (d k))
                        (:instance member-proots (x (scex1 (proots (plift (min-poly (normal-extension-p-witness k f) k f) f e) e)
			                                   (plift (proots (plift (min-poly (normal-extension-p-witness k f) k f) f k) k) k e)))
					         (f e) (p (plift (min-poly (normal-extension-p-witness k f) k f) f e)))
                        (:instance prootp-min-poly (x (normal-extension-p-witness k f)) (e k))))))

(local-defthmd ngsne-11
  (implies (and (extensionp e k) (extensionp k f) (galoisp e f) (not (normal-extension-p k f)))
           (let* ((x (normal-extension-p-witness k f))
	          (m (min-poly x k f))
		  (m1 (plift m f k))
		  (m2 (plift m1 k e))
		  (y (scex1 (proots m2 e) (plift (proots m1 k) k e))))
	     (and (prootp y m2 e)
	          (not (fliftedp y k e)))))
  :hints (("Goal" :use (ngsne-9 ngsne-10
                        (:instance ngsne-8 (z (fdrop (scex1 (proots (plift (min-poly (normal-extension-p-witness k f) k f) f e) e)
			                                    (plift (proots (plift (min-poly (normal-extension-p-witness k f) k f) f k) k) k e))
						     e k)))
                        (:instance flift-fdrop (f k) (x (scex1 (proots (plift (min-poly (normal-extension-p-witness k f) k f) f e) e)
			                                       (plift (proots (plift (min-poly (normal-extension-p-witness k f) k f) f k) k) k e))))))))

(local-defund p% (k f)
  (min-poly (normal-extension-p-witness k f) k f))

(local-defund x% (e k f)
  (flift (normal-extension-p-witness k f) k e))
 
(local-defund y% (e k f)
  (scex1 (proots (plift (min-poly (normal-extension-p-witness k f) k f) f e) e)
         (plift (proots (plift (min-poly (normal-extension-p-witness k f) k f) f k) k) k e)))

(local-defthmd ngsne-12
  (implies (and (extensionp e k) (extensionp k f) (galoisp e f) (not (normal-extension-p k f)))
           (and (feltp (x% e k f) e)
	        (feltp (y% e k f) e)
		(fliftedp (x% e k f) k e)
		(not (fliftedp (y% e k f) k e))
		(equal (p% k f) (min-poly (x% e k f) e f))
		(prootp (y% e k f) (plift (p% k f) f e) e)))
  :hints (("Goal" :in-theory (enable p% x% y%)
                  :use (ngsne-1 ngsne-10 ngsne-11
                        (:instance min-poly-flift-min-poly (d k) (x (normal-extension-p-witness k f)))))))

(local-defthmd ngsne-13
  (implies (and (extensionp e k) (extensionp k f) (galoisp e f) (not (normal-extension-p k f)))
           (equal (p% k f) (min-poly (y% e k f) e f)))
  :hints (("Goal" :use (ngsne-12
                        (:instance extends-trans (d k))
                        (:instance prootp-min-poly (x (x% e k f)))
                        (:instance prootp-min-poly (x (y% e k f)))
			(:instance min-poly-pdivides (x (y% e k f)) (q (p% k f)))
			(:instance irreduciblep-pdivides-monic-equal (x (min-poly (y% e k f) e f)) (y (p% k f)))))))

(local-defthmd ngsne-14
  (implies (and (extensionp e k) (extensionp k f) (galoisp e f) (not (normal-extension-p k f)))
           (not (fliftedp (x% e k f) f e)))
  :hints (("Goal" :in-theory (enable p% fliftedp)
                  :use (ngsne-12 ngsne-1
		        (:instance linear-splits (p (plift (p% k f) f k)) (f k))))))

(local-defthmd ngsne-15
  (implies (and (extensionp e k) (extensionp k f) (galoisp e f) (not (normal-extension-p k f)))
           (not (equal e k)))
  :hints (("Goal" :use (galois-equivalence))))

(local-defund phi1% (e k f)
  (fixedp-cex (y% e k f) (galois e k) e k))

(local-defthmd ngsne-16
  (implies (and (extensionp e k) (extensionp k f) (galoisp e f) (not (normal-extension-p k f)))
           (and (autop (phi1% e k f) e k)
	        (not (equal (embed (y% e k f) (phi1% e k f) e k) (y% e k f)))))
  :hints (("Goal" :in-theory (enable phi1%)
                  :use (ngsne-12 ngsne-15 galoisp-subfield
                        (:instance galois-no-fixed-elt (f k) (a (y% e k f)))
                        (:instance fixedp-cex-lemma (x (y% e k f)) (h (galois e k)) (f k))))))

(local-defund phi2% (e k f)
  (extend-embedding (phi1% e k f) k e f))

(local-defthmd ngsne-17
  (implies (and (extensionp e k) (extensionp k f) (galoisp e f) (not (normal-extension-p k f)))
           (and (autop (phi2% e k f) e f)
	        (in (phi2% e k f) (galois-subgroup k e f))
	        (not (equal (embed (y% e k f) (phi2% e k f) e f) (y% e k f)))))
  :hints (("Goal" :in-theory (enable phi2%)
                  :use (ngsne-16 ngsne-12
                        (:instance extends-trans (d k))
                        (:instance trunc-extend-embedding (x (phi1% e k f)))
			(:instance member-fixing-autos (x (phi2% e k f)))
			(:instance autop-trunc-embedding (d k) (x (y% e k f)) (phi (phi2% e k f)))))))

(local-defthmd ngsne-18
  (implies (and (extensionp e k) (extensionp k f) (galoisp e f) (not (normal-extension-p k f)))
           (not (fliftedp (y% e k f) f e)))
  :hints (("Goal" :in-theory (enable p% fliftedp)
                  :use (ngsne-1 ngsne-12 ngsne-13
		        (:instance linear-splits (p (plift (p% k f) f k)) (f k))))))

(local-defund phi3% (e k f)
  (roots-auto (y% e k f) (x% e k f) (galoisp-witness e f) e f))

(local-defthmd ngsne-19
  (implies (and (extensionp e k) (extensionp k f) (galoisp e f) (not (normal-extension-p k f)))
           (not (equal e f)))
  :hints (("Goal" :use (ngsne-15
                        (:instance extends-trans (d k))
			(:instance len-extends (e (cdr e)) (f k))
			(:instance len-extends (e (cdr k)) (f e)))
		  :expand ((extends e k) (extends k e)))))

(local-defthmd ngsne-20
  (implies (and (extensionp e k) (extensionp k f) (galoisp e f) (not (normal-extension-p k f)))
           (and (autop (phi3% e k f) e f)
	        (equal (embed (y% e k f) (phi3% e k f) e f)
		       (x% e k f))))
  :hints (("Goal" :in-theory (enable phi3%)
                  :use (ngsne-12 ngsne-13 ngsne-14 ngsne-15 ngsne-18 ngsne-19 galoisp
                        (:instance extends-trans (d k))
		        (:instance roots-auto-lemma (a (y% e k f)) (a1 (x% e k f)) (p (galoisp-witness e f)))))))

(local-defthmd ngsne-21
  (implies (and (extensionp e k) (extensionp k f) (galoisp e f) (not (normal-extension-p k f)))
           (and (autop (phi3% e k f) e f)
	        (equal (embed (x% e k f) (inv-auto (phi3% e k f) e f) e f)
		       (y% e k f))))
  :hints (("Goal" :in-theory (enable inv-auto)
                  :use (ngsne-12 ngsne-20
                        (:instance extends-trans (d k))
                        (:instance embed-embedding-inv (x (y% e k f)) (k e) (phi (phi3% e k f)))))))

(local-defthmd ngsne-22
  (implies (and (extensionp e k) (extensionp k f) (galoisp e f) (not (normal-extension-p k f)))
           (not (equal (embed (embed (y% e k f) (phi2% e k f) e f) (phi3% e k f) e f) (x% e k f))))
  :hints (("Goal" :in-theory (enable autop)
                  :use (ngsne-12 ngsne-20 ngsne-17
                        (:instance extends-trans (d k))
                        (:instance embedding-1-1 (k e) (phi (phi3% e k f)) (x (y% e k f)) (y (embed (y% e k f) (phi2% e k f) e f)))))))

(local-defund rho% (e k f)
  (conj (phi2% e k f) (phi3% e k f) (galois e f)))

(local-defthmd ngsne-23
  (implies (and (extensionp e k) (extensionp k f) (galoisp e f) (not (normal-extension-p k f)))
           (equal (embed (x% e k f) (rho% e k f) e f)
	          (embed (embed (embed (x% e k f) (inv-auto (phi3% e k f) e f) e f) (phi2% e k f) e f) (phi3% e k f) e f)))
  :hints (("Goal" :in-theory (enable inv-auto conj rho% autop)
                  :use (ngsne-12 ngsne-20 ngsne-17
                        (:instance extends-trans (d k))
		        (:instance embeddingp-inv-embedding (k e) (phi (phi3% e k f)))
			(:instance embeddingp-comp-embedding (psi (comp-embedding (phi3% e k f) (phi2% e k f) e e f))
			                                     (phi (inv-auto (phi3% e k f) e f))
							     (k e) (x (x% e k f)))
			(:instance embeddingp-comp-embedding (psi (phi3% e k f)) (phi (phi2% e k f)) (k e)
			                                     (x (embed (x% e k f) (inv-auto (phi3% e k f) e f) e f)))))))

(local-defthmd ngsne-24
  (implies (and (extensionp e k) (extensionp k f) (galoisp e f) (not (normal-extension-p k f)))
           (not (equal (embed (x% e k f) (rho% e k f) e f)
	               (x% e k f))))
  :hints (("Goal" :use (ngsne-21 ngsne-22 ngsne-23))))

(local-defthmd ngsne-25
  (implies (and (extensionp e k) (extensionp k f) (galoisp e f) (not (normal-extension-p k f)))
           (not (in (rho% e k f) (galois-subgroup k e f))))
  :hints (("Goal" :in-theory (enable x%)
                  :use (ngsne-1 ngsne-12 ngsne-24
                        (:instance extends-trans (d k))
                        (:instance fixing-auto-fixes (phi (rho% e k f)) (x (normal-extension-p-witness k f)))))))

(defthmd normalp-galois-subgroup-normal-extension-p
  (implies (and (extensionp e k) (extensionp k f) (galoisp e f)
                (normalp (galois-subgroup k e f) (galois e f)))
	   (normal-extension-p k f))
  :hints (("Goal" :in-theory (enable rho%)
                  :use (ngsne-17 ngsne-20 ngsne-25
                        (:instance extends-trans (d k))
		        (:instance normalp-conj (h (galois-subgroup k e f)) (g (galois e f)) (x (phi2% e k f)) (y (phi3% e k f)))))))

;;---------------------------------------------------

;; Now suppose k is a normal extension of f.  We shall construct a group homomorphism from g to (galois k f)
;; with kernel h.

;; Let x be an element of k.  Let x' = (flift x k e), m = (min-poly x k f), m' = (plift m f k), and
;; m" = (plift m f e).  Then m = (min-poly x' e f), m' splits in k, and m" splits in e.  By len-proots-max,

;;    (len (proots m' k)) = (len (proots m" e)) = (degree m).

;; It follows that every root of m" is lifted from k.  To prove this, note that if z is a member of
;; (proots m' k), then

;;    (peval m" (flift z k e) e) = (flift (peval m' z k) k e) = (flift (fzero k) k e) = (fzero e)

;; and hence (flift z k e) is a member of (proots m" e).  Thus, (plift (proots m' k) k e) is a sublist 
;; of (proots m" e).  Since (plift (proots m' k) k e) is a dlist of the same length as (proots m" e),
;; (plift (proots m' k) k e) is a permutation of (proots m" e) and every member of the latter is a
;; member of the former, which is lifted from k.

;; Let phi be an embedding of k in e over f.  By pembed-fixes and peval-pembed,

;;    (peval m" (embed x phi e f) e) = (peval (pembed m' phi e f) (embed x phi e f) e)
;;                                   = (embed (peval m' x k) phi e f)
;;                                   = (embed (fzero k) phi e f)
;;                                   = (fzero e),

;; i.e., (prootp (embed x phi e f) m" e), and hence (fliftedp (embed x phi e f) k e).

(local-defthmd nengs-1
  (implies (and (extensionp e k) (extensionp k f) (galoisp e f) (normal-extension-p k f) (feltp x k))
           (let* ((m (min-poly x k f))
	          (m1 (plift m f k))
	          (m2 (plift m f e))
		  (x1 (flift x k e)))
             (and (splits m1 k)
	          (splits m2 e)
		  (equal m (min-poly x1 e f)))))
  :hints (("Goal" :use (galois-equivalence
                        (:instance extends-trans (d k))
                        (:instance normal-extension-p-lemma (e k))
                        (:instance normal-extension-p-lemma (x (flift x k e)))
			(:instance min-poly-flift-min-poly (d k))))))

(local-defthmd nengs-2
  (implies (and (extensionp e k) (extensionp k f) (galoisp e f) (normal-extension-p k f) (feltp x k))
           (let* ((m (min-poly x k f))
	          (m1 (plift m f k))
	          (m2 (plift m f e)))
	     (equal (len (proots m2 e)) 
                    (len (proots m1 k)))))
  :hints (("Goal" :use (nengs-1 galois-equivalence separable-extension-p-subfield
                        (:instance extends-trans (d k))
			(:instance prootp-min-poly (e k))
			(:instance prootp-min-poly (x (flift x k e)))
			(:instance separable-extension-p-lemma (e k))
			(:instance separable-extension-p-lemma (x (flift x k e)))
			(:instance separablep-extension (p (min-poly x k f)))
			(:instance separablep-extension (p (min-poly x k f)) (e k))
                        (:instance len-proots-max (p (plift (min-poly x k f) f k)) (f k))
                        (:instance len-proots-max (p (plift (min-poly x k f) f e)) (f e))))))

(local-defthmd nengs-3
  (implies (and (extensionp e k) (extensionp k f) (galoisp e f) (normal-extension-p k f) (feltp x k))
           (let* ((m (min-poly x k f))
	          (m1 (plift m f k))
	          (m2 (plift m f e)))
	     (implies (member z (proots m1 k))
	              (member (flift z k e) (proots m2 e)))))
  :hints (("Goal" :in-theory (enable prootp)
                  :use ((:instance extends-trans (d k))
			(:instance prootp-min-poly (e k))
			(:instance member-proots (x z) (p (plift (min-poly x k f) f k)) (f k))
			(:instance member-proots (x (flift z k e)) (p (plift (min-poly x k f) f e)) (f e))
			(:instance flift-peval (f k) (x z) (p (plift (min-poly x k f) f k)))))))

(local-defthmd nengs-4
  (implies (and (extensionp e k) (extensionp k f) (galoisp e f) (normal-extension-p k f) (feltp x k))
           (let* ((m (min-poly x k f))
	          (m1 (plift m f k))
	          (m2 (plift m f e)))
	     (implies (sublistp l (proots m1 k))
	              (sublistp (plift l k e) (proots m2 e)))))
  :hints (("Goal" :induct (len l))
          ("Subgoal *1/1" :use (:instance nengs-3 (z (car l))))))

(local-defthmd nengs-5
  (implies (and (extensionp e k) (extensionp k f) (galoisp e f) (normal-extension-p k f) (feltp x k))
           (let* ((m (min-poly x k f))
	          (m1 (plift m f k))
	          (m2 (plift m f e)))
	     (sublistp (plift (proots m1 k) k e)
	               (proots m2 e))))
  :hints (("Goal" :use ((:instance nengs-4 (l (proots (plift (min-poly x k f) f k) k)))))))

(local-defthm nengs-6
  (implies (and (extensionp e k) (feltp x k) (feltsp l k) (not (member x l)))
           (not (member (flift x k e) (plift l k e))))
  :hints (("Subgoal *1/3" :use ((:instance flift-1-1 (y (car l)) (f k))))))

(local-defthm nengs-7
  (implies (and (extensionp e k) (feltsp l k) (dlistp l))
           (dlistp (plift l k e))))

(local-defthmd nengs-8
  (implies (and (extensionp e k) (extensionp k f) (galoisp e f) (normal-extension-p k f) (feltp x k))
           (let* ((m (min-poly x k f))
	          (m1 (plift m f k))
	          (m2 (plift m f e)))
	     (and (dlistp (plift (proots m1 k) k e))
	          (dlistp (proots m2 e)))))
  :hints (("Goal" :in-theory (enable dlistp-proots feltsp-proots)
                  :use ((:instance prootp-min-poly (e k))))))

(local-defthmd nengs-9
  (implies (and (extensionp e k) (extensionp k f) (galoisp e f) (normal-extension-p k f) (feltp x k))
           (let* ((m (min-poly x k f))
	          (m1 (plift m f k))
	          (m2 (plift m f e)))
	     (sublistp (proots m2 e)
	               (plift (proots m1 k) k e))))
  :hints (("Goal" :in-theory (enable permp)
                  :use (nengs-8 nengs-5 nengs-2
		        (:instance permp-eq-len (l (plift (proots (plift (min-poly x k f) f k) k) k e)) (m (proots (plift (min-poly x k f) f e) e)))))))

(local-defthmd nengs-10
  (implies (and (extensionp e k) (feltsp l k) (member x (plift l k e)))
           (fliftedp x k e)))

(local-defthmd nengs-11
  (implies (and (extensionp e k) (extensionp k f) (galoisp e f) (normal-extension-p k f)
                (feltp x k) (prootp z (plift (min-poly x k f) f e) e))
           (fliftedp z k e))
  :hints (("Goal" :in-theory (enable feltsp-proots)
                  :use (nengs-9
                        (:instance prootp-min-poly (e k))
			(:instance extends-trans (d k))
			(:instance member-proots (x z) (p (plift (min-poly x k f) f e)) (f e))
			(:instance nengs-10 (x z) (l (proots (plift (min-poly x k f) f k) k)))))))

(local-defthmd nengs-12
  (implies (and (extensionp e k) (extensionp k f) (galoisp e f) (normal-extension-p k f)
                (feltp x k) (embeddingp phi k e f))
           (let* ((m (min-poly x k f))
	          (m2 (plift m f e)))
	     (prootp (embed x phi e f) m2 e)))
  :hints (("Goal" :in-theory (enable prootp)
                  :use (nengs-9
                        (:instance prootp-min-poly (e k))
			(:instance extends-trans (d k))
			(:instance pembed-fixes (e k) (k e) (p (min-poly x k f)))
			(:instance peval-pembed (e k) (k e) (p (plift (min-poly x k f) f k)))))))

(defthmd fliftedp-embed
  (implies (and (extensionp e k) (extensionp k f) (galoisp e f) (normal-extension-p k f)
                (embeddingp phi k e f) (feltp x k))
	   (fliftedp (embed x phi e f) k e))
  :hints (("Goal" :use (nengs-12
                        (:instance nengs-11 (z (embed x phi e f)))))))

;;---------------------------------------------------

;; Based on this observation, we shall define the automorphism of k induced by phi.
;; First we show that the following function is a meta-automorphism of k over f:

(defund fdrop-embed (x phi e k f)
  (fdrop (embed x phi e f) e k))

(defthm fdrop-embed-image
  (implies (and (extensionp e k) (extensionp k f) (galoisp e f) (normal-extension-p k f)
                (embeddingp phi k e f) (feltp x k))
	   (feltp (fdrop-embed x phi e k f) k))
  :hints (("Goal" :in-theory (enable fdrop-embed)
                  :use (fliftedp-embed
			(:instance extends-trans (d k))
                        (:instance flift-fdrop (f k) (x (embed x phi e f)))))))

(defthm fdrop-embed-fzero-fone
  (implies (and (extensionp e k) (extensionp k f) (galoisp e f) (normal-extension-p k f)
                (embeddingp phi k e f))
	   (and (equal (fdrop-embed (fzero k) phi e k f) (fzero k))
	        (equal (fdrop-embed (fone k) phi e k f) (fone k))))
  :hints (("Goal" :in-theory (enable fdrop-embed)
                  :use ((:instance extends-trans (d k))
                        (:instance fdrop-flift (f k) (x (fzero k)))
                        (:instance fdrop-flift (f k) (x (fone k)))))))

(defthm fdrop-embed-fadd
  (implies (and (extensionp e k) (extensionp k f) (galoisp e f) (normal-extension-p k f)
                (embeddingp phi k e f) (feltp x k) (feltp y k))
	   (equal (fdrop-embed (fadd x y k) phi e k f)
	          (fadd (fdrop-embed x phi e k f) (fdrop-embed y phi e k f) k)))
  :hints (("Goal" :in-theory (enable fdrop-embed)
                  :use (fliftedp-embed
		        (:instance fliftedp-embed (x y))
			(:instance extends-trans (d k))
                        (:instance flift-fdrop (f k) (x (embed x phi e f)))
                        (:instance flift-fdrop (f k) (x (embed y phi e f)))
                        (:instance fdrop-flift (f k) (x (fadd (fdrop (embed x phi e f) e k) (fdrop (embed y phi e f) e k) k)))))))

(defthm fdrop-embed-fmul
  (implies (and (extensionp e k) (extensionp k f) (galoisp e f) (normal-extension-p k f)
                (embeddingp phi k e f) (feltp x k) (feltp y k))
	   (equal (fdrop-embed (fmul x y k) phi e k f)
	          (fmul (fdrop-embed x phi e k f) (fdrop-embed y phi e k f) k)))
  :hints (("Goal" :in-theory (enable fdrop-embed)
                  :use (fliftedp-embed
		        (:instance fliftedp-embed (x y))
			(:instance extends-trans (d k))
                        (:instance flift-fdrop (f k) (x (embed x phi e f)))
                        (:instance flift-fdrop (f k) (x (embed y phi e f)))
                        (:instance fdrop-flift (f k) (x (fmul (fdrop (embed x phi e f) e k) (fdrop (embed y phi e f) e k) k)))))))

(defthm fdrop-embed-fixes
  (implies (and (extensionp e k) (extensionp k f) (galoisp e f) (normal-extension-p k f)
                (embeddingp phi k e f) (feltp x f))
	   (equal (fdrop-embed (flift x f k) phi e k f)
	          (flift x f k)))
  :hints (("Goal" :in-theory (enable fdrop-embed)
                  :use ((:instance extends-trans (d k))
		        (:instance fdrop-flift (f k) (x (flift x f k)))))))

;; The corresponding automorphism is defined by emulating the definition of phi1 (see embeddings.lisp):

(defun fdrop-embedding-aux (phi e d k f)
  (if (and (extensionp e k) (extensionp k d) (extensionp d f) (not (equal d f)))
      (cons (fdrop-embed (flift (primitive d) d k) phi e k f)
            (fdrop-embedding-aux phi e (cdr d) k f))
    ()))

(defund fdrop-embedding (phi e k f)
  (fdrop-embedding-aux phi e k k f))

;; By functional instantiation of phi1-phi0, fdrop-embedding is the reification of fdrop-embed:

(defmacro fdrop-embedding-mac ()
  '(and (extensionp e k) (extensionp k f) (galoisp e f) (normal-extension-p k f)
        (embeddingp phi k e f)))

(in-theory (enable fdrop-embedding autop))

(defthmd autop-fdrop-embedding
  (implies (and (extensionp e k) (extensionp k f) (galoisp e f) (normal-extension-p k f)
                (embeddingp phi k e f))
	   (let ((phi1 (fdrop-embedding phi e k f)))
	     (and (autop phi1 k f)
	          (implies (feltp x k)
		           (equal (embed x phi1 k f)
			          (fdrop (embed x phi e f) e k))))))
  :hints (("Goal" :use ((:functional-instance phi1-phi0
                          (e0 (lambda () (if (fdrop-embedding-mac) k (e0))))
                          (k0 (lambda () (if (fdrop-embedding-mac) k (k0))))
                          (b0 (lambda () (if (fdrop-embedding-mac) f (b0))))
                          (phi0 (lambda (x) (if (fdrop-embedding-mac) (fdrop-embed x phi e k f) (phi0 x))))
			  (phi1-aux (lambda (d) (if (fdrop-embedding-mac) (fdrop-embedding-aux phi e d k f) (phi1-aux d))))
			  (phi1 (lambda () (if (fdrop-embedding-mac) (fdrop-embedding-aux phi e k k f) (phi1)))))))
	  ("Subgoal 14" :in-theory (enable fdrop-embed))
	  ("Subgoal 7" :use (extensionp-e0-k0-b0))
	  ("Subgoal 6" :use (extensionp-e0-k0-b0))
	  ("Subgoal 5" :use (extensionp-e0-k0-b0))
	  ("Subgoal 4" :use (extensionp-e0-k0-b0))
	  ("Subgoal 3" :use (extensionp-e0-k0-b0))))

(in-theory (disable fdrop-embedding autop))


;; Next we define a homomorphism from (galois e f) to (galois k f):

(defun galois-restriction (phi e k f)
  (fdrop-embedding (restrict-embedding phi e k) e k f))

(defmap galois-restriction-map (e k f)
  (auto-list e f)
  (galois-restriction x e k f))

;; By embeddingp-restrict-embedding, and autop-fdrop-embedding, galois-restriction-map maps
;; (galois e f) to (galois k f):

(defthm autop-galois-restriction
  (implies (and (extensionp e k) (extensionp k f) (galoisp e f) (normal-extension-p k f)
                (in phi (autos e f)))
	   (autop (galois-restriction phi e k f) k f))
  :hints (("Goal" :in-theory (enable autop)
                  :use ((:instance extends-trans (d k))
		        (:instance embeddingp-restrict-embedding (d k) (k e))
		        (:instance autop-fdrop-embedding (phi (restrict-embedding phi e k)))))))

;; If phi is in g and let x be an element of k, then

;;  (embed x (galois-restriction phi e k f) k f)
;;    = (embed x (fdrop-embedding (restrict-embedding phi e k) e k f) k f)  [definition]
;;    = (fdrop (embed x (restrict-embedding phi e k) e f) e k)              [autop-fdrop-embedding]
;;    = (fdrop (embed (flift x k e) phi e f) e k)                           [embed-flift-gen]

(local-defthmd embed-galois-restriction-1
  (implies (and (extensionp e k) (extensionp k f) (galoisp e f) (normal-extension-p k f)
                (autop phi e f) (feltp x k))
           (equal (embed x (galois-restriction phi e k f) k f)
	          (fdrop (embed x (restrict-embedding phi e k) e f) e k)))
  :hints (("Goal" :use ((:instance extends-trans (d k))
                        (:instance autop-fdrop-embedding (phi (restrict-embedding phi e k)))
                        (:instance embeddingp-restrict-embedding (d k) (k e))))))

(defthmd embed-galois-restriction
  (implies (and (extensionp e k) (extensionp k f) (galoisp e f) (normal-extension-p k f)
                (autop phi e f) (feltp x k))
           (equal (embed x (galois-restriction phi e k f) k f)
	          (fdrop (embed (flift x k e) phi e f) e k)))
  :hints (("Goal" :use ((:instance extends-trans (d k))
                        (:instance embed-flift-gen (d k) (k e))
                        (:instance autop-fdrop-embedding (phi (restrict-embedding phi e k)))
                        (:instance embeddingp-restrict-embedding (d k) (k e))))))

;; In particular,

;;  (embed x (galois-restriction (id-auto e f) e k f) k f)
;;    = (fdrop (embed (flift x k e) (id-auto e f) e f) e k)
;;    = (fdrop (flift x k e) e k)
;;    = x

(defthmd embed-galois-restriction-id
  (implies (and (extensionp e k) (extensionp k f) (galoisp e f) (normal-extension-p k f)
                (feltp x k))
           (equal (embed x (galois-restriction (id-auto e f) e k f) k f)
	          x))
  :hints (("Goal" :use ((:instance extends-trans (d k))
                        (:instance embed-galois-restriction (phi (id-auto e f)))  
                        (:instance fdrop-flift (f k))))))

;; Combine this with embed-cex-lemma:

(defthm galois-restriction-id
  (implies (and (extensionp e k) (extensionp k f) (galoisp e f) (normal-extension-p k f))
           (equal (galois-restriction (id-auto e f) e k f)
	          (id-auto k f)))
  :hints (("Goal" :in-theory (enable autop)
                  :use (autop-id-auto
		        (:instance autop-id-auto (e k))
		        (:instance extends-trans (d k))
			(:instance embed-cex-lemma (phi (galois-restriction (id-auto e f) e k f))
                                                   (psi (id-auto k f))
						   (e k))
			(:instance embed-galois-restriction-id
			  (x (embed-cex (galois-restriction (id-auto e f) e k f)  (id-auto k f) k f)))
			(:instance autop-galois-restriction (phi (id-auto e f)))))))

;; Now let phi and psi be in g.  By embed-comp-auto, autop-comp-auto, and embed-galois-restriction,

;; (embex x (comp-auto (galois-restriction psi e k f) (galois-restriction phi e k f) k f) k f)
;;   = (embed (embed x (galois-restriction phi e k f) k f) (galois-restriction psi e k f) k f)
;;   = (embed (fdrop (embed (flift x k e) phi e f) e k) (galois-restriction psi e k f) k f)
;;   = (fdrop (embed (flift (fdrop (embed (flift x k e) phi e f) e k) k e) psi e f) e k)
;;   = (fdrop (embed (embed (flift x k e) phi e f) psi e f) e k)
;;   = (fdrop (embed (flift x k e) (comp-auto psi phi e f) e f) e k)
;;   = (embed x (galois-restriction (comp-auto psi phi e f) e k f) k f)

(in-theory (disable galois-restriction))

(local-defthm embed-galois-restriction-comp-1
  (implies (and (extensionp e k) (extensionp k f) (galoisp e f) (normal-extension-p k f)
                (in phi (autos e f)) (in psi (autos e f))
		(feltp x k))
	   (equal (embed x (comp-auto (galois-restriction psi e k f) (galois-restriction phi e k f) k f) k f)
	          (fdrop (embed (flift (fdrop (embed (flift x k e) phi e f) e k) k e) psi e f) e k)))
  :hints (("Goal" :use (embed-galois-restriction
                        (:instance extends-trans (d k))
                        (:instance embed-galois-restriction (phi psi) (x (fdrop (embed (flift x k e) phi e f) e k)))))))

(local-defthm embed-galois-restriction-comp-2
  (implies (and (extensionp e k) (extensionp k f) (galoisp e f) (normal-extension-p k f)
                (in phi (autos e f)) (in psi (autos e f))
		(feltp x k))
	   (fliftedp (embed (flift x k e) phi e f) k e))
  :hints (("Goal" :use (embed-galois-restriction
                        (:instance extends-trans (d k))
                        (:instance embed-flift-gen (d k) (k e))
                        (:instance fliftedp-embed (phi (restrict-embedding phi e k)))
			(:instance embeddingp-restrict-embedding (d k) (k e))))))

(defthm embed-galois-restriction-comp
  (implies (and (extensionp e k) (extensionp k f) (galoisp e f) (normal-extension-p k f)
                (in phi (autos e f)) (in psi (autos e f))
		(feltp x k))
	   (equal (embed x (comp-auto (galois-restriction psi e k f) (galois-restriction phi e k f) k f) k f)
	          (embed x (galois-restriction (comp-auto psi phi e f) e k f) k f)))
  :hints (("Goal" :use (embed-galois-restriction-comp-1 embed-galois-restriction-comp-2
                        (:instance extends-trans (d k))
                        (:instance flift-fdrop (x (embed (flift x k e) phi e f)) (f k))
			(:instance embed-galois-restriction (phi (comp-auto psi phi e f)))))))

;; Once again we apply embed-cex-lemma:

(defthm galois-restriction-comp
  (implies (and (extensionp e k) (extensionp k f) (galoisp e f) (normal-extension-p k f)
                (in phi (autos e f)) (in psi (autos e f)))
	   (equal (comp-auto (galois-restriction psi e k f) (galois-restriction phi e k f) k f)
	          (galois-restriction (comp-auto psi phi e f) e k f)))
  :hints (("Goal" :in-theory (enable autop)
                  :use (autop-galois-restriction
                        (:instance autop-galois-restriction (phi psi))
                        (:instance autop-galois-restriction (phi (comp-auto psi phi e f)))
                        (:instance extends-trans (d k))
                        (:instance embed-galois-restriction-comp
                          (x (embed-cex (comp-auto (galois-restriction psi e k f) (galois-restriction phi e k f) k f)
			                (galois-restriction (comp-auto psi phi e f) e k f)
					k f)))
			(:instance embed-cex-lemma (phi (comp-auto (galois-restriction psi e k f) (galois-restriction phi e k f) k f))
			                           (psi (galois-restriction (comp-auto psi phi e f) e k f))
						   (e k))))))

;; This is now proved automatically:

(prove-homomorphismp galois-restriction-map
  (galois-restriction-map e k f)
  (galois e f)
  (galois k f)
  (and (extensionp e k) (extensionp k f) (extensionp e f) (galoisp e f) (normal-extension-p k f)))

(DEFTHM HOMOMORPHISMP-GALOIS-RESTRICTION-MAP
  (IMPLIES (AND (EXTENSIONP E K)
                (EXTENSIONP K F)
                (EXTENSIONP E F)
                (GALOISP E F)
                (NORMAL-EXTENSION-P K F))
          (HOMOMORPHISMP (GALOIS-RESTRICTION-MAP E K F)
                         (GALOIS E F)
                         (GALOIS K F))))

;; We have noted that if phi is in g and x is an element of k, then

;;  (embed x (galois-restriction phi e k f) k f)
;;    = (fdrop (embed x (restrict-embedding phi e k) k f) e k)

;; Suppose phi is in h.  Then (restrict-embedding phi e k) = (trivial-embedding k e f) and
;; we have

;;   (embed x (galois-restriction phi e k f) k f) = (fdrop (flift x k e) e k) = x

;; and hence (galois-restriction phi e k f) = (id-auto k f).
;; Conversely, if (galois-restriction phi e k f) = (id-auto k f), then we have

;;   (fdrop (embed x (restrict-embedding phi e k) e f) e k) = x

;; which implies (embed x (restrict-embedding phi e k) k f) = (flift x k e) and hence
;; (restrict-embedding phi e k) = (trivial-embedding k e f), i.e., phi is in h.

(defthmd fixing-autos-kelts-1
  (implies (and (extensionp e k) (extensionp k f) (galoisp e f) (normal-extension-p k f)
                (in phi (galois e f))
		(equal (restrict-embedding phi e k) (trivial-embedding k e f))
		(feltp x k))
	   (equal (embed x (galois-restriction phi e k f) k f)
	          x))
  :hints (("Goal" :use (embed-galois-restriction-1
                        (:instance extends-trans (d k))
			(:instance trivial-embedding-flift (k e) (e k))
                        (:instance fdrop-flift (f k))))))

(defthmd fixing-autos-kelts-2
  (implies (and (extensionp e k) (extensionp k f) (galoisp e f) (normal-extension-p k f)
                (in phi (galois e f))
		(equal (restrict-embedding phi e k) (trivial-embedding k e f)))
	   (equal (galois-restriction phi e k f)
	          (id-auto k f)))
  :hints (("Goal" :use ((:instance fixing-autos-kelts-1 (x (embed-cex (galois-restriction phi e k f) (id-auto k f) k f)))
                        (:instance embed-cex-lemma (phi (galois-restriction phi e k f)) (psi (id-auto k f)) (e k))
                        (:instance extends-trans (d k))))))

(defthmd fixing-autos-kelts-3
  (implies (and (extensionp e k) (extensionp k f) (galoisp e f) (normal-extension-p k f)
                (in phi (galois e f))
		(equal (galois-restriction phi e k f) (id-auto k f))
		(feltp x k))
	   (equal (embed x (restrict-embedding phi e k) e f)
	          (flift x k e)))
  :hints (("Goal" :use (embed-galois-restriction-1
                        (:instance extends-trans (d k))
                        (:instance embed-flift-gen (d k) (k e))
			(:instance embeddingp-restrict-embedding (d k) (k e))
                        (:instance fliftedp-embed (phi (restrict-embedding phi e k)))
			(:instance flift-fdrop (f k) (x (embed x (restrict-embedding phi e k) e f)))))))

(defthmd fixing-autos-kelts-4
  (implies (and (extensionp e k) (extensionp k f) (galoisp e f) (normal-extension-p k f)
                (in phi (galois e f))
		(equal (galois-restriction phi e k f) (id-auto k f)))
	   (equal (restrict-embedding phi e k)
	          (trivial-embedding k e f)))
  :hints (("Goal" :use ((:instance fixing-autos-kelts-3 (x (embed-cex (restrict-embedding phi e k) (trivial-embedding k e f) k f)))
                        (:instance embed-cex-lemma (phi (restrict-embedding phi e k)) (psi (trivial-embedding k e f)) (e k) (k e))
                        (:instance extends-trans (d k))
			(:instance trivial-embedding-flift
			   (k e) (e k) (x (embed-cex (restrict-embedding phi e k) (trivial-embedding k e f) k f)))
			(:instance embeddingp-restrict-embedding (d k) (k e))))))
			
(defthmd fixing-autos-kelts
  (implies (and (extensionp e k) (extensionp k f) (galoisp e f) (normal-extension-p k f)
                (in phi (galois e f)))
	   (iff (equal (galois-restriction phi e k f) (id-auto k f))
	        (equal (restrict-embedding phi e k)
	               (trivial-embedding k e f))))
  :hints (("Goal" :use (fixing-autos-kelts-2 fixing-autos-kelts-4))))

;; It follows that h is the kernel of (galois-restriction-map e k f):

(local-defthmd kernel-galois-restriction-map-1
  (implies (and (extensionp e k) (extensionp e f) (extensionp k f) (galoisp e f) (normal-extension-p k f)
                (sublistp l (auto-list e f)))
	   (equal (fixing-autos-aux l k e f)
	          (kelts-aux (galois-restriction-map e k f) l (galois k f))))
  :hints (("Goal" :induct (len l))
          ("Subgoal *1/1" :use ((:instance fixing-autos-kelts (phi (car l)))))))

(local-defthmd kernel-galois-restriction-map-2
  (implies (and (extensionp e k) (extensionp e f) (extensionp k f) (galoisp e f) (normal-extension-p k f))
	   (equal (fixing-autos k e f)
	          (kelts (galois-restriction-map e k f) (galois e f) (galois k f))))
  :hints (("Goal" :in-theory (enable fixing-autos kelts)
                  :use ((:instance kernel-galois-restriction-map-1 (l (auto-list e f)))))))

(defthmd kernel-galois-restriction-map
  (implies (and (extensionp e k) (extensionp k f) (galoisp e f)
	        (normal-extension-p k f))
           (equal (kernel (galois-restriction-map e k f) 
	                  (galois k f)
                          (galois e f))
	          (galois-subgroup k e f)))
  :hints (("Goal" :use (subgroupp-galois-subgroup homomorphismp-galois-restriction-map kernel-galois-restriction-map-2
                        (:instance extends-trans (d k))
                        (:instance subgroups-equal-elts (g (galois e f)) (h (galois-subgroup k e f))
                                                        (k (kernel (galois-restriction-map e k f) 
	                                                           (galois k f)
                                                                   (galois e f))))
			(:instance normalp-kernel (map (galois-restriction-map e k f)) (g (galois e f)) (h (galois k f)))))))

;; Thus, h is normal in g:

(defthmd normalp-normal-extension-p
  (implies (and (extensionp e k) (extensionp k f) (galoisp e f))
           (iff (normalp (galois-subgroup k e f) (galois e f))
	        (normal-extension-p k f)))
  :hints (("Goal" :use (subgroupp-galois-subgroup homomorphismp-galois-restriction-map kernel-galois-restriction-map
                        normalp-galois-subgroup-normal-extension-p
                        (:instance extends-trans (d k))
			(:instance normalp-kernel (map (galois-restriction-map e k f)) (g (galois e f)) (h (galois k f)))))))                        

;; Every homomorphism induces an endomorphism on the quotient of its kernel:

(defthmd endomorphismp-quotient-map-galois-restriction-map
  (implies (and (extensionp e k) (extensionp k f) (galoisp e f) (normal-extension-p k f))
	   (endomorphismp (quotient-map (galois-restriction-map e k f) (galois e f) (galois k f))
	                  (quotient (galois e f) (galois-subgroup k e f))
			  (galois k f)))
  :hints (("Goal" :use (kernel-galois-restriction-map homomorphismp-galois-restriction-map
                        (:instance extends-trans (d k))
                        (:instance endomorphismp-quotient-map (map (galois-restriction-map e k f)) (g (galois e f)) (h (galois k f)))))))

;; By isomorphismp-galois-subgroup-map, (order (galois-subgroup k e f)) = (order (galois e k)).
;; Thus, by order-galois-group, edegree-mult, and order-quotient,

;;   (order (quotient (galois e f) (galois-subgroup e k f))) = (order (galois k f),

;; and by equal-orders-isomorphism, this endomorphism is an isomorphism:

(local-defthmd isomorphismp-quotient-map-galois-restriction-map-1
  (implies (and (extensionp e k) (extensionp k f) (galoisp e f) (normal-extension-p k f))
           (equal (order (galois-subgroup k e f))
	          (edegree e k)))
  :hints (("Goal" :use (isomorphismp-galois-subgroup-map galoisp-subfield
                        (:instance extends-trans (d k))
                        (:instance isomorphism-equal-orders (map (GALOIS-SUBGROUP-MAP K E F))
                                                            (g (GALOIS-SUBGROUP K E F))
                                                            (h (GALOIS E K)))
			(:instance order-galois-group (f k))))))

(local-defthmd isomorphismp-quotient-map-galois-restriction-map-2
  (implies (and (extensionp e k) (extensionp k f) (galoisp e f) (normal-extension-p k f))
           (equal (* (edegree e k) (order (quotient (galois e f) (galois-subgroup k e f))))
	          (edegree e f)))
  :hints (("Goal" :use (order-galois-group normal-extension-p-subfield normalp-normal-extension-p
                        isomorphismp-quotient-map-galois-restriction-map-1
			(:instance lagrange (g (galois e f)) (h (galois-subgroup k e f)))
                        (:instance order-galois-group (e k))
			(:instance order-quotient (g (galois e f)) (h (galois-subgroup k e f)))
                        (:instance extends-trans (d k))))))

(local-defthmd isomorphismp-quotient-map-galois-restriction-map-3
  (implies (and (extensionp e k) (extensionp k f) (galoisp e f) (normal-extension-p k f))
           (equal (order (quotient (galois e f) (galois-subgroup k e f)))
	          (order (galois k f))))
  :hints (("Goal" :in-theory (disable posp-edegree)
                  :use (edegree-mult isomorphismp-quotient-map-galois-restriction-map-2 posp-edegree
		        normal-extension-p-subfield
                        (:instance posp-edegree (e k))
                        (:instance posp-edegree (f k))
                        (:instance order-galois-group (e k))
                        (:instance extends-trans (d k))))))

(defthmd isomorphismp-quotient-map-galois-restriction-map
  (implies (and (extensionp e k) (extensionp k f) (galoisp e f) (normal-extension-p k f))
	   (isomorphismp (quotient-map (galois-restriction-map e k f) (galois e f) (galois k f))
	                 (quotient (galois e f) (galois-subgroup k e f))
			 (galois k f)))
  :hints (("Goal" :use (endomorphismp-quotient-map-galois-restriction-map isomorphismp-quotient-map-galois-restriction-map-3
                        (:instance equal-orders-isomorphism (map (quotient-map (galois-restriction-map e k f) (galois e f) (galois k f)))
	                                                    (g (quotient (galois e f) (galois-subgroup k e f)))
			                                    (h (galois k f)))))))

;;----------------------------------------------------------------------------------------------------------

;; This is an important lemma for the fundamental theorem:

;; Artin's Lemma: Let e be an extension of f with intermediate field k.  Let h be a subgroup of (autos e f)
;; such that for all x in e, x is fixed by h iff x is lifted from k.  Then (edegree e k) <= (order h).

;; This predicate recognizes elements of e that are fixed by a subgroup h of (galois e f):

(defun fixedp-aux (x l e f)
  (if (consp l)
      (and (equal x (embed x (car l) e f))
           (fixedp-aux x (cdr l) e f))
    t))

(defund fixedp (x h e f)
  (fixedp-aux x (elts h) e f))

(defthm fixedp-embed
  (implies (and (fixedp x h e f) (in phi h))
           (equal (embed x phi e f) x))
  :hints (("Goal" :in-theory (enable fixedp))))

;; If x is not fixed by h, then we can find an element of h that does not fix x:

(defun fixedp-aux-cex (x l e f)
  (if (consp l)
      (if (equal x (embed x (car l) e f))
          (fixedp-aux-cex x (cdr l) e f)
	(car l))
    ()))

(defund fixedp-cex (x h e f)
  (fixedp-aux-cex x (elts h) e f))

(defthmd fixedp-cex-lemma
  (implies (not (fixedp x h e f))
           (let ((phi (fixedp-cex x h e f)))
	     (and (in phi h)
                  (not (equal x (embed x phi e f)))))))

;; The hypothesis of Artin's Lemma is that k satisfies the following predicate:

(defun-sk fixed-field-p (k h e f)
  (forall (x)
    (implies (feltp x e)
             (iff (fixedp x h e f)
	          (fliftedp x k e)))))

(defthmd fixed-field-p-lemma
  (implies (and (fixed-field-p k h e f) (feltp x e))
           (iff (fixedp x h e f)
	        (fliftedp x k e)))
  :hints (("Goal" :use (fixed-field-p-necc))))

;; For the proof, we need some results from linear algebra pertaining to the solutions of a homogeneous
;; system of linear equations.  These results are proved in "../linear/reduction.lisp" for the generic
;; field f0.  We can easily prove by functional instantiarion that they hold for an arbitrary field e.

;; In embeddings.lisp, we define several functions pertaining to lists of elements of a field e.  We
;; shall require some additional definitions.

;; Addition, scalar multiplication, and dot product:

(defun elist-add (x y e)
  (if (consp x)
      (cons (fadd (car x) (car y) e)
            (elist-add (cdr x) (cdr y) e))
    ()))

(defun elist-scalar-mul (c x e)
  (if (consp x)
      (cons (fmul c (car x) e)
            (elist-scalar-mul c (cdr x) e))
    ()))

(defun edot (x y e)
  (if (consp x)
      (fadd (fmul (car x) (car y) e)
            (edot (cdr x) (cdr y) e)
	    e)
    (fzero e)))

;; mxn matrix over e:

(defun ematp (a m n e)
  (declare (xargs :measure (nfix m)))
  (if (zp m)
      (null a)
    (and (consp a)
	 (elistnp (car a) n e)
	 (ematp (cdr a) (1- m) n e))))

;; Matrix multiplication:

(defun edot-list (x l e)
  (if (consp l)
      (cons (edot x (car l) e)
            (edot-list x (cdr l) e))
    ()))

(defund emat* (a b e)
  (if (consp a)
      (cons (edot-list (car a) (transpose-mat b) e)
            (emat* (cdr a) b e))
    ()))

;; We need the following lemmas, proved by functional instantiation of the corresponding lemmas in "../linear/fmat.lisp":

(in-theory (enable fmat* emat*))

(defthmd emat-entry-diff-lemma
  (implies (and (fieldp e) (posp m) (posp n) (ematp a m n e) (ematp b m n e) (not (equal a b)))
	   (let* ((pair (entry-diff a b))
		  (i (car pair))
		  (j (cdr pair)))
	     (and (natp i) (< i m)
		  (natp j) (< j n)
		  (not (equal (entry i j a) (entry i j b))))))
  :hints (("Goal" :use ((:functional-instance fmat-entry-diff-lemma
                         (fp (lambda (x) (if (fieldp e) (feltp x e) (fp x))))
			 (f0 (lambda () (if (fieldp e) (fzero e) (f0))))
			 (f1 (lambda () (if (fieldp e) (fone e) (f1))))
                         (f+ (lambda (x y) (if (fieldp e) (fadd x y e) (f+ x y))))
			 (f* (lambda (x y) (if (fieldp e) (fmul x y e) (f* x y))))
			 (f- (lambda (x) (if (fieldp e) (fneg x e) (f- x))))
			 (f/ (lambda (x) (if (fieldp e) (frecip x e) (f/ x))))
			 (flistnp (lambda (x n) (if (fieldp e) (elistnp x n e) (flistnp x n))))
			 (fmatp (lambda (a m n) (if (fieldp e) (ematp a m n e) (fmatp a m n)))))))
	  ("Subgoal 6" :use (f*assoc (:instance fmul-assoc (f e))))
	  ("Subgoal 5" :use (f+assoc (:instance fadd-assoc (f e))))
	  ("Subgoal 4" :use (f*comm (:instance fmul-comm (f e))))
	  ("Subgoal 3" :use (f+comm (:instance fadd-comm (f e))))))

(defthmd ematp-transpose
  (implies (and (fieldp e) (posp m) (posp n) (ematp a m n e))
	   (ematp (transpose-mat a) n m e))
  :hints (("Goal" :use ((:functional-instance fmatp-transpose
                         (fp (lambda (x) (if (fieldp e) (feltp x e) (fp x))))
			 (f0 (lambda () (if (fieldp e) (fzero e) (f0))))
			 (f1 (lambda () (if (fieldp e) (fone e) (f1))))
                         (f+ (lambda (x y) (if (fieldp e) (fadd x y e) (f+ x y))))
			 (f* (lambda (x y) (if (fieldp e) (fmul x y e) (f* x y))))
			 (f- (lambda (x) (if (fieldp e) (fneg x e) (f- x))))
			 (f/ (lambda (x) (if (fieldp e) (frecip x e) (f/ x))))
			 (flistnp (lambda (x n) (if (fieldp e) (elistnp x n e) (flistnp x n))))
			 (fmatp (lambda (a m n) (if (fieldp e) (ematp a m n e) (fmatp a m n)))))))))

(defthm transpose-emat-entry
  (implies (and (fieldp e) (posp m) (posp n) (ematp a m n e)
		(natp j) (< j n) (natp i) (< i m))
	   (equal (entry j i (transpose-mat a))
		  (entry i j a)))
  :hints (("Goal" :use ((:functional-instance transpose-fmat-entry
                         (fp (lambda (x) (if (fieldp e) (feltp x e) (fp x))))
			 (f0 (lambda () (if (fieldp e) (fzero e) (f0))))
			 (f1 (lambda () (if (fieldp e) (fone e) (f1))))
                         (f+ (lambda (x y) (if (fieldp e) (fadd x y e) (f+ x y))))
			 (f* (lambda (x y) (if (fieldp e) (fmul x y e) (f* x y))))
			 (f- (lambda (x) (if (fieldp e) (fneg x e) (f- x))))
			 (f/ (lambda (x) (if (fieldp e) (frecip x e) (f/ x))))
			 (flistnp (lambda (x n) (if (fieldp e) (elistnp x n e) (flistnp x n))))
			 (fmatp (lambda (a m n) (if (fieldp e) (ematp a m n e) (fmatp a m n)))))))))

(defthm transpose-emat-2
  (implies (and (fieldp e) (posp m) (posp n) (ematp a m n e))
           (equal (transpose-mat (transpose-mat a))
	          a))
  :hints (("Goal" :use ((:functional-instance transpose-fmat-2
                         (fp (lambda (x) (if (fieldp e) (feltp x e) (fp x))))
			 (f0 (lambda () (if (fieldp e) (fzero e) (f0))))
			 (f1 (lambda () (if (fieldp e) (fone e) (f1))))
                         (f+ (lambda (x y) (if (fieldp e) (fadd x y e) (f+ x y))))
			 (f* (lambda (x y) (if (fieldp e) (fmul x y e) (f* x y))))
			 (f- (lambda (x) (if (fieldp e) (fneg x e) (f- x))))
			 (f/ (lambda (x) (if (fieldp e) (frecip x e) (f/ x))))
			 (flistnp (lambda (x n) (if (fieldp e) (elistnp x n e) (flistnp x n))))
			 (fmatp (lambda (a m n) (if (fieldp e) (ematp a m n e) (fmatp a m n)))))))))

(defthm ematp-emat*
  (implies (and (fieldp e) (ematp a m n e) (ematp b n p e) (posp m) (posp n) (posp p) )
           (ematp (emat* a b e) m p e))
  :hints (("Goal" :use ((:functional-instance fmatp-fmat*
                         (fp (lambda (x) (if (fieldp e) (feltp x e) (fp x))))
			 (f0 (lambda () (if (fieldp e) (fzero e) (f0))))
			 (f1 (lambda () (if (fieldp e) (fone e) (f1))))
                         (f+ (lambda (x y) (if (fieldp e) (fadd x y e) (f+ x y))))
			 (f* (lambda (x y) (if (fieldp e) (fmul x y e) (f* x y))))
			 (f- (lambda (x) (if (fieldp e) (fneg x e) (f- x))))
			 (f/ (lambda (x) (if (fieldp e) (frecip x e) (f/ x))))
			 (flistnp (lambda (x n) (if (fieldp e) (elistnp x n e) (flistnp x n))))
			 (fdot (lambda (x y) (if (fieldp e) (edot x y e) (fdot x y))))
			 (fmatp (lambda (a m n) (if (fieldp e) (ematp a m n e) (fmatp a m n))))
			 (fdot-list (lambda (x l) (if (fieldp e) (edot-list x l e) (fdot-list x l))))
			 (fmat* (lambda (a b) (if (fieldp e) (emat* a b e) (fmat* a b)))))))))

(defthmd nth-emat*
  (implies (and (fieldp e) (natp m) (ematp a m n e) (natp i) (< i m))
           (equal (nth i (emat* a b e))
	          (edot-list (nth i a) (transpose-mat b) e)))
  :hints (("Goal" :use ((:functional-instance nth-fmat*
                         (fp (lambda (x) (if (fieldp e) (feltp x e) (fp x))))
			 (f0 (lambda () (if (fieldp e) (fzero e) (f0))))
			 (f1 (lambda () (if (fieldp e) (fone e) (f1))))
                         (f+ (lambda (x y) (if (fieldp e) (fadd x y e) (f+ x y))))
			 (f* (lambda (x y) (if (fieldp e) (fmul x y e) (f* x y))))
			 (f- (lambda (x) (if (fieldp e) (fneg x e) (f- x))))
			 (f/ (lambda (x) (if (fieldp e) (frecip x e) (f/ x))))
			 (flistnp (lambda (x n) (if (fieldp e) (elistnp x n e) (flistnp x n))))
			 (fdot (lambda (x y) (if (fieldp e) (edot x y e) (fdot x y))))
			 (fmatp (lambda (a m n) (if (fieldp e) (ematp a m n e) (fmatp a m n))))
			 (fdot-list (lambda (x l) (if (fieldp e) (edot-list x l e) (fdot-list x l))))
			 (fmat* (lambda (a b) (if (fieldp e) (emat* a b e) (fmat* a b)))))))))


;; Solution of a system of linear m equations in n unknowns, represented as an mxn matrix:

(defund esolutionp (x a b e)
  (equal (emat* a (col-mat x) e)
         (col-mat b)))

;; The homogeneous case:

(defund esol0p (x a e)
  (and (elistnp x (len (car a)) e)
       (esolutionp x a (elistn0 (len a) e) e)))

;; The next 3 results are proved by functional instantiation of corresponding results in "../linear/reduction.lisp".

;; The solution set is closed under addition and scalar multiplication:

(in-theory (enable solutionp esolutionp sol0p esol0p))

(defthmd esol0p-fadd
  (implies (and (fieldp e) (posp m) (posp n) (ematp a m n e)
                (esol0p x a e)
		(esol0p y a e))
	   (esol0p (elist-add x y e) a e))
  :hints (("Goal" :use ((:functional-instance sol0p-fadd
                         (fp (lambda (x) (if (fieldp e) (feltp x e) (fp x))))
			 (f0 (lambda () (if (fieldp e) (fzero e) (f0))))
			 (f1 (lambda () (if (fieldp e) (fone e) (f1))))
                         (f+ (lambda (x y) (if (fieldp e) (fadd x y e) (f+ x y))))
			 (f* (lambda (x y) (if (fieldp e) (fmul x y e) (f* x y))))
			 (f- (lambda (x) (if (fieldp e) (fneg x e) (f- x))))
			 (f/ (lambda (x) (if (fieldp e) (frecip x e) (f/ x))))
			 (flistnp (lambda (x n) (if (fieldp e) (elistnp x n e) (flistnp x n))))
			 (flistn0 (lambda (n) (if (fieldp e) (elistn0 n e) (flistn0 n))))
                         (flist-add (lambda (x y) (if (fieldp e) (elist-add x y e) (flist-add x y))))
                         (flist-scalar-mul (lambda (c x) (if (fieldp e) (elist-scalar-mul c x e) (flist-scalar-mul c x))))
			 (fdot (lambda (x y) (if (fieldp e) (edot x y e) (fdot x y))))
			 (fmatp (lambda (a m n) (if (fieldp e) (ematp a m n e) (fmatp a m n))))
			 (fdot-list (lambda (x l) (if (fieldp e) (edot-list x l e) (fdot-list x l))))
			 (fmat* (lambda (a b) (if (fieldp e) (emat* a b e) (fmat* a b))))
			 (solutionp (lambda (x a b) (if (fieldp e) (esolutionp x a b e) (solutionp x a b))))
			 (sol0p (lambda (x a) (if (fieldp e) (esol0p x a e) (sol0p x a)))))))))

(defthmd esol0p-scalar-mul
  (implies (and (fieldp e) (posp m) (posp n) (ematp a m n e)
                (esol0p x a e)
		(feltp c e))
	   (esol0p (elist-scalar-mul c x e) a e))
  :hints (("Goal" :use ((:functional-instance sol0p-scalar-mul
                         (fp (lambda (x) (if (fieldp e) (feltp x e) (fp x))))
			 (f0 (lambda () (if (fieldp e) (fzero e) (f0))))
			 (f1 (lambda () (if (fieldp e) (fone e) (f1))))
                         (f+ (lambda (x y) (if (fieldp e) (fadd x y e) (f+ x y))))
			 (f* (lambda (x y) (if (fieldp e) (fmul x y e) (f* x y))))
			 (f- (lambda (x) (if (fieldp e) (fneg x e) (f- x))))
			 (f/ (lambda (x) (if (fieldp e) (frecip x e) (f/ x))))
			 (flistnp (lambda (x n) (if (fieldp e) (elistnp x n e) (flistnp x n))))
			 (flistn0 (lambda (n) (if (fieldp e) (elistn0 n e) (flistn0 n))))
                         (flist-add (lambda (x y) (if (fieldp e) (elist-add x y e) (flist-add x y))))
                         (flist-scalar-mul (lambda (c x) (if (fieldp e) (elist-scalar-mul c x e) (flist-scalar-mul c x))))
			 (fdot (lambda (x y) (if (fieldp e) (edot x y e) (fdot x y))))
			 (fmatp (lambda (a m n) (if (fieldp e) (ematp a m n e) (fmatp a m n))))
			 (fdot-list (lambda (x l) (if (fieldp e) (edot-list x l e) (fdot-list x l))))
			 (fmat* (lambda (a b) (if (fieldp e) (emat* a b e) (fmat* a b))))
			 (solutionp (lambda (x a b) (if (fieldp e) (esolutionp x a b e) (solutionp x a b))))
			 (sol0p (lambda (x a) (if (fieldp e) (esol0p x a e) (sol0p x a)))))))))

;; If n > m, then there exists a nontrivial solution:

(defun-sk nontrivial-esol0p (a e)
  (exists (x)
    (and (not (elist0p x e))
         (esol0p x a e))))

(defthmd exists-esol0p
  (implies (and (fieldp e) (posp m) (posp n) (> n m) (ematp a m n e))
           (nontrivial-esol0p a e))
  :hints (("Goal" :use ((:functional-instance exists-sol0p
                         (fp (lambda (x) (if (fieldp e) (feltp x e) (fp x))))
			 (f0 (lambda () (if (fieldp e) (fzero e) (f0))))
			 (f1 (lambda () (if (fieldp e) (fone e) (f1))))
                         (f+ (lambda (x y) (if (fieldp e) (fadd x y e) (f+ x y))))
			 (f* (lambda (x y) (if (fieldp e) (fmul x y e) (f* x y))))
			 (f- (lambda (x) (if (fieldp e) (fneg x e) (f- x))))
			 (f/ (lambda (x) (if (fieldp e) (frecip x e) (f/ x))))
			 (flistnp (lambda (x n) (if (fieldp e) (elistnp x n e) (flistnp x n))))
			 (flist0p (lambda (x) (if (fieldp e) (elist0p x e) (flist0p x))))
			 (flistn0 (lambda (n) (if (fieldp e) (elistn0 n e) (flistn0 n))))
                         (flist-add (lambda (x y) (if (fieldp e) (elist-add x y e) (flist-add x y))))
                         (flist-scalar-mul (lambda (c x) (if (fieldp e) (elist-scalar-mul c x e) (flist-scalar-mul c x))))
			 (fdot (lambda (x y) (if (fieldp e) (edot x y e) (fdot x y))))
			 (fmatp (lambda (a m n) (if (fieldp e) (ematp a m n e) (fmatp a m n))))
			 (fdot-list (lambda (x l) (if (fieldp e) (edot-list x l e) (fdot-list x l))))
			 (fmat* (lambda (a b) (if (fieldp e) (emat* a b e) (fmat* a b))))
			 (solutionp (lambda (x a b) (if (fieldp e) (esolutionp x a b e) (solutionp x a b))))
			 (sol0p (lambda (x a) (if (fieldp e) (esol0p x a e) (sol0p x a))))
			 (nontrivial-sol0p (lambda (a) (if (fieldp e) (nontrivial-esol0p a e) (nontrivial-sol0p a))))
			 (nontrivial-sol0p-witness (lambda (a) (if (fieldp e) (nontrivial-esol0p-witness a e) (nontrivial-sol0p-witness a)))))))))

(in-theory (disable fmat* emat* solutionp esolutionp sol0p esol0p))


;; Proof of Artin's Lemma:  Let (order h) = m and let v be a list of elements of e of length n > m.  We shall
;; show that l is linearly dependent over k.

;; We define an mxn matrix, the ith row of which is the result of applying the ith element of h to each
;; member of v:

(defun embed-mat-aux (v l e f)
  (if (consp l)
      (cons (pembed v (car l) e f)
            (embed-mat-aux v (cdr l) e f))
    ()))

(defund embed-mat (v h e f)
  (embed-mat-aux v (elts h) e f))

(local-defthmd ematp-embed-mat-aux
  (implies (and (extensionp e f) (natp n) (elistnp v n e) (sublistp l (auto-list e f)))
           (ematp (embed-mat-aux v l e f) (len l) n e))
  :hints (("Goal" :induct (len l))))

(defthmd ematp-embed-mat
  (implies (and (extensionp e f) (natp n) (elistnp v n e) (subgroupp h (autos e f)))
           (ematp (embed-mat v h e f) (order h) n e))
  :hints (("Goal" :in-theory (enable embed-mat order)
                  :use ((:instance ematp-embed-mat-aux (l (elts h)))
		        (:instance subgroupp-sublistp (g (autos e f)))))))

(local-defthmd nth-embed-mat-aux
  (implies (and (natp i) (< i (len l)))
           (equal (nth i (embed-mat-aux v l e f))
	          (pembed v (nth i l) e f))))

(defthmd nth-embed-mat
  (implies (and (natp i) (< i (order h)))
           (equal (nth i (embed-mat v h e f))
	          (pembed v (nth i (elts h)) e f)))
  :hints (("Goal" :in-theory (enable embed-mat order)
                  :use ((:instance nth-embed-mat-aux (l (elts h)))))))

;; Let a = (embed-mat v h e f).  We consider the solutions of the homogeneous system corresponding to a.
;; If (elistnp x n e) and i < m, then

;;    (nth i (emat* a (col-mat x) e)) = (edot-list (nth i a) (transpose-mat (col-mat x)) e)
;;                                    = (edot-list (nth i a) (transpose-mat (transpose-mat (list x))) e)
;;                                    = (edot-list (nth i a) (list x) e)
;;                                    = (list (edot (nth i a) x e))

;; and hence

;;    (entry i 0 (emat* a (col-mat x) e)) = (edot (nth i a) x e).

;; Thus, x is a solution iff (edot (nth i a) x e) = (fzero e) for all i < m.

;; We know that the set of solutions is closed under addition and scalar multiplication.  Furthermore, if x
;; is a solution and phi is in h, then (pembed x phi e f) is also a solution.  To prove this, let i < m.
;; For some j < m,

;;     (nth i (elts h)) = (comp-auto phi (nth j (elts h)) e f)

;; and hence

;;    (edot (nth i a) (pembed x phi e f) e)
;;      = (edot (pembed v (nth i (elts h)) e f) (pembed x phi e f) e) 
;;      = (edot (pembed v (comp-auto phi (nth j (elts h)) e f) e f) (pembed x phi e f) e)
;;      = (edot (pembed (pembed v (nth j (elts h)) e f) phi e f) (pembed x phi e f) e)
;;      = (pembed (edot (pembed v (nth j (elts h)) e f) x e) phi e f)
;;      = (pembed (edot (nth j a) x e) phi e f)
;;      = (pembed (fzero e) phi e f)
;;      = (fzero e).

(local-defthmd esol0p-pembed-1
  (implies (and (extensionp e f) (subgroupp h (autos e f))
                (natp i) (< i (order h)))
	   (in (nth i (elts h)) h))	   
  :hints (("Goal" :in-theory (enable order))))

(local-defthm esol0p-pembed-2
  (implies (and (extensionp e f) (subgroupp h (autos e f))
                (natp i) (< i (order h)) (in phi h))
	   (and (in phi (autos e f))
	        (in (inv-auto phi e f) (autos e f))
		(in (nth i (elts h)) (autos e f))
	        (in (comp-auto (inv-auto phi e f) (nth i (elts h)) e f) h)))
  :hints (("Goal" :use (esol0p-pembed-1
                        (:instance group-closure (g h) (x (inv-auto phi e f)) (y (nth i (elts h))))
                        (:instance group-left-inverse (g h) (x phi))
			(:instance autos-op-rewrite (x (inv-auto phi e f)) (y (nth i (elts h))))
			(:instance subgroupp-subsetp (x phi) (g (autos e f)))
			(:instance subgroupp-subsetp (x (nth i (elts h))) (g (autos e f)))
			(:instance subgroupp-subsetp (x (inv-auto phi e f)) (g (autos e f)))))))

(local-defthm esol0p-pembed-3
  (implies (and (extensionp e f) (subgroupp h (autos e f))
                (natp i) (< i (order h)) (in phi h))
	   (equal (comp-auto phi (comp-auto (inv-auto phi e f) (nth i (elts h)) e f) e f)
	          (nth i (elts h))))
  :hints (("Goal" :in-theory (disable COMP-AUTO-ASSOC)
                  :use (esol0p-pembed-1 esol0p-pembed-2
		        (:instance group-right-inverse (x phi) (g (autos e f)))
                        (:instance group-assoc (g (autos e f)) (x phi) (y (inv-auto phi e f)) (z (nth i (elts h))))))))

(local-defthm esol0p-pembed-4
  (implies (and (extensionp e f) (subgroupp h (autos e f))
                (natp i) (< i (order h)) (in phi h))
	   (let ((j (ind (comp-auto (inv-auto phi e f) (nth i (elts h)) e f) h)))
	     (and (natp j) (< j (order h))
	          (equal (nth i (elts h))
		         (comp-auto phi (nth j (elts h)) e f)))))
  :hints (("Goal" :in-theory (enable order)
                  :use (esol0p-pembed-1 esol0p-pembed-2 esol0p-pembed-3))))

(local-defthm esol0p-pembed-5
  (implies (and (extensionp e f) (posp n) (elistnp x n e))
           (ematp (list x) 1 n e))
  :hints (("Goal" :in-theory (enable ematp))))

(local-defthmd esol0p-pembed-6
  (implies (and (extensionp e f) (elistnp x n e) (posp n))
           (equal (transpose-mat (col-mat x))
	          (list x)))
  :hints (("Goal" :in-theory (enable col-mat row-mat)
                  :use (esol0p-pembed-5
		        (:instance transpose-emat-2 (a (list x)) (m 1))))))

(local-defthmd esol0p-pembed-7
  (implies (and (extensionp e f) (posp n) (elistnp v n e) (subgroupp h (autos e f)) (elistnp x n e)
                (natp i) (< i (order h)))
           (equal (nth i (emat* (embed-mat v h e f) (col-mat x) e))
	          (list (edot (pembed v (nth i (elts h)) e f) x e))))
  :hints (("Goal" :in-theory (enable order nth-embed-mat)
                  :use (esol0p-pembed-5 esol0p-pembed-6 ematp-embed-mat
		        (:instance nth-emat* (a (embed-mat v h e f)) (m (order h)) (b (col-mat x)))))))

(local-defthmd esol0p-pembed-8
  (implies (and (extensionp e f) (posp n) (elistnp v n e) (subgroupp h (autos e f)) (elistnp x n e)
                (natp i) (< i (order h)))
           (equal (entry i 0 (emat* (embed-mat v h e f) (col-mat x) e))
	          (edot (pembed v (nth i (elts h)) e f) x e)))
  :hints (("Goal" :use (esol0p-pembed-7))))

(defthm elistnp-elistn0
  (implies (and (fieldp e) (natp m))
           (elistnp (elistn0 m e) m e)))

(local-defun nth-elistn0-induct (i m)
  (declare (irrelevant m))
  (if (zp i)
      t
    (nth-elistn0-induct (1- i) (1- m))))

(defthm nth-elistn0
  (implies (and (fieldp e) (posp m) (natp i) (< i m))
           (equal (nth i (elistn0 m e))
	          (fzero e)))
  :hints (("Goal" :induct (nth-elistn0-induct i m))
          ("Subgoal *1/1" :expand ((elistn0 m e)))))

(local-defthmd esol0p-pembed-9
  (implies (and (fieldp e) (posp m) (natp i) (< i m))
           (equal (entry i 0 (col-mat (elistn0 m e)))
	          (fzero e)))
  :hints (("Goal" :in-theory (enable row-mat col-mat)
                  :use ((:instance transpose-emat-entry (a (list (elistn0 m e))) (m 1) (n m) (j i) (i 0))
		        (:instance esol0p-pembed-5 (x (elistn0 m e)) (n m))))))

(defthm feltp-edot
  (implies (and (fieldp e) (elistnp x n e) (elistnp y n e) (natp n))
           (feltp (edot x y e) e)))

(defthmd edot-pembed
  (implies (and (extensionp e f) (natp n) (elistnp x n e) (elistnp y n e) (autop phi e f))
           (equal (edot (pembed x phi e f) (pembed y phi e f) e)
	          (embed (edot x y e) phi e f))))

(defthmd elistnp-pembed
  (implies (and (extensionp e f) (elistnp x n e) (natp n) (autop phi e f))
           (elistnp (pembed x phi e f) n e)))

(local-defthm esol0p-pembed-10
  (implies (and (extensionp e f) (natp n) (elistnp v n e) (subgroupp h (autos e f)) (in phi (autos e f)) (posp n) (elistnp x n e)
                (natp i) (< i (order h)))
           (equal (entry i 0 (emat* (embed-mat v h e f) (col-mat (pembed x phi e f)) e))
	          (edot (pembed v (nth i (elts h)) e f) (pembed x phi e f) e)))
  :hints (("Goal" :use (elistnp-pembed
		        (:instance esol0p-pembed-8 (x (pembed x phi e f)))))))

(local-defthmd esol0p-pembed-11
  (implies (and (extensionp e f) (natp n) (elistnp v n e) (subgroupp h (autos e f)) (in phi h) (posp n) (elistnp x n e)
                (natp i) (< i (order h)))
	   (let ((j (ind (comp-auto (inv-auto phi e f) (nth i (elts h)) e f) h)))
	     (and (natp j) (< j (order h))
	          (in (comp-auto (inv-auto phi e f) (nth i (elts h)) e f) h)
                  (equal (edot (pembed v (nth i (elts h)) e f) (pembed x phi e f) e)
	                 (edot (pembed v (comp-auto phi (nth j (elts h)) e f) e f) (pembed x phi e f) e)))))
  :hints (("Goal" :use (esol0p-pembed-4
                        (:instance subgroupp-subsetp (g (autos e f)) (x phi))))))

(in-theory (enable elistnp-feltsp))

(local-defthmd esol0p-pembed-12
  (implies (and (extensionp e f) (natp n) (elistnp v n e) (subgroupp h (autos e f)) (in phi h) (posp n) (elistnp x n e)
                (natp i) (< i (order h)))
	   (let ((j (ind (comp-auto (inv-auto phi e f) (nth i (elts h)) e f) h)))
	     (and (natp j) (< j (order h))
                  (equal (pembed v (comp-auto phi (nth j (elts h)) e f) e f)
	                 (pembed (pembed v (nth j (elts h)) e f) phi e f)))))
  :hints (("Goal" :in-theory (enable order comp-auto)
                  :use (esol0p-pembed-2
		        (:instance pembed-comp-embedding-feltsp (g e) (k e) (p v) (psi phi) (phi (comp-auto (inv-auto phi e f) (nth i (elts h)) e f)))
			(:instance subgroupp-subsetp (g (autos e f)) (x (comp-auto (inv-auto phi e f) (nth i (elts h)) e f)))))))

(local-defthmd esol0p-pembed-13
  (implies (and (extensionp e f) (natp n) (elistnp v n e) (subgroupp h (autos e f)) (in phi h) (posp n) (elistnp x n e)
                (natp i) (< i (order h)))
	   (let ((j (ind (comp-auto (inv-auto phi e f) (nth i (elts h)) e f) h)))
	     (and (natp j) (< j (order h))
	          (in (comp-auto (inv-auto phi e f) (nth i (elts h)) e f) h)
                  (equal (edot (pembed v (nth i (elts h)) e f) (pembed x phi e f) e)
	                 (edot (pembed (pembed v (nth j (elts h)) e f) phi e f)
			       (pembed x phi e f)
			       e)))))
  :hints (("Goal" :in-theory (theory 'minimal-theory)
                  :use (esol0p-pembed-11 esol0p-pembed-12))))

(local-defthmd esol0p-pembed-14
  (implies (and (extensionp e f) (natp n) (elistnp v n e) (subgroupp h (autos e f)) (in phi h) (posp n) (elistnp x n e)
                (natp i) (< i (order h)))
	   (let ((j (ind (comp-auto (inv-auto phi e f) (nth i (elts h)) e f) h)))
	     (and (natp j) (< j (order h))
	          (in (comp-auto (inv-auto phi e f) (nth i (elts h)) e f) h)
                  (equal (edot (pembed v (nth i (elts h)) e f) (pembed x phi e f) e)
			 (embed (edot (pembed v (nth j (elts h)) e f) x e) phi e f)))))
  :hints (("Goal" :use (esol0p-pembed-13
                        (:instance elistnp-pembed (x v) (phi (comp-auto (inv-auto phi e f) (nth i (elts h)) e f)))
			(:instance subgroupp-subsetp (g (autos e f)) (x (comp-auto (inv-auto phi e f) (nth i (elts h)) e f)))
			(:instance subgroupp-subsetp (g (autos e f)) (x phi))
                        (:instance edot-pembed (x (pembed v (comp-auto (inv-auto phi e f) (nth i (car h)) e f) e f)) (y x))))))

(defthm elistnp-len
  (implies (and (elistnp x n e) (natp n))
           (equal (len x) n)))

(local-defthm len-car-emat
  (implies (and (fieldp e) (ematp a m n e) (posp m) (posp n))
           (equal (len (car a)) n))
  :hints (("Goal" :expand ((EMATP A M N E)))))

(defthm len-ematp
  (implies (and (ematp a m n e) (natp m))
           (equal (len a) m))
  :hints (("Goal" :in-theory (enable ematp))))

(local-defthmd esol0p-pembed-15
  (implies (and (extensionp e f) (natp n) (elistnp v n e) (subgroupp h (autos e f)) (posp n) (esol0p x (embed-mat v h e f) e))
           (and (elistnp x n e)
	        (equal (emat* (embed-mat v h e f) (col-mat x) e)
		       (col-mat (elistn0 (order h) e)))))
  :hints (("Goal" :in-theory (e/d (esol0p esolutionp) (edot))
                  :use (ematp-embed-mat
		        (:instance order-pos (g h))
		        (:instance len-car-emat (a (embed-mat v h e f)) (m (order h)))))))

(local-defthmd esol0p-pembed-16
  (implies (and (extensionp e f) (elistnp v n e) (subgroupp h (autos e f)) (posp n) (esol0p x (embed-mat v h e f) e))
	   (elistnp x n e))
  :hints (("Goal" :use (esol0p-pembed-15 esol0p-pembed-8
                        (:instance esol0p-pembed-9 (m (order h)))))))

(local-defthmd esol0p-pembed-17
  (implies (and (extensionp e f) (elistnp v n e) (subgroupp h (autos e f)) (posp n) (esol0p x (embed-mat v h e f) e)
                (natp i) (< i (order h)))
	   (equal (edot (pembed v (nth i (elts h)) e f) x e)
		  (fzero e)))
  :hints (("Goal" :use (esol0p-pembed-15 esol0p-pembed-8
                        (:instance esol0p-pembed-9 (m (order h)))))))

(local-defthmd esol0p-pembed-18
  (implies (and (extensionp e f) (elistnp v n e) (subgroupp h (autos e f)) (in phi h) (posp n) (esol0p x (embed-mat v h e f) e)
                (natp i) (< i (order h)))
	   (equal (edot (pembed v (nth i (elts h)) e f) (pembed x phi e f) e)
	          (fzero e)))
  :hints (("Goal" :in-theory (enable embed-fzero-fone)
                  :use (esol0p-pembed-14 esol0p-pembed-16
			(:instance subgroupp-subsetp (g (autos e f)) (x phi))
                        (:instance esol0p-pembed-17 (i (ind (comp-auto (inv-auto phi e f) (nth i (elts h)) e f) h)))))))

(local-defthm esol0p-pembed-19
  (implies (and (extensionp e f) (posp n) (elistnp v n e) (subgroupp h (autos e f)) (in phi h) (esol0p x (embed-mat v h e f) e)
                (natp i) (< i (order h)))
           (equal (entry i 0 (emat* (embed-mat v h e f) (col-mat (pembed x phi e f)) e))
	          (fzero e)))
  :hints (("Goal" :use (esol0p-pembed-10 esol0p-pembed-16 esol0p-pembed-18
			(:instance subgroupp-subsetp (g (autos e f)) (x phi))))))

(local-defthm esol0p-pembed-20
  (implies (and (extensionp e f) (posp n) (elistnp x n e))
           (ematp (col-mat x) n 1 e))
  :hints (("Goal" :in-theory (enable col-mat row-mat)
                  :use (esol0p-pembed-5
		        (:instance ematp-transpose (a (list x)) (m 1))))))

(local-defthm esol0p-pembed-21
  (implies (and (extensionp e f) (posp n) (elistnp v n e) (subgroupp h (autos e f)) (in phi h) (elistnp x n e))
           (ematp (emat* (embed-mat v h e f) (col-mat x) e) (order h) 1 e))
  :hints (("Goal" :use (esol0p-pembed-20 ematp-embed-mat
                        (:instance order-pos (g h))
                        (:instance ematp-emat* (a (embed-mat v h e f)) (b (col-mat x)) (m (order h)) (p 1))))))

(local-defthm esol0p-pembed-22
  (implies (and (extensionp e f) (posp n) (elistnp v n e) (subgroupp h (autos e f)) (in phi h) (esol0p x (embed-mat v h e f) e))
           (and (elistnp (pembed x phi e f) n e)
                (equal (emat* (embed-mat v h e f) (col-mat (pembed x phi e f)) e)
	               (col-mat (elistn0 (order h) e)))))
  :hints (("Goal" :use (esol0p-pembed-16 elistnp-pembed
                        (:instance order-pos (g h))
                        (:instance subgroupp-subsetp (g (autos e f)) (x phi))
			(:instance esol0p-pembed-21 (x (pembed x phi e f)))
			(:instance esol0p-pembed-20 (x (elistn0 (order h) e)) (n (order h)))
                        (:instance esol0p-pembed-9 (m (order h)) (i (car (entry-diff (emat* (embed-mat v h e f) (col-mat (pembed x phi e f)) e) (col-mat (elistn0 (order h) e))))))
                        (:instance esol0p-pembed-19 (i (car (entry-diff (emat* (embed-mat v h e f) (col-mat (pembed x phi e f)) e) (col-mat (elistn0 (order h) e))))))
			(:instance emat-entry-diff-lemma (m (order h)) (n 1)
			                                 (a (emat* (embed-mat v h e f) (col-mat (pembed x phi e f)) e))
							 (b (col-mat (elistn0 (order h) e))))))))

(defthm esol0p-pembed
  (implies (and (extensionp e f) (posp n) (elistnp v n e) (subgroupp h (autos e f)) (in phi h) (esol0p x (embed-mat v h e f) e))
           (esol0p (pembed x phi e f) (embed-mat v h e f) e))
  :hints (("Goal" :in-theory (enable esolutionp esol0p)
                  :use (esol0p-pembed-22 ematp-embed-mat
		        (:instance len-car-emat (a (embed-mat v h e f)) (m (order h)))
                        (:instance order-pos (g h))))))

;; Count the number of nonzero entries of an elist:

(defun elist-zeroes-aux (x n e)
  (if (consp x)
      (if (equal (car x) (fzero e))
          (cons n (elist-zeroes-aux (cdr x) (1+ n) e))
	(elist-zeroes-aux (cdr x) (1+ n) e))
    ()))

(defthm member-elist-zeroes-aux
  (implies (natp n)
           (iff (member k (elist-zeroes-aux x n e))
	        (and (natp k)
		     (>= k n)
		     (< k (+ n (len x)))
		     (equal (nth (- k n) x) (fzero e))))))

(defthm dlistp-elist-zeroes-aux
  (implies (natp n) (dlistp (elist-zeroes-aux x n e))))

(defthmd elist-zeroes-aux-bound
  (<= (len (elist-zeroes-aux x n e)) (len x)))

(defund elist-zeroes (x e)
  (elist-zeroes-aux x 0 e))

(defthmd member-elist-zeroes
  (iff (member k (elist-zeroes x e))
       (and (natp k)
            (< k (len x))
	    (equal (nth k x) (fzero e))))
  :hints (("Goal" :in-theory (enable elist-zeroes))))

(defthm dlistp-elist-zeroes
  (dlistp (elist-zeroes x e))
  :hints (("Goal" :in-theory (enable elist-zeroes))))
  
(defthmd elist-zeroes-bound
  (<= (len (elist-zeroes x e)) (len x))
  :hints (("Goal" :in-theory (enable elist-zeroes)
                  :use ((:instance elist-zeroes-aux-bound (n 0))))))

(defun count-elist-zeroes (x e)
  (if (consp x)
      (if (equal (car x) (fzero e))
          (1+ (count-elist-zeroes (cdr x) e))
	(count-elist-zeroes (cdr x) e))
    0))

(defthm len-elist-zeroes-aux
  (equal (len (elist-zeroes-aux x n e))
         (count-elist-zeroes x e)))

(defthmd len-elist-zeroes
  (equal (len (elist-zeroes x e))
         (count-elist-zeroes x e))
  :hints (("Goal" :in-theory (enable elist-zeroes))))
  
;; If x is a nontrivial solution, then the following locates its first nonzero entry:

(defun first-nonzero-entry (x e)
  (if (consp x)
      (if (equal (car x) (fzero e))
          (1+ (first-nonzero-entry (cdr x) e))
	0)
    ()))

;; If x is not lifted from k, then the following locates its first unlifted entry:

(defun first-unlifted (x k e)
  (if (consp x)
      (if (fliftedp (car x) k e)
          (1+ (first-unlifted (cdr x) k e))
	0)
    ()))

;; If x is a nontrivial solution, then the following multiplies x by the reciprocal of its first nonzero entry:

(defund coerce-entry-to-1 (x e)
  (let ((i (first-nonzero-entry x e)))
    (elist-scalar-mul (frecip (nth i x) e) x e)))           

(local-defthmd zi-1
  (implies (and (fieldp e) (elistnp x n e) (natp n) (not (elist0p x e)))
           (let ((i (first-nonzero-entry x e)))
	     (and (natp i) (< i n) (feltp (nth i x) e) (not (equal (nth i x) (fzero e)))))))

(local-defthmd zi-2
  (implies (and (fieldp e) (elistnp x n e) (natp n) (not (elist0p x e))
                (feltp c e) (not (equal c (fzero e))))
	   (let ((x1 (elist-scalar-mul c x e)))
	     (and (not (elist0p x1 e))
	          (equal (nth (first-nonzero-entry x1 e) x1)
		         (fmul c (nth (first-nonzero-entry x e) x) e)))))
  :hints (("Subgoal *1/1" :use ((:instance field-integral-domain (f e) (x c) (y (car x)))))))

(local-defthmd zi-3a
  (implies (and (fieldp e) (elistnp x n e) (natp n)
                (feltp c e) (not (equal c (fzero e))))
	   (let ((x1 (elist-scalar-mul c x e)))
	     (equal (count-elist-zeroes x1 e)
	            (count-elist-zeroes x e))))
  :hints (("Subgoal *1/8" :use ((:instance field-integral-domain (f e) (x c) (y (car x)))))))

(local-defthmd zi-3
  (implies (and (fieldp e) (elistnp x n e) (natp n)
                (feltp c e) (not (equal c (fzero e))))
	   (let ((x1 (elist-scalar-mul c x e)))
	     (equal (len (elist-zeroes x1 e))
	            (len (elist-zeroes x e)))))
  :hints (("Goal" :use (zi-3a) :in-theory (enable len-elist-zeroes))))

(local-defthmd esol0p-elistnp
  (implies (and (fieldp e) (posp m) (posp n) (ematp a m n e)
                (esol0p x a e))
	   (elistnp x n e))
  :hints (("Goal" :in-theory (enable esol0p)
                  :use (len-car-emat))))

(defthmd first-nonzero-is-1
  (implies (and (fieldp e) (posp m) (posp n) (ematp a m n e)
                (esol0p x a e) (not (elist0p x e)))
	   (let ((x1 (coerce-entry-to-1 x e)))
	     (and (esol0p x1 a e)
	          (not (elist0p x1 e))
		  (equal (len (elist-zeroes x1 e))
		         (len (elist-zeroes x e)))
		  (equal (nth (first-nonzero-entry x1 e) x1)
		         (fone e)))))
  :hints (("Goal" :in-theory (enable coerce-entry-to-1)
                  :use (zi-1 esol0p-elistnp
		        (:instance frecip-not-fzero (f e) (x (nth (first-nonzero-entry x e) x)))
		        (:instance zi-2 (c (frecip (nth (first-nonzero-entry x e) x) e)))
		        (:instance zi-3 (c (frecip (nth (first-nonzero-entry x e) x) e)))
			(:instance esol0p-scalar-mul (c (frecip (nth (first-nonzero-entry x e) x) e)))))))

;; Let x be a nontrivial solution.  We shall by show induction on the number of nonzero entries of x that there 
;; exists a nontrivial solution that is lifted from k.  Let x' = (coerce-entry-to-1 x e).  We may assume that 
;; x' is not lifted from k.  The first nonzero entry of x' is 1.  We shall construct a nontrivial  solution
;; with more zeroes than x as follows.  Let (nth j x') be the first entry of x' that is not lifted from k.  For
;; some phi in h, (embed (nth j x') phi e f) != (nth j x').  Let

;;     x" = (elist-add x' (elist-scalar-mul (fneg (fone e) e) (pembed x' phi e f)) e).

;; By esol0p-pembed, esol0p-fadd, and esol0p-fmul, x" is a solution.  Since

;;     (nth j x") = (nth j x') + (fneg (fone e) e) * (embed (nth j x') phi e f) != 0,

;; x" is nontrivial.  All zeroes of x are also zeroes of x", and in addition, (nth i x") = 0.  Thus, x" has
;; more zeroes than x.

(defund increase-zeroes (x h e k f)
  (let* ((j (first-unlifted x k e))
	 (phi (fixedp-cex (nth j x) h e f)))
    (elist-add x (elist-scalar-mul (fneg (fone e) e) (pembed x phi e f) e) e)))

(local-defthmd zi-4
  (implies (and (extensionp e k) (elistnp x n e) (natp n) (not (pliftedp x k e)))
           (let ((j (first-unlifted x k e)))
	     (and (natp j) (< j n) (feltp (nth j x) e) (not (fliftedp (nth j x) k e))))))

(local-defthmd zi-5
  (implies (and (extensionp e k) (subgroupp h (autos e f)) (fixed-field-p k h e f) (feltp x e) (not (fliftedp x k e)))
           (let ((phi (fixedp-cex x h e f)))
	     (and (in phi h)
	          (not (equal (embed x phi e f) x)))))
  :hints (("Goal" :use (fixedp-cex-lemma fixed-field-p-lemma))))

(local-defthmd zi-6
  (implies (and (extensionp e k) (subgroupp h (autos e f)) (fixed-field-p k h e f)
                (elistnp x n e) (natp n) (not (pliftedp x k e)))
           (let* ((j (first-unlifted x k e))
	          (phi (fixedp-cex (nth j x) h e f)))
	     (and (natp j) (< j n)
	          (in phi h)
	          (feltp (nth j x) e)
	          (not (equal (embed (nth j x) phi e f) (nth j x))))))
  :hints (("Goal" :use (zi-4 (:instance zi-5 (x (nth (first-unlifted x k e) x)))))))

(local-defthm zi-7
  (implies (and (extensionp e f) (extensionp e k) (extensionp k f)
                (subgroupp h (autos e f)) (fixed-field-p k h e f)
                (posp n) (elistnp v n e)
		(esol0p x (embed-mat v h e f) e)
		(not (pliftedp x k e)))
           (esol0p (increase-zeroes x h e k f) (embed-mat v h e f) e))
  :hints (("Goal" :in-theory (enable increase-zeroes)
                  :use (ematp-embed-mat zi-4
		        (:instance esol0p-pembed (phi (fixedp-cex (nth (first-unlifted x k e) x) h e f)))
			(:instance zi-5 (x (nth (first-unlifted x k e) x)))
			(:instance order-pos (g h))
			(:instance esol0p-elistnp (m (order h)) (a (embed-mat v h e f)))
		        (:instance esol0p-scalar-mul (a (embed-mat v h e f)) (m (order h))
			                             (x (pembed x (fixedp-cex (nth (first-unlifted x k e) x) h e f) e f)) (c (fneg (fone e) e)))
			(:instance esol0p-fadd (a (embed-mat v h e f)) (m (order h))
			                      (y (elist-scalar-mul (fneg (fone e) e)
					                           (pembed x (fixedp-cex (nth (first-unlifted x k e) x) h e f) e f)
								   e)))))))

(local-defthmd zi-8
  (implies (and (fieldp e) (elistnp x n e) (feltp c e) (natp n) (natp i) (< i n))
           (equal (nth i (elist-scalar-mul c x e))
	          (fmul c (nth i x) e))))

(local-defthmd zi-9
  (implies (and (fieldp e) (elistnp x n e) (elistnp y n e) (natp n) (natp i) (< i n))
           (equal (nth i (elist-add x y e))
	          (fadd (nth i x) (nth i y) e))))

(local-defthm zi-10
  (implies (and (extensionp e f) (elistnp x n e) (natp n) (autop phi e f) (natp i) (< i n))
           (equal (nth i (pembed x phi e f))
	          (embed (nth i x) phi e f))))

(defthm elistnp-elist-scalar-mul
  (implies (and (fieldp e) (elistnp x n e) (natp n) (feltp c e))
           (elistnp (elist-scalar-mul c x e) n e)))

(local-defthm zi-11
  (implies (and (extensionp e f) (extensionp e k) (extensionp k f)
                (subgroupp h (autos e f)) (fixed-field-p k h e f)
                (posp n) (elistnp v n e)
		(esol0p x (embed-mat v h e f) e)
		(not (pliftedp x k e))
		(natp i) (< i n))
           (equal (nth i (increase-zeroes x h e k f))
	          (fadd (nth i x) (fmul (fneg (fone e) e) (embed (nth i x) (fixedp-cex (nth (first-unlifted x k e) x) h e f) e f) e) e)))
  :hints (("Goal" :in-theory (enable zi-8 zi-9 increase-zeroes)
                  :use (ematp-embed-mat zi-4
                        (:instance subgroupp-subsetp (g (autos e f)) (x (FIXEDP-CEX (NTH (FIRST-UNLIFTED X K E) X) H E F)))
			(:instance zi-5 (x (nth (first-unlifted x k e) x)))
			(:instance order-pos (g h))
			(:instance zi-9 (y (ELIST-SCALAR-MUL (FNEG (FONE E) E) (PEMBED X (FIXEDP-CEX (NTH (FIRST-UNLIFTED X K E) X) H E F) e f) e)))
			(:instance zi-8 (c (FNEG (FONE E) E))
			                (x (PEMBED X (FIXEDP-CEX (NTH (FIRST-UNLIFTED X K E) X) H E F) E F)))
			(:instance esol0p-elistnp (m (order h)) (a (embed-mat v h e f)))))))

(local-defthm zi-12
  (implies (and (extensionp e f) (extensionp e k) (extensionp k f)
                (subgroupp h (autos e f)) (fixed-field-p k h e f)
                (posp n) (elistnp v n e)
		(esol0p x (embed-mat v h e f) e)
		(not (pliftedp x k e))
		(natp i) (< i n)
		(equal (nth i x) (fzero e)))
           (equal (nth i (increase-zeroes x h e k f))
                  (fzero e)))
  :hints (("Goal" :use (ematp-embed-mat zi-6
			(:instance order-pos (g h))
                        (:instance subgroupp-subsetp (g (autos e f)) (x (FIXEDP-CEX (NTH (FIRST-UNLIFTED X K E) X) H E F)))
			(:instance esol0p-elistnp (m (order h)) (a (embed-mat v h e f)))))))

(local-defthmd zi-13
  (implies (and (extensionp e f) (extensionp e k) (extensionp k f)
                (subgroupp h (autos e f)) (fixed-field-p k h e f)
                (posp n) (elistnp v n e)
		(esol0p x (embed-mat v h e f) e)
		(not (pliftedp x k e)))
	   (let ((i (first-unlifted x k e)))
	      (and (natp i) (< i n)
	           (feltp (nth i x) e)
		   (feltp (embed (nth i x) (fixedp-cex (nth (first-unlifted x k e) x) h e f) e f) e)
		   (not (equal (embed (nth i x) (fixedp-cex (nth (first-unlifted x k e) x) h e f) e f)
		               (nth i x)))
	           (equal (nth i (increase-zeroes x h e k f))
	                  (fadd (nth i x)
			        (fmul (fneg (fone e) e)
				      (embed (nth i x) (fixedp-cex (nth (first-unlifted x k e) x) h e f) e f)
				      e)
				e)))))
  :hints (("Goal" :use (ematp-embed-mat zi-6
			(:instance order-pos (g h))
                        (:instance subgroupp-subsetp (g (autos e f)) (x (FIXEDP-CEX (NTH (FIRST-UNLIFTED X K E) X) H E F)))
			(:instance esol0p-elistnp (m (order h)) (a (embed-mat v h e f)))))))

(local-defthm zi-14
  (implies (and (fieldp e) (feltp x e) (feltp y e)
                (equal (fadd x (fmul (fneg (fone e) e) y e) e)
		       (fzero e)))
	   (equal x y))
  :rule-classes ()
  :hints (("Goal" :use ((:instance fadd-assoc (f e) (y (fmul (fneg (fone e) e) y e)) (z y))
                        (:instance fdistrib-comm (f e) (y (fneg (fone e) e)) (z (fone e)) (x y))))))

(local-defthm zi-15
  (implies (and (extensionp e f) (extensionp e k) (extensionp k f)
                (subgroupp h (autos e f)) (fixed-field-p k h e f)
                (posp n) (elistnp v n e)
		(esol0p x (embed-mat v h e f) e)
		(not (pliftedp x k e)))
	   (let ((i (first-unlifted x k e)))
	      (and (natp i) (< i n)
                   (not (equal (nth i (increase-zeroes x h e k f)) (fzero e))))))
  :hints (("Goal" :use (zi-13
                        (:instance zi-14 (x (nth (first-unlifted x k e) x))
			                 (y (embed (nth (first-unlifted x k e) x) (fixedp-cex (nth (first-unlifted x k e) x) h e f) e f)))))))

(local-defthmd zi-16
  (implies (and (fieldp e) (elistnp x n e) (elist0p x e) (natp n) (natp i) (< i n))
           (equal (nth i x) (fzero e))))

(local-defthm zi-17
  (implies (and (extensionp e f) (extensionp e k) (extensionp k f)
                (subgroupp h (autos e f)) (fixed-field-p k h e f)
                (posp n) (elistnp v n e)
		(esol0p x (embed-mat v h e f) e)
		(not (pliftedp x k e)))
           (not (elist0p (increase-zeroes x h e k f) e)))
  :hints (("Goal" :in-theory (disable zi-7 zi-11 zi-15)
                  :use (zi-6 zi-15 zi-7 ematp-embed-mat
                        (:instance zi-16 (x (increase-zeroes x h e k f)) (i (first-unlifted x k e)))
			(:instance order-pos (g h))
                        (:instance subgroupp-subsetp (g (autos e f)) (x (FIXEDP-CEX (NTH (FIRST-UNLIFTED X K E) X) H E F)))
			(:instance esol0p-elistnp (x (increase-zeroes x h e k f)) (m (order h)) (a (embed-mat v h e f)))))))

(local-defthm zi-18
  (implies (and (extensionp e f) (extensionp e k) (extensionp k f)
                (subgroupp h (autos e f)) (fixed-field-p k h e f)
                (posp n) (elistnp v n e)
		(esol0p x (embed-mat v h e f) e)
		(not (pliftedp x k e)))
	   (elistnp (increase-zeroes x h e k f) n e))
  :hints (("Goal" :in-theory (disable zi-7 zi-11 zi-15)
                  :use (zi-6 zi-15 zi-7 ematp-embed-mat
                        (:instance zi-16 (x (increase-zeroes x h e k f)) (i (first-unlifted x k e)))
			(:instance order-pos (g h))
                        (:instance subgroupp-subsetp (g (autos e f)) (x (FIXEDP-CEX (NTH (FIRST-UNLIFTED X K E) X) H E F)))
			(:instance esol0p-elistnp (x (increase-zeroes x h e k f)) (m (order h)) (a (embed-mat v h e f)))))))

(local-defthm zi-19
  (implies (and (extensionp e f) (extensionp e k) (extensionp k f)
                (subgroupp h (autos e f)) (fixed-field-p k h e f)
                (posp n) (elistnp v n e)
		(esol0p x (embed-mat v h e f) e)
		(not (pliftedp x k e)))
	   (elistnp x n e))
  :hints (("Goal" :in-theory (disable zi-7 zi-11 zi-15)
                  :use (zi-6 zi-15 zi-7 ematp-embed-mat
			(:instance order-pos (g h))
                        (:instance subgroupp-subsetp (g (autos e f)) (x (FIXEDP-CEX (NTH (FIRST-UNLIFTED X K E) X) H E F)))
			(:instance esol0p-elistnp (m (order h)) (a (embed-mat v h e f)))))))


(local-defthmd zi-20
  (implies (and (fieldp e) (natp n) (elistnp x n e))
           (equal (len x) n)))

(local-defthm zi-21
  (implies (and (extensionp e f) (extensionp e k) (extensionp k f)
                (subgroupp h (autos e f)) (fixed-field-p k h e f)
                (posp n) (elistnp v n e)
		(esol0p x (embed-mat v h e f) e)
		(not (pliftedp x k e))
		(member z (elist-zeroes x e)))
           (member z (elist-zeroes (increase-zeroes x h e k f) e)))
  :hints (("Goal" :use (zi-18 zi-19 zi-20 
                        (:instance zi-20 (x (increase-zeroes x h e k f)))
			(:instance member-elist-zeroes (k z))
			(:instance member-elist-zeroes (k z) (x (increase-zeroes x h e k f)))
			(:instance zi-12 (i k))))))

(local-defthm zi-22
  (implies (and (extensionp e f) (extensionp e k) (extensionp k f)
                (subgroupp h (autos e f)) (fixed-field-p k h e f)
                (posp n) (elistnp v n e)
		(esol0p x (embed-mat v h e f) e)
		(not (pliftedp x k e)))
	   (sublistp  (elist-zeroes x e)
                      (elist-zeroes (increase-zeroes x h e k f) e)))
  :hints (("Goal" :use ((:instance scex1-lemma (l (elist-zeroes x e)) (m (elist-zeroes (increase-zeroes x h e k f) e)))
                        (:instance zi-21 (z (scex1 (elist-zeroes x e) (elist-zeroes (increase-zeroes x h e k f) e))))))))

(local-defthm zi-23
  (implies (and (extensionp e f) (extensionp e k) (extensionp k f)
                (subgroupp h (autos e f)) (fixed-field-p k h e f)
                (posp n) (elistnp v n e)
		(esol0p x (embed-mat v h e f) e)
		(not (pliftedp x k e)))
	   (EQUAL (FADD (FONE E)
                        (FMUL (FNEG (FONE E) E)
                              (EMBED (FONE E)
                                     (FIXEDP-CEX (NTH (FIRST-UNLIFTED X K E) X) H E F)
                                     E F)
                              E)
                        E)
                  (FZERO E)))
  :hints (("Goal" :use (zi-6 zi-15 zi-19 zi-7 ematp-embed-mat
			(:instance order-pos (g h))
                        (:instance subgroupp-subsetp (g (autos e f)) (x (FIXEDP-CEX (NTH (FIRST-UNLIFTED X K E) X) H E F)))
			(:instance embed-fzero-fone (k e) (phi (FIXEDP-CEX (NTH (FIRST-UNLIFTED X K E) X) H E F)))))))

(local-defthm zi-24
  (implies (and (extensionp e f) (extensionp e k) (extensionp k f)
                (subgroupp h (autos e f)) (fixed-field-p k h e f)
                (posp n) (elistnp v n e)
		(esol0p x (embed-mat v h e f) e)
		(not (elist0p x e))
		(not (pliftedp x k e))
		(equal (nth (first-nonzero-entry x e) x) (fone e)))
	   (and (member (first-nonzero-entry x e) (elist-zeroes (increase-zeroes x h e k f) e))
	        (not (member (first-nonzero-entry x e) (elist-zeroes x e)))))
  :hints (("Goal" :use (zi-1 zi-19
                        (:instance zi-20 (x (increase-zeroes x h e k f)))
                        (:instance fone-fzero (f e))
                        (:instance member-elist-zeroes (k (first-nonzero-entry x e)))
			(:instance member-elist-zeroes (k (first-nonzero-entry x e)) (x (increase-zeroes x h e k f)))))))

(local-defthm zi-25
  (implies (and (extensionp e f) (extensionp e k) (extensionp k f)
                (subgroupp h (autos e f))
		(fixed-field-p k h e f)
                (posp n) (elistnp v n e)
		(esol0p x (embed-mat v h e f) e)
		(not (elist0p x e))
		(not (pliftedp x k e))
		(equal (nth (first-nonzero-entry x e) x) (fone e)))
	   (> (len (elist-zeroes (increase-zeroes x h e k f) e))
	      (len (elist-zeroes x e))))
  :hints (("Goal" :use (zi-22 zi-24 elist-zeroes-bound
                        (:instance len-proper-sublist (l (elist-zeroes x e)) (m (elist-zeroes (increase-zeroes x h e k f) e)) (x (first-nonzero-entry x e)))))))

(defthmd esol0p-coerce-entry-to-1
  (implies (and (extensionp e f) (posp n) (elistnp v n e)
                (subgroupp h (autos e f))
                (esol0p x (embed-mat v h e f) e) (not (elist0p x e)))
	   (let ((x1 (coerce-entry-to-1 x e)))
	     (and (esol0p x1 (embed-mat v h e f) e)
	          (not (elist0p x1 e))
		  (equal (len (elist-zeroes x1 e))
		         (len (elist-zeroes x e)))
		  (equal (nth (first-nonzero-entry x1 e) x1)
		         (fone e)))))
  :hints (("Goal" :use (ematp-embed-mat
			(:instance order-pos (g h))
			(:instance first-nonzero-is-1 (m (order h)) (a (embed-mat v h e f)))))))

(defthmd zeroes-increase
  (implies (and (extensionp e k) (extensionp k f)
                (subgroupp h (autos e f))
		(fixed-field-p k h e f)
		(posp n)
	        (elistnp v n e)
                (esol0p x (embed-mat v h e f) e)
	        (not (elist0p x e))
		(not (pliftedp x k e))
		(equal (nth (first-nonzero-entry x e) x) (fone e)))
	   (let ((y (increase-zeroes x h e k f)))
	     (and (esol0p y (embed-mat v h e f) e)
	          (not (elist0p y e))
		  (<= (len (elist-zeroes y e)) n)
		  (> (len (elist-zeroes y e))
		     (len (elist-zeroes x e))))))
  :hints (("Goal" :use (zi-7 zi-17 zi-25 zi-18
                        (:instance elist-zeroes-bound (x (increase-zeroes x h e k f)))
			(:instance zi-20 (x (increase-zeroes x h e k f)))
                        (:instance extends-trans (d k))))))

;; The desired solution is computed recursively:

(defun plifted-solution-aux (x v n h e k f)
  (declare (xargs :measure (nfix (- n (len (elist-zeroes x e))))
                  :hints (("Goal" :use (esol0p-coerce-entry-to-1
		                        (:instance zeroes-increase (x (coerce-entry-to-1 x e))))))))
  (if (and (extensionp e f) (extensionp e k) (extensionp k f)
           (subgroupp h (autos e f))
	   (fixed-field-p k h e f)
	   (natp n) (> n (order h))
	   (elistnp v n e)
           (esol0p x (embed-mat v h e f) e)
	   (not (elist0p x e)))
      (let ((x1 (coerce-entry-to-1 x e)))
        (if (pliftedp x1 k e)
            x1
          (plifted-solution-aux (increase-zeroes x1 h e k f) v n h e k f)))
    ()))

(defund plifted-solution (v h e k f)
  (plifted-solution-aux (nontrivial-esol0p-witness (embed-mat v h e f) e) v (len v) h e k f))

;; The following is proved by induction on the number of nonzero entries of x:

(defthmd pliftedp-plifted-solution-aux
  (implies (and (extensionp e k) (extensionp k f)
                (subgroupp h (autos e f))
	        (fixed-field-p k h e f)
	        (natp n) (> n (order h))
                (elistnp v n e)
                (esol0p x (embed-mat v h e f) e)
	        (not (elist0p x e)))
      (let ((x1 (plifted-solution-aux x v n h e k f)))
        (and (esol0p x1 (embed-mat v h e f) e)
	     (not (elist0p x1 e))
	     (pliftedp x1 k e))))
  :hints (("Goal" :induct (plifted-solution-aux x v n h e k f))
          ("Subgoal *1/3" :use ((:instance extends-trans (d k))))
	  ("Subgoal *1/2" :use (zi-19 esol0p-coerce-entry-to-1
		                (:instance zeroes-increase (x (coerce-entry-to-1 x e)))))
	  ("Subgoal *1/1" :use (zi-19 esol0p-coerce-entry-to-1))))

;; By exists-esol0p, (nontrivial-esol0p-witness (embed-mat v h e f) e) satisfies the hypothesis, and therefore
;; we have

(defthmd pliftedp-plifted-solution
  (implies (and (extensionp e k) (extensionp k f)
                (subgroupp h (autos e f))
	        (fixed-field-p k h e f)
	        (posp n) (> n (order h))
                (elistnp v n e))
	   (let ((x (plifted-solution v h e k f)))
             (and (esol0p x (embed-mat v h e f) e)
	          (not (elist0p x e))
	          (pliftedp x k e))))
  :hints (("Goal" :in-theory (enable plifted-solution)
                  :use (ematp-embed-mat
			(:instance order-pos (g h))
			(:instance extends-trans (d k))
			(:instance pliftedp-plifted-solution-aux (x (nontrivial-esol0p-witness (embed-mat v h e f) e)))
		        (:instance exists-esol0p (a (embed-mat v h e f)) (m (order h)))))))

;; We instantiate this result with v = (ebasis0 e k), the canonical basis of e as a vector space over k, and
;; n = (len v) = (edegree e k).  We shall assume n > (order h) and derive a contradiction.  The conclusion
;; of the lemma holds for x = (plifted-solution v h e k f).  Let c = (pdrop x e k).  Then x = (plift c k e),
;; (elistnp c n k), and (not (elistn0p c k)).  Let a = (embed-mat v h e f).  Since (esol0p x a e),

;;     (emat* a (col-mat x) e) = (elistn0 m e)

;; and in particular,

;;     (car (emat* a (col-mat x) e)) = (edot (car a) x e) = 0

;; where

;;    (car a) = (pembed v (car (elts h)) e f) = v.

;; Thus, (ecomb c v e) = (edot v x e) = 0, contradicting ebasis0-lin-indep.

(local-defthmd artin-1
  (implies (and (extensionp e k) (extensionp k f)
                (subgroupp h (autos e f))
	        (fixed-field-p k h e f)
	        (> (edegree e k) (order h)))
	   (let ((x (plifted-solution (ebasis0 e k) h e k f)))
             (and (esol0p x (embed-mat (ebasis0 e k) h e f) e)
	          (not (elist0p x e))
	          (pliftedp x k e))))
  :hints (("Goal" :use ((:instance pliftedp-plifted-solution (v (ebasis0 e k)) (n (edegree e k)))
                        (:instance elistnp-ebasis0 (f k))))))

(local-defthmd artin-2
  (implies (and (extensionp e k) (extensionp k f)
                (subgroupp h (autos e f))
	        (fixed-field-p k h e f)
	        (> (edegree e k) (order h)))
	   (let ((x (plifted-solution (ebasis0 e k) h e k f)))
	     (elistnp x (edegree e k) e)))
  :hints (("Goal" :use (artin-1
                        (:instance ematp-embed-mat (v (ebasis0 e k)) (n (edegree e k)))
			(:instance extends-trans (d k))
			(:instance order-pos (g h))
			(:instance  esol0p-elistnp (a (embed-mat (ebasis0 e k) h e f)) (n (edegree e k)) (m (order h)) (x (plifted-solution (ebasis0 e k) h e k f)))
                        (:instance pliftedp-plifted-solution (v (ebasis0 e k)) (n (edegree e k)))
                        (:instance elistnp-ebasis0 (f k))))))

(local-defthmd artin-3
  (implies (and (extensionp e k) (extensionp k f)
                (subgroupp h (autos e f))
	        (fixed-field-p k h e f)
	        (> (edegree e k) (order h)))
	   (let* ((x (plifted-solution (ebasis0 e k) h e k f))
	          (c (pdrop x e k)))
	     (and (feltsp c k)
	          (equal (plift c k e) x)
		  (equal (len c) (edegree e k)))))
  :hints (("Goal" :in-theory (disable elistnp-len)
                  :use (artin-1 artin-2
                        (:instance plift-pdrop-feltsp (p (plifted-solution (ebasis0 e k) h e k f)) (f k))
			(:instance elistnp-feltsp (l (plifted-solution (ebasis0 e k) h e k f)) (k (edegree e k)))
			(:instance len-elistnp (l (plifted-solution (ebasis0 e k) h e k f)) (k (edegree e k)))))))

(defthmd plift-elist0p
  (implies (and (extensionp e f) (elist0p x f))
           (elist0p (plift x f e) e)))

(defthm elist0p-elistn0
  (elist0p (elistn0 n e) e))

(local-defthmd artin-4
  (implies (and (extensionp e k) (extensionp k f)
                (subgroupp h (autos e f))
	        (fixed-field-p k h e f)
	        (> (edegree e k) (order h)))
	   (let* ((x (plifted-solution (ebasis0 e k) h e k f))
	          (c (pdrop x e k)))
	     (and (elistnp c (edegree e k) k)
	          (equal (plift c k e) x)
		  (not (equal (elistn0 (edegree e k) k) c)))))
  :hints (("Goal" :in-theory (enable feltsp-elistnp)
                  :use (artin-1 artin-3
		        (:instance plift-elist0p (f k) (x (pdrop (plifted-solution (ebasis0 e k) h e k f) e k)))))))

(local-defthmd artin-5
  (implies (and (extensionp e k) (extensionp k f)
                (subgroupp h (autos e f))
	        (fixed-field-p k h e f)
	        (> (edegree e k) (order h)))
	   (let* ((x (plifted-solution (ebasis0 e k) h e k f)))
             (equal (edot (pembed (ebasis0 e k) (caar h) e f) x e)
	            (fzero e))))
  :hints (("Goal" :use (artin-1 artin-2
			(:instance extends-trans (d k))
			(:instance order-pos (g h))
			(:instance elistnp-ebasis0 (f k))
                        (:instance esol0p-pembed-17 (i 0) (v (ebasis0 e k)) (n (edegree e k)) (x (plifted-solution (ebasis0 e k) h e k f)))))))

(local-defthmd artin-6
  (implies (and (extensionp e k) (extensionp k f)
                (subgroupp h (autos e f)))
	   (equal (caar h) (id-auto e f)))
  :hints (("Goal" :in-theory (enable e)
                  :use (autos-elts
		        (:instance extends-trans (d k))
		        (:instance subgroup-e (g (autos e f)))))))

(local-defthmd artin-7
  (implies (and (extensionp e k) (extensionp k f))
           (equal (pembed (ebasis0 e k) (id-auto e f) e f)
	          (ebasis0 e k)))
  :hints (("Goal" :in-theory (enable id-auto elistnp-feltsp)
                  :use ((:instance extends-trans (d k))
			(:instance elistnp-ebasis0 (f k))
			(:instance pembed-id-embedding-feltsp (p (ebasis0 e k)))))))

(local-defthmd artin-8
  (implies (and (extensionp e k) (extensionp k f)
                (subgroupp h (autos e f))
	        (fixed-field-p k h e f)
	        (> (edegree e k) (order h)))
	   (let* ((x (plifted-solution (ebasis0 e k) h e k f)))
             (equal (edot (ebasis0 e k) x e)
	            (fzero e))))
  :hints (("Goal" :use (artin-5 artin-6 artin-7))))

(local-defthmd artin-9
  (implies (and (extensionp e f)
                (elistnp c n f)
		(elistnp x n e))		
	   (equal (edot x (plift c f e) e)
	          (ecomb c x e f))))

(local-defthmd artin-10
  (implies (and (extensionp e k) (extensionp k f)
                (subgroupp h (autos e f))
	        (fixed-field-p k h e f)
	        (> (edegree e k) (order h)))
           (not (equal e k)))
  :hints (("Goal" :use ((:instance order-pos (g h))))))


(local-defthmd artin-11
  (implies (and (extensionp e k) (extensionp k f)
                (subgroupp h (autos e f))
	        (fixed-field-p k h e f)
	        (> (edegree e k) (order h)))
	   (let* ((x (plifted-solution (ebasis0 e k) h e k f))
	          (c (pdrop x e k)))
	     (and (not (equal e k))
	          (elistnp c (edegree e k) k)
	          (equal (ecomb c (ebasis0 e k) e k)
	                 (fzero e))
	          (not (equal (elistn0 (edegree e k) k)
	                      c)))))
  :hints (("Goal" :use (artin-10 artin-8 artin-4
			(:instance elistnp-ebasis0 (f k))
                        (:instance artin-9 (f k)
			                   (n (edegree e k))
			                   (x (ebasis0 e k))
			                   (c (pdrop (plifted-solution (ebasis0 e k) h e k f) e k)))))))

(defthmd artin-lemma
  (implies (and (extensionp e k) (extensionp k f)
                (subgroupp h (autos e f))
	        (fixed-field-p k h e f))
	   (<= (edegree e k) (order h)))
  :hints (("Goal" :use (artin-11
                        (:instance ebasis0-lin-indep (f k) (c (pdrop (plifted-solution (ebasis0 e k) h e k f) e k)))))))

;;---------------------------------------------------

;; The usual formulation of the fundamental theorem establishes to a 1-1 correspondence between the subgroups 
;; of g and the intermediate fields between e and f.  In our formalization, there is no guarantee that a 
;; given subgroup h is the galois subgroup corresponding to any of the fields that occur in the construction 
;; of e as an extension of f.  However, we can construct an extension k of f, an extension d of k, and an 
;; isomorphism phi from d to e over f such that h is the image of the galois subgroup of k under the galois
;; group isomorphism induced by phi, i.e.,

;;     (image (auto-map phi d e f) (galois-subgroup k d f) (galois e f)) = h.

;; The proof is based on functional instantiation of metafield-field, with the substitution of the predicate

;;     (lambda (x) (and (feltp x e) (fixedp x h e f)))

;; for the metafield m$.

;; Thus, we must show that this predicate recognizes a metafield:

(defthm fixedp-fadd
  (implies (and (extensionp e f) (galoisp e f) (subgroupp h (galois e f))
                (feltp x e) (fixedp x h e f)
                (feltp y e) (fixedp y h e f))
	   (and (feltp (fadd x y e) e) (fixedp (fadd x y e) h e f)))
  :hints (("Goal" :use ((:instance fixedp-cex-lemma (x (fadd x y e)))
                        (:instance subgroupp-sublistp (g (galois e f)))
			(:instance member-sublist (x (fixedp-cex (fadd x y e) h e f)) (l (elts h)) (m (elts (galois e f))))))))

(defthm fixedp-fmul
  (implies (and (extensionp e f) (galoisp e f) (subgroupp h (galois e f))
                (feltp x e) (fixedp x h e f)
                (feltp y e) (fixedp y h e f))
	   (and (feltp (fmul x y e) e) (fixedp (fmul x y e) h e f)))
  :hints (("Goal" :use ((:instance fixedp-cex-lemma (x (fmul x y e)))
                        (:instance subgroupp-sublistp (g (galois e f)))
			(:instance member-sublist (x (fixedp-cex (fmul x y e) h e f)) (l (elts h)) (m (elts (galois e f))))))))

(defthm fixedp-flift
  (implies (and (extensionp e f) (galoisp e f) (subgroupp h (galois e f))
                (feltp x f))
	   (fixedp (flift x f e) h e f))
  :hints (("Goal" :use ((:instance fixedp-cex-lemma (x (flift x f e)))
                        (:instance subgroupp-sublistp (g (galois e f)))
			(:instance member-sublist (x (fixedp-cex (flift x f e) h e f)) (l (elts h)) (m (elts (galois e f))))))))

(defun-sk range-includes-fixed (phi d h e f)
  (forall (y)
    (implies (and (feltp y e) (fixedp y h e f))
             (in-range-p y phi d e f))))

(defthmd range-includes-fixed-lemma
  (implies (and (range-includes-fixed phi d h e f)
                (feltp y e) (fixedp y h e f))
	   (in-range-p y phi d e f))	   
  :hints (("Goal" :use (range-includes-fixed-necc))))

(defthmd range-includes-fixed-witness-lemma
  (let ((y (range-includes-fixed-witness phi d h e f)))
    (implies (implies (and (feltp y e) (fixedp y h e f)) (in-range-p y phi d e f))
             (range-includes-fixed phi d h e f))))


(defmacro fixedp-mac ()
  '(and (extensionp e f) (galoisp e f) (subgroupp h (galois e f))))

(local-defthm extensionp-e$-f$-rewrite
  (and (fieldp (e$))
       (fieldp (f$))
       (extends (e$) (f$)))
  :hints (("Goal" :use (extensionp-e$-f$))))

(defthm extend-range-to-fixed-measure-decreases
  (implies (and (extensionp e f) (galoisp e f) (subgroupp h (galois e f))
                (extensionp d f)
                (embeddingp phi d e f)
		(feltp y e)
		(fixedp y h e f)
		(not (in-range-p y phi d e f)))
	   (and (posp (edegree d f))
	        (posp (edegree e f))
	        (< (edegree d f)
	           (edegree (cons (extension-poly y phi d e f) d) f))
	        (<= (edegree (cons (extension-poly y phi d e f) d) f)
	            (edegree e f))))
  :hints (("Goal" :use ((:functional-instance extend-range-to-m$-measure-decreases
                          (f$ (lambda () (if (fixedp-mac) f (f$))))
                          (e$ (lambda () (if (fixedp-mac) e (e$))))
                          (m$ (lambda (y) (if (fixedp-mac) (and (feltp y e) (fixedp y h e f)) (m$ y)))))))))

(defun extend-range-to-fixed (d phi h e f)
  (declare (xargs :measure (nfix (- (edegree e f) (edegree d f)))
                  :hints (("Goal" :nonlinearp t
		                  :use ((:instance extend-range-to-fixed-measure-decreases
				         (y (range-includes-fixed-witness phi d h e f))))))))
  (let* ((y (range-includes-fixed-witness phi d h e f))
         (q (extension-poly y phi d e f)))
    (if (and (extensionp e f) (galoisp e f) (subgroupp h (galois e f))
             (extensionp d f) (embeddingp phi d e f) (feltp y e) (fixedp y h e f) (not (in-range-p y phi d e f)))
        (extend-range-to-fixed (cons q d) (cons y phi) h e f)
      (mv d phi))))

(defthm extend-fixed-measure-decreases
  (implies (and (extensionp e f) (galoisp e f) (subgroupp h (galois e f))
                (extensionp d f)
                (embeddingp phi d e f)
		(feltp y e)
		(not (in-range-p y phi d e f)))
	   (and (posp (edegree d f))
	        (posp (edegree e f))
	        (< (edegree d f)
	           (edegree (cons (extension-poly y phi d e f) d) f))
	        (<= (edegree (cons (extension-poly y phi d e f) d) f)
	            (edegree e f))))
  :hints (("Goal" :use ((:functional-instance extend-to-isomorphism-measure-decreases
                          (f$ (lambda () (if (fixedp-mac) f (f$))))
                          (e$ (lambda () (if (fixedp-mac) e (e$))))			  
                          (m$ (lambda (y) (if (fixedp-mac) (and (feltp y e) (fixedp y h e f)) (m$ y)))))))))			  

(defun extend-fixed (d phi h e f)
  (declare (xargs :measure (nfix (- (edegree e f) (edegree d f)))
                  :hints (("Goal" :nonlinearp t
		                  :use ((:instance extend-fixed-measure-decreases
				          (y (range-includes-e-witness phi d e f))))))))
  (let* ((y (range-includes-e-witness phi d e f))
         (q (extension-poly y phi d e f)))
    (if (and (extensionp e f) (galoisp e f) (subgroupp h (galois e f))
             (extensionp d f) (embeddingp phi d e f) (feltp y e)
             (not (in-range-p y phi d e f)))
        (extend-fixed (cons q d) (cons y phi) h e f)
      (mv d phi))))

(defund k* (h e f) (mv-nth 0 (mv-list 2 (extend-range-to-fixed f () h e f))))

(defund psi* (h e f) (mv-nth 1 (mv-list 2 (extend-range-to-fixed f () h e f))))

(defund d* (h e f) (mv-nth 0 (mv-list 2 (extend-fixed (k* h e f) (psi* h e f) h e f))))

(defund phi* (h e f) (mv-nth 1 (mv-list 2 (extend-fixed (k* h e f) (psi* h e f) h e f))))

(in-theory (enable k* psi* d* phi* k$ psi$ d$ phi$))

(in-theory (enable range-includes-m$-lemma))

(defthmd fixed-field-1
  (implies (and (extensionp e f) (galoisp e f) (subgroupp h (galois e f)))
           (and (extensionp (d* h e f) (k* h e f)) (extensionp (k* h e f) f)
                (iso-embeddingp (phi* h e f) (d* h e f) e f)
                (implies (feltp x (d* h e f))
                         (iff (and (feltp (embed x (phi* h e f) e f) e)
			           (fixedp (embed x (phi* h e f) e f) h e f))
                              (fliftedp x (k* h e f) (d* h e f))))))
  :hints (("Goal" :use ((:functional-instance metafield-field
                          (f$ (lambda () (if (fixedp-mac) f (f$))))
                          (e$ (lambda () (if (fixedp-mac) e (e$))))			  
                          (m$ (lambda (y) (if (fixedp-mac) (and (feltp y e) (fixedp y h e f)) (m$ y))))
			  (range-includes-m$ (lambda (phi d) (if (fixedp-mac) (range-includes-fixed phi d h e f) (range-includes-m$ phi d))))
			  (range-includes-m$-witness (lambda (phi d) (if (fixedp-mac) (range-includes-fixed-witness phi d h e f)
			                                                 (range-includes-m$-witness phi d))))
			  (extend-range-to-m$ (lambda (d phi) (if (fixedp-mac) (extend-range-to-fixed d phi h e f) (extend-range-to-m$ d phi))))
			  (extend-to-isomorphism (lambda (d phi) (if (fixedp-mac) (extend-fixed d phi h e f) (extend-to-isomorphism d phi))))
			  (k$ (lambda () (if (fixedp-mac) (k* h e f) (k$))))
			  (psi$ (lambda () (if (fixedp-mac) (psi* h e f) (psi$))))
			  (d$ (lambda () (if (fixedp-mac) (d* h e f) (d$))))
			  (phi$ (lambda () (if (fixedp-mac) (phi* h e f) (phi$)))))))
	  ("Subgoal 5" :use (range-includes-fixed-witness-lemma range-includes-fixed-lemma))
	  ("Subgoal 4" :use (range-includes-m$-witness-lemma range-includes-m$-lemma))))

(in-theory (disable k* psi* d* phi* k$ psi$ d$ phi$))

(defthmd fixed-field
  (implies (and (extensionp e f) (galoisp e f) (subgroupp h (galois e f)))
           (and (extensionp (d* h e f) (k* h e f)) (extensionp (k* h e f) f)
                (iso-embeddingp (phi* h e f) (d* h e f) e f)
                (implies (feltp x (d* h e f))
                         (iff (fixedp (embed x (phi* h e f) e f) h e f)
                              (fliftedp x (k* h e f) (d* h e f))))))
  :hints (("Goal" :use (fixed-field-1
                        (:instance embed-image (phi (phi* h e f)) (e (d* h e f)) (k e))
			(:instance extends-trans (e (d* h e f)) (d (k* h e f)))))))

;;---------------------------------------------------
;;----------------------------------------------------------------------------------------------------------

;; Conversely, let h be an arbitrary subgroup of g and suppose (fixed-field-p k h e f).  

;; To show that h is a subgroup of (galois-subgroup k e f), suppose v is in h.  Let x be an element of k and
;; let x' = (flift x k e).  Since (fixedp x' h e f), by embed-flift-gen,

;;     (embed x (restrict-embedding v e k) e f) = (embed x' v e f)
;;                                              = x'
;;                                              = (embed x (trivial-embedding k e f) e f).

;; By embed-cex-lemma, (restrict-embedding v e k) = (trivial-embedding k e f), and by member-fixing-autos,
;; v is in (galois-subgroup k e f).  Thus, h is a subgroup of (galois-subgroup k e f).

;; By Artin's Lemma, (edegree e k) <= (order h) and therefore

;;     (edegree e k) <= (order h) <= (order (galois-subgroup k e f)) = (edegree e k),

;; which implies (order h) = (order (galois-subgroup k e f)) and (galois-subgroup k e f) is a subgroup of h.z

(local-defthmd ffpgs-1
  (implies (and (extensionp e k) (extensionp k f) (galoisp e f)
                (subgroupp h (galois e f)) (fixed-field-p k h e f)
                (in v h))
	   (and (member v (auto-list e f))
	        (embeddingp (trivial-embedding k e f) k e f)
	        (embeddingp (restrict-embedding v e k) k e f)))
  :hints (("Goal" :in-theory (disable subgroupp-sublistp subgroupp-subsetp)
                  :use ((:instance subgroupp-subsetp (g (galois e f)) (x v))
                        (:instance extends-trans (d k))
			(:instance trivial-embedding-flift (e k) (k e))			
			(:instance embeddingp-restrict-embedding (phi v) (d k) (k e))))))

(local-defthmd ffpgs-2
  (implies (and (extensionp e k) (extensionp k f) (galoisp e f)
                (subgroupp h (galois e f)) (fixed-field-p k h e f)
                (in v h)
		(feltp x k))
	   (equal (embed x (restrict-embedding v e k) e f)
		  (embed x (trivial-embedding k e f) e f)))
  :hints (("Goal" :in-theory (disable subgroupp-sublistp subgroupp-subsetp)
                  :use ((:instance fixed-field-p-lemma (x (flift x k e)))
		        (:instance subgroupp-subsetp (g (galois e f)) (x v))
                        (:instance extends-trans (d k))
                        (:instance embed-flift-gen (k e) (d k) (phi v))
			(:instance fixedp-embed (phi v) (x (flift x k e)))
			(:instance trivial-embedding-flift (e k) (k e))))))

(local-defthmd ffpgs-3
  (implies (and (extensionp e k) (extensionp k f) (galoisp e f)
                (subgroupp h (galois e f)) (fixed-field-p k h e f)
                (in v h))
	   (equal (restrict-embedding v e k)
		  (trivial-embedding k e f)))
  :hints (("Goal" :use (ffpgs-1
                        (:instance embed-cex-lemma (e k) (k e) (phi (restrict-embedding v e k)) (psi (trivial-embedding k e f)))
                        (:instance extends-trans (d k))
                        (:instance ffpgs-2 (x (embed-cex (restrict-embedding v e k) (trivial-embedding k e f) k f)))))))
                        
(local-defthmd ffpgs-4
  (implies (and (extensionp e k) (extensionp k f) (galoisp e f)
                (subgroupp h (galois e f)) (fixed-field-p k h e f)
                (in v h))
	   (in v (galois-subgroup k e f)))
  :hints (("Goal" :use (ffpgs-1 ffpgs-3
                        (:instance extends-trans (d k))
			(:instance member-fixing-autos (x v))))))

(local-defthmd ffpgs-5
  (implies (and (extensionp e k) (extensionp k f) (galoisp e f)
                (subgroupp h (galois e f)) (fixed-field-p k h e f))
	   (subgroupp h (galois-subgroup k e f)))
  :hints (("Goal" :use (subgroupp-galois-subgroup
                        (:instance subgroup-subgroup (g (galois e f)) (k (galois-subgroup k e f)))
                        (:instance extends-trans (d k))
			(:instance scex1-lemma (l (elts h)) (m (elts (galois-subgroup k e f))))
			(:instance ffpgs-4 (v (scex1 (elts h) (elts (galois-subgroup k e f)))))))))

(local-defthmd ffpgs-6
  (implies (and (extensionp e k) (extensionp k f) (galoisp e f)
                (subgroupp h (galois e f)) (fixed-field-p k h e f))
	   (<= (edegree e k) (order h)))
  :hints (("Goal" :use (artin-lemma))))

(local-defthmd ffpgs-7
  (implies (and (extensionp e k) (extensionp k f) (galoisp e f)
                (subgroupp h (galois e f)) (fixed-field-p k h e f))
	   (<= (order h) (order (galois-subgroup k e f))))
  :hints (("Goal" :use (ffpgs-5 (:instance subgroup-order-<= (g (galois-subgroup k e f)))))))

(local-defthmd ffpgs-8
  (implies (and (extensionp e k) (extensionp k f) (galoisp e f)
                (subgroupp h (galois e f)) (fixed-field-p k h e f))
	   (= (order (galois-subgroup k e f))
	      (edegree e k)))
  :hints (("Goal" :use (isomorphismp-galois-subgroup-map galoisp-subfield
                        (:instance order-galois-group (f k))
			(:instance isomorphism-equal-orders (map (galois-subgroup-map k e f))
			                                    (g (galois-subgroup k e f))
							    (h (galois e k)))))))

(local-defthmd ffpgs-9
  (implies (and (extensionp e k) (extensionp k f) (galoisp e f)
                (subgroupp h (galois e f)) (fixed-field-p k h e f))
	   (= (order h)
	      (order (galois-subgroup k e f))))
  :hints (("Goal" :use (ffpgs-6 ffpgs-7 ffpgs-8))))

(defthmd fixed-field-p-galois-subgroup
  (implies (and (extensionp e k) (extensionp k f) (galoisp e f)
                (subgroupp h (galois e f))
                (fixed-field-p k h e f))
	   (and (subgroupp h (galois-subgroup k e f))
	        (subgroupp (galois-subgroup k e f) h)))
  :hints (("Goal" :in-theory (e/d (order) (SUBGROUPP-SUBLISTP))
                  :use (ffpgs-5 ffpgs-9 subgroupp-galois-subgroup
                        (:instance subgroup-subgroup (g (galois e f)) (k h) (h (galois-subgroup k e f)))
                        (:instance extends-trans (d k))
			(:instance subgroupp-sublistp (g (galois-subgroup k e f)))
			(:instance equal-len-sublistp (m (elts (galois-subgroup k e f))) (l (elts h)))))))
