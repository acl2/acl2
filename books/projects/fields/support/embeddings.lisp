(in-package "DM")

(include-book "extensions")

;; The theme of the book "extensions" is the reification of the metalogical notion of a field.  Similarly, 
;; a major theme of this book is the reification of the notion of a field homomomorphism.  That is, given 
;; extensions e and k of a field f, we shall define the homomorphic embeddings of e in k over f as ACL2 
;; objects.  In the case e = k, these are the automorphisms of e over k, which form the Galois group of the 
;; extension.  The culmination of the book is a formal version of the Fundamental Theorem of Galois Theory.  
;; The proof depends on a variety of previously formalized results in the areas of elementary number theory 
;; ("../numbers/"), finite group theory ("../groups/"), and linear algrbra ("../linear/").  Several other 
;; topics are encountered on the path to this result, including the evaluation, factorization, and roots of 
;; polynomials and the characteristic of a field.

;;----------------------------------------------------------------------------------------------------------
;;                                          Field Homomorphisms
;;----------------------------------------------------------------------------------------------------------

;; Axiomatization of a field homomorphism:

(encapsulate (((fld1) => *) ((fld2) => *) ((hom *) => *))
  (local (defun fld1 () 0))
  (local (defun fld2 () 0))
  (local (defun hom (x) x))
  (defthm fieldp-fld1-fld2
    (and (fieldp (fld1)) (fieldp (fld2))))
  (defthm hom-fld1-fld2
    (implies (feltp x (fld1)) (feltp (hom x) (fld2))))
  (defthm hom-id
    (and (equal (hom (fzero (fld1))) (fzero (fld2)))
	 (equal (hom (fone (fld1))) (fone (fld2)))))
  (defthm hom-fadd
    (implies (and (feltp x (fld1)) (feltp y (fld1)))
             (equal (hom (fadd x y (fld1))) (fadd (hom x) (hom y) (fld2)))))
  (defthm hom-fmul
    (implies (and (feltp x (fld1)) (feltp y (fld1)))
             (equal (hom (fmul x y (fld1))) (fmul (hom x) (hom y) (fld2))))))

;; Some trivial consequences of the axioms:

(defthmd hom-fneg
  (implies (feltp x (fld1))
           (equal (hom (fneg x (fld1)))
	          (fneg (hom x) (fld2))))
  :hints (("Goal" :use (hom-id
                        (:instance hom-fadd (x (fneg x (fld1))) (y x))
                        (:instance fneg-unique (f (fld2)) (x (hom (fneg x (fld1)))) (y (hom x)))))))

(defthmd hom-frecip
  (implies (and (feltp x (fld1)) (not (equal x (fzero (fld1)))))
           (equal (hom (frecip x (fld1)))
	          (frecip (hom x) (fld2))))
  :hints (("Goal" :use (hom-id
                        (:instance hom-fmul (x (frecip x (fld1))) (y x))
                        (:instance frecip-unique (f (fld2)) (x (hom (frecip x (fld1)))) (y (hom x)))))))

(defthm hom-fzero
  (implies (and (feltp x (fld1)) (equal (hom x) (fzero (fld2))))
           (equal x (fzero (fld1))))
  :hints (("Goal" :use (hom-id
                        (:instance hom-fmul (y (frecip x (fld1))))
			(:instance fone-fzero (f (fld2)))
			(:instance fmul-fzero-2 (f (fld2)) (x (hom (frecip x (fld1))))))))
  :rule-classes ())

(defthm hom-1-1
  (implies (and (feltp x (fld1)) (feltp y (fld1)) (equal (hom x) (hom y)))
           (equal x y))
  :hints (("Goal" :use ((:instance hom-fadd (y (fneg y (fld1))))
                        (:instance hom-fneg (x y))
			(:instance fneg-unique (y (fneg y (fld1))) (f (fld1)))
			(:instance hom-fzero (x (fadd x (fneg y (fld1)) (fld1)))))))
  :rule-classes ())

(defthm hom-fone
  (implies (and (feltp x (fld1)) (equal (hom x) (fone (fld2))))
           (equal x (fone (fld1))))
  :hints (("Goal" :use (hom-id
                        (:instance hom-1-1 (y (fone (fld1)))))))
  :rule-classes ())

;; A field homomorphism induces a homomorphism of polynomial rings:

(defun phom (p)
  (if (consp p)
      (cons (hom (car p)) (phom (cdr p)))
    ()))

(defthmd feltsp-phom
  (implies (feltsp p (fld1))
           (feltsp (phom p) (fld2))))

(defthmd polyp-phom
  (implies (polyp p (fld1))
           (polyp (phom p) (fld2)))
  :hints (("Goal" :in-theory (enable polyp)
                  :use (feltsp-phom
                        (:instance hom-fzero (x (car p)))))))

(defthmd monicp-phom
  (implies (and (polyp p (fld1)) (monicp p (fld1)))
           (monicp (phom p) (fld2)))
  :hints (("Goal" :in-theory (enable polyp monicp)
                  :use (feltsp-phom
		        (:instance hom-fone (x (car p)))))))

(defthmd phom-id
  (and (equal (phom (pzero (fld1))) (pzero (fld2)))
       (equal (phom (pone (fld1))) (pone (fld2))))
  :hints (("Goal" :in-theory (enable pone pzero))))

(defthmd phom-pzero
  (implies (and (polyp p (fld1))
                (not (equal p (pzero (fld1)))))
	   (not (equal (phom p) (pzero (fld2)))))
  :hints (("Goal" :in-theory (enable polyp pzero)
                  :use (polyp-phom
		        (:instance hom-fzero (x (car p)))))))

(local-defun phom-1-1-induct (p q)
  (if (consp p)
      (phom-1-1-induct (cdr p) (cdr q))
    (list p q)))    

(local-defthmd phom-1-1-1
  (implies (and (feltsp p (fld1)) (feltsp q (fld1)) (not (equal p q)))
           (not (equal (phom p) (phom q))))
  :hints (("Goal" :induct (phom-1-1-induct p q))
          ("Subgoal *1/2" :expand (phom q))
          ("Subgoal *1/1" :expand (phom q) :use ((:instance hom-1-1 (x (car p)) (y (car q)))))))

(defthmd phom-1-1
  (implies (and (polyp p (fld1)) (polyp q (fld1)) (not (equal p q)))
           (not (equal (phom p) (phom q))))
  :hints (("Goal" :use (phom-1-1-1))))

(defthm len-phom
  (equal (len (phom p))
         (len p)))

(defthmd phom-faddl
  (implies (and (feltsp p (fld1)) (feltsp q (fld1)))
           (equal (phom (faddl p q (fld1)))
	          (faddl (phom p) (phom q) (fld2))))
  :hints (("Goal" :induct (faddl-induct p q))
          ("Subgoal *1/4" :expand (phom q))
	  ("Subgoal *1/3" :in-theory (enable hom-fadd))))

(defthmd phom-pstrip
  (implies (feltsp p (fld1))
           (equal (phom (pstrip p (fld1)))
	          (pstrip (phom p) (fld2))))
  :hints (("Subgoal *1/2" :use ((:instance hom-fzero (x (car p)))))))

(defthmd phom-padd
  (implies (and (polyp p (fld1)) (polyp q (fld1)))
           (equal (phom (padd p q (fld1)))
	          (padd (phom p) (phom q) (fld2))))
  :hints (("Goal" :in-theory (enable feltsp-faddl phom-faddl padd)
                  :use ((:instance phom-pstrip (p (faddl p q (fld1))))))))

(defthmd phom-cmul
  (implies (and (feltsp q (fld1)) (feltp c (fld1)) (not (equal c (fzero (fld1)))))
           (equal (phom (cmul c q (fld1)))
	          (cmul (hom c) (phom q) (fld2))))		  
  :hints (("Subgoal *1/3" :use ((:instance hom-fzero (x c))))
          ("Subgoal *1/2" :use ((:instance hom-fzero (x c))
	                        (:instance hom-fmul (x c) (y (car q)))))))

(defthmd phom-append
  (implies (and (feltsp p (fld1)) (feltsp q (fld1)))
           (equal (phom (append p q))
	          (append (phom p) (phom q)))))

(defthm phom-fzero-list
  (implies (natp k)
           (equal (phom (fzero-list k (fld1)))
	          (fzero-list k (fld2)))))

(defthmd phom-pshift
  (implies (and (polyp p (fld1)) (natp k))
           (equal (phom (pshift p k (fld1)))
	          (pshift (phom p) k (fld2))))
  :hints (("Goal" :in-theory (enable polyp-phom)
                  :use ((:instance pshift-rewrite (x p) (f (fld1)))
                        (:instance pshift-rewrite (x (phom p)) (f (fld2)))
                        (:instance phom-append (q (fzero-list k (fld1))))))))

(local-defthmd phom-pmul-1
  (implies (and (polyp p (fld1)) (polyp q (fld1))
                (or (equal p (pzero (fld1)))
		    (equal q (pzero (fld1)))))
	   (equal (phom (pmul p q (fld1)))
	          (pmul (phom p) (phom q) (fld2))))		  
  :hints (("Goal" :in-theory (enable polyp-phom phom-id))))

(local-defthmd phom-pmul-2
  (implies (and (polyp p (fld1)) (polyp q (fld1))
                (not (equal p (pzero (fld1))))
		(not (equal q (pzero (fld1))))
		(not (and (consp p) (consp (cdr p)))))
	   (equal (phom (pmul p q (fld1)))
	          (pmul (phom p) (phom q) (fld2))))		  
  :hints (("Goal" :in-theory (enable polyp pzero)
                  :use ((:instance hom-fzero (x (car p)))
		        (:instance phom-cmul (c (car p)))))))

(local-defthmd phom-pmul-3
  (implies (and (polyp p (fld1)) (polyp q (fld1))
                (not (equal p (pzero (fld1))))
		(not (equal q (pzero (fld1))))
		(consp (cdr p)))
	   (equal (phom (pmul p q (fld1)))
	          (phom (padd (pshift (cmul (car p) q (fld1)) (degree p) (fld1))
                              (pmul (pstrip (cdr p) (fld1)) q (fld1))
			      (fld1)))))
  :hints (("Goal" :expand (pmul p q (fld1)))))

(local-defthmd phom-pmul-4
  (implies (and (polyp p (fld1)) (polyp q (fld1))
                (not (equal p (pzero (fld1))))
		(not (equal q (pzero (fld1))))
		(consp (cdr p)))
	   (equal (phom (padd (pshift (cmul (car p) q (fld1)) (degree p) (fld1))
                              (pmul (pstrip (cdr p) (fld1)) q (fld1))
			      (fld1)))
		  (padd (phom (pshift (cmul (car p) q (fld1)) (degree p) (fld1)))
		        (phom (pmul (pstrip (cdr p) (fld1)) q (fld1)))
			(fld2))))
  :hints (("Goal" :in-theory (enable pzero polyp)
                  :use ((:instance phom-padd (p (pshift (cmul (car p) q (fld1)) (degree p) (fld1)))
                                             (q (pmul (pstrip (cdr p) (fld1)) q (fld1))))
			(:instance polyp-cmul (c (car p)) (x q) (f (fld1)))
			(:instance field-integral-domain (x (car p)) (y (car q)) (f (fld1)))
			(:instance polyp-pshift (x (cmul (car p) q (fld1))) (k (degree p)) (f (fld1)))))))

(local-defthmd phom-pmul-5
  (implies (and (polyp p (fld1)) (polyp q (fld1))
                (not (equal p (pzero (fld1))))
		(not (equal q (pzero (fld1))))
		(consp (cdr p)))
	   (equal (phom (pshift (cmul (car p) q (fld1)) (degree p) (fld1)))
	          (pshift (cmul (car (phom p)) (phom q) (fld2)) (degree (phom p)) (fld2))))
  :hints (("Goal" :in-theory (enable polyp)
                  :use ((:instance phom-pshift (p (cmul (car p) q (fld1))) (k (degree p)))
		        (:instance phom-cmul (c (car p)))
			(:instance polyp-cmul (c (car p)) (x q) (f (fld1)))))))

(local-defthmd phom-pmul-6
  (implies (and (polyp p (fld1)) (polyp q (fld1))
                (not (equal p (pzero (fld1))))
		(not (equal q (pzero (fld1))))
		(consp (cdr p))
		(equal (phom (pmul (pstrip (cdr p) (fld1)) q (fld1)))
		       (pmul (phom (pstrip (cdr p) (fld1))) (phom q) (fld2))))
	   (equal (phom (pmul (pstrip (cdr p) (fld1)) q (fld1)))
	          (pmul (pstrip (cdr (phom p)) (fld2)) (phom q) (fld2))))
  :hints (("Goal" :in-theory (enable polyp)
                  :use ((:instance phom-pstrip (p (cdr p)))))))

(local-defthmd phom-pmul-7
  (implies (and (polyp p (fld1)) (polyp q (fld1))
                (not (equal p (pzero (fld1))))
		(not (equal q (pzero (fld1))))
		(consp (cdr p))
		(equal (phom (pmul (pstrip (cdr p) (fld1)) q (fld1)))
		       (pmul (phom (pstrip (cdr p) (fld1))) (phom q) (fld2))))
	   (equal (phom (pmul p q (fld1)))
	          (padd (pshift (cmul (car (phom p)) (phom q) (fld2)) (degree (phom p)) (fld2))
		        (pmul (pstrip (cdr (phom p)) (fld2)) (phom q) (fld2))
			(fld2))))
  :hints (("Goal" :use (phom-pmul-3 phom-pmul-4 phom-pmul-5 phom-pmul-6))))

(local-defthmd phom-pmul-8
  (implies (and (polyp p (fld1)) (polyp q (fld1))
                (not (equal p (pzero (fld1))))
		(not (equal q (pzero (fld1))))
		(consp (cdr p)))
	   (and (polyp (phom p) (fld2))
	        (polyp (phom q) (fld2))
		(not (equal (phom p) (pzero (fld2))))
		(not (equal (phom q) (pzero (fld2))))
		(consp (cdr (phom p)))))
  :hints (("Goal" :in-theory (enable polyp pzero)
                  :use (polyp-phom
			(:instance polyp-phom (p q))
			(:instance phom (p (cdr p)))
		        (:instance hom-fzero (x (car p)))
		        (:instance hom-fzero (x (car q)))))))

(local-defthmd phom-pmul-9
  (implies (and (polyp p (fld1)) (polyp q (fld1))
                (not (equal p (pzero (fld1))))
		(not (equal q (pzero (fld1))))
		(consp (cdr p)))
	   (equal (pmul (phom p) (phom q) (fld2))
	          (padd (pshift (cmul (car (phom p)) (phom q) (fld2)) (degree (phom p)) (fld2))
		        (pmul (pstrip (cdr (phom p)) (fld2)) (phom q) (fld2))
			(fld2))))
  :hints (("Goal" :use (phom-pmul-8)
                  :expand (pmul (phom p) (phom q) (fld2)))))

(local-defthmd phom-pmul-10
  (implies (and (polyp p (fld1)) (polyp q (fld1))
                (not (equal p (pzero (fld1))))
		(not (equal q (pzero (fld1))))
		(consp (cdr p))
		(equal (phom (pmul (pstrip (cdr p) (fld1)) q (fld1)))
		       (pmul (phom (pstrip (cdr p) (fld1))) (phom q) (fld2))))
	   (equal (phom (pmul p q (fld1)))
	          (pmul (phom p) (phom q) (fld2))))
  :hints (("Goal" :use (phom-pmul-7 phom-pmul-9))))

(defthmd phom-pmul
  (implies (and (polyp p (fld1)) (polyp q (fld1)))
           (equal (phom (pmul p q (fld1)))
	          (pmul (phom p) (phom q) (fld2))))
  :hints (("Goal" :induct (pmul-induct p q (fld1)))
          ("Subgoal *1/3" :use (phom-pmul-2))
          ("Subgoal *1/2" :use (phom-pmul-10))
          ("Subgoal *1/1" :use (phom-pmul-1))))

(defthmd phom-pquot-prem-1
  (implies (and (polyp x (fld1)) (polyp y (fld1)) (not (equal y (pzero (fld1)))))
           (and (polyp (phom (pquot x y (fld1))) (fld2))
	        (polyp (phom (prem x y (fld1))) (fld2))
                (equal (phom x)
	               (padd (pmul (phom y) (phom (pquot x y (fld1))) (fld2))
		             (phom (prem x y (fld1)))
			     (fld2)))
		(if (pconstp (phom y))
		    (equal (phom (prem x y (fld1))) (pzero (fld2)))
		  (< (degree (prem x y (fld1)))
		     (degree (phom y))))))
  :hints (("Goal" :in-theory (e/d (pconstp polyp-phom phom-id) (pquot-prem polyp-pquot-prem))
                  :expand ((len (cdr (phom y))))
                  :use ((:instance pquot-prem (f (fld1)))
                        (:instance phom-padd (p (pmul y (pquot x y (fld1)) (fld1))) (q (prem x y (fld1))))
			(:instance phom-pmul (p y) (q (pquot x y (fld1))))
			(:instance phom-pzero (p (prem x y (fld1))))			
			(:instance len (x (phom y)))))))

(defthmd phom-pquot-prem
  (implies (and (polyp x (fld1)) (polyp y (fld1)) (not (equal y (pzero (fld1)))))
           (and (polyp (phom (pquot x y (fld1))) (fld2))
	        (polyp (phom (prem x y (fld1))) (fld2))
                (equal (phom  (pquot x y (fld1)))
		       (pquot (phom x) (phom y) (fld2)))
                (equal (phom  (prem x y (fld1)))
		       (prem (phom x) (phom y) (fld2)))))
  :hints (("Goal" :in-theory (enable polyp-phom)
                  :use (phom-pquot-prem-1
                        (:instance phom-pzero (p y))
                        (:instance pquot-prem-unique (f (fld2)) (x (phom x)) (y (phom y)) (q (phom  (pquot x y (fld1)))) (r (phom  (prem x y (fld1)))))))))

(defthmd pdivides-phom
  (implies (and (polyp x (fld1)) (polyp y (fld1)) (not (equal y (pzero (fld1)))))
           (iff (pdivides (phom y) (phom x) (fld2))
	        (pdivides y x (fld1))))
  :hints (("Goal" :in-theory (enable phom-id pconstp pdivides polyp-phom)
                  :expand ((len (cdr (phom y))))
                  :use (phom-pquot-prem-1 phom-pquot-prem
		        (:instance phom-pzero (p (prem x y (fld1))))
			(:instance len (x (phom y)))))))
			
	  

;;----------------------------------------------------------------------------------------------------------
;;                             The Embedding of a Field in an Extension Field
;;----------------------------------------------------------------------------------------------------------

;; Let e be an extension of f:

(defun extends (e f)
  (or (equal e f)
      (and (consp e)
           (extends (cdr e) f))))

(defun extensionp (e f)
  (and (fieldp f) (fieldp e) (extends e f)))

;; We may think of f as a subfield of e, but this is not strictly true -- the elements of f are not elements
;; of e.  However, there is a natural embedding of f in e:

(defun fliftn (x n)
  (if (zp n)
      x
    (list (fliftn x (1- n)))))

(defund flift (x f e)
  (fliftn x (- (len e) (len f))))

;; flift satisfies the homomomorphism axioms:

(defthmd len-extends
  (implies (extends e f)
           (<= (len f) (len e))))

(local-defthmd fliftn-lifts-1
  (implies (and (fieldp e) (consp e) (feltp x (cdr e)))
           (feltp (list x) e))
  :hints (("Goal" :in-theory (enable feltp polyp)
                  :use ((:instance degree-car-field (f e))))))

(local-defthmd fliftn-lifts
  (implies (and (fieldp f) (fieldp e) (extends e f)
                (feltp x f))
	   (feltp (fliftn x (- (len e) (len f)))
	          e))
  :hints (("Subgoal *1/4" :use ((:instance len-extends (e (cdr e)))
                                (:instance fliftn-lifts-1 (x (FLIFTN X (+ (- (LEN F)) (LEN (CDR E))))))))))

(defthm feltp-flift
  (implies (and (extensionp e f)
                (feltp x f))
	   (feltp (flift x f e) e))
  :hints (("Goal" :in-theory (enable flift)
                  :use (fliftn-lifts))))

(local-defthmd fliftn-id
  (implies (and (fieldp f) (fieldp e) (extends e f))
           (and (equal (fliftn (fzero f) (- (len e) (len f))) (fzero e))
	        (equal (fliftn (fone f) (- (len e) (len f))) (fone e))))
  :hints (("Subgoal *1/2" :in-theory (enable fzero fone)
                          :use ((:instance len-extends (e (cdr e)))))))

(defthm flift-id
  (implies (extensionp e f)
           (and (equal (flift (fzero f) f e) (fzero e))
	        (equal (flift (fone f) f e) (fone e))))
  :hints (("Goal" :in-theory (enable flift)
                  :use (fliftn-id))))

(local-defthmd fliftn-fadd-1
  (implies (and (fieldp e) (consp e) (feltp x (cdr e)) (feltp y (cdr e)))
           (equal (list (fadd x y (cdr e)))
	          (fadd (list x) (list y) e)))
  :hints (("Goal" :in-theory (enable feltp fadd padd))))

(local-defthmd fliftn-fadd
  (implies (and (fieldp f) (fieldp e) (extends e f)
                (feltp x f) (feltp y f))
	   (equal (fliftn (fadd x y f) (- (len e) (len f)))
	          (fadd (fliftn x (- (len e) (len f)))
		        (fliftn y (- (len e) (len f)))
			e)))
  :hints (("Subgoal *1/4" :use ((:instance fliftn-lifts (e (cdr e)))
                                (:instance fliftn-lifts (e (cdr e)) (x y))
                                (:instance len-extends (e (cdr e)))  
                                (:instance fliftn-fadd-1 (x (fliftn x (- (len (cdr e)) (len f))))
				                         (y (fliftn y (- (len (cdr e)) (len f)))))))))

(defthm flift-fadd
  (implies (and (extensionp e f)
                (feltp x f) (feltp y f))
           (equal (flift (fadd x y f) f e)
	          (fadd (flift x f e) (flift y f e) e)))
  :hints (("Goal" :in-theory (enable flift)
                  :use (fliftn-fadd))))

(local-defthmd fliftn-fmul-1
  (implies (and (fieldp e) (consp e) (feltp x (cdr e)) (feltp y (cdr e)))
           (equal (list (fmul x y (cdr e)))
	          (fmul (list x) (list y) e)))
  :hints (("Goal" :in-theory (enable polyp feltp pzero fmul pmul)
                  :use ((:instance degree-car-field (f e))
		        (:instance prem-equal (f (cdr e)) (y (car e)) (x (list (fmul x y (cdr e))))))
                  :expand ((FMUL (LIST X) (LIST Y) E)))))

(local-defthmd fliftn-fmul
  (implies (and (fieldp f) (fieldp e) (extends e f)
                (feltp x f) (feltp y f))
	   (equal (fliftn (fmul x y f) (- (len e) (len f)))
	          (fmul (fliftn x (- (len e) (len f)))
		        (fliftn y (- (len e) (len f)))
			e)))
  :hints (("Subgoal *1/4" :use ((:instance fliftn-lifts (e (cdr e)))
                                (:instance fliftn-lifts (e (cdr e)) (x y))
                                (:instance len-extends (e (cdr e)))  
                                (:instance fliftn-fmul-1 (x (fliftn x (- (len (cdr e)) (len f))))
				                         (y (fliftn y (- (len (cdr e)) (len f)))))))))

(defthm flift-fmul
  (implies (and (extensionp e f)
                (feltp x f) (feltp y f))
           (equal (flift (fmul x y f) f e)
	          (fmul (flift x f e) (flift y f e) e)))
  :hints (("Goal" :in-theory (enable flift)
                  :use (fliftn-fmul))))

;; Some trivial consequences of the axioms:

(defthmd flift-fneg
  (implies (and (extensionp e f)
                (feltp x f))
           (equal (flift (fneg x f) f e)
	          (fneg (flift x f e) e)))
  :hints (("Goal" :use (flift-id
                        (:instance flift-fadd (x (fneg x f)) (y x))
                        (:instance fneg-unique (f e) (x (flift (fneg x f) f e)) (y (flift x f e)))))))

(defthmd flift-frecip
  (implies (and (extensionp e f)
                (feltp x f) (not (equal x (fzero f))))
           (equal (flift (frecip x f) f e)
	          (frecip (flift x f e) e)))
  :hints (("Goal" :use (flift-id
                        (:instance flift-fmul (x (frecip x f)) (y x))
                        (:instance frecip-unique (f e) (x (flift (frecip x f) f e)) (y (flift x f e)))))))

(defthm flift-fzero
  (implies (and (extensionp e f)
                (feltp x f) (equal (flift x f e) (fzero e)))
           (equal x (fzero f)))
  :hints (("Goal" :use (flift-id
                        (:instance flift-fmul (y (frecip x f)))
			(:instance fone-fzero (f e))
			(:instance fmul-fzero-2 (f e) (x (flift (frecip x f) f e))))))
  :rule-classes ())

(local-defthmd fliftn-1-1
  (implies (and (fieldp f) (fieldp e) (extends e f)
                (feltp x f) (feltp y f) (not (equal x y)))
	   (not (equal (fliftn x (- (len e) (len f)))
	               (fliftn y (- (len e) (len f)))))))

(defthmd flift-1-1
  (implies (and (extensionp e f)
                (feltp x f) (feltp y f) (not (equal x y)))
	   (not (equal (flift x f e) (flift y f e))))
  :hints (("Goal" :in-theory (enable flift)
                  :use (fliftn-1-1))))

(defthm flift-fone
  (implies (and (extensionp e f)
                (feltp x f) (equal (flift x f e) (fone e)))
           (equal x (fone f)))
  :hints (("Goal" :use (flift-id
                        (:instance flift-1-1 (y (fone f))))))
  :rule-classes ())

;; Additional properties:

(defthm flift-noop
  (equal (flift x f f) x)
  :hints (("Goal" :in-theory (enable flift))))

(local-defthmd fliftn-plus
  (implies (and (natp n) (natp m))
           (equal (fliftn (fliftn x n) m)
	          (fliftn x (+ n m)))))

(defthm flift-comp
  (implies (and (extensionp e d) (extensionp d f))
           (equal (flift (flift x f d) d e)
	          (flift x f e)))
  :hints (("Goal" :in-theory (enable flift)
                  :use ((:instance fliftn-plus (n (- (len d) (len f))) (m (- (len e) (len d))))
		        (:instance len-extends (f d))
		        (:instance len-extends (e d))))))

;; flift induces a homomorphism of polynomial rings:

(defun plift (p f e)
  (if (consp p)
      (cons (flift (car p) f e) (plift (cdr p) f e))
    ()))

(defthmd feltsp-plift
  (implies (and (extensionp e f) (feltsp p f))
           (feltsp (plift p f e) e)))

(defthm len-plift
  (equal (len (plift p f e))
         (len p)))

(defthmd polyp-plift
  (implies (and (extensionp e f) (polyp p f))
	   (polyp (plift p f e) e))
  :hints (("Goal" :in-theory (enable polyp)
                  :use (feltsp-plift
                        (:instance flift-fzero (x (car p)))))))

(defthm monicp-plift
  (implies (and (extensionp e f) (polyp p f) (monicp p f))
           (monicp (plift p f e) e))
  :hints (("Goal" :in-theory (enable polyp monicp)
                  :expand ((plift p f e)))))

(defthmd pstrip-plift
  (implies (and (extensionp e f) (feltsp p f))
           (equal (pstrip (plift p f e) e)
	          (plift (pstrip p f) f e)))
  :hints (("Goal" :induct (len p))
          ("Subgoal *1/1" :use ((:instance flift-fzero (x (car p)))))))

(defthmd plift-id
  (implies (extensionp e f)
           (and (equal (plift (pzero f) f e) (pzero e))
	        (equal (plift (pone f) f e) (pone e))))
  :hints (("Goal" :in-theory (enable pone pzero))))

(defthmd plift-pzero
  (implies (and (extensionp e f)
                (polyp p f) (not (equal p (pzero f))))
           (not (equal (plift p f e) (pzero e))))
  :hints (("Goal" :use ((:functional-instance phom-pzero
                         (fld1 (lambda () (if (and (extensionp e f) (polyp p f) (not (equal p (pzero f)))) f (fld1))))
                         (fld2 (lambda () (if (and (extensionp e f) (polyp p f) (not (equal p (pzero f)))) e (fld2))))
			 (hom (lambda (x) (if (and (extensionp e f) (polyp p f) (not (equal p (pzero f)))) (flift x f e) (hom x))))
			 (phom (lambda (x) (if (and (extensionp e f) (polyp p f) (not (equal p (pzero f)))) (plift x f e) (phom x)))))))))

(defthmd plift-1-1
  (implies (and (extensionp e f)
                (polyp p f) (polyp q f) (not (equal p q)))
           (not (equal (plift p f e) (plift q f e))))
  :hints (("Goal" :use ((:functional-instance phom-1-1
                         (fld1 (lambda () (if (and (extensionp e f) (polyp p f) (polyp q f) (not (equal p q))) f (fld1))))
                         (fld2 (lambda () (if (and (extensionp e f) (polyp p f) (polyp q f)(not (equal p q))) e (fld2))))
			 (hom (lambda (x) (if (and (extensionp e f) (polyp p f) (polyp q f)(not (equal p q))) (flift x f e) (hom x))))
			 (phom (lambda (x) (if (and (extensionp e f) (polyp p f) (polyp q f)(not (equal p q))) (plift x f e) (phom x)))))))))
		  
(defthmd plift-padd
  (implies (and (extensionp e f)
                (polyp p f) (polyp q f))
           (equal (plift (padd p q f) f e)
	          (padd (plift p f e) (plift q f e) e)))
  :hints (("Goal" :use ((:functional-instance phom-padd
                         (fld1 (lambda () (if (and (extensionp e f) (polyp p f) (polyp q f)) f (fld1))))
                         (fld2 (lambda () (if (and (extensionp e f) (polyp p f) (polyp q f)) e (fld2))))
			 (hom (lambda (x) (if (and (extensionp e f) (polyp p f) (polyp q f)) (flift x f e) (hom x))))
			 (phom (lambda (x) (if (and (extensionp e f) (polyp p f) (polyp q f)) (plift x f e) (phom x)))))))))			 
		  
(defthmd plift-cmul
  (implies (and (extensionp e f) (feltsp p f)
                (feltp c f) (not (equal c (fzero f))))
           (equal (plift (cmul c p f) f e)
	          (cmul (flift c f e) (plift p f e) e)))
  :hints (("Subgoal *1/3" :use ((:instance flift-fzero (x c))))
          ("Subgoal *1/2" :use ((:instance flift-fzero (x c))))))

(defthmd plift-pmul
  (implies (and (extensionp e f)
                (polyp p f) (polyp q f))
	   (equal (plift (pmul p q f) f e)
	          (pmul (plift p f e) (plift q f e) e)))
  :hints (("Goal" :use ((:functional-instance phom-pmul
                         (fld1 (lambda () (if (and (extensionp e f) (polyp p f) (polyp q f)) f (fld1))))
                         (fld2 (lambda () (if (and (extensionp e f) (polyp p f) (polyp q f)) e (fld2))))
			 (hom (lambda (x) (if (and (extensionp e f) (polyp p f) (polyp q f)) (flift x f e) (hom x))))
			 (phom (lambda (x) (if (and (extensionp e f) (polyp p f) (polyp q f)) (plift x f e) (phom x)))))))))

(defthmd pdivides-plift
  (implies (and (extensionp e f)
                (polyp x f) (polyp y f) (not (equal y (pzero f))))
	   (iff (pdivides (plift y f e) (plift x f e) e)
	        (pdivides y x f)))
  :hints (("Goal" :use ((:functional-instance pdivides-phom
                         (fld1 (lambda () (if (and (extensionp e f) (polyp x f) (polyp y f) (not (equal y (pzero f)))) f (fld1))))
                         (fld2 (lambda () (if (and (extensionp e f) (polyp x f) (polyp y f) (not (equal y (pzero f)))) e (fld2))))
			 (hom (lambda (z) (if (and (extensionp e f) (polyp x f) (polyp y f) (not (equal y (pzero f)))) (flift z f e) (hom z))))
			 (phom (lambda (z) (if (and (extensionp e f) (polyp x f) (polyp y f) (not (equal y (pzero f)))) (plift z f e) (phom z)))))))))

(local-defthm plift-noop-1
  (implies (feltsp p f)
           (equal (plift p f f) p)))

(defthm plift-noop
  (implies (polyp p f)
           (equal (plift p f f) p)))

(defthm plift-comp
  (implies (and (extensionp e d) (extensionp d f))
           (equal (plift (plift x f d) d e)
	          (plift x f e))))

(local-defthm plift-append
  (implies (and (extensionp e f) (feltsp p f) (feltsp q f))
           (equal (plift (append p q) f e)
	          (append (plift p f e) (plift q f e)))))

(local-defthmd plift-pshift-feltsp
  (implies (and (extensionp e f)
                (feltsp p f) (natp k))
	   (equal (plift (pshift p k f) f e)
	          (pshift (plift p f e) k e))))

(defthmd plift-pshift
  (implies (and (extensionp e f)
                (polyp p f) (natp k))
	   (equal (plift (pshift p k f) f e)
	          (pshift (plift p f e) k e)))
  :hints (("Goal" :use (plift-pshift-feltsp))))

;; We have informally referred to a simple extension e of f as adjoining a root of the irreducible polynomial
;; (car e) to f.  We shall show that (car e) -- or more precisely, (plift (car e) f e) -- does indeed have a
;; root in e.  We must first define the notion of a root.


;;----------------------------------------------------------------------------------------------------------
;;                                          Polynomial Evaluation
;;----------------------------------------------------------------------------------------------------------

;; Power of a field element:

(defun fpower (x n f)
  (if (zp n)
      (fone f)
    (fmul x (fpower x (1- n) f) f)))

(defthm feltp-fpower
  (implies (and (fieldp f) (feltp x f))
           (feltp (fpower x n f) f)))

(defthmd fpower-nonzero
  (implies (and (fieldp f) (feltp x f) (not (equal x (fzero f))))
           (not (equal (fpower x n f) (fzero f))))
  :hints (("Subgoal *1/2" :use ((:instance field-integral-domain (y (fpower x (1- n) f)))))))

;; Power of a polynomial:

(defun ppower (p n f)
  (if (zp n)
      (pone f)
    (pmul p (ppower p (1- n) f) f)))

(defthm polyp-ppower
  (implies (and (fieldp f) (polyp x f))
           (polyp (ppower x n f) f)))

;; If f is a non-base field, then (fpower x n f) and (ppower x n (cdr f)) are related as follows:

;;    (fpower x n f) = (fmul x (fpower x (1- n) f) f)
;;                   = (fmul x (prem (ppower x (1- n) (cdr f)) (car f) (cdr f)) f)
;;		     = (prem (pmul x (prem (ppower x (1- n) (cdr f)) (car f) (cdr f)) (cdr f)) (car f))
;;		     = (prem (pmul x (ppower x (1- n) (cdr f)) (cdr f)) (car f) (cdr f))
;;		     = (prem (ppower x n (cdr f)) (car f) (cdr f))

(local-defthmd fpower-ppower-1
  (implies (and (fieldp f) (consp f)
                (feltp x f) (zp n))
	   (equal (fpower x n f)
	          (prem (ppower x n (cdr f)) (car f) (cdr f))))
  :hints (("Goal" :in-theory (enable fmul)
                  :use (degree-car-field
		        (:instance degree-pone (f (cdr f)))
		        (:instance prem-equal (f (cdr f)) (x (pone (cdr f))) (y (car f)))))
	  ("Goal'''" :in-theory (enable fone pone))))

(local-defthmd fpower-ppower-2
  (implies (and (fieldp f) (consp f)
                (feltp x f) (not (zp n))
		(equal (fpower x (1- n) f)
		       (prem (ppower x (1- n) (cdr f)) (car f) (cdr f))))
	   (equal (fpower x n f)
	          (prem (ppower x n (cdr f)) (car f) (cdr f))))
  :hints (("Goal" :expand ((:free (y) (FMUL X y f)))
                  :in-theory (enable feltp)
                  :use (irreduciblep-car-field
		        (:instance prem-pmul-prem (y (ppower x (+ -1 n) (cdr f))) (z (car f)) (f (cdr f)))))))

(defthmd fpower-ppower
  (implies (and (fieldp f) (consp f)
                (feltp x f) (natp n))
	   (equal (fpower x n f)
	          (prem (ppower x n (cdr f)) (car f) (cdr f))))
  :hints (("Subgoal *1/2" :use (fpower-ppower-2))
          ("Subgoal *1/1" :use (fpower-ppower-1))))

;; Evaluation of a polynomial:

(defun peval (p x f)
  (declare (xargs :measure (len p) :hints (("Goal" :use ((:instance len-pstrip (x (cdr p))))))))
  (if (consp p)
      (if (pconstp p)
          (car p)
	(fadd (fmul (car p) (fpower x (degree p) f) f)
	      (peval (pstrip (cdr p) f) x f)
	      f))
    ()))

(defthm feltp-peval
  (implies (and (fieldp f) (polyp p f) (feltp x f))
           (feltp (peval p x f) f))
  :hints (("Subgoal *1/4" :in-theory (enable polyp))
          ("Subgoal *1/3" :in-theory (enable pconstp polyp) :use ((:instance polyp-pstrip (x (cdr p)) (f (fld1)))))
          ("Subgoal *1/2" :in-theory (enable pconstp polyp) :use ((:instance polyp-pstrip (x (cdr p)) (f (fld1)))))
          ("Subgoal *1/1" :in-theory (enable pconstp polyp))))

;; hom commutes with polynomial evaluation:

(defthmd hom-fpower
  (implies (and (feltp x (fld1)) (natp n))
           (equal (hom (fpower x n (fld1)))
	          (fpower (hom x) n (fld2)))))

(defthmd pconstp-phom
  (iff (pconstp (phom p))
       (pconstp p))
  :hints (("Goal" :in-theory (enable pconstp))))

(local-defthmd hom-peval-1
  (implies (and (polyp p (fld1)) (feltp x (fld1)) (not (pconstp p)))
           (equal (hom (fadd (fmul (car p) (fpower x (len (cdr p)) (fld1)) (fld1))
                             (peval (pstrip (cdr p) (fld1)) x (fld1))
                             (fld1)))
		  (fadd (hom (fmul (car p) (fpower x (len (cdr p)) (fld1)) (fld1)))
		        (hom (peval (pstrip (cdr p) (fld1)) x (fld1)))
			(fld2))))
  :hints (("Goal" :in-theory (enable polyp pconstp)
                  :use ((:instance hom-fadd (x (fmul (car p) (fpower x (len (cdr p)) (fld1)) (fld1)))
		                            (y (peval (pstrip (cdr p) (fld1)) x (fld1))))))))

(local-defthmd hom-peval-2
  (implies (and (polyp p (fld1)) (feltp x (fld1)) (not (pconstp p)))
           (equal (hom (fmul (car p) (fpower x (len (cdr p)) (fld1)) (fld1)))
	          (fmul (hom (car p)) (fpower (hom x) (len (cdr p)) (fld2)) (fld2))))
  :hints (("Goal" :in-theory (enable polyp pconstp)
                  :use ((:instance hom-fpower (n (degree p)))
		        (:instance hom-fmul (x (car p)) (y (fpower x (len (cdr p)) (fld1))))))))

(local-defthmd hom-peval-3
  (implies (and (polyp p (fld1)) (feltp x (fld1)) (not (pconstp p))
                (equal (hom (peval (pstrip (cdr p) (fld1)) x (fld1)))
                       (peval (phom (pstrip (cdr p) (fld1))) (hom x) (fld2))))
           (equal (hom (peval (pstrip (cdr p) (fld1)) x (fld1)))
	          (peval (pstrip (phom (cdr p)) (fld2)) (hom x) (fld2))))
  :hints (("Goal" :in-theory (enable polyp pconstp)
                  :use ((:instance phom-pstrip (p (cdr p)))))))

(local-defthmd hom-peval-4
  (implies (and (polyp p (fld1)) (feltp x (fld1)) (not (pconstp p))
                (equal (hom (peval (pstrip (cdr p) (fld1)) x (fld1)))
                       (peval (phom (pstrip (cdr p) (fld1))) (hom x) (fld2))))
           (equal (hom (fadd (fmul (car p) (fpower x (len (cdr p)) (fld1)) (fld1))
                             (peval (pstrip (cdr p) (fld1)) x (fld1))
                             (fld1)))
	          (fadd (fmul (hom (car p)) (fpower (hom x) (len (cdr p)) (fld2)) (fld2))
		        (peval (pstrip (phom (cdr p)) (fld2)) (hom x) (fld2))
			(fld2))))
  :hints (("Goal" :use (hom-peval-1 hom-peval-2 hom-peval-3))))

(defthmd hom-peval
  (implies (and (polyp p (fld1)) (feltp x (fld1)))
           (equal (hom (peval p x (fld1)))
	          (peval (phom p) (hom x) (fld2))))
  :hints (("Subgoal *1/4" :in-theory (enable polyp))
	  ("Subgoal *1/3" :use (pconstp-phom hom-peval-4))
          ("Subgoal *1/2" :in-theory (enable pconstp polyp) :use ((:instance polyp-pstrip (x (cdr p)) (f (fld1)))))
	  ("Subgoal *1/1" :use (pconstp-phom))))

;; By functional instantiation of hom-peval, lifting commutes with polynomial evaluation:

(defthmd flift-peval
  (implies (and (extensionp e f)
                (polyp p f) (feltp x f))
	   (equal (flift (peval p x f) f e)
	          (peval (plift p f e) (flift x f e) e)))
  :hints (("Goal" :use ((:functional-instance hom-peval
                         (fld1 (lambda () (if (and (extensionp e f) (polyp p f) (feltp x f)) f (fld1))))
                         (fld2 (lambda () (if (and (extensionp e f) (polyp p f) (feltp x f)) e (fld2))))
			 (hom (lambda (z) (if (and (extensionp e f) (polyp p f) (feltp x f)) (flift z f e) (hom z))))
			 (phom (lambda (z) (if (and (extensionp e f) (polyp p f) (feltp x f)) (plift z f e) (phom z)))))))))	          

;; Evaluation of constants:

(defthmd peval-pconstp
  (implies (and (fieldp f) (polyp p f) (pconstp p) (feltp x f))
           (equal (peval p x f) (car p))))

;; Evaluation of sums and products:

(defun feval (p x f)
  (if (consp p)
      (fadd (fmul (car p) (fpower x (degree p) f) f)
            (feval (cdr p) x f)
	    f)
    (fzero f)))

(defthm feltp-feval
  (implies (and (fieldp f) (feltsp p f) (feltp x f))
           (feltp (feval p x f) f)))

(defthmd feval-pstrip
  (implies (and (fieldp f) (feltsp p f) (feltp x f))
           (equal (feval (pstrip p f) x f)
	          (feval p x f))))

(defthmd feval-peval
  (implies (and (fieldp f) (polyp p f) (feltp x f))
           (equal (feval p x f)
	          (peval p x f)))
  :hints (("Subgoal *1/4" :in-theory (enable polyp))
          ("Subgoal *1/3" :in-theory (enable pconstp polyp) :use ((:instance feval-pstrip (p (cdr p)))))
          ("Subgoal *1/2" :in-theory (enable pconstp polyp) :use ((:instance polyp-pstrip (x (cdr p)))))
          ("Subgoal *1/1" :in-theory (enable pconstp polyp))))

(local-defthm faddl-nil-2
  (implies (feltsp q f)
           (equal (faddl () q f) q))
  :hints (("Goal" :induct (len q))))

(local-defthmd hack-1
  (implies (and (fieldp f) (feltp p f) (feltp q f) (feltp c f))
           (equal (fadd c (fadd p q f) f)
	          (fadd p (fadd q c f) f)))
  :hints (("Goal" :use ((:instance fadd-comm (x c) (y (fadd p q f)))
                        (:instance fadd-assoc (x p) (y q) (z c))))))

(local-defthmd hack-2
  (implies (and (fieldp f) (feltp p f) (feltp q f) (feltp c f) (feltp d f) (feltp x f))
           (equal (fadd (fmul (fadd c d f) x f)
	                (fadd p q f)
			f)
		  (fadd p
		        (fadd (fmul c x f)
			      (fadd q (fmul d x f) f)
			      f)
			f)))
  :hints (("Goal" :use ((:instance fadd-comm (x p) (y (fadd (fmul c x f) (fadd q (fmul d x f) f) f)))
                        (:instance fadd-comm (x (fmul d x f)) (y q))
			(:instance fadd-assoc (x (fmul c x f)) (y (fmul d x f)) (z q))
			(:instance fadd-assoc (x (fadd (fmul c x f) (fmul d x f) f)) (y q) (z p))
			(:instance fadd-comm (x q) (y p))
			(:instance fdistrib (y c) (z d))
			(:instance fadd-comm (y (fadd c d f)))))))


(local-defthm feval-nil
  (implies (equal (len p) 0)
           (equal (feval p x f) (fzero f))))

(defthmd feval-faddl
  (implies (and (fieldp f) (feltsp p f) (feltsp q f) (feltp x f))
           (equal (feval (faddl p q f) x f)
	          (fadd (feval p x f) (feval q x f) f)))
  :hints (("Goal" :induct (faddl-induct p q))
          ("Subgoal *1/3" :in-theory (enable len-faddl)
	                  :use ((:instance hack-2 (x (fpower x (len (cdr p)) f)) (c (car p)) (d (car q))
			                          (p (feval (cdr p) x f)) (q (feval (cdr q) x f)))))
          ("Subgoal *1/2" :in-theory (enable len-faddl)
	                  :use ((:instance hack-1 (c (fmul (car q) (fpower x (len (cdr q)) f) f))
			                          (p (feval p x f)) (q (feval (cdr q) x f)))))
          ("Subgoal *1/1" :in-theory (enable len-faddl)
	                  :use ((:instance hack-1 (c (fmul (car p) (fpower x (len (cdr p)) f) f))
			                          (p (feval q x f)) (q (feval (cdr p) x f)))))))

(local-defthmd peval-padd-1
  (implies (and (fieldp f) (polyp p f) (polyp q f) (feltp x f))
           (equal (peval (padd p q f) x f)
	          (feval (padd p q f) x f)))
  :hints (("Goal" :use ((:instance feval-peval (p (padd p q f)))))))

(local-defthmd peval-padd-2
  (implies (and (fieldp f) (polyp p f) (polyp q f) (feltp x f))
           (equal (feval (padd p q f) x f)
	          (fadd (peval p x f) (peval q x f) f)))
  :hints (("Goal" :in-theory (enable padd feval-peval feval-faddl)
                  :use ((:instance feval-pstrip (p (faddl p q f)))
		        (:instance feltsp-faddl (x p) (y q))))))

(defthmd peval-padd
  (implies (and (fieldp f) (polyp p f) (polyp q f) (feltp x f))
           (equal (peval (padd p q f) x f)
	          (fadd (peval p x f) (peval q x f) f)))
  :hints (("Goal" :use (peval-padd-1 peval-padd-2))))

(defthmd feval-cmul
  (implies (and (fieldp f) (feltp c f) (feltsp q f) (feltp x f))
           (equal (feval (cmul c q f) x f)
	          (fmul c (feval q x f) f))))

(local-defthmd peval-pmul-1
  (implies (and (fieldp f) (polyp p f) (polyp q f) (feltp x f)
                (or (equal p (pzero f)) (equal q (pzero f))))
           (equal (peval (pmul p q f) x f)
	          (fmul (peval p x f) (peval q x f) f)))
  :hints (("Goal" :in-theory (enable polyp pzero)
                  :use (peval-pconstp
                        (:instance peval-pconstp (p q))))))

(defthmd peval-cmul
  (implies (and (fieldp f) (feltp c f) (not (equal c (fzero f))) (polyp q f) (feltp x f))
           (equal (peval (cmul c q f) x f)
	          (fmul c (peval q x f) f)))
  :hints (("Goal" :in-theory (enable polyp)
                  :use (feval-cmul
		        (:instance polyp-cmul (x q))
			(:instance feval-peval (p q))
			(:instance feval-peval (p (cmul c q f)))))))

(local-defthmd peval-pmul-2
  (implies (and (fieldp f) (polyp p f) (polyp q f) (feltp x f)
                (not (equal p (pzero f)))
		(not (equal q (pzero f)))
		(not (and (consp p) (consp (cdr p)))))
           (equal (peval (pmul p q f) x f)
	          (fmul (peval p x f) (peval q x f) f)))
  :hints (("Goal" :in-theory (enable polyp pzero)
                  :use (peval-pconstp
                        (:instance peval-cmul (c (car p)))))))

(local-defthmd peval-pmul-3
  (implies (and (fieldp f) (polyp p f) (polyp q f) (feltp x f)
                (not (equal p (pzero f)))
		(not (equal q (pzero f)))
		(consp p)
		(consp (cdr p)))
           (equal (peval (pmul p q f) x f)
	          (fadd (peval (pshift (cmul (car p) q f) (degree p) f) x f)
		        (peval (pmul (pstrip (cdr p) f) q f) x f)
			f)))
  :hints (("Goal" :in-theory (enable pzero polyp)
                  :expand (pmul p q f)
                  :use ((:instance peval-padd (p (pshift (cmul (car p) q f) (degree p) f))
		                              (q (pmul (pstrip (cdr p) f) q f)))
			(:instance polyp-cmul (c (car p)) (x q))
			(:instance field-integral-domain (x (car p)) (y (car q)))
			(:instance polyp-pshift (x (cmul (car p) q f)) (k (degree p)))
			(:instance polyp-pstrip (x (cdr p)))))))

(local-defthmd hack-3
  (implies (and (fieldp f) (feltp x f) (feltp q f) (feltp p f))
           (equal (fmul q (fmul x p f) f)
	          (fmul x (fmul q p f) f)))
  :hints (("Goal" :use ((:instance fmul-comm (y q))
                        (:instance fmul-assoc (y q) (z p))
			(:instance fmul-assoc (x q) (y x) (z p))))))

(local-defthmd peval-pshift-1
  (implies (and (fieldp f) (feltsp q f) (feltp x f))
           (equal (feval (append q (list (fzero f))) x f)
	          (fmul x (feval q x f) f)))
  :hints (("Subgoal *1/4" :in-theory (enable polyp))
          ("Subgoal *1/3" :in-theory (enable polyp))
          ("Subgoal *1/2" :in-theory (enable polyp)
	                  :use ((:instance hack-3 (q (car q)) (p (fpower x (len (cdr q)) f)))))))

(local-defthmd peval-pshift-2
  (implies (and (fieldp f) (polyp q f) (feltp x f))
           (equal (peval (append q (list (fzero f))) x f)
	          (fmul x (peval q x f) f)))
  :hints (("Goal" :in-theory (enable polyp)
                  :use (peval-pshift-1
		        (:instance feval-peval (p q))
		        (:instance feval-peval (p (append q (list (fzero f)))))))))

(local-defthmd peval-pshift-3
  (implies (and (fieldp f) (polyp q f) (feltp x f) (posp k))
           (equal (fmul (fpower x (1- k) f)
                        (peval (append q (list (fzero f))) x f)
                        f)
		  (fmul (fpower x k f) (peval q x f) f)))
  :hints (("Goal" :use (peval-pshift-2
                        (:instance fmul-assoc (x (fpower x (1- k) f)) (y x) (z (peval q x f)))
			(:instance fmul-comm (y (fpower x (1- k) f))))))) 

(local-defthmd peval-pshift-4
  (implies (and (fieldp f) (polyp q f) (feltp x f) (posp k)
                (equal (peval (pshift (append q (list (fzero f))) (1- k) f) x f)
                       (fmul (fpower x (1- k) f)
                             (peval (append q (list (fzero f))) x f)
                             f)))
           (equal (peval (pshift q k f) x f)
                  (fmul (fpower x k f) (peval q x f) f)))
  :hints (("Goal" :use (peval-pshift-3))))

(defthmd peval-pshift
  (implies (and (fieldp f) (polyp q f) (not (equal q (pzero f))) (natp k) (feltp x f))
           (equal (peval (pshift q k f) x f)
	          (fmul (fpower x k f) (peval q x f) f)))
  :hints (("Subgoal *1/6" :use (peval-pshift-4))
          ("Subgoal *1/5" :use (peval-pshift-4))  
          ("Subgoal *1/3" :in-theory (enable polyp pzero))
          ("Subgoal *1/2" :use ((:instance polyp-pshift (x q) (k 1))))))

(local-defthmd peval-pmul-4
  (implies (and (fieldp f) (polyp p f) (polyp q f) (feltp x f)
                (not (equal p (pzero f)))
		(not (equal q (pzero f)))
		(consp p)
		(consp (cdr p)))
           (and (natp (degree p))
	        (polyp (cmul (car p) q f) f)
		(not (equal (cmul (car p) q f) (pzero f)))))
  :hints (("Goal" :in-theory (enable pzero polyp)
                  :use ((:instance polyp-cmul (c (car p)) (x q))
			(:instance field-integral-domain (x (car p)) (y (car q)))))))

(local-defthmd peval-pmul-5
  (implies (and (fieldp f) (polyp p f) (polyp q f) (feltp x f)
                (not (equal p (pzero f))))
           (equal (peval (cmul (car p) q f) x f)
		  (fmul (car p) (peval q x f) f)))
  :hints (("Goal" :in-theory (enable pzero polyp)
                  :use ((:instance peval-cmul (c (car p)))))))

(local-defthmd peval-pmul-6
  (implies (and (fieldp f) (polyp p f) (polyp q f) (feltp x f)
                (not (equal p (pzero f)))
		(not (equal q (pzero f)))
		(consp p)
		(consp (cdr p)))
           (equal (peval (pmul p q f) x f)
	          (fadd (fmul (fpower x (degree p) f)
			      (fmul (car p) (peval q x f) f)
			      f)
		        (peval (pmul (pstrip (cdr p) f) q f) x f)
			f)))
  :hints (("Goal" :in-theory (theory 'minimal-theory)
                  :use (peval-pmul-3 peval-pmul-4 peval-pmul-5
                        (:instance peval-pshift (k (degree p)) (q (cmul (car p) q f)))))))

(local-defthmd peval-pmul-7
  (implies (and (fieldp f) (polyp p f) (polyp q f) (feltp x f)
                (not (equal p (pzero f)))
		(not (equal q (pzero f)))
		(consp p)
		(consp (cdr p))
		(equal (peval (pmul (pstrip (cdr p) f) q f) x f)
		       (fmul (peval (pstrip (cdr p) f) x f)
		             (peval q x f)
			     f)))
           (equal (peval (pmul p q f) x f)
	          (fadd (fmul (fpower x (degree p) f)
			      (fmul (car p) (peval q x f) f)
			      f)
		        (fmul (peval (pstrip (cdr p) f) x f)
		              (peval q x f)
			      f)
			f)))
  :hints (("Goal" :in-theory (theory 'minimal-theory)
                  :use (peval-pmul-6))))

(local-defthmd hack-4
  (implies (and (fieldp f) (feltp p f) (feltp c f) (feltp q f) (feltp s f))
           (equal (fadd (fmul p (fmul c q f) f) (fmul s q f) f)
	          (fmul (fadd (fmul c p f) s f) q f)))
  :hints (("Goal" :use ((:instance fmul-assoc (x p) (y c) (z q))
                        (:instance fmul-comm (x q) (y (fmul p c f)))
                        (:instance fmul-comm (x q) (y s))
			(:instance fdistrib (x q) (y (fmul p c f)) (z s))
			(:instance fmul-comm (x q) (y (fadd (fmul p c f) s f)))
			(:instance fmul-comm (x p) (y c))))))

(local-defthmd peval-pmul-8
  (implies (and (fieldp f) (polyp p f) (polyp q f) (feltp x f)
                (not (equal p (pzero f)))
		(not (equal q (pzero f)))
		(consp p)
		(consp (cdr p))
		(equal (peval (pmul (pstrip (cdr p) f) q f) x f)
		       (fmul (peval (pstrip (cdr p) f) x f)
		             (peval q x f)
			     f)))
           (equal (peval (pmul p q f) x f)
	          (fmul (fadd (fmul (car p) (fpower x (degree p) f) f)
		              (peval (pstrip (cdr p) f) x f)
			      f)
			(peval q x f)
			f)))
  :hints (("Goal" :in-theory (enable pconstp polyp pzero)
                  :use (peval-pmul-7
                        (:instance hack-4 (p (fpower x (degree p) f)) (c (car p))
			                  (s (peval (pstrip (cdr p) f) x f)) (q (peval q x f)))))))

(local-defthmd peval-pmul-9
  (implies (and (fieldp f) (polyp p f) (polyp q f) (feltp x f)
                (not (equal p (pzero f)))
		(not (equal q (pzero f)))
		(consp p)
		(consp (cdr p))
		(equal (peval (pmul (pstrip (cdr p) f) q f) x f)
		       (fmul (peval (pstrip (cdr p) f) x f)
		             (peval q x f)
			     f)))
           (equal (peval (pmul p q f) x f)
	          (fmul (peval p x f)
			(peval q x f)
			f)))
  :hints (("Goal" :use (peval-pmul-8) :expand ((len p) (len (cdr p))))))

(defthmd peval-pmul
  (implies (and (fieldp f) (polyp p f) (polyp q f) (feltp x f))
           (equal (peval (pmul p q f) x f)
	          (fmul (peval p x f) (peval q x f) f)))
  :hints (("Goal" :induct (pmul-induct p q f))
          ("Subgoal *1/3" :use (peval-pmul-2))
          ("Subgoal *1/2" :use (peval-pmul-9))
          ("Subgoal *1/1" :use (peval-pmul-1))))
  
;; The identity polynomial is the monic monomial of degree 1.  We may think of this as the polynomial X:

(defund pid (f)
  (list (fone f) (fzero f)))

(defthmd polyp-pid
  (implies (fieldp f)
           (polyp (pid f) f))
  :hints (("Goal" :in-theory (enable polyp pid))))

(defthmd peval-pid
  (implies (and (fieldp f) (feltp x f))
           (equal (peval (pid f) x f) x))
  :hints (("Goal" :in-theory (enable pconstp pid)
                  :expand ((FPOWER X 1 F)))))

;; Root of a polynomial:

(defund prootp (x p f)
  (and (feltp x f)
       (equal (peval p x f) (fzero f))))


;;----------------------------------------------------------------------------------------------------------
;;                                    Primitive Element of an Extension 
;;----------------------------------------------------------------------------------------------------------

;; The primitive element of a non-base field f is the identity polynomial of (cdr f):

(defund primitive (f)
  (pid (cdr f)))

(defthm feltp-primitive
  (implies (and (fieldp f) (consp f))
           (feltp (primitive f) f))
  :hints (("Goal" :in-theory (enable feltp polyp pid primitive)
                  :use (fieldp))))

(defthmd primitive-nonzero
  (implies (and (fieldp f) (consp f))
           (not (equal (primitive f) (fzero f))))
  :hints (("Goal" :in-theory (enable fzero pid primitive))))

;; We shall show that (primitive f) is a root of the lifted generating polynomial of f,
;; (plift (car f) (cdr f) f).

;; A power of the primitive element:

(local-defthmd fpower-primitive-1
  (implies (and (fieldp f) (consp f) (posp n))
           (equal (pmul (primitive f) (pshift (pone (cdr f)) (1- n) (cdr f)) (cdr f))
	          (pshift (pone (cdr f)) n (cdr f))))
  :hints (("Goal" :in-theory (enable primitive pid))
          ("Subgoal 2" :in-theory (e/d (primitive pid pone pzero) (len-pshift))
	               :use ((:instance len-pshift (x (list (fone (cdr f)))) (k (1- n)) (f (cdr f)))))
	  ("Subgoal 1" :in-theory (enable pshift-pshift))
	  ("Subgoal 1.1" :in-theory (enable pzero))))

(local-defthmd fpower-primitive-2
  (implies (and (fieldp f) (consp f) (natp n))
           (equal (fpower (primitive f) n f)
	          (prem (pshift (pone (cdr f)) n (cdr f)) (car f) (cdr f))))
  :hints (("Subgoal *1/1" :in-theory (enable pone fone)
                          :use (fieldp
			        (:instance polyp-pone (f (cdr f)))
			        (:instance prem-equal (x (list (fone (cdr f)))) (y (car f)) (f (cdr f)))))
	  ("Subgoal *1/2" :in-theory (e/d (polyp-pid primitive) (pshift))
	                  :expand (FMUL (PRIMITIVE F) (FPOWER (PRIMITIVE F) (+ -1 N) F) F)
			  :use (fpower-primitive-1
			        (:instance prem-pmul-prem (x (primitive f)) (y (PSHIFT (PONE (CDR F)) (+ -1 N) (CDR F)))
				                          (z (car f)) (f (cdr f)))))))

(defthmd fpower-primitive
  (implies (and (fieldp f) (consp f) (natp n))
           (equal (fpower (primitive f) n f)
	          (prem (monomial (fone (cdr f)) n (cdr f))
		        (car f)
			(cdr f))))
  :hints (("Goal" :in-theory (enable fpower-primitive-2 monomial pone))))

;; Let p be any polynomial over (cdr f).  if we lift p to f and evaluate it on the primitive element, we get 
;; the remainder of p modulo (car f):

;;   (peval (plift p (cdr f) f) (primitive f) f)
;;     = (peval (cons (list (car p)) (plift (cdr p) (cdr f) f)) (primitive f) f)
;;     = (fadd (fmul (list (car p))
;;                   (fpower (primitive f) (degree p) f)
;;		     f)
;;             (peval (pstrip (plift (cdr p) (cdr f) f) f) (primitive f) f)
;;             f)
;;     = (fadd (fmul (list (car p))
;;                   (fpower (primitive f) (degree p) f)
;;		     f)
;;             (peval (plift (pstrip (cdr p) (cdr f)) (cdr f) f) (primitive f) f)
;;             f)
;;     = (fadd (fmul (list (car p))
;;                   (fpower (primitive f) (degree p) f)
;;		     f)
;;             (prem (pstrip (cdr p) (cdr f)) (car f) (cdr f))
;;             f)
;;     = (padd (prem (pmul (list (car p))
;;                         (fpower (primitive f) (degree p) f)
;;			   (cdr f))
;;                   (car f)
;;		     (cdr f))
;;             (prem (pstrip (cdr p) (cdr f)) (car f) (cdr f))
;;             (cdr f))
;;     = (padd (prem (pmul (list (car p))
;;                         (prem (monomial (fone (cdr f)) (degree p) (cdr f)) (car f) (cdr f))
;;			   (cdr f))
;;                   (car f)
;;		     (cdr f))
;;             (prem (pstrip (cdr p) (cdr f)) (car f) (cdr f))
;;             (cdr f))
;;     = (padd (prem (pmul (list (car p))
;;                         (monomial (fone (cdr f)) (degree p) (cdr f))
;;			   (cdr f))
;;                   (car f)
;;		     (cdr f))
;;             (prem (pstrip (cdr p) (cdr f)) (car f) (cdr f))
;;             (cdr f))
;;     = (padd (prem (monomial (car p) (degree p) (cdr f)) (car f) (cdr f))
;;             (prem (pstrip (cdr p) (cdr f)) (car f) (cdr f))
;;             (cdr f))
;;     = (prem (padd (monomial (car p) (degree p) (cdr f))
;;                   (pstrip (cdr p) (cdr f))
;;                   (cdr f))
;;             (car f)
;;             (cdr f))
;;     = (prem (padd (head p (cdr f))
;;                   (tail p (cdr f))
;;                   (cdr f))
;;             (car f)
;;             (cdr f))
;;     = (prem p (car f) (cdr f))

(local-defthm peval-primitive-1
  (implies (and (fieldp f) (consp f) (polyp p (cdr f)))
           (equal (peval (plift p (cdr f) f) (primitive f) f)
                  (peval (cons (list (car p)) (plift (cdr p) (cdr f) f)) (primitive f) f)))
  :hints (("Goal" :in-theory (enable polyp plift flift fliftn) :expand (FLIFTN (CAR P) 1))))

(local-defthm peval-primitive-2
  (implies (and (fieldp f) (consp f) (polyp p (cdr f)) (pconstp p))
           (equal (peval (plift p (cdr f) f) (primitive f) f)
                  (peval (cons (list (car p)) (plift (cdr p) (cdr f) f)) (primitive f) f)))
  :hints (("Goal" :in-theory (enable polyp plift flift fliftn pconstp) :expand (FLIFTN (CAR P) 1))))

(local-defthmd peval-primitive-3
  (implies (and (fieldp f) (consp f) (polyp p (cdr f)) (not (pconstp p)))
           (consp (plift (cdr p) (cdr f) f)))
  :hints (("Goal" :in-theory (e/d (pconstp polyp) (len-plift))
                  :expand (len (cdr p))
                  :use ((:instance len-plift (p (cdr p)) (f (cdr f)) (e f))))))

(local-defthmd peval-primitive-4
  (implies (and (fieldp f) (consp f) (polyp p (cdr f)) (not (pconstp p)))
           (equal (peval (cons (list (car p)) (plift (cdr p) (cdr f) f)) (primitive f) f)
                  (fadd (fmul (list (car p))
                              (fpower (primitive f) (degree p) f)
 		              f)
                        (peval (pstrip (plift (cdr p) (cdr f) f) f) (primitive f) f)
                        f)))
  :hints (("Goal" :in-theory (enable polyp pconstp peval)
                  :expand ((len p) (len (cdr p)))
                  :use (peval-primitive-3))))

(local-defthmd pstrip-plist
  (implies (and (fieldp f) (consp f) (feltsp p (cdr f)))
           (equal (pstrip (plift p (cdr f) f) f)
	          (plift (pstrip p (cdr f)) (cdr f) f)))
  :hints (("Goal" :induct (len p))
          ("Subgoal *1/1" :use ((:instance flift-fzero (f (cdr f)) (e f) (x (car p)))))))
	  
(local-defthmd peval-primitive-5
  (implies (and (fieldp f) (consp f) (polyp p (cdr f)) (not (pconstp p)))
           (equal (pstrip (plift (cdr p) (cdr f) f) f)
                  (plift (pstrip (cdr p) (cdr f)) (cdr f) f)))
  :hints (("Goal" :in-theory (enable pconstp polyp)
                  :use ((:instance pstrip-plist (p (cdr p)))))))

(local-defthmd peval-primitive-6
  (implies (and (fieldp f) (consp f) (polyp p (cdr f)) (not (pconstp p)))
           (equal (peval (plift p (cdr f) f) (primitive f) f)
                  (fadd (fmul (list (car p))
                              (fpower (primitive f) (degree p) f)
 		              f)
                        (peval (plift (pstrip (cdr p) (cdr f)) (cdr f) f) (primitive f) f)
                        f)))
  :hints (("Goal" :in-theory (theory 'minimal-theory)
                  :use (peval-primitive-1 peval-primitive-4 peval-primitive-5))))

(local-defthmd peval-primitive-7
  (implies (and (fieldp f) (consp f) (polyp p (cdr f)) (not (pconstp p)))
           (equal (fadd (fmul (list (car p))
                              (fpower (primitive f) (degree p) f)
 		              f)
                        (peval (plift (pstrip (cdr p) (cdr f)) (cdr f) f) (primitive f) f)
                        f)
		  (padd (fmul (list (car p))
                              (fpower (primitive f) (degree p) f)
 		              f)
                        (peval (plift (pstrip (cdr p) (cdr f)) (cdr f) f) (primitive f) f)
                        (cdr f))))
  :hints (("Goal" :in-theory (enable fadd))))

(local-defthmd peval-primitive-8
  (implies (and (fieldp f) (consp f) (polyp p (cdr f)) (not (pconstp p)))
           (equal (fmul (list (car p))
                        (fpower (primitive f) (degree p) f)
 		        f)
		  (prem (pmul (list (car p))
                              (fpower (primitive f) (degree p) f)
			      (cdr f))
			(car f)
			(cdr f))))
  :hints (("Goal" :in-theory (enable fmul))))

(local-defthmd peval-primitive-9
  (implies (and (fieldp f) (consp f) (polyp p (cdr f)) (not (pconstp p))
                (equal (peval (plift (pstrip (cdr p) (cdr f)) (cdr f) f) (primitive f) f)
		       (prem (pstrip (cdr p) (cdr f)) (car f) (cdr f))))
           (equal (peval (plift p (cdr f) f) (primitive f) f)
                  (padd (prem (pmul (list (car p))
                                    (fpower (primitive f) (degree p) f)
			            (cdr f))
                              (car f)
		              (cdr f))
                        (prem (pstrip (cdr p) (cdr f)) (car f) (cdr f))
                        (cdr f))))
  :hints (("Goal" :in-theory (theory 'minimal-theory)
                  :use (peval-primitive-6 peval-primitive-7 peval-primitive-8))))

(local-defthmd peval-primitive-10
  (implies (and (fieldp f) (consp f) (polyp p (cdr f)) (not (pconstp p)))
           (equal (fpower (primitive f) (degree p) f)
		  (prem (monomial (fone (cdr f)) (degree p) (cdr f))
			(car f)
			(cdr f))))
  :hints (("Goal" :in-theory (enable polyp)
                  :use ((:instance fpower-primitive (n (degree p)))))))

(local-defthmd peval-primitive-11
  (implies (and (fieldp f) (consp f) (polyp p (cdr f)) (not (pconstp p)))
           (and (polyp (list (car p)) (cdr f))
	        (polyp (monomial (fone (cdr f)) (degree p) (cdr f)) (cdr f))
		(polyp (car f) (cdr f))
		(not (equal (car f) (pzero (cdr f))))))
  :hints (("Goal" :in-theory (e/d (feltp pconstp polyp) (feltp-fpower))
                  :use (fieldp
		        (:instance feltp-fpower (x (primitive f)) (n (degree p)))))))

(local-defthmd peval-primitive-12
  (implies (and (fieldp f) (consp f) (polyp p (cdr f)) (not (pconstp p)))
           (equal (prem (pmul (list (car p))
                              (monomial (fone (cdr f)) (degree p) (cdr f))
			      (cdr f))
                        (car f)
		        (cdr f))
		  (prem (pmul (list (car p))
                              (prem (monomial (fone (cdr f)) (degree p) (cdr f))
			            (car f)
				    (cdr f))
			      (cdr f))
                        (car f)
		        (cdr f))))
  :hints (("Goal" :use (peval-primitive-11
		        (:instance prem-pmul-prem (x (list (car p))) (y (monomial (fone (cdr f)) (degree p) (cdr f)))
			                          (z (car f)) (f (cdr f)))))))

(local-defthmd peval-primitive-13
  (implies (and (fieldp f) (consp f) (polyp p (cdr f)) (not (pconstp p))
                (equal (peval (plift (pstrip (cdr p) (cdr f)) (cdr f) f) (primitive f) f)
		       (prem (pstrip (cdr p) (cdr f)) (car f) (cdr f))))
           (equal (peval (plift p (cdr f) f) (primitive f) f)
                  (padd (prem (pmul (list (car p))
                                    (monomial (fone (cdr f)) (degree p) (cdr f))
			            (cdr f))
                              (car f)
		              (cdr f))
                        (prem (pstrip (cdr p) (cdr f)) (car f) (cdr f))
                        (cdr f))))
  :hints (("Goal" :in-theory (theory 'minimal-theory)
                  :use (peval-primitive-9 peval-primitive-10 peval-primitive-12))))

(local-defthmd peval-primitive-14
  (implies (and (fieldp f) (consp f) (polyp p (cdr f)) (not (pconstp p)))
           (equal (pmul (list (car p))
                        (monomial (fone (cdr f)) (degree p) (cdr f))
			(cdr f))
		  (monomial (car p) (degree p) (cdr f))))
  :hints (("Goal" :in-theory (e/d (cmul-pshift pzero polyp pconstp monomial) (len-pshift))
                  :use ((:instance degree-monomial (c (fone (cdr f))) (k (degree p)) (f (cdr f)))))))

(local-defthmd peval-primitive-15
  (implies (and (fieldp f) (consp f) (polyp p (cdr f)) (not (pconstp p))
                (equal (peval (plift (pstrip (cdr p) (cdr f)) (cdr f) f) (primitive f) f)
		       (prem (pstrip (cdr p) (cdr f)) (car f) (cdr f))))
           (equal (peval (plift p (cdr f) f) (primitive f) f)
                  (padd (prem (monomial (car p) (degree p) (cdr f)) (car f) (cdr f))
                        (prem (pstrip (cdr p) (cdr f)) (car f) (cdr f))
                        (cdr f))))
  :hints (("Goal" :in-theory (theory 'minimal-theory)
                  :use (peval-primitive-13 peval-primitive-14))))

(local-defthmd peval-primitive-16
  (implies (and (fieldp f) (consp f) (polyp p (cdr f)) (not (pconstp p)))
           (and (polyp (pstrip (cdr p) (cdr f)) (cdr f))
	        (polyp (monomial (car p) (degree p) (cdr f)) (cdr f))
		(polyp (car f) (cdr f))
		(not (equal (car f) (pzero (cdr f))))))
  :hints (("Goal" :in-theory (enable pconstp polyp)
                  :use (fieldp
		        (:instance polyp-pstrip (x (cdr p)) (f (cdr f)))))))

(local-defthmd peval-primitive-17
  (implies (and (fieldp f) (consp f) (polyp p (cdr f)) (not (pconstp p)))
           (equal (padd (prem (monomial (car p) (degree p) (cdr f)) (car f) (cdr f))
                        (prem (pstrip (cdr p) (cdr f)) (car f) (cdr f))
                        (cdr f))
		  (prem (padd (monomial (car p) (degree p) (cdr f))
		              (pstrip (cdr p) (cdr f))
			      (cdr f))
			(car f)
			(cdr f))))
  :hints (("Goal" :use (peval-primitive-16
                        (:instance padd-prem-prem (f (cdr f)) (z (car f))
                                                  (x (monomial (car p) (degree p) (cdr f))) (y (pstrip (cdr p) (cdr f))))))))

(local-defthmd peval-primitive-18
  (implies (and (fieldp f) (consp f) (polyp p (cdr f)) (not (pconstp p)))
           (equal (padd (monomial (car p) (degree p) (cdr f))
		        (pstrip (cdr p) (cdr f))
			(cdr f))
		  p))
  :hints (("Goal" :in-theory (enable head tail pconstp polyp)
                  :use ((:instance pdecomp (x p) (f (cdr f)))))))

(local-defthmd peval-primitive-induction
  (implies (and (fieldp f) (consp f) (polyp p (cdr f)) (not (pconstp p))
                (equal (peval (plift (pstrip (cdr p) (cdr f)) (cdr f) f) (primitive f) f)
		       (prem (pstrip (cdr p) (cdr f)) (car f) (cdr f))))
           (equal (peval (plift p (cdr f) f) (primitive f) f)
                  (prem p (car f) (cdr f))))
  :hints (("Goal" :in-theory (theory 'minimal-theory)
                  :use (peval-primitive-15 peval-primitive-17 peval-primitive-18))))

(local-defthmd peval-primitive-base
  (implies (and (fieldp f) (consp f) (polyp p (cdr f)) (pconstp p))
           (equal (peval (plift p (cdr f) f) (primitive f) f)
                  (prem p (car f) (cdr f))))
  :hints (("Goal" :in-theory (enable polyp pconstp)
                  :use (peval-primitive-2 fieldp
		        (:instance prem-equal (x p) (y (car f)) (f (cdr f)))))))

(local-defun peval-induct (p f)
  (declare (xargs :measure (len p) :hints (("Goal" :use ((:instance len-pstrip (x (cdr p)) (f (cdr f))))))))
  (if (consp p)
      (if (pconstp p)
          ()
	(peval-induct (pstrip (cdr p) (cdr f)) f))
    ()))

(defthmd peval-primitive
  (implies (and (fieldp f) (consp f) (polyp p (cdr f)))
           (equal (peval (plift p (cdr f) f) (primitive f) f)
	          (prem p (car f) (cdr f))))
  :hints (("Goal" :induct (peval-induct p f))
          ("Subgoal *1/3" :in-theory (enable polyp))
	  ("Subgoal *1/2.4" :in-theory (enable polyp polyp-pstrip))
	  ("Subgoal *1/2.3" :in-theory (enable polyp polyp-pstrip))
	  ("Subgoal *1/2.2" :in-theory (enable polyp) :use (peval-primitive-induction))
	  ("Subgoal *1/2.1" :in-theory (enable polyp) :use (peval-primitive-induction))
	  ("Subgoal *1/1" :in-theory (enable polyp) :use (peval-primitive-base))))

;; The claim follows:

(defthmd prootp-primitive
  (implies (and (fieldp f) (consp f))
           (prootp (primitive f) (plift (car f) (cdr f) f) f))
  :hints (("Goal" :in-theory (e/d (pzero fzero prootp) (peval))
                  :use (fieldp
		        (:instance peval-primitive (p (car f)))
			(:instance prem-self (x (car f)) (f (cdr f)))))))
  

;;----------------------------------------------------------------------------------------------------------
;;                                        Polynomial Factorization
;;----------------------------------------------------------------------------------------------------------

;; If p is monic and reducible, then p is a product of 2 monic polynomials of lesser degree:

(defthmd reduciblep-product
  (implies (and (fieldp f) (polyp p f) (monicp p f) (reduciblep p f))
           (let* ((d (pfactor p f)) (q (pquot p d f)))
	     (and (polyp d f) (monicp d f) (> (degree d) 0) (< (degree d) (degree p))
	          (polyp q f) (monicp q f) (> (degree q) 0) (< (degree q) (degree p))
		  (equal (pmul d q f) p))))
  :hints (("Goal" :in-theory (e/d (polyp monicp reduciblep) (fone-id))
                  :use ((:instance pdivides-pquot (x (pfactor p f)) (y p))
		        (:instance polyp-pquot-prem (x p) (y (pfactor p f)))
			(:instance fone-id (x (car (pquot p (pfactor p f) f))))
		        (:instance car-pmul (x (pfactor p f)) (y (pquot p (pfactor p f) f)))
		        (:instance degree-pmul (x (pfactor p f)) (y (pquot p (pfactor p f) f)))))))

;; Factorization of a polynomial as a product of irreducible polynomials:

(defun factorization (p f)
  (declare (xargs :measure (len p) :hints (("Goal" :use (reduciblep-product)))))
  (if (and (fieldp f) (polyp p f) (monicp p f) (>= (degree p) 2) (reduciblep p f))
      (let ((d (pfactor p f)))
        (append (factorization d f)
                (factorization (pquot p d f) f)))
    (list p)))

;; The factorization of a non-constant monic polynomial is a list of monic irreducible polynomials
;; with product p:

(defun monicp-irreduciblep-listp (l f)
  (if (consp l)
      (and (polyp (car l) f)
           (irreduciblep (car l) f)
           (monicp (car l) f)
	   (>= (degree (car l)) 1)
	   (monicp-irreduciblep-listp (cdr l) f))
    (null l)))

(defthmd member-monicp-irreduciblep-listp
  (implies (and (monicp-irreduciblep-listp l f)
                (member p l))
	   (and (polyp p f)
                (irreduciblep p f)
                (monicp p f)
	        (>= (degree p) 1))))

(defthmd monicp-irreduciblep-append
  (implies (and (fieldp f) (monicp-irreduciblep-listp l f) (monicp-irreduciblep-listp m f))
           (monicp-irreduciblep-listp (append l m) f)))

(defun pmul-list (l f)
  (if (consp l)
      (pmul (car l) (pmul-list (cdr l) f) f)
    (pone f)))

(defthm polyp-pmul-list
  (implies (and (fieldp f) (monicp-irreduciblep-listp l f))
           (polyp (pmul-list l f) f)))

(defthm monicp-pmul-list
  (implies (and (fieldp f) (monicp-irreduciblep-listp l f))
           (monicp (pmul-list l f) f))
  :hints (("Goal" :induct (len l))
          ("Subgoal *1/1" :in-theory (enable monicp)
	                  :use ((:instance car-pmul (x (car l)) (y (pmul-list (cdr l) f)))))
	  ("Subgoal *1/2" :in-theory (enable monicp pone))))

(defthm pmul-list-append
  (implies (and (fieldp f) (monicp-irreduciblep-listp l f) (monicp-irreduciblep-listp m f))
           (equal (pmul-list (append l m) f)
	          (pmul (pmul-list l f) (pmul-list m f) f)))
  :hints (("Subgoal *1/3" :use ((:instance pmul-assoc (x (car l)) (y (pmul-list (cdr l) f)) (z (pmul-list m f)))))))

(defthmd pmul-list-irreduciblep-factorization
  (implies (and (fieldp f) (polyp p f)
                (monicp p f) (>= (degree p) 1))
	   (and (monicp-irreduciblep-listp (factorization p f) f)
	        (equal (pmul-list (factorization p f) f)
	               p)))
  :hints (("Goal" :induct (factorization p f))
          ("Subgoal *1/2" :in-theory (enable reduciblep irreduciblep))
          ("Subgoal *1/1" :in-theory (enable monicp-irreduciblep-append reduciblep irreduciblep)
	                  :use (reduciblep-product))))

(local-defthmd len-fact-1
  (implies (and (fieldp f) (monicp-irreduciblep-listp l f))
           (>= (degree (pmul-list l f))
	       (len l)))
  :hints (("Subgoal *1/2" :use ((:instance degree-pmul (x (CAR L)) (y (PMUL-LIST (CDR L) F)))))
          ("Subgoal *1/7" :in-theory (enable pone))))

(defthmd len-factorization-bound
  (implies (and (fieldp f) (polyp p f)
                (monicp p f) (>= (degree p) 1))
           (<= (len (factorization p f))
	       (degree p)))
  :hints (("Goal" :use (pmul-list-irreduciblep-factorization
                        (:instance len-fact-1 (l (factorization p f)))))))

;; A root of the product of p and q must be a root of either p or q:

(defthmd prootp-pmul
  (implies (and (fieldp f) (polyp p f) (polyp q f) (feltp x f))
           (iff (prootp x (pmul p q f) f)
	        (or (prootp x p f) (prootp x q f))))
  :hints (("Goal" :in-theory (enable prootp)
                  :use (peval-pmul
		        (:instance field-integral-domain (x (peval p x f)) (y (peval q x f)))))))

;; x is a root of p iff p is divisible by X - x:

(defun root-poly (x f)
  (list (fone f) (fneg x f)))

(defthmd peval-root-poly
  (implies (and (fieldp f) (feltp x f))
           (equal (peval (root-poly x f) x f)
	          (fzero f)))
  :hints (("Goal" :in-theory (enable pconstp)
                  :expand (FPOWER X 1 F))))

(defthmd prootp-root-poly
  (implies (and (fieldp f) (feltp x f))
           (prootp x (root-poly x f) f))
  :hints (("Goal" :in-theory (enable prootp)
                  :use (peval-root-poly))))

(defthmd polyp-root-poly
  (implies (and (fieldp f) (feltp x f))
           (polyp (root-poly x f) f))
  :hints (("Goal" :in-theory (enable polyp))))

(defthmd degree-root-poly
  (implies (and (fieldp f) (feltp x f))
           (equal (degree (root-poly x f))
	          1)))

(defthmd monicp-irreduciblep-root-poly
  (implies (and (fieldp f) (feltp x f))
           (let ((p (root-poly x f)))
	     (and (polyp p f)
	          (monicp p f)
		  (irreduciblep p f)
		  (equal (degree p) 1))))
  :hints (("Goal" :in-theory (enable polyp monicp irreduciblep reduciblep))))

(in-theory (disable pmul))
  
(local-defthmd prootp-pdivides-2
  (implies (and (fieldp f) (feltp x f) (polyp p f))
           (equal (peval p x f)
	          (peval (padd (pmul (list (fone f) (fneg x f)) (pquot p (list (fone f) (fneg x f)) f) f)
		               (prem p (list (fone f) (fneg x f)) f)
			       f)
			 x f)))
  :hints (("Goal" :use (polyp-root-poly
		        (:instance pquot-prem (x p) (y (list (fone f) (fneg x f))))))))

(local-defthmd prootp-pdivides-3
  (implies (and (fieldp f) (feltp x f) (polyp p f))
           (equal (peval (padd (pmul (list (fone f) (fneg x f)) (pquot p (list (fone f) (fneg x f)) f) f)
		               (prem p (list (fone f) (fneg x f)) f)
			       f)
			 x f)
	          (fadd (peval (pmul (list (fone f) (fneg x f)) (pquot p (list (fone f) (fneg x f)) f) f) x f)
		        (peval (prem p (list (fone f) (fneg x f)) f) x f)
			f)))
  :hints (("Goal" :use (polyp-root-poly
		        (:instance peval-padd (p (pmul (list (fone f) (fneg x f)) (pquot p (list (fone f) (fneg x f)) f) f))
			                      (q (prem p (list (fone f) (fneg x f)) f)))
			(:instance polyp-pquot-prem (x p) (y (list (fone f) (fneg x f))))))))

(local-defthmd prootp-pdivides-4
  (implies (and (fieldp f) (feltp x f) (polyp p f))
           (equal (peval (pmul (list (fone f) (fneg x f)) (pquot p (list (fone f) (fneg x f)) f) f) x f)
		  (fzero f)))
  :hints (("Goal" :use (polyp-root-poly peval-root-poly
		        (:instance peval-pmul (p (list (fone f) (fneg x f))) (q (pquot p (list (fone f) (fneg x f)) f)))
			(:instance polyp-pquot-prem (x p) (y (list (fone f) (fneg x f))))))))

(in-theory (disable pquot-prem polyp-pquot-prem))

(local-defthmd pconstp-prem-root-poly
  (implies (and (fieldp f) (feltp x f) (polyp p f))
           (and (polyp (prem p (list (fone f) (fneg x f)) f) f)
	        (pconstp (prem p (list (fone f) (fneg x f)) f))))
  :hints (("Goal" :in-theory (enable pconstp)
                  :expand (len (cdr (prem p (list (fone f) (fneg x f)) f)))
                  :use (polyp-root-poly
		        (:instance pquot-prem (x p) (y (list (fone f) (fneg x f))))
			(:instance polyp-pquot-prem (x p) (y (list (fone f) (fneg x f))))))))

(local-defthmd prootp-pdivides-5
  (implies (and (fieldp f) (feltp x f) (polyp p f))
           (equal (peval (prem p (list (fone f) (fneg x f)) f) x f)
		  (car (prem p (list (fone f) (fneg x f)) f))))
  :hints (("Goal" :in-theory (enable pconstp)
                  :use (polyp-root-poly pconstp-prem-root-poly
                        (:instance peval-pconstp (p (prem p (list (fone f) (fneg x f)) f)))))))

(in-theory (disable polyp-pquot-prem-*))

(local-defthmd prootp-pdivides-6
  (implies (and (fieldp f) (feltp x f) (polyp p f))
           (equal (fadd (peval (pmul (list (fone f) (fneg x f)) (pquot p (list (fone f) (fneg x f)) f) f) x f)
		        (peval (prem p (list (fone f) (fneg x f)) f) x f)
			f)
	          (car (prem p (list (fone f) (fneg x f)) f))))
  :hints (("Goal" :in-theory (enable pconstp polyp)
                  :use (prootp-pdivides-4 pconstp-prem-root-poly prootp-pdivides-5))))

(local-defthmd prootp-pdivides-7
  (implies (and (fieldp f) (feltp x f) (polyp p f))
           (equal (peval p x f)
                  (car (prem p (list (fone f) (fneg x f)) f))))
  :hints (("Goal" :use (prootp-pdivides-2 prootp-pdivides-3 prootp-pdivides-6))))

(defthmd prootp-pdivides
  (implies (and (fieldp f) (feltp x f) (polyp p f))
           (iff (prootp x p f)
	        (pdivides (root-poly x f) p f)))
  :hints (("Goal" :in-theory (enable polyp pzero pdivides prootp prootp-pdivides-7)
                  :use (pconstp-prem-root-poly))))

(defthmd prootp-not-pconstp
  (implies (and (fieldp f) (feltp x f) (polyp p f) (not (equal p (pzero f)))
                (prootp x p f))
	   (>= (degree p) 1))
  :hints (("Goal" :use (prootp-pdivides monicp-irreduciblep-root-poly
                        (:instance pdivides-degree (x (list (fone f) (fneg x f))) (y p))))))

(local-defthmd irreduciblep-pdivides-equal-1
  (implies (and (fieldp f)
                (polyp p f) (monicp p f) (irreduciblep p f) (>= (degree p) 1)
                (polyp q f) (monicp q f) (irreduciblep q f) (>= (degree q) 1)
		(pdivides p q f))
	   (let ((u (pquot q p f)))
	     (and (polyp q f)
	          (equal (pmul p u f) q))))
  :hints (("Goal" :in-theory (enable pdivides)
                  :use ((:instance pquot-prem (x q) (y p))))))

(local-defthmd irreduciblep-pdivides-equal-2
  (implies (and (fieldp f)
                (polyp p f) (monicp p f) (irreduciblep p f) (>= (degree p) 1)
                (polyp q f) (monicp q f) (irreduciblep q f) (>= (degree q) 1)
		(pdivides p q f))
	   (and (polyp (pquot q p f) f)
	        (pconstp (pquot q p f))))
  :hints (("Goal" :use (irreduciblep-pdivides-equal-1
                        (:instance irreduciblep-no-factor (x (pquot q p f)) (p q))
			(:instance pdivides-multiple (x (pquot q p f)) (y p))
			(:instance polyp-pquot-prem (x q) (y p))
			(:instance pmul-comm (x p) (y (pquot q p f)))
			(:instance degree-pmul (x p) (y (pquot q p f)))))))

(local-defthmd irreduciblep-pdivides-equal-3
  (implies (and (fieldp f)
                (polyp p f) (monicp p f) (irreduciblep p f) (>= (degree p) 1)
                (polyp q f) (monicp q f) (irreduciblep q f) (>= (degree q) 1)
		(pdivides p q f))
	   (equal (car (pquot q p f)) (fone f)))
  :hints (("Goal" :in-theory (e/d (polyp monicp) (fone-id))
                  :use (irreduciblep-pdivides-equal-1 irreduciblep-pdivides-equal-2
                        (:instance car-pmul (x p) (y (pquot q p f)))
			(:instance fone-id (x (car (pquot q p f))))))))

(local-defthmd irreduciblep-pdivides-equal-4
  (implies (and (fieldp f)
                (polyp p f) (monicp p f) (irreduciblep p f) (>= (degree p) 1)
                (polyp q f) (monicp q f) (irreduciblep q f) (>= (degree q) 1)
		(pdivides p q f))
	   (equal (pquot q p f) (pone f)))
  :hints (("Goal" :in-theory (enable polyp pone pconstp)
                  :use (irreduciblep-pdivides-equal-2 irreduciblep-pdivides-equal-3))))

(defthm irreduciblep-pdivides-equal
  (implies (and (fieldp f)
                (polyp p f) (monicp p f) (irreduciblep p f) (>= (degree p) 1)
                (polyp q f) (monicp q f) (irreduciblep q f) (>= (degree q) 1)
		(pdivides p q f))
	   (equal p q))
  :hints (("Goal" :use (irreduciblep-pdivides-equal-1 irreduciblep-pdivides-equal-4)))
  :rule-classes ())

(defthmd pdivides-pmul-listp
  (implies (and (fieldp f)
                (monicp-irreduciblep-listp l f)
		(polyp p f) (monicp p f) (irreduciblep p f) (>= (degree p) 1))
	   (iff (pdivides p (pmul-list l f) f)
	        (member p l)))
  :hints (("Subgoal *1/1" :in-theory (enable pzero pone) :use (polyp-pone (:instance pdivides-degree (x p) (y (pone f)))))
          ("Subgoal *1/2" :use ((:instance pdivides-multiple (x (car l)) (y (PMUL-LIST (CDR L) F)))))
	  ("Subgoal *1/3" :use ((:instance peuclid (x (CAR L)) (y (PMUL-LIST (CDR L) F)))
	                        (:instance irreduciblep-pdivides-equal (q (car l)))))))

(defthmd pdivides-member-factorization
  (implies (and (fieldp f)
		(polyp q f) (monicp q f) (>= (degree q) 1)
		(polyp p f) (monicp p f) (irreduciblep p f) (>= (degree p) 1))
	   (iff (pdivides p q f)
	        (member p (factorization q f))))
  :hints (("Goal" :use ((:instance pmul-list-irreduciblep-factorization (p q))
                        (:instance pdivides-pmul-listp (l (factorization q f)))))))

(defthmd member-factorization
  (implies (and (fieldp f)
                (polyp q f) (monicp q f) (>= (degree q) 1)
		(member p (factorization q f)))
	   (and (polyp p f)
                (irreduciblep p f)
                (monicp p f)
	        (>= (degree p) 1)
	        (<= (degree p) (degree q))
		(pdivides p q f)))
  :hints (("Goal" :use (pdivides-member-factorization
                        (:instance pmul-list-irreduciblep-factorization (p q))
			(:instance pdivides-degree (x p) (y q))
		        (:instance member-monicp-irreduciblep-listp (l (factorization q f)))))))

(defthmd prootp-pmul-listp
  (implies (and (fieldp f)
                (monicp-irreduciblep-listp l f)
		(feltp x f))
	   (iff (prootp x (pmul-list l f) f)
	        (member (root-poly x f) l)))
  :hints (("Goal" :use (monicp-irreduciblep-root-poly
                        (:instance pdivides-pmul-listp (p (list (fone f) (fneg x f))))
			(:instance prootp-pdivides (p (pmul-list l f)))))))

(defthmd prootp-member-factorization
  (implies (and (fieldp f)
                (polyp p f) (monicp p f) (>= (degree p) 1)
		(feltp x f))
	   (iff (prootp x p f)
	        (member (root-poly x f)
		        (factorization p f))))
  :hints (("Goal" :use (pmul-list-irreduciblep-factorization
                        (:instance prootp-pmul-listp (l (factorization p f)))))))

;; If p is irreducible and (degree p) > 1, then p has no roots, for if (prootp x p f), then since (factorization p f)) = (list p),
;; prootp-member-factorization implies p = (root-poly x f), wehich has degree 1:

(defthmd irreduciblep-no-root
  (implies (and (fieldp f)
                (polyp p f) (irreduciblep p f) (monicp p f) (> (degree p) 1)
		(feltp x f))
	   (not (prootp x p f)))
  :hints (("Goal" :expand ((factorization p f))
                  :in-theory (enable root-poly irreduciblep)
                  :use (prootp-member-factorization))))


;; List of the distinct roots of p:

(defun proots-aux (l f)
  (if (consp l)
      (let ((d (proots-aux (cdr l) f))
            (r (fneg (cadar l) f)))
        (if (and (= (degree (car l)) 1)
	         (not (member r d)))
            (cons r d)
	  d))
    ()))

(defund proots (p f)
  (proots-aux (factorization p f) f))

(defthmd len-proots-aux-bound
  (<= (len (proots-aux l f))
      (len l)))

(defthmd len-proots-<=-len-factorization
  (<= (len (proots p f))
      (len (factorization p f)))
  :hints (("Goal" :in-theory (enable proots)
                  :use ((:instance len-proots-aux-bound (l (factorization p f)))))))
      
(defthmd len-proots-bound
  (implies (and (fieldp f) (polyp p f)
                (monicp p f) (>= (degree p) 1))
	   (<= (len (proots p f))
	       (degree p)))
  :hints (("Goal" :in-theory (enable proots)
                  :use (len-factorization-bound
		        (:instance len-proots-aux-bound (l (factorization p f)))))))

(defthmd len-factorization-bound
  (implies (and (fieldp f) (polyp p f)
                (monicp p f) (>= (degree p) 1))
           (<= (len (factorization p f))
	       (degree p))))

(local-defthmd feltsp-proots-1
  (implies (and (fieldp f) (polyp p f) (>= (degree p) 1))
           (feltp (fneg (cadr p) f) f))
  :hints (("Goal" :in-theory (enable polyp))))

(local-defthmd feltsp-proots-2
  (implies (and (fieldp f) (monicp-irreduciblep-listp l f))
           (feltsp (proots-aux l f) f))
  :hints (("Subgoal *1/2" :use ((:instance feltsp-proots-1 (p (car l)))))))

(defthmd feltsp-proots
  (implies (and (fieldp f) (polyp p f) (monicp p f) (>= (degree p) 1))
           (feltsp (proots p f) f))
  :hints (("Goal" :in-theory (enable proots)
                  :use (pmul-list-irreduciblep-factorization
		        (:instance feltsp-proots-2 (l (factorization p f)))))))

(defthmd feltp-member-proots-aux
  (implies (and (fieldp f) (monicp-irreduciblep-listp l f)
                (member x (proots-aux l f)))
	   (feltp x f))
  :hints (("Subgoal *1/2" :use ((:instance feltsp-proots-1 (p (car l)))))))

(defthmd feltp-member-proots
  (implies (and (fieldp f) (polyp p f) (monicp p f) (>= (degree p) 1)
                (member x (proots p f)))
           (feltp x f))
  :hints (("Goal" :in-theory (enable proots)
                  :use (pmul-list-irreduciblep-factorization
		        (:instance feltp-member-proots-aux (l (factorization p f)))))))

(local-defthmd dlistp-proots-aux
  (dlistp (proots-aux l f)))

(defthmd dlistp-proots
  (dlistp (proots p f))
  :hints (("Goal" :in-theory (enable proots))))

(local-defthmd member-proots-aux-1
  (implies (and (fieldp f) (feltsp p f) (equal (degree p) 1))
           (equal (list (car p) (cadr p))
	          p))
  :hints (("Goal" :expand ((len p) (LEN (CDR P)) (LEN (CDDR P)) (FELTSP P F) (feltsp (cdr p) f)))))
  
(local-defthmd member-proots-aux-2
  (implies (and (fieldp f) (feltp x f)
                (polyp p f) (monicp p f))
	   (iff (equal p (list (fone f) (fneg x f)))
	        (and (equal (degree p) 1)
		     (equal x (fneg (cadr p) f)))))
  :hints (("Goal" :in-theory (enable monicp polyp)
                  :use (member-proots-aux-1 (:instance fneg-fneg (x (cadr p)))))))

(local-defthmd member-proots-aux-3
  (implies (and (fieldp f)
                (monicp-irreduciblep-listp l f)
		(feltp x f))
	   (iff (member (list (fone f) (fneg x f)) l)
	        (member x (proots-aux l f))))
  :hints (("Subgoal *1/1" :use ((:instance member-proots-aux-2 (p (car l)))))))

(defthmd member-proots-aux
  (implies (and (fieldp f)
                (monicp-irreduciblep-listp l f)
		(feltp x f))
	   (iff (prootp x (pmul-list l f) f)
	        (member x (proots-aux l f))))
  :hints (("Goal" :use (prootp-pmul-listp member-proots-aux-3))))

(defthmd member-proots
  (implies (and (fieldp f) (polyp p f) (monicp p f) (>= (degree p) 1))
           (iff (member x (proots p f))
	        (prootp x p f)))
  :hints (("Goal" :in-theory (enable prootp proots)
                  :use (pmul-list-irreduciblep-factorization feltp-member-proots
                        (:instance member-proots-aux (l (factorization p f)))))))



;; To do:
#|
(defthmd polyp-factorization-unique
  (implies (and (fieldp f) (polyp p f) (>= (degree p) 1)
                (monicp-irreduciblep-listp l f)
		(equal (pmul-list l f) p))
	   (permutationp l (factorization p f))))
|#

;;----------------------------------------------------------------------------------------------------------
;;                                        Field Extensions as Vector Spaces
;;----------------------------------------------------------------------------------------------------------

;; We shall show that an extension e of f is a vector space over f.  That is, we shall define functions
;; corresponding to the functions that are introduced by the encapsulation of "../linear/vectors" that 
;; characterize a vector space and prove the theorems corresponding to the vector space axioms.

;; The first 5 of these functions are easily defined, and their required properties are readily verified:

;;  vp        (lambda (x) (feltp x e))
;;  v+        (lambda (x y) (fadd x y e))
;;  v0        (lambda () (fzero e))
;;  v-        (lambda (x) (fneg x e))
;;  v*        (lambda (c x) (fmul (flift c f e) x e))

;; The remaining 5 functions are defined below:

;;  vlistnp   (lambda (x n) (elistnp x n e))
;;  vcomb     (lambda (flist elist) (ecomb flist elist e))
;;  vdim      (lambda () (edegree e f))
;;  vbasis    (lambda () (ebasis0 e f))
;;  vcoords   (lambda (x) (ecoords0 x e f))

;; List of vectors of length n:

(defun elistnp (x n e)
  (if (zp n)
      (null x)
    (and (consp x)
         (feltp (car x) e)
	 (elistnp (cdr x) (1- n) e))))

;; List of zeroes:

(defun elist0p (x e)
  (if (consp x)
      (and (= (car x) (fzero e))
           (elist0p (cdr x) e))
    (null x)))

;; List of n zeroes:

(defun elistn0 (n e)
  (if (zp n)
      ()
    (cons (fzero e) (elistn0 (1- n) e))))
	 
;; Linear combination of a list of vectors:

(defun ecomb (flist elist e f)
  (if (consp flist)
      (fadd (fmul (flift (car flist) f e)
                  (car elist)
		  e)
            (ecomb (cdr flist) (cdr elist) e f)
	    e)
    (fzero e)))

;; The dimension of the space is the degree of the extension, defined as follows:

(defun edegree (e f)
  (if (equal e f)
      1
    (and (consp e)
         (* (degree (car e)) (edegree (cdr e) f)))))

;; Note that edegree is multiplicative in the following sense:

(defthmd edegree-mult
  (implies (and (extensionp e k) (extensionp k f))
           (equal (edegree e f)
	          (* (edegree e k) (edegree k f))))
  :hints (("Goal" :induct (len e))
          ("Subgoal *1/1" :use ((:instance len-extends (e k) (f e))	  
	                        (:instance len-extends (e (cdr e)) (f k))))))

;; A lower bound on the degree of an extension:

(defthmd edegree-lower-bound
  (implies (extensionp e f)
           (>= (edegree e f) (expt 2 (- (len e) (len f)))))
  :hints (("Subgoal *1/2" :nonlinearp t :use ((:instance degree-car-field (f e))))))

;; The canonical basis is defined recursively.  First we define the canonical basis of
;; a simple extension:

(defun pid-powers (n f)
  (if (zp n)
      ()
    (cons (pshift (pone f) (1- n) f)
          (pid-powers (1- n) f))))

(defund simple-extension-basis (e)
  (pid-powers (degree (car e)) (cdr e)))

;; Multiply a field element x by each of a list of field elements l:

(defun fmul-list (x l e)
  (if (consp l)
      (cons (fmul x (car l) e)
            (fmul-list x (cdr l) e))
    ()))

;; Multiply each of a list of field elements l by each of a list of field elements m:

(defun fmul-lists (l m e)
  (if (consp l)
      (append (fmul-list (car l) m e)
              (fmul-lists (cdr l) m e))
    ()))

;; The canonical basis of an arbitrary extension:

(defun ebasis0 (e f)
  (if (equal e f)
      (list (fone f))
    (and (consp e)
         (fmul-lists (simple-extension-basis e)
                     (plift (ebasis0 (cdr e) f) (cdr e) e)
		     e))))

;; Given a polynomial x over f, extend it with zeroes to a generalized polynomial of length n:

(defun zpad (x n f)
  (if (and (natp n) (> n (len x)))
      (cons (fzero f) (zpad x (1- n) f))
    x))

;; The coordinates of x with respect to the canonical basis:

(encapsulate ()

(local (include-book "ordinals/lexicographic-book" :dir :system))

(set-well-founded-relation acl2::l<)

(mutual-recursion

  (defun ecoords0 (x e f)
    (declare (xargs :measure (list (len e) (acl2-count x))))
    (if (equal e f)
        (list x)
      (and (consp e)
           (ecoords0-list (zpad x (degree (car e)) (cdr e))
	                  (cdr e)
			  f))))

  (defun ecoords0-list (x e f)
    (declare (xargs :measure (list (len e) (acl2-count x))))
    (if (consp x)
        (append (ecoords0 (car x) e f)
	        (ecoords0-list (cdr x) e f))
      ()))
))

;;------------------------------------------

;; Basic properties of the functions defined above:

(defthmd elistnp-append
  (implies (and (natp m) (natp n) (elistnp x m f) (elistnp y n f))
           (elistnp (append x y) (+ m n) f)))

(defthmd feltsp-elistnp
  (implies (and (fieldp e) (feltsp l e))
           (elistnp l (len l) e)))

(defthmd elistnp-feltsp
  (implies (and (fieldp e) (elistnp l k e))
           (feltsp l e)))

(defthmd len-elistnp
  (implies (and (elistnp l k e) (natp k))
           (equal (len l) k)))

(defthm elistnp-plift-2
  (implies (and (extensionp e f)
                (natp n) (elistnp x n f))
	   (elistnp (plift x f e) n e)))

(defthm elistnp-plift
  (implies (and (fieldp e) (consp e)
                (natp n) (elistnp x n (cdr e)))
	   (elistnp (plift x (cdr e) e) n e)))

(defthmd feltp-ecomb
  (implies (and (extensionp e f) (natp n)
                (elistnp c n f) (elistnp l n e))
	   (feltp (ecomb c l e f) e)))

(local-defun ecomb-append-induct (c b m)
  (declare (irrelevant c b))
  (if (zp m)
      ()
    (ecomb-append-induct (cdr c) (cdr b) (1- m))))

(defthmd ecomb-append
  (implies (and (extensionp e f) (natp m) (natp n)
                (elistnp c1 m f) (elistnp c2 n f)
		(elistnp b1 m e) (elistnp b2 n e))
	   (equal (ecomb (append c1 c2) (append b1 b2) e f)
	          (fadd (ecomb c1 b1 e f) (ecomb c2 b2 e f) e)))
  :hints (("Goal" :induct (ecomb-append-induct c1 b1 m))
          ("Subgoal *1/1" :use ((:instance feltp-ecomb (c c2) (l b2))))
	  ("subgoal *1/2" :use ((:instance fadd-assoc (f e)
	                                              (x (FMUL (CAR B1) (FLIFT (CAR C1) F E) E))
	                                              (y (ECOMB (CDR C1) (CDR B1) E F))
	                                              (z (ECOMB C2 B2 E F)))
				(:instance feltp-ecomb (c c2) (l b2))
				(:instance feltp-ecomb (n (1- m)) (c (cdr c1)) (l (cdr b1)))))))

(defthm len-pid-powers
  (implies (natp n)
           (equal (len (pid-powers n f))
	          n)))
	   
(local-defthmd polyp-pid-power
  (implies (and (fieldp f) (natp k))
           (and (polyp (pshift (pone f) k f) f)
	        (equal (degree (pshift (pone f) k f)) k)))
  :hints (("Goal" :in-theory (e/d (polyp pone) (polyp-pshift) )
                  :use ((:instance polyp-pshift (x (fone f)))))))

(defthm feltp-pid-power
  (implies (and (fieldp e) (consp e) (natp k) (< k (degree (car e))))
           (feltp (pshift (pone (cdr e)) k (cdr e)) e))
  :hints (("Goal" :in-theory (enable feltp)
                  :use ((:instance polyp-pid-power (f (cdr e)))))))

(defthmd feltsp-pid-powers
  (implies (and (fieldp e) (consp e) (natp k) (<= k (degree (car e))))
           (feltsp (pid-powers k (cdr e)) e)))

(defthmd feltsp-zpad
  (implies (and (fieldp f) (feltsp x f) (natp n) (< (degree x) n))
           (feltsp (zpad x n f) f))
  :hints (("Goal" :induct (fact n))
          ("Subgoal *1/1" :in-theory (enable polyp))))

(defthmd len-zpad
  (implies (and (natp n) (feltsp x f) (<= (len x) n))
           (equal (len (zpad x n f)) n)))

(defthmd pstrip-zpad
  (implies (and (polyp x f) (natp n) (< (degree x) n))
           (equal (pstrip (zpad x n f) f)
	          x))
  :hints (("Goal" :in-theory (enable polyp))))

(defthmd elistnp-zpad
  (implies (and (fieldp f) (polyp x f) (natp n) (< (degree x) n))
           (elistnp (zpad x n f) n f))
  :hints (("Goal" :induct (fact n))
          ("Subgoal *1/2" :in-theory (enable polyp)
	                  :use ((:instance feltsp-elistnp (e f) (l x))))
          ("Subgoal *1/1" :in-theory (enable polyp))))

(defthm len-fmul-list
  (equal (len (fmul-list x l e))
         (len l)))

(defthm len-fmul-lists
  (equal (len (fmul-lists l m e))
         (* (len l) (len m))))

(defthm feltsp-fmul-list
  (implies (and (fieldp e) (feltp x e) (feltsp l e))
           (feltsp (fmul-list x l e) e)))

(defthm feltsp-fmul-lists
  (implies (and (fieldp e) (feltsp l e) (feltsp m e))
           (feltsp (fmul-lists l m e) e)))

(defthmd elistnp-fmul-list
  (implies (and (fieldp f) (natp n) (feltp x f) (elistnp y n f))
           (elistnp (fmul-list x y f) n f)))

(defthmd elistnp-fmul-lists
  (implies (and (fieldp f) (natp m) (natp n) (elistnp x m f) (elistnp y n f))
           (elistnp (fmul-lists x y f) (* m n) f))
  :hints (("Subgoal *1/4" :in-theory (enable elistnp-fmul-list)
                          :use ((:instance elistnp-append (x (FMUL-LIST (CAR X) Y F)) (y (FMUL-LISTS (CDR X) Y F))
                                                          (m n) (n (* (1- m) n)))))))

;;------------------------------------------

;; Length of (ebasis0 e):

(defthm len-simple-extension-basis
  (implies (and (fieldp e) (consp e))
           (equal (len (simple-extension-basis e))
                  (degree (car e))))
  :hints (("Goal" :in-theory (enable simple-extension-basis)
                  :use ((:instance degree-car-field (f e))))))

(defthm len-ebasis0
  (implies (extensionp e f)
           (equal (edegree e f)
	          (len (ebasis0 e f)))))

;; (ebasis0 e) is a list of elements of e:

(defthmd feltsp-simple-extension-basis
  (implies (and (fieldp e) (consp e))
           (feltsp (simple-extension-basis e) e))
  :hints (("Goal" :in-theory (enable simple-extension-basis)
                  :use ((:instance feltsp-pid-powers (k (degree (car e))))))))

(defthmd feltsp-ebasis0
  (implies (extensionp e f)
           (feltsp (ebasis0 e f) e))	   
  :hints (("Subgoal *1/4" :use (feltsp-simple-extension-basis
                                (:instance feltsp-plift (f (cdr e)) (p (EBASIS0 (CDR E) f)))
                                (:instance feltsp-fmul-lists (l (SIMPLE-EXTENSION-BASIS E))
                                                             (m (PLIFT (EBASIS0 (CDR E) F) (CDR E) E)))))))

(defthmd elistnp-simple-extension-basis
  (implies (and (fieldp e) (consp e))
           (elistnp (simple-extension-basis e) (degree (car e)) e))
  :hints (("Goal" :use (feltsp-simple-extension-basis
                        (:instance feltsp-elistnp (l (simple-extension-basis e)))))))

(defthmd elistnp-ebasis0
  (implies (extensionp e f)
           (elistnp (ebasis0 e f) (edegree e f) e))
  :hints (("Goal" :use (feltsp-ebasis0 len-ebasis0
                        (:instance feltsp-elistnp (l (ebasis0 e f)))))))

;;-----------------------------------------------
;; Linear independence of simple-extension-basis
;;-----------------------------------------------

(defthm flift-cdr
  (implies (and (fieldp e) (consp e))
           (equal (flift x (cdr e) e)
	          (list x)))
  :hints (("Goal" :in-theory (enable flift)
                  :expand (FLIFTN X 1))))

(local-defun ecomb-induct (c k)
  (declare (irrelevant c))
  (if (or (= k 1) (zp k))
      ()
    (ecomb-induct (cdr c) (1- k))))

(local-defthmd hack-5
  (implies (and (consp c) (not (cdr c)))
           (equal (list (car c)) c)))

(local-defthmd ecomb-pstrip-1
  (IMPLIES (AND (FIELDP E) (CONSP E)
                (FELTP x (CDR E)))
	   (feltp (list x) e))
  :hints (("Goal" :in-theory (enable feltp polyp)
                  :use ((:instance degree-car-field (f e))))))

(local-defthmd ecomb-pstrip-2
  (IMPLIES (AND (FIELDP E) (CONSP E)
                (FELTP x (CDR E)))
           (EQUAL (FADD (FMUL (LIST x) (PONE (CDR E)) E)
                        (FZERO E)
                        E)
                  (list x)))		  
  :hints (("Goal" :in-theory (enable pone fone)
                  :use (ecomb-pstrip-1
		        (:instance fone-id-2 (x (list x)) (f e))))))

(local-defthmd ecomb-pstrip-3
  (IMPLIES (AND (FIELDP E)
                (CONSP E)
                (<= 2 (LEN (CAR E)))
                (CONSP C)
                (FELTP (CAR C) (CDR E))
                (NOT (CDR C)))
           (EQUAL (FADD (FMUL (LIST (CAR C)) (PONE (CDR E)) E)
                        (FZERO E)
                        E)
                  C))
  :hints (("Goal" :use (hack-5
                        (:instance ecomb-pstrip-2 (x (car c)))))))

(local-defthmd ecomb-pstrip-4
  (IMPLIES (AND (FIELDP E)
                (CONSP E)
                (<= 2 (LEN (CAR E)))
                (ELISTNP C 1 (CDR E)))
           (EQUAL (ECOMB C (PID-POWERS 1 (CDR E))
                         E (CDR E))
                  (PSTRIP C (CDR E))))
  :hints (("Goal" :expand ((PID-POWERS 1 (CDR E)) (ELISTNP C 1 (CDR E)))
                  :use (ecomb-pstrip-3))))

(local-defthmd ecomb-pstrip-5
  (IMPLIES (AND (FIELDP E) (CONSP E) (not (zp k)) (<= k (degree (car e)))
                (ELISTNP (CDR C) (+ -1 K) (CDR E))
                (CONSP (CDR C)))
           (feltp (PSTRIP (CDR C) (CDR E)) e))
  :hints (("Goal" :in-theory (enable feltp)
                  :use ((:instance elistnp-feltsp (l (cdr c)) (k (1- k)) (e (cdr e)))
                        (:instance polyp-pstrip (x (cdr c)) (f (cdr e)))
			(:instance len-elistnp (e (cdr e)) (l (cdr c)) (k (1- k)))
			(:instance len-pstrip (x (cdr c)) (f (cdr e)))))))

(local-defthmd ecomb-pstrip-6
  (IMPLIES (AND (FIELDP E) (CONSP E) (not (zp k)) (<= k (degree (car e)))
                (ELISTNP (CDR C) (+ -1 K) (CDR E))
                (CONSP (CDR C)))
           (EQUAL (FADD (FMUL (LIST (FZERO (CDR E)))
                              (PSHIFT (PONE (CDR E)) (+ -1 K) (CDR E))
                              E)
                        (PSTRIP (CDR C) (CDR E))
                        E)
                  (PSTRIP (CDR C) (CDR E))))
  :hints (("Goal" :in-theory (enable fzero)
                  :use (ecomb-pstrip-5
		        (:instance feltp-pid-power (k (1- k)))
		        (:instance fmul-fzero-2 (f e) (x (PSHIFT (PONE (CDR E)) (+ -1 K) (CDR E))))
			(:instance fzero-id (f e) (x (PSTRIP (CDR C) (CDR E))))))))

(local-defthmd ecomb-pstrip-7
  (implies (and (fieldp f) (feltp c f) (not (equal c (fzero f))) (natp k))
           (equal (pmul (list c) (pshift (pone f) k f) f)
	          (cmul c (pshift (pone f) k f) f)))
  :hints (("Goal" :in-theory (enable pzero pmul))))

(local-defthmd ecomb-pstrip-8
  (implies (and (fieldp f) (feltp c f) (not (equal c (fzero f))) (natp k))
           (equal (cmul c (pshift (pone f) k f) f)
	          (pshift (list c) k f)))
  :hints (("Goal" :in-theory (enable cmul-pshift))
          ("Goal''" :in-theory (enable pone))))

(local-defthmd ecomb-pstrip-9
  (implies (and (fieldp e) (consp e) (feltp c (cdr e)) (not (equal c (fzero (cdr e)))) (natp k) (< k (degree (car e))))
           (equal (prem (pshift (list c) k (cdr e)) (car e) (cdr e))
	          (pshift (list c) k (cdr e))))
  :hints (("Goal" :in-theory (enable polyp)
                  :use ((:instance polyp-pshift (x (list c)) (f (cdr e)))
                        (:instance prem-equal (x (pshift (list c) k (cdr e))) (y (car e)) (f (cdr e)))))))

(local-defthmd ecomb-pstrip-10
  (implies (and (fieldp e) (consp e) (feltp c (cdr e)) (not (equal c (fzero (cdr e)))) (natp k) (< k (degree (car e))))
           (equal (fmul (list c) (pshift (pone (cdr e)) k (cdr e)) e) 
	          (monomial c k (cdr e))))
  :hints (("Goal" :in-theory (enable monomial fmul)
                  :use (ecomb-pstrip-9
		        (:instance ecomb-pstrip-7 (f (cdr e)))
                        (:instance ecomb-pstrip-8 (f (cdr e)))))))

(local-defthmd ecomb-pstrip-11
  (implies (and (fieldp e) (consp e)
                (INTEGERP K) (< 1 K)
                (< k (LEN (CAR E)))
                (ELISTNP c k (cdr e))
                (NOT (EQUAL (CAR C) (FZERO (CDR E)))))
           (and (polyp c (cdr e))
	        (consp (cdr c))))
  :hints (("Goal" :in-theory (enable polyp)
                  :use ((:instance len-elistnp (l c) (e (cdr e)))
		        (:instance elistnp-feltsp (l c) (e (cdr e)))))))

(local-defthmd ecomb-pstrip-12
  (IMPLIES (AND (FIELDP E) (CONSP E)
                (INTEGERP K) (< 1 K)
                (< k (LEN (CAR E)))
                (ELISTNP c k (cdr e))
                (NOT (EQUAL (CAR C) (FZERO (CDR E)))))
           (EQUAL (FADD (FMUL (LIST (CAR C))
                              (PSHIFT (PONE (CDR E)) (+ -1 K) (CDR E))
                              E)
                        (PSTRIP (CDR C) (CDR E))
                        E)
                  C))
  :hints (("Goal" :in-theory (enable fadd head tail)
                  :use (ecomb-pstrip-11
		        (:instance len-elistnp (l c) (e (cdr e)))
                        (:instance ecomb-pstrip-10 (c (car c)) (k (1- k)))
			(:instance pdecomp (f (cdr e)) (x c))))))

(defthmd ecomb-pstrip
  (implies (and (fieldp e) (consp e) (posp k) (<= k (degree (car e)))
                (elistnp c k (cdr e)))
	   (equal (ecomb c (pid-powers k (cdr e)) e (cdr e))
	          (pstrip c (cdr e))))
  :hints (("Goal" :induct (ecomb-induct c k))  
          ("Subgoal *1/1" :use (ecomb-pstrip-4))
          ("Subgoal *1/2.2" :use (ecomb-pstrip-6))
          ("Subgoal *1/2.1" :use (ecomb-pstrip-12))))

(defthmd ecomb-simple-extension-basis
  (implies (and (fieldp e) (consp e)
                (elistnp c (degree (car e)) (cdr e)))
	   (equal (ecomb c (simple-extension-basis e) e (cdr e))
	          (pstrip c (cdr e))))
  :hints (("Goal" :in-theory (enable simple-extension-basis)
                  :use ((:instance ecomb-pstrip (k (degree (car e))))
		        (:instance degree-car-field (f e))))))

(defthmd pstrip-elistn0
  (implies (and (fieldp e) (consp e) (posp n)
                (elistnp c n (cdr e))
		(equal (pstrip c (cdr e)) (fzero e)))
	   (equal (elistn0 n (cdr e)) c))
  :hints (("Subgoal *1/2" :in-theory (enable fzero))))

(defthmd simple-extension-basis-lin-indep
  (implies (and (fieldp e) (consp e)
                (elistnp c (degree (car e)) (cdr e))
	        (equal (ecomb c (simple-extension-basis e) e (cdr e))
	               (fzero e)))
	   (equal (elistn0 (degree (car e)) (cdr e))
	          c))
  :hints (("Goal" :use (ecomb-simple-extension-basis
                        (:instance pstrip-elistn0 (n (degree (car e))))))))

(defthmd ebasis0-simple-extension-1
  (implies (and (fieldp e) (consp e))
           (equal (plift (list (fone (cdr e))) (cdr e) e)
	          (list (fone e))))
  :hints (("Goal" :in-theory (enable plift fone))))

(defthmd ebasis0-simple-extension-2
  (implies (and (fieldp e) (consp e))
           (equal (ebasis0 e (cdr e))
	          (fmul-lists (simple-extension-basis e)
		              (list (fone e))
			      e)))
  :hints (("Goal" :expand ((PLIFT (FONE E) (CDR E) E)) :use (ebasis0-simple-extension-1))))

(defthmd ebasis0-simple-extension-3
  (implies (and (fieldp e) (feltsp l e))
           (equal (fmul-lists l (list (fone e)) e)
	          l)))

(defthmd ebasis0-simple-extension
  (implies (and (fieldp e) (consp e))
           (equal (ebasis0 e (cdr e))
	          (simple-extension-basis e)))		  
  :hints (("Goal" :use (ebasis0-simple-extension-2 feltsp-simple-extension-basis
                        (:instance ebasis0-simple-extension-3 (l (simple-extension-basis e)))))))

;;--------------------------------
;; Linear independence of ebasis0
;;--------------------------------

;; The proof requires an alternative formulation of linear independence:

(defun-sk eindepp-sk (l e f)
  (forall (c)
    (implies (and (elistnp c (len l) f)
                  (equal (ecomb c l e f) (fzero e)))
	     (equal c (elistn0 (len l) f)))))

(defthmd eindepp-sk-lemma
  (implies (and (eindepp-sk l e f)
                (elistnp c (len l) f)
                (equal (ecomb c l e f) (fzero e)))
	   (equal (elistn0 (len l) f) c))
  :hints (("Goal" :use (eindepp-sk-necc))))

(defthmd eindepp-sk-witness-lemma
  (let ((c (eindepp-sk-witness l e f)))
     (implies (implies (and (elistnp c (len l) f)
                            (equal (ecomb c l e f) (fzero e)))
	               (equal c (elistn0 (len l) f)))
              (eindepp-sk l e f))))


;; Sum of a list of field elements:

(defun fadd-list (l e)
  (if (consp l)
      (fadd (car l) (fadd-list (cdr l) e) e)
    (fzero e)))

;; A list of m lists of field elements, each of length n:

(defun elistn-listp (x n m e)
  (if (zp m)
      (null x)
    (and (consp x)
         (elistnp (car x) n e)
	 (elistn-listp (cdr x) n (1- m) e))))

;; A list of m lists of zeroes, each of length n:

(defun elistn0-list (n m e)
  (if (zp m)
      ()
    (cons (elistn0 n e)
          (elistn0-list n (1- m) e))))

;; Partition a list of length m * n into m lists of length n:

(defun firstn (n l)
  (if (zp n)
      ()
    (cons (car l) (firstn (1- n) (cdr l)))))

(defun split (n l)
  (if (and (posp n) (>= (len l) n))
      (cons (firstn n l) (split n (nthcdr n l)))
    ()))

(defthmd append-firstn-nthcdr
  (implies (and (natp n) (<= n (len l)))
           (equal (append (firstn n l) (nthcdr n l))
	          l)))

(defun elistnp-nthcdr-induct (x n k)
  (declare (irrelevant x k))
  (if (zp n)
      ()
    (elistnp-nthcdr-induct (cdr x) (1- n) (1- k))))

(defthmd elistnp-nthcdr
  (implies (and (natp n) (natp k) (<= n k) (elistnp x k f))
           (elistnp (nthcdr n x) (- k n) f))
  :hints (("Goal" :induct (elistnp-nthcdr-induct x n k))))

(defthmd elistnp-firstn
  (implies (and (natp n) (natp k) (<= n k) (elistnp x k f))
           (elistnp (firstn n x) n f)))

(local-defun split-elistnp-induct (m n x)
  (declare (irrelevant n x))
  (if (zp m)
      ()
    (split-elistnp-induct (1- m) n (nthcdr n x))))

(defthmd split-elistnp
  (implies (and (fieldp f) (natp m) (posp n) (elistnp x (* m n) f))
           (elistn-listp (split n x) n m f))
  :hints (("Goal" :induct (split-elistnp-induct m n x))
          ("Subgoal *1/2" :use ((:instance len-elistnp (l x) (k (* m n)) (e f))
	                        (:instance elistnp-nthcdr (k (* m n)))
	                        (:instance elistnp-firstn (k (* m n)))))))

;; List of linear combinations of b:

(defun ecomb-list (c b e f)
  (if (consp c)
      (cons (ecomb (car c) b e f)
            (ecomb-list (cdr c) b e f))
    ()))

(defthmd elistnp-ecomb-list
  (implies (and (extensionp e f)
                (elistn-listp c n m f)
		(elistnp b n e))
	   (elistnp (ecomb-list c b e f) m e)))
	 
;; Decomposition of a linear combination:

(defun ecomb-lists (c b e f)
  (if (consp c)
      (cons (ecomb (car c) (car b) e f)
            (ecomb-lists (cdr c) (cdr b) e f))
    ()))

(defun ecomb-decomp-induct (c b m n)
  (declare (irrelevant b c n))
  (if (zp m)
      ()
    (ecomb-decomp-induct (nthcdr n c) (nthcdr n b) (1- m) n)))

(local-defthmd ecomb-decomp-1
  (implies (and (extensionp e f) (natp n) (natp k) (<= n k)
                (elistnp c k f) (elistnp b k e))
           (equal (ecomb c b e f)
                  (fadd (ecomb (firstn n c) (firstn n b) e f)
                        (ecomb (nthcdr n c) (nthcdr n b) e f)
                        e)))			
  :hints (("subgoal *1/1" :use ((:instance feltp-ecomb (c (cdr c)) (l (cdr b)) (n (1- k)))))
          ("Subgoal *1/9" :use ((:instance feltp-ecomb (c (firstn (1- n) (cdr c))) (l (firstn (1- n) (cdr b))) (n (1- n)))
	                        (:instance feltp-ecomb (c (nthcdr (1- n) (cdr c))) (l (nthcdr (1- n) (cdr b))) (n (- k n)))
				(:instance elistnp-nthcdr (n (1- n)) (x c))
				(:instance elistnp-nthcdr (n (1- n)) (x b) (f e))
				(:instance elistnp-firstn (n (1- n)) (x (cdr c)) (k (1- k)))
				(:instance elistnp-firstn (n (1- n)) (x (cdr b)) (f e) (k (1- k)))
	                        (:instance fadd-assoc (f e) (x (FMUL (CAR B) (FLIFT (CAR C) F E) E))
	                                                    (y (ECOMB (FIRSTN (+ -1 N) (CDR C))
                                                                      (FIRSTN (+ -1 N) (CDR B))
                                                                      E F))
							    (z (ECOMB (CDR (NTHCDR (+ -1 N) C))
                                                                      (CDR (NTHCDR (+ -1 N) B))
                                                                      E F)))))))

(defthmd ecomb-decomp
  (implies (and (extensionp e f) (natp m) (natp n)
                (elistnp c (* m n) f)
		(elistnp b (* m n) e))
	   (equal (ecomb c b e f)
	          (fadd-list (ecomb-lists (split n c) (split n b) e f) e)))
  :hints (("Goal" :induct (ecomb-decomp-induct c b m n))
          ("Subgoal *1/2" :use ((:instance ecomb-decomp-1 (k (* m n)))
	                        (:instance elistnp-nthcdr (x c) (k (* m n)))
	                        (:instance elistnp-nthcdr (x b) (f e) (k (* m n)))
				(:instance len-elistnp (l c) (e f) (k (* m n)))
				(:instance len-elistnp (l b) (k (* m n)))))))

(defthm firstn-append
  (implies (true-listp x)
           (equal (firstn (len x) (append x y))
	          x)))

(defthm nthcdr-append
  (equal (nthcdr (len x) (append x y))
	 y))

(defthmd split-append
  (implies (and (true-listp x) (consp x))
           (equal (split (len x) (append x y))
	          (cons x (split (len x) y)))))

(defthm consp-fmul-list
  (implies (consp b)
           (consp (fmul-list a (plift b f e) e))))

(local-defthmd fadd-list-ecomb-1
  (implies (and (extensionp e f) (consp e) (natp m) (natp n)
                (elistn-listp c n m f)
		(elistnp b1 m e) (consp b1)
		(elistnp b2 n (cdr e)) (consp b2))
	   (equal (fadd-list (ecomb-lists c (split n (fmul-lists b1 (plift b2 (cdr e) e) e)) e f) e)
	          (fadd (ecomb (car c) (fmul-list (car b1) (plift b2 (cdr e) e) e) e f)
                        (fadd-list (ecomb-lists (cdr c) (split n (fmul-lists (cdr b1) (plift b2 (cdr e) e) e)) e f) e)
	                e)))
  :hints (("Goal" :in-theory (enable len-elistnp)
                  :use ((:instance split-append (x (fmul-list (car b1) (plift b2 (cdr e) e) e))
                                                (y (fmul-lists (cdr b1) (plift b2 (cdr e) e) e)))))))

(local-defthmd fadd-list-ecomb-2
  (implies (and (extensionp e f) (consp e) (not (equal e f)) (natp m) (natp n)
                (elistn-listp c n m f)
		(elistnp b1 m e) (consp b1)
		(elistnp b2 n (cdr e)) (consp b2))
	   (equal (fadd (fmul (flift (ecomb (car c) b2 (cdr e) f) (cdr e) e) (car b1) e)
                        (ecomb (ecomb-list (cdr c) b2 (cdr e) f) (cdr b1) e (cdr e))
	                e)
                  (ecomb (ecomb-list c b2 (cdr e) f) b1 e (cdr e)))))

(defthm flift-flift
  (implies (and (extensionp e f) (consp e) (not (equal e f)) (feltp x f))
           (equal (flift (flift x f (cdr e)) (cdr e) e)
	          (flift x f e)))
  :hints (("Goal" :in-theory (enable flift)
                  :use ((:instance len-extends (e (cdr e))))
                  :expand ((FLIFTN (FLIFTN X (+ (- (LEN F)) (LEN (CDR E)))) 1)))))

(in-theory (disable flift-cdr))

(defthmd flift-ecomb
  (implies (and (extensionp e f) (consp e) (not (equal e f)) (natp n)
                (elistnp c n f)
		(elistnp b2 n (cdr e)))
	   (equal (flift (ecomb c b2 (cdr e) f) (cdr e) e)
                  (ecomb c (plift b2 (cdr e) e) e f)))
  :hints (("Subgoal *1/2" :in-theory (enable fzero))
          ("Subgoal *1/1" :in-theory (e/d () (flift-cdr))
	                  :use ((:instance feltp-ecomb (n (1- n)) (c (cdr c)) (l (cdr b2)) (e (cdr e)))
			        (:instance feltp-ecomb (n (1- n)) (c (cdr c)) (l (PLIFT (CDR B2) (CDR E) E)))
			        (:instance fadd-comm (f e) (x (ECOMB (CDR C) (PLIFT (CDR B2) (CDR E) E) E F))
				                     (y (FMUL (FLIFT (CAR C) F E) (FLIFT (CAR B2) (CDR E) E) E)))))))

(local-defthmd fadd-list-ecomb-4
  (implies (and (fieldp f) (feltp x f) (feltp b f) (feltp c f) (feltp e f))
           (equal (fadd (fmul c (fmul x b f) f) (fmul e x f) f)
	          (fmul (fadd (fmul b c f) e f) x f)))
  :hints (("Goal" :use ((:instance fmul-comm (y b))
                        (:instance fmul-assoc (x c) (y b) (z x))
                        (:instance fmul-comm (x b) (y c))
                        (:instance fmul-comm (y (fmul b c f)))
                        (:instance fmul-comm (y e))
                        (:instance fdistrib (y (fmul b c f)) (z e))
                        (:instance fmul-comm (y (fadd (fmul b e f) e f)))))))

(defthmd fmul-ecomb
  (implies (and (extensionp e f) (natp n)
                (feltp x e)
                (elistnp c n f)
		(elistnp b n e))
	   (equal (ecomb c (fmul-list x b e) e f)
	          (fmul (ecomb c b e f) x e)))		  
  :hints (("Subgoal *1/5" :use ((:instance fadd-list-ecomb-4 (f e) (b (car b)) (c (flift (car c) f e))
                                                             (e (ECOMB (CDR C) (CDR B) E F)))
                                (:instance feltp-ecomb (n (1- n)) (c (cdr c)) (l (cdr b)))))))

(defthmd fadd-list-ecomb-step
  (implies (and (extensionp e f) (consp e) (not (equal e f)) (natp m) (natp n)
                (elistn-listp c n m f)
		(elistnp b1 m e) (consp b1)
		(elistnp b2 n (cdr e)) (consp b2)
		(equal (fadd-list (ecomb-lists (cdr c) (split n (fmul-lists (cdr b1) (plift b2 (cdr e) e) e)) e f) e)
		       (ecomb (ecomb-list (cdr c) b2 (cdr e) f) (cdr b1) e (cdr e))))
	   (equal (fadd-list (ecomb-lists c (split n (fmul-lists b1 (plift b2 (cdr e) e) e)) e f) e)
	          (ecomb (ecomb-list c b2 (cdr e) f) b1 e (cdr e))))
  :hints (("Goal" :use (fadd-list-ecomb-1 fadd-list-ecomb-2
                        (:instance flift-ecomb (c (car c)))
			(:instance fmul-ecomb (c (car c)) (x (car b1)) (b (plift b2 (cdr e) e)))))))
			
;; Proof:

;; (fadd-list (ecomb-lists c (split n (fmul-lists b1 (plift b2 (cdr e) e) e)) e f) e)
;;   = (fadd (ecomb (car c) (firstn n (fmul-lists b1 (plift b2 (cdr e) e) e)) e f)
;;           (fadd-list (ecomb-lists (cdr c) (split n (nthcdr n (fmul-lists b1 (plift b2 (cdr e) e) e))) e f) e)
;; 	     e)
;;   = (fadd (ecomb (car c) (fmul-list (car b1) (plift b2 (cdr e) e) e) e f)
;;           (fadd-list (ecomb-lists (cdr c) (split n (fmul-lists (cdr b1) (plift b2 (cdr e) e) e)) e f) e)
;; 	     e)
;;   = (fadd (ecomb (car c) (fmul-list (car b1) (plift b2 (cdr e) e) e) e f)
;;           (ecomb (ecomb-list (cdr c) b2 (cdr e) f) (cdr b1) e (cdr e))
;; 	     e)
;;   = (fadd (fmul (ecomb (car c) (plift b2 (cdr e) e) e f) (car b1) e)
;;           (ecomb (ecomb-list (cdr c) b2 (cdr e) f) (cdr b1) e (cdr e))
;; 	     e)
;;   = (fadd (fmul (flift (ecomb (car c) b2 (cdr e) f) (cdr e) e) (car b1) e)
;;           (ecomb (ecomb-list (cdr c) b2 (cdr e) f) (cdr b1) e (cdr e))
;; 	     e)
;;   = (ecomb (ecomb-list c b2 (cdr e) f) b1 e (cdr e))

(local-defthmd fadd-list-ecomb
  (implies (and (extensionp e f) (not (equal e f)) (natp m) (natp n)
                (elistn-listp c n m f)
		(elistnp b1 m e) (consp b1)
		(elistnp b2 n (cdr e)) (consp b2))
	   (equal (fadd-list (ecomb-lists c (split n (fmul-lists b1 (plift b2 (cdr e) e) e)) e f) e)
	          (ecomb (ecomb-list c b2 (cdr e) f) b1 e (cdr e))))
  :hints (("Subgoal *1/1" :use (fadd-list-ecomb-step))))


(local-defthmd ecomb-list-elistn0-listp-step
  (implies (and (extensionp e f)
                (elistnp b n e)
                (elistn-listp c (len b) m f)
		(eindepp-sk b e f)
		(equal (ecomb-list c b e f)
		       (elistn0 m e))
		(equal (elistn0-list (len b) (1- m) f)
                       (cdr c)))
	   (equal (elistn0-list (len b) m f)
	          c))
  :hints (("Goal" :use ((:instance eindepp-sk-lemma (c (car c)) (l b))))))

(defthmd ecomb-list-elistn0-listp
  (implies (and (extensionp e f)
                (elistnp b n e)
                (elistn-listp c (len b) m f)
		(eindepp-sk b e f)
		(equal (ecomb-list c b e f)
		       (elistn0 m e)))
	   (equal (elistn0-list (len b) m f)
	          c))
  :hints (("Subgoal *1/2" :use (ecomb-list-elistn0-listp-step))))

;; Proof:

;; (ecomb-list c b e f) = (cons (ecomb (car c) b e f) (ecomb-list (cdr c) b e f))
;;                      = (elistn0 m e)

;; => (ecomb (car c) b e f) = (fzero e)
;;    (ecomb-list (cdr c) b e f) = (elistn0 (1- m) e)

;; => (car c) = (elistn0 (len b) e)                [eindepp-sk-lemma]
;;    (cdr c) = (elistn0-list (len b) (1- m) f)    [induction]

;; => c = (elistn0-list (len b) m f)


(defthmd append-firstn-nthcdr
  (implies (and (natp n) (<= n (len l)))
           (equal (append (firstn n l) (nthcdr n l))
	          l)))

(defthmd append-elistn0
  (implies (and (natp m) (natp n))
           (equal (append (elistn0 m f) (elistn0 n f))
	          (elistn0 (+ m n) f))))

(defthmd split-elistn0
  (implies (and (fieldp f) (posp n) (natp m) (elistnp c (* m n) f)
                (equal (elistn0-list n m f) (split n c)))
	   (equal (elistn0 (* m n) f)
	          c))
  :hints (("Goal" :induct (split-elistnp-induct m n c))
          ("Subgoal *1/2" :in-theory (enable len-elistnp)
	                  :use ((:instance elistnp-nthcdr (x c) (k (* m n)))
	                        (:instance append-firstn-nthcdr (l c))
				(:instance append-elistn0 (m n) (n (* (1- m) n))))))) 

(local-defthmd elindepp-ebasis0-1
  (implies (and (extensionp e f) (not (equal e f))
                (elistnp c (edegree e f) f)
		(equal (ecomb c (ebasis0 e f) e f) (fzero e)))
	   (equal (fzero e)
	          (fadd-list (ecomb-lists (split (edegree (cdr e) f) c)
		                          (split (edegree (cdr e) f) (ebasis0 e f))
					  e f)
			     e)))	          
  :hints (("Goal" :in-theory (disable len-ebasis0 ebasis0)
                  :use (elistnp-ebasis0 edegree
		        (:instance degree-car-field (f e))
		        (:instance ecomb-decomp (b (ebasis0 e f)) (m (degree (car e))) (n (edegree (cdr e) f)))))))

(local-defthmd elindepp-ebasis0-2
  (implies (and (extensionp e f) (not (equal e f)) (not (equal (cdr e) f))
                (elistnp c (edegree e f) f))
	   (and (elistn-listp (split (edegree (cdr e) f) c) (edegree (cdr e) f) (degree (car e)) f)
		(elistnp (simple-extension-basis e) (degree (car e)) e) (consp (simple-extension-basis e))
		(elistnp (ebasis0 (cdr e) f) (edegree (cdr e) f) (cdr e)) (consp (ebasis0 (cdr e) f))))
  :hints (("Goal" :use (elistnp-simple-extension-basis
                        (:instance edegree-lower-bound (e (cdr e)))
                        (:instance split-elistnp (x c) (n (edegree (cdr e) f)) (m (degree (car e))))
                        (:instance degree-car-field (f e))
			(:instance elistnp-ebasis0 (e (cdr e)))))))

(local-defthmd elindepp-ebasis0-3
  (implies (and (extensionp e f) (not (equal e f)) (not (equal (cdr e) f))
                (elistnp c (edegree e f) f))
	   (equal (fadd-list (ecomb-lists (split (edegree (cdr e) f) c)
		                          (split (edegree (cdr e) f) (ebasis0 e f))
					  e f)
			     e)
		  (ecomb (ecomb-list (split (edegree (cdr e) f) c) (ebasis0 (cdr e) f) (cdr e) f) (simple-extension-basis e) e (cdr e))))
  :hints (("Goal" :expand ((ebasis0 e f))
                  :use (elindepp-ebasis0-2
		        (:instance fadd-list-ecomb (n (edegree (cdr e) f)) (m (degree (car e)))
		                                   (b1 (simple-extension-basis e)) (b2 (ebasis0 (cdr e) f))
		                                   (c (split (edegree (cdr e) f) c)))))))

(local-defthmd elindepp-ebasis0-4
  (implies (and (extensionp e f) (not (equal e f)) (not (equal (cdr e) f))
                (elistnp c (edegree e f) f)
		(equal (ecomb c (ebasis0 e f) e f) (fzero e)))
	   (equal (fzero e)
		  (ecomb (ecomb-list (split (edegree (cdr e) f) c) (ebasis0 (cdr e) f) (cdr e) f)
		         (simple-extension-basis e)
			 e (cdr e))))
  :hints (("Goal" :use (elindepp-ebasis0-1 elindepp-ebasis0-3))))

(local-defthmd elindepp-ebasis0-5
  (implies (and (extensionp e f) (not (equal e f)) (not (equal (cdr e) f))
                (elistnp c (edegree e f) f)
		(equal (ecomb c (ebasis0 e f) e f) (fzero e)))
	   (equal (ecomb-list (split (edegree (cdr e) f) c) (ebasis0 (cdr e) f) (cdr e) f)
	          (elistn0 (degree (car e)) (cdr e))))
  :hints (("Goal" :use (elindepp-ebasis0-4
                        (:instance edegree-lower-bound (e (cdr e)))
                        (:instance elistnp-ecomb-list (c (split (edegree (cdr e) f) c)) (b (ebasis0 (cdr e) f))
			                              (m (degree (car e))) (n (edegree (cdr e) f)) (e (cdr e)))
			(:instance elistnp-ebasis0 (e (cdr e)))
			(:instance split-elistnp (x c) (n (edegree (cdr e) f)) (m (degree (car e))))
                        (:instance simple-extension-basis-lin-indep
			  (c (ecomb-list (split (edegree (cdr e) f) c) (ebasis0 (cdr e) f) (cdr e) f)))))))

(local-defthmd elindepp-ebasis0-6
  (implies (and (extensionp e f) (not (equal e f)) (not (equal (cdr e) f))
                (eindepp-sk (ebasis0 (cdr e) f) (cdr e) f)
                (elistnp c (edegree e f) f)
		(equal (ecomb c (ebasis0 e f) e f) (fzero e)))
	   (equal (elistn0-list (edegree (cdr e) f) (degree (car e)) f)
	          (split (edegree (cdr e) f) c)))
  :hints (("Goal" :use (elindepp-ebasis0-5
                        (:instance edegree-lower-bound (e (cdr e)))
			(:instance elistnp-ebasis0 (e (cdr e)))
			(:instance split-elistnp (x c) (n (edegree (cdr e) f)) (m (degree (car e))))
                        (:instance ecomb-list-elistn0-listp (c (split (edegree (cdr e) f) c)) (b (ebasis0 (cdr e) f))
			                                    (n (edegree (cdr e) f)) (m (degree (car e))) (e (cdr e)))))))

(defthmd elindepp-ebasis0
  (implies (and (extensionp e f) (not (equal e f)) (not (equal (cdr e) f))
                (eindepp-sk (ebasis0 (cdr e) f) (cdr e) f)
                (elistnp c (edegree e f) f)
		(equal (ecomb c (ebasis0 e f) e f) (fzero e)))
	   (equal (elistn0 (edegree e f) f)
	          c))
  :hints (("Goal" :use (elindepp-ebasis0-6
                        (:instance edegree-lower-bound (e (cdr e)))
                        (:instance split-elistn0 (m (degree (car e))) (n (edegree (cdr e) f)))))))

;; Proof:

;; Let m = (degree (car e), n = (edegree (cdr e) f), b1 = (simple-extension-basis e), b2 = (ebasis0 (cdr e) f).

;; (fzero e) = (ecomb c (ebasis0 e f) e f)                                                [hypothesis]
;;           = (fadd-list (ecomb-lists (split n c) (split n (ebasis0 e f)) e f) e)        [ecomb-decomp]
;;           = (fadd-list (ecomb-lists (split n c)                                        [definition of ebasis0]
;; 	                            (split n (fmul-lists b1 (plift b2 (cdr e) e) e))
;; 				    e f)
;; 		       e)
;;           = (ecomb (ecomb-list (split n c) b2 (cdr e) f) b1 e (cdr e))                 [fadd-list-ecomb]               [

;; => (ecomb-list (split n c) b2 (cdr e) f) = (elist0n m (cdr e))                         [simple-extension-basis-lin-indep]

;; => (split n c) = (elistn0-list n m f)                                                  [ecomb-list-elistn0-listp]

;; => c = (elistn0 (* m n) f))


(defthmd eindepp-sk-inductive-case
  (implies (and (extensionp e f) (not (equal e f)) (not (equal (cdr e) f))
                (eindepp-sk (ebasis0 (cdr e) f) (cdr e) f))
	   (eindepp-sk (ebasis0 e f) e f))
  :hints (("Goal" :use ((:instance eindepp-sk-witness-lemma (l (ebasis0 e f)))
                        (:instance elindepp-ebasis0 (c (eindepp-sk-witness (ebasis0 e f) e f)))))))

(defthmd eindepp-sk-base-case
  (implies (and (fieldp e) (consp e))
           (eindepp-sk (ebasis0 e (cdr e)) e (cdr e)))
  :hints (("Goal" :use (ebasis0-simple-extension
                        (:instance eindepp-sk-witness-lemma (l (ebasis0 e (cdr e))) (f (cdr e)))
                        (:instance simple-extension-basis-lin-indep (c (eindepp-sk-witness (ebasis0 e (cdr e)) e (cdr e))))))))

(defthmd eindepp-sk-ebasis0
  (implies (and (extensionp e f) (not (equal e f)))
           (eindepp-sk (ebasis0 e f) e f))
  :hints (("Goal" :induct (len e))
          ("Subgoal *1/1" :use (eindepp-sk-inductive-case eindepp-sk-base-case))))

(defthmd ebasis0-lin-indep
  (implies (and (extensionp e f) (not (equal e f))
                (elistnp c (edegree e f) f)
	        (equal (ecomb c (ebasis0 e f) e f)
	               (fzero e)))
	   (equal (elistn0 (edegree e f) f)
	          c))
  :hints (("Goal" :use (eindepp-sk-ebasis0
                        (:instance eindepp-sk-lemma (l (ebasis0 e f)))))))
			

;;--------------------------------
;; Properties of ecoords0
;;--------------------------------

;; Tow lemmas pertaining to ecoords0 remain to be proved:

;; (defthmd elistnp-ecoords0
;;   (implies (and (extensionp e f) (not (equal e f)) (feltp x e))
;;            (elistnp (ecoords0 x e f) (edegree e f) f))
;;   :hints (("Goal" :use ((:instance elistnp-ecoords0-gen (flg ()))))))


;; (defthmd ebasis0-spans
;;   (implies (and (extensionp e f) (not (equal e f))
;;                 (feltp x e))
;; 	      (equal (ecomb (ecoords0 x e f) (ebasis0 e f) e f)
;; 	             x)))

;; The proofs are facilitated by an alternative formulation of ebasis0-spans:

(defun-sk ebasis0-spans-sk (e f)
  (forall (x)
    (implies (feltp x e)
	     (equal (ecomb (ecoords0 x e f) (ebasis0 e f) e f)
	            x))))

(defthmd ebasis0-spans-sk-lemma
  (implies (and (ebasis0-spans-sk e f)
                (feltp x e))
	   (equal (ecomb (ecoords0 x e f) (ebasis0 e f) e f)
	          x))		  
  :hints (("Subgoal 2" :use (ebasis0-spans-sk-necc))
          ("Subgoal 1" :use (ebasis0-spans-sk-necc))))

(defthmd ebasis0-spans-sk-witness-lemma
  (let ((x (ebasis0-spans-sk-witness e f)))
     (implies (implies (feltp x e)
	               (equal (ecomb (ecoords0 x e f) (ebasis0 e f) e f)
	                      x))
              (ebasis0-spans-sk e f))))

;; First we consider the case of a simple extension, f = (cdr e).

;; In this case, (ecoords0 x e f) reduces to (zpad x (degree (car e)) (cdr e))):

(local-defthmd ecoords0-simple-1
  (implies (and (fieldp e) (feltsp x e))
           (equal (ecoords0-list x e e)
	          x))
  :hints (("Goal" :induct (len x))))

(defthmd ecoords0-simple
  (implies (and (fieldp e) (consp e) (feltp x e))
           (equal (ecoords0 x e (cdr e))
	          (zpad x (degree (car e)) (cdr e))))		  
  :hints (("Goal" :in-theory (enable polyp feltp)
                  :use ((:instance ecoords0-simple-1 (e (cdr e)) (x (zpad x (degree (car e)) (cdr e))))
                        (:instance feltsp-zpad (f (cdr e)) (n (degree (car e))))))))

(local-defthmd feltsp-ecoords0-simple
  (implies (and (fieldp e) (consp e) (feltp x e))
           (feltsp (ecoords0 x e (cdr e)) (cdr e)))		  
  :hints (("Goal" :in-theory (enable polyp feltp)
                  :use ((:instance ecoords0-simple-1 (e (cdr e)) (x (zpad x (degree (car e)) (cdr e))))
                        (:instance feltsp-zpad (f (cdr e)) (n (degree (car e))))))))

(defthmd elistnp-ecoords0-simple
  (implies (and (fieldp e) (consp e) (feltp x e))
           (elistnp (ecoords0 x e (cdr e)) (degree (car e)) (cdr e)))
  :hints (("Goal" :in-theory (enable polyp feltp)
                  :use ((:instance ecoords0-simple-1 (e (cdr e)) (x (zpad x (degree (car e)) (cdr e))))
                        (:instance feltsp-zpad (f (cdr e)) (n (degree (car e))))
			(:instance feltsp-elistnp (e (cdr e)) (l (ecoords0 x e (cdr e))))
			(:instance len-zpad (n (degree (car e))) (f (cdr e)))))))

;; In the case f = (cdr e), (ecoords0 x e f) reduces to (zpad x (degree (car e)) (cdr e))
;; and the following is a consequence of ecomb-simple-extension-basis:

(local-defthmd ecomb-zpad
  (implies (and (fieldp e) (consp e) (feltp x e))
           (equal (ecomb (zpad x (degree (car e)) (cdr e))
	                 (simple-extension-basis e)
			 e (cdr e))
		  x))
  :hints (("Goal" :in-theory (enable feltp)
                  :use ((:instance ecomb-simple-extension-basis (c (zpad x (degree (car e)) (cdr e))))
                        (:instance pstrip-zpad (f (cdr e)) (n (degree (car e))))
			(:instance elistnp-zpad (f (cdr e)) (n (degree (car e))))))))

(defthmd ecomb-ecoords0-simple
  (implies (and (fieldp e) (consp e) (feltp x e))
           (equal (ecomb (ecoords0 x e (cdr e))
	                 (simple-extension-basis e)
			 e (cdr e))
		  x))
  :hints (("Goal" :use (ecoords0-simple ecomb-zpad))))

(defthmd ebasis0-spans-sk-simple
  (implies (and (fieldp e) (consp e))
           (ebasis0-spans-sk e (cdr e)))
  :hints (("Goal" :use (ebasis0-simple-extension
                        (:instance ebasis0-spans-sk-witness-lemma (f (cdr e)))
                        (:instance ecomb-ecoords0-simple (x (ebasis0-spans-sk-witness e (cdr e))))))))

;; For the general case, we use the following induction scheme:

(encapsulate ()

(local (include-book "ordinals/lexicographic-book" :dir :system))

(set-well-founded-relation acl2::l<)

(defun elistnp-ecoords0-induct (flg x e f)
  (declare (xargs :measure (list (len e) (if flg 1 0) (len x))))
  (if flg
      (if (consp x)
          (list (elistnp-ecoords0-induct () (car x) e f)
	        (elistnp-ecoords0-induct t (cdr x) e f))
	())
    (if (equal e f)
        ()
      (and (consp e)
           (elistnp-ecoords0-induct t (zpad x (degree (car e)) (cdr e)) (cdr e) f)))))
)

;; The desired theorem elistnp-ecoords0 is generalized as follows:

(defthmd elistnp-ecoords0-gen
  (implies (and (extensionp e f) (not (equal e f)))
           (if flg
	       (implies (feltsp x e)
	                (elistnp (ecoords0-list x e f) (* (edegree e f) (len x)) f))
	     (implies (and (not (equal e f)) (feltp x e))
	              (elistnp (ecoords0 x e f) (edegree e f) f))))
  :hints (("Goal" :induct (elistnp-ecoords0-induct flg x e f))
          ("Subgoal *1/1" :use ((:instance degree-car-field (f e))
	                        (:instance elistnp-append (x (ECOORDS0 (CAR X) E F)) (y (ECOORDS0-LIST (CDR X) E F))
				                          (m (LEN (EBASIS0 E F))) (n (* (LEN (CDR X)) (LEN (EBASIS0 E F)))))))
	  ("Subgoal *1/3.4" :use (elistnp-ecoords0-simple))
	  ("Subgoal *1/3.3" :in-theory (enable feltp polyp) :use ((:instance feltsp-zpad (n (degree (car e))) (f (cdr e)))))
	  ("Subgoal *1/3.2" :in-theory (enable feltp polyp) :use ((:instance len-zpad (f (cdr e)) (n (degree (car e))))))))

;; We instantiate the above lemma twice, with flg = NIL and flg = T:

(defthmd elistnp-ecoords0
  (implies (and (extensionp e f) (not (equal e f)) (feltp x e))
           (elistnp (ecoords0 x e f) (edegree e f) f))
  :hints (("Goal" :use ((:instance elistnp-ecoords0-gen (flg ()))))))

(defthmd elistnp-ecoords0-list
  (implies (and (extensionp e f) (not (equal e f)) (feltsp x e))
           (elistnp (ecoords0-list x e f) (* (edegree e f) (len x)) f))
  :hints (("Goal" :use ((:instance elistnp-ecoords0-gen (flg t))))))

;; The main lemma:

(local-defthmd ecomb-ecoords0-list-1
  (implies (and (extensionp e f) (not (equal e f)) (not (equal (cdr e) f))
                (posp m)
                (elistnp a m e)
		(elistnp d m (cdr e)))
	   (and (elistnp (ecoords0 (car d) (cdr e) f) (edegree (cdr e) f) f)
	        (elistnp (fmul-list (car a) (plift (ebasis0 (cdr e) f) (cdr e) e) e) (edegree (cdr e) f) e)
		(elistnp (ecoords0-list (cdr d) (cdr e) f) (* (1- m) (edegree (cdr e) f)) f)
		(elistnp (fmul-lists (cdr a) (plift (ebasis0 (cdr e) f) (cdr e) e) e) (* (1- m) (edegree (cdr e) f)) e)))
  :hints (("Goal" :use ((:instance elistnp-ecoords0 (e (cdr e)) (x (car d)))
			(:instance elistnp-ecoords0-list (e (cdr e)) (x (cdr d)))
			(:instance elistnp-ebasis0 (e (cdr e)))
			(:instance len-elistnp (l d) (k m) (e (cdr e)))
 			(:instance elistnp-feltsp (l (cdr d)) (k (1- m)) (e (cdr e)))
			(:instance elistnp-fmul-list (x (car a)) (y (plift (ebasis0 (cdr e) f) (cdr e) e))
			                             (f e) (n (edegree (cdr e) f)))
			(:instance elistnp-fmul-lists (x (cdr a)) (y (plift (ebasis0 (cdr e) f) (cdr e) e))
			                              (f e) (m (1- m)) (n (edegree (cdr e) f)))))))

(local-defthmd ecomb-ecoords0-list-2
  (implies (and (extensionp e f) (not (equal e f)) (not (equal (cdr e) f))
                (posp m)
                (elistnp a m e)
		(elistnp d m (cdr e)))
	   (equal (ecomb (ecoords0-list d (cdr e) f)
		         (fmul-lists a (plift (ebasis0 (cdr e) f) (cdr e) e) e)
			 e f)
		  (fadd (ecomb (ecoords0 (car d) (cdr e) f)
                               (fmul-list (car a) (plift (ebasis0 (cdr e) f) (cdr e) e) e)
		               e f)
	                (ecomb (ecoords0-list (cdr d) (cdr e) f)
                               (fmul-lists (cdr a) (plift (ebasis0 (cdr e) f) (cdr e) e) e)
                               e f)
	                e)))
  :hints (("Goal" :use (ecomb-ecoords0-list-1
                        (:instance ecomb-append (c1 (ecoords0 (car d) (cdr e) f))
                                                (c2 (ecoords0-list (cdr d) (cdr e) f))
						(b1 (fmul-list (car a) (plift (ebasis0 (cdr e) f) (cdr e) e) e))
						(b2 (fmul-lists (cdr a) (plift (ebasis0 (cdr e) f) (cdr e) e) e))
						(m (edegree (cdr e) f))
						(n (* (1- m) (edegree (cdr e) f))))))))

(local-defthmd ecomb-ecoords0-list-3
  (implies (and (extensionp e f) (not (equal e f)) (not (equal (cdr e) f))
                (posp m)
                (elistnp a m e)
		(elistnp d m (cdr e)))
	   (equal (ecomb (ecoords0 (car d) (cdr e) f)
                         (fmul-list (car a) (plift (ebasis0 (cdr e) f) (cdr e) e) e)
		         e f)
		  (fmul (ecomb (ecoords0 (car d) (cdr e) f)                               
                               (plift (ebasis0 (cdr e) f) (cdr e) e)
		               e f)
		        (car a)
		        e)))
  :hints (("Goal" :use ((:instance fmul-ecomb (c (ecoords0 (car d) (cdr e) f))
                                              (x (car a))
					      (b (plift (ebasis0 (cdr e) f) (cdr e) e))
					      (n (edegree (cdr e) f)))
			(:instance elistnp-ebasis0 (e (cdr e)))
                        (:instance elistnp-ecoords0 (e (cdr e)) (x (car d)))))))

(local-defthmd ecomb-ecoords0-list-4
  (implies (and (extensionp e f) (not (equal e f)) (not (equal (cdr e) f))
                (posp m)
                (elistnp a m e)
		(elistnp d m (cdr e)))
	   (equal (fmul (ecomb (ecoords0 (car d) (cdr e) f)                               
                               (plift (ebasis0 (cdr e) f) (cdr e) e)
		               e f)
		        (car a)
		        e)
		  (fmul (flift (ecomb (ecoords0 (car d) (cdr e) f)
                                      (ebasis0 (cdr e) f)
		                      (cdr e) f)
		               (cdr e) e)
		        (car a)
		        e)))
  :hints (("Goal" :use ((:instance flift-ecomb (c (ecoords0 (car d) (cdr e) f))
                                               (b2 (ebasis0 (cdr e) f))
					       (n (edegree (cdr e) f)))
			(:instance elistnp-ebasis0 (e (cdr e)))
                        (:instance elistnp-ecoords0 (e (cdr e)) (x (car d)))))))

(local-defthmd ecomb-ecoords0-list-5
  (implies (and (extensionp e f) (not (equal e f)) (not (equal (cdr e) f))
                (ebasis0-spans-sk (cdr e) f)
                (posp m)
                (elistnp a m e)
		(elistnp d m (cdr e)))
	   (equal (ecomb (ecoords0 (car d) (cdr e) f)
                         (ebasis0 (cdr e) f)
		         (cdr e) f)
		  (car d)))
  :hints (("Goal" :use ((:instance ebasis0-spans-sk-lemma (e (cdr e)) (x (car d)))))))

(local-defthmd ecomb-ecoords0-list-6
  (implies (and (extensionp e f) (not (equal e f)) (not (equal (cdr e) f))
                (ebasis0-spans-sk (cdr e) f)
                (posp m)
                (elistnp a m e)
		(elistnp d m (cdr e))
		(equal (ecomb (ecoords0-list (cdr d) (cdr e) f)
                              (fmul-lists (cdr a) (plift (ebasis0 (cdr e) f) (cdr e) e) e)
                              e f)
		       (ecomb (cdr d) (cdr a) e (cdr e))))
	   (equal (ecomb (ecoords0-list d (cdr e) f)
		         (fmul-lists a (plift (ebasis0 (cdr e) f) (cdr e) e) e)
			 e f)
		  (ecomb d a e (cdr e))))
  :hints (("Goal" :use (ecomb-ecoords0-list-2 ecomb-ecoords0-list-3 ecomb-ecoords0-list-4 ecomb-ecoords0-list-5))))

(defthmd ecomb-ecoords0-list
  (implies (and (extensionp e f) (not (equal e f)) (not (equal (cdr e) f))
                (ebasis0-spans-sk (cdr e) f)
                (natp m)
                (elistnp a m e)
		(elistnp d m (cdr e)))
	   (equal (ecomb d a e (cdr e))
	          (ecomb (ecoords0-list d (cdr e) f)
		         (fmul-lists a (plift (ebasis0 (cdr e) f) (cdr e) e) e)
			 e f)))
  :hints (("Subgoal *1/1" :use (ecomb-ecoords0-list-6))))

;; Proof by induction:

;; (ecomb (ecoords0-list d (cdr e) f)
;;        (fmul-lists a (plift (ebasis0 (cdr e) f) (cdr e) e) e)
;;        e f)
;;   = (fadd (ecomb (ecoords0 (car d) (cdr e) f)                                  [ecomb-append]
;;                  (fmul-list (car a) (plift (ebasis0 (cdr e) f) (cdr e) e) e)
;; 		    e f)
;; 	     (ecomb (ecoords0-list (cdr d) (cdr e) f)
;;                  (fmul-lists (cdr a) (plift (ebasis0 (cdr e) f) (cdr e) e) e)
;;                  e f)
;; 	     e)
;;   = (fadd (ecomb (ecoords0 (car d) (cdr e) f)                                  [induction]
;;                  (fmul-list (car a) (plift (ebasis0 (cdr e) f) (cdr e) e) e)
;; 		    e f)
;; 	     (ecomb (cdr d) (cdr a) e (cdr e))
;; 	     e)
;;   = (fadd (fmul (ecomb (ecoords0 (car d) (cdr e) f)                            [fmul-ecomb]
;;                        (plift (ebasis0 (cdr e) f) (cdr e) e)
;; 		          e f)
;; 		   (car a)
;; 	   	   e)		
;; 	     (ecomb (cdr d) (cdr a) e (cdr e))
;; 	     e)
;;   = (fadd (fmul (flift (ecomb (ecoords0 (car d) (cdr e) f)                     [flift-ecomb]
;;                               (ebasis0 (cdr e) f)
;; 		                 (cdr e) f)
;; 		          (cdr e) e)
;; 		   (car a)
;; 	  	   e)		
;; 	     (ecomb (cdr d) (cdr a) e (cdr e))
;; 	     e)
;;   = (fadd (fmul (flift (car d) (cdr e) e)                                      [ebasis0-spans-sk-lemma]
;; 		   (car a)
;; 		   e)		
;; 	     (ecomb (cdr d) (cdr a) e (cdr e))
;; 	     e)
;;   = (ecomb d a e (cdr e))                                                      [definition of ecomb]
		         
;; We instantiate ecomb-ecoords0-list with

;;    m = (degree (car e))
;;    a = (simple-extension-basis e)
;;    d = (zpad x (degree (car e)) (cdr e))

;; where (feltp x e), and combine this result with elistnp-simple-extension-basis, ecomb-ecoords0-simple,
;; ecoords0-simple, and elistnp-ecoords0-simple:

(local-defthmd ecomb-ecoords0-list-8
  (implies (and (extensionp e f) (not (equal e f)) (not (equal (cdr e) f)) (fieldp e) (consp e) (NATP (DEGREE (CAR E)))
                (ebasis0-spans-sk (cdr e) f)
		(feltp x e))
	   (equal (ecomb (ecoords0 x e (cdr e)) (simple-extension-basis e) e (cdr e))
	          (ecomb (ecoords0-list (ecoords0 x e (cdr e)) (cdr e) f)
		         (fmul-lists (simple-extension-basis e) (plift (ebasis0 (cdr e) f) (cdr e) e) e)
			 e f)))
  :hints (("Goal" :in-theory (theory 'minimal-theory)
                  :use (elistnp-simple-extension-basis ecoords0-simple elistnp-ecoords0-simple
                        (:instance ecomb-ecoords0-list (m (degree (car e))) (a (simple-extension-basis e))
                                                       (d (zpad x (degree (car e)) (cdr e))))))))

(local-defthmd ecomb-ecoords0-list-9
  (implies (and (extensionp e f) (not (equal e f)) (not (equal (cdr e) f))
                (ebasis0-spans-sk (cdr e) f)
		(feltp x e))
	   (equal (ecomb (ecoords0-list (ecoords0 x e (cdr e)) (cdr e) f)
		         (ebasis0 e f)
			 e f)
	          x))
  :hints (("Goal" :use (ecomb-ecoords0-list-8 ecomb-ecoords0-simple
		        (:instance degree-car-field (f e))))))

(local-defthmd ecomb-ecoords0-list-10
  (implies (and (extensionp e f) (not (equal e f)) (not (equal (cdr e) f))
                (ebasis0-spans-sk (cdr e) f)
		(feltp x e))
	   (equal (ecoords0-list (ecoords0 x e (cdr e)) (cdr e) f)
	          (ecoords0 x e f)))
  :hints (("Goal" :use (ecoords0-simple))))

(defthmd ecomb-ecoords0
  (implies (and (extensionp e f) (not (equal e f)) (not (equal (cdr e) f))
                (ebasis0-spans-sk (cdr e) f)
		(feltp x e))
	   (equal (ecomb (ecoords0 x e f)
		         (ebasis0 e f)
			 e f)
	          x))
  :hints (("Goal" :use (ecomb-ecoords0-list-9 ecomb-ecoords0-list-10))))

;; Apply ebasis0-spans-sk-witness-lemma:

(defthmd ebasis-spans-step
  (implies (and (extensionp e f) (not (equal e f)) (not (equal (cdr e) f))
                (ebasis0-spans-sk (cdr e) f))
	   (ebasis0-spans-sk e f))
  :hints (("Goal" :use (ebasis0-spans-sk-witness-lemma
                        (:instance ecomb-ecoords0 (x (ebasis0-spans-sk-witness e f)))))))

;; Apply induction:

(defthmd ebasis0-spans-lemma
  (implies (and (extensionp e f) (not (equal e f)))
	   (ebasis0-spans-sk e f))	   
  :hints (("Goal" :induct (len e))
          ("Subgoal *1/1" :use (ebasis0-spans-sk-simple ebasis-spans-step))))

;; Apply ebasis0-spans-sk-lemma:

(defthmd ebasis0-spans
  (implies (and (extensionp e f) (not (equal e f))
                (feltp x e))
	   (equal (ecomb (ecoords0 x e f) (ebasis0 e f) e f)
	          x))
  :hints (("Goal" :use (ebasis0-spans-lemma ebasis0-spans-sk-lemma))))


;;----------------------------------------------------------------------------------------------------------
;;                                              Minimal Polynomials
;;----------------------------------------------------------------------------------------------------------

;; We shall show that every extension e of f (under our definition) is algebraic over f, i.e, every element
;; of e is a root of (the fifting of) some polynomial over f, and consequently of a unique irreducible
;; polynomial, over f.  The degree of this irreducible polynomial is at most the degree of the extension.

;; We have proved that in a vector space of degree d, any list l of vectors with (len l) > d is linearly
;; dependent:

(include-book "projects/linear/vectors" :dir :system)

(defthmd not-vindepp-sk-if->-dim
  (implies (and (natp m) (> m (vdim))
		(vlistnp l m))
	   (not (vindepp-sk l))))

;; Let d = (edegree e f).  Since e is a vector space over f of dimension d, functional instantiation of the 
;; above result yields the following:

(in-theory (disable vindepp-sk eindepp-sk))

(in-theory (disable len-ebasis0))

(defthm posp-edegree
  (implies (extensionp e f)
           (posp (edegree e f)))
  :hints (("Goal" :expand ((fieldp e) (extends e f))))
  :rule-classes (:type-prescription :rewrite))

(defmacro eindepp-mac ()
  '(and (extensionp e f) (not (equal e f))))

(defthmd not-eindepp-sk-if->-edegree
  (implies (and (extensionp e f) (not (equal e f))
                (natp m) (> m (edegree e f))
		(elistnp l m e))
	   (not (eindepp-sk l e f)))
  :hints (("Goal" :in-theory (enable vindepp-sk-lemma eindepp-sk-lemma fmul-assoc f*assoc fadd-assoc f+assoc fmul-comm
                                     fadd-comm ebasis0-lin-indep ebasis0-spans elistnp-ecoords0 elistnp-ebasis0 vdistv fdistrib-comm
				     vdistv fdistrib-comm vdistf v*assoc fmul-assoc v+assoc fadd-assoc fadd-comm)
                  :use ((:functional-instance not-vindepp-sk-if->-dim
                          (f0 (lambda () (if (eindepp-mac) (fzero f) (f0))))
                          (f1 (lambda () (if (eindepp-mac) (fone f) (f1))))
                          (fp (lambda (x) (if (eindepp-mac) (feltp x f) (fp x))))
                          (f+ (lambda (x y) (if (eindepp-mac) (fadd x y f) (f+ x y))))
                          (f* (lambda (x y) (if (eindepp-mac) (fmul x y f) (f* x y))))
                          (f- (lambda (x) (if (eindepp-mac) (fneg x f) (f- x))))
                          (f/ (lambda (x) (if (eindepp-mac) (frecip x f) (f/ x))))
                          (vp (lambda (x) (if (eindepp-mac) (feltp x e) (vp x))))
			  (v+ (lambda (x y) (if (eindepp-mac) (fadd x y e) (v+ x y))))
			  (v0 (lambda () (if (eindepp-mac) (fzero e) (v0))))
			  (v- (lambda (x) (if (eindepp-mac) (fneg x e) (v- x))))
			  (v* (lambda (c x) (if (eindepp-mac) (fmul (flift c f e) x e) (v* c x))))
			  (vlistnp (lambda (x n) (if (eindepp-mac) (elistnp x n e) (vlistnp x n))))
			  (vcomb (lambda (flist elist) (if (eindepp-mac) (ecomb flist elist e f) (vcomb flist elist))))
			  (vdim (lambda () (if (eindepp-mac) (edegree e f) (vdim))))
			  (vbasis0 (lambda () (if (eindepp-mac) (ebasis0 e f) (vbasis0))))
			  (vcoords0 (lambda (x) (if (eindepp-mac) (ecoords0 x e f) (vcoords0 x))))
			  (flistnp (lambda (x n) (if (eindepp-mac) (elistnp x n f) (flistnp x n))))
			  (flistn0 (lambda (n) (if (eindepp-mac) (elistn0 n f) (flistn0 n))))
			  (vindepp-sk (lambda (l) (if (eindepp-mac) (eindepp-sk l e f) (vindepp-sk l))))
			  (vindepp-sk-witness (lambda (l) (if (eindepp-mac) (eindepp-sk-witness l e f) (vindepp-sk-witness l)))))))			  
	  ("Subgoal 39" :in-theory (enable vindepp-sk eindepp-sk))	  
	  ("Subgoal 25" :in-theory (enable f*comm))
	  ("Subgoal 24" :in-theory (enable f+comm))
	  ("Subgoal 19" :use ((:instance vindepp-vcomb-v0 (m (vdim)) (l (vbasis0)))))
	  ("Subgoal 15" :use (posp-edegree))
	  ("Subgoal 6" :in-theory (enable v+comm))
	  ("Subgoal 2" :in-theory (enable vdim) :use (len-ebasis0))))


;; According to the definition of eindepp-sk, this may be restated as follows:

(defthmd ecomb-eindepp-sk-witness
  (implies (and (extensionp e f) (not (equal e f))
                (natp m) (> m (edegree e f))
		(elistnp l m e))
           (let ((c (eindepp-sk-witness l e f)))
	     (and (elistnp c m f)
	          (not (equal c (elistn0 m f)))
		  (equal (ecomb c l e f) (fzero e)))))
  :hints (("Goal" :use (eindepp-sk not-eindepp-sk-if->-edegree (:instance len-elistnp (k m))))))

;; In particular, the first d + 1 powers of x are linearly dependent over f:

(defun fpowers (x n e)
  (if (zp n)
      ()
    (cons (fpower x (1- n) e)
          (fpowers x (1- n) e))))

(defthm len-fpowers
  (implies (natp n)
           (equal (len (fpowers x n e))
	          n)))

(defthmd elistnp-fpowers
  (implies (and (fieldp e) (feltp x e) (natp n))
           (elistnp (fpowers x n e) n e)))

;; This produces a nonzero polynomial over f of degree at most d of which x is a root:

(local-defthmd ecomb-feval
  (implies (and (extensionp e f)
                (elistnp c n f)
		(feltp x e))
	   (equal (ecomb c (fpowers x n e) e f)
	          (feval (plift c f e) x e)))
  :hints (("Subgoal *1/2" :in-theory (enable len-elistnp))))

(defthmd ecomb-peval
  (implies (and (extensionp e f)
                (posp n)
		(elistnp c n f)
		(feltp x e))
	   (let ((p (pstrip c f)))
	     (and (polyp p f)
	          (equal (ecomb c (fpowers x n e) e f)
	                 (peval (plift p f e) x e)))))
  :hints (("Goal" :in-theory (enable elistnp-feltsp ecomb-feval)
                  :use ((:instance polyp-pstrip (x c))
		        (:instance polyp-plift (p (pstrip c f)))
			(:instance feltsp-plift (p c))
		        (:instance feval-pstrip (f e) (p (plift c f e)))
			(:instance pstrip-plift (p c))
			(:instance feval-peval (p (plift (pstrip c f) f e)) (f e))))))

(defthmd pstrip-nonzero
  (implies (and (fieldp f) (posp n) (elistnp x n f) (not (equal x (elistn0 n f))))
           (not (equal (pstrip x f) (pzero f))))
  :hints (("Goal" :in-theory (enable pzero))))

;; We multiply this polynomial by the reciprocal of its leading coefficient to produce a monic polynomial
;; with the same properties:

(local-defthmd prootp-zero-poly-1
  (implies (and (extensionp e f) (not (equal e f)) (feltp x e))
           (let* ((l (fpowers x (1+ (edegree e f)) e))
	          (c (eindepp-sk-witness l e f))
	          (p (pstrip c f)))
	     (and (polyp p f)
	          (<= (degree p) (edegree e f))
	          (not (equal p (pzero f)))
	          (equal (peval (plift p f e) x e)
		         (fzero e)))))
  :hints (("Goal" :in-theory (e/d (len-elistnp) (posp-edegree))
                  :use (posp-edegree
		        (:instance ecomb-peval (n (1+ (edegree e f)))
                                               (c (eindepp-sk-witness (fpowers x (1+ (edegree e f)) e) e f)))
			(:instance ecomb-eindepp-sk-witness (m (1+ (edegree e f)))
			                                    (l (fpowers x (1+ (edegree e f)) e)))
			(:instance elistnp-fpowers (n (1+ (edegree e f))))
			(:instance len-pstrip (x (eindepp-sk-witness (fpowers x (1+ (edegree e f)) e) e f)))
			(:instance pstrip-nonzero (n (1+ (edegree e f)))
			                          (x (eindepp-sk-witness (fpowers x (1+ (edegree e f)) e) e f)))))))

(local-defthmd prootp-zero-poly-2
  (implies (and (fieldp f) (polyp p f) (not (equal p (pzero f))))
           (not (equal (car p) (fzero f))))
  :hints (("Goal" :in-theory (enable pzero polyp))))

(local-defthmd prootp-zero-poly-3
  (implies (and (extensionp e f) (feltp x e)
                (polyp p f) (not (equal p (pzero f)))
		(equal (peval (plift p f e) x e)
		       (fzero e)))
           (let ((q (cmul (frecip (car p) f) p f)))
	     (and (polyp q f)
	          (monicp q f)
		  (= (degree q) (degree p))
		  (equal (peval (plift q f e) x e)
		         (fzero e)))))
  :hints (("Goal" :in-theory (enable polyp monicp)
                  :use (polyp-plift prootp-zero-poly-2
		        (:instance polyp-cmul (x p) (c (frecip (car p) f)))
                        (:instance plift-cmul (c (frecip (car p) f)))
			(:instance frecip-not-fzero (x (car p)))
			(:instance peval-cmul (f e) (c (flift (frecip (car p) f) f e)) (q (plift p f e)))))))

(defund zero-poly (x e f)
  (if (equal e f)
      (root-poly x f)
    (let ((p (pstrip (eindepp-sk-witness (fpowers x (1+ (edegree e f)) e) e f) f)))
      (cmul (frecip (car p) f) p f))))

(defthmd prootp-zero-poly
  (implies (and (extensionp e f) (feltp x e))
           (let ((p (zero-poly x e f)))
             (and (polyp p f)
	          (monicp p f)
	          (<= (degree p) (edegree e f))
	          (prootp x (plift p f e) e))))
  :hints (("Goal" :in-theory (enable prootp zero-poly)
                  :use (prootp-zero-poly-1 prootp-root-poly monicp-irreduciblep-root-poly
                        (:instance frecip-not-fzero (x (car p)))
		        (:instance len-cmul (c (frecip (car p) f)) (x (pstrip (eindepp-sk-witness (fpowers x (1+ (edegree e f)) e) e f) f)))
		        (:instance prootp-zero-poly-3 (p (pstrip (eindepp-sk-witness (fpowers x (1+ (edegree e f)) e) e f) f)))))))

(defthmd zero-poly-not-pconstp
  (implies (and (extensionp e f) (feltp x e))
           (>= (degree (zero-poly x e f)) 1))
  :hints (("Goal" :in-theory (enable monicp pzero polyp-plift)
                  :use (prootp-zero-poly
		        (:instance plift-pzero (p (zero-poly x e f)))
		        (:instance prootp-not-pconstp (f e) (p (plift (zero-poly x e f) f e)))))))	   

;; The minimal polynomial of x is computed by factoring (zero-poly x e f) and selecting an irreducible
;; factor of which x is a root:

(defun min-poly-aux (x l e f)
  (if (consp l)
      (if (prootp x (plift (car l) f e) e)
          (car l)
	(min-poly-aux x (cdr l) e f))
    ()))

(defund min-poly (x e f)
  (min-poly-aux x (factorization (zero-poly x e f) f) e f))

(defthmd min-poly-trivial
  (implies (and (fieldp f) (feltp x f))
           (equal (min-poly x f f)
	          (root-poly x f)))
  :hints (("Goal" :in-theory (enable min-poly prootp zero-poly)
                  :expand ((FACTORIZATION (ROOT-POLY X F) f))
                  :use (degree-root-poly peval-root-poly))))

(local-defthmd prootp-min-poly-1
  (implies (and (extensionp e f)
                (feltp x e)
                (monicp-irreduciblep-listp l f)
	        (prootp x (plift (pmul-list l f) f e) e))
	   (let ((p (min-poly-aux x l e f)))
	     (and (member p l)
	          (prootp x (plift p f e) e))))
  :hints (("Subgoal *1/3" :in-theory (enable pone pconstp prootp)
                          :use (plift-id
			        (:instance peval-pconstp (f e) (p (pone e)))))
	  ("Subgoal *1/2" :in-theory (enable polyp-plift)
	                  :use ((:instance plift-pmul (p (car l)) (q (pmul-list (cdr l) f)))
	                        (:instance prootp-pmul (f e) (p (plift (car l) f e)) (q (plift (pmul-list (cdr l) f) f e)))))))

(defthmd prootp-min-poly
  (implies (and (extensionp e f)
                (feltp x e))
	   (let ((p (min-poly x e f)))
	     (and (polyp p f)
	          (monicp p f)
		  (irreduciblep p f)
	          (>= (degree p) 1)
	          (<= (degree p) (edegree e f))
		  (prootp x (plift p f e) e))))
  :hints (("Goal" :in-theory (enable min-poly)
                  :use (prootp-zero-poly zero-poly-not-pconstp
		        (:instance prootp-min-poly-1 (l (factorization (zero-poly x e f) f)))
		        (:instance member-factorization (q (zero-poly x e f)) (p (min-poly x e f)))
			(:instance pmul-list-irreduciblep-factorization (p (zero-poly x e f)))))))

;; Let q be a polynomial over f.  If q is divisible by (min-poly x e f), then clearly x is a root of q.  
;; The converse is also true.  The proof requires the following deceptively simple property of the 
;; greatest common divisor:

(local-defthmd plift-pgcd-1
  (implies (and (extensionp e f)
                (polyp p f) (polyp q f)
		(not (equal p (pzero f)))
		(not (equal q (pzero f))))
	   (and (polyp (pquot p (pgcd p q f) f) f)
	        (equal (pmul (pgcd p q f) (pquot p (pgcd p q f) f) f)
	               p)))
  :hints (("Goal" :use ((:instance polyp-pgcd (x p) (y q))
                        (:instance pgcd-divides (x p) (y q))
			(:instance pgcd-nonzero (x p) (y q))
			(:instance polyp-pquot-prem (x p) (y (pgcd p q f)))
			(:instance pdivides-pquot (y p) (x (pgcd p q f)))))))

(local-defthmd plift-pgcd-2
  (implies (and (extensionp e f)
                (polyp p f) (polyp q f)
		(not (equal p (pzero f)))
		(not (equal q (pzero f))))
	   (and (polyp (plift (pquot p (pgcd p q f) f) f e) e)
	        (polyp (plift (pgcd p q f) f e) e)
		(polyp (plift p f e) e)
	        (pdivides (plift (pgcd p q f) f e)
		          (plift p f e)
			  e)))
  :hints (("Goal" :in-theory (enable polyp-plift)
                  :use (plift-pgcd-1
		        (:instance polyp-pgcd (x p) (y q))
			(:instance pdivides-multiple (f e) (x (plift (pgcd p q f) f e)) (y (plift (pquot p (pgcd p q f) f) f e)))
                        (:instance plift-pmul (p (pgcd p q f)) (q (pquot p (pgcd p q f) f)))))))

(local-defthmd plift-pgcd-3
  (implies (and (extensionp e f)
                (polyp p f) (polyp q f)
		(not (equal p (pzero f)))
		(not (equal q (pzero f))))
	   (and (polyp (pquot q (pgcd p q f) f) f)
	        (equal (pmul (pgcd p q f) (pquot q (pgcd p q f) f) f)
	               q)))
  :hints (("Goal" :use ((:instance polyp-pgcd (x p) (y q))
                        (:instance pgcd-divides (x p) (y q))
			(:instance pgcd-nonzero (x p) (y q))
			(:instance polyp-pquot-prem (x q) (y (pgcd p q f)))
			(:instance pdivides-pquot (y q) (x (pgcd p q f)))))))

(local-defthmd plift-pgcd-4
  (implies (and (extensionp e f)
                (polyp p f) (polyp q f)
		(not (equal p (pzero f)))
		(not (equal q (pzero f))))
	   (and (polyp (plift (pquot q (pgcd p q f) f) f e) e)
	        (polyp (plift (pgcd p q f) f e) e)
		(polyp (plift q f e) e)
	        (pdivides (plift (pgcd p q f) f e)
		          (plift q f e)
			  e)))
  :hints (("Goal" :in-theory (enable polyp-plift)
                  :use (plift-pgcd-3
		        (:instance polyp-pgcd (x p) (y q))
			(:instance pdivides-multiple (f e) (x (plift (pgcd p q f) f e)) (y (plift (pquot q (pgcd p q f) f) f e)))
                        (:instance plift-pmul (p (pgcd p q f)) (q (pquot q (pgcd p q f) f)))))))

(local-defthmd plift-pgcd-5
  (implies (and (extensionp e f)
                (polyp p f) (polyp q f)
		(not (equal p (pzero f)))
		(not (equal q (pzero f))))
	   (and (polyp (plift (pgcd p q f) f e) e)
		(polyp (plift p f e) e)
		(polyp (plift q f e) e)
		(not (equal (plift p f e) (pzero e)))
		(not (equal (plift q f e) (pzero e)))
		(polyp (pgcd (plift p f e) (plift q f e) e) e)
	        (pdivides (plift (pgcd p q f) f e)
		          (pgcd (plift p f e) (plift q f e) e)
			  e)))
  :hints (("Goal" :use (plift-pgcd-2 plift-pgcd-4 plift-pzero
                        (:instance plift-pzero (p q))
		        (:instance polyp-pgcd (x (plift p f e)) (y (plift q f e)) (f e))
			(:instance divides-pgcd (x (plift p f e)) (y (plift q f e)) (z (plift (pgcd p q f) f e)) (f e))))))

(local-defthmd plift-pgcd-6
  (implies (and (extensionp e f)
                (polyp p f) (polyp q f)
		(not (equal p (pzero f)))
		(not (equal q (pzero f))))
	   (let ((r (plift (r$ p q f) f e))
	         (s (plift (s$ p q f) f e)))		 
	     (and (polyp r e)
	          (polyp s e)
		  (equal (padd (pmul r (plift p f e) e)
		               (pmul s (plift q f e) e)
			       e)
			 (plift (pgcd p q f) f e)))))
  :hints (("Goal" :in-theory (enable polyp-plift)
                  :use ((:instance pgcd-linear-combination (x p) (y q))
		        (:instance plift-pmul (p (r$ p q f)) (q p))
		        (:instance plift-pmul (p (s$ p q f)))
			(:instance plift-padd (p (pmul (r$ p q f) p f)) (q (pmul (s$ p q f) q f)))))))

(local-defthmd plift-pgcd-7
  (implies (and (extensionp e f)
                (polyp p f) (polyp q f)
		(not (equal p (pzero f)))
		(not (equal q (pzero f))))
	   (and (polyp (pgcd (plift p f e) (plift q f e) e) e)
	        (pdivides (pgcd (plift p f e) (plift q f e) e) (plift p f e) e)
	        (pdivides (pgcd (plift p f e) (plift q f e) e) (plift q f e) e)))
  :hints (("Goal" :in-theory (enable polyp-plift)
                  :use (plift-pgcd-5
		        (:instance polyp-pgcd (f e) (x (plift p f e)) (y (plift q f e)))
		        (:instance pgcd-divides (f e) (x (plift p f e)) (y (plift q f e)))))))

(local-defthmd plift-pgcd-8
  (implies (and (extensionp e f)
                (polyp p f) (polyp q f)
		(not (equal p (pzero f)))
		(not (equal q (pzero f))))
	   (and (polyp (pgcd (plift p f e) (plift q f e) e) e)
	        (pdivides (pgcd (plift p f e) (plift q f e) e)
		          (plift (pgcd p q f) f e)
			  e)))
  :hints (("Goal" :in-theory (enable polyp-plift)
                  :use (plift-pgcd-6 plift-pgcd-7
		        (:instance pdivides-pmul (f e) (x (pgcd (plift p f e) (plift q f e) e))
			                               (y (plift p f e))
						       (z (plift (r$ p q f) f e)))
		        (:instance pdivides-pmul (f e) (x (pgcd (plift p f e) (plift q f e) e))
			                               (y (plift q f e))
						       (z (plift (s$ p q f) f e)))
			(:instance pmul-comm (f e) (x (plift p f e)) (y (plift (r$ p q f) f e)))
			(:instance pmul-comm (f e) (x (plift q f e)) (y (plift (s$ p q f) f e)))
		        (:instance pdivides-padd (f e) (x (pgcd (plift p f e) (plift q f e) e))
			                               (y (pmul (plift (r$ p q f) f e) (plift p f e) e))
			                               (z (pmul (plift (s$ p q f) f e) (plift q f e) e)))))))

(defthmd monicp-plift
  (implies (and (extensionp e f)
                (polyp p f)
		(monicp p f))
	   (monicp (plift p f e) e))
  :hints (("Goal" :in-theory (enable polyp monicp)
                  :expand (PLIFT P F E)
                  :use (flift-id))))

(local-defthmd plift-pgcd-9
  (implies (and (extensionp e f)
                (polyp p f) (polyp q f)
		(not (equal p (pzero f)))
		(not (equal q (pzero f))))
	   (and (polyp (pgcd (plift p f e) (plift q f e) e) e)
	        (polyp (plift (pgcd p q f) f e) e)
		(monicp (pgcd (plift p f e) (plift q f e) e) e)
	        (monicp (plift (pgcd p q f) f e) e)))
  :hints (("Goal" :in-theory (enable polyp-plift)
                  :use (plift-pzero
		        (:instance plift-pzero (p q))
			(:instance polyp-pgcd (x p) (y q))
		        (:instance polyp-pgcd (x (plift p f e)) (y (plift q f e)) (f e))
			(:instance pgcd-monic (x p) (y q))
		        (:instance pgcd-monic (x (plift p f e)) (y (plift q f e)) (f e))
			(:instance monicp-plift (p (pgcd p q f)))))))

(defthmd plift-pgcd
  (implies (and (extensionp e f)
                (polyp p f) (polyp q f)
		(not (equal p (pzero f)))
		(not (equal q (pzero f))))
           (equal (pgcd (plift p f e) (plift q f e) e)
	          (plift (pgcd p q f) f e)))
  :hints (("Goal" :use (plift-pgcd-5 plift-pgcd-8 plift-pgcd-9 
                        (:instance pdivides-monic-equal (f e)
			                                (x (pgcd (plift p f e) (plift q f e) e))
			                                (y (plift (pgcd p q f) f e)))))))

;; If p is a polynomial over f, let p' denote (plift p f e).  Thus, if p = (min-poly x e f), then x is 
;; a root of p'.  Let q be another polynomial over f such that x is a root of q' and suppose p does not 
;; divide q.  Then (pgcd p q f) = 1, which implies (pgcd p' q' e) = 1.  Thus, we can find r and s such 
;; that rp' + sq' = 1.  Since x is not a root of 1, we have a contradiction:

(local-defthmd min-poly-pdivides-1
  (implies (and (extensionp e f)
                (feltp x e) (polyp q f)
	        (pdivides (min-poly x e f) q f))
           (prootp x (plift q f e) e))
  :hints (("Goal" :in-theory (enable polyp-plift)
                  :use (prootp-min-poly
                        (:instance pdivides-pquot (x (min-poly x e f)) (y q))
			(:instance polyp-pquot-prem (x q) (y (min-poly x e f)))
                        (:instance plift-pmul (p (min-poly x e f)) (q (pquot q (min-poly x e f) f)))
			(:instance prootp-pmul (f e) (p (plift (min-poly x e f) f e)) (q (plift (pquot q (min-poly x e f) f) f e)))))))

(local-defthmd min-poly-pdivides-2
  (implies (and (extensionp e f)
                (feltp x e) (polyp q f)
	        (not (pdivides (min-poly x e f) q f))
                (prootp x (plift q f e) e))
	   (equal (pgcd (min-poly x e f) q f) (pone f)))
  :hints (("Goal" :in-theory (enable polyp-plift)
                  :use (prootp-min-poly
                        (:instance pgcd-irreduciblep (p (min-poly x e f)) (x q))))))

(local-defthmd min-poly-pdivides-3
  (implies (and (extensionp e f)
                (feltp x e) (polyp q f) (not (equal q (pzero f)))
	        (not (pdivides (min-poly x e f) q f))
                (prootp x (plift q f e) e))
	   (equal (pgcd (plift (min-poly x e f) f e)
	                (plift q f e)
			e)
		  (pone e)))
  :hints (("Goal" :in-theory (enable pzero)
                  :use (prootp-min-poly min-poly-pdivides-2 plift-id
                        (:instance plift-pgcd (p (min-poly x e f)))))))

(local-defthmd min-poly-pdivides-4
  (implies (and (extensionp e f)
                (feltp x e) (polyp q f) (not (equal q (pzero f)))
	        (not (pdivides (min-poly x e f) q f))
                (prootp x (plift q f e) e))
	   (let ((r (r$ (plift (min-poly x e f) f e) (plift q f e) e))
	         (s (s$ (plift (min-poly x e f) f e) (plift q f e) e)))
	     (and (polyp r e)
	          (polyp s e)
		  (equal (padd (pmul r (plift (min-poly x e f) f e) e)
		               (pmul s (plift q f e) e)
			       e)
			 (pone e)))))
  :hints (("Goal" :in-theory (enable polyp-plift)
                  :use (prootp-min-poly min-poly-pdivides-3
                        (:instance plift-pzero (p q))
			(:instance pgcd-linear-combination (f e) (x (plift (min-poly x e f) f e)) (y (plift q f e)))))))

(local-defthmd min-poly-pdivides-5
  (implies (and (extensionp e f)
                (feltp x e) (polyp q f) (not (equal q (pzero f)))
	        (not (pdivides (min-poly x e f) q f))
                (prootp x (plift q f e) e))
	   (equal (peval (pone e) x e) (fzero e)))
  :hints (("Goal" :in-theory (enable prootp polyp-plift)
                  :use (prootp-min-poly min-poly-pdivides-3 min-poly-pdivides-4
                        (:instance peval-pmul (p (r$ (plift (min-poly x e f) f e) (plift q f e) e))
			                      (q (plift (min-poly x e f) f e))
					      (f e))
                        (:instance peval-pmul (p (s$ (plift (min-poly x e f) f e) (plift q f e) e))
			                      (q (plift q f e))
					      (f e))
			(:instance peval-padd (p (pmul (r$ (plift (min-poly x e f) f e) (plift q f e) e)
			                               (plift (min-poly x e f) f e)
						       e))
					      (q (pmul (s$ (plift (min-poly x e f) f e) (plift q f e) e)
			                               (plift q f e)
						       e))
					      (f e))))))

(local-defthmd min-poly-pdivides-6
  (implies (and (extensionp e f)
                (feltp x e) (polyp q f) (not (equal q (pzero f)))
	        (not (pdivides (min-poly x e f) q f)))
           (not (prootp x (plift q f e) e)))
  :hints (("Goal" :in-theory (enable pconstp pone)
                  :use (min-poly-pdivides-5
                        (:instance peval-pconstp (f e) (p (pone e)))
			(:instance fone-fzero (f e))))))

(local-defthmd min-poly-pdivides-7
  (implies (and (extensionp e f) (feltp x e))
	   (pdivides (min-poly x e f) (pzero f) f))
  :hints (("Goal" :use (prootp-min-poly
                        (:instance pdivides-pzero (x (min-poly x e f)))))))

(defthmd min-poly-pdivides
  (implies (and (extensionp e f)
                (feltp x e) (polyp q f))
	   (iff (prootp x (plift q f e) e)
	        (pdivides (min-poly x e f) q f)))
  :hints (("Goal" :use (min-poly-pdivides-1 min-poly-pdivides-6 min-poly-pdivides-7))))

;; Since (primitive e) is a root of (car e), (car e) must be divisible by (min-poly (primitive e) e (cdr e)), and since both of
;; these polynomials are irreducible, they must be equal:

(defthmd min-poly-primitive
  (implies (and (fieldp f) (consp f))
           (equal (min-poly (primitive f) f (cdr f))
	          (car f)))
  :hints (("Goal" :in-theory (e/d (polyp-plift) (fieldp len-plift))
		  :use (prootp-primitive fieldp
                        (:instance min-poly-pdivides (e f) (f (cdr f)) (x (primitive f)) (q (car f)))
			(:instance irreduciblep-pdivides-equal (f (cdr f)) (q (car f)) (p (min-poly (primitive f) f (cdr f))))
			(:instance len-plift (p (min-poly (primitive f) f (cdr f))) (f (cdr f)) (e f))
			(:instance len-plift (p (car f)) (f (cdr f)) (e f))
			(:instance prootp-min-poly (x (primitive f)) (e f) (f (cdr f)))			
			(:instance prootp-not-pconstp (p (PLIFT (min-poly (primitive f) f (cdr f)) (cdr f) f)) (x (primitive f)))))))

;; An element of e is lifted from f iff the degree of its minimal polynomial is 1:

(defund fliftedp (x f e)
  (= (degree (min-poly x e f)) 1))

(local-defthmd min-poly-flift-1
  (implies (and (extensionp e f)
                (feltp x f))
	   (pdivides (min-poly (flift x f e) e f) (list (fone f) (fneg x f)) f))
  :hints (("Goal" :in-theory (enable pconstp prootp)
                  :use (peval-root-poly polyp-root-poly plift-id
		        (:instance flift-peval (p (list (fone f) (fneg x f))))
		        (:instance min-poly-pdivides (x (flift x f e)) (q (list (fone f) (fneg x f))))))))

(defthmd min-poly-flift
  (implies (and (extensionp e f)
                (feltp x f))
	   (equal (min-poly (flift x f e) e f)
	          (root-poly x f)))
  :hints (("Goal" :in-theory (enable polyp monicp)
                  :use (min-poly-flift-1
		        (:instance prootp-min-poly (x (flift x f e)))
		        (:instance pdivides-equal-degree (x (min-poly (flift x f e) e f)) (y (list (fone f) (fneg x f))))
			(:instance pdivides-degree (x (min-poly (flift x f e) e f)) (y (list (fone f) (fneg x f))))
			(:instance pdivides-monic-equal (x (min-poly (flift x f e) e f)) (y (list (fone f) (fneg x f))))))))
                        
(defthm fliftedp-flift
  (implies (and (extensionp e f)
                (feltp x f))
	   (fliftedp (flift x f e) f e))
  :hints (("Goal" :in-theory (enable fliftedp)
                  :use (min-poly-flift))))

;; If (fliftedp x f e), then this function returns the element of f that lifts to x:

(defund fdrop (x e f)
  (fneg (cadr (min-poly x e f)) f))

(local-defthmd flift-fdrop-1
  (implies (and (extensionp e f)
                (polyp p f) (monicp p f) (= (degree p) 1) (feltp x e))
           (equal (feval (plift p f e) x e)
	          (fadd x (flift (cadr p) f e) e)))
  :hints (("Goal" :in-theory (enable pconstp polyp monicp))))

(local-defthmd flift-fdrop-2
  (implies (and (extensionp e f)
                (polyp p f) (monicp p f) (= (degree p) 1) (feltp x e))
           (equal (peval (plift p f e) x e)
	          (fadd x (flift (cadr p) f e) e)))
  :hints (("Goal" :use (polyp-plift flift-fdrop-1
		        (:instance feval-peval (p (plift p f e)) (f e))))))

(local-defthmd flift-fdrop-3
  (implies (and (extensionp e f)
                (feltp x e) (fliftedp x f e))
	   (equal (fadd x (flift (cadr (min-poly x e f)) f e) e)
	          (fzero e)))
  :hints (("Goal" :in-theory (enable prootp fliftedp)
                  :use (prootp-min-poly
                        (:instance flift-fdrop-2 (p (min-poly x e f)))))))

(local-defthmd flift-fdrop-4
  (implies (and (fieldp f) (polyp p f) (= (degree p) 1))
           (feltp (cadr p) f))
  :hints (("Goal" :in-theory (enable polyp))))

(local-defthmd flift-fdrop-5
  (implies (and (extensionp e f)
                (feltp x e) (fliftedp x f e))
	   (equal (flift (fneg (cadr (min-poly x e f)) f) f e)
	          x))
  :hints (("Goal" :in-theory (enable fliftedp)
                  :use (flift-fdrop-3 prootp-min-poly
                        (:instance flift-fdrop-4 (p (min-poly x e f)))
			(:instance flift-fneg (x (cadr (min-poly x e f))))
                        (:instance fneg-unique (f e) (y (flift (cadr (min-poly x e f)) f e)))))))

(defthmd flift-fdrop
  (implies (and (extensionp e f)
                (feltp x e) (fliftedp x f e))
	   (let ((y (fdrop x e f)))
	     (and (feltp y f)
	           (equal (flift y f e) x))))
  :hints (("Goal" :in-theory (enable fliftedp fdrop)
                  :use (flift-fdrop-5 prootp-min-poly
				      (:instance flift-fdrop-4 (p (min-poly x e f)))))))

(defthmd fdrop-flift
  (implies (and (extensionp e f) (feltp x f))
           (equal (fdrop (flift x f e) e f)
	          x))
  :hints (("Goal" :use ((:instance flift-fdrop (x (flift x f e)))
                        (:instance flift-1-1 (y (fdrop (flift x f e) e f)))))))


;; The notion of a lifted polynomial will also be important:

(defun pliftedp (p f e)
  (if (consp p)
      (and (fliftedp (car p) f e)
           (pliftedp (cdr p) f e))
    t))

(local-defthmd plifted-plift-1
  (implies (and (extensionp e f) 
                (feltsp p f))
	   (pliftedp (plift p f e) f e)))

(defthmd plifted-plift
  (implies (and (extensionp e f)
                (polyp p f))
	   (pliftedp (plift p f e) f e))
  :hints (("Goal" :use (plifted-plift-1))))

(defun pdrop (p e f)
  (if (consp p)
      (cons (fdrop (car p) e f)
            (pdrop (cdr p) e f))
    ()))

(defthmd plift-pdrop-feltsp
  (implies (and (extensionp e f)
                (feltsp p e) (pliftedp p f e))
	   (let ((q (pdrop p e f)))
	     (and (feltsp q f)
	          (equal (plift q f e) p))))
  :hints (("Subgoal *1/1" :use ((:instance flift-fdrop (x (car p)))))))

(defthmd plift-pdrop
  (implies (and (extensionp e f)
                (polyp p e) (pliftedp p f e))
	   (let ((q (pdrop p e f)))
	     (and (polyp q f)
	          (equal (plift q f e) p))))
  :hints (("Goal" :in-theory (enable polyp)
                  :use (plift-pdrop-feltsp))))


;;----------------------------------------------------------------------------------------------------------
;;                                      Characteristic of a Field
;;----------------------------------------------------------------------------------------------------------

;; The following function computes the sum of n copies of an element of a field f:

(defun ntimes (n x f)
  (if (zp n)
      (fzero f)
    (fadd x (ntimes (1- n) x f) f)))

(defthm feltp-ntimes
  (implies (and (fieldp f) (feltp x f) (natp n))
           (feltp (ntimes n x f) f)))

(defthmd ntimes-plus
  (implies (and (fieldp f) (feltp x f) (natp n) (natp m))
           (equal (ntimes (+ n m) x f)
	          (fadd (ntimes n x f) (ntimes m x f) f)))
  :hints (("Goal" :induct (fact n))
          ("Subgoal *1/2" :use ((:instance fadd-comm (y (fadd (ntimes m x f) (ntimes (+ -1 n) x f) f)))
	                        (:instance fadd-assoc (x (ntimes m x f)) (y (ntimes (+ -1 n) x f)) (z x))
				(:instance fadd-comm (y (ntimes (+ -1 n) x f)))))))

;; We have a natural mapping of the natural numbers to f:

(defund fnat (n f)
  (ntimes n (fone f) f))

(defthm feltp-fnat
  (implies (and (fieldp f) (natp n))
           (feltp (fnat n f) f))
  :hints (("Goal" :in-theory (enable fnat))))

(defthm fnat-0
  (implies (fieldp f)
           (equal (fnat 0 f)
	          (fzero f)))
  :hints (("Goal" :in-theory (enable fnat))))

(defthmd fnat-plus
  (implies (and (fieldp f) (natp n) (natp m))
           (equal (fnat (+ n m) f)
	          (fadd (fnat n f) (fnat m f) f)))
  :hints (("Goal" :in-theory (enable fnat)
                  :use ((:instance ntimes-plus (x (fone f)))))))

(defthmd ntimes-fnat
  (implies (and (fieldp f) (feltp x f) (natp n))
           (equal (ntimes n x f)
	          (fmul (fnat n f) x f)))
  :hints (("Goal" :in-theory (enable fnat))
          ("Subgoal *1/4" :use ((:instance fdistrib-comm (y (fone f)) (z (ntimes (+ -1 n) (fone f) f)))))))

(defthmd fnat-product
  (implies (and (fieldp f) (natp n) (natp m))
           (equal (fnat (* n m) f)
	          (fmul (fnat n f) (fnat m f) f)))
  :hints (("Goal" :induct (fact n))
          ("Subgoal *1/2" :in-theory (enable fnat)
	                  :use ((:instance ntimes-plus (x (fone f)) (n (* m (1- n))))
			        (:instance fdistrib (x (fnat m f)) (y (fnat (1- n) f)) (z (fone f)))))))

;; The characteristic of f is the minimal positive n such that (fnat n f) = (fzero f), or 0 if
;; no such n exists.  We use defchoose to formalize this notion:

(defchoose n0 n (f)
  (and (posp n)
       (equal (fnat n f) (fzero f))))

(defun fchar-aux (k n f)
  (declare (xargs :measure (nfix (- n k))))
  (if (and (posp k) (posp n) (<= k n) (equal (fnat n f) (fzero f)))
      (if (equal (fnat k f) (fzero f))
          k
	(fchar-aux (1+ k) n f))
    0))

(defund fchar (f)
  (fchar-aux 1 (n0 f) f))

(in-theory (disable (fchar)))

(local-defthmd fchar-aux-1
  (implies (and (posp n) (equal (fnat n f) (fzero f))
                (posp k) (<= k n))
	   (let ((c (fchar-aux k n f)))
             (and (posp c) (equal (fnat c f) (fzero f))))))

(local-defthmd fchar-aux-2
  (implies (and (posp n) (equal (fnat n f) (fzero f))
                (posp k) (<= k n)
		(posp j) (<= k j) (equal (fnat j f) (fzero f)))
	   (<= (fchar-aux k n f) j)))

(local-defthmd fchar-aux-3
  (implies (not (and (posp n) (equal (fnat n f) (fzero f))))
	   (equal (fchar-aux k n f) 0)))

(defthmd fchar-0-fnat-non-0
  (implies (and (fieldp f) (equal (fchar f) 0) (posp n))
           (not (equal (fnat n f) (fzero f))))
  :hints (("Goal" :in-theory (enable fchar)
                  :use (n0 (:instance fchar-aux-1 (k 1))))))

(defthmd fchar-not-0-fnat-0
  (implies (and (fieldp f) (not (equal (fchar f) 0)))
           (and (posp (fchar f))
	        (equal (fnat (fchar f) f) (fzero f))))
  :hints (("Goal" :in-theory (enable fchar)
                  :use (n0
		        (:instance fchar-aux-1 (n (n0 f)) (k 1))
		        (:instance fchar-aux-3 (n (n0 f)) (k 1))))))

(defthm fchar-min-0
  (implies (and (fieldp f) (not (equal (fchar f) 0))
                (posp n) (equal (fnat n f) (fzero f)))
	   (<= (fchar f) n))
  :hints (("Goal" :in-theory (enable fchar)
                  :use ((:instance fchar-aux-2 (n (n0 f)) (k 1) (j n))
		        (:instance fchar-aux-3 (n (n0 f)) (k 1))))))

;; The rational field Q has characteristic 0:

(defthm fnat-Q
  (implies (natp n)
           (equal (fnat n 0) n))
  :hints (("Goal" :in-theory (enable fadd badd fone bone fnat))))

(defthmd fchar-Q
  (equal (fchar 0) 0)
  :hints (("Goal" :in-theory (enable fzero bzero)
                  :use ((:instance fchar-not-0-fnat-0 (f 0))))))

;; The prime field Fp has characteristic p:

(defthmd ntimes-Fp
  (implies (and (primep f) (natp n))
           (equal (ntimes n 1 f) (mod n f)))
  :hints (("Goal" :in-theory (enable fadd badd))
          ("Subgoal *1/2" :use ((:instance rtl::mod-sum (rtl::n f) (rtl::a 1) (rtl::b (1- n)))
	                        (:instance rtl::mod-does-nothing (rtl::n f) (rtl::m (1+ (mod (1- n) f))))))
	  ("Subgoal *1/1" :in-theory (enable fzero bzero))))

(defthm fnat-Fp
  (implies (and (primep f) (natp n))
           (equal (fnat n f) (mod n f)))
  :hints (("Goal" :in-theory (enable fnat fone bone)
                  :use (ntimes-fp))))

(defthmd fchar-fp
  (implies (primep p)
           (equal (fchar p) p))
  :hints (("Goal" :in-theory (enable fieldp fzero bzero)
                  :use ((:instance fchar-not-0-fnat-0 (f p))
		        (:instance fchar-0-fnat-non-0 (f p) (n p))
		        (:instance fchar-min-0 (f p) (n p))
			(:instance rtl::mod-does-nothing (rtl::n p) (rtl::m (fchar p)))))))

;; It follows from field-integral-domain that the characteristic of any field is either 0 or prime:

;; I don't know why this isn't in euclid.lisp:

(defthmd not-prime-factors
  (implies (and (natp n) (> n 1) (not (primep n)))
           (let* ((a (least-prime-divisor n))
	          (b (/ n a)))
	     (and (natp a) (> a 1) (natp b) (> b 1)
	          (equal (* a b) n))))
  :hints (("Goal" :in-theory (enable primep divides)
                  :use ((:instance least-divisor-divides (k 2))))))

(defthm primep-fchar
  (implies (and (fieldp f) (not (equal (fchar f) 0)))
           (primep (fchar f)))
  :hints (("Goal" :expand ((fnat 1 f) (ntimes 1 (fone f) f))
                  :use (fchar-not-0-fnat-0 fone-fzero
                        (:instance not-prime-factors (n (fchar f)))
			(:instance fnat-product (n (least-prime-divisor (fchar f))) (m (/ (fchar f) (least-prime-divisor (fchar f)))))
			(:instance fchar-min-0 (n (least-prime-divisor (fchar f))))
			(:instance fchar-min-0 (n (/ (fchar f) (least-prime-divisor (fchar f)))))
			(:instance field-integral-domain (x (fnat (least-prime-divisor (fchar f)) f))
			                                 (y (fnat (/ (fchar f) (least-prime-divisor (fchar f))) f)))))))

;; An equivalent condition for (ntimes n x f) = (fzero f):

(local-defthmd ntimes-fchar-0-1
  (implies (and (fieldp f) (feltp x f) (not (equal x (fzero f))) (posp n)
                (equal (ntimes n x f) (fzero f)))
	   (primep (fchar f)))
  :hints (("Goal" :in-theory (enable ntimes-fnat)
                  :use (fchar-0-fnat-non-0 primep-fchar
		        (:instance field-integral-domain (x (fnat n f)) (y x))))))

(local-defthmd ntimes-fchar-0-2
  (implies (and (fieldp f) (feltp x f) (not (equal x (fzero f))) (posp n)
                (primep (fchar f)))
	   (iff (equal (ntimes n x f) (fzero f))
	        (equal (fnat n f) (fzero f))))
  :hints (("Goal" :in-theory (enable ntimes-fnat)
		  :use ((:instance field-integral-domain (x (fnat n f)) (y x))))))

(local-defthmd ntimes-fchar-0-3
  (implies (and (fieldp f) (feltp x f) (not (equal x (fzero f))) (posp n)
                (primep (fchar f)))
	   (equal (fnat n f)
	          (fnat (mod n (fchar f)) f)))
  :hints (("Goal" :in-theory (enable fnat)
                  :use (fchar-not-0-fnat-0 fchar-not-0-fnat-0
                        (:instance rtl::mod-def (rtl::x n) (rtl::y (fchar f)))
			(:instance fnat-product (n (fchar f)) (m (fl (/ n (fchar f)))))
			(:instance ntimes-plus (x (fone f)) (n (* (fchar f) (fl (/ n (fchar f))))) (m (mod n (fchar f))))))))

(local-defthmd ntimes-fchar-0-4
  (implies (and (fieldp f) (feltp x f) (not (equal x (fzero f))) (posp n)
                (primep (fchar f)))
	   (iff (equal (fnat (mod n (fchar f)) f) (fzero f))
	        (divides (fchar f) n)))
  :hints (("Goal" :use (fchar-min-0
                        (:instance divides-mod-0 (n (fchar f)) (a n))))))

(defthmd ntimes-fchar-0
  (implies (and (fieldp f) (feltp x f) (not (equal x (fzero f))) (posp n))
           (iff (equal (ntimes n x f) (fzero f))
	        (and (primep (fchar f))
		     (divides (fchar f) n))))
  :hints (("Goal" :use (ntimes-fchar-0-1 ntimes-fchar-0-2 ntimes-fchar-0-3 ntimes-fchar-0-4))))

(defthmd fnat-fchar-0
  (implies (and (fieldp f) (posp n))
           (iff (equal (fnat n f) (fzero f))
	        (and (primep (fchar f))
		     (divides (fchar f) n))))
  :hints (("Goal" :in-theory (enable fnat)
                  :use (fone-fzero (:instance ntimes-fchar-0 (x (fone f)))))))

;; The characteristic of a field is the same as that of its base field:

(defthmd flift-ntimes
  (implies (and (extensionp e f) (natp n))
           (equal (flift (ntimes n (fone f) f) f e)
	          (ntimes n (fone e) e))))

(defthmd fnat-0-extension
  (implies (and (extensionp e f) (natp n))
           (iff (equal (fnat n e) (fzero e))
	        (equal (fnat n f) (fzero f))))
  :hints (("Goal" :in-theory (enable fnat)
                  :use (flift-ntimes
		        (:instance flift-fzero (x (ntimes n (fone f) f)))))))

(defthmd fchar-extension
  (implies (extensionp e f)
           (equal (fchar e) (fchar f)))
  :hints (("Goal" :use (fchar-not-0-fnat-0
                        (:instance fchar-not-0-fnat-0 (f e))
			(:instance fchar-0-fnat-non-0 (n (fchar e)))
			(:instance fchar-0-fnat-non-0 (n (fchar f)) (f e))
			(:instance fchar-min-0 (n (fchar e)))
			(:instance fchar-min-0 (n (fchar f)) (f e))
			(:instance fnat-0-extension (n (fchar f)))
			(:instance fnat-0-extension (n (fchar e)))))))

(defthm extensionp-base
  (implies (fieldp f)
           (extensionp f (fbase f))))

(defthmd fchar-base
  (implies (fieldp f)
           (equal (fchar f) (fchar (fbase f))))
  :hints (("Goal" :use ((:instance fchar-extension (e f) (f (fbase f)))))))

;; The characteristic of F0, which is unknown, will be denoted by (fchar0):

(defund fchar0 ()
  (fchar 'f0))


;;----------------------------------------------------------------------------------------------------------
;;                                           Formal Derivative
;;----------------------------------------------------------------------------------------------------------

;; The formal deriviative of a polynomial provides a test for multiple roots:

(defun derivative-aux (p f)
  (if (and (consp p) (consp (cdr p)))
      (cons (fmul (fnat (degree p) f) (car p) f)
            (derivative-aux (cdr p) f))
    ()))

(defun derivative (p f)
  (if (pconstp p)
      (pzero f)
    (pstrip (derivative-aux p f) f)))

;; Note that derivative of a constant is 0:

(defthmd derivative-pconstp
  (implies (pconstp p)
           (equal (derivative p f)
	          (pzero f)))
  :hints (("Goal" :in-theory (enable pconstp))))

;; The derivative of a linear polynomial:

(defthmd derivative-linear
  (implies (and (fieldp f) (polyp p f) (equal (degree p) 1))
           (equal (derivative p f)
	          (list (car p))))
  :hints (("Goal" :in-theory (enable fnat ntimes pconstp polyp derivative derivative-aux)
                  :expand ((LEN (CDR P)) (LEN (CDDR P)) (DERIVATIVE-AUX P F) (DERIVATIVE-AUX (CDR P) F) (NTIMES 1 (FONE F) F)))))

;; The derivative of a non-constant polynomial is a polynomial of lesser degree:

(defthm len-derivative-aux
  (implies (and (fieldp f) (feltsp p f) (consp p))
           (equal (len (derivative-aux p f))
		  (1- (len p)))))

(defthm feltsp-derivative-aux
  (implies (and (fieldp f) (feltsp p f))
           (feltsp (derivative-aux p f) f)))

(defthmd polyp-derivative
  (implies (and (fieldp f) (polyp p f))
           (let ((d (derivative p f)))
             (and (polyp d f)
	          (or (pconstp p)
		      (< (degree d) (degree p))))))
  :hints (("Goal" :in-theory (enable derivative pconstp polyp)
                  :use (len-derivative-aux feltsp-derivative-aux
		        (:instance len-pstrip (x (derivative-aux (cdr p) f)))
		        (:instance polyp-pstrip (x (derivative-aux p f)))))))

(defthmd derivative-max-degree
  (implies (and (fieldp f) (polyp p f) (not (pconstp p))
                (not (equal (fnat (degree p) f) (fzero f))))
	   (and (equal (derivative p f) (derivative-aux p f))
	        (equal (degree (derivative p f)) (1- (degree p)))))
  :hints (("Goal" :in-theory (enable derivative pconstp polyp)
                  :use (len-derivative-aux feltsp-derivative-aux
		        (:instance field-integral-domain (x (fnat (degree p) f)) (y (car p)))))))

;; Derivative of a sum:

(local-defun derivative-aux-faddl-induct (p q)
  (declare (xargs :measure (+ (len p) (len q))))
  (if (and (consp p) (consp (cdr p)) (consp q) (consp (cdr q)))
      (if (> (len p) (len q))
          (derivative-aux-faddl-induct (cdr p) q)
	(if (< (len p) (len q))
	    (derivative-aux-faddl-induct p (cdr q))
	  (derivative-aux-faddl-induct (cdr p) (cdr q))))
    ()))

(in-theory (enable len-faddl))

(local-defthm derivative-aux-faddl-1
  (implies (not (consp (cdr p)))
           (equal (derivative-aux (faddl p q f) f)
	          (derivative-aux q f)))
  :hints (("Subgoal *1/1" :expand ((FADDL P Q F)))))

(local-defthm derivative-aux-faddl-2
  (implies (not (consp (cdr q)))
           (equal (derivative-aux (faddl p q f) f)
	          (derivative-aux p f)))
  :hints (("Subgoal *1/1" :expand ((FADDL P Q F)))))
			  
(defthmd derivative-aux-faddl
  (implies (and (fieldp f) (feltsp p f) (feltsp q f))
           (equal (derivative-aux (faddl p q f) f)
                  (faddl (derivative-aux p f)
		         (derivative-aux q f)
			 f)))
  :hints (("Goal" :induct (derivative-aux-faddl-induct p q))  
          ("Subgoal *1/3" :use ((:instance fdistrib-comm (x (FNAT (LEN (CDR P)) F)) (y (car p)) (z (car q)))))))

(defthmd pstrip-derivative-aux-pstrip
  (implies (and (fieldp f) (feltsp p f) (consp (cdr (pstrip p f))))
           (equal (pstrip (derivative-aux (pstrip p f) f) f)
	          (pstrip (derivative-aux p f) f ))))

(local-defthmd faddl-pstrip-derivative-aux-fzero
  (implies (and (fieldp f) (feltsp p f) (feltsp q f)
                (consp (cdr p)) (consp (cdr q))
		(not (cdr (pstrip (faddl p q f) f))))
           (equal (pstrip (faddl (derivative-aux p f) (derivative-aux q f) f) f)
	          (list (fzero f))))
  :hints (("Goal" :induct (derivative-aux-faddl-induct p q))  
          ("Subgoal *1/3" :in-theory (disable len-derivative-aux LEN-FLIST FLISTNP LEN-WLISTNP LEN-VLISTNP VLISTNP WLISTNP
					      ACL2::DEFAULT-PLUS-2 ACL2::DEFAULT-PLUS-1 FNAT-FP FIELDP-CDR)
	                  :use (len-derivative-aux
	                        (:instance fdistrib-comm (x (fnat (degree p) f)) (y (car p)) (z (car q)))
	                        (:instance len-derivative-aux (p q))))
          ("Subgoal *1/2" :in-theory (disable len-derivative-aux LEN-FLIST FLISTNP LEN-WLISTNP LEN-VLISTNP VLISTNP WLISTNP
					      ACL2::DEFAULT-PLUS-2 ACL2::DEFAULT-PLUS-1 FNAT-FP FIELDP-CDR)
			  :use (len-derivative-aux (:instance len-derivative-aux (p q))))
	  ("Subgoal *1/1" :in-theory (disable len-derivative-aux LEN-FLIST FLISTNP LEN-WLISTNP LEN-VLISTNP VLISTNP WLISTNP
					      ACL2::DEFAULT-PLUS-2 ACL2::DEFAULT-PLUS-1 FNAT-FP FIELDP-CDR)
			  :use (len-derivative-aux (:instance len-derivative-aux (p q))))))

(local-defthmd derivative-aux-faddl-const-1
  (implies (and (fieldp f) (feltsp p f) (feltsp q f) (not (cdr p)))
           (equal (derivative-aux (faddl p q f) f)
	          (derivative-aux q f))))

(local-defthmd derivative-aux-faddl-const-2
  (implies (and (fieldp f) (feltsp p f) (feltsp q f) (not (cdr q)))
           (equal (derivative-aux (faddl p q f) f)
	          (derivative-aux p f))))

(local-defthmd derivative-padd-both-const-1
  (implies (and (fieldp f) (polyp p f) (polyp q f) (not (consp (cdr p))) (not (consp (cdr q))))
           (not (consp (cdr (padd p q f)))))
  :hints (("Goal" :in-theory (enable polyp padd))))

(local-defthmd derivative-padd-both-const
  (implies (and (fieldp f) (polyp p f) (polyp q f) (not (consp (cdr p))) (not (consp (cdr q))))
           (equal (derivative (padd p q f) f)
	          (padd (derivative p f) (derivative q f) f)))
  :hints (("Goal" :in-theory (enable pconstp polyp)
                  :use (derivative-padd-both-const-1 derivative-pconstp
		        (:instance derivative-pconstp (p q))
			(:instance derivative-pconstp (p (padd p q f)))))))

(local-defthmd derivative-padd-q-const-1
  (implies (and (fieldp f) (polyp p f) (polyp q f) (consp (cdr p)) (not (consp (cdr q))))
           (equal (pstrip (faddl p q f) f)
	          (faddl p q f)))
  :hints (("Goal" :in-theory (enable polyp)
                  :expand ((len p) (len (cdr p)))
                  :use ((:instance car-faddl (x p) (y q))))))

(local-defthmd derivative-padd-q-const-2
  (implies (and (fieldp f) (polyp p f) (polyp q f) (consp (cdr p)) (not (consp (cdr q))))
           (equal (derivative (padd p q f) f)
	          (derivative p f)))
  :hints (("Goal" :in-theory (e/d (derivative-padd-q-const-1 pconstp polyp padd derivative) (len-faddl))
                  :use ((:instance len-faddl (x p) (y q))))))

(in-theory (disable derivative))

(local-defthmd derivative-padd-q-const
  (implies (and (fieldp f) (polyp p f) (polyp q f) (consp (cdr p)) (not (consp (cdr q))))
           (equal (derivative (padd p q f) f)
	          (padd (derivative p f) (derivative q f) f)))
  :hints (("Goal" :in-theory (enable polyp pconstp)
                  :expand ((len p) (len (cdr p)))
		  :use (polyp-derivative derivative-padd-q-const-2 (:instance derivative-pconstp (p q))))))
		        
(local-defthmd derivative-padd-p-const-1
  (implies (and (fieldp f) (polyp p f) (polyp q f) (consp (cdr q)) (not (consp (cdr p))))
           (equal (pstrip (faddl p q f) f)
	          (faddl p q f)))
  :hints (("Goal" :in-theory (enable polyp)
                  :expand ((len q) (len (cdr q)))
                  :use ((:instance car-faddl (x p) (y q))))))

(local-defthmd derivative-padd-p-const-2
  (implies (and (fieldp f) (polyp p f) (polyp q f) (consp (cdr q)) (not (consp (cdr p))))
           (equal (derivative (padd p q f) f)
	          (derivative q f)))
  :hints (("Goal" :in-theory (e/d (derivative-padd-p-const-1 pconstp polyp padd derivative) (len-faddl))
                  :use ((:instance len-faddl (x p) (y q))))))

(local-defthmd derivative-padd-p-const
  (implies (and (fieldp f) (polyp p f) (polyp q f) (consp (cdr q)) (not (consp (cdr p))))
           (equal (derivative (padd p q f) f)
	          (padd (derivative p f) (derivative q f) f)))
  :hints (("Goal" :in-theory (enable polyp pconstp)
		  :use (derivative-padd-p-const-2 derivative-pconstp
		        (:instance polyp-derivative (p q))))))

(local-defthmd derivative-padd-padd-const-1
  (implies (and (fieldp f) (polyp p f) (polyp q f) (consp (cdr q)) (consp (cdr p))
                (not (cdr (pstrip (faddl p q f) f))))
           (equal (derivative (padd p q f) f)
	          (pzero f)))
  :hints (("Goal" :in-theory (enable pconstp padd)
		  :use ((:instance derivative-pconstp (p (padd p q f)))))))

(local-defthmd derivative-padd-padd-const-2
  (implies (and (fieldp f) (polyp p f) (polyp q f) (consp (cdr q)) (consp (cdr p))
                (not (cdr (pstrip (faddl p q f) f))))
           (equal (padd (derivative p f) (derivative q f) f)
	          (pstrip (faddl (derivative-aux p f) (derivative-aux q f) f) f)))
  :hints (("Goal" :in-theory (e/d (polyp derivative pzero pconstp padd) (feltsp-derivative-aux))
		  :use (feltsp-derivative-aux
		        (:instance pstrip-faddl-pstrip-pstrip (x (derivative-aux p f)) (y (derivative-aux q f)))		  
		        (:instance feltsp-derivative-aux  (p q))))))

(local-defthmd derivative-padd-padd-const-3
  (implies (and (fieldp f) (polyp p f) (polyp q f) (consp (cdr q)) (consp (cdr p))
                (not (cdr (pstrip (faddl p q f) f))))
           (equal (padd (derivative p f) (derivative q f) f)
	          (pzero f)))
  :hints (("Goal" :in-theory (enable polyp pzero)
		  :use (faddl-pstrip-derivative-aux-fzero derivative-padd-padd-const-2))))

(local-defthmd derivative-padd-padd-const
  (implies (and (fieldp f) (polyp p f) (polyp q f) (consp (cdr q)) (consp (cdr p))
                (not (cdr (pstrip (faddl p q f) f))))
           (equal (derivative (padd p q f) f)
	          (padd (derivative p f) (derivative q f) f)))
  :hints (("Goal" :use (derivative-padd-padd-const-1 derivative-padd-padd-const-3))))

(local-defthmd derivative-padd-no-const-1
  (implies (and (fieldp f) (polyp p f) (polyp q f) (consp (cdr q)) (consp (cdr p))
                (consp (cdr (pstrip (faddl p q f) f))))
           (equal (derivative (padd p q f) f)
	          (pstrip (derivative-aux (faddl p q f) f) f)))
  :hints (("Goal" :in-theory (enable pconstp feltsp-faddl derivative padd)
                  :use ((:instance pstrip-derivative-aux-pstrip (p (faddl p q f)))))))

(local-defthmd hack-6
  (implies (and (fieldp f) (polyp p f) (cdr p))
           (consp (cdr p)))
  :hints (("Goal" :in-theory (enable polyp))))

(local-defthmd derivative-padd-no-const-2
  (implies (and (fieldp f) (polyp p f) (polyp q f) (consp (cdr q)) (consp (cdr p))
                (cdr (pstrip (faddl p q f) f)))
           (consp (cdr (pstrip (faddl p q f) f))))
  :hints (("Goal" :in-theory (enable polyp feltsp-faddl)
                  :use ((:instance polyp-pstrip (x (faddl p q f)))
		        (:instance hack-6 (p (pstrip (faddl p q f) f)))))))

(local-defthmd derivative-padd-no-const-3
  (implies (and (fieldp f) (polyp p f) (polyp q f) (consp (cdr q)) (consp (cdr p))
                (cdr (pstrip (faddl p q f) f)))
           (equal (pstrip (derivative-aux (faddl p q f) f) f)
	          (pstrip (faddl (derivative-aux p f) (derivative-aux q f) f) f)))
  :hints (("Goal" :use (derivative-padd-no-const-1 derivative-aux-faddl))))

(local-defthmd derivative-padd-no-const-4
  (implies (and (fieldp f) (polyp p f) (polyp q f) (consp (cdr q)) (consp (cdr p))
                (cdr (pstrip (faddl p q f) f)))
           (equal (pstrip (faddl (derivative-aux p f) (derivative-aux q f) f) f)
	          (pstrip (faddl (pstrip (derivative-aux p f) f)
                                 (pstrip (derivative-aux q f) f)
                                 f)
		          f)))
  :hints (("Goal" :in-theory (enable pconstp feltsp-faddl)
                  :use (feltsp-derivative-aux
		        (:instance feltsp-derivative-aux (p q))
		        (:instance pstrip-faddl-pstrip-pstrip (x (derivative-aux p f)) (y (derivative-aux q f)))))))

(local-defthmd derivative-padd-no-const-5
  (implies (and (fieldp f) (polyp p f) (polyp q f) (consp (cdr q)) (consp (cdr p))
                (cdr (pstrip (faddl p q f) f)))
           (equal (pstrip (faddl (pstrip (derivative-aux p f) f)
                                 (pstrip (derivative-aux q f) f)
                                 f)
		          f)
		  (padd (derivative p f) (derivative q f) f)))
  :hints (("Goal" :in-theory (enable padd derivative pconstp)
                  :use (len-derivative-aux
		        (:instance len-derivative-aux (p q))))))

(local-defthmd derivative-padd-no-const
  (implies (and (fieldp f) (polyp p f) (polyp q f) (consp (cdr q)) (consp (cdr p))
                (cdr (pstrip (faddl p q f) f)))
           (equal (derivative (padd p q f) f)
		  (padd (derivative p f) (derivative q f) f)))
  :hints (("Goal" :in-theory (theory 'minimal-theory)
                  :use (derivative-padd-no-const-1 derivative-padd-no-const-2 derivative-padd-no-const-3
		        derivative-padd-no-const-4 derivative-padd-no-const-5))))

(defthmd derivative-padd
  (implies (and (fieldp f) (polyp p f) (polyp q f))
           (equal (derivative (padd p q f) f)
	          (padd (derivative p f) (derivative q f) f)))
  :hints (("Goal" :in-theory (theory 'minimal-theory)
                  :use (derivative-padd-both-const derivative-padd-p-const derivative-padd-q-const
		        derivative-padd-padd-const derivative-padd-no-const))))

;; Proof:  The claim is trivial is either p or q is a constant.  If (padd p q f) = (pzero f), then
;; (padd (derivative p f) (derivative q f) f) = (pzero f) = (derivative (padd p f) (padd q f) f).
;; In the remaining case,

;; (derivative (padd p q f) f)
;;   = (pstrip (derivative-aux (padd p q f) f) f)                      [definition of derivative]
;;   = (pstrip (derivative-aux (pstrip (faddl p q f) f) f) f)          [definition of padd]
;;   = (pstrip (derivative-aux (faddl p q f) f) f)                     [pstrip-derivative-aux-pstrip]
;;   = (pstrip (faddl (derivative-aux p f) (derivative-aux q f) f) f)  [derivative-aux-faddl]
;;   = (pstrip (faddl (pstrip (derivative-aux p f) f)                  [pstrip-faddl-pstrip-pstrip]
;;                    (pstrip (derivative-aux q f) f)
;;                    f)
;;             f)
;;   = (pstrip (faddl (derivative p f) (derivative q f) f) f)          [definition of derivative]
;;   = (padd (derivative p f) (derivative q f) f)                      [definition of padd]

;;--------------------------------------------------

;; The proof of the product rule requires several lemmas:

(local-defthmd derivative-aux-cmul
  (implies (and (fieldp f) (feltsp p f) (feltp c f) (not (equal c (fzero f))))
	   (equal (derivative-aux (cmul c p f) f)
	          (cmul c (derivative-aux p f) f)))
  :hints (("Subgoal *1/2" :use ((:instance fmul-assoc (x (FNAT (LEN (CDR P)) F)) (y c) (z (car p)))
                                (:instance fmul-comm (x c) (y (FNAT (LEN (CDR P)) F)))
				(:instance fmul-assoc (x c) (y (FNAT (LEN (CDR P)) F)) (z (car p)))
                                (:instance fmul-comm (x (car p)) (y (FNAT (LEN (CDR P)) F)))))))

(local-defthmd derivative-cmul-1
  (implies (and (fieldp f) (polyp p f) (feltp c f) (not (equal c (fzero f))))
	   (iff (pconstp (cmul c p f))
	        (pconstp p)))
  :hints (("Goal" :in-theory (enable polyp pconstp)
                  :expand ((CMUL C P F) (CMUL C (CDR P) F)))))

(defthmd derivative-cmul
  (implies (and (fieldp f) (polyp p f) (feltp c f) (not (equal c (fzero f))))
	   (equal (derivative (cmul c p f) f)
	          (cmul c (derivative p f) f)))
  :hints (("Goal" :in-theory (enable pzero pstrip-cmul derivative)
                  :use (derivative-cmul-1 derivative-aux-cmul))))

;;------------------------------------------

(local-defthm derivative-aux-fzero-list
  (implies (and (fieldp f) (posp k))
           (equal (derivative-aux (fzero-list k f) f)
	          (fzero-list (1- k) f)))
  :hints (("Goal" :induct (fact k))))

(local-defthmd derivative-aux-monomial
  (implies (and (fieldp f) (feltp c f) (not (equal c (fzero f))) (posp k))
           (equal (derivative-aux (monomial c k f) f)
	          (monomial (fmul (fnat k f) c f) (1- k) f)))
  :hints (("Goal" :cases ((= k 1)) :in-theory (enable monomial-rewrite))))

(local-defthmd derivative-monomial-1
  (implies (and (fieldp f) (feltp c f) (not (equal c (fzero f))) (posp k)
                (equal (fnat k f) (fzero f)))
	   (equal (monomial (fmul (fnat k f) c f) (1- k) f)
	          (fzero-list k f)))
  :hints (("Goal" :in-theory (enable monomial-rewrite))))

(local-defthmd derivative-monomial-2
  (implies (and (fieldp f) (posp k))
           (equal (pstrip (fzero-list k f) f)
	          (pzero f)))
  :hints (("Goal" :in-theory (enable pzero))))

(local-defthmd derivative-monomial-3
  (implies (and (fieldp f) (feltp c f) (not (equal c (fzero f))) (posp k))
	   (not (pconstp (monomial c k f))))
  :hints (("Goal" :in-theory (enable pconstp monomial-rewrite))))

(local-defthmd derivative-monomial-4
  (implies (and (fieldp f) (feltp c f) (not (equal c (fzero f))) (posp k)
                (equal (fnat k f) (fzero f)))
	   (equal (derivative (monomial c k f) f)
	          (cmul (fnat k f) (monomial c (1- k) f) f)))
  :hints (("Goal" :in-theory '(pzero cmul derivative)
                  :use (derivative-monomial-2 derivative-monomial-3 derivative-aux-monomial derivative-monomial-1))))

(local-defthmd derivative-monomial-5
  (implies (and (fieldp f) (feltp c f) (not (equal c (fzero f))) (posp k)
                (not (equal (fnat k f) (fzero f))))
	   (equal (monomial (fmul (fnat k f) c f) (1- k) f)
	          (cmul (fnat k f) (monomial c (1- k) f) f)))
  :hints (("Goal" :in-theory (enable polyp monomial)
                  :use ((:instance cmul-pshift (c (fnat k f)) (x (list c)) (k (1- k)))))))

(defthmd derivative-monomial-6
  (implies (and (fieldp f) (feltp c f) (not (equal c (fzero f))) (posp k)
                (not (equal (fnat k f) (fzero f))))
	   (equal (pstrip (cmul (fnat k f) (monomial c (1- k) f) f) f)
	          (cmul (fnat k f) (monomial c (1- k) f) f)))
  :hints (("Goal" :in-theory (enable monomial-rewrite)
                  :use ((:instance field-integral-domain (x c) (y (fnat k f)))))))

(local-defthmd derivative-monomial-7
  (implies (and (fieldp f) (feltp c f) (not (equal c (fzero f))) (posp k)
                (not (equal (fnat k f) (fzero f))))
	   (equal (derivative (monomial c k f) f)
	          (cmul (fnat k f) (monomial c (1- k) f) f)))
  :hints (("Goal" :in-theory (enable derivative)
                  :use (derivative-monomial-6 derivative-monomial-3 derivative-aux-monomial derivative-monomial-5))))

(defthmd derivative-monomial
  (implies (and (fieldp f) (feltp c f) (not (equal c (fzero f))) (posp k))
           (equal (derivative (monomial c k f) f)
	          (cmul (fnat k f) (monomial c (1- k) f) f)))
  :hints (("Goal" :in-theory (enable derivative pconstp monomial-rewrite)
                  :use (derivative-monomial-4 derivative-monomial-7))))

;;------------------------------------------

;; The following function is useful for expressing a formula for the derivative of a
;; shifted polynomial:

(defund pshift$ (p k f)
  (if (equal p (pzero f))
      (pzero f)
    (pshift p k f)))

(defthmd padd-pshift$
  (implies (and (fieldp f) (polyp p f) (polyp q f) (natp k))
           (equal (padd (pshift$ p k f) (pshift$ q k f) f)
	          (pshift$ (padd p q f) k f)))
  :hints (("Goal" :in-theory (enable pshift$)
                  :use ((:instance padd-pshift (x p) (y q))))))

(defthmd cmul-pshift$
  (implies (and (fieldp f) (feltp c f) (natp k)
                (polyp p f) (not (equal p (pzero f))))
           (equal (cmul c (pshift p k f) f)
	          (pshift$ (cmul c p f) k f)))
  :hints (("Goal" :in-theory (enable pzero pshift$)
                  :use ((:instance cmul-pshift (x p))
		        (:instance cmul-nonzero (x p))))))

(local-defthmd derivative-pshift-1
  (implies (and (fieldp f) (polyp p f) (not (equal p (pzero f))) (natp k)
                (not (consp (cdr p))))
           (equal (pshift p k f)
                  (monomial (car p) k f)))
  :hints (("Goal" :in-theory (enable monomial polyp))))

(local-defthmd derivative-pshift-2
  (implies (and (fieldp f) (polyp p f) (not (equal p (pzero f))) (posp k)
                (not (consp (cdr p))))
           (equal (derivative (pshift p k f) f)
                  (cmul (fnat k f) (monomial (car p) (1- k) f) f)))
  :hints (("Goal" :in-theory (enable pzero polyp)
                  :use (derivative-pshift-1 (:instance derivative-monomial (c (car p)))))))

(local-defthmd derivative-pshift-3
  (implies (and (fieldp f) (polyp p f) (not (equal p (pzero f))) (posp k)
                (not (consp (cdr p))))
           (equal (derivative (pshift p k f) f)
                  (cmul (fnat k f) (pshift p (1- k) f) f)))
  :hints (("Goal" :use (derivative-pshift-2 (:instance derivative-pshift-1 (k (1- k)))))))

(local-defthmd derivative-pshift-4
  (implies (and (fieldp f) (polyp p f) (not (equal p (pzero f))) (posp k)
                (not (consp (cdr p))))
           (equal (derivative (pshift p k f) f)
                  (cmul (fnat k f) (pshift p (1- k) f) f)))
  :hints (("Goal" :in-theory (enable pshift)
                  :use (derivative-pshift-3 (:instance derivative-pshift-1 (k (1- k)))))))

(local-defthmd derivative-pshift-5
  (implies (and (fieldp f) (polyp p f) (not (equal p (pzero f))) (posp k)
                (not (consp (cdr p))))
           (equal (derivative (pshift p k f) f)
                  (padd (pshift$ (derivative p f) k f)
		        (cmul (fnat k f) (pshift p (1- k) f) f)
			f)))
  :hints (("Goal" :in-theory (enable polyp cmul derivative-pshift-3 pshift$ pconstp derivative-pconstp)
                  :use (pzero (:instance polyp-cmul (c (fnat k f)) (x (pshift p (1- k) f)))))))

(local-defthmd derivative-pshift-6
  (implies (and (fieldp f) (polyp p f) (not (equal p (pzero f))) (posp k) (consp (cdr p)))
           (equal (pshift p k f)
                  (padd (pshift (monomial (car p) (degree p) f) k f)
		        (pshift (pstrip (cdr p) f) k f)
			f)))
  :hints (("Goal" :in-theory (enable polyp head tail)
                  :use ((:instance pdecomp (x p))
		        (:instance padd-pshift (x (monomial (car p) (degree p) f))
			                       (y (pstrip (cdr p) f)))))))

(local-defthmd derivative-pshift-7
  (implies (and (fieldp f) (polyp p f) (not (equal p (pzero f))) (posp k) (consp (cdr p)))
           (and (polyp (monomial (car p) (degree p) f) f)
	        (not (equal (monomial (car p) (degree p) f) (pzero f)))))
  :hints (("Goal" :in-theory (e/d (polyp pzero) (car-monomial))
                  :use ((:instance car-monomial (c (car p)) (k (degree p)))
		        (:instance polyp-monomial (c (car p)) (k (degree p)))))))

(local-defthmd derivative-pshift-8
  (implies (and (fieldp f) (polyp p f) (not (equal p (pzero f))) (posp k) (consp (cdr p)))
           (equal (pshift (monomial (car p) (degree p) f) k f)
	          (monomial (car p) (+ k (degree p)) f)))	          
  :hints (("Goal" :in-theory (enable polyp monomial-rewrite pshift-rewrite)  
                  :use ((:instance polyp-monomial (c (car p)) (k (degree p)))))))

(local-defthmd derivative-pshift-9
  (implies (and (fieldp f) (polyp p f) (not (equal p (pzero f))) (posp k) (consp (cdr p)))
           (equal (derivative (pshift (monomial (car p) (degree p) f) k f) f)
	          (cmul (fnat (+ (degree p) k) f) (monomial (car p) (1- (+ (degree p) k)) f) f)))
  :hints (("Goal" :in-theory (enable polyp)
                  :use (derivative-pshift-8
                        (:instance derivative-monomial (c (car p)) (k (+ k (degree p))))))))

(local-defthmd derivative-pshift-10
  (implies (and (fieldp f) (polyp p f) (not (equal p (pzero f))) (posp k) (consp (cdr p)))
           (equal (derivative (pshift (monomial (car p) (degree p) f) k f) f)
	          (padd (cmul (fnat (degree p) f) (monomial (car p) (1- (+ (degree p) k)) f) f)
		        (cmul (fnat k f) (monomial (car p) (1- (+ (degree p) k)) f) f)
			f)))
  :hints (("Goal" :in-theory (enable polyp)
                  :use (derivative-pshift-9 polyp
                        (:instance derivative-monomial (c (car p)) (k (+ k (degree p))))
			(:instance fnat-plus (n (degree p)) (m k))
			(:instance cmul-fadd (c (fnat (degree p) f)) (d (fnat k f)) (x (monomial (car p) (1- (+ (degree p) k)) f)))))))

(local-defthmd derivative-pshift-11
  (implies (and (fieldp f) (natp m) (natp n) (feltp c f) (not (equal c (fzero f))))
           (equal (pshift (monomial c m f) n f)
	          (monomial c (+ m n) f)))
  :hints (("Goal" :in-theory (enable polyp monomial pshift-pshift))))

(local-defthmd derivative-pshift-12
  (implies (and (fieldp f) (polyp p f) (not (equal p (pzero f))) (posp k) (consp (cdr p)))
           (equal (derivative (pshift (monomial (car p) (degree p) f) k f) f)
	          (padd (cmul (fnat (degree p) f) (pshift (monomial (car p) (1- (degree p)) f) k f) f)
		        (cmul (fnat k f) (pshift (monomial (car p) (degree p) f) (1- k) f) f)
			f)))
  :hints (("Goal" :in-theory (enable polyp)
                  :use (derivative-pshift-10
                        (:instance derivative-pshift-11 (c (car p)) (m (1- (degree p))) (n k))
                        (:instance derivative-pshift-11 (c (car p)) (m (degree p)) (n (1- k))))
		  :expand ((len p) (LEN (CDR P))))))

(local-defthmd derivative-pshift-13
  (implies (and (fieldp f) (polyp p f) (not (equal p (pzero f))) (posp k) (consp (cdr p)))
           (equal (derivative (pshift (monomial (car p) (degree p) f) k f) f)
	          (padd (pshift$ (cmul (fnat (degree p) f) (monomial (car p) (1- (degree p)) f) f) k f)
		        (cmul (fnat k f) (pshift (monomial (car p) (degree p) f) (1- k) f) f)
			f)))
  :hints (("Goal" :in-theory (enable polyp pzero)
                  :expand ((len p) (len (cdr p)))
                  :use (polyp derivative-pshift-12
		        (:instance polyp-monomial (c (car p)) (k (1- (degree p))))
		        (:instance car-monomial (c (car p)) (k (degree p)))
                        (:instance cmul-pshift$ (c (fnat (degree p) f)) (p (monomial (car p) (1- (degree p)) f)))))))

(local-defthmd derivative-pshift-14
  (implies (and (fieldp f) (polyp p f) (not (equal p (pzero f))) (posp k) (consp (cdr p)))
           (equal (derivative (pshift (monomial (car p) (degree p) f) k f) f)
	          (padd (pshift$ (derivative (monomial (car p) (degree p) f) f) k f)
		        (cmul (fnat k f) (pshift (monomial (car p) (degree p) f) (1- k) f) f)
			f)))
  :hints (("Goal" :in-theory (enable polyp pzero)
                  :expand ((len p) (len (cdr p)))
                  :use (polyp derivative-pshift-13
		        (:instance derivative-monomial (c (car p)) (k (degree p)))))))

(local-defthmd derivative-pshift-15
  (implies (and (fieldp f) (polyp p f) (not (equal p (pzero f))) (posp k) (consp (cdr p))
                (equal (pstrip (cdr p) f) (pzero f)))
           (equal (derivative (pshift p k f) f)
                  (padd (pshift$ (derivative p f) k f)
                        (cmul (fnat k f) (pshift p (1- k) f) f)
	                f)))
  :hints (("Goal" :in-theory (enable polyp head tail)
                  :use (derivative-pshift-14
		        (:instance pdecomp (x p))
		        (:instance polyp-monomial (c (car p)) (k (degree p)))))))

(local-defthmd derivative-pshift-16
  (implies (and (fieldp f) (polyp p f) (not (equal p (pzero f))) (posp k) (consp (cdr p))
                (not (equal (pstrip (cdr p) f) (pzero f))))
           (equal (derivative (pshift p k f) f)
                  (padd (derivative (pshift (monomial (car p) (degree p) f) k f) f)
                        (derivative (pshift (pstrip (cdr p) f) k f) f)
	                f)))
  :hints (("Goal" :in-theory (enable polyp)
                  :use (derivative-pshift-6 derivative-pshift-7
		        (:instance derivative-padd (p (pshift (monomial (car p) (degree p) f) k f))
			                           (q (pshift (pstrip (cdr p) f) k f)))
			(:instance polyp-pstrip (x (cdr p)))))))

(local-defthmd derivative-pshift-17
  (implies (and (fieldp f) (polyp p f) (not (equal p (pzero f))) (posp k) (consp (cdr p))
                (not (equal (pstrip (cdr p) f) (pzero f)))
		(equal (derivative (pshift (pstrip (cdr p) f) k f) f)
		       (padd (pshift$ (derivative (pstrip (cdr p) f) f) k f)
		             (cmul (fnat k f) (pshift (pstrip (cdr p) f) (1- k) f) f)
			     f)))
           (equal (derivative (pshift p k f) f)
                  (padd (padd (pshift$ (derivative (monomial (car p) (degree p) f) f) k f)
		              (cmul (fnat k f) (pshift (monomial (car p) (degree p) f) (1- k) f) f)
			      f)
                        (padd (pshift$ (derivative (pstrip (cdr p) f) f) k f)
		              (cmul (fnat k f) (pshift (pstrip (cdr p) f) (1- k) f) f)
			      f)
	                f)))
  :hints (("Goal" :use (derivative-pshift-16 derivative-pshift-14))))

(local-defthmd derivative-pshift-18
  (implies (and (fieldp f) (polyp p f) (not (equal p (pzero f))) (posp k) (consp (cdr p))
                (not (equal (pstrip (cdr p) f) (pzero f))))
           (and (polyp (pshift$ (derivative (monomial (car p) (degree p) f) f) k f) f)
		(polyp (cmul (fnat k f) (pshift (monomial (car p) (degree p) f) (1- k) f) f) f)
                (polyp (pshift$ (derivative (pstrip (cdr p) f) f) k f) f)
		(polyp (cmul (fnat k f) (pshift (pstrip (cdr p) f) (1- k) f) f) f)
		(polyp (pstrip (cdr p) f) f)
		(polyp (monomial (car p) (degree p) f) f)
		(polyp (pshift (monomial (car p) (degree p) f) (1- k) f) f)
		(polyp (pshift (pstrip (cdr p) f) (1- k) f) f)))
  :hints (("Goal" :in-theory (e/d (polyp-derivative cmul polyp-cmul pshift$ pzero) (polyp-pshift polyp-pzero))
                  :use (derivative-pshift-7 polyp-pzero
		        (:instance polyp-pshift (x (pstrip (cdr p) f)) (k (1- k)))
		        (:instance polyp-pshift (x (monomial (car p) (degree p) f)) (k (1- k)))
			(:instance polyp-pshift (x (derivative (pstrip (cdr p) f) f)))
			(:instance polyp-pshift (x (derivative (monomial (car p) (degree p) f) f)))
			(:instance polyp-cmul (c (fnat k f)) (x (pshift (monomial (car p) (degree p) f) (1- k) f)))
			(:instance polyp-cmul (c (fnat k f)) (x (pshift (pstrip (cdr p) f) (1- k) f)))
			(:instance polyp-pstrip (x (cdr p)))))))

(local-defthmd hack-8
  (implies (and (fieldp f) (polyp a f) (polyp b f) (polyp c f) (polyp d f))
           (equal (padd (padd a b f) (padd c d f) f)
	          (padd (padd a c f) (padd b d f) f)))
  :hints (("Goal" :use ((:instance padd-assoc (x (padd a b f)) (y c) (z d))
		        (:instance padd-assoc (x a) (y b) (z c))
                        (:instance padd-comm (x c) (y b))
		        (:instance padd-assoc (x a) (y c) (z b))
		        (:instance padd-assoc (x (padd a c f)) (y b) (z d))))))
		       
(local-defthmd derivative-pshift-19
  (implies (and (fieldp f) (polyp p f) (not (equal p (pzero f))) (posp k) (consp (cdr p))
                (not (equal (pstrip (cdr p) f) (pzero f)))
		(equal (derivative (pshift (pstrip (cdr p) f) k f) f)
		       (padd (pshift$ (derivative (pstrip (cdr p) f) f) k f)
		             (cmul (fnat k f) (pshift (pstrip (cdr p) f) (1- k) f) f)
			     f)))
           (equal (derivative (pshift p k f) f)
                  (padd (padd (pshift$ (derivative (monomial (car p) (degree p) f) f) k f)
		              (pshift$ (derivative (pstrip (cdr p) f) f) k f)
			      f)
                        (padd (cmul (fnat k f) (pshift (monomial (car p) (degree p) f) (1- k) f) f)
		              (cmul (fnat k f) (pshift (pstrip (cdr p) f) (1- k) f) f)
			      f)
	                f)))
  :hints (("Goal" :use (derivative-pshift-17 derivative-pshift-18
                        (:instance hack-8 (a (pshift$ (derivative (monomial (car p) (degree p) f) f) k f))
			                  (b (cmul (fnat k f) (pshift (monomial (car p) (degree p) f) (1- k) f) f))
					  (c (pshift$ (derivative (pstrip (cdr p) f) f) k f))
					  (d (cmul (fnat k f) (pshift (pstrip (cdr p) f) (1- k) f) f)))))))

(local-defthmd derivative-pshift-20
  (implies (and (fieldp f) (polyp p f) (not (equal p (pzero f))) (posp k) (consp (cdr p))
                (not (equal (pstrip (cdr p) f) (pzero f)))
		(equal (derivative (pshift (pstrip (cdr p) f) k f) f)
		       (padd (pshift$ (derivative (pstrip (cdr p) f) f) k f)
		             (cmul (fnat k f) (pshift (pstrip (cdr p) f) (1- k) f) f)
			     f)))
           (equal (padd (pshift$ (derivative (monomial (car p) (degree p) f) f) k f)
		        (pshift$ (derivative (pstrip (cdr p) f) f) k f)
			f)
		  (pshift$ (derivative p f) k f)))
  :hints (("Goal" :in-theory (enable head tail polyp-derivative)
                  :use (derivative-pshift-18
                        (:instance padd-pshift$ (p (derivative (monomial (car p) (degree p) f) f))
			                        (q (derivative (pstrip (cdr p) f) f)))
			(:instance derivative-padd (p (monomial (car p) (degree p) f))
			                           (q (pstrip (cdr p) f)))
			(:instance pdecomp (x p))))))

(local-defthmd hack-9
  (implies (fieldp f)
           (equal (padd (pzero f) (pzero f) f)
	          (pzero f))))

(local-defthmd derivative-pshift-21
  (implies (and (fieldp f) (polyp p f) (not (equal p (pzero f))) (posp k) (consp (cdr p))
                (not (equal (pstrip (cdr p) f) (pzero f)))
		(equal (derivative (pshift (pstrip (cdr p) f) k f) f)
		       (padd (pshift$ (derivative (pstrip (cdr p) f) f) k f)
		             (cmul (fnat k f) (pshift (pstrip (cdr p) f) (1- k) f) f)
			     f)))
           (equal (padd (cmul (fnat k f) (pshift (monomial (car p) (degree p) f) (1- k) f) f)
		        (cmul (fnat k f) (pshift (pstrip (cdr p) f) (1- k) f) f)
			f)
		  (cmul (fnat k f) (pshift p (1- k) f) f)))
  :hints (("Goal" :in-theory (enable pzero head tail)
                  :use (derivative-pshift-18 hack-9
                        (:instance cmul-padd (c (fnat k f))
			                     (x (pshift (monomial (car p) (degree p) f) (1- k) f))
			                     (y (pshift (pstrip (cdr p) f) (1- k) f)))
			(:instance padd-pshift (x (monomial (car p) (degree p) f))
			                       (y (pstrip (cdr p) f))
					       (k (1- k)))
			(:instance pdecomp (x p))))))

(local-defthmd derivative-pshift-22
  (implies (and (fieldp f) (polyp p f) (not (equal p (pzero f))) (posp k) (consp (cdr p))
                (not (equal (pstrip (cdr p) f) (pzero f)))
		(equal (derivative (pshift (pstrip (cdr p) f) k f) f)
		       (padd (pshift$ (derivative (pstrip (cdr p) f) f) k f)
		             (cmul (fnat k f) (pshift (pstrip (cdr p) f) (1- k) f) f)
			     f)))
           (equal (derivative (pshift p k f) f)
                  (padd (pshift$ (derivative p f) k f)
                        (cmul (fnat k f) (pshift p (1- k) f) f)
	                f)))
  :hints (("Goal" :use (derivative-pshift-19 derivative-pshift-20 derivative-pshift-21))))

(local-defun derivative-pshift-induct (p f)
  (if (or (not (consp (cdr p))) (equal (pstrip (cdr p) f) (pzero f)))
      p
    (derivative-pshift-induct (pstrip (cdr p) f) f)))

(defthmd derivative-pshift
  (implies (and (fieldp f) (polyp p f) (not (equal p (pzero f))) (posp k))
           (equal (derivative (pshift p k f) f)
                  (padd (pshift$ (derivative p f) k f)
                        (cmul (fnat k f) (pshift p (1- k) f) f)
	                f)))
  :hints (("Goal" :induct (derivative-pshift-induct p f))
          ("Subgoal *1/2" :use (derivative-pshift-22))
          ("Subgoal *1/1" :use (derivative-pshift-5 derivative-pshift-15))))

;; Proof: Let d = (degree p), c = (car p), p' = (pstrip (cdr p) f).  If d = 0, then p = (list c),
;; (derivative p f) = (pzero f), and

;;   (derivative (pshift p k f) f) = (derivative (monomial c k f) f)
;;                                 = (cmul (fnat k f) (monomial c (1- k) f) f)
;;                                 = (cmul (fnat k f) (pshift c (1- k) f) f)
;;                                 = (pshift$ (derivative p f) k f) + (cmul (fnat k f) (pshift c (1- k) f) f)

;; Assume d > 0.  Then p = (monomial c d f) + p' and

;;   (derivative (pshift (monomial c d f) k f) f)
;;     = (derivative (monomial c (+ d k) f) f)
;;     = (cmul (fnat (+ d k) f) (monomial c (1- (+ d k)) f) f)
;;     = (cmul (fnat d f) (monomial c (1- (+ d k)) f) f) + (cmul (fnat k f) (monomial c (1- (+ d k)) f) f)
;;     = (cmul (fnat d f) (pshift (monomial c (1- d) f) k f) f) + (cmul (fnat k f) (pshift (monomial c d f) (1- k) f) f)
;;     = (pshift$ (cmul (fnat d f) (monomial c (1- d) f) f) k f) + (cmul (fnat k f) (pshift (monomial c d f) (1- k) f) f)
;;     = (pshift$ (derivative (monomial c d f) f) k f) + (cmul (fnat k f) (pshift (monomial c d f) (1- k) f) f)

;; If p' = (pzero f), then

;;   (derivative (pshift p k f) f)
;;     = (derivative (pshift (monomial c d f) k f) f)
;;     = (pshift$ (derivative (monomial c d f) f) k f) + (cmul (fnat k f) (pshift (monomial c d f) (1- k) f) f)
;;     = (pshift$ (derivative p f) k f) + (cmul (fnat k f) (pshift p (1- k) f) f)

;; Suppose p' != (pzero).  By induction,

;;   (derivative (pshift p' k f) f) = (pshift$ (derivative p' f) k f) + (cmul (fnat k f) (pshift p' (1- k) f) f)

;; Thus,

;;   (derivative (pshift p k f) f)
;;     = (derivative (pshift ((monomial c d f) + p') k f) f)
;;     = (derivative ((pshift (monomial c d f) k f) + (pshift p' k f)) f)
;;     = (derivative (pshift (monomial c d f) k f) f) + (derivative (pshift p' k f) f)
;;     =  ((pshift$ (derivative (monomial c d f) f) k f) + (cmul (fnat k f) (pshift (monomial c d f) (1- k) f) f))
;;      + ((pshift$ (derivative p' f) k f) + (cmul (fnat k f) (pshift p' (1- k) f) f))
;;     =  ((pshift$ (derivative (monomial c d f) f) k f) + (pshift$ (derivative p' f) k f))
;;      + ((cmul (fnat k f) (pshift (monomial c d f) (1- k) f) f) + (cmul (fnat k f) (pshift p' (1- k) f) f))

;; where

;;   (pshift$ (derivative (monomial c d f) f) k f) + (pshift$ (derivative p' f) k f)
;;     = (pshift$ ((derivative (monomial c d f) f) + (derivative p' f)) k f)
;;     = (pshift$ (derivative ((monomial c d f) f) + p') k f) 
;;     = (pshift$ (derivative p f) k f)

;; and

;;   (cmul (fnat k f) (pshift (monomial c d f) (1- k) f) f) + (cmul (fnat k f) (pshift p' (1- k) f) f)
;;     = (cmul (fnat k f) ((pshift (monomial c d f) (1- k) f) + (pshift p' (1- k) f)) f)
;;     = (cmul (fnat k f) (pshift ((monomial c d f) + p') (1- k) f) f)
;;     = (cmul (fnat k f) (pshift p (1- k) f) f)

;; and hence

;;   (derivative (pshift p' k f) k f) = (pshift$ (derivative p f) k f) + (cmul (fnat k f) (pshift c (1- k) f) f).

;;-----------------------------------------------------

(local-defthm derivative-pzero
  (implies (fieldp f)
           (equal (derivative (pzero f) f)
	          (pzero f)))
  :hints (("Goal" :in-theory (enable derivative pzero pconstp))))

(local-defthmd derivative-pmul-1
  (implies (and (fieldp f) (polyp p f) (polyp q f)
                (or (equal p (pzero f)) (equal q (pzero f))))
           (equal (derivative (pmul p q f) f)
                  (padd (pmul (derivative p f) q f)
                        (pmul p (derivative q f) f)
                        f))))

(local-defthmd derivative-pmul-2
  (implies (and (fieldp f) (polyp p f) (polyp q f)
                (not (or (equal p (pzero f)) (equal q (pzero f))))
		(not (consp (cdr p))))
           (equal (derivative (pmul p q f) f)
                  (padd (pmul (derivative p f) q f)
                        (pmul p (derivative q f) f)
                        f)))
  :hints (("Goal" :in-theory (e/d (pconstp polyp-derivative cmul-pzero polyp) (POLYP-FELTSP))
                  :use (pmul polyp derivative-pconstp
		        (:instance polyp-car-nonzero (x p))
		        (:instance pmul (q (derivative q f)))
                        (:instance derivative-cmul (c (car p)) (p q))))))

(local-defthmd derivative-pmul-3
  (implies (and (fieldp f) (polyp p f) (polyp q f)
                (not (or (equal p (pzero f)) (equal q (pzero f))))
		(not (consp (cdr q))))
           (equal (derivative (pmul p q f) f)
                  (padd (pmul (derivative p f) q f)
                        (pmul p (derivative q f) f)
                        f)))
  :hints (("Goal" :in-theory (enable polyp-derivative)
                  :use ((:instance pmul-comm (x p) (y q))
                        (:instance pmul-comm (x p) (y (derivative q f)))
                        (:instance pmul-comm (x q) (y (derivative p f)))
			(:instance padd-comm (x (pmul q (derivative p f) f)) (y (pmul p (derivative q f) f)))
			(:instance derivative-pmul-2 (p q) (q p))))))

(local-defthmd derivative-pmul-4
  (implies (and (fieldp f) (polyp p f) (polyp q f)
                (not (or (equal p (pzero f)) (equal q (pzero f))))
		(consp (cdr p)) (consp (cdr q)))
           (and (equal (padd (monomial (car p) (degree p) f)
	                     (pstrip (cdr p) f)
			     f)
		       p)
		(feltp (car p) f)
		(not (equal (car p) (fzero f)))
		(polyp (monomial (car p) (degree p) f) f)
		(polyp (pstrip (cdr p) f) f)))		
  :hints (("Goal" :in-theory (enable head tail)
                  :use ((:instance pdecomp (x p))
		        (:instance polyp-car-nonzero (x p))
			(:instance polyp-pstrip (x (cdr p)))
		        (:instance polyp-monomial (c (car p)) (k (degree p)))))))

(local-defthmd derivative-pmul-5
  (implies (and (fieldp f) (polyp p f) (polyp q f)
                (not (or (equal p (pzero f)) (equal q (pzero f))))
		(consp (cdr p)) (consp (cdr q)))
           (equal (derivative p f)
	          (padd (cmul (fnat (degree p) f) (monomial (car p) (1- (degree p)) f) f)
		        (derivative (pstrip (cdr p) f) f)
			f)))
  :hints (("Goal" :expand ((len p) (len (cdr p)))
                  :use (derivative-pmul-4
		        (:instance derivative-padd (p (monomial (car p) (degree p) f))
			                           (q (pstrip (cdr p) f)))
		        (:instance derivative-monomial (c (car p)) (k (degree p)))))))

(local-defthmd derivative-pmul-6
  (implies (and (fieldp f) (polyp p f) (polyp q f)
                (not (or (equal p (pzero f)) (equal q (pzero f))))
		(consp (cdr p)) (consp (cdr q)))
           (and (equal (pmul p q f)
	               (padd (pshift (cmul (car p) q f) (degree p) f)
                             (pmul (pstrip (cdr p) f) q f)
                             f))
		(polyp (cmul (car p) q f) f)
		(not (equal (cmul (car p) q f) (pzero f)))
                (polyp (pshift (cmul (car p) q f) (degree p) f) f)
		(polyp (pmul (pstrip (cdr p) f) q f) f)))
  :hints (("Goal" :use (derivative-pmul-4 pmul
		        (:instance polyp-pshift (x (cmul (car p) q f)) (k (degree p)))
			(:instance polyp-cmul (c (car p)) (x q))
			(:instance cmul-nonzero (c (car p)) (x q))))))

(local-defthmd derivative-pmul-7
  (implies (and (fieldp f) (polyp p f) (polyp q f)
                (not (or (equal p (pzero f)) (equal q (pzero f))))
		(consp (cdr p)) (consp (cdr q)))
            (and (equal (derivative (pmul p q f) f)
	                (padd (derivative (pshift (cmul (car p) q f) (degree p) f) f)
                              (derivative (pmul (pstrip (cdr p) f) q f) f)
                              f))
		(polyp (cmul (car p) q f) f)
		(not (equal (cmul (car p) q f) (pzero f)))
                (polyp (pshift (cmul (car p) q f) (degree p) f) f)
		(polyp (pmul (pstrip (cdr p) f) q f) f)))
  :hints (("Goal" :use (derivative-pmul-6
                         (:instance derivative-padd (p (pshift (cmul (car p) q f) (degree p) f))
			                           (q (pmul (pstrip (cdr p) f) q f)))))))

(local-defthmd derivative-pmul-8
  (implies (and (fieldp f) (polyp p f) (polyp q f)
                (not (or (equal p (pzero f)) (equal q (pzero f))))
		(consp (cdr p)) (consp (cdr q)))
           (equal (derivative (pshift (cmul (car p) q f) (degree p) f) f)
	          (padd (pshift$ (derivative (cmul (car p) q f) f) (degree p) f)
                        (cmul (fnat (degree p) f) (pshift (cmul (car p) q f) (1- (degree p)) f) f)
                        f)))
  :hints (("Goal" :expand ((len p) (len (cdr p)))
                  :use (derivative-pmul-7
                        (:instance derivative-pshift (p (cmul (car p) q f)) (k (degree p)))))))

(local-defthmd derivative-pmul-9
  (implies (and (fieldp f) (polyp p f) (polyp q f)
                (not (or (equal p (pzero f)) (equal q (pzero f))))
		(consp (cdr p)) (consp (cdr q)))
           (equal (pshift$ (derivative (cmul (car p) q f) f) (degree p) f)
		  (pshift$ (cmul (car p) (derivative q f) f) (degree p) f)))
  :hints (("Goal" :expand ((len p) (len (cdr p)))
                  :use (derivative-pmul-4 derivative-pmul-7
                        (:instance derivative-cmul (c (car p)) (p q))))))

(local-defthmd derivative-pmul-10
  (implies (and (fieldp f) (polyp p f) (polyp q f)
                (not (or (equal p (pzero f)) (equal q (pzero f))))
		(consp (cdr p)) (consp (cdr q)))
           (equal (pshift$ (cmul (car p) (derivative q f) f) (degree p) f)
	          (pmul (monomial (car p) (degree p) f) (derivative q f) f)))
  :hints (("Goal" :in-theory (enable polyp-derivative pshift$)
                  :use (derivative-pmul-4
                        (:instance pmul-monomial (y (derivative q f)) (c (car p)) (k (degree p)))
			(:instance cmul-pzero (c (car p)))
			(:instance cmul-nonzero (c (car p)) (x (derivative q f)))))))

(local-defthmd derivative-pmul-11
  (implies (and (fieldp f) (polyp p f) (polyp q f)
                (not (or (equal p (pzero f)) (equal q (pzero f))))
		(consp (cdr p)) (consp (cdr q)))
           (equal (cmul (fnat (degree p) f) (pshift (cmul (car p) q f) (1- (degree p)) f) f)
	          (pmul (cmul (fnat (degree p) f) (monomial (car p) (1- (degree p)) f) f) q f)))
  :hints (("Goal" :expand ((len p) (len (cdr p)))
		  :use (derivative-pmul-4
		        (:instance cmul-pmul (c (fnat (degree p) f)) (x (monomial (car p) (1- (degree p)) f)) (y q))
		        (:instance polyp-monomial (c (car p)) (k (1- (degree p))))
                        (:instance pmul-monomial (y q) (c (car p)) (k (1- (degree p))))))))

(local-defthmd derivative-pmul-12
  (implies (and (fieldp f) (polyp p f) (polyp q f)
                (not (or (equal p (pzero f)) (equal q (pzero f))))
		(consp (cdr p)) (consp (cdr q)))
           (equal (derivative (pshift (cmul (car p) q f) (degree p) f) f)
	          (padd (pmul (monomial (car p) (degree p) f) (derivative q f) f)
                        (pmul (cmul (fnat (degree p) f) (monomial (car p) (1- (degree p)) f) f) q f)
                        f)))
  :hints (("Goal" :use (derivative-pmul-8 derivative-pmul-9 derivative-pmul-10 derivative-pmul-11))))

(local-defthmd derivative-pmul-13
  (implies (and (fieldp f) (polyp p f) (polyp q f)
                (not (or (equal p (pzero f)) (equal q (pzero f))))
		(consp (cdr p)) (consp (cdr q))
		(equal (derivative (pmul (pstrip (cdr p) f) q f) f)
		       (padd (pmul (derivative (pstrip (cdr p) f) f) q f)
		             (pmul (pstrip (cdr p) f) (derivative q f) f)
			     f)))
           (equal (derivative (pmul p q f) f)
	          (padd (padd (pmul (monomial (car p) (degree p) f) (derivative q f) f)
                              (pmul (cmul (fnat (degree p) f) (monomial (car p) (1- (degree p)) f) f) q f)
                              f)
			(padd (pmul (derivative (pstrip (cdr p) f) f) q f)
		              (pmul (pstrip (cdr p) f) (derivative q f) f)
			      f)
			f)))
  :hints (("Goal" :use (derivative-pmul-7 derivative-pmul-9 derivative-pmul-12))))

(local-defthmd derivative-pmul-14
  (implies (and (fieldp f) (polyp p f) (polyp q f)
                (not (or (equal p (pzero f)) (equal q (pzero f))))
		(consp (cdr p)) (consp (cdr q)))
           (and (polyp (monomial (car p) (degree p) f) f)
	        (polyp (monomial (car p) (1- (degree p)) f) f)
	        (polyp (derivative q f) f)
		(polyp (cmul (fnat (degree p) f) (monomial (car p) (1- (degree p)) f) f) f)
		(polyp (pstrip (cdr p) f) f)
		(polyp (derivative (pstrip (cdr p) f) f) f)))
  :hints (("Goal" :expand ((len p) (len (cdr p)))
                  :in-theory (e/d (pzero polyp-derivative) (polyp-pzero))
		  :use (derivative-pmul-4 polyp-pzero
		        (:instance polyp-monomial (c (car p)) (k (1- (degree p))))
			(:instance polyp-cmul (c (fnat (degree p) f)) (x (monomial (car p) (1- (degree p)) f)))))))

(local-defthmd derivative-pmul-15
  (implies (and (fieldp f) (polyp c f) (polyp q f) (polyp m f) (polyp d f) (polyp p f) (polyp r f))
           (equal (padd (padd (pmul m d f) (pmul c q f) f)
	                (padd (pmul r q f) (pmul p d f) f)
			f)
		  (padd (pmul (padd c r f) q f )
		        (pmul (padd m p f) d f)
			f)))
  :hints (("Goal" :use ((:instance padd-comm (x (pmul m d f)) (y (pmul c q f)))
                        (:instance padd-assoc (x (pmul c q f)) (y (pmul m d f)) (z (padd (pmul r q f) (pmul p d f) f)))
                        (:instance padd-assoc (x (pmul m d f)) (y (pmul r q f)) (z (pmul p d f)))
			(:instance padd-comm (x (pmul r q f)) (y (pmul m d f)))
			(:instance padd-assoc (x (pmul r q f)) (y (pmul m d f)) (z (pmul p d f)))
			(:instance padd-assoc (x (pmul c q f)) (y (pmul r q f)) (z (padd (pmul m d f) (pmul p d f) f)))
			(:instance pdistrib-2 (x q) (y c) (z r))
			(:instance pdistrib-2 (x d) (y m) (z p))))))

(local-defthmd derivative-pmul-16
  (implies (and (fieldp f) (polyp p f) (polyp q f)
                (not (or (equal p (pzero f)) (equal q (pzero f))))
		(consp (cdr p)) (consp (cdr q))
		(equal (derivative (pmul (pstrip (cdr p) f) q f) f)
		       (padd (pmul (derivative (pstrip (cdr p) f) f) q f)
		             (pmul (pstrip (cdr p) f) (derivative q f) f)
			     f)))
           (equal (derivative (pmul p q f) f)
	          (padd (pmul (padd (cmul (fnat (degree p) f) (monomial (car p) (1- (degree p)) f) f)
                                    (derivative (pstrip (cdr p) f) f)
			            f)
		              q f)
	                (pmul (padd (monomial (car p) (degree p) f) (pstrip (cdr p) f) f) (derivative q f) f)
                        f)))
  :hints (("Goal" :use (derivative-pmul-13 derivative-pmul-14
                        (:instance derivative-pmul-15 (c (cmul (fnat (degree p) f) (monomial (car p) (1- (degree p)) f) f))
						      (m (monomial (car p) (degree p) f))
						      (d (derivative q f))
						      (p (pstrip (cdr p) f))
						      (r (derivative (pstrip (cdr p) f) f)))))))

(local-defun derivative-pmul-induct (p q f)
  (if (and (not (or (equal p (pzero f)) (equal q (pzero f))))
           (consp (cdr p)) (consp (cdr q)))
      (derivative-pmul-induct (pstrip (cdr p) f) q f)
    (list p q f)))

(defthmd derivative-pmul
  (implies (and (fieldp f) (polyp p f) (polyp q f))
           (equal (derivative (pmul p q f) f)
                  (padd (pmul (derivative p f) q f)
                        (pmul p (derivative q f) f)
                        f)))
  :hints (("Goal" :induct (derivative-pmul-induct p q f))
          ("Subgoal *1/2" :use (derivative-pmul-1 derivative-pmul-2 derivative-pmul-3))
          ("Subgoal *1/1" :use (derivative-pmul-5 derivative-pmul-4 derivative-pmul-16))))
                        

;; Proof:  We may assume (degree p) > 0 and (degree q) > 0.  Let k = (degree p), c = (car p), and
;; p' = (pstrip (cdr p) f).  Then

;;   p = (padd (monomial c k f) p' f)  [pdecomp]

;;   (derivative p f) = (padd (derivative (monomial c k f) f)            [derivative-padd]
;;                            (derivative p' f)
;;			      f)
;;                    = (padd (cmul (fnat k f) (monomial c (1- k) f) f)  [derivative-monomial]
;;                            (derivative p' f)
;;			      f)

;; and

;;   (derivative (pmul p q f) f) = (derivative (padd (pshift (cmul c q f) k f)     [definition of pmul]
;;                                                   (pmul p' q f)
;;                                                   f)
;;                                               f)
;;                               = (padd (derivative (pshift (cmul c q f) k f) f)  [derivative-padd] 
;;                                       (derivative (pmul p' q f) f)
;;                                       f)

;; Consider the 2 terms of the last sum.  The first term is

;;   (derivative (pshift (cmul c q f) k f) f)
;;     = (padd (pshift$ (derivative (cmul c q f) f) k f)              [derivative-pshift]
;;             (cmul (fnat k f) (pshift (cmul c q f) (1- k) f) f)
;;             f)

;; where

;;   (pshift$ (derivative (cmul c q f) f) k f)
;;     = (pshift$ (cmul c (derivative q f) f) k f)     [derivative-cmul]
;;     = (pmul (monomial c k f) (derivative q f) f)    [pmul-monomial]

;; and

;;   (cmul (fnat k f) (pshift (cmul c q f) (1- k) f) f)
;;     = (cmul (fnat k f) (pmul (monomial c (1- k) f) q f) f)   [pmul-monomial]
;;     = (pmul (cmul (fnat k f) (monomial c (1- k) f) f) q f)   [cmul-pmul]

;; By induction, the second term is

;;   (derivative (pmul p' q f) f) = (padd (pmul (derivative p' f) q f) (pmul p' (derivative q f) f) f)

;; Thus, by the algebraic properties of the polynomial ring,

;;   (derivative (pmul p q f) f)
;;     = (padd (padd (pmul (monomial c k f) (derivative q f) f)
;;                   (pmul (cmul (fnat k f) (monomial c (1- k) f) f) q f)
;;                   f)
;;             (padd (pmul (derivative p' f) q f)
;;                   (pmul p' (derivative q f) f)
;;                   f)
;;             f)
;;     = (padd (padd (pmul (cmul (fnat k f) (monomial c (1- k) f) f) q f)
;;                   (pmul (derivative p' f) q f)
;;		     f)
;;	       (padd (pmul (monomial c k f) (derivative q f) f)
;;	             (pmul p' (derivative q f) f)
;;		     f)
;;	       f)
;;     = (padd (pmul (padd (cmul (fnat k f) (monomial c (1- k) f) f)
;;                         (derivative p' f)
;;			   f)
;;		     q f)
;;	       (pmul (padd (monomial c k f) p' f) (derivative q f) f)
;;             f)
;;     = (padd (pmul (derivative p f) q f)
;;             (pmul p (derivative q f) f)
;;             f)

;;-----------------------------------------------------

;; The derivative commutes with phom:

(defthmd phom-monomial
  (implies (and (feltp c (fld1)) (natp k))
           (equal (phom (monomial c k (fld1)))
	          (monomial (hom c) k (fld2))))
  :hints (("Goal" :in-theory (enable polyp monomial)
                  :use ((:instance phom-pshift (p (list c)))))))

(defthm flift-fnat
  (implies (natp k)
           (equal (hom (fnat k (fld1)))
	          (fnat k (fld2))))
  :hints (("Goal" :induct (fact k))
          ("Subgoal *1/2" :in-theory (enable fnat))))

(defthmd derivative-phom-monomial
  (implies (and (feltp c (fld1)) (not (equal c (fzero (fld1)))) (posp k))
           (equal (derivative (phom (monomial c k (fld1))) (fld2))
	          (phom (derivative (monomial c k (fld1)) (fld1)))))
  :hints (("Goal" :in-theory (e/d (derivative-monomial phom-monomial) (hom-id))
                  :use (hom-id
		        (:instance hom-fzero (x c))
		        (:instance phom-cmul (c (fnat k (fld1))) (q (monomial c (1- k) (fld1))))))))

(local-defthmd derivative-phom-pconst
  (implies (and (polyp p (fld1)) (not (consp (cdr p))))
           (equal (derivative (phom p) (fld2))
	          (phom (derivative p (fld1)))))
  :hints (("Goal" :in-theory (enable polyp phom-id pconstp derivative-pconstp))))

(local-defthmd derivative-phom-step-1
  (implies (and (polyp p (fld1)) (consp (cdr p))
                (equal (derivative (phom (pstrip (cdr p) (fld1))) (fld2))
		       (phom (derivative (pstrip (cdr p) (fld1)) (fld1)))))
           (and (feltp (car p) (fld1)) (not (equal (car p) (fzero (fld1))))
	        (equal (phom p)
	               (padd (phom (monomial (car p) (degree p) (fld1)))
		             (phom (pstrip (cdr p) (fld1)))
			     (fld2)))))
  :hints (("Goal" :in-theory (enable polyp head tail)
	          :use (polyp
		        (:instance pdecomp (f (fld1)) (x p))
			(:instance polyp-monomial (c (car p)) (f (fld1)))
			(:instance phom-padd (p (head p (fld1))) (q (tail p (fld1))))))))

(local-defthmd derivative-phom-step-2
  (implies (and (polyp p (fld1)) (consp (cdr p)) (feltp (car p) (fld1)) (not (equal (car p) (fzero (fld1)))))
           (equal (derivative (padd (phom (monomial (car p) (degree p) (fld1)))
		                    (phom (pstrip (cdr p) (fld1)))
			            (fld2))
			      (fld2))
	          (padd (derivative (phom (monomial (car p) (degree p) (fld1))) (fld2))
		        (derivative (phom (pstrip (cdr p) (fld1))) (fld2))
			(fld2))))
  :hints (("Goal" :use ((:instance polyp-pstrip (f (fld1)) (x (cdr p)))
			(:instance polyp-phom (p (pstrip (cdr p) (fld1))))
			(:instance polyp-phom (p (monomial (car p) (degree p) (fld1))))
			(:instance derivative-padd (f (fld2)) (p (phom (monomial (car p) (degree p) (fld1))))
			                                 (q (phom (pstrip (cdr p) (fld1)))))
			(:instance polyp-monomial (f (fld1)) (c (car p)) (k (degree p)))))))

(local-defthmd derivative-phom-step-3
  (implies (and (polyp p (fld1)) (consp (cdr p))
                (equal (derivative (phom (pstrip (cdr p) (fld1))) (fld2))
		       (phom (derivative (pstrip (cdr p) (fld1)) (fld1)))))
           (equal (derivative p (fld1))
	          (padd (derivative (monomial (car p) (degree p) (fld1)) (fld1))
		        (derivative (pstrip (cdr p) (fld1)) (fld1))
			(fld1))))
  :hints (("Goal" :in-theory (enable polyp head tail)
	          :use ((:instance pdecomp (f (fld1)) (x p))
			(:instance polyp-monomial (f (fld1)) (c (car p)) (k (degree p)))
			(:instance polyp-pstrip (f (fld1)) (x (cdr p)))
                        (:instance derivative-padd (f (fld1)) (p (monomial (car p) (degree p) (fld1))) (q (pstrip (cdr p) (fld1))))))))

(local-defthmd derivative-phom-step-4
  (implies (and (polyp p (fld1)) (consp (cdr p)) (feltp (car p) (fld1)) (not (equal (car p) (fzero (fld1))))
                (equal (derivative (phom (pstrip (cdr p) (fld1))) (fld2))
		       (phom (derivative (pstrip (cdr p) (fld1)) (fld1)))))
           (equal (phom (padd (derivative (monomial (car p) (degree p) (fld1)) (fld1))
		               (derivative (pstrip (cdr p) (fld1)) (fld1))
			       (fld1)))
	          (padd (phom (derivative (monomial (car p) (degree p) (fld1)) (fld1)))
		        (phom (derivative (pstrip (cdr p) (fld1)) (fld1)))
			(fld2))))
  :hints (("Goal" :in-theory (enable polyp-derivative)
	          :use ((:instance polyp-monomial (f (fld1)) (c (car p)) (k (degree p)))
			(:instance polyp-pstrip (f (fld1)) (x (cdr p)))
                        (:instance phom-padd (p (derivative (monomial (car p) (degree p) (fld1)) (fld1)))
			                      (q (derivative (pstrip (cdr p) (fld1)) (fld1))))))))

(local-defthmd derivative-phom-step-5
  (implies (and (polyp p (fld1)) (consp (cdr p)) (feltp (car p) (fld1)) (not (equal (car p) (fzero (fld1)))))
           (equal (derivative (phom (monomial (car p) (degree p) (fld1))) (fld2))
		  (phom (derivative (monomial (car p) (degree p) (fld1)) (fld1)))))
  :hints (("Goal" :expand ((len p) (len (cdr p)))
                  :use ((:instance derivative-phom-monomial (c (car p)) (k (degree p)))))))			

(local-defthmd derivative-phom-step
  (implies (and (polyp p (fld1)) (consp (cdr p))
                (equal (derivative (phom (pstrip (cdr p) (fld1))) (fld2))
		       (phom (derivative (pstrip (cdr p) (fld1)) (fld1)))))
           (equal (derivative (phom p) (fld2))
	          (phom (derivative p (fld1)))))
  :hints (("Goal" :use (derivative-phom-step-1 derivative-phom-step-2 derivative-phom-step-3
                        derivative-phom-step-4 derivative-phom-step-5))))

(local-defun derivative-phom-induct (p)
  (if (consp (cdr p))
      (derivative-phom-induct (pstrip (cdr p) (fld1)))
    (list p)))

(defthmd derivative-phom
  (implies (polyp p (fld1))
           (equal (derivative (phom p) (fld2))
	          (phom (derivative p (fld1)))))
  :hints (("Goal" :induct (derivative-phom-induct p))
          ("Subgoal *1/2" :use (derivative-phom-pconst))
	  ("Subgoal *1/1" :use (derivative-phom-step))))

;; By functional instantiation, the derivative commutes with plift:

(defthmd derivative-plift
  (implies (and (extensionp e f) (polyp p f))
           (equal (derivative (plift p f e) e)
	          (plift (derivative p f) f e)))
  :hints (("Goal" :use ((:functional-instance derivative-phom
                         (fld1 (lambda () (if (and (extensionp e f) (polyp p f)) f (fld1))))
                         (fld2 (lambda () (if (and (extensionp e f) (polyp p f)) e (fld2))))
			 (hom (lambda (z) (if (and (extensionp e f) (polyp p f)) (flift z f e) (hom z))))
			 (phom (lambda (z) (if (and (extensionp e f) (polyp p f)) (plift z f e) (phom z)))))))))


;;----------------------------------------------------------------------------------------------------------
;;                                             Separable Polynomials
;;----------------------------------------------------------------------------------------------------------

;; Let r = (root-poly x f).  x is a multiple root of p iff the square of r^2 divides p:

(defund multiple-prootp (x p f)
  (pdivides (ppower (root-poly x f) 2 f) p f))

;; Here p' will denote the derivative of p.  Let x be a root of p.  Then p = r * q, 
;; p' = q + r * q', and x is a multiple root of p <=> x is a root of q <=> x is a root of p':

(local-defthmd prootp-derivative-1
  (implies (and (fieldp f) (polyp p f) (feltp x f))
           (iff (multiple-prootp x p f)
                (and (prootp x p f)
                     (pdivides (root-poly x f)
		               (pquot p (root-poly x f) f)
			       f))))
  :hints (("Goal" :in-theory (enable prootp multiple-prootp)
                  :expand ((:free (n) (ppower (list (fone f) (fneg x f)) n f)))
                  :use (polyp-root-poly prootp-pdivides
		        (:instance product-pdivides (x (root-poly x f)) (y (root-poly x f)) (z p))))))

(defthm derivative-root-poly
  (implies (and (fieldp f) (feltp x f))
           (equal (derivative (root-poly x f) f)
	          (pone f)))
  :hints (("Goal" :expand ((ntimes 1 (fone f) f) (:free (p) (derivative p f)))
                  :in-theory (enable pone fnat pconstp))))

(defthm root-poly-nonzero
  (implies (and (fieldp f) (feltp x f))
           (not (equal (root-poly x f) (pzero f))))
  :hints (("Goal" :in-theory (enable pzero))))

(in-theory (disable root-poly))
(in-theory (enable polyp-root-poly))

(local-defthmd prootp-derivative-2
  (implies (and (fieldp f) (polyp p f) (feltp x f) (pdivides (root-poly x f) p f))
           (and (polyp (pquot p (root-poly x f) f) f)
	        (equal (derivative p f)
	               (padd (pquot p (root-poly x f) f)
		             (pmul (root-poly x f) (derivative (pquot p (root-poly x f) f) f) f)
			     f))))
  :hints (("Goal" :use ((:instance polyp-pquot-prem (x p) (y (root-poly x f)))
                        (:instance pdivides-pquot (x (root-poly x f)) (y p))
                        (:instance derivative-pmul (p (root-poly x f)) (q (pquot p (root-poly x f) f)))))))

(local-defthmd prootp-derivative-3
  (implies (and (fieldp f) (polyp p f) (feltp x f) (pdivides (root-poly x f) p f)
                (pdivides (root-poly x f) (pquot p (root-poly x f) f) f))
           (pdivides (root-poly x f) (derivative p f) f))
  :hints (("Goal" :in-theory (enable polyp-derivative  prootp-derivative-2)
                  :use ((:instance pdivides-multiple (x (root-poly x f)) (y (derivative (pquot p (root-poly x f) f) f)))
                        (:instance pdivides-padd (x (root-poly x f))
			                         (y (pquot p (root-poly x f) f))
						 (z (pmul (root-poly x f) (derivative (pquot p (root-poly x f) f) f) f)))))))



(local-defthmd prootp-derivative-4
  (implies (and (fieldp f) (polyp p f) (feltp x f) (pdivides (root-poly x f) p f)
                (pdivides (root-poly x f) (derivative p f) f))
	   (pdivides (root-poly x f) (pquot p (root-poly x f) f) f))           
  :hints (("Goal" :in-theory (enable polyp-derivative  prootp-derivative-2)
                  :use ((:instance pdivides-multiple (x (root-poly x f)) (y (derivative (pquot p (root-poly x f) f) f)))
                        (:instance pdivides-padd-converse (x (root-poly x f))
			                                  (y (pquot p (root-poly x f) f))
						          (z (pmul (root-poly x f) (derivative (pquot p (root-poly x f) f) f) f)))))))

(defthmd prootp-derivative
  (implies (and (fieldp f) (polyp p f) (feltp x f))
           (iff (multiple-prootp x p f)
                (and (prootp x p f)
                     (prootp x (derivative p f) f))))
  :hints (("Goal" :in-theory (enable polyp-derivative prootp-pdivides prootp-derivative-1)
                  :use (prootp-derivative-3 prootp-derivative-4))))

;; p is separable if p and p' are relatively prime:

(defund separablep (p f)
  (equal (pgcd p (derivative p f) f)
         (pone f)))

(defthmd derivative-pzero-not-separablep
  (implies (and (fieldp f) (polyp p f) (>= (degree p) 1) (equal (derivative p f) (pzero f)))
           (not (separablep p f)))
  :hints (("Goal" :in-theory (enable polyp separablep pone pzero)
                  :use (pgcd-pzero
		        (:instance pgcd-comm (x p) (y (pzero f)))
			(:instance monicp-make-monic (x p))))))

(defthmd pconstp-separablep
  (implies (and (fieldp f) (polyp p f) (= (degree p) 0) (not (equal p (pzero f))))
           (separablep p f))
  :hints (("Goal" :in-theory (enable pone polyp pzero make-monic separablep pconstp)
                  :expand ((CMUL (FRECIP (CAR P) F) (CDR P) F) (CMUL (FRECIP (CAR P) F) P F))
                  :use (derivative-pconstp pgcd-pzero
		        (:instance polyp-car-nonzero (x p))
			(:instance frecip-not-fzero (x (car p)))
		        (:instance pgcd-comm (x p) (y (pzero f)))))))

;; Look at pgcd-monic in extensions.lisp.  This is better:

(local-defthmd pgcd-monic-better
  (implies (and (fieldp f) 
                (polyp x f) (polyp y f)
                (not (equal x (pzero f))))
           (monicp (pgcd x y f) f))
  :hints (("Goal" :use (pgcd-monic pgcd-comm monicp-make-monic
                        (:instance pgcd-pzero (p x))))))

(local-defthmd separablep-linear-1
  (implies (and (fieldp f) (polyp p f) (equal (degree p) 1))
           (and (polyp (pgcd p (derivative p f) f) f)
	        (equal (degree (pgcd p (derivative p f) f)) 0)))
  :hints (("Goal" :in-theory (enable pzero polyp)
                  :expand ((LEN (PGCD P (LIST (CAR P)) F)))
                  :use (derivative-linear
		        (:instance polyp-pgcd (x p) (y (list (car p))))
		        (:instance pgcd-divides (x p) (y (derivative p f)))
			(:instance pdivides-degree (x (pgcd p (derivative p f) f)) (y (list (car p))))))))

(in-theory (enable polyp-pgcd polyp-derivative))

(local-defthmd separablep-linear-2
  (implies (and (fieldp f) (polyp p f) (equal (degree p) 1))
           (monicp (pgcd p (derivative p f) f) f))
  :hints (("Goal" :use ((:instance pgcd-monic-better (x p) (y (derivative p f)))))))

(local-defthmd separablep-linear-3
  (implies (and (fieldp f) (polyp p f) (monicp p f) (equal (degree p) 0))
           (equal (pone f) p))
  :hints (("Goal" :in-theory (enable monicp pone polyp)
                  :expand ((len p) (len (cdr p))))))
		  
(defthmd separablep-linear
  (implies (and (fieldp f) (polyp p f) (equal (degree p) 1))
           (separablep p f))
  :hints (("Goal" :in-theory (enable separablep)
                  :use (separablep-linear-1 separablep-linear-2
		        (:instance separablep-linear-3 (p (pgcd p (derivative p f) f)))))))

;; Suppose p is separable and divisible by q.  Let p = q * s.  Then p' = q' * s + q * s'.  Let g = (pgcd q q').  Since g divides
;; q and q', g divides p and p', which implies g = 1 and q is separable:

(defthmd pdivides-separablep-1
  (implies (and (fieldp f) (polyp p f) (polyp q f)
                (not (equal p (pzero f))) (not (equal q (pzero f)))  (pdivides q p f))
           (let ((g (pgcd q (derivative q f) f)))
	     (and (pdivides g p f)
	          (pdivides g (derivative p f) f))))
  :hints (("Goal" :use ((:instance pdivides-pquot (x q) (y p))
                        (:instance polyp-pquot-prem (x p) (y q))
			(:instance derivative-pmul (p q) (q (pquot p q f)))
			(:instance polyp-derivative (p q))
			(:instance polyp-derivative (p (pquot p q f)))
			(:instance pgcd-divides (x q) (y (derivative q f)))
			(:instance pdivides-pmul (x (pgcd q (derivative q f) f)) (y (derivative q f)) (z (pquot p q f)))
			(:instance pdivides-pmul (x (pgcd q (derivative q f) f)) (y q) (z (derivative (pquot p q f) f)))
			(:instance pdivides-padd (x (pgcd q (derivative q f) f)) (y (pmul (derivative q f) (pquot p q f) f)) (z (pmul q (derivative (pquot p q f) f) f)))
			(:instance pdivides-pmul (x (pgcd q (derivative q f) f)) (y q) (z (pquot p q f)))
			(:instance polyp-pgcd (x q) (y (derivative q f)))))))

(defthmd pdivides-separablep-2
  (implies (and (fieldp f) (polyp p f) (polyp q f) (>= (degree q) 1) (separablep p f)
                (not (equal p (pzero f))) (not (equal q (pzero f)))  (pdivides q p f))
           (pdivides (pgcd q (derivative q f) f)
	             (pone f)
		     f))
  :hints (("Goal" :in-theory (enable separablep)
                  :use (polyp-derivative  pdivides-separablep-1
                        (:instance divides-pgcd (z (pgcd q (derivative q f) f)) (x p) (y (derivative p f)))
			(:instance polyp-derivative (p q))
			(:instance polyp-pgcd (x q) (y (derivative q f)))))))

(defthmd pdivides-separablep-3
  (implies (and (fieldp f) (polyp p f) (polyp q f) (>= (degree q) 1) (separablep p f)
                (not (equal p (pzero f))) (not (equal q (pzero f)))  (pdivides q p f))
           (not (equal (derivative q f) (pzero f))))
  :hints (("Goal" :in-theory (enable pzero pone)
                  :use (pdivides-separablep-2 polyp-pone polyp-pzero
                        (:instance pgcd-pzero (p q))
			(:instance pgcd-comm (x q) (y (pzero f)))
			(:instance monicp-make-monic (x q))
			(:instance pdivides-degree (x (make-monic q f)) (y (pone f)))))))

(defthmd pdivides-separablep
  (implies (and (fieldp f) (polyp p f) (polyp q f) (>= (degree q) 1) (separablep p f)
                (not (equal p (pzero f))) (not (equal q (pzero f))) (pdivides q p f))
           (separablep q f))
  :hints (("Goal" :in-theory (enable pconstp pone monicp separablep)
                  :use (pdivides-separablep-2 pdivides-separablep-3 polyp-pone
                        (:instance polyp-pgcd (x q) (y (derivative q f)))
			(:instance polyp-derivative (p q))
                        (:instance pgcd-monic (x q) (y (derivative q f)))
			(:instance pdivides-monic-equal (x (pone f)) (y (pgcd q (derivative q f) f)))
			(:instance pconstp-pdivides (y (pone f)) (x (pgcd q (derivative q f) f)))))))

;; We shall prove that the product of relatively prime separable polynomials is separable.
;; Let0 p and q be nonzero separable polynomials with (pgcd p q f) = 1 and suppose p * q is not
;; separable.  Then we can find a non-constant irreducible polynomial r that divides both p * q and 
;; (p * q)' = p' * q + p * q'.  Suppose r divides p.  Then r divides p * q' and therefore r divides
;; (p * q)' - p * q' = p' * q.  But then either r divides p', contradicting separability of p, or r
;; divides q, contradicting (pgcd p q f) = 1.  Thus r cannot divide p, and similarly, r cannot divide q.
;; By peuclid, r does not divide p * q, a contradiction.

(local-defthmd separablep-pmul-1
  (implies (and (fieldp f)
                (polyp p f)
		(monicp p f)
		(not (equal p (pone f))))
	   (>= (degree p) 1))
  :hints (("Goal" :in-theory (enable monicp polyp pone)
                  :expand ((len p) (len (cdr p))))))

(local-defthmd separablep-pmul-2
  (implies (and (fieldp f) (polyp p f) (not (equal p (pzero f)))
                (not (separablep p f)))
	   (>= (degree (pgcd p (derivative p f) f)) 1))
  :hints (("Goal" :in-theory (enable separablep)
                  :use ((:instance pgcd-monic-better (x p) (y (derivative p f)))
                        (:instance separablep-pmul-1 (p (pgcd p (derivative p f) f)))))))

(local-defthmd separablep-pmul-3
  (implies (and (fieldp f) (polyp p f) (not (equal p (pzero f)))
                (not (separablep p f)))
	   (let ((r (irred-factor (pgcd p (derivative p f) f) f)))
	     (and (polyp r f)
	          (irreduciblep r f)
		  (>= (degree r) 1)
		  (pdivides r p f)
		  (pdivides r (derivative p f) f))))
  :hints (("Goal" :use (separablep-pmul-2
		        (:instance pgcd-divides (x p) (y (derivative p f)))
			(:instance pdivides-transitive (x (irred-factor (pgcd p (derivative p f) f) f)) (y (pgcd p (derivative p f) f)) (z p))
			(:instance pdivides-transitive (x (irred-factor (pgcd p (derivative p f) f) f)) (y (pgcd p (derivative p f) f)) (z (derivative p f)))
                        (:instance irreduciblep-irred-factor (p (pgcd p (derivative p f) f)))))))

(local-defthmd separablep-pmul-4
  (implies (and (fieldp f) (polyp p f) (polyp q f))
           (equal (pmul (derivative p f) q f)
	          (padd (derivative (pmul p q f) f)
		        (pmul p (pneg (derivative q f) f) f)
			f)))
  :hints (("Goal" :use (derivative-pmul
                        (:instance padd-assoc (x (pmul (derivative p f) q f)) (y (pmul p (derivative q f) f)) (z (pneg (pmul p (derivative q f) f) f)))
			(:instance padd-pneg (x (pmul p (derivative q f) f)))
			(:instance pmul-comm (x p) (y (derivative q f)))
			(:instance pmul-pneg (x (derivative q f)) (y p))
			(:instance pmul-comm (x p) (y (pneg (derivative q f) f)))))))

(local-defthmd separablep-pmul-5
  (implies (and (fieldp f) (polyp p f) (polyp q f)
                (polyp r f)
	        (irreduciblep r f)
		(>= (degree r) 1)
		(pdivides r (derivative (pmul p q f) f) f)
		(pdivides r p f))
 	   (or (pdivides r (derivative p f) f)
	       (pdivides r q f)))
  :hints (("Goal" :use (separablep-pmul-4
                        (:instance pdivides-pmul (x r) (y p) (z (pneg (derivative q f) f)))
                        (:instance pdivides-padd (x r) (y (derivative (pmul p q f) f)) (z (pmul p (pneg (derivative q f) f) f)))
                        (:instance peuclid (p r) (x (derivative p f)) (y q))))))

(local-defthmd separablep-pmul-6
  (implies (and (fieldp f) (polyp p f) (not (equal p (pzero f)))
                (polyp q f) (equal (pgcd p q f) (pone f))
                (polyp r f)
	        (irreduciblep r f)
		(>= (degree r) 1)
		(pdivides r p f))
 	   (not (pdivides r q f)))
  :hints (("Goal" :in-theory (enable pzero pone)
                  :use ((:instance divides-pgcd (z r) (x p) (y q))
		        (:instance pdivides-degree (x r) (y (pone f)))))))

(local-defthmd separablep-pmul-7
  (implies (and (fieldp f) (polyp p f) (not (equal p (pzero f))) (separablep p f)
                (polyp q f) (equal (pgcd p q f) (pone f))
                (polyp r f)
	        (irreduciblep r f)
		(>= (degree r) 1)
		(pdivides r (derivative (pmul p q f) f) f))
           (not (pdivides r p f)))
  :hints (("Goal" :in-theory (enable separablep)
                  :use (separablep-pmul-5 separablep-pmul-6
                        (:instance separablep-pmul-6 (q (derivative p f)))))))

(local-defthmd separablep-pmul-8
  (implies (and (fieldp f) (polyp q f) (not (equal q (pzero f))) (separablep q f)
                (polyp p f) (equal (pgcd p q f) (pone f))
                (polyp r f)
	        (irreduciblep r f)
		(>= (degree r) 1)
		(pdivides r (derivative (pmul p q f) f) f))
           (not (pdivides r q f)))
  :hints (("Goal" :use ((:instance separablep-pmul-7 (p q) (q p))
                        (:instance pmul-comm (x p) (y q))
			(:instance pgcd-comm (x p) (y q))))))

(local-defthmd separablep-pmul-9
  (implies (and (fieldp f)
                (polyp p f) (not (equal p (pzero f))) (separablep p f)
                (polyp q f) (not (equal q (pzero f))) (separablep q f)
                (equal (pgcd p q f) (pone f))
                (polyp r f)
	        (irreduciblep r f)
		(>= (degree r) 1)
                (pdivides r (derivative (pmul p q f) f) f))
	   (not (pdivides r (pmul p q f) f)))
  :hints (("Goal" :use (separablep-pmul-7 separablep-pmul-8
                        (:instance peuclid (p r) (x p) (y q))))))

(defthmd separablep-pmul
  (implies (and (fieldp f)
                (polyp p f) (not (equal p (pzero f))) (separablep p f)
                (polyp q f) (not (equal q (pzero f))) (separablep q f)
                (equal (pgcd p q f) (pone f)))
	   (separablep (pmul p q f) f))
  :hints (("Goal" :use ((:instance separablep-pmul-3 (p (pmul p q f)))
                        (:instance separablep-pmul-9 (r (irred-factor (pgcd (pmul p q f) (derivative (pmul p q f) f) f) f)))))))
  
;; By plift-pgcd and derivative-plift, if p is separable over f, then (plift p f e) is separable over e:

(local-defthmd separablep-extension-1
  (implies (and (extensionp e f) (polyp p f) (not (equal p (pzero f))) (equal (derivative p f) (pzero f)))
           (iff (separablep (plift p f e) e)
                (separablep p f)))
  :hints (("Goal" :in-theory (enable polyp polyp-plift pconstp pzero polyp-derivative derivative-pconstp)
                  :use (pconstp-separablep len-plift plift-id plift-pzero derivative-pzero-not-separablep derivative-plift
		        (:instance derivative-pzero-not-separablep (p (plift p f e)) (f e))
			(:instance pconstp-separablep (p (plift p f e)) (f e))
			(:instance plift-pgcd (q (derivative p f)))))))

(local-defthmd separablep-extension-2
  (implies (and (extensionp e f) (polyp p f) (not (equal (derivative p f) (pzero f))))
           (iff (separablep (plift p f e) e)
                (separablep p f)))
  :hints (("Goal" :in-theory (enable polyp pone polyp-plift separablep pconstp pzero polyp-derivative derivative-pconstp)
                  :use (plift-id plift-pzero derivative-plift
		        (:instance plift-1-1 (q (pone f)))
			(:instance polyp-pgcd (x p) (y (DERIVATIVE P F)))
		        (:instance plift-1-1 (p (PGCD P (DERIVATIVE P F) F)) (q (pone f)))
			(:instance plift-pgcd (q (derivative p f)))))))
			
(defthmd separablep-extension
  (implies (and (extensionp e f) (polyp p f) (not (equal p (pzero f))))
           (iff (separablep (plift p f e) e)
                (separablep p f)))
  :hints (("Goal" :use (separablep-extension-1 separablep-extension-2))))

;; a separable polynomial over f has no multiple roots in any extension of f:

(defthmd separable-no-multiple-root
  (implies (and (fieldp f) (polyp p f) (not (equal p (pzero f))) (separablep p f)
                (feltp x f))
           (not (multiple-prootp x p f)))
  :hints (("Goal" :in-theory (enable polyp pzero pone polyp-derivative prootp-derivative prootp-pdivides separablep)
                  :use (monicp-irreduciblep-root-poly
		        (:instance divides-pgcd (z (root-poly x f)) (x p) (y (derivative p f)))
		        (:instance pdivides-degree (x (root-poly x f)) (y (pone f)))))))

(defthmd separable-no-multiple-root-extension
  (implies (and (extensionp e f)
                (polyp p f) (not (equal p (pzero f))) (separablep p f)
                (feltp x e))
           (not (multiple-prootp x (plift p f e) e)))
  :hints (("Goal" :use (separablep-extension polyp-plift plift-pzero
                        (:instance separable-no-multiple-root (f e) (p (plift p f e)))))))
			
;; An irreducible polynomial is separable unless its derivative is 0:

(local-defthmd separablep-derivative-nonzero-1
  (implies (and (fieldp f) (polyp p f) (irreduciblep p f) (> (degree p) 0)
                (separablep p f))
           (not (equal (derivative p f) (pzero f))))
  :hints (("Goal" :in-theory (enable pone polyp-derivative separablep)
                  :use (pgcd-pzero
		        (:instance monicp-make-monic (x p))
		        (:instance pgcd-comm (x p) (y (derivative p f)))))))

(local-defthmd separablep-derivative-nonzero-2
  (implies (and (fieldp f) (polyp p f) (irreduciblep p f) (> (degree p) 0)
                (not (separablep p f)))
           (equal (derivative p f) (pzero f)))
  :hints (("Goal" :in-theory (enable pconstp polyp-derivative separablep)
                  :use (polyp-derivative
		        (:instance pgcd-irreduciblep (x (derivative p f)))
		        (:instance pdivides-degree (x p) (y (derivative p f)))))))

(defthmd separablep-derivative-nonzero
  (implies (and (fieldp f) (polyp p f) (irreduciblep p f) (not (pconstp p)))
           (iff (separablep p f)
                (not (equal (derivative p f) (pzero f)))))
  :hints (("Goal" :in-theory (enable pconstp)
                  :expand ((len p) (len (cdr p)))
                  :use (separablep-derivative-nonzero-1 separablep-derivative-nonzero-2))))

;; In a field of characteristic 0, the derivative of a non-constant polynomial cannot be 0.  Consequently, every
;; irreducible polynomial over a field of characteric 0 is separable:

(defthmd char-0-derivative-nonzero
  (implies (and (fieldp f) (= (fchar f) 0) (polyp p f) (not (pconstp p)))
           (not (equal (derivative p f) (pzero f))))
  :hints (("Goal" :in-theory (enable pzero polyp derivative pconstp)
                  :expand ((len p) (len (cdr p)) (derivative-aux p f))
		  :use ((:instance field-integral-domain (x (car p)) (y (fnat (degree p) f)))
		        (:instance fchar-0-fnat-non-0 (n (degree p)))))))

(defthmd char-0-separablep
  (implies (and (fieldp f) (= (fchar f) 0)
                (polyp p f) (irreduciblep p f) (not (equal p (pzero f))))
           (separablep p f))
  :hints (("Goal" :in-theory (enable pconstp)
                  :use (char-0-derivative-nonzero separablep-derivative-nonzero pconstp-separablep))))
                        
;; It is also true that in any extension of Fp, i.e., any finite field, every polynomial is separable, but the
;; proof of this result is deferred to the book "finite".  Thus, only infinite fields of prime characteristic
;; may have inseparable polynomials.


;;----------------------------------------------------------------------------------------------------------
;;                                      Embeddings of an Extension Field
;;----------------------------------------------------------------------------------------------------------

;; Let e and k be extensions of a field f.  An embedding of e in k over f is conceptually a field homomorphism
;; from e into k that fixes f.  To formalize this notion, We shall define 3 functions:

;; (1) (embed x phi k f): If x is an element of e and phi is an embedding of e in k over f, then this is the
;;     image of x in k under phi.

;; (2) (pembed p phi k f): If p is a generalized polynomial over e, then this is the image of p under phi, 
;;     i.e, the generalized polynomial over k constructed by replacing each coefficient of p with its image
;;    under phi.

;; (3) (embeddingp phi e k f): This is the predicate that recognizes phi as a well-formed embedding of e in k
;;     over f.  Such an embedding phi is represented by a list of elements of k of length (len e) - (len f),
;;     constructed recursively as follows:

;;     (a) If e = f, then phi = () and (embed x phi k f) = (flift x k f).

;;     (b) Otherwise. let phi' be an embedding of (cdr e) in k over f.  Then phi may be constructed as an 
;;         extension of phi' by specifying the image of (primitive e) under phi, which must be a root of the 
;;         image of (car e) under phi'.  If this root is b, then phi = (b . phi').

;; These 3 functions are formally defined as follows.  Note that the first 2 are mutually recursive:

(encapsulate ()
  (local (include-book "ordinals/lexicographic-book" :dir :system))
  (set-well-founded-relation acl2::l<)
  (mutual-recursion

    (defund embed (x phi k f)
      (declare (xargs :measure (list (len phi) (acl2-count x))))
      (if (consp phi)
          (peval (pembed x (cdr phi) k f) (car phi) k)
        (flift x f k)))

    (defun pembed (p phi k f)
      (declare (xargs :measure (list (len phi) (acl2-count p))))
      (if (consp p)
          (cons (embed (car p) phi k f)
                (pembed (cdr p) phi k f))
        ()))
  )
)

(defund embeddingp (phi e k f)
  (if (equal e f)
      (null phi)
    (and (consp phi)
	 (prootp (car phi) (pembed (car e) (cdr phi) k f) k)
	 (embeddingp (cdr phi) (cdr e) k f))))

;; Our objective is to prove the following 5 essential properties:

;; (defthmd embed-image
;;   (implies (and (embeddingp phi e k f) (extensionp e f) (extensionp k f)
;;                 (feltp x e))
;;            (feltp (embed x phi k f) k)))

;; (defthmd embed-fixes
;;   (implies (and (extensionp e f) (extensionp k f) (embeddingp phi e k f)
;;                 (feltp x f))
;;            (equal (embed (flift x f e) phi k f)
;;                   (flift x f k))))

;; (defthmd embed-fadd
;;   (implies (and (extensionp e f) (extensionp k f) (embeddingp phi e k f)
;;                 (feltp x e) (feltp y e))
;;            (equal (embed (fadd x y e) phi k f)
;;                   (fadd (embed x phi k f) (embed y phi k f) k))))

;; (defthmd embed-fmul
;;   (implies (and (extensionp e f) (extensionp k f) (embeddingp phi e k f)
;;                 (feltp x e) (feltp y e))
;;            (equal (embed (fmul x y e) phi k f)
;;                   (fmul (embed x phi k f) (embed y phi k f) k))))

;; (defthmd embed-fzero-fone
;;   (implies (and (extensionp e f) (extensionp k f) (embeddingp phi e k f))
;;            (and (equal (embed (fzero e) phi k f) (fzero k))
;;                 (equal (embed (fone e) phi k f) (fone k)))))

;; We shall prove by induction that every embedding satisfies the predicate embed-props,
;; defined as follows:

(defun-sk embed-prop-1 (phi e k f)
  (forall (x)
    (implies (feltp x e)
             (feltp (embed x phi k f) k))))

(defun-sk embed-prop-2 (phi e k f)
  (forall (x)
    (implies (feltp x f)
             (equal (embed (flift x f e) phi k f)
	            (flift x f k)))))

(defun-sk embed-prop-3 (phi e k f)
  (forall (x1 x2)
    (implies (and (feltp x1 e) (feltp x2 e))
             (let ((y1 (embed x1 phi k f)) (y2 (embed x2 phi k f)))
	       (and (equal (embed (fadd x1 x2 e) phi k f)
	                   (fadd y1 y2 k))
		    (equal (embed (fmul x1 x2 e) phi k f)
	                   (fmul y1 y2 k)))))))

(defun embed-prop-4 (phi e k f)
  (and (equal (embed (fzero e) phi k f) (fzero k))
       (equal (embed (fone e) phi k f) (fone k))))

(defund embed-props (phi e k f)
  (and (embed-prop-1 phi e k f)
       (embed-prop-2 phi e k f)
       (embed-prop-3 phi e k f)
       (embed-prop-4 phi e k f)))

;; The usual lemmas corresponding to the above definitions:

(defthm embed-prop-1-lemma
  (implies (and (embed-props phi e k f) (feltp x e))
           (feltp (embed x phi k f) k))
  :hints (("Goal" :in-theory (enable embed-props)
                  :use (embed-prop-1-necc))))

(defthmd embed-prop-1-witness-lemma
  (let ((x (embed-prop-1-witness phi e k f)))
    (implies (implies (feltp x e) (feltp (embed x phi k f) k))
	     (embed-prop-1 phi e k f))))

(defthm embed-prop-2-lemma
  (implies (and (embed-props phi e k f) (feltp x f))
           (equal (embed (flift x f e) phi k f)
	                 (flift x f k)))
  :hints (("Goal" :in-theory (enable embed-props)
                  :use (embed-prop-2-necc))))

(defthmd embed-prop-2-witness-lemma
  (let ((x (embed-prop-2-witness phi e k f)))
    (implies (implies (feltp x f)
                      (equal (embed (flift x f e) phi k f)
	                     (flift x f k)))
	     (embed-prop-2 phi e k f))))

(defthm embed-prop-3-lemma
  (implies (and (embed-props phi e k f) (feltp x1 e) (feltp x2 e))
           (let ((y1 (embed x1 phi k f)) (y2 (embed x2 phi k f)))
	     (and (equal (embed (fadd x1 x2 e) phi k f)
	                 (fadd y1 y2 k))
		  (equal (embed (fmul x1 x2 e) phi k f)
	                 (fmul y1 y2 k)))))
  :hints (("Goal" :in-theory (enable embed-props)
                  :use (embed-prop-3-necc))))

(defthmd embed-prop-3-witness-lemma
  (mv-let (x1 x2) (embed-prop-3-witness phi e k f)
    (implies (implies (and (feltp x1 e) (feltp x2 e))
                      (let ((y1 (embed x1 phi k f)) (y2 (embed x2 phi k f)))
	                (and (equal (embed (fadd x1 x2 e) phi k f)
	                            (fadd y1 y2 k))
		             (equal (embed (fmul x1 x2 e) phi k f)
	                            (fmul y1 y2 k)))))
	     (embed-prop-3 phi e k f))))

(defthm embed-prop-4-lemma
  (implies (embed-props phi e k f)
           (and (equal (embed (fzero e) phi k f)
	               (fzero k))
		(equal (embed (fone e) phi k f)
	               (fone k))))
  :hints (("Goal" :in-theory (enable embed-props embed-prop-4))))

(in-theory (disable embed-prop-1 embed-prop-2 embed-prop-3 embed-prop-4))

;; If an embedding phi satistfies the above properties, then it is a homomorphism and inherits
;; the properties of hom:

(defthmd embed-fzero-*
  (implies (and (fieldp e) (fieldp k) (embed-props phi e k f)
                (feltp x e) (equal (embed x phi k f) (fzero k)))
	   (equal (fzero e) x))
  :hints (("Goal" :use ((:functional-instance hom-fzero
                         (hom (lambda (x) (if (and (fieldp e) (fieldp k) (embed-props phi e k f)) (embed x phi k f) (hom x))))
			 (fld1 (lambda () (if (and (fieldp e) (fieldp k) (embed-props phi e k f)) e (fld1))))
			 (fld2 (lambda () (if (and (fieldp e) (fieldp k) (embed-props phi e k f)) k (fld2)))))))))

;; Simiarly, pembed inherits the properties of phom:

(defthmd polyp-pembed-*
  (implies (and (fieldp e) (fieldp k) (embed-props phi e k f)
                (polyp p e))
	   (polyp (pembed p phi k f) k))
  :hints (("Goal" :use ((:functional-instance polyp-phom
                         (hom (lambda (x) (if (and (fieldp e) (fieldp k) (embed-props phi e k f)) (embed x phi k f) (hom x))))
			 (fld1 (lambda () (if (and (fieldp e) (fieldp k) (embed-props phi e k f)) e (fld1))))
			 (fld2 (lambda () (if (and (fieldp e) (fieldp k) (embed-props phi e k f)) k (fld2))))
			 (phom (lambda (p) (if (and (fieldp e) (fieldp k) (embed-props phi e k f)) (pembed p phi k f) (phom p)))))))))

(defthmd monicp-pembed-*
  (implies (and (fieldp e) (fieldp k) (embed-props phi e k f)
                (polyp p e) (monicp p e))
	   (monicp (pembed p phi k f) k))
  :hints (("Goal" :use ((:functional-instance monicp-phom
                         (hom (lambda (x) (if (and (fieldp e) (fieldp k) (embed-props phi e k f)) (embed x phi k f) (hom x))))
			 (fld1 (lambda () (if (and (fieldp e) (fieldp k) (embed-props phi e k f)) e (fld1))))
			 (fld2 (lambda () (if (and (fieldp e) (fieldp k) (embed-props phi e k f)) k (fld2))))
			 (phom (lambda (p) (if (and (fieldp e) (fieldp k) (embed-props phi e k f)) (pembed p phi k f) (phom p)))))))))

(defthmd len-pembed-*
  (implies (and (fieldp e) (fieldp k) (embed-props phi e k f))
           (equal (len (pembed p phi k f))
	          (len p)))
  :hints (("Goal" :use ((:functional-instance len-phom
                         (hom (lambda (x) (if (and (fieldp e) (fieldp k) (embed-props phi e k f)) (embed x phi k f) (hom x))))
			 (fld1 (lambda () (if (and (fieldp e) (fieldp k) (embed-props phi e k f)) e (fld1))))
			 (fld2 (lambda () (if (and (fieldp e) (fieldp k) (embed-props phi e k f)) k (fld2))))
			 (phom (lambda (p) (if (and (fieldp e) (fieldp k) (embed-props phi e k f)) (pembed p phi k f) (phom p)))))))))

(defthmd pembed-id-*
  (implies (and (fieldp e) (fieldp k) (embed-props phi e k f))
	   (and (equal (pembed (pzero e) phi k f) (pzero k))
	        (equal (pembed (pone e) phi k f) (pone k))))
  :hints (("Goal" :use ((:functional-instance phom-id
                         (hom (lambda (x) (if (and (fieldp e) (fieldp k) (embed-props phi e k f)) (embed x phi k f) (hom x))))
			 (fld1 (lambda () (if (and (fieldp e) (fieldp k) (embed-props phi e k f)) e (fld1))))
			 (fld2 (lambda () (if (and (fieldp e) (fieldp k) (embed-props phi e k f)) k (fld2))))
			 (phom (lambda (p) (if (and (fieldp e) (fieldp k) (embed-props phi e k f)) (pembed p phi k f) (phom p)))))))))

(defthmd pembed-pzero-*
  (implies (and (fieldp e) (fieldp k) (embed-props phi e k f)
                (polyp p e) (not (equal p (pzero e))))
	   (not (equal (pembed p phi k f) (pzero k))))
  :hints (("Goal" :use ((:functional-instance phom-pzero
                         (hom (lambda (x) (if (and (fieldp e) (fieldp k) (embed-props phi e k f)) (embed x phi k f) (hom x))))
			 (fld1 (lambda () (if (and (fieldp e) (fieldp k) (embed-props phi e k f)) e (fld1))))
			 (fld2 (lambda () (if (and (fieldp e) (fieldp k) (embed-props phi e k f)) k (fld2))))
			 (phom (lambda (p) (if (and (fieldp e) (fieldp k) (embed-props phi e k f)) (pembed p phi k f) (phom p)))))))))

(defthmd pembed-padd-*
  (implies (and (fieldp e) (fieldp k) (embed-props phi e k f)
                (polyp p e) (polyp q e))
	   (equal (pembed (padd p q e) phi k f)
	          (padd (pembed p phi k f) (pembed q phi k f) k)))
  :hints (("Goal" :use ((:functional-instance phom-padd
                         (hom (lambda (x) (if (and (fieldp e) (fieldp k) (embed-props phi e k f)) (embed x phi k f) (hom x))))
			 (fld1 (lambda () (if (and (fieldp e) (fieldp k) (embed-props phi e k f)) e (fld1))))
			 (fld2 (lambda () (if (and (fieldp e) (fieldp k) (embed-props phi e k f)) k (fld2))))
			 (phom (lambda (p) (if (and (fieldp e) (fieldp k) (embed-props phi e k f)) (pembed p phi k f) (phom p)))))))))

(defthmd pembed-pmul-*
  (implies (and (fieldp e) (fieldp k) (embed-props phi e k f)
                (polyp p e) (polyp q e))
	   (equal (pembed (pmul p q e) phi k f)
	          (pmul (pembed p phi k f) (pembed q phi k f) k)))
  :hints (("Goal" :use ((:functional-instance phom-pmul
                         (hom (lambda (x) (if (and (fieldp e) (fieldp k) (embed-props phi e k f)) (embed x phi k f) (hom x))))
			 (fld1 (lambda () (if (and (fieldp e) (fieldp k) (embed-props phi e k f)) e (fld1))))
			 (fld2 (lambda () (if (and (fieldp e) (fieldp k) (embed-props phi e k f)) k (fld2))))
			 (phom (lambda (p) (if (and (fieldp e) (fieldp k) (embed-props phi e k f)) (pembed p phi k f) (phom p)))))))))

;;----------------------

;; Base case:

(defthmd embed-prop-1-base
  (implies (and (fieldp f) (extensionp k f) (embeddingp phi f k f))
           (embed-prop-1 phi f k f))
  :hints (("Goal" :in-theory (enable embed embeddingp)
                  :use ((:instance embed-prop-1-witness-lemma (e f))))))

(defthmd embed-prop-2-base
  (implies (and (fieldp f) (extensionp k f) (embeddingp phi f k f))
           (embed-prop-2 phi f k f))
  :hints (("Goal" :in-theory (enable flift embed embeddingp)
                  :use ((:instance embed-prop-2-witness-lemma (e f))))))

(defthmd embed-prop-3-base
  (implies (and (fieldp f) (extensionp k f) (embeddingp phi f k f))
           (embed-prop-3 phi f k f))
  :hints (("Goal" :in-theory (enable embed embeddingp)
                  :Use ((:instance embed-prop-3-witness-lemma (e f))))))

(defthmd embed-prop-4-base
  (implies (and (fieldp f) (extensionp k f) (embeddingp phi f k f))
           (embed-prop-4 phi f k f))
  :hints (("Goal" :in-theory (enable embed embed-prop-4 embeddingp)
                  :use ((:instance flift-id (e k))))))

(defthmd embed-props-base
  (implies (and (fieldp f) (extensionp k f) (embeddingp phi f k f))
           (embed-props phi f k f))
  :hints (("Goal" :in-theory (enable embed-props embed-prop-1-base embed-prop-2-base
                                     embed-prop-3-base embed-prop-4-base))))

;;-----------------------------------------------------------

;; Inductive case:

;; Let e' = (cdr e) and phi' = (cdr phi).  We must prove that if the properties hold for
;; e' and phi', then they hold for e and phi.

(local-defthmd embed-props-induct-1
  (implies (and (extensionp e f) (extensionp k f) (not (equal e f)) (embeddingp phi e k f)
                (embed-props (cdr phi) (cdr e) k f)
		(feltsp x (cdr e)))
	   (let ((y (pembed x (cdr phi) k f)))
	     (and (feltsp y k)
	          (equal (len y) (len x))
	          (or (null x) (equal (car y) (embed (car x) (cdr phi) k f))))))
  :hints (("Goal" :induct (len x))
          ("Subgoal *1/1" :expand ((pembed x (cdr phi) k f)))))

(local-defthmd embed-props-induct-2
  (implies (and (extensionp e f) (extensionp k f) (not (equal e f)) (embeddingp phi e k f)
                (embed-props (cdr phi) (cdr e) k f)
		(feltp x e))
	   (polyp (pembed x (cdr phi) k f) k))
  :hints (("Goal" :in-theory (enable embeddingp feltp polyp)
                  :use (embed-props-induct-1
		        (:instance embed-fzero-* (x (car x)) (e (cdr e)) (phi (cdr phi)))))))

(defthmd embed-image-*
  (implies (and (extensionp e f) (extensionp k f) (not (equal e f)) (embeddingp phi e k f)
                (embed-props (cdr phi) (cdr e) k f)
		(feltp x e))
	   (feltp (embed x phi k f) k))
  :hints (("Goal" :in-theory (enable embed feltp prootp embeddingp)
                  :use (embed-props-induct-2))))

; (:instance feltp-peval (p (pembed x (cdr phi) k f)) (x (car phi)) (f k))))))

(defthmd embed-fzero-fone-*
  (implies (and (extensionp e f) (extensionp k f) (not (equal e f)) (embeddingp phi e k f)
                (embed-props (cdr phi) (cdr e) k f))
	   (and (equal (embed (fzero e) phi k f) (fzero k))
	        (equal (embed (fone e) phi k f) (fone k))))
  :hints (("Goal" :in-theory (enable fzero fone pconstp embed embeddingp)
                  :expand (embed x phi k f))))

(local-defthmd embed-fixes-*-1
  (implies (and (extensionp e f) (extensionp k f) (not (equal e f)) (embeddingp phi e k f)
                (embed-props (cdr phi) (cdr e) k f)
		(feltp x f))
           (equal (flift x f e)
	          (list (flift x f (cdr e)))))
  :hints (("Goal" :in-theory (enable flift)
                  :use ((:instance len-extends (e (cdr e)))))))

(local-defthmd embed-fixes-*-2
  (implies (and (extensionp e f) (extensionp k f) (not (equal e f)) (embeddingp phi e k f)
                (embed-props (cdr phi) (cdr e) k f)
		(feltp x f))
           (equal (pembed (list (flift x f (cdr e))) (cdr phi) k f)
	          (list (flift x f k))))
  :hints (("Goal" :expand ((:free (x) (pembed x (cdr phi) k f))))))

(local-defthmd embed-fixes-*-3
  (implies (and (extensionp e f) (extensionp k f) (not (equal e f)) (embeddingp phi e k f)
                (embed-props (cdr phi) (cdr e) k f)
		(feltp x f))
           (equal (peval (list (flift x f k)) (car phi) k)
	          (flift x f k)))
  :hints (("Goal" :in-theory (enable polyp pconstp embeddingp)
                  :use ((:instance peval-pconstp (p (list (flift x f k))) (x (car phi)) (f k))))))

(defthmd embed-fixes-*
  (implies (and (extensionp e f) (extensionp k f) (not (equal e f)) (embeddingp phi e k f)
                (embed-props (cdr phi) (cdr e) k f)
		(feltp x f))
	   (equal (embed (flift x f e) phi k f)
	          (flift x f k)))
  :hints (("Goal" :in-theory (enable embed embeddingp)
                  :use (embed-fixes-*-1 embed-fixes-*-2 embed-fixes-*-3))))


;; Proof:
	   
;;   (flift x f e) = (fliftn x (- (len e) (len f))))             [definition of flift]
;;                 = (list (fliftn x (1- (- (len e) (len f)))))  [definition of fliftn]
;;                 = (list (fliftn x (- (len e') (len f))))
;;                 = (list (flift x f e'))                       [definition of flift]
	      
;;   (pembed (flift x f e) phi' k f) = (pembed (list (flift x f e')) phi' k f)
;;                                   = (list (embed (flift x f e')) phi' k f)   [definition of pembed]
;;                                   = (list (flift x f k))                     [induction]

;;   (embed (flift x f e) phi k f) = (peval (list (flift x f k)) (car phi) k)   [definition of embed]
;;                                 = (flift x f k)                              [peval-pconstp]

(defthmd peval-pembed-prem
  (implies (and (extensionp e f) (extensionp k f) (embed-props phi e k f)
                (polyp x e) (polyp y e) (not (equal y (pzero e)))
		(feltp a k) (prootp a (pembed y phi k f) k))
	   (equal (peval (pembed x phi k f) a k)
	          (peval (pembed (prem x y e) phi k f) a k)))
  :hints (("Goal" :in-theory (enable prootp polyp-pembed-*)
                  :use ((:instance pquot-prem (f e))
                        (:instance polyp-pquot-prem (f e))
			(:instance pembed-padd-* (p (pmul y (pquot x y e) e)) (q (prem x y e)))
			(:instance pembed-pmul-* (p y) (q (pquot x y e)))
			(:instance peval-padd (p (pmul (pembed y phi k f) (pembed (pquot x y e) phi k f) k))
			                      (q (pembed (prem x y e) phi k f))
					      (x a) (f k))
			(:instance peval-pmul (p (pembed y phi k f)) (q (pembed (pquot x y e) phi k f)) (x a) (f k))))))

;; Proof: Let q = (pquot x y e) and r = (prem x y e).

;;   (peval (pembed x phi k f) a k) = (peval (pembed (padd (pmul y q e) r e)        [pquot-prem]
;;                                                   phi k f)
;;                                           a k)                             
;;                                  = (peval (padd (pembed (pmul y q e) phi k f)    [pembed-padd-*]                            
;;                                                 (pembed r phi k f)                             
;;                                                 k)                             
;;                                           a k)                             
;;                                  = (peval (padd (pmul (pembed y phi k f)         [pembed-pmul-*]
;;                                                       (pembed q phi k f)
;;                                                       k)
;;                                                 (pembed r phi k f)
;;                                                 k)
;;                                           a k)
;;                                  = (fadd (peval (pmul (pembed y phi k f)         [peval-padd]
;;                                                       (pembed q phi k f)
;;                                                       e)
;;                                                 a k)
;;                                          (peval (pembed r phi k f) a k)
;;                                          k)
;;                                  = (fadd (fmul (peval (pembed y phi k f) a k)    [peval-pmul]
;;                                                (peval (pembed q phi k f) a k)
;;                                                k)
;;                                          (peval (pembed r phi k f) a k)
;;                                          k)
;;                                  = (fadd (fmul (fzero k)                         [hypothesis]
;;                                                (peval (pembed q phi k f) a k)
;;                                                k)
;;                                          (peval (pembed r phi k f) a k)
;;                                          k)
;;                                  = (peval (pembed r phi k f) a k)

(local-defthmd embed-fadd-fmul-*-1
  (implies (and (extensionp e f) (extensionp k f) (not (equal e f)) (embed-props (cdr phi) (cdr e) k f)
                (embed-props (cdr phi) (cdr e) k f)
                (feltp x e) (feltp y e))
           (equal (pembed (fadd x y e) (cdr phi) k f)
	          (padd (pembed x (cdr phi) k f) (pembed y (cdr phi) k f) k)))
  :hints (("Goal" :in-theory (enable feltp fadd)
                  :use ((:instance pembed-padd-* (p x) (q y) (phi (cdr phi)) (e (cdr e)))))))

(local-defthmd embed-fadd-fmul-*-2
  (implies (and (extensionp e f) (extensionp k f) (not (equal e f)) (embeddingp phi e k f) (embed-props (cdr phi) (cdr e) k f)
                (embed-props (cdr phi) (cdr e) k f)
                (feltp x e) (feltp y e))
           (equal (embed (fadd x y e) phi k f)
                  (fadd (embed x phi k f) (embed y phi k f) k)))
  :hints (("Goal" :in-theory (enable fieldp feltp embeddingp prootp polyp-pembed-* embed)
                  :use (embed-fadd-fmul-*-1
		        (:instance peval-padd (p (pembed x (cdr phi) k f)) (q (pembed y (cdr phi) k f))
			                      (x (car phi)) (f k))))))

(local-defthmd embed-fadd-fmul-*-3
  (implies (and (extensionp e f) (extensionp k f) (not (equal e f)) (embeddingp phi e k f) (embed-props (cdr phi) (cdr e) k f)
                (embed-props (cdr phi) (cdr e) k f)
                (feltp x e) (feltp y e))
           (equal (embed (fmul x y e) phi k f)
                  (fmul (embed x phi k f) (embed y phi k f) k)))
  :hints (("Goal" :in-theory (enable feltp fieldp polyp-pembed-* prootp embeddingp fmul embed)
                  :use ((:instance peval-pembed-prem (e (cdr e)) (phi (cdr phi)) (x (pmul x y (cdr e))) (y (car e)) (a (car phi)))
		        (:instance pembed-pmul-* (p x) (q y) (phi (cdr phi)) (e (cdr e)))
			(:instance peval-pmul (p (pembed x (cdr phi) k f)) (q (pembed y (cdr phi) k f))
			                      (x (car phi)) (f k))))))

(defthmd embed-fadd-fmul-*
  (implies (and (extensionp e f) (extensionp k f) (not (equal e f))
                (embeddingp phi e k f) (embed-props (cdr phi) (cdr e) k f)
                (feltp x e) (feltp y e))
           (and (equal (embed (fadd x y e) phi k f)
                       (fadd (embed x phi k f) (embed y phi k f) k))
                (equal (embed (fmul x y e) phi k f)
                       (fmul (embed x phi k f) (embed y phi k f) k))))
  :hints (("Goal" :use (embed-fadd-fmul-*-2 embed-fadd-fmul-*-3))))

;; Proof:

;;   (pembed (fadd x y e) phi k f) = (pembed (padd x y e') phi k f)                      [definition of fadd]
;;                                   (padd (pembed x phi k f) (pembed y phi k f) k)      [pembed-padd-*]
;; 
;;   (embed (fadd x y e) phi k f) = (peval (pembed (fadd x y e) phi' k f) (car phi) k)   [definition of embed]
;;                                = (peval (padd (pembed x phi k f)                      [proved above]   
;;                                               (pembed y phi k f)
;;                                               k)
;;                                         (car phi) k)
;;                                = (fadd (peval (pembed x phi' k f) (car phi) k)        [peval-padd, polyp-pembed-*]
;;                                        (peval (pembed y phi' k f) (car phi) k)
;;                                        k)
;;                                = (fadd (embed x phi k f) (embed y phi k f) k)         [definition of embed]

;; For the second equation, we invoke peval-pembed-prem with e <- e', phi <- phi',
;; x <- (pmul x y e'), y <- (car e), and a <- (car phi):

;;   (embed (fmul x y e) phi k f) = (peval (pembed (fmul x y e) phi k f) (car phi) k)    [definition of embed]
;;                                = (peval (pembed (prem (pmul x y e') (car e) e')       [definition of fmul]
;;                                                 phi' k f)
;;                                         (car phi) k)
;;                                = (peval (pembed (pmul x y e') phi' k f) (car phi) k)  [peval-pembed-prem]
;;                                = (peval (pmul (pembed x phi' k f)                     [pembed-pmul-*]
;;                                               (pembed y phi' k f)
;;                                               k)
;;                                         (car phi) k)
;;                                = (fmul (peval (pembed x phi' k f) (car phi) k)        [peval-pmul, polyp-pembed-*]
;;                                        (peval (pembed y phi' k f) (car phi) k)
;;                                        k)
;;                                = (fmul (embed x phi k f)                              [definition of embed]
;;                                        (embed y phi k f)
;;                                        y)

(defthmd embed-props-induct
  (implies (and (extensionp e f) (extensionp k f) (not (equal e f))
                (embeddingp phi e k f) (embed-props (cdr phi) (cdr e) k f))
           (embed-props phi e k f))
  :hints (("Goal" :in-theory (enable embed-prop-4 embed-fzero-fone-* embed-fadd-fmul-*)
                  :use (embed-props embed-prop-1-witness-lemma embed-prop-2-witness-lemma embed-prop-3-witness-lemma
		        (:instance embed-image-* (x (embed-prop-1-witness phi e k f)))
		        (:instance embed-fixes-* (x (embed-prop-2-witness phi e k f)))))))

(in-theory (enable embeddingp))

;; Now apply induction:

(defthm embed-props-lemma
  (implies (and (extensionp e f) (extensionp k f)
                (embeddingp phi e k f))
           (embed-props phi e k f))
  :hints (("Goal" :induct (embeddingp phi e k f))
          ("Subgoal *1/2" :use (embed-props-induct))
          ("Subgoal *1/1" :use (embed-props-base))))

;; The required properties follow:
                        
(defthm embed-image
  (implies (and (embeddingp phi e k f) (extensionp e f) (extensionp k f) 
                (feltp x e))
           (feltp (embed x phi k f) k))
  :hints (("Goal" :use (embed-prop-1-lemma))))

(defthm embed-fixes
  (implies (and (extensionp e f) (extensionp k f) (embeddingp phi e k f)
                (feltp x f))
           (equal (embed (flift x f e) phi k f)
                  (flift x f k)))
  :hints (("Goal" :use (embed-prop-2-lemma))))

(defthm embed-fadd
  (implies (and (extensionp e f) (extensionp k f) (embeddingp phi e k f)
                (feltp x e) (feltp y e))
           (equal (embed (fadd x y e) phi k f)
                  (fadd (embed x phi k f) (embed y phi k f) k)))
  :hints (("Goal" :use (embed-prop-3-lemma))))

(defthm embed-fmul
  (implies (and (extensionp e f) (extensionp k f) (embeddingp phi e k f)
                (feltp x e) (feltp y e))
           (equal (embed (fmul x y e) phi k f)
                  (fmul (embed x phi k f) (embed y phi k f) k)))
  :hints (("Goal" :use (embed-prop-3-lemma))))

(defthmd embed-fzero-fone
  (implies (and (extensionp e f) (extensionp k f) (embeddingp phi e k f))
           (and (equal (embed (fzero e) phi k f) (fzero k))
                (equal (embed (fone e) phi k f) (fone k)))))

;; The derived properties of hom and phom follow by functional instantiation:

(defthmd embed-fneg
  (implies (and (extensionp e f) (extensionp k f) (embeddingp phi e k f)
                (feltp x e))
	   (equal (embed (fneg x e) phi k f)
	          (fneg (embed x phi k f) k)))
  :hints (("Goal" :use ((:functional-instance hom-fneg
                         (hom (lambda (x) (if (and (fieldp e) (fieldp k) (embed-props phi e k f)) (embed x phi k f) (hom x))))
			 (fld1 (lambda () (if (and (fieldp e) (fieldp k) (embed-props phi e k f)) e (fld1))))
			 (fld2 (lambda () (if (and (fieldp e) (fieldp k) (embed-props phi e k f)) k (fld2)))))))))

(defthmd embed-frecip
  (implies (and (extensionp e f) (extensionp k f) (embeddingp phi e k f)
                (feltp x e) (not (equal x (fzero e))))
	   (equal (embed (frecip x e) phi k f)
	          (frecip (embed x phi k f) k)))
  :hints (("Goal" :use ((:functional-instance hom-frecip
                         (hom (lambda (x) (if (and (fieldp e) (fieldp k) (embed-props phi e k f)) (embed x phi k f) (hom x))))
			 (fld1 (lambda () (if (and (fieldp e) (fieldp k) (embed-props phi e k f)) e (fld1))))
			 (fld2 (lambda () (if (and (fieldp e) (fieldp k) (embed-props phi e k f)) k (fld2)))))))))

(defthmd embed-fzero
  (implies (and (extensionp e f) (extensionp k f) (embeddingp phi e k f)
                (feltp x e) (equal (embed x phi k f) (fzero k)))
	   (equal (fzero e) x))
  :hints (("Goal" :use (embed-fzero-*))))

(defthm embedding-1-1
  (implies (and (extensionp e f) (extensionp k f) (embeddingp phi e k f)
                (feltp x e) (feltp y e)
		(equal (embed x phi k f) (embed y phi k f)))
           (equal x y))
  :rule-classes ()
  :hints (("Goal" :use ((:functional-instance hom-1-1
                         (hom (lambda (x) (if (and (fieldp e) (fieldp k) (embed-props phi e k f)) (embed x phi k f) (hom x))))
			 (fld1 (lambda () (if (and (fieldp e) (fieldp k) (embed-props phi e k f)) e (fld1))))
			 (fld2 (lambda () (if (and (fieldp e) (fieldp k) (embed-props phi e k f)) k (fld2)))))))))

(defthmd polyp-pembed
  (implies (and (extensionp e f) (extensionp k f) (embeddingp phi e k f)
                (polyp p e))
	   (polyp (pembed p phi k f) k))
  :hints (("Goal" :use (polyp-pembed-*))))

(defthmd monicp-pembed
  (implies (and (extensionp e f) (extensionp k f) (embeddingp phi e k f)
                (polyp p e) (monicp p e))
	   (monicp (pembed p phi k f) k))
  :hints (("Goal" :use (monicp-pembed-*))))

(defthm len-pembed
  (equal (len (pembed p phi k f))
	 (len p)))

(defthmd pembed-id
  (implies (and (extensionp e f) (extensionp k f) (embeddingp phi e k f))
	   (and (equal (pembed (pzero e) phi k f) (pzero k))
	        (equal (pembed (pone e) phi k f) (pone k))))
  :hints (("Goal" :use (pembed-id-*))))

(defthmd pembed-pzero
  (implies (and (extensionp e f) (extensionp k f) (embeddingp phi e k f)
                (polyp p e) (not (equal p (pzero e))))
	   (not (equal (pembed p phi k f) (pzero k))))
  :hints (("Goal" :use (pembed-pzero-*))))

(defthmd pembed-padd
  (implies (and (extensionp e f) (extensionp k f) (embeddingp phi e k f)
                (polyp p e) (polyp q e))
	   (equal (pembed (padd p q e) phi k f)
	          (padd (pembed p phi k f) (pembed q phi k f) k)))
  :hints (("Goal" :use (pembed-padd-*))))

(defthmd pembed-pmul
  (implies (and (extensionp e f) (extensionp k f) (embeddingp phi e k f)
                (polyp p e) (polyp q e))
	   (equal (pembed (pmul p q e) phi k f)
	          (pmul (pembed p phi k f) (pembed q phi k f) k)))
  :hints (("Goal" :use (pembed-pmul-*))))

(defthmd peval-pembed
  (implies (and (extensionp e f) (extensionp k f) (embeddingp phi e k f)
                (feltp x e) (polyp p e))
	   (equal (peval (pembed p phi k f) (embed x phi k f) k)
	          (embed (peval p x e) phi k f)))
  :hints (("Goal" :use ((:functional-instance hom-peval
                         (hom (lambda (x) (if (and (fieldp e) (fieldp k) (embed-props phi e k f)) (embed x phi k f) (hom x))))
			 (fld1 (lambda () (if (and (fieldp e) (fieldp k) (embed-props phi e k f)) e (fld1))))
			 (fld2 (lambda () (if (and (fieldp e) (fieldp k) (embed-props phi e k f)) k (fld2))))
			 (phom (lambda (p) (if (and (fieldp e) (fieldp k) (embed-props phi e k f)) (pembed p phi k f) (phom p)))))))))

;; We also have the following consequence of embed-fixes:

(local-defthmd pembed-fixes-1
  (implies (and (extensionp e f) (extensionp k f) (embeddingp phi e k f)
                (feltsp p f))
           (equal (pembed (plift p f e) phi k f)
                  (plift p f k))));

(defthmd pembed-fixes
  (implies (and (extensionp e f) (extensionp k f) (embeddingp phi e k f)
                (polyp p f))
           (equal (pembed (plift p f e) phi k f)
                  (plift p f k)))
  :hints (("Goal" :use (pembed-fixes-1))))


; Embedding commutes with lifting in the following sense:

(defthm embed-flift
  (implies (and (extensionp e f) (extensionp k f) (not (equal e f))
                (embeddingp phi e k f) (feltp x (cdr e)))
	   (equal (embed (flift x (cdr e) e) phi k f)
	          (embed x (cdr phi) k f)))
  :hints (("Goal" :in-theory (enable pconstp embed flift)
                  :use ((:instance peval-pconstp (p (list (embed x (cdr phi) k f))) (x (car e)) (f k)))
                  :expand ((pembed (list x) (cdr phi) k f) (fliftn x 1)))))

;; Proof: Let e' = (cdr e) and phi' = (cdr phi).

;;   (embed (flift x e' e) phi k f) = (embed (list x) phi k f)
;;                                  = (peval (pembed (list x) phi' k f) (car e) k)
;; 				    = (peval (list (embed x phi' k f)) (car e) k)
;; 				    = (embed x phi' k f)

(local-defthmd pembed-plift-1
  (implies (and (extensionp e f) (extensionp k f) (not (equal e f))
                (embeddingp phi e k f) (feltsp p (cdr e)))
	   (equal (pembed (plift p (cdr e) e) phi k f)
	          (pembed p (cdr phi) k f)))
  :hints (("Goal" :induct (len p))))

(defthmd pembed-plift
  (implies (and (extensionp e f) (extensionp k f) (not (equal e f))
                (embeddingp phi e k f) (polyp p (cdr e)))
	   (equal (pembed (plift p (cdr e) e) phi k f)
	          (pembed p (cdr phi) k f)))
  :hints (("Goal" :use (pembed-plift-1))))

;; If e != f, there is no embedding of e in f over f.  First suppose e is a simple extension of f.
;; If phi is an embedding of e in f over f, then (prootp (car phi) (pembed (car e) () f f) f), where
;; (pembed (car e) () f f) = (car e), contradicting irreduciblep-no-root.  The general case follows by
;; induction:

(local-defthmd pembed-nil
  (implies (and (fieldp f) (feltsp p f))
           (equal (pembed p () f f) p))
  :hints (("Goal" :induct (len p))
          ("Subgoal *1/1" :expand ((pembed p () f f) (EMBED (CAR P) NIL F F)))))

(local-defthmd no-embedding-in-f-1
  (implies (and (extensionp e f) (not (equal e f)) (embeddingp phi e f f))
           (and (feltp (car phi) f)
	        (prootp (car phi) (pembed (car e) (cdr phi) f f) f)))
  :hints (("Goal" :in-theory (enable prootp) :expand (embeddingp phi e f f))))

(local-defthmd no-embedding-in-f-2
  (implies (and (extensionp e f) (not (equal e f)) (equal (cdr e) f)(embeddingp phi e f f))
           (and (polyp (car e) f)
	        (irreduciblep (car e) f)
		(monicp (car e) f)
		(>= (degree (car e)) 2)
	        (prootp (car phi) (car e) f)))
  :hints (("Goal" :expand ((fieldp e))
                  :use (no-embedding-in-f-1
                        (:instance pembed-nil (p (car e)))))))

(local-defthmd no-embedding-in-f-3
  (implies (and (extensionp e f) (not (equal e f)) (equal (cdr e) f))
           (not (embeddingp phi e f f)))
  :hints (("Goal" :in-theory (enable prootp)
		  :use (no-embedding-in-f-2
                        (:instance irreduciblep-no-root (p (car e)) (x (car phi)))))))

(defun no-embedding-induct (e phi)
  (declare (irrelevant phi))
  (if (consp e)
      (no-embedding-induct (cdr e) (cdr phi))
    ()))

(defthmd no-embedding-in-f
  (implies (and (extensionp e f) (not (equal e f)))
           (not (embeddingp phi e f f)))
  :hints (("Goal" :induct (no-embedding-induct e phi))  
          ("Subgoal *1/1" :use ((:instance no-embedding-in-f-3)))))

;; The car of an embedding phi of an extension field e is the image under phi of (primitive e).
;; Thus an embedding is constructed by specifying the image of the primitive element of each of the
;; simple extensions that compose the extension:

(defthmd embed-primitive
  (implies (and (extensionp e f) (extensionp k f) (not (equal e f))
                (embeddingp phi e k f))
           (equal (embed (primitive e) phi k f)
	          (car phi)))
  :hints (("Goal" :in-theory (enable embeddingp prootp embed primitive pid)
                  :use ((:instance embed-fzero-fone (phi (cdr phi)) (e (cdr e)))
		        (:instance peval-pid (x (car phi)) (f k))))))

;; Proof:

;; (embed (primitive e) phi k f)
;;   = (peval (pembed (primitive e) (cdr phi) k f) (car phi) k)  [def of embed]
;;   = (peval (pembed (pid (cdr e)) (cdr phi) k f) (car phi) k)  [def of primitive]
;;   = (peval (pid k) (car phi) k)                               [defs of pid and pembed, fembed-id]
;;   = (car phi)                                                 [peval-pid]

;; Let phi and psi be embeddings of e in k over f.  If (embed x phi k f) = (embed x psi k f) for all
;; x in e, then phi = psi:

(defun embed-cex (phi psi e f)
  (if (and (extensionp e f) (not (equal e f)) (consp phi))
      (if (equal (car phi) (car psi))
          (flift (embed-cex (cdr phi) (cdr psi) (cdr e) f) (cdr e) e)
        (primitive e))
    ()))

(local-defun embed-cex-induct (phi psi e)
  (declare (irrelevant psi e))
  (if (consp phi)
      (embed-cex-induct (cdr phi) (cdr psi) (cdr e))
    ()))
    
(defthmd embed-cex-lemma
  (implies (and (extensionp e f) (extensionp k f)
                (embeddingp phi e k f) (embeddingp psi e k f)
		(not (equal phi psi)))
	   (let ((x (embed-cex phi psi e f)))
	     (and (feltp x e)
	          (not (equal (embed x phi k f) (embed x psi k f))))))
  :hints (("Goal" :induct (embed-cex-induct phi psi e))
          ("Subgoal *1/1" :use (embed-primitive (:instance embed-primitive (phi psi))))))


;;------------------------------------------------

;; The following encapsulation introduces 2 arbitrary extensions, (e0) and (k0), of a field (b0) and a
;; function phi0 that satisfies each of the essential properties of an embedding of (e0) in (k0) over
;; (b0).  Such a function might be termed a "meta-embedding" of (e0) in (k0) over (b0).  Our objective
;; is to define an embedding phi1 of (e0) in (k0) over (b0) that reifies phi0, i.e., with the property
;; that

;;     (feltp x (e0)) => (embed x (phi1) (k0) (b0)) = (phi0 x).

;; Subsequently, given any such meta-embedding, we can construct the corresponding embedding by 
;; functional instantiation.  Thus, in a real sense, for any extensions e and k of a field f, the 
;; embeddings of e in k over f are the only homomorphisms of e into k that fix f.
;; [Note: I wanted to call the base field f0, but it seems we already have a function with that name.]

(encapsulate (((b0) => *) ((e0) => *) ((k0) => *) ((phi0 *) => *))
  (local (defun b0 () 0))
  (local (defun e0 () 0))
  (local (defun k0 () 0))
  (local (defun phi0 (x) x))
  (defthmd extensionp-e0-k0-b0
    (and (extensionp (e0) (b0)) (extensionp (k0) (b0))))
  (defthm phi0-image
    (implies (feltp x (e0)) (feltp (phi0 x) (k0))))
  (defthm phi0-fzero-fone
    (and (equal (phi0 (fzero (e0))) (fzero (k0)))
         (equal (phi0 (fone (e0))) (fone (k0)))))
  (defthm phi0-fadd
    (implies (and (feltp x (e0)) (feltp y (e0)))
	     (equal (phi0 (fadd x y (e0)))
		    (fadd (phi0 x) (phi0 y) (k0)))))
  (defthm phi0-fmul
    (implies (and (feltp x (e0)) (feltp y (e0)))
	     (equal (phi0 (fmul x y (e0)))
		    (fmul (phi0 x) (phi0 y) (k0)))))
  (defthm phi0-fixes
    (implies (feltp x (b0)) (equal (phi0 (flift x (b0) (e0))) (flift x (b0) (k0))))))

(local-defthm e0-k0-b0
  (and (fieldp (e0))
       (fieldp (k0))
       (fieldp (b0))
       (extends (e0) (b0))
       (extends (k0) (b0)))
  :hints (("Goal" :use (extensionp-e0-k0-b0))))

;; phi1 is defined as follows:

(defun phi1-aux (d)
  (if (and (extensionp (e0) d) (extensionp d (b0)) (not (equal d (b0))))
      (cons (phi0 (flift (primitive d) d (e0)))
            (phi1-aux (cdr d)))
    ()))

(defund phi1 () (phi1-aux (e0)))

;; We shall show that the following property holds whenever d is an intermediate field between b0 and e0:

(defun-sk phi1-aux-phi0 (d)
  (forall (x)
    (implies (feltp x d)
             (equal (embed x (phi1-aux d) (k0) (b0))
	            (phi0 (flift x d (e0)))))))

(defthm phi1-aux-phi0-lemma
  (implies (and (phi1-aux-phi0 d) (feltp x d))
           (equal (embed x (phi1-aux d) (k0) (b0))
	          (phi0 (flift x d (e0)))))
  :hints (("Goal" :use (phi1-aux-phi0-necc))))

(defthmd phi1-aux-phi0-witness-lemma
  (let ((x (phi1-aux-phi0-witness d)))
    (implies (implies (feltp x d)
                      (equal (embed x (phi1-aux d) (k0) (b0))
	                     (phi0 (flift x d (e0)))))
	     (phi1-aux-phi0 d))))

(in-theory (disable phi1-aux-phi0))

;; The desired result:

;; (defthmd phi1-aux-lemma
;;   (implies (and (extensionp d (b0)) (extensionp (e0) d))
;; 	      (and (embeddingp (phi1-aux d) d (k0) (b0))
;; 	           (phi1-aux-phi0 d))))

;; The case d = (b0) is trivial:

(defthmd phi1-aux-base
  (and (embeddingp (phi1-aux (b0)) (b0) (k0) (b0))
       (phi1-aux-phi0 (b0)))
  :hints (("Goal" :in-theory (enable embed embeddingp)
                  :use ((:instance phi1-aux-phi0-witness-lemma (d (b0)))))))

;; Assume d != (b0) and that the lemma holds for d' = (cdr d).
;; Let phi = (phi1-aux d) and phi' = (cdr phi) = (phi1-aux d').  We must show that it also holds for d.
;; Note that (car phi) = (phi0 (flift (primitive d) d (e0))).  Clearly, (feltp (car phi) (k0)).
;; To show (embeddingp phi d (k0) (b0)), we must show

;;   (prootp (car phi) (pembed (car d) (cdr phi' (k0) (b0)) (k0)),

;; i.e,

;;   (peval (pembed (car d) phi' (k0) (b0))
;;          (phi0 (flift (primitive d) d (e0))) (k0))
;;     = (fzero (k0)).

;; We define

(defun pphi0 (p)
  (if (consp p)
      (cons (phi0 (car p))
            (pphi0 (cdr p)))
    ()))

;; Then

(local-defthmd pembed-pphi0-1
  (implies (and (extensionp d (b0)) (extensionp (e0) d) (phi1-aux-phi0 d)
                (feltsp p d))
           (equal (pembed p (phi1-aux d) (k0) (b0))
                  (pphi0 (plift p d (e0))))))

(defthmd pembed-pphi0
  (implies (and (extensionp d (b0)) (extensionp (e0) d) (phi1-aux-phi0 d)
                (polyp p d))
           (equal (pembed p (phi1-aux d) (k0) (b0))
                  (pphi0 (plift p d (e0)))))
  :hints (("Goal" :use (pembed-pphi0-1))))

;; By functional instantiation of hom-peval,

(defthmd phi0-peval
  (implies (and (polyp p (e0)) (feltp x (e0)))
           (equal (phi0 (peval p x (e0)))
                  (peval (pphi0 p) (phi0 x) (k0))))
  :hints (("Goal" :use ((:functional-instance hom-peval (hom phi0) (fld1 e0) (fld2 k0) (phom pphi0))))))
 
;;   (peval (pembed (car d) phi' (k0) (b0))
;;          (phi0 (flift (primitive d) d (e0))) (k0))
;;     = (peval (pphi0 (plift (car d) d' (e0)))            [pembed-pphi0]
;;              (phi0 (flift (primitive d) d (e0))) (k0))
;;     = (phi0 (peval (plift (car d) d' (e0))              [phi0-peval]
;;                    (flift (primitive d) d (e0))
;;                    (e0)))
;;     = (phi0 (peval (plift (plift (car d) d' d) d (e0))  [plift-comp]
;;                    (flift (primitive d) d (e0))
;;                    (e0)))
;;     = (phi0 (flift (peval (plift (car d) d' d)          [flift-peval]
;;                    (primitive d) d)
;;                    d (e0)))
;;     = (phi0 (flift (prem (car d) (car d) (cdr d))       [peval-primitive] 
;;                    d (e0)))
;;     = (phi0 (flift (fzero d) d (e0)))                   [prem-self]
;;     = (phi0 (fzero (e0)))
;;     = (fzero (k0))

;; Thus, we have

(defthmd extends-trans
  (implies (and (extends e d) (extends d f))
           (extends e f)))

(local-defthmd encodingp-phi1-aux-1
  (implies (and (extensionp d (b0)) (extensionp (e0) d) (not (equal d (b0)))
                (embeddingp (phi1-aux (cdr d)) (cdr d) (k0) (b0))
                (phi1-aux-phi0 (cdr d)))
           (polyp (plift (car d) (cdr d) (e0)) (e0)))
  :hints (("Goal" :expand ((fieldp d))
                  :use (extensionp-e0-k0-b0
		        (:instance extends-trans (e (e0)) (f (cdr d)))
		        (:instance polyp-plift (p (car d)) (f (cdr d)) (e (e0)))))))

(local-defthmd encodingp-phi1-aux-2
  (implies (and (extensionp d (b0)) (extensionp (e0) d) (not (equal d (b0))))
           (extends (e0) (cdr d)))
  :hints (("Goal" :use ((:instance extends-trans (e (e0)) (f (cdr d)))))))

(local-in-theory (enable polyp-plift))

(local-defthmd encodingp-phi1-aux-3
  (implies (and (extensionp d (b0)) (extensionp (e0) d) (not (equal d (b0)))
                (embeddingp (phi1-aux (cdr d)) (cdr d) (k0) (b0))
                (phi1-aux-phi0 (cdr d)))
           (equal (peval (pembed (car d) (cdr (phi1-aux d)) (k0) (b0))
                         (phi0 (flift (primitive d) d (e0)))
                         (k0))
	          (phi0 (peval (plift (plift (car d) (cdr d) d) d (e0))
                               (flift (primitive d) d (e0))
                               (e0)))))
  :hints (("Goal" :expand ((fieldp d))
                  :use (encodingp-phi1-aux-1 encodingp-phi1-aux-2 encodingp-phi1-aux-1 extensionp-e0-k0-b0
		        (:instance plift-comp (x (car d)) (e (e0)) (f (cdr d)))
		        (:instance extends-trans (e (e0)) (f (cdr d)))
		        (:instance pembed-pphi0 (d (cdr d)) (p (car d)))
                        (:instance phi0-peval (x (flift (primitive d) d (e0)))
			                      (p (plift (car d) (cdr d) (e0))))))))

(local-defthmd encodingp-phi1-aux-4
  (implies (and (extensionp d (b0)) (extensionp (e0) d) (not (equal d (b0)))
                (embeddingp (phi1-aux (cdr d)) (cdr d) (k0) (b0))
                (phi1-aux-phi0 (cdr d)))
           (equal (peval (plift (plift (car d) (cdr d) d) d (e0))
                         (flift (primitive d) d (e0))
                         (e0))
		  (flift (peval (plift (car d) (cdr d) d) (primitive d) d)
                         d (e0))))
  :hints (("Goal" :expand ((fieldp d))
                  :use ((:instance flift-peval (p (plift (car d) (cdr d) d)) (f d) (e (e0)) (x (primitive d)))))))

(local-defthmd encodingp-phi1-aux-5
  (implies (and (extensionp d (b0)) (extensionp (e0) d) (not (equal d (b0)))
                (embeddingp (phi1-aux (cdr d)) (cdr d) (k0) (b0))
                (phi1-aux-phi0 (cdr d)))
           (equal (peval (plift (car d) (cdr d) d) (primitive d) d)
		  (fzero d)))
  :hints (("Goal" :expand ((fieldp d) (fzero d) (pzero (cdr d)))
                  :use ((:instance peval-primitive (p (car d)) (f d))
		        (:instance prem-self (x (car d)) (f (cdr d)))))))

(local-defthmd encodingp-phi1-aux-6
  (implies (and (extensionp d (b0)) (extensionp (e0) d) (not (equal d (b0)))
                (embeddingp (phi1-aux (cdr d)) (cdr d) (k0) (b0))
                (phi1-aux-phi0 (cdr d)))
           (equal (phi0 (flift (fzero d) d (e0)))
	          (fzero (k0))))
  :hints (("Goal" :use ((:instance flift-id (f d) (e (e0)))))))

(local-defthmd encodingp-phi1-aux-7
  (implies (and (extensionp d (b0)) (extensionp (e0) d) (not (equal d (b0)))
                (embeddingp (phi1-aux (cdr d)) (cdr d) (k0) (b0))
                (phi1-aux-phi0 (cdr d)))
           (equal (peval (pembed (car d) (cdr (phi1-aux d)) (k0) (b0))
                         (phi0 (flift (primitive d) d (e0)))
                         (k0))
	          (fzero (k0))))
  :hints (("Goal" :in-theory (theory 'minimal-theory)
                  :use (encodingp-phi1-aux-3 encodingp-phi1-aux-4 encodingp-phi1-aux-5 encodingp-phi1-aux-6))))

(local-defthmd encodingp-phi1-aux-8
  (implies (and (extensionp d (b0)) (extensionp (e0) d) (not (equal d (b0)))
                (embeddingp (phi1-aux (cdr d)) (cdr d) (k0) (b0))
                (phi1-aux-phi0 (cdr d)))
           (prootp (car (phi1-aux d))
	           (pembed (car d) (cdr (phi1-aux d)) (k0) (b0))                         
                   (k0)))
  :hints (("Goal" :in-theory (enable prootp)
                  :use (encodingp-phi1-aux-7))))

(local-defthmd encodingp-phi1-aux-9
  (implies (and (extensionp d (b0)) (extensionp (e0) d) (not (equal d (b0)))
                (embeddingp (phi1-aux (cdr d)) (cdr d) (k0) (b0))
                (phi1-aux-phi0 (cdr d)))
           (feltp (car (phi1-aux d)) (k0))))

(defthmd encodingp-phi1-aux
  (implies (and (extensionp d (b0)) (extensionp (e0) d) (not (equal d (b0)))
                (embeddingp (phi1-aux (cdr d)) (cdr d) (k0) (b0))
                (phi1-aux-phi0 (cdr d)))
           (embeddingp (phi1-aux d) d (k0) (b0)))
  :hints (("Goal" :use (encodingp-phi1-aux-8 encodingp-phi1-aux-9)
                  :in-theory (enable embeddingp))))

;; We must also show (phi1-aux-phi0 d), i.e., if (feltp x d), then

;;   (embed x phi (k0) (b0)) = (phi0 (flift x d (e0))):

;;   (embed x phi (k0) (b0))
;;     = (peval (pembed x phi' (k0) (b0)) (car phi) (k0))   [definition of embed]
;;     = (peval (pphi0 (plift x d' (e0))) (car phi) (k0))   [pembed-pphi0]
;;     = (peval (pphi0 (plift x d' (e0)))                   [def of phi1-aux]
;;              (phi0 (flift (primitive d) d (e0))) (k0))
;;     = (phi0 (peval (plift x d' (e0))                     [phi0-peval]
;;                    (flift (primitive d) d (e0))
;;                    (e0)))
;;     = (phi0 (peval (plift (plift x d' d) d (e0))         [plift-comp]
;;                    (flift (primitive d) d (e0))
;;                    (e0)))
;;     = (phi0 (flift (peval (plift x d' d)                 [flift-peval]
;;                           (primitive d)
;;                           d)
;;                    d (e0)))
;;     = (phi0 (flift d (e0)))                              [peval-primitive]

(in-theory (disable embeddingp))

(local-defthmd embed-phi0-1
  (implies (and (extensionp d (b0)) (extensionp (e0) d) (not (equal d (b0)))
                (embeddingp (phi1-aux (cdr d)) (cdr d) (k0) (b0))
                (phi1-aux-phi0 (cdr d))
		(feltp x d))
           (equal (embed x (phi1-aux d) (k0) (b0))
                  (peval (pembed x (cdr (phi1-aux d)) (k0) (b0)) (phi0 (flift (primitive d) d (e0))) (k0))))
  :hints (("Goal" :in-theory (enable embed))))

(local-defthmd embed-phi0-2
  (implies (and (extensionp d (b0)) (extensionp (e0) d) (not (equal d (b0))))
           (extensionp (e0) (cdr d)))
  :hints (("Goal" :use ((:instance extends-trans (e (e0)) (f (cdr d)))))))	   
  
(local-defthmd embed-phi0-3
  (implies (and (extensionp d (b0)) (extensionp (e0) d) (not (equal d (b0)))
                (embeddingp (phi1-aux (cdr d)) (cdr d) (k0) (b0))
                (phi1-aux-phi0 (cdr d))
		(feltp x d))
           (equal (embed x (phi1-aux d) (k0) (b0))
                  (peval (pphi0 (plift x (cdr d) (e0))) (phi0 (flift (primitive d) d (e0))) (k0))))
  :hints (("Goal" :in-theory (enable feltp)
                  :use (embed-phi0-1 embed-phi0-2
                        (:instance pembed-pphi0 (p x) (d (cdr d)))))))

(local-defthmd embed-phi0-4
  (implies (and (extensionp d (b0)) (extensionp (e0) d) (not (equal d (b0)))
                (embeddingp (phi1-aux (cdr d)) (cdr d) (k0) (b0))
                (phi1-aux-phi0 (cdr d))
		(feltp x d))
           (equal (embed x (phi1-aux d) (k0) (b0))
                  (phi0 (peval (plift (plift x (cdr d) d) d (e0))
                               (flift (primitive d) d (e0))
                               (e0)))))
  :hints (("Goal" :in-theory (enable feltp polyp-plift)
                  :use (embed-phi0-2 embed-phi0-3
                        (:instance phi0-peval (p (plift x (cdr d) (e0)))
			                      (x (flift (primitive d) d (e0))))))))

(local-defthmd embed-phi0-5
  (implies (and (extensionp d (b0)) (extensionp (e0) d) (not (equal d (b0)))
                (embeddingp (phi1-aux (cdr d)) (cdr d) (k0) (b0))
                (phi1-aux-phi0 (cdr d))
		(feltp x d))
           (equal (peval (plift (plift x (cdr d) d) d (e0))
                         (flift (primitive d) d (e0))
                         (e0))
                  (flift (peval (plift x (cdr d) d)
                                (primitive d)
                                d)
			 d (e0))))
  :hints (("Goal" :in-theory '(feltp fieldp extensionp extends)
                  :use ((:instance polyp-plift (p x) (f (cdr d)) (e d))
		        (:instance feltp-primitive (f d))
		        (:instance flift-peval (p (plift x (cdr d) d)) (x (primitive d)) (f d) (e (e0)))))))

(local-defthmd embed-phi0-6
  (implies (and (extensionp d (b0)) (extensionp (e0) d) (not (equal d (b0)))
                (embeddingp (phi1-aux (cdr d)) (cdr d) (k0) (b0))
                (phi1-aux-phi0 (cdr d))
		(feltp x d))
           (equal (peval (plift x (cdr d) d)
                         (primitive d)
                         d)
		  x))
  :hints (("Goal" :in-theory (enable feltp)
                  :use ((:instance peval-primitive (p x) (f d))
		        (:instance prem-equal (y (car d)) (f (cdr d)))))))

(defthmd embed-phi0
  (implies (and (extensionp d (b0)) (extensionp (e0) d) (not (equal d (b0)))
                (embeddingp (phi1-aux (cdr d)) (cdr d) (k0) (b0))
                (phi1-aux-phi0 (cdr d))
		(feltp x d))
           (equal (embed x (phi1-aux d) (k0) (b0))
                  (phi0 (flift x d (e0)))))
  :hints (("Goal" :use (embed-phi0-4 embed-phi0-5 embed-phi0-6))))

;; Apply phi1-aux-phi0-witness-lemma:

(defthmd embed-phi1-aux
  (implies (and (extensionp d (b0)) (extensionp (e0) d) (not (equal d (b0)))
                (embeddingp (phi1-aux (cdr d)) (cdr d) (k0) (b0))
                (phi1-aux-phi0 (cdr d)))
           (phi1-aux-phi0 d))
  :hints (("Goal" :use (phi1-aux-phi0-witness-lemma
                        (:instance embed-phi0 (x (phi1-aux-phi0-witness d)))))))

;; Combine this with encodingp-phi1-aux:

(defthmd phi1-aux-step
  (implies (and (extensionp d (b0)) (extensionp (e0) d) (not (equal d (b0)))
                (embeddingp (phi1-aux (cdr d)) (cdr d) (k0) (b0))
                (phi1-aux-phi0 (cdr d)))
           (and (embeddingp (phi1-aux d) d (k0) (b0))
                (phi1-aux-phi0 d)))
  :hints (("Goal" :use (encodingp-phi1-aux embed-phi1-aux))))

;; Apply induction:

(local-defthmd extensionp-cdr
  (implies (and (extensionp d (b0)) (extensionp (e0) d) (not (equal d (b0))))
           (and (extensionp (cdr d) (b0)) (extensionp (e0) (cdr d))))
  :hints (("Goal" :use ((:instance extends-trans (e (e0)) (f (cdr d)))))))

(defthmd phi1-aux-lemma
  (implies (and (extensionp d (b0)) (extensionp (e0) d))
           (and (embeddingp (phi1-aux d) d (k0) (b0))
                (phi1-aux-phi0 d)))
  :hints (("Goal" :induct (extends d (b0)))
          ("Subgoal *1/1" :use (phi1-aux-base))
          ("Subgoal *1/2" :use (phi1-aux-step extensionp-cdr))))

;; Instantiating phi1-aux-lemma with d = (e0) yields the desired properties of phi1:

(defthmd phi1-phi0
  (and (embeddingp (phi1) (e0) (k0) (b0))
       (implies (feltp x (e0))
                (equal (embed x (phi1) (k0) (b0))
                       (phi0 x))))
  :hints (("Goal" :in-theory (enable phi1)
                  :use (phi1-aux-phi0-lemma
                        (:instance phi1-aux-lemma (d (e0)))))))

;; We present 3 applications of phi1-phi0 through functional instantiation.
		       
;;-------------------------------------------------------

;; If k is an extension of e and e is an extension of f, then the trivial embedding of e in k 
;; over f is defined as follows:

(defun trivial-embedding (e k f)
  (if (and (extensionp e f) (not (equal e f)))
      (cons (flift (primitive e) e k)
            (trivial-embedding (cdr e) k f))
    ()))

;; We shall show that this is indeed an embedding and that for all x in e,

;;    (embed x (trivial-embedding e k f) k f) = (flift x e k).

;; To that end, we define a generalization of trivial-embedding that emulates phi1-aux:

(defun trivial-embedding-aux (e d k f)
  (if (and (extensionp e d) (extensionp d f) (not (equal d f)))
      (cons (flift (primitive d) d k)
            (trivial-embedding-aux e (cdr d) k f))
    ()))

(defthmd trivial-embedding-aux-rewrite
  (implies (extensionp e d)
           (equal (trivial-embedding-aux e d k f)
                  (trivial-embedding d k f))))

;; The following is proved by functional instantiation of phi1-phi0:

(in-theory (enable phi1))

(defthmd trivial-embedding-aux-flift
  (implies (and (extensionp k e) (extensionp e f))
           (and (embeddingp (trivial-embedding-aux e e k f) e k f)
	        (implies (feltp x e)
		         (equal (embed x (trivial-embedding-aux e e k f) k f)
			        (flift x e k)))))
  :hints (("Goal" :use ((:functional-instance phi1-phi0
                          (e0 (lambda () (if (and (extensionp k e) (extensionp e f)) e (e0))))
                          (k0 (lambda () (if (and (extensionp k e) (extensionp e f)) k (k0))))
                          (b0 (lambda () (if (and (extensionp k e) (extensionp e f)) f (b0))))
                          (phi0 (lambda (x) (if (and (extensionp k e) (extensionp e f)) (flift x e k) (phi0 x))))
			  (phi1-aux (lambda (d) (if (and (extensionp k e) (extensionp e f)) (trivial-embedding-aux e d k f) (phi1-aux d))))
			  (phi1 (lambda () (if (and (extensionp k e) (extensionp e f)) (trivial-embedding-aux e e k f) (phi1)))))))
	  ("Subgoal 5" :use ((:instance extends-trans (e k) (d e))))))

;; The desired result follows from trivial-embedding-aux-flift and trivial-embedding-aux-rewrite:

(defthmd trivial-embedding-flift
  (implies (and (extensionp k e) (extensionp e f))
           (and (embeddingp (trivial-embedding e k f) e k f)
	        (implies (feltp x e)
		         (equal (embed x (trivial-embedding e k f) k f)
			        (flift x e k)))))
  :hints (("Goal" :use (trivial-embedding-aux-flift
                        (:instance trivial-embedding-aux-rewrite (d e))))))

;; The case e = k is the identity embedding of e in e over f:

(defund id-embedding (e f)
  (trivial-embedding e e f))

(defthmd id-embedding-id
  (implies (extensionp e f)
           (and (embeddingp (id-embedding e f) e e f)
	        (implies (feltp x e)
                         (equal (embed x (id-embedding e f) e f)
	                        x))))
  :hints (("Goal" :in-theory (enable id-embedding)
                  :use ((:instance trivial-embedding-flift (k e))))))

(defthmd pembed-id-embedding-feltsp
  (implies (and (extensionp e f) (feltsp p e))
           (equal (pembed p (id-embedding e f) e f)
	          p))
  :hints (("Goal" :induct (len p))
          ("Subgoal *1/1" :use ((:instance id-embedding-id (x (car p)))))))

(defthm pembed-id-embedding
  (implies (and (extensionp e f) (polyp p e))
           (equal (pembed p (id-embedding e f) e f)
	          p))
  :hints (("Goal" :use (pembed-id-embedding-feltsp))))

;;-----------------------

;; If phi embeds e in g and psi embeds g in k, then the composition embeds e in k:

(defun comp-embedding (psi phi e k f)
  (if (and (extensionp e f) (not (equal e f)))
      (cons (embed (car phi) psi k f)
            (comp-embedding psi (cdr phi) (cdr e) k f))
    ()))

(defun comp-embedding-aux (psi phi e d g k f)
  (if (and (extensionp e d) (extensionp d f) (not (equal d f)))
      (cons (embed (embed (primitive d) phi g f) psi k f)
            (comp-embedding-aux psi (cdr phi) e (cdr d) g k f))
    ()))

(defthmd comp-embedding-aux-rewrite
  (implies (and (extensionp e d) (extensionp d f) (extensionp g f) (embeddingp phi d g f))
           (equal (comp-embedding-aux psi phi e d g k f)
	          (comp-embedding psi phi d k f)))
  :hints (("Subgoal *1/5" :use ((:instance embed-primitive (k g) (e d))))
          ("Subgoal *1/4" :in-theory (enable embeddingp) :use ((:instance embed-primitive (k g) (e d))))))

(defund restrict-embedding (phi e d)
  (nthcdr (- (len e) (len d)) phi))

(defthm restrict-embedding-noop
  (equal (restrict-embedding phi e e) phi)
  :hints (("Goal" :in-theory (enable restrict-embedding))))

(defthmd cdr-nthcdr
  (implies (natp n)
           (equal (cdr (nthcdr n l))
	          (nthcdr (1+ n) l))))

(defthmd cdr-restrict-embedding
  (implies (and (extensionp e d) (extensionp d f) (not (equal d f)))
           (equal (cdr (restrict-embedding phi e d))
	          (restrict-embedding phi e (cdr d))))
  :hints (("Goal" :in-theory (enable restrict-embedding)
                  :expand ((extends e d))
                  :use ((:instance cdr-nthcdr (n (- (len e) (len d))) (l phi))
		        (:instance len-extends (f d))))))

(defthmd restrict-embedding-cdr
  (implies (and (extensionp e d) (not (equal e d)))
           (equal (restrict-embedding phi e d)
	          (restrict-embedding (cdr phi) (cdr e) d)))
  :hints (("Goal" :in-theory (enable restrict-embedding)
                  :use ((:instance len-extends (e (cdr e)) (f d))))))

(defthmd embed-flift-step
  (implies (and (extensionp e f) (extensionp k f) (embeddingp phi e k f)
                (extensionp e d) (extensionp d f) (not (equal e d)) (feltp x d)
		(EQUAL (EMBED (FLIFT X D (CDR E)) (CDR PHI) K F)
                       (EMBED X (RESTRICT-EMBEDDING (CDR PHI) (CDR E) D) K F)))
	   (equal (embed (flift x d e) phi k f)
	          (embed x (restrict-embedding phi e d) k f)))
  :hints (("Goal" :in-theory (disable flift-comp flift-flift)
                  :use (restrict-embedding-cdr
                       (:instance flift-flift (f d))
		       (:instance len-extends (e (cdr e)) (f d))
		       (:instance len-extends (e d) (f e))
                       (:instance embed-flift (x (flift x d (cdr e))))))))

(in-theory (enable embeddingp))
			
(defthmd embed-flift-gen
  (implies (and (extensionp e f) (extensionp k f) (embeddingp phi e k f)
                (extensionp e d) (extensionp d f) (feltp x d))
	   (equal (embed (flift x d e) phi k f)
	          (embed x (restrict-embedding phi e d) k f)))
  :hints (("Goal" :induct (embeddingp phi e k f))
          ("Subgoal *1/1" :in-theory (enable embed flift restrict-embedding)
	                  :use ((:instance len-extends (f d))
			        (:instance len-extends (f e) (e d))))
	  ("Subgoal *1/2" :use (embed-flift-step))))

(defmacro comp-embedding-mac ()
  '(and (extensionp e f) (extensionp g f) (extensionp k f)
        (embeddingp phi e g f) (embeddingp psi g k f)))

(defthmd embeddingp-comp-embedding-aux
  (implies (comp-embedding-mac)
	   (and (embeddingp (comp-embedding-aux psi phi e e g k f) e k f)
	        (implies (feltp x e)
		         (equal (embed x (comp-embedding-aux psi phi e e g k f) k f)
			        (embed (embed x phi g f) psi k f)))))
  :hints (("Goal" :use ((:functional-instance phi1-phi0
                          (e0 (lambda () (if (comp-embedding-mac) e (e0))))
                          (k0 (lambda () (if (comp-embedding-mac) k (k0))))
                          (b0 (lambda () (if (comp-embedding-mac) f (b0))))
                          (phi0 (lambda (x) (if (comp-embedding-mac) (embed (embed x phi g f) psi k f) (phi0 x))))
			  (phi1-aux (lambda (d) (if (comp-embedding-mac) (comp-embedding-aux psi (restrict-embedding phi e d) e d g k f) (phi1-aux d))))
			  (phi1 (lambda () (if (comp-embedding-mac) (comp-embedding-aux psi phi e e g k f) (phi1)))))))
	  ("Subgoal 1" :expand ((COMP-EMBEDDING-AUX PSI (RESTRICT-EMBEDDING PHI E D) E D G K F))
	               :in-theory (enable embed-flift-gen))		       
	  ("Subgoal 1.57" :use (cdr-restrict-embedding))))

(defthmd embeddingp-comp-embedding
  (implies (and (extensionp e f) (extensionp g f) (extensionp k f)
                (embeddingp phi e g f) (embeddingp psi g k f))
	   (and (embeddingp (comp-embedding psi phi e k f) e k f)
	        (implies (feltp x e)
		         (equal (embed x (comp-embedding psi phi e k f) k f)
			        (embed (embed x phi g f) psi k f)))))
  :hints (("Goal" :use (embeddingp-comp-embedding-aux
                        (:instance comp-embedding-aux-rewrite (d e))))))

;; Composed embedding of a polynomial:

(defthmd pembed-comp-embedding-feltsp
  (implies (and (extensionp e f) (extensionp g f) (extensionp k f)
                (embeddingp phi e g f) (embeddingp psi g k f)
		(feltsp p e))
	   (equal (pembed p (comp-embedding psi phi e k f) k f)
	          (pembed (pembed p phi g f) psi k f)))
  :hints (("Goal" :induct (len p))
          ("Subgoal *1/1" :use ((:instance embeddingp-comp-embedding (x (car p)))))))

(defthmd pembed-comp-embedding
  (implies (and (extensionp e f) (extensionp g f) (extensionp k f)
                (embeddingp phi e g f) (embeddingp psi g k f)
		(polyp p e))
	   (equal (pembed p (comp-embedding psi phi e k f) k f)
	          (pembed (pembed p phi g f) psi k f)))
  :hints (("Goal" :use (pembed-comp-embedding-feltsp))))

;; I just discovered that we need to prove that (restrict-embedding phi e d) is an embedding:

(defthmd embeddingp-restrict-embedding-1
  (implies (and (extensionp e f) (extensionp k f) (embeddingp phi e k f) (natp n) (<= n (- (len e) (len f))))               
	   (embeddingp (nthcdr n phi) (nthcdr n e) k f)))

(defthmd nthcdr-extension
  (implies (extends e f)
           (equal (nthcdr (- (len e) (len f)) e)
	          f))
  :hints (("Subgoal *1/3" :use ((:instance len-extends (e (cdr e)))))))
	   
(defthmd embeddingp-restrict-embedding
  (implies (and (extensionp e d) (extensionp d f) (extensionp k f) (embeddingp phi e k f))                
	   (embeddingp (restrict-embedding phi e d) d k f))
  :hints (("Goal" :in-theory (enable restrict-embedding)
                  :use (extends-trans
		        (:instance len-extends (f d))	
		        (:instance len-extends (e d))
			(:instance nthcdr-extension (f d))
	                (:instance embeddingp-restrict-embedding-1 (n (- (len e) (len d))))))))

;; Composition with the identity embedding:

(defthmd embed-comp-id-embedding-1
  (implies (and (extensionp e f) (extensionp k f) (embeddingp phi e k f)
                (feltp x e))
           (equal (embed x (comp-embedding (id-embedding k f) phi e k f) k f)
	          (embed x phi k f)))
  :hints (("Goal" :use ((:instance id-embedding-id (e k) (x (embed x phi k f)))
                        (:instance embeddingp-comp-embedding (g k) (psi (id-embedding k f)))))))

(defthmd embed-comp-id-embedding-2
  (implies (and (extensionp e f) (extensionp k f) (embeddingp phi e k f)
                (feltp x e))
           (equal (embed x (comp-embedding phi (id-embedding e f) e k f) k f)
	          (embed x phi k f)))
  :hints (("Goal" :use (id-embedding-id
                        (:instance embeddingp-comp-embedding (g e) (phi (id-embedding e f)) (psi phi))))))

(defthmd comp-id-embedding
  (implies (and (extensionp e f) (extensionp k f) (embeddingp phi e k f))
           (and (equal (comp-embedding (id-embedding k f) phi e k f) phi)
	        (equal (comp-embedding phi (id-embedding e f) e k f) phi)))
  :hints (("Goal" :use (id-embedding-id
                        (:instance id-embedding-id (e k) (x (embed x phi k f)))
                        (:instance embeddingp-comp-embedding (g k) (psi (id-embedding k f)))
			(:instance embeddingp-comp-embedding (g e) (phi (id-embedding e f)) (psi phi))
                        (:instance embed-comp-id-embedding-1 (x (embed-cex (comp-embedding (id-embedding k f) phi e k f) phi e f)))
                        (:instance embed-comp-id-embedding-2 (x (embed-cex (comp-embedding phi (id-embedding e f) e k f) phi e f)))
			(:instance embed-cex-lemma (phi (comp-embedding (id-embedding k f) phi e k f)) (psi phi))
			(:instance embed-cex-lemma (phi (comp-embedding phi (id-embedding e f) e k f)) (psi phi))))))

;; Associativity of composition:

(defthmd embed-comp-embedding-assoc
  (implies (and (extensionp e1 f) (extensionp e2 f) (extensionp e3 f) (extensionp e4 f)
                (embeddingp phi1 e1 e2 f) (embeddingp phi2 e2 e3 f) (embeddingp phi3 e3 e4 f)
		(feltp x e1))
	   (equal (embed x (comp-embedding phi3 (comp-embedding phi2 phi1 e1 e3 f) e1 e4 f) e4 f)
	          (embed x (comp-embedding (comp-embedding phi3 phi2 e2 e4 f) phi1 e1 e4 f) e4 f)))
  :hints (("Goal" :use ((:instance embeddingp-comp-embedding (phi phi1) (psi phi2) (e e1) (g e2) (k e3))
		        (:instance embeddingp-comp-embedding (phi phi2) (psi phi3) (e e2) (g e3) (k e4) (x (embed x phi1 e2 f)))
			(:instance embeddingp-comp-embedding (phi (comp-embedding phi2 phi1 e1 e3 f)) (psi phi3) (e e1) (g e3) (k e4))
			(:instance embeddingp-comp-embedding (phi phi1) (psi (comp-embedding phi3 phi2 e2 e4 f)) (e e1) (g e2) (k e4))))))

(defthmd comp-embedding-assoc
  (implies (and (extensionp e1 f) (extensionp e2 f) (extensionp e3 f) (extensionp e4 f)
                (embeddingp phi1 e1 e2 f) (embeddingp phi2 e2 e3 f) (embeddingp phi3 e3 e4 f))
	   (equal (comp-embedding phi3 (comp-embedding phi2 phi1 e1 e3 f) e1 e4 f)
	          (comp-embedding (comp-embedding phi3 phi2 e2 e4 f) phi1 e1 e4 f)))
  :hints (("Goal" :use ((:instance embeddingp-comp-embedding (phi phi1) (psi phi2) (e e1) (g e2) (k e3))
		        (:instance embeddingp-comp-embedding (phi phi2) (psi phi3) (e e2) (g e3) (k e4) (x (embed x phi1 e2 f)))
			(:instance embeddingp-comp-embedding (phi (comp-embedding phi2 phi1 e1 e3 f)) (psi phi3) (e e1) (g e3) (k e4))
			(:instance embeddingp-comp-embedding (phi phi1) (psi (comp-embedding phi3 phi2 e2 e4 f)) (e e1) (g e2) (k e4))
			(:instance embed-comp-embedding-assoc (x (embed-cex (comp-embedding phi3 (comp-embedding phi2 phi1 e1 e3 f) e1 e4 f)
			                                                    (comp-embedding (comp-embedding phi3 phi2 e2 e4 f) phi1 e1 e4 f)
									    e1 f)))
			(:instance embed-cex-lemma (e e1) (k e4)
			                           (phi (comp-embedding phi3 (comp-embedding phi2 phi1 e1 e3 f) e1 e4 f))
						   (psi (comp-embedding (comp-embedding phi3 phi2 e2 e4 f) phi1 e1 e4 f)))))))

			
;;---------------------------------------------------------------------

;; We shall construct the inverse of an embedding by functional instantiation of phi1-phi0.
;; An embedding of e in k over f is an injective linear transformation from e into k, viewed as vector spaces.  It follows by functional instantiation
;; of injection-dim-<= ("../linear/vectors") that the degree of k over f is at least the degree of e over f:

(defmacro injective-mac ()
  '(and (extensionp e f) (not (equal e f)) (extensionp k f) (not (equal k f)) (embeddingp phi e k f)))

(local-defthmd embedding-degree
  (implies (and (extensionp e f) (not (equal e f)) (extensionp k f) (not (equal k f)) (embeddingp phi e k f))
	   (<= (edegree e f)
	       (edegree k f)))
  :hints (("Goal" :in-theory (enable fmul-assoc f*assoc fadd-assoc f+assoc fmul-comm
                                     fadd-comm ebasis0-lin-indep ebasis0-spans elistnp-ecoords0 elistnp-ebasis0 fdistrib-comm
				     vdistv fdistrib-comm vdistf v*assoc fmul-assoc v+assoc fadd-assoc fadd-comm
				     wdistw wdistf w+assoc w*assoc)
                  :use ((:functional-instance injection-dim-<=
                          (f0 (lambda () (if (injective-mac) (fzero f) (f0))))
                          (f1 (lambda () (if (injective-mac) (fone f) (f1))))
                          (fp (lambda (x) (if (injective-mac) (feltp x f) (fp x))))
                          (f+ (lambda (x y) (if (injective-mac) (fadd x y f) (f+ x y))))
                          (f* (lambda (x y) (if (injective-mac) (fmul x y f) (f* x y))))
                          (f- (lambda (x) (if (injective-mac) (fneg x f) (f- x))))
                          (f/ (lambda (x) (if (injective-mac) (frecip x f) (f/ x))))
			  (flistnp (lambda (x n) (if (injective-mac) (elistnp x n f) (flistnp x n))))
			  (flistn0 (lambda (n) (if (injective-mac) (elistn0 n f) (flistn0 n))))			  
                          (vp (lambda (x) (if (injective-mac) (feltp x e) (vp x))))
			  (v+ (lambda (x y) (if (injective-mac) (fadd x y e) (v+ x y))))
			  (v0 (lambda () (if (injective-mac) (fzero e) (v0))))
			  (v- (lambda (x) (if (injective-mac) (fneg x e) (v- x))))
			  (v* (lambda (c x) (if (injective-mac) (fmul (flift c f e) x e) (v* c x))))
			  (vlistnp (lambda (x n) (if (injective-mac) (elistnp x n e) (vlistnp x n))))
			  (vcomb (lambda (flist elist) (if (injective-mac) (ecomb flist elist e f) (vcomb flist elist))))
			  (vdim (lambda () (if (injective-mac) (edegree e f) (vdim))))
			  (vbasis0 (lambda () (if (injective-mac) (ebasis0 e f) (vbasis0))))
			  (vcoords0 (lambda (x) (if (injective-mac) (ecoords0 x e f) (vcoords0 x))))
                          (wp (lambda (x) (if (injective-mac) (feltp x k) (wp x))))
			  (w+ (lambda (x y) (if (injective-mac) (fadd x y k) (w+ x y))))
			  (w0 (lambda () (if (injective-mac) (fzero k) (w0))))
			  (w- (lambda (x) (if (injective-mac) (fneg x k) (w- x))))
			  (w* (lambda (c x) (if (injective-mac) (fmul (flift c f k) x k) (w* c x))))
			  (wlistnp (lambda (x n) (if (injective-mac) (elistnp x n k) (wlistnp x n))))
			  (wcomb (lambda (flist elist) (if (injective-mac) (ecomb flist elist k f) (wcomb flist elist))))
			  (wdim (lambda () (if (injective-mac) (edegree k f) (wdim))))
			  (wbasis0 (lambda () (if (injective-mac) (ebasis0 k f) (wbasis0))))
			  (wcoords0 (lambda (x) (if (injective-mac) (ecoords0 x k f) (wcoords0 x))))
			  (lin (lambda (x) (if (injective-mac) (embed x phi k f) (lin x))))
			  (lin-injective-p (lambda () (if (injective-mac) (embeddingp phi e k f) (lin-injective-p)))))))
          ("Subgoal 51" :in-theory (enable f*comm))
          ("Subgoal 50" :in-theory (enable f+comm))
	  ("Subgoal 45" :use (ebasis0-lin-indep (:instance vindepp-vcomb-v0 (m (vdim)) (l (vbasis0)))))
	  ("Subgoal 41" :use (posp-edegree))
	  ("Subgoal 32" :in-theory (enable v+comm))
	  ("Subgoal 28" :in-theory (enable vdim) :use (len-ebasis0))
	  ("Subgoal 25" :use ((:instance ebasis0-lin-indep (e k)) (:instance windepp-wcomb-w0 (m (wdim)) (l (wbasis0)))))
	  ("Subgoal 21" :use ((:instance posp-edegree (e k))))
	  ("Subgoal 12" :in-theory (enable w+comm))
	  ("Subgoal 8" :in-theory (enable wdim) :use ((:instance len-ebasis0 (e k))))
	  ("Subgoal 6" :in-theory (enable lin-injective-p-lemma) :use (embed-fzero))
	  ("Subgoal 5" :use (lin-injective-p-witness-lemma (:instance embed-fzero (x (lin-injective-p-witness))) (:instance lin-injective-p-lemma (x (lin-injective-p-witness)))))))

(defthmd embedding-degree-<=
  (implies (and (extensionp e f) (extensionp k f) (embeddingp phi e k f))
	   (<= (edegree e f)
	       (edegree k f)))
  :hints (("Goal" :use (embedding-degree no-embedding-in-f
                        (:instance posp-edegree (e k))))))


;; If k and e have the same degree over f, then it similarly follows from injection-dim-= that this linear transformation is surjective:

(defchoose preembed x (y phi e k f)
  (and (feltp x e)
       (equal (embed x phi k f) y)))

(defun-sk surjective-embedding-p (phi e k f)
  (forall (y)
    (implies (feltp y k)
             (let ((x (preembed y phi e k f)))
	       (and (feltp x e)
                    (equal (embed x phi k f) y))))))

(defthm surjective-embedding-p-lemma
  (implies (and (surjective-embedding-p phi e k f) (feltp y k))
           (let ((x (preembed y phi e k f)))
	     (and (feltp x e)
                  (equal (embed x phi k f) y))))
  :hints (("Goal" :use (surjective-embedding-p-necc))))

(defthmd surjective-embedding-p-witness-lemma
  (let ((y (surjective-embedding-p-witness phi e k f)))
    (implies (implies (feltp y k)
                      (let ((x (preembed y phi e k f)))
	                (and (feltp x e)
                             (equal (embed x phi k f) y))))
	     (surjective-embedding-p phi e k f))))

(defmacro surjective-mac ()
  '(and (extensionp e f) (extensionp k f) (not (equal e f)) (not (equal k f)) (embeddingp phi e k f)))

(local-defthmd embedding-surjective-1
  (implies (and (extensionp e f) (extensionp k f) (not (equal e f)) (not (equal k f)) (embeddingp phi e k f))
           (iff (equal (edegree e f) (edegree k f))		
	        (surjective-embedding-p phi e k f)))
  :hints (("Goal" :in-theory (enable fmul-assoc f*assoc fadd-assoc f+assoc fmul-comm
                                     fadd-comm ebasis0-lin-indep ebasis0-spans elistnp-ecoords0 elistnp-ebasis0 fdistrib-comm
				     vdistv fdistrib-comm vdistf v*assoc fmul-assoc v+assoc fadd-assoc fadd-comm
				     wdistw wdistf w+assoc w*assoc)
                  :use ((:functional-instance injection-surjection-dim-=
                          (f0 (lambda () (if (surjective-mac) (fzero f) (f0))))
                          (f1 (lambda () (if (surjective-mac) (fone f) (f1))))
                          (fp (lambda (x) (if (surjective-mac) (feltp x f) (fp x))))
                          (f+ (lambda (x y) (if (surjective-mac) (fadd x y f) (f+ x y))))
                          (f* (lambda (x y) (if (surjective-mac) (fmul x y f) (f* x y))))
                          (f- (lambda (x) (if (surjective-mac) (fneg x f) (f- x))))
                          (f/ (lambda (x) (if (surjective-mac) (frecip x f) (f/ x))))
			  (flistnp (lambda (x n) (if (surjective-mac) (elistnp x n f) (flistnp x n))))
			  (flistn0 (lambda (n) (if (surjective-mac) (elistn0 n f) (flistn0 n))))			  
                          (vp (lambda (x) (if (surjective-mac) (feltp x e) (vp x))))
			  (v+ (lambda (x y) (if (surjective-mac) (fadd x y e) (v+ x y))))
			  (v0 (lambda () (if (surjective-mac) (fzero e) (v0))))
			  (v- (lambda (x) (if (surjective-mac) (fneg x e) (v- x))))
			  (v* (lambda (c x) (if (surjective-mac) (fmul (flift c f e) x e) (v* c x))))
			  (vlistnp (lambda (x n) (if (surjective-mac) (elistnp x n e) (vlistnp x n))))
			  (vcomb (lambda (flist elist) (if (surjective-mac) (ecomb flist elist e f) (vcomb flist elist))))
			  (vdim (lambda () (if (surjective-mac) (edegree e f) (vdim))))
			  (vbasis0 (lambda () (if (surjective-mac) (ebasis0 e f) (vbasis0))))
			  (vcoords0 (lambda (x) (if (surjective-mac) (ecoords0 x e f) (vcoords0 x))))
                          (wp (lambda (x) (if (surjective-mac) (feltp x k) (wp x))))
			  (w+ (lambda (x y) (if (surjective-mac) (fadd x y k) (w+ x y))))
			  (w0 (lambda () (if (surjective-mac) (fzero k) (w0))))
			  (w- (lambda (x) (if (surjective-mac) (fneg x k) (w- x))))
			  (w* (lambda (c x) (if (surjective-mac) (fmul (flift c f k) x k) (w* c x))))
			  (wlistnp (lambda (x n) (if (surjective-mac) (elistnp x n k) (wlistnp x n))))
			  (wcomb (lambda (flist elist) (if (surjective-mac) (ecomb flist elist k f) (wcomb flist elist))))
			  (wdim (lambda () (if (surjective-mac) (edegree k f) (wdim))))
			  (wbasis0 (lambda () (if (surjective-mac) (ebasis0 k f) (wbasis0))))
			  (wcoords0 (lambda (x) (if (surjective-mac) (ecoords0 x k f) (wcoords0 x))))
			  (lin (lambda (x) (if (surjective-mac) (embed x phi k f) (lin x))))
			  (lin-preimage (lambda (y) (if (surjective-mac) (preembed y phi e k f) (lin-preimage y))))
			  (lin-injective-p (lambda () (if (surjective-mac) (embeddingp phi e k f) (lin-injective-p))))
			  (lin-surjective-p (lambda () (if (surjective-mac) (surjective-embedding-p phi e k f) (lin-surjective-p))))
			  (lin-injective-p-witness (lambda () (if (surjective-mac) (fzero e) (lin-injective-p-witness))))
			  (lin-surjective-p-witness (lambda () (if (surjective-mac) (surjective-embedding-p-witness phi e k f) (lin-surjective-p-witness)))))))
          ("Subgoal 67" :use (lin-surjective-p-lemma))
          ("Subgoal 66" :use (surjective-embedding-p-witness-lemma lin-surjective-p-witness-lemma) :in-theory (enable surjective-embedding-p-lemma lin-surjective-p-lemma))
          ("Subgoal 65" :use ((:instance embed-fmul (y (flift c f e))) (:instance embed-fixes (x c))))
          ("Subgoal 54" :in-theory (enable f*comm))
          ("Subgoal 53" :in-theory (enable f+comm))
	  ("Subgoal 48" :use ((:instance vindepp-vcomb-v0 (m (vdim)) (l (vbasis0))) (:instance windepp-wcomb-w0 (m (wdim)) (l (wbasis0)))))
	  ("Subgoal 44" :use (posp-edegree (:instance posp-edegree (e k))))
	  ("Subgoal 35" :in-theory (enable w+comm v+comm))	  
	  ("Subgoal 31" :in-theory (enable wdim vdim) :use (len-ebasis0 (:instance len-ebasis0 (e k))))
	  ("Subgoal 28" :use ((:instance windepp-wcomb-w0 (m (wdim)) (l (wbasis0))) (:instance vindepp-vcomb-v0 (m (vdim)) (l (vbasis0)))))
	  ("Subgoal 24" :use (posp-edegree (:instance posp-edegree (e k))))
	  ("Subgoal 15" :in-theory (enable v+comm w+comm))
	  ("Subgoal 14" :in-theory (enable wdim) :use ((:instance len-ebasis0 (e k))))
	  ("Subgoal 12" :in-theory (enable lin-injective-p-lemma) :use (embed-fzero))
	  ("Subgoal 11" :in-theory (enable vdim) :use ((:instance len-ebasis0 (e e))))
	  ("Subgoal 9" :use (lin-surjective-p-lemma lin-preimage preembed))
	  ("Subgoal 8" :use (embed-fzero lin-surjective-p-witness-lemma (:instance lin-surjective-p-lemma (y (lin-surjective-p-witness)))))
	  ("Subgoal 7" :use (lin-injective-p-witness-lemma) :in-theory (enable lin-injective-p-lemma))
	  ("Subgoal 3" :use (lin-preimage (:instance preembed (y (embed x phi k f)))))
	  ("Subgoal 2" :use (embed-fzero lin-injective-p-lemma))
	  ("Subgoal 1" :use (lin-injective-p-witness-lemma (:instance lin-injective-p-lemma (x (lin-injective-p-witness)))))))

(local-defthmd embedding-surjective-2
  (implies (and (fieldp f) (embeddingp phi f f f) (feltp x f))
           (equal (embed x phi f f) x))
  :hints (("Goal" :expand ((EMBED X NIL F F)))))

(local-defthmd embedding-surjective-3
  (implies (and (fieldp f) (embeddingp phi f f f))
           (surjective-embedding-p phi f f f))
  :hints (("Goal" :use (surjective-embedding-p-witness-lemma
                        (:instance embedding-surjective-2 (x (surjective-embedding-p-witness phi f f f)))
			(:instance preembed (e f) (k f) (y (surjective-embedding-p-witness phi f f f))
			                                (x (surjective-embedding-p-witness phi f f f)))))))

(local-defthm embedding-surjective-4
  (implies (and (extensionp e f) (extensionp k f)
                (equal (edegree e f) (edegree k f))
		(embeddingp phi e k f))
	   (surjective-embedding-p phi e k f))
  :hints (("Goal" :use (embedding-surjective-1 embedding-surjective-3 no-embedding-in-f
                        (:instance posp-edegree (e (cdr k)) (f e)))
		  :nonlinearp t		  
                  :expand ((FIELDP K)))))

(local-defthm embedding-surjective-5
  (implies (and (extensionp e f) (extensionp k f) (embeddingp phi e k f) (not (equal e f))
                (surjective-embedding-p phi e k f))
           (equal (edegree e f) (edegree k f)))	        
  :hints (("Goal" :in-theory (disable posp-edegree) :use (posp-edegree embedding-degree-<= embedding-surjective-1))))

(local-defthm embedding-surjective-6
  (implies (and (extensionp k f) (not (equal k f)) (embeddingp phi f k f)
                (surjective-embedding-p phi f k f)
		(feltp x k))
           (fliftedp x (cdr k) k))
  :hints (("Goal" :in-theory (disable fliftedp-flift flift-comp flift-flift)
                  :use ((:instance surjective-embedding-p-lemma (y x) (e f))
                        (:instance embed-fixes (e f) (x (preembed x phi f k f)))
			(:instance fliftedp-flift (e k) (f (cdr k)) (x (FLIFT (PREEMBED X NIL F K F) F (CDR K))))
			(:instance flift-flift (e k) (x (preembed x phi f k f)))))))

(local-defthm embedding-surjective-7
  (implies (and (extensionp k f) (embeddingp phi f k f)
                (surjective-embedding-p phi f k f))
           (equal k f))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable fliftedp)
                  :expand ((fieldp k))
                  :use ((:instance embedding-surjective-6 (x (primitive k)))
                        (:instance min-poly-primitive (f k))))))

(local-defthm embedding-surjective-8
  (implies (and (extensionp e f) (extensionp k f) (embeddingp phi e k f)
                (surjective-embedding-p phi e k f))
           (equal (edegree e f) (edegree k f)))	        
  :hints (("Goal" :use (embedding-surjective-5 embedding-surjective-7))))

(defthm embedding-surjective
  (implies (and (extensionp e f) (extensionp k f) (embeddingp phi e k f))
           (iff (equal (edegree e f) (edegree k f))		
	        (surjective-embedding-p phi e k f)))
  :hints (("Goal" :use (embedding-surjective-4 embedding-surjective-8))))

(defun iso-embeddingp (phi e k f)
  (and (embeddingp phi e k f)
       (equal (edegree e f) (edegree k f))))

(defthm embed-preembed
  (implies (and (extensionp e f) (extensionp k f)
		(iso-embeddingp phi e k f)
                (feltp y k))
	   (let ((x (preembed y phi e k f)))
	     (and (feltp x e)
	          (equal (embed x phi k f) y))))
  :hints (("Goal" :use (embedding-surjective surjective-embedding-p-lemma))))


(defthm preembed-embed
  (implies (and (extensionp e f) (extensionp k f)
		(iso-embeddingp phi e k f)
                (feltp x e))
	   (let ((y (embed x phi k f)))
	     (and (feltp y k)
	          (equal (preembed y phi e k f) x))))
  :hints (("Goal" :use ((:instance embed-preembed (y (embed x phi k f)))
                        (:instance embedding-1-1 (y (preembed (embed x phi k f) phi e k f)))))))

(defthm preembed-fzero-fone
  (Implies (and (extensionp e f) (extensionp k f)
		(iso-embeddingp phi e k f))
	   (and (equal (preembed (fzero k) phi e k f)
	               (fzero e))
	        (equal (preembed (fone k) phi e k f)
	               (fone e))))
  :hints (("Goal" :use ((:instance embedding-1-1 (x (fzero e)) (y (preembed (fzero k) phi e k f)))
                        (:instance embedding-1-1 (x (fone e)) (y (preembed (fone k) phi e k f)))))))

(defthm preembed-fadd-fmul
  (implies (and (extensionp e f) (extensionp k f)
		(iso-embeddingp phi e k f)
		(feltp x k) (feltp y k))
	   (and (equal (preembed (fadd x y k) phi e k f)
	               (fadd (preembed x phi e k f) (preembed y phi e k f) e))
		(equal (preembed (fmul x y k) phi e k f)
	               (fmul (preembed x phi e k f) (preembed y phi e k f) e))))
  :hints (("Goal" :use ((:instance embedding-1-1 (x (fadd (preembed x phi e k f) (preembed y phi e k f) e))
                                                 (y (preembed (fadd x y k) phi e k f)))
                        (:instance embedding-1-1 (x (fmul (preembed x phi e k f) (preembed y phi e k f) e))
                                                 (y (preembed (fmul x y k) phi e k f)))))))

(defthm preembed-fixes
  (implies (and (extensionp e f) (extensionp k f)
		(iso-embeddingp phi e k f)
		(feltp x f))
	   (equal (preembed (flift x f k) phi e k f)
	          (flift x f e)))
  :hints (("Goal" :use ((:instance embedding-1-1 (x (flift x f e)) (y (preembed (flift x f k) phi e k f)))))))

;; We define the inverse of an embedding phi of e in k over f:
          
(defun inv-embedding-aux (phi e k d f)
  (and (extensionp k d) (extensionp d f) (not (equal d f))
       (cons (preembed (flift (primitive d) d k) phi e k f)
             (inv-embedding-aux phi e k (cdr d) f))))

(defun inv-embedding (phi e k f)
  (inv-embedding-aux phi e k k f))

;; The following is proved by functional instantiantion of phi1-phi0:

(defmacro inv-embedding-mac ()
  '(and (extensionp e f) (extensionp k f)
        (iso-embeddingp phi e k f)))

(defthmd embeddingp-inv-embedding-aux
  (implies (and (extensionp e f) (extensionp k f)
		(iso-embeddingp phi e k f))
           (and (embeddingp (inv-embedding-aux phi e k k f) k e f)
	        (implies (feltp x k)
                         (equal (embed x (inv-embedding-aux phi e k k f) e f)
	                        (preembed x phi e k f)))))
  :hints (("Goal" :use ((:functional-instance phi1-phi0
                          (e0 (lambda () (if (inv-embedding-mac) k (e0))))
                          (k0 (lambda () (if (inv-embedding-mac) e (k0))))
                          (b0 (lambda () (if (inv-embedding-mac) f (b0))))
                          (phi0 (lambda (x) (if (inv-embedding-mac) (preembed x phi e k f) (phi0 x))))
			  (phi1-aux (lambda (d) (if (inv-embedding-mac) (inv-embedding-aux phi e k d f) (phi1-aux d))))
			  (phi1 (lambda () (if (inv-embedding-mac) (inv-embedding-aux phi e k k f) (phi1)))))))))

;; Instantiate embeddingp-inv-embedding-aux:

(defthmd embeddingp-inv-embedding
  (implies (and (extensionp e f) (extensionp k f)
		(iso-embeddingp phi e k f))
           (and (embeddingp (inv-embedding phi e k f) k e f)
	        (implies (feltp x k)
                         (equal (embed x (inv-embedding phi e k f) e f)
	                        (preembed x phi e k f)))))
  :hints (("Goal" :in-theory (enable inv-embedding)
                  :use (embeddingp-inv-embedding-aux))))

(local-defthmd comp-inv-embedding-1
  (implies (and (extensionp e f) (extensionp k f) (iso-embeddingp phi e k f)
		(feltp x e))
	   (equal (embed x (comp-embedding (inv-embedding phi e k f) phi e e f)
	                 e f)
	          x))
  :hints (("Goal" :use ((:instance embeddingp-inv-embedding (x (embed x phi k f)))
                        (:instance embeddingp-comp-embedding (psi (inv-embedding phi e k f)) (g k) (k e))))))

(local-defthmd comp-inv-embedding-2
  (implies (and (extensionp e f) (extensionp k f) (iso-embeddingp phi e k f))
	   (equal (comp-embedding (inv-embedding phi e k f) phi e e f)
	          (id-embedding e f)))
   :hints (("Goal" :use (embeddingp-inv-embedding
                         (:instance id-embedding-id
			   (x (embed-cex (comp-embedding (inv-embedding phi e k f) phi e e f)
                                         (id-embedding e f)
				         e f)))
                         (:instance comp-inv-embedding-1
                           (x (embed-cex (comp-embedding (inv-embedding phi e k f) phi e e f)
                                         (id-embedding e f)
				         e f)))
			(:instance embed-cex-lemma (phi (comp-embedding (inv-embedding phi e k f) phi e e f))
			                           (psi (id-embedding e f))
						   (k e))
                        (:instance embeddingp-comp-embedding (psi (inv-embedding phi e k f)) (g k) (k e))))))

(local-defthmd comp-inv-embedding-3
  (implies (and (extensionp e f) (extensionp k f) (iso-embeddingp phi e k f)
		(feltp x k))
	   (equal (embed x (comp-embedding phi (inv-embedding phi e k f) k k f)
	                 k f)
	          x))
  :hints (("Goal" :use (embeddingp-inv-embedding
                        (:instance embeddingp-comp-embedding (phi (inv-embedding phi e k f)) (psi phi) (g e) (e k))))))

(defthmd comp-inv-embedding-4
  (implies (and (extensionp e f) (extensionp k f) (iso-embeddingp phi e k f))
	   (equal (comp-embedding phi (inv-embedding phi e k f) k k f)
	          (id-embedding k f)))
   :hints (("Goal" :use (embeddingp-inv-embedding
                         (:instance id-embedding-id
			   (x (embed-cex (comp-embedding phi (inv-embedding phi e k f) k k f)
                                         (id-embedding k f)
				         k f))
			   (e k))
                         (:instance comp-inv-embedding-3
                           (x (embed-cex (comp-embedding phi (inv-embedding phi e k f) k k f)
                                         (id-embedding k f)
				         k f)))
			(:instance embed-cex-lemma (phi (comp-embedding phi (inv-embedding phi e k f) k k f))
			                           (psi (id-embedding k f))
						   (e k))
                        (:instance embeddingp-comp-embedding (phi (inv-embedding phi e k f)) (psi phi) (g e) (e k))))))

(defthmd comp-inv-embedding
  (implies (and (extensionp e f) (extensionp k f) (iso-embeddingp phi e k f))
	   (let ((inv (inv-embedding phi e k f)))
	     (and (embeddingp inv k e f)
	          (equal (comp-embedding inv phi e e f)
		         (id-embedding e f))
                  (equal (comp-embedding phi inv k k f)
		         (id-embedding k f)))))
  :hints (("Goal" :use (embeddingp-inv-embedding comp-inv-embedding-2 comp-inv-embedding-4))))

(defthmd embed-embedding-inv
  (implies (and (extensionp e f) (extensionp k f) (iso-embeddingp phi e k f)
		(feltp x e))
	   (equal (embed (embed x phi k f) (inv-embedding phi e k f) e f)
	          x))
  :hints (("Goal" :in-theory (enable id-embedding-id)
                  :use (comp-inv-embedding
                        (:instance embeddingp-comp-embedding (psi (inv-embedding phi e k f)) (g k) (k e))))))

(defthmd embed-inv-embedding
  (implies (and (extensionp e f) (extensionp k f) (iso-embeddingp phi e k f)
		(feltp x k))
	   (equal (embed (embed x (inv-embedding phi e k f) e f) phi k f)
	          x))
  :hints (("Goal" :in-theory (enable id-embedding-id)
                  :use (comp-inv-embedding
                        (:instance embeddingp-comp-embedding (phi (inv-embedding phi e k f)) (psi phi) (e k) (g e))))))

(defthmd pembed-embedding-inv
  (implies (and (extensionp e f) (extensionp k f) (iso-embeddingp phi e k f)
		(polyp p e))
	   (equal (pembed (pembed p phi k f) (inv-embedding phi e k f) e f)
	          p))
  :hints (("Goal" :in-theory (enable id-embedding-id)
                  :use (comp-inv-embedding
                        (:instance pembed-comp-embedding (psi (inv-embedding phi e k f)) (g k) (k e))))))

(defthmd pembed-inv-embedding
  (implies (and (extensionp e f) (extensionp k f) (iso-embeddingp phi e k f)
		(polyp p k))
	   (equal (pembed (pembed p (inv-embedding phi e k f) e f) phi k f)
	          p))
  :hints (("Goal" :in-theory (enable id-embedding-id)
                  :use (comp-inv-embedding
                        (:instance pembed-comp-embedding (phi (inv-embedding phi e k f)) (psi phi) (e k) (g e))))))


;;-------------------------------------------------------

;; We shall construct a list of all embeddings of e in k over f.
;; First, given an embedding phi of (cdr e) in k over f, construct a list of all embeddings of e in
;; k that extend phi:

(defun consl (l x)
  (if (consp l)
      (cons (cons (car l) x)
            (consl (cdr l) x))
    ()))

(defun simple-embedding-extensions (phi e k f)
  (consl (proots (pembed (car e) phi k f) k)
         phi))

;; Given a list l of embeddings of (cdr e) in k over f, construct a list of all embeddings of e in
;; k that extend a member of l:

(defun simple-embeddings-extensions (l e k f)
  (if (consp l)
      (append (simple-embedding-extensions (car l) e k f)
              (simple-embeddings-extensions (cdr l) e k f))
    ()))

;; A list of all embeddings of e in k over f:

(defun embeddings (e k f)
  (if (and (consp e) (not (equal e f)))
      (simple-embeddings-extensions (embeddings (cdr e) k f) e k f)
    (list ())))

;; (embeddings e k f) is a dlist of all embeddings of e in k over f:

(local-defthmd dlistp-embeddings-1
  (implies (member (cons x c) (consl r c))
           (member x r)))

(local-defthmd dlistp-embeddings-2
  (implies (dlistp r)
           (dlistp (consl r c)))	   
  :hints (("Subgoal *1/2" :use ((:instance dlistp-embeddings-1 (x (car r)) (r (cdr r)))))))

(local-defthmd dlistp-embeddings-3
  (implies (member x (consl r c))
           (equal (cdr x) c)))

(local-defthmd dlistp-embeddings-4
  (implies (member x (simple-embedding-extensions c e k f))
           (equal (cdr x) c))
  :hints (("Goal" :use ((:instance dlistp-embeddings-3 (r (PROOTS (PEMBED (CAR E) C K F) K)))))))

(local-defthmd dlistp-embeddings-5
  (implies (member x (simple-embeddings-extensions l e k f))
           (member (cdr x) l))
  :hints (("Subgoal *1/3" :use ((:instance dlistp-embeddings-4 (c (car l)))))))

(local-defthmd dlistp-embeddings-6
  (implies (and (dlistp l) (consp l))
           (disjointp (simple-embedding-extensions (car l) e k f)
	              (simple-embeddings-extensions (cdr l) e k f)))
  :hints (("Goal" :in-theory (disable common-member-shared)
                  :use ((:instance dlistp-embeddings-5
                          (l (cdr l))
                          (x (common-member (simple-embedding-extensions (car l) e k f)
			                    (simple-embeddings-extensions (cdr l) e k f))))
			(:instance dlistp-embeddings-4
                          (c (car l))
                          (x (common-member (simple-embedding-extensions (car l) e k f)
			                    (simple-embeddings-extensions (cdr l) e k f))))
			(:instance common-member-shared (l (simple-embedding-extensions (car l) e k f))
			                                (m (simple-embeddings-extensions (cdr l) e k f)))))))

(local-defthmd dlistp-embeddings-7
  (dlistp (simple-embedding-extensions phi e k f))
  :hints (("Goal" :use ((:instance dlistp-embeddings-2 (r (proots (pembed (car e) phi k f) k)) (c phi))
                        (:instance dlistp-proots (p (pembed (car e) phi k f)) (f k))))))

(local-defthmd dlistp-embeddings-8
  (implies (dlistp l)
           (dlistp (simple-embeddings-extensions l e k f)))
  :hints (("Subgoal *1/2" :use (dlistp-embeddings-6
                                (:instance dlistp-embeddings-7 (phi (car l)))
				(:instance dlistp-append (l (simple-embedding-extensions (car l) e k f))
				                         (m (simple-embeddings-extensions (cdr l) e k f)))))))

(defthmd dlistp-embeddings
  (dlistp (embeddings e k f)))


(in-theory (disable simple-embedding-extensions))

(local-defthmd all-embeddings-1
  (implies (member x l)
           (sublistp (simple-embedding-extensions x e k f)
	             (simple-embeddings-extensions l e k f))))

(local-defthmd all-embeddings-2
  (implies (and (consp phi) (member (car phi) r))
           (member phi (consl r (cdr phi)))))

(defthm len-pembed
  (equal (len (pembed p phi k f))
         (len p)))

(local-defthmd all-embeddings-3
  (implies (and (extensionp e f) (extensionp k f) (not (equal e f))
                (embeddingp phi e k f))
	   (member (car phi) (proots (pembed (car e) (cdr phi) k f) k)))
  :hints (("Goal" :expand ((fieldp e) (embeddingp phi e k f))
                  :use ((:instance member-proots (x (car phi)) (p (pembed (car e) (cdr phi) k f)) (f k))
		        (:instance polyp-pembed (e (cdr e)) (p (car e)) (phi (cdr phi)))
		        (:instance monicp-pembed (e (cdr e)) (p (car e)) (phi (cdr phi)))))))

(local-defthmd all-embeddings-4
  (implies (and (extensionp e f) (extensionp k f) (not (equal e f))
                (embeddingp phi e k f))
	   (member phi (simple-embedding-extensions (cdr phi) e k f)))
  :hints (("Goal" :in-theory (enable simple-embedding-extensions)
                  :use (all-embeddings-3
                        (:instance all-embeddings-2 (r (proots (pembed (car e) (cdr phi) k f) k)))))))

(local-defthmd all-embeddings-5
  (implies (and (extensionp e f) (extensionp k f) (not (equal e f))
                (embeddingp phi e k f) (member (cdr phi) (embeddings (cdr e) k f)))
	   (member phi (embeddings e k f)))
  :hints (("Goal" :use (all-embeddings-4
                        (:instance all-embeddings-1 (x (cdr phi)) (l (embeddings (cdr e) k f)))))))

(local-defthmd all-embeddings-6
  (implies (and (extensionp e f) (extensionp k f)
	        (embeddingp phi e k f))
	   (member phi (embeddings e k f)))
  :hints (("Goal" :induct (embeddingp phi e k f))
          ("Subgoal *1/2" :use (all-embeddings-5))))

(local-defthmd all-embeddings-7
  (implies (member phi (consl r c))
           (and (consp phi)
	        (member (car phi) r)
		(equal (cdr phi) c))))

(local-defthmd all-embeddings-8
  (implies (member phi (simple-embedding-extensions c e k f))
           (and (consp phi)
	        (member (car phi) (proots (pembed (car e) c k f) k))
		(equal (cdr phi) c)))
  :hints (("Goal" :in-theory (enable simple-embedding-extensions)
                  :use ((:instance all-embeddings-7 (r (proots (pembed (car e) c k f) k)))))))

(local-defthmd all-embeddings-9
  (implies (member phi (simple-embeddings-extensions l e k f))
           (member (cdr phi) l))
  :hints (("Subgoal *1/3" :use ((:instance all-embeddings-8 (c (car l)))))))

(local-defthmd all-embeddings-10
  (implies (and (dlistp l) (member phi (simple-embeddings-extensions l e k f)))
           (and (member phi (simple-embedding-extensions (cdr phi) e k f))
		(member (cdr phi) l)))
  :hints (("Subgoal *1/3" :use ((:instance all-embeddings-8 (c (car l)))))
          ("Subgoal *1/2" :use ((:instance all-embeddings-8 (c (car l)))
	                        (:instance all-embeddings-9 (l (cdr l)))))))

(local-defthmd all-embeddings-11
  (implies (and (extensionp e f) (extensionp k f) (not (equal e f))
                (member phi (embeddings e k f)))
	   (and (consp phi)
	        (member (cdr phi) (embeddings (cdr e) k f))
		(member (car phi) (proots (pembed (car e) (cdr phi) k f) k))))
  :hints (("Goal" :use ((:instance all-embeddings-8 (c (cdr phi)))
                        (:instance all-embeddings-10 (l (embeddings (cdr e) k f)))))))

(defthm member-felts
  (implies (and (feltsp p f) (member x p))
           (feltp x f)))

(local-defthmd all-embeddings-12
  (implies (and (extensionp e f) (extensionp k f) (not (equal e f))
                (member phi (embeddings e k f))
		(embeddingp (cdr phi) (cdr e) k f))
	   (and (consp phi)
	        (member (cdr phi) (embeddings (cdr e) k f))
		(feltp (car phi) k)
		(prootp (car phi) (pembed (car e) (cdr phi) k f) k)))
  :hints (("Goal" :in-theory (enable fieldp)
                  :use (all-embeddings-11
                        (:instance member-proots (f k) (x (car phi)) (p (pembed (car e) (cdr phi) k f)))
			(:instance feltsp-proots (p (pembed (car e) (cdr phi) k f)) (f k))
		        (:instance polyp-pembed (e (cdr e)) (p (car e)) (phi (cdr phi)))
		        (:instance monicp-pembed (e (cdr e)) (p (car e)) (phi (cdr phi)))))))

(local-defthmd all-embeddings-13
  (implies (and (extensionp e f) (extensionp k f) (not (equal e f))
                (member phi (embeddings e k f))
		(implies (member (cdr phi) (embeddings (cdr e) k f))
		         (embeddingp (cdr phi) (cdr e) k f)))
	   (embeddingp phi e k f))
  :hints (("Goal" :in-theory (enable embeddingp)
                  :use (all-embeddings-11 all-embeddings-12))))

(in-theory (disable embeddings embeddingp))

(local-defun embeddingp-induct (e phi f)
  (declare (irrelevant phi))
  (if (and (extensionp e f) (not (equal e f)))
      (embeddingp-induct (cdr e) (cdr phi) f)
    ()))

(local-defthmd all-embeddings-14
  (implies (and (extensionp e f) (extensionp k f)
                (member phi (embeddings e k f)))
	   (embeddingp phi e k f))
  :hints (("Goal" :induct (embeddingp-induct e phi f))  
          ("Subgoal *1/2" :in-theory (enable embeddingp embeddings))
          ("Subgoal *1/1" :use (all-embeddings-13))))

(defthmd all-embeddings
  (implies (and (extensionp e f) (extensionp k f))
	   (iff (member phi (embeddings e k f))
	        (embeddingp phi e k f)))
  :hints (("Goal" :use (all-embeddings-6 all-embeddings-14))))

;; The number of embeddings of e in k over f is at most the degree of e over f:

(local-defthm len-consl
  (equal (len (consl r x))
         (len r)))

(local-defthmd len-embeddings-1
  (implies (and (extensionp e f) (extensionp k f) (not (equal e f))
                (embeddingp phi (cdr e) k f))
	   (<= (len (simple-embedding-extensions phi e k f))
	       (degree (car e))))
  :hints (("Goal" :in-theory (enable simple-embedding-extensions fieldp)
                  :use ((:instance len-proots-bound (p (pembed (car e) phi k f)) (f k))
		        (:instance polyp-pembed (e (cdr e)) (p (car e)) (phi phi))
		        (:instance monicp-pembed (e (cdr e)) (p (car e)) (phi phi))))))

(local-defthmd len-embeddings-2
  (implies (and (extensionp e f) (extensionp k f) (not (equal e f))
                (sublistp l (embeddings (cdr e) k f)))
           (<= (len (simple-embeddings-extensions l e k f))
	       (* (len l) (degree (car e)))))
  :hints (("Subgoal *1/1" :use ((:instance all-embeddings (e (cdr e)) (phi (car l)))
                                (:instance len-embeddings-1 (phi (car l)))))))

(in-theory (disable len-ebasis0))

(local-defthmd len-embeddings-3
  (implies (and (extensionp e f) (extensionp k f) (not (equal e f))
                (<= (len (embeddings (cdr e) k f))
		    (edegree (cdr e) f)))
	   (<= (len (embeddings e k f))
	       (edegree e f)))
  :hints (("Goal" :expand ((fieldp e) (embeddings e k f) (edegree e f))
                  :nonlinearp t
                  :use ((:instance len-embeddings-2 (l (embeddings (cdr e) k f)))))))

(defthmd len-embeddings
  (implies (and (extensionp e f) (extensionp k f))
	   (<= (len (embeddings e k f))
	       (edegree e f)))
  :hints (("Subgoal *1/1" :expand (embeddings e k e))
          ("Subgoal *1/2" :use (len-embeddings-3))))

;;--------------------------------------------------------------------------------------------------------------------------

;; Afterthoughts:

(defthmd min-poly-divides-min-poly-plift
  (implies (and (extensionp e d) (extensionp d f) (feltp x e))
           (pdivides (min-poly x e d)
	             (plift (min-poly x e f) f d)
		     d))
  :hints (("Goal" :in-theory (enable polyp-plift)
                  :use (prootp-min-poly extends-trans
                        (:instance min-poly-pdivides (f d) (q (plift (min-poly x e f) f d)))))))

;; If d is an intermediate field between e and f, then (min-poly (flift x d e) e f) = (min-poly x d f).  To prove this, note that

;;    (peval (plift (min-poly x d f) f e) (flift x d e) e)
;;      = (peval (plift (plift (min-poly x d f) f d) d e) (flift x d e) e)  [plift-comp] 
;;      = (flift (peval (plift (min-poly x d f) f d) x d) d e)              [flift-peval]
;;      = (flift (fzero d) d e)                                             [prootp-min-poly, def of prootp]
;;      = (fzero e)                                                         [flift-id]

;; Thus, (flift x d e) is a root of (plift (min-poly x d f) f e) e), and by min-poly-pdivides, (min-poly (flift x d e) e f) divides
;; (min-poly x d f).  Since both polynomials are monic and irreducible, they are equal according to irreduciblep-no-factor,
;; pdivides-monic-equal, and pdivides-degree:

(in-theory (enable polyp-plift))

(defthmd pembed-min-poly
  (implies (and (extensionp e f) (extensionp k f) (embeddingp phi e k f)
                (feltp x e))
	   (equal (min-poly (embed x phi k f) k f)
	          (min-poly x e f)))
  :hints (("Goal" :in-theory (enable polyp-plift prootp)
                  :use (prootp-min-poly embed-fzero-fone
		        (:instance peval-pembed (p (plift (min-poly x e f) f e)))
		        (:instance pembed-fixes (p (min-poly x e f)))
			(:instance prootp-min-poly (x (embed x phi k f)) (e k))
			(:instance min-poly-pdivides (e k) (x (embed x phi k f)) (q (min-poly x e f)))
			(:instance irreduciblep-pdivides-monic-equal (x (min-poly (embed x phi k f) k f)) (y (min-poly x e f)))))))

(local-defthmd min-poly-flift-min-poly-1
  (implies (and (extensionp e d) (extensionp d f) (feltp x d))
           (equal (peval (plift (min-poly x d f) f e) (flift x d e) e)
	          (flift (peval (plift (min-poly x d f) f d) x d) d e)))
  :hints (("Goal" :use ((:instance plift-comp (x (min-poly x d f)))
                        (:instance flift-peval (p (plift (min-poly x d f) f d)) (f d))
			(:instance prootp-min-poly (e d))))))

(local-defthmd min-poly-flift-min-poly-2
  (implies (and (extensionp e d) (extensionp d f) (feltp x d))
           (equal (peval (plift (min-poly x d f) f d) x d)
	          (fzero d)))
  :hints (("Goal" :in-theory (enable prootp)
                  :use ((:instance prootp-min-poly (e d))))))

(local-defthmd min-poly-flift-min-poly-3
  (implies (and (extensionp e d) (extensionp d f) (feltp x d))
           (prootp (flift x d e) (plift (min-poly x d f) f e) e))
  :hints (("Goal" :in-theory (enable prootp)
                  :use (min-poly-flift-min-poly-1 min-poly-flift-min-poly-2))))

(local-defthmd min-poly-flift-min-poly-4
  (implies (and (extensionp e d) (extensionp d f) (feltp x d))
           (pdivides (min-poly (flift x d e) e f)
	             (min-poly x d f)
		     f))
  :hints (("Goal" :use (min-poly-flift-min-poly-3 extends-trans
                        (:instance min-poly-pdivides (x (flift x d e)) (q (min-poly x d f)))
			(:instance prootp-min-poly (e d))))))

(defthmd min-poly-flift-min-poly
  (implies (and (extensionp e d) (extensionp d f) (feltp x d))
           (equal (min-poly (flift x d e) e f)
	          (min-poly x d f)))
  :hints (("Goal" :use (min-poly-flift-min-poly-4 extends-trans
                        (:instance prootp-min-poly (e d))
			(:instance prootp-min-poly (x (flift x d e)))
			(:instance irreduciblep-no-factor (x (min-poly (flift x d e) e f)) (p (min-poly x d f)))
			(:instance pdivides-degree (x (min-poly (flift x d e) e f)) (y (min-poly x d f)))
			(:instance pdivides-monic-equal (x (min-poly (flift x d e) e f)) (y (min-poly x d f)))
			(:instance pdivides-equal-degree (x (min-poly (flift x d e) e f)) (y (min-poly x d f)))))))

(defthmd derivative-pembed
  (implies (and (extensionp e f) (extensionp k f) (embeddingp phi e k f)
                (polyp p e))
	   (equal (derivative (pembed p phi k f) k)
	          (pembed (derivative p e) phi k f)))
  :hints (("Goal" :use ((:functional-instance derivative-phom
                         (hom (lambda (x) (if (and (extensionp e f) (extensionp k f) (embeddingp phi e k f)) (embed x phi k f) (hom x))))
			 (fld1 (lambda () (if (and (extensionp e f) (extensionp k f) (embeddingp phi e k f)) e (fld1))))
			 (fld2 (lambda () (if (and (extensionp e f) (extensionp k f) (embeddingp phi e k f)) k (fld2))))
			 (phom (lambda (p) (if (and (extensionp e f) (extensionp k f) (embeddingp phi e k f)) (pembed p phi k f) (phom p)))))))))

(defthmd pdivides-pembed
  (implies (and (extensionp e f) (extensionp k f) (embeddingp phi e k f)
                (polyp x e) (polyp y e) (not (equal y (pzero e))))
	   (iff (pdivides (pembed y phi k f) (pembed x phi k f) k)
	        (pdivides y x e)))
  :hints (("Goal" :use ((:functional-instance pdivides-phom
                         (hom (lambda (x) (if (and (extensionp e f) (extensionp k f) (embeddingp phi e k f)) (embed x phi k f) (hom x))))
			 (fld1 (lambda () (if (and (extensionp e f) (extensionp k f) (embeddingp phi e k f)) e (fld1))))
			 (fld2 (lambda () (if (and (extensionp e f) (extensionp k f) (embeddingp phi e k f)) k (fld2))))
			 (phom (lambda (p) (if (and (extensionp e f) (extensionp k f) (embeddingp phi e k f)) (pembed p phi k f) (phom p)))))))))

(defthmd reduciblep-pembed
  (implies (and (extensionp e f) (extensionp k f) (embeddingp phi e k f)
                (polyp x e) (reduciblep x e))
	   (reduciblep (pembed x phi k f) k))
  :hints (("Goal" :in-theory (enable irreduciblep reduciblep)
                  :use ((:instance pdivides-pembed (y (pfactor x e)))
		        (:instance polyp-pembed (p x))
		        (:instance polyp-pembed (p (pfactor x e)))
		        (:instance irreduciblep-no-factor (f k) (x (pembed (pfactor x e) phi k f)) (p (pembed x phi k f)))))))

(local-defthmd inv-inv-embedding-1
  (implies (and (extensionp e f) (extensionp k f) (iso-embeddingp phi e k f))
	   (equal (comp-embedding phi (comp-embedding (inv-embedding phi e k f) (inv-embedding (inv-embedding phi e k f) k e f) e e f) e k f)
	          phi))
  :hints (("Goal" :use (comp-inv-embedding comp-id-embedding
                        (:instance comp-inv-embedding (phi (inv-embedding phi e k f)) (e k) (k e))))))

(defthmd inv-inv-embedding
  (implies (and (extensionp e f) (extensionp k f) (iso-embeddingp phi e k f))
	   (equal (inv-embedding (inv-embedding phi e k f) k e f)
	          phi))
  :hints (("Goal" :use (comp-inv-embedding comp-id-embedding
                        (:instance comp-inv-embedding (phi (inv-embedding phi e k f)) (e k) (k e))
			(:instance comp-embedding-assoc (phi1 (inv-embedding (inv-embedding phi e k f) k e f)) (phi2 (inv-embedding phi e k f)) (phi3 phi)
			                                (e1 e) (e2 k) (e3 e) (e4 k))
			(:instance comp-id-embedding (phi (inv-embedding (inv-embedding phi e k f) k e f)))))))

;;-------------------------------------

;; Let e be an extension of k.  Let m be a unary predicate that recognizes a subset of e that includes all elements of e that are lifted 
;; from f and is closed under the field operations on e.  Thus, m satisfies the following properties:

;;  (1) (implies (m x) (feltp x e))
;;  (2) (implies (feltp x f) (m (flift x f e)))
;;  (3) (implies (and (m x) (m y)) (and (m (fadd x y e)) (m (fmul x y e))))

;; Informally, we shall refer to m as an intermediate metafield between e and f. We would like to identify an intermediate field k between
;; e and f that corresponds to m, i.e., that satisfies

;;     (iff (m x) (fliftedp x k e)).

;; In general, of course, no such intermediate field k exists.  However, there exists an extension of f that is isomorphic to e and does
;; contain an intermediate field corresponding to m.  That is, we can construct an extension d of f with an intermediate field k and an
;; isomorphism phi from d to e over f such that the image of k under phi is the metafield defined by m, i.e., satisfying

;;     (implies (feltp x d)
;;              (iff (m (embed x phi e f))
;;                   (fliftedp x k d)))

;; As a basis for proving this result, we constrain a field extension e$ over f$ and a metafield m$ to satisfy (1) - (3) above:

(local (in-theory (enable feltp beltp bmul badd)))

(encapsulate (((e$) => *) ((f$) => *) ((m$ *) => *))
   (local (defun e$ () 0))
   (local (defun f$ () 0))
   (local (defun m$ (x) (feltp x 0)))
   (defthmd extensionp-e$-f$
     (extensionp (e$) (f$)))
   (defthm e$-includes-m$
     (implies (m$ x) (feltp x (e$))))
   (defthm m$-includes-f$
     (implies (feltp x (f$)) (m$ (flift x (f$) (e$)))))
   (defthm m$-closed
     (implies (and (m$ x) (m$ y))
              (and (m$ (fadd x y (e$))) (m$ (fmul x y (e$)))))))

;; Our objective is to define fields d$ and k$ and an embedding phi$ that satisfy the following:

;;    (and (extensionp (d$) (k$)) (extensionp (k$) (f$))
;;         (iso-embeddingp (phi$) (d$) (e$) (f$))
;;         (implies (feltp x (d$))
;;                  (iff (m$ (embed x (phi$) (e$) (f$)))
;;                       (fliftedp x (k$) (d$)))))

;; Let d be an extension of f$ and phi an embedding of d in e$ over f$. The following predicate holds iff y is in the range of phi:

(defund in-range-p (y phi d e f)
  (let ((x (preembed y phi d e f)))
    (and (feltp x d)
         (equal (embed x phi e f)
                y))))

(defthmd in-range-p-lemma
  (implies (and (feltp x d)
                (equal (embed x phi e f)
                       y))
	   (in-range-p y phi d e f))
  :hints (("Goal" :in-theory (enable in-range-p)
                  :use ((:instance preembed  (e d) (k e))))))

;; The following predicate holds when the range of phi is included in m$:

(defun-sk m$-includes-range (phi d)
  (forall (y)
    (implies (in-range-p y phi d (e$) (f$))
             (m$ y))))             

(defthmd m$-includes-range-lemma
  (implies (and (m$-includes-range phi d)
                (in-range-p y phi d (e$) (f$)))
	   (m$ y))
  :hints (("Goal" :use (m$-includes-range-necc))))

(defthmd m$-includes-range-witness-lemma
  (let ((y (m$-includes-range-witness phi d)))
    (implies (implies (in-range-p y phi d (e$) (f$)) (m$ y))
             (m$-includes-range phi d))))

;; The following predicate holds when m$ is included in the range of phi:

(defun-sk range-includes-m$ (phi d)
  (forall (y)
    (implies (m$ y)
             (in-range-p y phi d (e$) (f$)))))

(defthmd range-includes-m$-lemma
  (implies (and (range-includes-m$ phi d)
                (m$ y))
	   (in-range-p y phi d (e$) (f$)))	   
  :hints (("Goal" :use (range-includes-m$-necc))))

(defthmd range-includes-m$-witness-lemma
  (let ((y (range-includes-m$-witness phi d)))
    (implies (implies (m$ y) (in-range-p y phi d (e$) (f$)))
             (range-includes-m$ phi d))))

;; Suppose y is an element of e$ outside of the range of phi.  Let p = (min-poly y (e$) (f$)) and let p' = (plift p (f$) d).  Since y 
;; is a root of (plift p (f$) (e$)) = (pembed p' phi (e$) (f$)), there exists an irreducible monic factor q of p' such that y is a 
;; root of (pembed q phi (e$) (f$)).  Since y is not in the range of phi, (degree q) > 1.  Such a polynomial q is identified by the
;; function extension-poly:

(defun extension-poly-aux (l y phi e f)
  (if (consp l)
      (if (prootp y (pembed (car l) phi e f) e)
          (car l)
	(extension-poly-aux (cdr l) y phi e f))
    ()))

(defun extension-poly (y phi d e f)
  (extension-poly-aux (factorization (plift (min-poly y e f) f d) d) y phi e f))

;; An extension d' of d may be constructed by adjoining a root of this polynomial, and phi may be extended to an embedding of d' in e$:

(local-defthmd epe-1
  (implies (and (extensionp d (f$))
                (embeddingp phi d (e$) (f$))
		(feltp x (f$)))
	   (in-range-p (flift x (f$) (e$)) phi d (e$) (f$)))
  :hints (("Goal" :in-theory (enable in-range-p)
                  :use (extensionp-e$-f$
                        (:instance embed-fixes (e d) (k (e$)) (f (f$)))
                        (:instance preembed (x (flift x (f$) d)) (y (flift x (f$) (e$))) (e d) (k (e$)) (f (f$)))))))

(local-defthmd epe-2
  (implies (and (extensionp d (f$))
                (embeddingp phi d (e$) (f$))
		(m$ y)
		(not (in-range-p y phi d (e$) (f$))))
	   (not (fliftedp y (f$) (e$))))
  :hints (("Goal" :use (extensionp-e$-f$
                        (:instance epe-1 (x (fdrop y (e$) (f$))))
                        (:instance flift-fdrop (x y) (f (f$)) (e (e$)))))))

(local-defun mp (y d)
  (plift (min-poly y (e$) (f$)) (f$) d))

(local-defthmd epe-3
  (implies (and (extensionp d (f$))
                (embeddingp phi d (e$) (f$))
		(m$ y)
		(not (in-range-p y phi d (e$) (f$))))
	   (prootp y (pembed (mp y d) phi (e$) (f$)) (e$)))
  :hints (("Goal" :use (extensionp-e$-f$
                        (:instance pembed-fixes (p (min-poly y (e$) (f$))) (f (f$)) (e d) (k (e$)))
                        (:instance prootp-min-poly (x y) (e (e$)) (f (f$)))))))

(local-defthmd epe-4
  (implies (and (extensionp d (f$))
                (embeddingp phi d (e$) (f$))
		(m$ y)
		(not (in-range-p y phi d (e$) (f$))))
	   (and (polyp (mp y d) d)
	        (monicp (mp y d) d)
		(> (degree (mp y d)) 1)))
  :hints (("Goal" :in-theory (enable fliftedp polyp-plift)
                  :use (extensionp-e$-f$ epe-2
		        (:instance monicp-plift (p (min-poly y (e$) (f$))) (f (f$)) (e d))
                        (:instance prootp-min-poly (x y) (e (e$)) (f (f$)))))))

(local-defthmd epe-5
  (implies (and (extensionp d (f$))
                (embeddingp phi d (e$) (f$))
		(m$ y)
		(not (in-range-p y phi d (e$) (f$))))
           (and (monicp-irreduciblep-listp (factorization (mp y d) d) d)
	        (equal (pmul-list (factorization (mp y d) d) d)
		       (mp y d))))
  :hints (("Goal" :use (extensionp-e$-f$ epe-4
                        (:instance pmul-list-irreduciblep-factorization (p (mp y d)) (f d))))))

(local-defthm peval-pone
  (implies (and (fieldp f) (feltp x f))
           (equal (peval (pone f) x f)
	          (fone f)))
  :hints (("Goal" :in-theory (enable pconstp pone)
                  :use ((:instance peval-pconstp (p (pone f)))))))

(local-defthmd epe-6
  (implies (and (extensionp d (f$))
                (embeddingp phi d (e$) (f$))
		(m$ y)
		(not (in-range-p y phi d (e$) (f$)))
                (monicp-irreduciblep-listp l d)
	        (prootp y (pembed (pmul-list l d) phi (e$) (f$)) (e$)))
	   (let ((q (extension-poly-aux l y phi (e$) (f$))))
	     (and (member q l)
	          (prootp y (pembed q phi (e$) (f$)) (e$)))))
  :hints (("Goal" :induct (len l))
          ("Subgoal *1/2" :in-theory (enable prootp pembed-id)
	                  :use (extensionp-e$-f$))
	  ("Subgoal *1/1" ;:in-theory (enable polyp-pembed)
	                  :use (extensionp-e$-f$
	                        (:instance prootp-pmul (x y) (f (e$))
				                       (p (pembed (car l) phi (e$) (f$)))
				                       (q (pembed (pmul-list (cdr l) d) phi (e$) (f$))))
				(:instance pembed-pmul (e d) (k (e$)) (f (f$)) (p (car l)) (q (pmul-list (cdr l) d)))
				(:instance polyp-pembed (p (car l)) (e d) (k (e$)) (f (f$)))
				(:instance polyp-pembed (p (pmul-list (cdr l) d)) (e d) (k (e$)) (f (f$)))))))

(local-defthmd epe-7
  (implies (and (extensionp d (f$))
                (embeddingp phi d (e$) (f$))
		(m$ y)
		(not (in-range-p y phi d (e$) (f$))))
	   (let ((q (extension-poly y phi d (e$) (f$))))
	     (and (member q (factorization (mp y d) d))
	          (prootp y (pembed q phi (e$) (f$)) (e$)))))
  :hints (("Goal" :in-theory (enable extension-poly)
                  :use (epe-3 epe-5 (:instance epe-6 (l (factorization (mp y d) d)))))))

(in-theory (disable extension-poly))

(local-defthmd epe-8
  (implies (and (extensionp d (f$))
                (embeddingp phi d (e$) (f$))
		(m$ y)
		(not (in-range-p y phi d (e$) (f$))))
	   (let ((q (extension-poly y phi d (e$) (f$))))
	     (and (polyp q d)
                  (irreduciblep q d)
                  (monicp q d)
	          (>= (degree q) 1)
	          (prootp y (pembed q phi (e$) (f$)) (e$)))))
  :hints (("Goal" :use (epe-3 epe-5 epe-7
			(:instance member-monicp-irreduciblep-listp (p (extension-poly y phi d (e$) (f$))) (f d) (l (factorization (mp y d) d)))))))

(local-defthmd epe-9
  (implies (and (fieldp f) (polyp p f) (monicp p f) (= (degree p) 1) (feltp x f) (prootp x p f))
           (equal (root-poly x f) p))
  :hints (("Goal" :use (monicp-irreduciblep-root-poly prootp-pdivides
                        (:instance pdivides-equal-degree (x (root-poly x f)) (y p))
			(:instance pdivides-monic-equal (x (root-poly x f)) (y p))))))

(local-defthmd epe-10
  (implies (and (fieldp f) (polyp p f) (monicp p f) (= (degree p) 1) (feltp x f) (prootp x p f))
           (equal (cadr p) (fneg x f)))
  :hints (("Goal" :in-theory (enable root-poly) :use (epe-9))))

(local-defthmd epe-11
  (implies (and (extensionp d f) (extensionp e f) (embeddingp phi d e f)
                (feltp y e)
		(polyp q d)
                (monicp q d)
	        (= (degree q) 1)
	        (prootp y (pembed q phi e f) e))
	   (equal (embed (cadr q) phi e f)
	          (fneg y e)))
  :hints (("Goal" :use ((:instance epe-10 (x y) (f e) (p (pembed q phi e f)))
		        (:instance monicp-pembed (p q) (e d) (k e))
		        (:instance polyp-pembed (p q) (e d) (k e))))))

(local-defthmd epe-12
  (implies (and (extensionp d f) (extensionp e f) (embeddingp phi d e f)
                (feltp y e)
		(polyp q d)
                (monicp q d)
	        (= (degree q) 1)
	        (prootp y (pembed q phi e f) e))
	   (and (feltp (fneg (cadr q) d) d)
	        (equal (embed (fneg (cadr q) d) phi e f)
	               y)))
  :hints (("Goal" :in-theory (enable polyp)
                  :use (epe-11
                        (:instance embed-fneg (x (cadr q)) (e d) (k e))))))

(local-defthmd epe-13
  (implies (and (extensionp d (f$))
                (embeddingp phi d (e$) (f$))
		(m$ y)
		(polyp q d)
                (monicp q d)
	        (= (degree q) 1)
	        (prootp y (pembed q phi (e$) (f$)) (e$)))
	   (in-range-p y phi d (e$) (f$)))
  :hints (("Goal" :in-theory (enable in-range-p)
                  :use (extensionp-e$-f$
                        (:instance epe-12 (f (f$)) (e (e$)))
                        (:instance preembed (x (fneg (cadr q) d)) (e d) (k (e$)) (f (f$)))))))

(local-defthmd epe-14
  (implies (and (extensionp d (f$))
                (embeddingp phi d (e$) (f$))
		(m$ y)
		(not (in-range-p y phi d (e$) (f$))))
	   (let ((q (extension-poly y phi d (e$) (f$))))
	     (and (polyp q d)
                  (irreduciblep q d)
                  (monicp q d)
	          (> (degree q) 1)
	          (prootp y (pembed q phi (e$) (f$)) (e$)))))
  :hints (("Goal" :use (epe-8 
			(:instance epe-13 (q (extension-poly y phi d (e$) (f$))))))))
			        
(local-defthmd epe-15
  (implies (and (extensionp d (f$))
                (embeddingp phi d (e$) (f$))
		(m$ y)
		(not (in-range-p y phi d (e$) (f$))))
	   (embeddingp (cons y phi)
	               (cons (extension-poly y phi d (e$) (f$)) d)
		       (e$)
		       (f$)))
  :hints (("Goal" :in-theory (enable embeddingp)
                  :use (epe-14
		        (:instance len-extends (e d) (f (f$)))))))

(local-defthmd epe-16
  (implies (and (extensionp d (f$))
                (embeddingp phi d (e$) (f$))
		(m$ y)
		(not (in-range-p y phi d (e$) (f$))))
	   (fieldp (cons (extension-poly y phi d (e$) (f$)) d)))
  :hints (("Goal" :in-theory (enable fieldp)
                  :use (epe-14))))

(local-defthmd epe-17
  (implies (and (extensionp d (f$))
                (embeddingp phi d (e$) (f$))
		(m$ y)
		(not (in-range-p y phi d (e$) (f$))))
	   (extensionp (cons (extension-poly y phi d (e$) (f$)) d)
	               (f$)))
  :hints (("Goal" :use (epe-16))))

(defthmd extensionp-extension-poly
  (implies (and (extensionp d (f$))
                (embeddingp phi d (e$) (f$))
		(m$ y)
		(not (in-range-p y phi d (e$) (f$))))
           (let* ((q (extension-poly y phi d (e$) (f$)))
	          (d1 (cons q d))
		  (phi1 (cons y phi)))
	     (and (extensionp d1 d)
		  (embeddingp phi1 d1 (e$) (f$)))))
  :hints (("Goal" :use (epe-15 epe-17))))

;; Now suppose m$ includes the range of phi.  We shall show that m$ also includes the range of phi'.  Let x be an element of d1.
;; Then (polyp x d) and

;;    (embed x phi' (e$) (f$)) = (peval (pembed x phi (e$) (f$)) y (e$)).

;; Since m$ includes the range of phi, m$ includes the coefficients of (pembed x phi (e$) (f$)), and it follows that m$ contains
;; (embed x phi' (e$) (f$)):

(local-defun m$-list (p)
  (if (consp p)
      (and (m$ (car p))
           (m$-list (cdr p)))
    t))
			        
(local-defthmd epe-18
  (implies (and (extensionp d (f$))
                (embeddingp phi d (e$) (f$))
		(m$-includes-range phi d)
		(feltsp p d))
	   (m$-list (pembed p phi (e$) (f$))))
  :hints (("Goal" :induct (len p))
          ("Subgoal *1/1" :expand ((PEMBED P PHI (E$) (F$)))
	                  :in-theory (enable in-range-p)
	                  :use ((:instance m$-includes-range-lemma (y (EMBED (CAR P) PHI (E$) (F$))))
                                (:instance preembed (x (car p)) (y (EMBED (CAR P) PHI (E$) (F$))) (e d) (k (e$)) (f (f$)))))))

(local-defthm epe-19
  (implies (and (m$ y) (natp n))
           (m$ (fpower y n (e$))))
  :hints (("Subgoal *1/1" :use (extensionp-e$-f$ (:instance m$-includes-f$ (x (fone (f$))))))))

(local-defthm epe-20
  (m$ (fzero (e$)))
  :hints (("Goal" :use (extensionp-e$-f$ (:instance m$-includes-f$ (x (fzero (f$))))))))

(local-defthmd epe-21
  (implies (and (m$ y) (m$-list p))
           (m$ (feval p y (e$)))))

(defthmd m$-peval-pembed
  (implies (and (extensionp d (f$))
                (embeddingp phi d (e$) (f$))
		(m$-includes-range phi d)
		(m$ y)
		(polyp x d))
	   (m$ (peval (pembed x phi (e$) (f$)) y (e$))))
  :hints (("Goal" :use (extensionp-e$-f$
                        (:instance epe-18 (p x))
                        (:instance epe-21 (p (pembed x phi (e$) (f$))))
			(:instance polyp-pembed (e d) (k (e$)) (p x) (f (f$)))
			(:instance feval-peval (p (pembed x phi (e$) (f$))) (x y) (f (e$)))))))

;; Thus, m$ includes the range of phi':
 
(local-defthmd epe-23
  (implies (and (extensionp d (f$))
                (embeddingp phi d (e$) (f$))
		(m$-includes-range phi d)
		(m$ y)
		(not (in-range-p y phi d (e$) (f$))))
	   (let* ((p (extension-poly y phi d (e$) (f$)))
	          (d1 (cons p d))
		  (phi1 (cons y phi)))
	     (implies (feltp x d1)
	              (m$ (embed x phi1 (e$) (f$))))))
  :hints (("Goal" :in-theory (enable embed feltp)
                  :use (m$-peval-pembed))))

(local-defthmd epe-24
  (implies (and (extensionp d (f$))
                (embeddingp phi d (e$) (f$))
		(m$-includes-range phi d)
		(m$ y)
		(not (in-range-p y phi d (e$) (f$))))
	   (let* ((p (extension-poly y phi d (e$) (f$)))
	          (d1 (cons p d))
		  (phi1 (cons y phi)))
	     (m$-includes-range phi1 d1)))
  :hints (("Goal" :in-theory (enable in-range-p)
                  :use ((:instance m$-includes-range-witness-lemma (d (cons (extension-poly y phi d (e$) (f$)) d))
                                                                   (phi (cons y phi)))
			(:instance epe-23 (x (preembed (m$-includes-range-witness (cons y phi) (cons (extension-poly y phi d (e$) (f$)) d))
			                               (cons y phi)
						       (cons (extension-poly y phi d (e$) (f$)) d)
						       (e$) (f$))))))))

(defthmd extension-poly-extends
  (implies (and (extensionp d (f$))
                (embeddingp phi d (e$) (f$))
		(m$-includes-range phi d)
		(m$ y)
		(not (in-range-p y phi d (e$) (f$))))
	   (let* ((p (extension-poly y phi d (e$) (f$)))
	          (d1 (cons p d))
		  (phi1 (cons y phi)))
	     (and (extensionp d1 d)
	          (embeddingp phi1 d1 (e$) (f$))
		  (m$-includes-range phi1 d1))))
  :hints (("Goal" :use (epe-15 epe-17 epe-24))))

;; The function extend-embedding recursively extends phi to an embedding of an extension of d in e$ with range m$. Note that in
;; the context of the recursive call, according to the above lemma, (cons y phi) is an embedding of (cons p d) in e$ over f$.
;; By embedding-degree-<=, (edegree (cons p d) (f$)) <= (edegree (e$) (f$)), and therefore the declared measure decreases.

(defthm extend-range-to-m$-measure-decreases
  (implies (and (extensionp d (f$))
                (embeddingp phi d (e$) (f$))
		(m$ y)
		(not (in-range-p y phi d (e$) (f$))))
	   (and (posp (edegree d (f$)))
	        (posp (edegree (e$) (f$)))
	        (< (edegree d (f$))
	           (edegree (cons (extension-poly y phi d (e$) (f$)) d) (f$)))
	        (<= (edegree (cons (extension-poly y phi d (e$) (f$)) d) (f$))
	            (edegree (e$) (f$)))))
  :hints (("Goal" :in-theory (disable posp-edegree)
                  :nonlinearp t
                  :use (extensionp-e$-f$ extensionp-extension-poly epe-14
                        (:instance posp-edegree (e (e$)) (f (f$)))
                        (:instance posp-edegree (e d) (f (f$)))
                        (:instance edegree-mult (e (cons (extension-poly y phi d (e$) (f$)) d)) (k d) (f (f$)))
                        (:instance embedding-degree-<= (e (cons (extension-poly y phi d (e$) (f$)) d)) (phi (cons y phi)) (k (e$)) (f (f$)))))))

(defun extend-range-to-m$ (d phi)
  (declare (xargs :measure (nfix (- (edegree (e$) (f$)) (edegree d (f$))))
                  :hints (("Goal" :nonlinearp t
		                  :use ((:instance extend-range-to-m$-measure-decreases (y (range-includes-m$-witness phi d))))))))
  (let* ((y (range-includes-m$-witness phi d))
         (q (extension-poly y phi d (e$) (f$))))
    (if (and (extensionp d (f$)) (embeddingp phi d (e$) (f$)) (m$ y) (not (in-range-p y phi d (e$) (f$))))
        (extend-range-to-m$ (cons q d) (cons y phi))
      (mv d phi))))

(in-theory (disable m$-includes-range range-includes-m$))

(local-defthmd range-extended-to-m$-1
  (implies (and (extensionp d (f$)) (embeddingp phi d (e$) (f$)) (m$-includes-range phi d))
           (mv-let (d1 phi1) (extend-range-to-m$ d phi)
	     (and (extensionp d1 d)
		  (embeddingp phi1 d1 (e$) (f$))
		  (m$-includes-range phi1 d1)
		  (range-includes-m$ phi1 d1)
		  (equal (restrict-embedding phi1 d1 d) phi))))
  :hints (("Goal" :induct (extend-range-to-m$ d phi))
          ("Subgoal *1/2" :use (range-includes-m$-witness-lemma))
	  ("subgoal *1/1" :in-theory (enable restrict-embedding)
	                  :use ((:instance extension-poly-extends (y (range-includes-m$-witness phi d)))
	                        (:instance extends-trans
				  (e (mv-nth 0 (extend-range-to-m$ (cons (extension-poly (range-includes-m$-witness phi d) phi d (e$) (f$)) d)
				                                   (cons (range-includes-m$-witness phi d) phi))))
				  (d (cons (extension-poly (range-includes-m$-witness phi d) phi d (e$) (f$)) d))
	                          (f d))
				(:instance len-extends
				  (e (mv-nth 0 (extend-range-to-m$ (cons (extension-poly (range-includes-m$-witness phi d) phi d (e$) (f$)) d)
                                                                   (cons (range-includes-m$-witness phi d) phi))))
	                          (f (cons (extension-poly (range-includes-m$-witness phi d) phi d (e$) (f$)) d)))
				(:instance cdr-nthcdr
				  (n (+ -1 (- (len d))
				       (len (mv-nth 0 (extend-range-to-m$ (cons (extension-poly (range-includes-m$-witness phi d) phi d (e$) (f$)) d)
                                                                          (cons (range-includes-m$-witness phi d) phi))))))
	                          (l (mv-nth 1 (extend-range-to-m$ (cons (extension-poly (range-includes-m$-witness phi d) phi d (e$) (f$)) d)
                                                                   (cons (range-includes-m$-witness phi d) phi)))))))))

(defthmd range-extended-to-m$
  (implies (and (extensionp d (f$)) (embeddingp phi d (e$) (f$)) (m$-includes-range phi d))
           (mv-let (d1 phi1) (extend-range-to-m$ d phi)
	     (and (extensionp d1 d)
		  (embeddingp phi1 d1 (e$) (f$))
		  (iff (in-range-p y phi1 d1 (e$) (f$)) (m$ y))
		  (equal (restrict-embedding phi1 d1 d) phi))))
  :hints (("Goal" :use (range-extended-to-m$-1
                        (:instance m$-includes-range-lemma (phi (mv-nth 1 (extend-range-to-m$ d phi))) (d (mv-nth 0 (extend-range-to-m$ d phi))))
                        (:instance range-includes-m$-lemma (phi (mv-nth 1 (extend-range-to-m$ d phi))) (d (mv-nth 0 (extend-range-to-m$ d phi))))))))

;; By functional instantiation, with (feltp x (e0)) substituted for (m$ x), d may be extended to to an isomorph of e$.
;; This requires defining functions analogous to m$-includes-range, range-includes-m$, and extend-range-to-m$:

(defun-sk e-includes-range (phi d e f)
  (forall (y)
    (implies (in-range-p y phi d e f)
             (feltp y e))))            

(defthmd e-includes-range-lemma
  (implies (and (e-includes-range phi d e f)
                (in-range-p y phi d e f))
	   (feltp y e))
  :hints (("Goal" :use (e-includes-range-necc))))

(defthmd e-includes-range-witness-lemma
  (let ((y (e-includes-range-witness phi d e f)))
    (implies (implies (in-range-p y phi d e f) (feltp y e))
             (e-includes-range phi d e f))))

(defun-sk range-includes-e (phi d e f)
  (forall (y)
    (implies (feltp y e)
             (in-range-p y phi d e f))))

(defthmd range-includes-e-lemma
  (implies (and (range-includes-e phi d e f)
                (feltp y e))
	   (in-range-p y phi d e f))	   
  :hints (("Goal" :use (range-includes-e-necc))))

(defthmd range-includes-e-witness-lemma
  (let ((y (range-includes-e-witness phi d e f)))
    (implies (implies (feltp y e) (in-range-p y phi d e f))
             (range-includes-e phi d e f))))

(defthm extensionp-e$-f$-rewrite
  (and (fieldp (e$))
       (fieldp (f$))
       (extends (e$) (f$)))
  :hints (("Goal" :use (extensionp-e$-f$))))

;; The third definition requires the following, which is proved by functional instantiation of
;; extend-range-to-m$-measure-decreases:

(defthm extend-to-isomorphism-measure-decreases
  (implies (and (extensionp d (f$))
                (embeddingp phi d (e$) (f$))
		(feltp y (e$))
		(not (in-range-p y phi d (e$) (f$))))
	   (and (posp (edegree d (f$)))
	        (posp (edegree (e$) (f$)))
	        (< (edegree d (f$))
	           (edegree (cons (extension-poly y phi d (e$) (f$)) d) (f$)))
	        (<= (edegree (cons (extension-poly y phi d (e$) (f$)) d) (f$))
	            (edegree (e$) (f$)))))
  :hints (("Goal" :use ((:functional-instance extend-range-to-m$-measure-decreases (m$ (lambda (y) (feltp y (e$)))))))))

(defun extend-to-isomorphism (d phi)
  (declare (xargs :measure (nfix (- (edegree (e$) (f$)) (edegree d (f$))))
                  :hints (("Goal" :nonlinearp t
		                  :use ((:instance extend-to-isomorphism-measure-decreases
					  (y (range-includes-e-witness phi d (e$) (f$)))))))))
  (let* ((y (range-includes-e-witness phi d (e$) (f$)))
         (q (extension-poly y phi d (e$) (f$))))
    (if (and (extensionp d (f$)) (embeddingp phi d (e$) (f$)) (feltp y (e$))
	     (not (in-range-p y phi d (e$) (f$))))
        (extend-to-isomorphism (cons q d) (cons y phi))
      (mv d phi))))

(defthm e-includes-range-rewrite
  (implies (and (embeddingp phi d e f) (extensionp e f) (extensionp d f))
           (e-includes-range phi d e f))
  :hints (("Goal" :in-theory (enable in-range-p)
                  :use ((:instance preembed (x (preembed (e-includes-range-witness phi d e f) phi d e f))
		                            (y (e-includes-range-witness phi d e f))
					    (e d) (k e))
			(:instance embed-image (x (preembed (e-includes-range-witness phi d e f) phi d e f))
  					       (e d) (k e))))))

(defthmd range-extended-to-m$-instance
  (implies (and (extensionp d (f$)) (embeddingp phi d (e$) (f$))); (e$-includes-range phi d))
           (mv-let (d1 phi1) (extend-to-isomorphism d phi)
	     (and (extensionp d1 d)
		  (embeddingp phi1 d1 (e$) (f$))
		  (iff (in-range-p y phi1 d1 (e$) (f$)) (feltp y (e$)))
		  (equal (restrict-embedding phi1 d1 d) phi))))
  :hints (("Goal" :use ((:functional-instance range-extended-to-m$
                          (m$ (lambda (y) (feltp y (e$))))
			  (m$-includes-range (lambda (phi d) (e-includes-range phi d (e$) (f$))))
			  (range-includes-m$ (lambda (phi d) (range-includes-e phi d (e$) (f$))))
			  (m$-includes-range-witness (lambda (phi d) (e-includes-range-witness phi d (e$) (f$))))
			  (range-includes-m$-witness (lambda (phi d) (range-includes-e-witness phi d (e$) (f$))))
			  (extend-range-to-m$ extend-to-isomorphism))))
	  ("Subgoal 4" :use ((:instance range-includes-e-lemma (e (e$)) (f (f$)))
			     (:instance range-includes-e-witness-lemma (e (e$)) (f (f$)))))
	  ("Subgoal 2" :use ((:instance e-includes-range-lemma (e (e$)) (f (f$)))
			     (:instance e-includes-range-witness-lemma (e (e$)) (f (f$)))))))

;; Combine this with embedding-surjective:

(local-defthmd extended-to-isomorphism-1
  (implies (and (extensionp d (f$)) (embeddingp phi d (e$) (f$)))
           (mv-let (d1 phi1) (extend-to-isomorphism d phi)
	     (and (extensionp d1 d)
		  (embeddingp phi1 d1 (e$) (f$))
		  (surjective-embedding-p phi1 d1 (e$) (f$))
		  (equal (restrict-embedding phi1 d1 d) phi))))
  :hints (("Goal" :in-theory (e/d (in-range-p) (embedding-surjective))
                  :use (surjective-embedding-p-witness-lemma
                        (:instance range-extended-to-m$-instance
			  (y (surjective-embedding-p-witness (mv-nth 1 (extend-to-isomorphism d phi))
			                                     (mv-nth 0 (extend-to-isomorphism d phi))
							     (e$) (f$))))))))

(defthmd extended-to-isomorphism
  (implies (and (extensionp d (f$)) (embeddingp phi d (e$) (f$)))
           (mv-let (d1 phi1) (extend-to-isomorphism d phi)
	     (and (extensionp d1 d)
		  (iso-embeddingp phi1 d1 (e$) (f$))
		  (equal (restrict-embedding phi1 d1 d) phi))))
  :hints (("Goal" :in-theory (e/d (in-range-p) (embedding-surjective))
                  :use (extended-to-isomorphism-1
		        (:instance extends-trans (e (mv-nth 0 (extend-to-isomorphism d phi))) (f (f$)))
			(:instance embedding-surjective (phi (mv-nth 1 (extend-to-isomorphism d phi)))
			                                (e (mv-nth 0 (extend-to-isomorphism d phi)))
							(k (e$))
							(f (f$)))))))

;; The desired extension and isomorphism are constructed in 2 steps.  First, the intermediate field is constructed
;; by applying extend-range-to-m$ to f$ and the null embedding:

(defund k$ () (mv-nth 0 (mv-list 2 (extend-range-to-m$ (f$) ()))))

;; Let psi$ be the resulting embedding of k$ in e$:

(defund psi$ () (mv-nth 1 (mv-list 2 (extend-range-to-m$ (f$) ()))))

;; The following is an instance of range-extended-to-m$:

(defthmd k$-psi$-lemma
  (and (extensionp (k$) (f$))
       (embeddingp (psi$) (k$) (e$) (f$))
       (iff (in-range-p y (psi$) (k$) (e$) (f$)) (m$ y)))
  :hints (("Goal" :in-theory (enable in-range-p embed embeddingp k$ psi$)
                  :use ((:instance range-extended-to-m$ (d (f$)) (phi ()))
		        (:instance M$-INCLUDES-RANGE-witness-lemma (d (f$)) (phi ()))
			(:instance m$-includes-f$ (x (PREEMBED (M$-INCLUDES-RANGE-WITNESS NIL (F$)) () (F$) (E$) (F$))))))))

;; Next we construct the extension d$ and the isomorphism phi$ by applying extend-to-isomorphism to
;; k$ and psi$:

(defund d$ () (mv-nth 0 (mv-list 2 (extend-to-isomorphism (k$) (psi$)))))

(defund phi$ () (mv-nth 1 (mv-list 2 (extend-to-isomorphism (k$) (psi$)))))

(in-theory (disable (d$) (phi$) (k$) (psi$)))

;; The following is an instance of extended-to-isomorphism:

(defthmd d$-phi$-lemma
  (and (extensionp (d$) (k$))
       (iso-embeddingp (phi$) (d$) (e$) (f$))
       (equal (restrict-embedding (phi$) (d$) (k$)) (psi$)))
  :hints (("Goal" :in-theory (enable d$ phi$)
                  :use (k$-psi$-lemma (:instance extended-to-isomorphism (d (k$)) (phi (psi$)))))))

;; Let x be an element of d$ and let y = (embed x (phi$) (e$) (f$)).  We must show (m$ y) iff x is lifted from k$.
;; Suppose x is lifted from k$.  Let z = (fdrop x (d$) (k$)).  By fdrop-flift, embed-flift-gen, and d$-phi$-lemma,

;;     y = (embed (flift z (k$) (d$)) (phi$) (e$) (f$))
;;       = (embed z (restrict-embedding (phi$) (d$) (k$)) (e$) (f$))
;;       = (embed z (psi$) (e$) (f$)).

;; Thus, (in-range-p y (psi$) (k$) (e$) (f$)) and by k$-psi$-lemma, (m$ y).
;; On the other hand, suppose (m$ y).  Let x' = (preembed y (psi$) (k$) (e$) (f$)).  By k$-psi$-lemma,
;; (feltp x' (k$)) and y = (embed x' (psi$) (e$) (f$)).  By embed-flift-gen and d$-phi$-lemma,

;;   (embed (flift x' (k$) (d$)) (phi$) (e$) (f$)) = (embed x' (restrict-embedding (phi$) (d$) (k$)) (e$) (f$))
;;                                                 = (embed x' (psi$) (e$) (f$))
;;                                                 = y
;;                                                 = (embed x (phi$) (e$) (f$))

;; and by embedding-1-1, x = (flift x' (k$) (d$)).

(local-defthmd metafield-field-1
  (implies (and (feltp x (d$)) (fliftedp x (k$) (d$)))
           (let ((y (embed x (phi$) (e$) (f$)))
	         (z (fdrop x (d$) (k$))))
             (and (feltp z (k$))
	          (equal (flift z (k$) (d$)) x)
	          (equal y (embed z (psi$) (e$) (f$))))))
  :hints (("Goal" :use (k$-psi$-lemma d$-phi$-lemma
                        (:instance extends-trans (e (d$)) (d (k$)) (f (f$)))
                        (:instance flift-fdrop (e (d$)) (f (k$)))
			(:instance embed-flift-gen (x (fdrop x (d$) (k$))) (phi (phi$)) (e (d$)) (d (k$)) (k (e$)) (f (f$)))))))

(local-defthmd metafield-field-2
  (implies (and (feltp x (d$)) (fliftedp x (k$) (d$)))
           (m$ (embed x (phi$) (e$) (f$))))
  :hints (("Goal" :use (d$-phi$-lemma metafield-field-1
                        (:instance k$-psi$-lemma (y (embed x (phi$) (e$) (f$))))
                        (:instance extends-trans (e (d$)) (d (k$)) (f (f$)))
                        (:instance in-range-p-lemma (y (embed x (phi$) (e$) (f$)))
				                    (x (fdrop x (d$) (k$)))
						    (phi (psi$)) (d (k$)) (e (e$)) (f (f$)))))))

(local-defthmd metafield-field-3
  (implies (and (feltp x (d$)) (m$ (embed x (phi$) (e$) (f$))))
           (let* ((y (embed x (phi$) (e$) (f$)))
	          (x1 (preembed y (psi$) (k$) (e$) (f$))))
	     (and (feltp x1 (k$))
	          (equal (embed x1 (psi$) (e$) (f$))
		         y))))
  :hints (("Goal" :in-theory (enable in-range-p)
                  :use ((:instance k$-psi$-lemma (y (embed x (phi$) (e$) (f$))))))))

(local-defthmd metafield-field-4
  (implies (and (feltp x (d$)) (m$ (embed x (phi$) (e$) (f$))))
           (let* ((y (embed x (phi$) (e$) (f$)))
	          (x1 (preembed y (psi$) (k$) (e$) (f$))))
	     (and (feltp x1 (k$))
	          (equal (embed (flift x1 (k$) (d$)) (phi$) (e$) (f$))
		         y))))
  :hints (("Goal" :use (d$-phi$-lemma k$-psi$-lemma metafield-field-3
                        (:instance extends-trans (e (d$)) (d (k$)) (f (f$)))
                        (:instance embed-flift-gen (x (preembed (embed x (phi$) (e$) (f$)) (psi$) (k$) (e$) (f$)))
			                           (phi (phi$)) (d (k$)) (e (d$)) (k (e$)) (f (f$)))))))

(local-defthmd metafield-field-5
  (implies (and (feltp x (d$)) (m$ (embed x (phi$) (e$) (f$))))
           (let* ((y (embed x (phi$) (e$) (f$)))
	          (x1 (preembed y (psi$) (k$) (e$) (f$))))
	     (and (feltp x1 (k$))
	          (equal (flift x1 (k$) (d$))
		         x))))
  :hints (("Goal" :use (d$-phi$-lemma k$-psi$-lemma metafield-field-4
                        (:instance extends-trans (e (d$)) (d (k$)) (f (f$)))
                        (:instance embedding-1-1 (phi (phi$)) (e (d$)) (f (f$)) (k (e$))
			                         (y (flift (preembed (embed x (phi$) (e$) (f$)) (psi$) (k$) (e$) (f$)) (k$) (d$))))))))

(local-defthmd metafield-field-6
  (implies (and (feltp x (d$)) (m$ (embed x (phi$) (e$) (f$))))
           (fliftedp x (k$) (d$)))
  :hints (("Goal" :use (d$-phi$-lemma k$-psi$-lemma metafield-field-5
                        (:instance fliftedp-flift (f (k$)) (e (d$)) (x (preembed (embed x (phi$) (e$) (f$)) (psi$) (k$) (e$) (f$))))))))

;; Thus, we have the desired result:

(defthmd metafield-field
  (and (extensionp (d$) (k$)) (extensionp (k$) (f$))
       (iso-embeddingp (phi$) (d$) (e$) (f$))
       (implies (feltp x (d$))
                (iff (m$ (embed x (phi$) (e$) (f$)))
                     (fliftedp x (k$) (d$)))))
  :hints (("Goal" :use (d$-phi$-lemma k$-psi$-lemma metafield-field-2 metafield-field-6))))
