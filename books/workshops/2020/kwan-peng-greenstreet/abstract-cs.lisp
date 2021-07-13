(in-package "ACL2")

; cert_param: (uses-acl2r, uses-smtlink)

(include-book "arithmetic/top"       :dir :system)
(include-book "std/util/top"         :dir :system)
(include-book "centaur/fty/top"      :dir :system)
(include-book "nonstd/nsa/sqrt"      :dir :system)
(include-book "projects/smtlink/top" :dir :system)

(value-triple (tshell-ensure))
(add-default-hints '((SMT::SMT-computed-hint clause)))

(defsection a-vec

  ;; This fty stuff is in /fty/basetypes
  (fty::defbasetype real-equiv realp :fix realfix)

  (fty::deffixtype real
 		:pred  realp
		:fix   realfix
		:equiv real-equiv)

  (fty::deflist real-vec
                :elt-type real ;; deflist needs a fixing function (see deffixtype above)
                :true-listp t)

 ;; Witness is just the same as regular proof for the reals.  All proofs
 ;; dependent on reasoning about the reals are encapsulated and local.  Only
 ;; the inner product space axioms and other basic properties are exported.
 (encapsulate
  (((a-vec-p *) => *)
   ((vector-zero-p  *) => *)
   ((vector-compatible * *) => *)
   ((vector-add * *) => *)
   ((scalar-vector-prod * *) => *)
   ((inner-prod * *) => *))

  (local
   (define a-vec-p (v)
    :enabled t ;; enabled so the proof works as before with the reals
    :returns (avec booleanp)
    (real-vec-p v)))

  (local
   (define vector-zero-p ((v a-vec-p))
     :returns (is-z booleanp)
     :measure (len v)
     (b* (((if (equal v nil)) t)
          ((cons hd tl) v)
          ((unless (equal hd 0)) nil))
       (vector-zero-p tl))
     ///
     (more-returns
      (is-z (implies (and is-z v) (equal (car v) 0))
 	         :name car-when-vec-zero-p)
      (is-z (implies (and is-z v) (vector-zero-p (cdr v)))
 	         :name monotonicity-of-vector-zero-p-with-cdr
 	         :hints(("Goal" :do-not-induct t)))
      (is-z (implies is-z (vector-zero-p (cons 0 v)))
 	         :name monotonicity-of-vector-zero-p-with-cons
 	         :hints(("Goal" :do-not-induct t))))))

  (local
   (define vector-compatible (u v)
     :guard t
     :returns (ok booleanp)
     :enabled t
     (and (a-vec-p u) (a-vec-p v) (equal (len u) (len v)))))

   (defthm reflexivity-of-vector-compatible-when-a-vec-p
    (equal (vector-compatible x x) (a-vec-p x))
    :hints(("Goal" :expand((vector-compatible x x)))))

   ;; Need to export theorems about basic properties of vector-compatible
   (defthm vector-compatible-implies-a-vec-p
     (implies (vector-compatible u v)
	      (and (a-vec-p u)
		   (a-vec-p v))))

   (defthm booleanp-of-vector-compatible-2
    (booleanp (vector-compatible u v)))

   (defthm vector-compatible-implies-a-vec-p
    (implies (vector-compatible u v) (and (a-vec-p u) (a-vec-p v))))

   (defthm commutativity-of-vector-compatible
    (equal (vector-compatible u v) (vector-compatible v u)))

   (defthm transitivity-of-vector-compatible
    (implies (and (vector-compatible u v) (vector-compatible v w))
             (vector-compatible u w)))

   (local
    (define vector-add ((u a-vec-p) (v a-vec-p))
      :guard (vector-compatible u v)
      :returns (sum a-vec-p)
      :enabled t
      (b* (((unless (vector-compatible u v)) nil)
           ((unless (consp u)) nil)
           ((cons uhd utl) u)
           ((cons vhd vtl) v))
        (cons (+ uhd vhd) (vector-add utl vtl)))
      ///
      (more-returns
       (sum (implies (vector-compatible u v)
                     (vector-compatible u sum))
            :name compatibility-of-vector-add-2)
       (sum (implies (vector-compatible u v)
          	               (and (equal (len sum) (len u))
          	                    (equal (len sum) (len v))))
            :name length-of-vector-add)
       (sum (implies (not (vector-compatible u v))
                     (not sum))
            :name incompatibility-of-vector-add-local)
       (sum (equal (vector-add v u) sum)
            :name commutativity-of-vector-add-local)
       (sum (implies (and (a-vec-p u) (a-vec-p v) (equal (len u) (len v))
                          (vector-zero-p u))
                     (equal sum v))
            :name zero-is-identity-for-vector-sum-local))))

   ;; Need to export theorems about basic properties of vector-add
   (defthm a-vec-p-of-vector-add-2
     (a-vec-p (vector-add u v)))

   (defthm compatibility-of-vector-add
    (implies (vector-compatible u v)
             (vector-compatible u (vector-add u v))))

   (defthm incompatibility-of-vector-add
 	   (implies (not (vector-compatible u v))
                    (not (vector-add u v))))

    (defthm commutativity-of-vector-add
	(equal (vector-add v u) (vector-add u v)))

    (defthm zero-is-identity-for-vector-sum
	(implies (and (a-vec-p u) (a-vec-p v) (vector-compatible u v)
                          (vector-zero-p u))
                     (equal (vector-add u v) v)))

   (local
    (define scalar-vector-prod ((a realp) (v a-vec-p))
      :returns (prod a-vec-p)
      :enabled t
      (b* (((unless (and (realp a) (a-vec-p v))) nil)
           ((unless (consp v)) nil)
           ((cons vhd vtl) v))
        (cons (* a vhd) (scalar-vector-prod a vtl)))
      ///
      (more-returns
       (prod (implies (and (realp a) (a-vec-p v))
                      (vector-compatible prod v))
             :name compatibility-of-scalar-vector-prod-local)
       (prod (implies (and (realp a) (a-vec-p v))
                      (equal (len prod) (len v)))
             :name length-of-scalar-vector-prod)
       (prod (implies (not (and (realp a) (a-vec-p v)))
                      (not prod))
             :name incompatibility-of-scalar-vector-prod-local)
       (prod (implies (vector-zero-p v) (vector-zero-p prod))
             :name scalar-vector-prod-when-vector-zero-local))))

   ;; Need to export basic theorems about scalar-vector-prod
   (defthm a-vec-p-of-scalar-vector-prod-2
    (a-vec-p (scalar-vector-prod a v)))

   (defthm incompatibility-of-scalar-vector-prod
    (implies (not (and (realp a) (a-vec-p v)))
             (not (scalar-vector-prod a v))))

   (defthm scalar-vector-prod-when-vector-zero
    (implies (vector-zero-p v) (vector-zero-p (scalar-vector-prod a v))))

   (defthm compatibility-of-scalar-vector-prod
    (implies (and (realp a) (a-vec-p v))
             (vector-compatible (scalar-vector-prod a v) v)))

   (defthm scalar-vector-prod-when-scalar-zero
     (vector-zero-p (scalar-vector-prod 0 v)))

   (defthm scalar-vector-prod-when-scalar-one
     (implies (a-vec-p v)
              (equal (scalar-vector-prod 1 v) v)))

   (local (defthmd random-lemma-1
    (implies (and (realp b) (real-vec-p v))
	     (real-vec-p (scalar-vector-prod b v)))
    :hints (("GOAL" :in-theory (e/d (scalar-vector-prod))))))

   (local (defthmd random-lemma-2
    (implies (and (realp b) (real-vec-p v))
	     (real-vec-p (scalar-vector-prod b (cdr v))))
    :hints (("GOAL" :use ((:instance random-lemma-1 (v (cdr v))))))))

   (defthm compatibility-of-scalar-scalar-vector-prod
     (implies (and (realp a) (realp b) (a-vec-p v))
	      (equal (scalar-vector-prod a (scalar-vector-prod b v))
		     (scalar-vector-prod (* a b) v)))
     :hints (("GOAL" :in-theory (e/d (scalar-vector-prod))
	      	     :use ((:instance random-lemma-2))) ;; This is necessary
	     ("Subgoal *1/1'4'" :use ((:instance random-lemma-2)))))

    ;; Useful in general
    (defthm vector-sum-inverse
	(implies (and (a-vec-p u) (a-vec-p v) (vector-compatible u v)
                      (vector-zero-p (vector-add u v)))
                     (equal u (scalar-vector-prod -1 v)))
	:rule-classes nil
	:hints (("GOAL" :in-theory (enable vector-zero-p vector-add))))

  ;; This lemma wasn't needed for the non-abstract version
   (local
    (defthmd lemma-1
     (implies (and (real-vec-p v) (realp a))
 	      (real-vec-p (scalar-vector-prod a (cdr v))))
     :hints (("Goal" :induct (len v)))))

   (defthm distributivity-scalarsum-vector-prod
     (implies (and (realp a) (realp b) (a-vec-p v))
              (equal (vector-add (scalar-vector-prod a v)
 		                (scalar-vector-prod b v))
 	            (scalar-vector-prod (+ a b) v)))
     :hints (("Goal" :in-theory (enable lemma-1))))

  ;; Again, this wasn't needed for the non-abstract version
   (local
    (defthmd lemma-2
     (implies (and (real-vec-p u) (real-vec-p v))
 	     (real-vec-p (vector-add (cdr u) (cdr v))))
     :hints (("Goal" :induct (len v)))))

   ;; The prefered direction for the rewrite tuple for
   ;;   distributivity-scalarsum-vector-prod seems obvious.
   ;;   For the next theorem, I'm guessing it's better to "simplify"
   ;;   to a vector add of scalar-vector-prods rather than the other
   ;;   way around, but this may be a bozo guess.
   (defthm distributivity-scalar-vecsum-prod
     (implies (and (realp a) (a-vec-p u) (a-vec-p v))
              (equal (scalar-vector-prod a (vector-add u v))
 	            (vector-add (scalar-vector-prod a u)
 		                (scalar-vector-prod a v))))
     :hints (("Goal" :in-theory (enable lemma-1 lemma-2))))
 		;; need to enable both "obvious" lemmas

   (local
    (define inner-prod ((u a-vec-p) (v a-vec-p))
      :guard (vector-compatible u v)
      :returns (prod realp)
      :enabled t
      (b* (((unless (vector-compatible u v)) 0)
           ((unless (consp u)) 0)
           ((cons uhd utl) u)
           ((cons vhd vtl) v))
        (+ (* uhd vhd) (inner-prod utl vtl)))
      ///
      (more-returns
       (prod (implies (vector-zero-p u) (equal prod 0))
             :name inner-prod-when-left-zero-local)
       (prod (implies (vector-zero-p v) (equal prod 0))
             :name inner-prod-when-right-zero-local)
       (prod (equal (inner-prod v u) prod)
             :name commutativity-of-inner-prod-local))))

  ;; Need to export theorems of basic properties of inner prod
  (defthm realp-of-inner-prod-2
    (realp (inner-prod u v)))

  (defthm inner-prod-when-left-zero
    (implies (vector-zero-p u)
	     (equal (inner-prod u v) 0)))

  (defthm inner-prod-when-right-zero
    (implies (vector-zero-p v)
	     (equal (inner-prod u v) 0)))

  (defthm commutativity-of-inner-prod
    (equal (inner-prod v u) (inner-prod u v)))

  (defthm positivity-of-inner-prod (<= 0 (inner-prod v v)))

  (defthm positivity-of-inner-prod-strict
    (implies (and (a-vec-p v) (not (vector-zero-p v)))
             (and (< 0 (inner-prod v v))
                  (not (equal (inner-prod v v) 0)))))

  (defthm definiteness-of-inner-prod
    (implies (and (a-vec-p v) (equal (inner-prod v v) 0))
             (and (vector-zero-p v))))

   (defthm bilinearity-of-inner-prod-scalar
     (implies (and (vector-compatible u v) (realp a) (realp b))
 	           (equal (inner-prod (scalar-vector-prod a u)
 	                              (scalar-vector-prod b v))
 		                (* a b (inner-prod u v))))
     :hints (("Goal" :in-theory (enable lemma-1))))
 		;; have to enable one of the obvious lemmas

   (defthm distributivity-of-inner-prod-left
     (implies (and (vector-compatible v x) (vector-compatible x y))
              (equal (inner-prod v (vector-add x y))
 	                  (+ (inner-prod v x) (inner-prod v y))))
     :hints (("Goal" :in-theory (enable lemma-2))))
 		;; have to enable the other obvious lemma

   (defthm distributivity-of-inner-prod-right
     (implies (and (vector-compatible u x) (vector-compatible v x))
              (equal (inner-prod (vector-add u v) x)
 	                  (+ (inner-prod u x) (inner-prod v x)))))))
;; end encapsulation

(defsection cs1
 ;; proof sketch.
 ;; let a = <u,v>/<v,v>
 ;; 0 <= <u - a*v, u - a*v>  :use positivity-of-inner-prod
 ;;    = <u,u-a*v> + <-a*v,u-a*v> :use distributivity-of-inner-prod-right
 ;;    = <u,u> + <u,-a*v> + <-a*v,u-a*v> :use distributivity-of-inner-prod-left
 ;;    = <u,u> + <u,-a*v> + <-a*v,u> + <-a*v,-a*v> :use distributivity-of-inner-prod-left
 ;;    = <u,u> + <1*u,-a*v> + <-a*v,1*u> + <-a*v,-a*v> :use scalar-vector-prod-when-scalar-one
 ;;    = <u,u> + 1*-a*<u,v> + <-a*v,1*u> + <-a*v,-a*v> :use bilinearity-of-inner-prod-scalar
 ;;    = <u,u> + 1*-a*<u,v> + -a*1*<v,u> + <-a*v,-a*v> :use bilinearity-of-inner-prod-scalar
 ;;    = <u,u> + 1*-a*<u,v> + -a*1*<v,u> + (-a)*(-a)<v,v> :use bilinearity-of-inner-prod-scalar
 ;;    = <u,u> + -a*<u,v> + -a*<u,v> + a*a<v,v> :use commutativity-of-inner-prod
 ;;    = <u,u> - 2*a*<u,v> + a*a*<v,v>
 ;;    = <u,u> - 2*(<u,v>/<v,v>)*<u,v> + (<u,v>/<v,v>)*(<u,v>/<v,v>)*<v,v>
 ;;    = <u,u> - 2*(<u,v>*<u,v>/<v,v>) + <u,v>*<u,v>/<v,v>
 ;;    = <u,u> - <u,v>*<u,v>/<v,v>
 ;; 0 <= <u,u><v,v> - <u,v>*<u,v>
 ;; <u,v>*<u,v> <= <u,u><v,v>
 ;;
 ;; Strategy: let Smtlink do all of the algebraic manipulation.
 ;;   Use :hypotheses hints to instantiate the theorem instances needed by Smtlink.

 ;; (aa u v) -- a function for 'a' as described in the proof sketch.
 ;; I didn't want to call it 'a' because that seemed way to likely to collide
 ;; with a variable name.
 (local (define aa ((u a-vec-p) (v a-vec-p))
   :guard (vector-compatible u v)
   :returns (a realp)
   (if (vector-zero-p v) 0
     (/ (inner-prod u v) (inner-prod v v)))))

 ;; Many of the theorems referenced in the proof sketch above require
 ;; vector-compatibility in their hypotheses.  cs1-compatibility establishes
 ;; all of the compatibility results we need for the main proof.
 (local (defthm cs1-compatibilty
   (implies (and (vector-compatible u v) (not (vector-zero-p v)))
	    (and (vector-compatible u (vector-add u (scalar-vector-prod (- (aa u v)) v)))
		 (vector-compatible u (scalar-vector-prod (- (aa u v)) v))))
  :hints(("Goal"
   :in-theory (disable compatibility-of-scalar-vector-prod
		       compatibility-of-vector-add)
   :use(
    (:instance compatibility-of-scalar-vector-prod (a (- (aa u v))) (v v))
    (:instance compatibility-of-vector-add (u u) (v (scalar-vector-prod (- (aa u v)) v))))))))

 ;; Most of the :hypotheses that we use for Smtlink are discharged by ACL2
 ;; without any extra help.  The step that uses bilinearity-of-inner-prod-scalar
 ;; got stuck, even when I hinted it with the same hints as for scratch-5 below.
 ;; I'm pulled the theorem out as a lemma, and instantiate it when it's needed.
 (local (defthm scratch-5
   (implies (and (vector-compatible u v) (not (vector-zero-p v)))
	    (equal
	     (+ (inner-prod u u)
		(inner-prod (scalar-vector-prod 1 u)
			    (scalar-vector-prod (- (aa u v)) v))
		(inner-prod (scalar-vector-prod (- (aa u v)) v)
			    (scalar-vector-prod 1 u))
		(inner-prod (scalar-vector-prod (- (aa u v)) v)
			    (scalar-vector-prod (- (aa u v)) v)))
	     (+ (inner-prod u u)
		(* (- (aa u v)) (inner-prod u v))
		(* (- (aa u v)) (inner-prod v u))
		(* (- (aa u v)) (- (aa u v))
		(inner-prod v v)))))
  :hints(("Goal"
    :in-theory (disable bilinearity-of-inner-prod-scalar)
    :use(
     (:instance bilinearity-of-inner-prod-scalar (a 1) (b (- (aa u v))) (u u) (v v))
     (:instance bilinearity-of-inner-prod-scalar (a (- (aa u v))) (b 1) (u v) (v u))
     (:instance bilinearity-of-inner-prod-scalar (a (- (aa u v))) (b (- (aa u v))) (u v) (v v)))))))

 ;; scratch does the main derivation for cs1.
 (local (defthm scratch
   (implies (and (a-vec-p u) (a-vec-p v)
		 (vector-compatible u v) (not (vector-zero-p v)))
	    (equal (inner-prod (vector-add u (scalar-vector-prod (- (aa u v)) v))
				     (vector-add u (scalar-vector-prod (- (aa u v)) v)))
			 (+ (inner-prod u u)
			    (* (- 2) (aa u v) (inner-prod u v))
			    (* (aa u v) (aa u v) (inner-prod v v)))))
   :hints(("Goal"
    :smtlink(
     :abstract (a-vec-p)
     :functions(
      (vector-add
       :formals ((u a-vec-p) (v a-vec-p))
       :returns ((sum a-vec-p))
       :level 0)
      (scalar-vector-prod
       :formals ((a realp) (v a-vec-p))
       :returns ((prod a-vec-p))
       :level 0)
      (inner-prod
       :formals ((u a-vec-p) (v a-vec-p))
       :returns ((prod realp))
       :level 0)
      (vector-zero-p
       :formals ((v a-vec-p))
       :returns ((is-z booleanp))
       :level 0)
      (vector-compatible
       :formals ((u a-vec-p) (v a-vec-p))
       :returns ((ok booleanp))
       :level 0))
     :hypotheses(
      ((equal ;; scratch-1
	(inner-prod (vector-add u (scalar-vector-prod (- (aa u v)) v))
		    (vector-add u (scalar-vector-prod (- (aa u v)) v)))
	(+ (inner-prod u
	   (vector-add u (scalar-vector-prod (- (aa u v)) v)))
	   (inner-prod (scalar-vector-prod (- (aa u v)) v)
	   (vector-add u (scalar-vector-prod (- (aa u v)) v))))))
      ((equal ;; scratch-2
	(+ (inner-prod u
	   (vector-add u (scalar-vector-prod (- (aa u v)) v)))
	   (inner-prod (scalar-vector-prod (- (aa u v)) v)
	   (vector-add u (scalar-vector-prod (- (aa u v)) v))))
	(+ (inner-prod u u)
	   (inner-prod u (scalar-vector-prod (- (aa u v)) v))
	   (inner-prod (scalar-vector-prod (- (aa u v)) v)
	   (vector-add u (scalar-vector-prod (- (aa u v)) v))))))
      ((equal ;; scratch-3
	(+ (inner-prod u u)
	   (inner-prod u (scalar-vector-prod (- (aa u v)) v))
	   (inner-prod (scalar-vector-prod (- (aa u v)) v)
	   (vector-add u (scalar-vector-prod (- (aa u v)) v))))
	(+ (inner-prod u u)
	   (inner-prod u (scalar-vector-prod (- (aa u v)) v))
	   (inner-prod (scalar-vector-prod (- (aa u v)) v) u)
	   (inner-prod (scalar-vector-prod (- (aa u v)) v)
	   (scalar-vector-prod (- (aa u v)) v)))))
      ((equal ;; scratch-4
	(+ (inner-prod u u)
	   (inner-prod u (scalar-vector-prod (- (aa u v)) v))
	   (inner-prod (scalar-vector-prod (- (aa u v)) v) u)
	   (inner-prod (scalar-vector-prod (- (aa u v)) v)
	   (scalar-vector-prod (- (aa u v)) v)))
	(+ (inner-prod u u)
	   (inner-prod (scalar-vector-prod 1 u)
		       (scalar-vector-prod (- (aa u v)) v))
	   (inner-prod (scalar-vector-prod (- (aa u v)) v)
		       (scalar-vector-prod 1 u))
	   (inner-prod (scalar-vector-prod (- (aa u v)) v)
		       (scalar-vector-prod (- (aa u v)) v)))))
      ((implies (and (vector-compatible u v) (not (vector-zero-p v)))
		     (equal ;; scratch-5
		       (+ (inner-prod u u)
			  (inner-prod (scalar-vector-prod 1 u)
			  (scalar-vector-prod (- (aa u v)) v))
			  (inner-prod (scalar-vector-prod (- (aa u v)) v)
			  (scalar-vector-prod 1 u))
			  (inner-prod (scalar-vector-prod (- (aa u v)) v)
			  (scalar-vector-prod (- (aa u v)) v)))
		       (+ (inner-prod u u)
			  (* (- (aa u v)) (inner-prod u v))
			  (* (- (aa u v)) (inner-prod v u))
			  (* (- (aa u v)) (- (aa u v))
			  (inner-prod v v)))))
       :hints(
	:in-theory (disable scratch-5)
	:use((:instance scratch-5 (u u) (v v)))))
      ((equal ;; scratch-6
	(+ (inner-prod u u)
	   (* (- (aa u v)) (inner-prod u v))
	   (* (- (aa u v)) (inner-prod v u))
	   (* (- (aa u v)) (- (aa u v))
	   (inner-prod v v)))
	(+ (inner-prod u u)
	   (* (- (aa u v)) (inner-prod u v))
	   (* (- (aa u v)) (inner-prod u v))
	   (* (- (aa u v)) (- (aa u v))
	   (inner-prod v v)))))))))))

 ;; cs1-extra-hyps -- to make Smtlink happy, we need all of the
 ;;   we need type-recognizers for each free variable in the hypotheses.
 ;;   Because (vector-compatible u v) implies (real-vec-p u) and
 ;;   (real-vec-p v), these hypotheses are redundant
 ;; changed everything to a-vec-p
 (local (defthm cs1-when-v-not-zero
   (implies (and (a-vec-p u) (a-vec-p v)
		 (vector-compatible u v) (not (vector-zero-p v)))
	    (b* ((uu (inner-prod u u))
		 (uv (inner-prod u v))
		 (vv (inner-prod v v)))
	      (<= (* uv uv) (* uu vv))))
   :hints
   (("Goal"
     :smtlink(
      :abstract (a-vec-p)
      :functions(
       (vector-add
	:formals ((u a-vec-p) (v a-vec-p))
	:returns ((sum a-vec-p))
	:level 0)
       (scalar-vector-prod
	:formals ((a realp) (v a-vec-p))
	:returns ((prod a-vec-p))
	:level 0)
       (inner-prod
	:formals ((u a-vec-p) (v a-vec-p))
	:returns ((prod realp))
	:level 0)
       (vector-zero-p
	:formals ((v a-vec-p))
	:returns ((is-z booleanp))
	:level 0)
       (vector-compatible
	:formals ((u a-vec-p) (v a-vec-p))
	:returns ((ok booleanp))
	:level 0))
      :hypotheses(
       ((<= 0 (inner-prod (vector-add u (scalar-vector-prod (- (aa u v)) v))
			  (vector-add u (scalar-vector-prod (- (aa u v)) v)))))
       ((< 0 (inner-prod v v)))
       ((equal (inner-prod (vector-add u (scalar-vector-prod (- (aa u v)) v))
			   (vector-add u (scalar-vector-prod (- (aa u v)) v)))
	       (+ (inner-prod u u)
		  (* (- 2) (aa u v) (inner-prod u v))
		  (* (aa u v) (aa u v) (inner-prod v v)))))))))))

 (local (defthm cs1-when-v-is-zero
   (implies (vector-zero-p v)
	    (b* ((uu (inner-prod u u))
		 (uv (inner-prod u v))
		 (vv (inner-prod v v)))
	      (and (equal uv 0) (equal vv 0)
	           (equal (* uv uv) (* uu vv)))))))

 (defthm cs1
   (implies (vector-compatible u v)
	    (b* ((uu (inner-prod u u))
		 (uv (inner-prod u v))
		 (vv (inner-prod v v)))
	      (<= (* uv uv) (* uu vv))))
   :hints(("Goal" :cases ((vector-zero-p v)))))

 ;; Proof that cs1 equality implies linear dependence, i.e.
 ;;  	bu + av = 0
 ;; for some nonzero a, b, and given v nonzero.
 ;; In this case, b=1 and a=<u,v>/<v,v>=(aa u v)
 (encapsulate
   ()
 ;; true because
 ;; <u,v>^2 = <u,u> <v,v> implies
 ;; 0 = <u,u> - <u,v><u,v>/<v,v> = ... = <u-av,u-av>
 (local (defthm lemma-1
  (implies (and (vector-compatible u v)
		(a-vec-p u)
		(a-vec-p v)
		(not (vector-zero-p v))
       	        (equal (* (inner-prod u v) (inner-prod u v))
		       (* (inner-prod u u) (inner-prod v v))))
	   (equal (inner-prod (vector-add u (scalar-vector-prod (- (aa u v)) v))
			      (vector-add u (scalar-vector-prod (- (aa u v)) v)))
		  0))
  :hints
   (("Goal"
     :smtlink(
      :abstract (a-vec-p)
      :functions(
       (vector-add
	:formals ((u a-vec-p) (v a-vec-p))
	:returns ((sum a-vec-p))
	:level 0)
       (scalar-vector-prod
	:formals ((a realp) (v a-vec-p))
	:returns ((prod a-vec-p))
	:level 0)
       (inner-prod
	:formals ((u a-vec-p) (v a-vec-p))
	:returns ((prod realp))
	:level 0)
       (vector-zero-p
	:formals ((v a-vec-p))
	:returns ((is-z booleanp))
	:level 0)
       (vector-compatible
	:formals ((u a-vec-p) (v a-vec-p))
	:returns ((ok booleanp))
	:level 0))
      :hypotheses (
       ((implies (not (vector-zero-p v))
		 (not (equal (inner-prod v v) 0))))
       ((equal (+ (inner-prod u u)
		  (* (- 2) (aa u v) (inner-prod u v))
		  (* (aa u v) (aa u v) (inner-prod v v)))
	       (inner-prod (vector-add u (scalar-vector-prod (- (aa u v)) v))
			   (vector-add u (scalar-vector-prod (- (aa u v)) v)))))))))))

  (defthm cs1-equality-implies-linear-dependence-nz
   (implies (and (vector-compatible u v)
		 (a-vec-p u)
		 (a-vec-p v)
		 (not (vector-zero-p v))
       	         (equal (* (inner-prod u v) (inner-prod u v))
		        (* (inner-prod u u) (inner-prod v v))))
	    (b* ((uv (inner-prod u v))
		 (vv (inner-prod v v)))
	   	(vector-zero-p (vector-add u (scalar-vector-prod (- (/ uv vv)) v)))))
   :hints (("GOAL" :expand (aa u v)
	    	   :use ((:instance lemma-1)))))

  (defthm cs1-equality-implies-linear-dependence
   (b* ((uu (inner-prod u u))
	(uv (inner-prod u v))
	(vv (inner-prod v v)))
       (implies (and (vector-compatible u v)
		     (equal (* uv uv)
		            (* uu vv)))
	   	(or (vector-zero-p v)
		    (vector-zero-p (vector-add u (scalar-vector-prod (- (/ uv vv)) v))))))))
 ;; end encapsulation


 ;; Proof that linear dependence implies cs1-equality, i.e.
 ;;   u = av implies <u,v>^2 = <u,u><v,v>
 (encapsulate
  ()
  ;; Had to take this lemma out of the smtlink hints for some reason
  (local (defthm lemma-1
   (implies (and (a-vec-p v) (realp a))
 	   (equal (inner-prod v (scalar-vector-prod a v))
 		  (* a (inner-prod v v))))
   :hints (("GOAL" :use ((:instance bilinearity-of-inner-prod-scalar (a 1) (b a) (u v)))))))

  ;; True because
  ;; <u, v> <u, v> = <av, v> <av, v>
  ;;		   = aa <v,v> <v,v>
  ;;		   = <av, av> <v,v>
  ;;		   = <u, u>   <v,v>
  (defthm linear-dependence-implies-cs1-equality
   (implies (and (vector-compatible u v)
 		(a-vec-p u)
 		(a-vec-p v)
 		(realp a)
 		(equal u (scalar-vector-prod a v)))
 	   (b* ((uu (inner-prod u u))
         	(uv (inner-prod u v))
         	(vv (inner-prod v v)))
        	       (equal (* uv uv) (* uu vv))))
   :hints
    (("Goal"
      :smtlink(
       :abstract (a-vec-p)
       :functions(
        (vector-add
 	:formals ((u a-vec-p) (v a-vec-p))
 	:returns ((sum a-vec-p))
 	:level 0)
        (scalar-vector-prod
 	:formals ((a realp) (v a-vec-p))
 	:returns ((prod a-vec-p))
 	:level 0)
        (inner-prod
 	:formals ((u a-vec-p) (v a-vec-p))
 	:returns ((prod realp))
 	:level 0)
        (vector-zero-p
 	:formals ((v a-vec-p))
 	:returns ((is-z booleanp))
 	:level 0)
        (vector-compatible
 	:formals ((u a-vec-p) (v a-vec-p))
 	:returns ((ok booleanp))
 	:level 0))
       :hypotheses(
        ((equal (inner-prod (scalar-vector-prod a v)
 			   (scalar-vector-prod a v))
 	       (* (* a a) (inner-prod v v))))
        ((equal (inner-prod (scalar-vector-prod a v)
 			   v)
 	       (* a (inner-prod v v)))))))))))

;; Proof of cs2 from cs1, conditions for cs2 equivalence, and some
;; useful lemmas about the equivalence of cs1 and cs2. ACL2 way of
;; proving cs2 from cs1 works but want to use Smtlink in the future
(defsection cs2

 ;; some useful lemmas about square roots
 (local (defthm lemma-1
  (b* ((uv (inner-prod u v))
       (uu (inner-prod u u))
       (vv (inner-prod v v)))
      (and (equal (acl2-sqrt (* uv uv)) (abs uv))
	   (equal (acl2-sqrt (* uu vv))
		  (* (acl2-sqrt uu) (acl2-sqrt vv)))
	   ;; used to show cs2-equality-iff-cs1-equality
	   (equal (* (* (acl2-sqrt uu) (acl2-sqrt vv))
		     (* (acl2-sqrt uu) (acl2-sqrt vv)))
		  (* uu vv))))))

 (local (defthm lemma-2
  (implies (and (realp a) (realp b) (<= 0 a) (<= 0 b) (<= a b))
	   (<= (acl2-sqrt a) (acl2-sqrt b)))))

 (defthmd cs2-iff-cs1
  (implies (vector-compatible u v)
           (b* ((uv (inner-prod u v))
                (uu (inner-prod u u))
                (vv (inner-prod v v)))
	       (equal (<= (abs uv)  (* (acl2-sqrt uu) (acl2-sqrt vv)))
                      (<= (* uv uv) (* uu vv)))))
  :hints (("GOAL" :use ((:instance lemma-1)
			(:instance lemma-2 (a (* (inner-prod u v)
						 (inner-prod u v)))
				   	   (b (* (inner-prod u u)
						 (inner-prod v v))))
			(:instance positivity-of-inner-prod-strict)))))

  (defthm cs2
   (implies (vector-compatible u v)
            (b* ((uv (inner-prod u v))
         	 (uu (inner-prod u u))
        	 (vv (inner-prod v v)))
                (<= (abs uv) (* (acl2-sqrt uu) (acl2-sqrt vv)))))
   :hints (("GOAL" :use ((:instance cs2-iff-cs1)))))

  ;; Normally, I would prove this with ACL2 but ACL2 did not
  ;; recognise the "obvious" substitution for the L/RHS's and kept on
  ;; trying to reason about square roots. Smtlink was easier.
  (defthm linear-dependence-implies-cs2-equality
   (implies (and (vector-compatible u v)
 		(a-vec-p u)
 		(a-vec-p v)
 		(realp a)
 		(equal u (scalar-vector-prod a v)))
            (equal (abs (inner-prod u v))
		   (* (acl2-sqrt (inner-prod u u))
		      (acl2-sqrt (inner-prod v v)))))
   :hints
    (("Goal"
      :smtlink(
       :abstract (a-vec-p)
       :functions(
        (vector-add
 	 :formals ((u a-vec-p) (v a-vec-p))
 	 :returns ((sum a-vec-p))
 	 :level 0)
        (scalar-vector-prod
 	 :formals ((a realp) (v a-vec-p))
 	 :returns ((prod a-vec-p))
 	 :level 0)
        (inner-prod
 	 :formals ((u a-vec-p) (v a-vec-p))
 	 :returns ((prod realp))
 	 :level 0)
        (vector-zero-p
 	 :formals ((v a-vec-p))
 	 :returns ((is-z booleanp))
 	 :level 0)
        (vector-compatible
 	 :formals ((u a-vec-p) (v a-vec-p))
 	 :returns ((ok booleanp))
 	 :level 0)
	(acl2-sqrt
	 :formals ((sq realp))
	 :returns ((rt realp))
	 :level 0))
       :hypotheses(
	((equal (acl2-sqrt (* (inner-prod u v) (inner-prod u v)))
		(abs (inner-prod u v))))
	((equal (acl2-sqrt (* (inner-prod u u) (inner-prod v v)))
		(* (acl2-sqrt (inner-prod u u))
		   (acl2-sqrt (inner-prod v v)))))
	((equal (* (inner-prod u v) (inner-prod u v))
		(* (inner-prod u u) (inner-prod v v)))
	 :hints (:use linear-dependence-implies-cs1-equality)))))))

  ;; Square roots are tricky for ACL2 and Smtlink individually. Use
  ;; both together to avoid introducing excess and needless lemmas.
  (defthmd cs2-equality-iff-cs1-equality
   (implies (and (vector-compatible u v)
		 (a-vec-p u)
		 (a-vec-p v))
       	    (equal (equal (abs (inner-prod u v))
		          (* (acl2-sqrt (inner-prod u u))
		 	     (acl2-sqrt (inner-prod v v))))
	           (equal (* (inner-prod u v) (inner-prod u v))
	 	          (* (inner-prod u u) (inner-prod v v)))))
   :hints
    (("Goal"
      :in-theory (disable abs)
      :smtlink(
       :abstract (a-vec-p)
       :functions(
        (vector-add
 	 :formals ((u a-vec-p) (v a-vec-p))
 	 :returns ((sum a-vec-p))
 	 :level 0)
        (scalar-vector-prod
 	 :formals ((a realp) (v a-vec-p))
 	 :returns ((prod a-vec-p))
 	 :level 0)
        (inner-prod
 	 :formals ((u a-vec-p) (v a-vec-p))
 	 :returns ((prod realp))
 	 :level 0)
        (vector-zero-p
 	 :formals ((v a-vec-p))
 	 :returns ((is-z booleanp))
 	 :level 0)
        (vector-compatible
 	 :formals ((u a-vec-p) (v a-vec-p))
 	 :returns ((ok booleanp))
 	 :level 0)
	(acl2-sqrt
	 :formals ((sq realp))
	 :returns ((rt realp))
	 :level 0))
       :hypotheses(
	;; hypotheses for the reverse direction
	((equal (acl2-sqrt (* (inner-prod u v) (inner-prod u v)))
		(abs (inner-prod u v))))
	((equal (acl2-sqrt (* (inner-prod u u) (inner-prod v v)))
		(* (acl2-sqrt (inner-prod u u))
		   (acl2-sqrt (inner-prod v v)))))
	;; hypotheses for the forward direction
	((equal (* (* (acl2-sqrt (inner-prod u u))
		      (acl2-sqrt (inner-prod v v)))
		   (* (acl2-sqrt (inner-prod u u))
		      (acl2-sqrt (inner-prod v v))))
		(* (inner-prod u u) (inner-prod v v)))))))))

 (defthm cs2-equality-implies-linear-dependence
   (b* ((uu (inner-prod u u))
	(uv (inner-prod u v))
	(vv (inner-prod v v)))
       (implies (and (vector-compatible u v)
		     (equal (abs uv)
		            (* (acl2-sqrt uu) (acl2-sqrt vv))))
	   	(or (vector-zero-p v)
		    (vector-zero-p (vector-add u (scalar-vector-prod (- (/ uv vv)) v))))))
   :hints (("GOAL" :use ((:instance cs2-equality-iff-cs1-equality))))))
;; end cs2 section
