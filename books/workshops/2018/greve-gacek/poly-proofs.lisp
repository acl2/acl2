;; 
;; Copyright (C) 2018, Rockwell Collins
;; All rights reserved.
;; 
;; This software may be modified and distributed under the terms
;; of the 3-clause BSD license.  See the LICENSE file for details.
;; 
;; 
(in-package "ACL2")
(include-book "fuzzm-datatypes")

;; This seems like a "dangerous" rule ..
(in-theory (disable set-upper-bound-equiv-bound-varid-list))

(defthm >=all-set-subtract
  (implies
   (force (>=all varid x))
   (>=all varid (set-subtract x y))))

(defthm >-all-set-subtract
  (implies
   (force (>-all varid x))
   (>-all varid (set-subtract x y))))

(in-theory (disable ADVISER::>-ALL-BY-MULTIPLICITY))

(in-theory (enable mv-nth-to-val))

;; ============================================================

;; Conceptually, this is our andTrue spec ..

(encapsulate
    (
     (andTrue-spec (x y env) (mv t t) :guard (and (variableBound-p x) (variableBound-p y) (env-p env)))
     )
     
  (local
   (defun andTrue-spec (x y env)
     (declare (ignore env)
              (xargs :guard (and (variableBound-p x) (variableBound-p y) (env-p env))))
     (mv x (list y))))
  
  (defthm andTrue-spec-inv1
    (implies
     (and (eval-ineq a cex)
          (eval-ineq b cex))
     (eval-ineq (conjoinResults (val 0 (andTrue-spec a b cex)) (val 1 (andTrue-spec a b cex))) cex))
    :hints (("Goal" :do-not-induct t
             :in-theory (enable eval-ineq))))
  
  (defthm andTrue-spec-inv2
    (implies
     (eval-ineq (conjoinResults (val 0 (andTrue-spec a b cex)) (val 1 (andTrue-spec a b cex))) any)
     (and (eval-ineq a any)
          (eval-ineq b any)))
    :rule-classes (:forward-chaining)
    :hints (("Goal" :in-theory (enable eval-ineq))))

  (def::signature andTrue-spec (VariableBound-p variableBound-p env-p)
    variableBound-p variableBound-listp)

  )

;; We will be doing this a lot, so ..
(defmacro def::trueAnd (fname args body &key (ignore 'nil) (xtype 'nil) (ytype 'nil) (precondition 'nil))
  (let ((precondition (if precondition (list precondition) nil))
        (ignore       (if ignore `((ignore ,@ignore)) nil))
        (xguard       (if xtype `(lambda (x) (and (,xtype x) (variableBound-p x))) 'variableBound-p))
        (yguard       (if ytype `(lambda (y) (and (,ytype y) (variableBound-p y))) 'variableBound-p))
        (xtype        (if xtype `(lambda (x) (and (,xtype x) (normalized-variableBound-p x))) 'normalized-variableBound-p))
        (ytype        (if ytype `(lambda (y) (and (,ytype y) (normalized-variableBound-p y) (equal (bound-varid x) (bound-varid y)))) 
                        `(lambda (y) (and (normalized-variableBound-p y) (equal (bound-varid x) (bound-varid y))))))
        (ytype3       (if ytype `(lambda (y) (and (,ytype y) (normalized-variableBound-p y) (equal (bound-varid x3) (bound-varid y)))) 
                        `(lambda (y) (and (normalized-variableBound-p y) (equal (bound-varid x3) (bound-varid y))))))
        )
    `(encapsulate
         ()
       
       (def::und ,fname ,args
         (declare (xargs :signature ((,xguard ,yguard env-p) variableBound-p variableBound-listp)
                         :guard-hints (("Goal" :do-not-induct t)))
                  ,@ignore)
         ,body)
       
       (def::signature ,fname (,xtype ,ytype3 env-p) normalized-variableBound-p normalized-variableBound-listp
         :hints (("Goal" :in-theory (enable ,fname))))

       (defthm ,(packn-pos `("BOUND-VARID-LIST-" ,fname) fname)
         (implies
          (and (equal varid (bound-varid x))
               (env-p cex)
               (normalized-variableBound-p x)
               (normalized-variableBound-p y)
               (equal (bound-varid x) (bound-varid y))
               (,xtype x)
               (,ytype y)
               ,@precondition)
          (>-all varid (all-bound-list-variables (val 1 (,fname x y cex)))))
         :hints (("Goal" :in-theory (enable ,fname))))

       (defthm ,(packn-pos `("UPPER-BOUND-ALL-BOUND-LIST-VARIABLES" ,fname) fname)
         (implies
          (and (equal varid (bound-varid x))
               (env-p cex)
               (normalized-variableBound-p x)
               (normalized-variableBound-p y)
               (equal (bound-varid x) (bound-varid y))
               (,xtype x)
               (,ytype y)
               ,@precondition)
          (set-upper-bound-equiv (all-bound-list-variables (val 1 (,fname x y cex)))
                                 (append (bounding-variables x)
                                         (bounding-variables y))))
         :hints (("Goal" :in-theory (enable ,fname))))

       (defthm ,(packn-pos `("BOUND-VARID-" ,fname) fname)
         (implies
          (and (env-p cex)
               (normalized-variableBound-p x)
               (normalized-variableBound-p y)
               (equal (bound-varid x) (bound-varid y))
               (,xtype x)
               (,ytype y)
               ,@precondition)
          (equal (bound-varid (val 0 (,fname x y cex)))
                 (bound-varid x)))
         :hints (("Goal" :in-theory (enable ,fname))))

       (defthm ,(packn-pos `("UPPER-BOUND-BOUND-VARID-LIST-" ,fname) fname)
         (implies
          (and (env-p cex)
               (normalized-variableBound-p x)
               (normalized-variableBound-p y)
               (equal (bound-varid x) (bound-varid y))
               (,xtype x)
               (,ytype y)
               ,@precondition)
          (set-upper-bound-equiv (bound-varid-list (val 1 (,fname x y cex)))
                                 (append (bounding-variables x)
                                         (bounding-variables y))))
         :hints (("Goal" :in-theory (enable ,fname))))

       (defthm ,(packn-pos `("UPPER-BOUND-BOUNDING-VARIABLES-" ,fname) fname)
         (implies
          (and (env-p cex)
               (normalized-variableBound-p x)
               (normalized-variableBound-p y)
               (equal (bound-varid x) (bound-varid y))
               (,xtype x)
               (,ytype y)
               ,@precondition)
          (set-upper-bound-equiv (bounding-variables (val 0 (,fname x y cex)))
                                 (append (bounding-variables x)
                                         (bounding-variables y))))
         :hints (("Goal" :in-theory (enable ,fname))))

       (defthm ,(packn-pos `(,fname "-INV1") fname)
         (implies
          (and (env-p cex)
               (normalized-variableBound-p x)
               (normalized-variableBound-p y)
               (equal (bound-varid x) (bound-varid y))
               (,xtype x)
               (,ytype y)
               ,@precondition
               (eval-ineq x cex)
               (eval-ineq y cex))
          (eval-ineq (conjoinResults (val 0 (,fname x y cex)) (val 1 (,fname x y cex))) cex))
         :hints (("Goal" :do-not-induct t
                  :in-theory (enable ,fname))))
       
       (defthm ,(packn-pos `(,fname "-INV2") fname)
         (implies
          (and
           (env-p cex)
           (syntaxp (equal any 'any))
           ,@precondition
           (eval-ineq x cex)
           (eval-ineq y cex)
           (normalized-variableBound-p x)
           (normalized-variableBound-p y)
           (equal (bound-varid x) (bound-varid y))
           (,xtype x)
           (,ytype y)
           (not (and (eval-ineq x any)
                     (eval-ineq y any))))
          (not (eval-ineq (conjoinResults (val 0 (,fname x y cex)) (val 1 (,fname x y cex))) any)))
         :hints (("Goal" :do-not-induct t
                  :in-theory (enable ,fname))))
       
       #+joe
       (defthm ,(packn-pos `(,fname "-INV2-REWRITE") fname)
         (implies
          (and (in-conclusion-check (eval-ineq (conjoinresults (val 0 (,fname x y cex)) (val 1 (,fname x y cex))) any) :top t)
               (not-in-conclusion-check (stop-forward (hide (eval-ineq (conjoinresults (val 0 (,fname x y cex)) (val 1 (,fname x y cex))) any))) :top t)
               ,@precondition
               (eval-ineq x cex)
               (eval-ineq y cex)
               (normalized-variableBound-p x)
               (normalized-variableBound-p y)
               (equal (bound-varid x) (bound-varid y))
               (,xtype x)
               (,ytype y))
          (iff (eval-ineq (conjoinresults (val 0 (,fname x y cex)) (val 1 (,fname x y cex))) any)
               (and (forward-wrapper (hide (eval-ineq (conjoinresults (val 0 (,fname x y cex)) (val 1 (,fname x y cex))) any)))
                    (eval-ineq x any)
                    (eval-ineq y any))))
         :hints (("goal" :expand (:free (x) (hide x))
                  :use ,(packn-pos `(,fname "-INV2") fname)
                       :in-theory `(forward-wrapper))))
       
       )))

;; ============================================================

(in-theory (enable signum))

(defstub heuristicX (x y) nil)

(defstub featureCount (x) nil)

(def::un countFeatures(x)
  (declare (xargs :signature ((variableBound-p) natp)))
  (nfix (featureCount x)))

;; static Random seed = new Random();
(defstub randomChoice (x y) nil)

;; JAVA: Variable.java
;; static Variable better(Variable c1, Variable c2) {
(def::un better (x y)
  (declare (xargs :signature ((variableBound-p variableBound-p) variableBound-p)))
;; 	if (c1.countFeatures() > c2.countFeatures()) return c1;
  (if (< (countFeatures y) (countFeatures x)) x
;; 	if (c2.countFeatures() > c1.countFeatures()) return c2;
    (if (< (countFeatures x) (countFeatures y)) y
;; 	if (seed.nextBoolean()) {
;; 		return c1;
;; 	} else {
;; 		return c2;
;; 	}
      (if (randomChoice x y) x y))))
;; }	

(def::signature better (variableInequality-p variableInequality-p) variableInequality-p)
(def::signature better (variableGreater-p variableGreater-p) variableGreater-p)
(def::signature better (variableLess-p variableLess-p) variableLess-p)

;; ============================================================

;; JAVA: VariaboutBound.java
;; static VariableInequality solvePolyGreater0(AbstractPoly poly, RelationType relation) {
;; 	//
;; 	// Normalizes an expression of the form (<~ 0 poly)
;; 	//
(def::un solvePolyGreater0 (relation poly cex)
  (declare (xargs :signature ((relation-p poly-p env-p) variableInequality-p)
                  ;;:guard (and (not-constp poly) (gt-relation-p relation (eval-poly poly cex)))
                  :signature-hints (("Goal" :in-theory (enable signum)))
                  :guard-hints (("Goal" :in-theory (enable signum))))
           (ignore cex))
  ;; (< 0 poly)
  ;; (< 0 ax + poly)
;; 	VariableID name = poly.leadingVariable();
  (let ((name (leading-variable poly)))
;; 	int sign = poly.getCoefficient(name).signum();
    (let ((sign (signum (get-poly-coeff name poly))))
;; 	AbstractPoly sln = poly.solveFor(name);
      (let ((poly (solve name poly)))
;; 	VariableInequality r = (sign < 0) ? new VariableLess(name,true,relation,sln,FeatureType.NONFEATURE) :
;;                             new VariableGreater(name,true,relation,sln,FeatureType.NONFEATURE);
;; 	if (Debug.isEnabled()) System.out.println(ID.location() + "(< 0 " +  poly + ") = " + r);
;; 	return r;
        (if (< sign 0) (variableLess name relation poly)
          (variableGreater name relation poly))))))
;; }

(def::signature solvePolyGreater0 (t t t) variableInequality-p)

(defthm normalized-variableBound-p-solvePolyGreater0
  (implies
   (and
    (relation-p relation)
    (poly-p poly)
    (env-p env)
    (not-constp poly)
    )
   (normalized-variableBound-p (solvePolyGreater0 relation poly env)))
  :rule-classes (:rewrite
                 (:forward-chaining :trigger-terms ((solvePolyGreater0 relation poly env)))))
 
(defthm bound-varid-solvepolygreater0
  (implies
   (not-constp poly)
   (list::memberp (bound-varid (solvepolygreater0 relation poly cex))
                  (get-poly-variables poly)))
  :rule-classes (:rewrite (:forward-chaining :trigger-terms ((bound-varid (solvepolygreater0 relation poly cex))))))

(defthm memberp-upper-bound-bound-varid-solvepolygreater0
  (implies
   (not-constp poly)
   (memberp-upper-bound-equiv (bound-varid (solvepolygreater0 relation poly cex))
                              (get-poly-variables poly))))

(defthm bound-varid-solvepolygreater0-rewrite
  (implies 
   (and
    (varid-p varid)
    (not-constp poly)
    (force (>-all varid (get-poly-variables poly))))
   (< (bound-varid (solvepolygreater0 relation poly cex)) varid))
  :hints (("Goal" :in-theory (disable >-all solvepolygreater0))))

(defthm bounding-variables-solvepolygreater0
  (implies
   (and
    (poly-p poly)
    (force (>-all varid (get-poly-variables poly))))
   (>-all varid (bounding-variables (solvepolygreater0 relation poly cex))))
  :hints (("Goal" :in-theory (enable ADVISER::>-ALL-BY-MULTIPLICITY))))

(defthm set-upper-bound-variables-solvepolygreater0
  (implies
   (poly-p poly)
   (set-upper-bound-equiv (bounding-variables (solvepolygreater0 relation poly cex))
                          (get-poly-variables poly))))

(local (include-book "arithmetic-5/top" :dir :system))

(defthm solve-mul--1
  (equal (eval-poly (solve x (mul -1 poly)) env)
         (eval-poly (solve x poly) env))
  :hints (("Goal" :do-not-induct t
           :in-theory (enable solve))))

(defthm solvePolyGreater0-contract
  (implies
   (force (not-constp poly))
   (equal (eval-ineq (solvePolyGreater0 relation poly cex) env)
          (if (equal (fix-relation relation) :exclusive) (< 0 (eval-poly poly env))
            (<= 0 (eval-poly poly env))))))

(def::un solvePolyLess0 (relation poly cex)
  (declare (xargs :signature ((relation-p poly-p env-p) variableInequality-p)
                  :guard (and (not-constp poly) (lt-relation-p relation (eval-poly poly cex)))
                  :signature-hints (("Goal" :in-theory (enable signum)))
                  :guard-hints (("Goal" :in-theory (enable signum)))))
  (solvePolyGreater0 relation (mul -1 poly) cex))

(def::signature solvePolyLess0 (t t t) variableInequality-p)

(defthm bounding-variables-solvepolyLess0
  (implies
   (and
    (poly-p poly)
    (force (>-all varid (get-poly-variables poly))))
   (>-all varid (bounding-variables (solvepolyLess0 relation poly cex))))
  :hints (("Goal" :in-theory (disable solvepolyGreater0))))

(defthm bound-varid-solvepolyLess0
  (implies
   (not-constp poly)
   (list::memberp (bound-varid (solvepolyLess0 relation poly cex))
                  (get-poly-variables poly)))
  :rule-classes (:rewrite (:forward-chaining :trigger-terms ((bound-varid (solvepolyLess0 relation poly cex))))))

(defthm memberp-upper-bound-bound-varid-solvepolyLess0
  (implies
   (not-constp poly)
   (memberp-upper-bound-equiv (bound-varid (solvepolyLess0 relation poly cex))
                              (get-poly-variables poly))))

(defthm bound-varid-solvepolyLess0-rewrite
  (implies 
   (and
    (varid-p varid)
    (not-constp poly)
    (force (>-all varid (get-poly-variables poly))))
   (< (bound-varid (solvepolyLess0 relation poly cex)) varid))
  :hints (("Goal" :in-theory (disable >-all solvepolyLess0))))

(defthm set-upper-bound-variables-solvepolyLess0
  (implies
   (poly-p poly)
   (set-upper-bound-equiv (bounding-variables (solvepolyLess0 relation poly cex))
                          (get-poly-variables poly))))

(defthm solvePolyLess0-contract
  (implies
   (force (not-constp poly))
   (equal (eval-ineq (solvePolyLess0 relation poly cex) env)
          (if (equal (fix-relation relation) :exclusive) (< (eval-poly poly env) 0)
            (<= (eval-poly poly env) 0)))))

(in-theory (disable solvePolyGreater0))
(in-theory (disable solvePolyLess0))
(in-theory (enable gt-relation-p))

;; ============================================================

;; JAVA: VariableBound.java
;; static RestrictionResult restrictInequality(VariableInequality x, VariableInequality y) {
(def::trueAnd restrictInequality (x y cex)
;; 	assert(x.cex && y.cex);
;; 	assert(x.vid.equals(y.vid));
;; 	AbstractPoly diff = (x instanceof VariableGreater) ? y.poly.subtract(x.poly) :
;; 							x.poly.subtract(y.poly);
  (let ((diff (if (gt-op-p (relation-op x)) (sub (relation-bounding-poly y) (relation-bounding-poly x))
                (sub (relation-bounding-poly x) (relation-bounding-poly y)))))
;; 	int cmp = diff.evaluateCEX().signum();				
    (let ((cmp (signum (eval-poly diff cex))))
;; 	int xcmp = x.relation.compareWith(y.relation);
      (let ((xcmp (compareWith (op-relation (relation-op x)) (op-relation (relation-op y)))))
;; 	boolean choosex = ((cmp < 0) ||
;; 			           ((cmp == 0) && 
;; 			        	((xcmp < 0) || 
;; 			             ((xcmp == 0) && (x.countFeatures() > y.countFeatures())))));
        (let ((choosex (or (< cmp 0)
                           (and (= cmp 0) 
                                (or (< xcmp 0)
                                    (and (= xcmp 0) (equal (heuristicX x y) :x)))))))
;; 	VariableInequality keep;
;; 	if (choosex) {
;; 		keep = x;
;; 		diff = diff.negate();
;; 	} else {
;; 		keep = y;
;; 	}
          (met ((keep drop diff) (cond
                                  (chooseX   (mv x y (mul -1 diff)))
                                  (t         (mv y x diff))))
            (declare (ignore drop))
;; 	if (diff.isConstant()) {
;; 		return new RestrictionResult(keep);
;; 	}
            (let ((const (not (not-constp diff))))
              (if const (mv keep nil)
;; 	RelationType relation = RelationType.INCLUSIVE;
;; 	if ((xcmp != 0) && (keep.relation == RelationType.INCLUSIVE)) {
;; 		relation = RelationType.EXCLUSIVE;
;; 	}
                (let ((relation (if (and (not (= xcmp 0)) (equal (op-relation (relation-op keep)) :inclusive))
                                    :exclusive
                                  :inclusive)))
;; 	return new RestrictionResult(keep,solvePolyGreater0(diff,relation));
                  (mv keep (list (solvePolyGreater0 relation diff cex)))))))))))
;; }
  :xtype variableInequality-p
  :ytype variableInequality-p
  :precondition (similarInequalities (relation-op x) (relation-op y))
  )

(def::signature restrictInequality (variableLess-p variableLess-p t) variableLess-p variableBound-listp
  :hints (("Goal" :in-theory (enable restrictInequality))))

(def::signature restrictInequality (variableGreater-p variableGreater-p t) variableGreater-p variableBound-listp
  :hints (("Goal" :in-theory (enable restrictInequality))))

;; Terminal implementations ..

;;
;; variableLess class
;;

;; JAVA: VariableLess.java
;; public VariableInequality chooseBestComplement(VariableInterval arg) {
(def::un chooseBestComplement-variableLess-variableInterval (x y)
  (declare (xargs :signature ((variableLess-p variableInterval-p) variableInequality-p))
           (ignore x))
;; 	if (arg.lt.countFeatures() > arg.gt.countFeatures()) {
  (if (> (countFeatures (interval-lt y)) (countFeatures (interval-gt y)))
;; 		return arg.lt;
      (interval-lt y)
;; 	}
;; 	return arg.gt;
    (interval-gt y)))
;; }

;; JAVA: VariableLess.java
;; public RestrictionResult andTrue2(VariableLess left) {
(def::trueAnd andTrue-variableLess-variableLess (x y cex)
;; 		VariableLess p1 = left;
;; 		VariableLess p2 = this;
;; 		return restrictInequality(p1,p2);
  (restrictInequality x y cex)
;; 	}
  :xtype variableLess-p 
  :ytype variableLess-p
  )

;;
;; variableGreater class
;;

;; JAVA: VariableGreater.java
;; public VariableInequality chooseBestComplement(VariableInterval arg) {
(def::un chooseBestComplement-variableGreater-variableInterval (x y)
  (declare (xargs :signature ((variableGreater-p variableInterval-p) variableInequality-p))
           (ignore x))
;; 	if (arg.gt.countFeatures() > arg.lt.countFeatures()) {
  (if (> (countFeatures (interval-lt y)) (countFeatures (interval-gt y)))
;; 		return arg.gt;
      (interval-gt y)
;; 	}
;; 	return arg.lt;
    (interval-lt y)))
;; }

;; JAVA: virtual method
(def::un chooseBestComplement-variableInequality-variableInterval (x y)
  (declare (xargs :signature ((variableInequality-p variableInterval-p) variableInequality-p)))
  (if (variableLess-p x)
      (chooseBestComplement-variableLess-variableInterval x y)
    (chooseBestComplement-variableGreater-variableInterval x y)))

;; JAVA: variableGreater.java
;; public RestrictionResult andTrue2(VariableLess left) {
;; JAVA: variableLess.java
;; public RestrictionResult andTrue2(VariableGreater left) {
(def::trueAnd andTrue-variableGreater-variableLess (x y cex)
;;  return new RestrictionResult(new VariableInterval(gt,lt,OpType.AND));
  (mv (variableInterval x y) nil)
;; }
  :xtype variableGreater-p
  :ytype variableLess-p
  :ignore (cex)
  )


;; JAVA: variableGreater.java
;; public RestrictionResult andTrue2(VariableGreater left) {
(def::trueAnd andTrue-variableGreater-variableGreater (x y cex)
;;    return restrictInequality(left,this);
  (restrictInequality x y cex)
;; }
  :xtype variableGreater-p 
  :ytype variableGreater-p
  )

;;
;; variableInterval class
;;

;; JAVA: virtual method invocation
(def::trueAnd andTrue-variableInequality-variableLess (x y cex)
  (if (variableLess-p x)
      (andTrue-variableLess-variableLess x y cex)
    (andTrue-variableGreater-variableLess x y cex))
  :xtype variableInequality-p
  :ytype variableLess-p
  )

;; JAVA: virtual method invocation
(def::trueAnd andTrue-variableInequality-variableGreater (x y cex)
  (if (variableLess-p x)
      (andTrue-variableGreater-variableLess y x cex)
    (andTrue-variableGreater-variableGreater x y cex))
  :xtype variableInequality-p
  :ytype variableGreater-p
  )

;; JAVA: VariableInterval.java
;; public RestrictionResult andTrue2(VariableLess left) {
(def::trueAnd andTrue-variableInterval-variableLess (x y cex)
;; 	RestrictionResult res = restrictInequality(left,lt);
  (met ((lt ltres) (restrictInequality y (interval-lt x) cex))
;; 	VariableLess less = (VariableLess) res.newConstraint;		
;; 	return new RestrictionResult(new VariableInterval(gt,less,OpType.AND),res.restrictionList);
    (mv (variableInterval (interval-gt x) lt) (bound-append nil ltres)))
;; }
  :xtype variableInterval-p
  :ytype variableLess-p
  )

;; JAVA: variableInterval.java : public RestrictionResult andTrue2(VariableGreater left)
;; public RestrictionResult andTrue2(VariableGreater left) {
(def::trueAnd andTrue-variableInterval-variableGreater (x y cex)
;; 	RestrictionResult res = restrictInequality(left,gt);
  (met ((gt gtres) (restrictInequality y (interval-gt x) cex))
;; 	VariableGreater greater = (VariableGreater) res.newConstraint;	
;; 	return new RestrictionResult(new VariableInterval(greater,lt,OpType.AND),res.restrictionList);
    (mv (variableInterval gt (interval-lt x)) (bound-append gtres nil)))
;; }
  :xtype variableInterval-p
  :ytype variableGreater-p
  )

;; JAVA: virtual method invocation
(def::trueAnd andTrue-variableInterval-variableInequality (x y cex)
  (if (variableLess-p y)
      (andTrue-variableInterval-variableLess x y cex)
    (andTrue-variableInterval-variableGreater x y cex))
  :xtype variableInterval-p 
  :ytype variableInequality-p
  )

;; JAVA: virtual method invocation
(def::trueAnd andTrue-variableGreater-variableInequality (x y cex)
  (if (variableLess-p y)
      (andTrue-variableGreater-variableLess x y cex)
    (andTrue-variableGreater-variableGreater x y cex))
  :xtype variableGreater-p
  :ytype variableInequality-p
  )

;; JAVA: virtual method invocation
(def::trueAnd andTrue-variableLess-variableInequality (x y cex)
  (if (variableLess-p y)
      (andTrue-variableLess-variableLess x y cex)
    (andTrue-variableGreater-variableLess y x cex))
  :xtype variableLess-p
  :ytype variableInequality-p
  )

;; JAVA: virtual method invocation
(def::trueAnd andTrue-variableInequality-variableInequality (x y cex)
  (if (variableLess-p x)
      (andTrue-variableLess-variableInequality x y cex)
    (andTrue-variableGreater-variableInequality x y cex))
  :xtype variableInequality-p
  :ytype variableInequality-p
  )

;; JAVA: VariableInterval.java : public RestrictionResult andTrue2(VariableInterval left)
;; public RestrictionResult andTrue2(VariableInterval left) {
(def::trueAnd andTrue-variableInterval-variableInterval (x y cex)
;; 	VariableInterval right = this;
  (let ((left  y)
        (right x))
;; 	RestrictionResult gt = restrictInequality(left.gt,right.gt);
    (met ((gt rres) (restrictInequality (interval-gt left) (interval-gt right) cex))
;; 	RestrictionResult lt = restrictInequality(left.lt,right.lt);
      (met ((lt lres) (restrictInequality (interval-lt left) (interval-lt right) cex))
;; 	return lt.andRegion(gt);
        (mv (variableInterval gt lt) (bound-append rres lres)))))
;; }
  :xtype variableInterval-p
  :ytype variableInterval-p
  )

;;
;; variableEquality class
;;

;; JAVA: VariableEquality.java
;; static VariableInequality linearizeTrue(VariableID v, VariableEquality eq) {
(def::un linearizeTrue(x cex)
  (declare (xargs :signature ((variableEquality-p env-p) variableInequality-p)
                  :guard (and (eval-ineq x cex)
                              (exclusive-op-p (relation-op x)))))
;; 	int sign = v.cex.compareTo(eq.poly.evaluateCEX());
  (let ((sign (compareTo (rfix (binding->value (get-binding (bound-varid x) cex))) (eval-poly (relation-bounding-poly x) cex))))
;; 	if (sign < 0) {
    (if (< sign 0)
;; 		return new VariableLess(v,eq.poly,eq.relation,true);
        (variableLess (bound-varid x) :exclusive (relation-bounding-poly x))
;; 	}
;; 	if (sign > 0) {
      (if (> sign 0)
;; 		return new VariableGreater(v,eq.poly,eq.relation,true);
          (variableGreater (bound-varid x) :exclusive (relation-bounding-poly x))
;; 	}
;; 	// sign == 0
;; 	return null;
;;      This cannot happen when the guards are satisfied.
        (variableGreater (bound-varid x) :exclusive (relation-bounding-poly x))))))
;; }

(in-theory (enable EXCLUSIVE-OP-P INCLUSIVE-OP-P))

(defun zero-inclusive-relation-p (relation value)
  (declare (type t relation value))
  (implies (equal (rfix value) 0) (equal relation :inclusive)))

;; JAVA: VariableBound.java
;; static List<VariableBound> restrictDisequality(AbstractPoly xpoly, AbstractPoly ypoly, RelationType relation) {
(def::un restrictDisequality (xpoly ypoly relation cex)
  (declare (xargs :signature ((poly-p poly-p relation-p env-p) variableBound-listp)
                  ;;:guard (zero-inclusive-relation-p relation (- (eval-poly xpoly cex) (eval-poly ypoly cex)))
                  :guard-hints (("Goal" :do-not-induct t))
                  ))
;; 	// If you already know the relation and which variable bound to keep ..
;; 	List<VariableBound> res = new ArrayList<>();
;; 	if (Debug.isEnabled()) System.out.println(ID.location() + "restrictX: " + x + " & " + y);
;;      AbstractPoly diff = xpoly.subtract(ypoly);
  (let ((diff (sub xpoly ypoly)))
;; 	if (diff.isConstant()) {
    (if (isConstant diff)
;; 		return res;
        nil
;; 	}
;; 	BigFraction z = diff.evaluateCEX();
      (let ((z (eval-poly diff cex)))
;; 	int cmp = z.signum();
        (let ((cmp (signum z)))
;; 	diff = (0 < cmp) ? diff : diff.negate();
          (let ((diff (if (< 0 cmp) diff (mul -1 diff))))
;; 	if (! (diff.evaluateCEX().signum() >= 0)) 
;; 		assert(false);
;; 	res.add(solvePolyGreater0(diff,relation));
;; 	return res;
            (list (solvePolyGreater0 relation diff cex))))))))
;; }

(def::signature restrictdisequality (poly-p poly-p relation-p env-p)
  normalized-variablebound-listp
  :hints (("goal" :in-theory (enable normalized-variablebound-p))))

;;
;; Just a brief detour to consider the spec for restrictDisequality
;;
(defthmd eval-ineq-conjoinresults
  (iff (eval-ineq (conjoinresults x list) env)
       (and (eval-ineq x env)
            (eval-ineq-list list env))))

(defthm conjoinresults-restrictDisequality
  (iff (eval-ineq (conjoinresults x (restrictDisequality p1 p2 rel cex)) env)
       (and (eval-ineq x env)
            (eval-ineq-list (restrictDisequality p1 p2 rel cex) env)))
  :hints (("Goal" :in-theory (enable eval-ineq-conjoinresults))))

(defthm restrictDisequality-inv2
  (implies
   (and
    (<= (eval-poly xpoly cex) (eval-poly ypoly cex))
    (< (eval-poly ypoly any) (eval-poly xpoly any)))
   (not (eval-ineq-list (restrictDisequality xpoly ypoly rel cex) any)))
  :hints (("Goal" :do-not-induct t)))

(defthm restrictDisequality-inv2-exclusive
  (implies
   (and
    (relation-p rel)
    (not (equal rel :inclusive))
    (< (eval-poly xpoly cex) (eval-poly ypoly cex))
    (<= (eval-poly ypoly any) (eval-poly xpoly any)))
   (not (eval-ineq-list (restrictDisequality xpoly ypoly rel cex) any)))
  :hints (("Goal" :in-theory (enable fix-relation) :do-not-induct t)))

(defthm restrictDisequality-inv1
  (implies
   (not (equal (eval-poly xpoly cex) (eval-poly ypoly cex)))
   (eval-ineq-list (restrictDisequality xpoly ypoly rel cex) cex))
  :hints (("Goal" :do-not-induct t)))

(defthm restrictDisequality-inv1-inclusive
  (implies
   (<= (eval-poly xpoly cex) (eval-poly ypoly cex))
   (eval-ineq-list (restrictDisequality xpoly ypoly :inclusive cex) cex))
  :hints (("Goal" :do-not-induct t)))

(defthm upper-bound-all-bound-list-variables-restrictdisequality
  (set-upper-bound-equiv (all-bound-list-variables (restrictdisequality p1 p2 rel cex))
                         (append (get-poly-variables p1)
                                 (get-poly-variables p2))))

(defthm upper-bound-bound-varid-list-restrictdisequality
  (set-upper-bound-equiv (bound-varid-list (restrictdisequality p1 p2 rel cex))
                         (append (get-poly-variables p1)
                                 (get-poly-variables p2))))

(in-theory (disable restrictDisequality))

(defthm conjoinresults-append
  (iff (eval-ineq (conjoinresults x (append a b)) cex)
       (and (eval-ineq (conjoinresults x a) cex)
            (eval-ineq (conjoinresults x b) cex)))
  :hints (("Goal" :in-theory (enable append)
           :induct (append a b))))

;; JAVA: VariableEquality.java
;; static RestrictionResult restrictEquality(VariableEquality x, VariableEquality y) {
(def::un restrictEquality (x y)
  (declare (xargs :signature ((variableEquality-p variableEquality-p) variableEquality-p variableBound-listp)))
;;  AbstractPoly diff = x.poly.subtract(y.poly);
  (let ((diff (sub (relation-bounding-poly x) (relation-bounding-poly y))))
;;  if (diff.isConstant()) return new RestrictionResult(x);
    (if (isConstant diff) (mv x nil)
;;  VariableID vid = diff.leadingVariable();
      (let ((xid (leading-variable diff)))
;;  AbstractPoly sln = diff.solveFor(vid);
        (let ((rst (solve xid diff)))
;;  VariableEquality res = new VariableEquality(vid,true, y.relation,sln,x.feature);
          (let ((r (variableEquality xid rst)))
;;  return new RestrictionResult(x,res);
            (mv x (list r))))))))
;; }

;; JAVA: VariableEquality.java
;; public RestrictionResult  andTrue2(VariableLess left) {
(def::trueAnd andTrue-variableEquality-variableLess (x y cex)
  (if (not (equal (BOUND-VARID X) (BOUND-VARID Y))) (mv x (list y))
;;	   RestrictionResult res = new RestrictionResult(this,VariableBound.restrictDisequality(this.poly, left.poly));
    (let ((res (restrictDisequality (relation-bounding-poly x) (relation-bounding-poly y) (op-relation (relation-op y)) cex)))
;; 	   return res;
      (mv x res)))
;; 	}
  :xtype variableEquality-p
  :ytype variableLess-p
  )

;; JAVA: VariableEquality.java
;; public RestrictionResult  andTrue2(VariableGreater left) {
(def::trueAnd andTrue-variableEquality-variableGreater (x y cex)
  (if (not (equal (BOUND-VARID X) (BOUND-VARID Y))) (mv x (list y))
;;	  RestrictionResult res = new RestrictionResult(this,VariableBound.restrictDisequality(left.poly, this.poly));
    (let ((res (restrictDisequality  (relation-bounding-poly y) (relation-bounding-poly x) (op-relation (relation-op y)) cex)))
;; 		return res;
      (mv x res)))
;; 	}
  :xtype variableEquality-p 
  :ytype variableGreater-p
  )

;; JAVA: virtual method invocation
(def::trueAnd andTrue-variableEquality-variableInequality (x y cex)
  (if (variableLess-p y)
      (andTrue-variableEquality-variableLess x y cex)
    (andTrue-variableEquality-variableGreater x y cex))
  :xtype variableEquality-p
  :ytype variableInequality-p
  )


;; JAVA: VariableEquality.java
;; public RestrictionResult  andTrue2(VariableInterval left) {
(def::trueAnd andTrue-variableEquality-variableInterval (x y cex)
;; 			List<VariableBound> list = VariableBound.restrictDisequality(this.poly,left.lt.poly,left.lt.relation);
  (let ((reslt (restrictDisequality  (relation-bounding-poly x) (relation-bounding-poly (interval-lt y)) (op-relation (relation-op (interval-lt y))) cex)))
;; 			list.addAll(VariableBound.restrictDisequality(left.gt.poly,this.poly,left.gt.relation));
    (let ((resgt (restrictDisequality  (relation-bounding-poly (interval-gt y)) (relation-bounding-poly x) (op-relation (relation-op (interval-gt y))) cex)))
;; 			RestrictionResult res = new RestrictionResult(this,list);
;; 			return res;
      (mv x (append resgt reslt))))
;; 		}
  :xtype variableEquality-p
  :ytype variableInterval-p
  )

;; JAVA: variableEquality.java
;; public RestrictionResult  andTrue2(VariableEquality left) {
(def::trueAnd andTrue-variableEquality-variableEquality (x y cex)
;; 			VariableEquality x;
;; 			VariableEquality y;
;;                      if (left.countFeatures() < this.countFeatures()) {
;; 				x = this;
;; 				y = left;
;; 			} else {
;; 				x = left;
;; 				y = this;
;; 			}
  (met ((x y) (if (< (countFeatures y) (countFeatures x)) (mv x y) (mv y x)))
                    ;; 			return restrictEquality(x,y);
    (restrictEquality x y))
  :ignore (cex)
  :xtype variableEquality-p
  :ytype variableEquality-p
  )

(in-theory (disable EVAL-INEQ-polyINTERVALP EVAL-INEQ-polyRELATIONP))

;; JAVA: virtual method invocation
(def::trueAnd andTrue-variableInequality-variableRelation (x y cex)
  (if (variableEquality-p y)
      (andTrue-variableEquality-variableInequality y x cex)
    (andTrue-variableInequality-variableInequality x y cex))
  :xtype variableInequality-p 
  :ytype variableRelation-p
  )

;; JAVA: virtual method invocation
(def::trueAnd andTrue-variableEquality-variableRelation (x y cex)
  (if (variableEquality-p y)
      (andTrue-variableEquality-variableEquality x y cex)
    (andTrue-variableEquality-variableInequality x y cex))
  :xtype variableEquality-p
  :ytype variableRelation-p
  )

;; JAVA: virtual method invocation
(def::trueAnd andTrue-variableRelation-variableRelation (x y cex)
  (if (variableEquality-p x)
      (andTrue-variableEquality-variableRelation x y cex)
    (andTrue-variableInequality-variableRelation x y cex))
  :xtype variableRelation-p 
  :ytype variableRelation-p
  )

;; JAVA: virtual method invocation
(def::trueAnd andTrue-variableInterval-variableRelation (x y cex)
  (if (variableEquality-p y)
      (andTrue-variableEquality-variableInterval y x cex)
    (andTrue-variableInterval-variableInequality x y cex))
  :xtype variableInterval-p
  :ytype variableRelation-p
  )

;; JAVA: virtual method invocation
(def::trueAnd andTrue-variableInterval-variableBound (x y cex)
  (if (variableInterval-p y)
      (andTrue-variableInterval-variableInterval x y cex)
    (andTrue-variableInterval-variableRelation x y cex))
  :xtype variableInterval-p 
  :ytype variableBound-p
  )

;; JAVA: virtual method invocation
(def::trueAnd andTrue-variableRelation-variableBound (x y cex)
  (if (variableInterval-p y)
      (andTrue-variableInterval-variableRelation y x cex)
    (andTrue-variableRelation-variableRelation x y cex))
  :xtype variableRelation-p
  :ytype variableBound-p
  )

;; JAVA: virtual method invocation
(def::trueAnd andTrue-variableBound-variableBound (x y cex)
  (met ((z res) (if (variableInterval-p x)
                    (andTrue-variableInterval-variableBound x y cex)
                  (andTrue-variableRelation-variableBound x y cex)))
    (list z res))
  :xtype variableBound-p
  :ytype variableBound-p
  )

