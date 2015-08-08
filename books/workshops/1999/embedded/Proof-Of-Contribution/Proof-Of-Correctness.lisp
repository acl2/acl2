;(ld "Proof-Of-Correctness.lisp")

(in-package "ACL2")

(include-book "Proof-Of-Correctness-OneCycle")

(defun updated-cell (var value mem)
 (make-cell
  value
  (var-attribute (get-cell var mem))
  (var-type      (get-cell var mem))))

(defun equal-put-vals (varlist vals mem memafterputs)
  (if (endp varlist)
      (null varlist)
    (and
     (equal
      (get-cell (car varlist) memafterputs)
      (updated-cell (car varlist) (car vals) mem))
     (equal-put-vals
      (cdr varlist)
      (cdr vals)
      mem
      memafterputs))))


(defthm equal-put-vals-have-same-attributes
 (implies
  (and
   (true-listp varlist)
   (equal-put-vals varlist vals mem memafter))
  (equal (var-attributes varlist memafter) (var-attributes varlist mem)))
 :hints (("Goal" :in-theory (enable var-attribute))))

(defthm equal-put-vals-have-values-that-are-vals
  (implies
   (and
    (true-listp vals)
    (true-listp varlist)
    (equal (len varlist) (len vals))
    (equal-put-vals varlist vals mem memafter))
   (equal (var-values varlist memafter)
          vals ))
 :hints ( ("Goal" :in-theory (enable var-value get-cell make-cell))))

(defthm props-of-updated-cell
 (and (equal (var-attribute (updated-cell gvar newv mem)) (var-attribute (get-cell gvar mem)))
      (equal (var-type      (updated-cell gvar newv mem)) (var-type      (get-cell gvar mem)))
      (equal (var-value     (updated-cell gvar newv mem)) newv))
 :hints (("Goal" :in-theory (enable var-value var-type var-attribute)))
 :rule-classes nil)


(defthm if-values-are-rns-then-equal-values-is-kept
 (implies
  (and
   (true-listp varlist)
   (true-listp vals)
   (equal (len varlist) (len vals))
   (equal-put-vals varlist vals mem memafter)
   (equal
    vals
    (apply-direct-rns-to-value-according-to-type
     (updated-cell gvar newv gmem)
     type))
   (equal-values-and-attributes
    (get-cell gvar gmem)
    varlist
    mem
    type))
  (equal-values-and-attributes
   (updated-cell gvar newv gmem)
   varlist
   memafter
   type))
 :hints (("Goal"
          :use ( (:instance props-of-updated-cell (mem gmem))
                 (:instance equal-put-vals-have-values-that-are-vals))
          :in-theory (disable apply-direct-rns-to-value-according-to-type))))


(defun input-var (var val mem)
 (put-cell var (updated-cell var val mem) mem))

(defun input-vars-e (varlist vals mem)
 (if (endp varlist)
     mem
     (input-vars-e
      (cdr varlist)
      (cdr vals)
      (input-var (car varlist) (car vals) mem))))



(defun index-different-input-vars-e (varlist vals mem memafter)
  (cond
   ( (endp varlist)
     0 )
   ( (not (equal (get-cell (car varlist) memafter)
		 (updated-cell (car varlist) (car vals) mem)))
     0 )
   ( t
     (1+ (index-different-input-vars-e
	  (cdr varlist)
	  (cdr vals)
	  mem
	  memafter)))))

(defthm if-bad-index-in-range-ten-must-be-noninput
  (let ((bad-idx (index-different-input-vars-e varlist vals mem memafter)))
    (implies
     (in-range bad-idx varlist)
     (not (equal
	   (get-cell (nth bad-idx varlist) memafter)
           (updated-cell
	    (nth bad-idx varlist)
	    (nth bad-idx vals)
	    mem)))))
 :hints (("Goal" :in-theory (disable get-cell updated-cell))))


(defthm if-bad-index-not-in-range-then-every-update
  (let ((bad-idx (index-different-input-vars-e varlist vals mem memafter)))
    (implies (and (true-listp varlist)
		  (not (in-range bad-idx varlist)))
	  (equal-put-vals varlist vals mem memafter))))


(defthm input-list-decomp
 (implies
  (and
   (in-range idx l1)
   (in-range idx l2))
  (equal
   (input-vars-e l1 l2 mem)
   (input-vars-e (nthcdr idx l1) (nthcdr idx l2)
		(input-vars-e (firstn idx l1) (firstn idx l2) mem))))
 :hints (("Goal" :in-theory (disable updated-cell))))

(defthm not-in-list-untouched-by-input-vars-e
 (implies (not (member-equal-bool v l1))
          (equal (get-cell v (input-vars-e l1 l2 mem)) (get-cell v mem))))

(defthm update-independent-from-firstbn
 (implies
  (not (member-equal-bool (nth idx l1) (firstn idx l1)))
  (equal (updated-cell
	  (nth idx l1)
	  (nth idx l2)
	  (input-vars-e (firstn idx l1) (firstn idx l2) mem))
	 (updated-cell
	  (nth idx l1)
	  (nth idx l2)
          mem))))

(defthm if-el-does-not-appear-after-its-position-then-input-vars-e-produces-v
 (implies
  (and
   (not (member-equal-bool (nth idx l1) (cdr (nthcdr idx l1))))
   (in-range idx l1)
   (in-range idx l2))
  (equal
   (get-cell (nth idx l1) (input-vars-e l1 l2 mem))
   (updated-cell
     (nth idx l1)
     (nth idx l2)
     (input-vars-e (firstn idx l1) (firstn idx l2) mem))))
  :hints (("Goal" :in-theory (disable updated-cell))))


(defthm rtm-variable-of-input-vars-e-is-correspondent-value
  (implies
   (and
    (true-listp ll)
    (no-duplicates-p (append-lists ll))
    (in-range gem1 ll)
    (in-range idx vals)
    (in-range idx (nth gem1 ll)))
   (equal
    (get-cell (nth idx (nth gem1 ll)) (input-vars-e (nth gem1 ll) vals mem))
    (updated-cell (nth idx (nth gem1 ll)) (nth idx vals) mem)))
:hints (("Goal" :in-theory (disable updated-cell)
 :use (
       (:instance no-duplicates-all-implies-no-duplicates-one (idx1 gem1))
       (:instance
        no-duplicates-means-an-element-does-not-appear-after-its-position
        (l (nth gem1 ll)))
       if-el-does-not-appear-after-its-position-then-input-vars-e-produces-v
       (:instance input-list-decomp
                  (l1 (nth gem1 ll)) (l2 (nth vals ll)))
       (:instance update-independent-from-firstbn
                  (l1 (nth gem1 ll)) (l2 (nth vals ll)))))))



(defthm rtm-variable-of-input-vars-e-is-put-vals
  (implies
   (and
    (true-listp ll)
    (no-duplicates-p (append-lists ll))
    (equal (len (nth gem1 ll)) (len vals))
    (in-range gem1 ll)
    (true-listp (nth gem1 ll)))
   (equal-put-vals (nth gem1 ll) vals mem
    (input-vars-e  (nth gem1 ll) vals mem)))
  :hints (("Goal" :use (:instance rtm-variable-of-input-vars-e-is-correspondent-value
			 (idx (index-different-input-vars-e
                               (nth gem1 ll)
                               vals
                               mem
                               (input-vars-e (nth gem1 ll) vals  mem)))))
	  ("Goal'" :cases ( (in-range (index-different-input-vars-e
				      (nth gem1 ll)
				      vals
				      mem
				      (input-vars-e (nth gem1 ll) vals mem))
				     (nth gem1 ll)) ) )
	  ("Subgoal 1" :in-theory '((:definition in-range)
				    (:rewrite if-bad-index-in-range-ten-must-be-noninput)))
	  ("Subgoal 2" :in-theory '((:rewrite if-bad-index-not-in-range-then-every-update)))))



(defthm input-vars-e-preserves-equal-values-attributes
  (implies
   (and
    (true-listp ll)
    (no-duplicates-p (append-lists ll))
    (equal (len (nth gem1 ll)) (len vals))
    (in-range gem1 ll)
    (true-listp vals)
    (true-listp (nth gem1 ll))
    (equal
     vals
     (apply-direct-rns-to-value-according-to-type (updated-cell gvar newv gmem) type))
    (equal-values-and-attributes (get-cell gvar gmem) (nth gem1 ll) mem type))
   (equal-values-and-attributes (updated-cell gvar newv gmem)
                                (nth gem1 ll)
                                (input-vars-e (nth gem1 ll) vals mem) type))
  :hints (("Goal"
           :use
            ((:instance rtm-variable-of-input-vars-e-is-put-vals)
            (:instance if-values-are-rns-then-equal-values-is-kept
                       (varlist (nth gem1 ll))
                       (memafter (input-vars-e (nth gem1 ll) vals mem)))))))



(defthm variable-of-other-cell-untouched-input
 (implies
  (and
   (true-listp m)
   (no-duplicates-p (append-lists (retrieve-rtmvars m)))
   (assoc-equal gvar1 m)
   (assoc-equal gvar2 m)
   (in-range idx2 (rtmintvars-i gvar2 m))
   (not (equal gvar1 gvar2)))
  (equal
   (get-cell (nth idx2 (rtmintvars-i gvar2 m)) rm)
   (get-cell (nth idx2 (rtmintvars-i gvar2 m)) (input-vars-e (rtmintvars-i gvar1 m) vals rm))))
 :hints (("Goal" :use (:instance lemma1-different-vars-do-not-belong
                                 (idx1 idx2)
                                 (gvar1 gvar2)
                                 (gvar2 gvar1)))))



(defthm variables-of-other-cells-untouched-input
 (implies
  (and
   (true-listp m)
   (true-listp (rtmintvars-i gvar2 m))
   (no-duplicates-p (append-lists (retrieve-rtmvars m)))
   (m-correspondent-values-p m gm rm)
   (assoc-equal gvar1 m)
   (assoc-equal gvar2 m)
   (not (equal gvar1 gvar2)))
  (equal-get-cells (rtmintvars-i gvar2 m) rm (input-vars-e (rtmintvars-i gvar1 m) vals rm)))
  :hints (("Goal" :in-theory nil
	   :use ( (:instance variable-of-other-cell-untouched-input
			     (idx2 (idx-different-cell
				    (rtmintvars-i gvar2 m)
				    rm
				    (input-vars-e (rtmintvars-i gvar1 m) vals rm))))))
	  ("Goal'" :cases ( (in-range
			     (idx-different-cell
				    (rtmintvars-i gvar2 m)
				    rm
				    (input-vars-e (rtmintvars-i gvar1 m) vals rm))
			     (rtmintvars-i gvar2 m)) ))
	  ("Subgoal 2" :in-theory '((:rewrite if-bad-index-not-in-range-then-every-equal)))
	  ("Subgoal 1" :in-theory '((:forward-chaining if-bad-index-in-range-then-cells-must-be-different)))))





(defthm result-of-input-one-var
 (equal
  (get-cell var0 (input-var var val mem))
  (if (equal var var0)
      (updated-cell var val mem)
      (get-cell var0 mem))))

(defthm other-variables-equal-values-attributes-input
 (implies
  (and
   (true-listp m)
   (true-listp (rtmintvars-i gvar1 m))
   (no-duplicates-p (append-lists (retrieve-rtmvars m)))
   (m-correspondent-values-p m gm rm)
   (assoc-equal gvar1 m)
   (assoc-equal gvar2 m)
   (not (equal gvar1 gvar2)))
  (equal-values-and-attributes
   (get-cell gvar1 (input-var gvar2 gval2 gm))
   (rtmintvars-i gvar1 m)
   (input-vars-e (rtmintvars-i gvar2 m) vals rm)
   (type-i gvar1 m)))
 :hints (("Goal" :use ( (:instance result-of-input-one-var
                                   (var0 gvar1) (var gvar2) (val gval2))
                        (:instance m-correspondent-values-implies-equal-values-and-attribus
                                   (memgstate gm)
                                   (memrstate rm))
                        (:instance variables-of-other-cells-untouched-input
                                   (gvar1 gvar2) (gvar2 gvar1))))))


(defthm equal-values-kept-by-appropriate-input-vars
 (implies
  (and
   (true-listp m)
   (true-listp (retrieve-rtmvars m))
   (true-listp (rtmintvars-i gvar1 m))
   (true-listp vals)
   (no-duplicates-p (append-lists (retrieve-rtmvars m)))
   (equal (len (rtmintvars-i gvar1 m)) (len vals))
   (m-correspondent-values-p m gm rm)
   (equal
    vals
    (apply-direct-rns-to-value-according-to-type
     (updated-cell gvar1 gval1 gm)
     (type-i gvar1 m)))
   (assoc-equal gvar1 m))
  (equal-values-and-attributes
   (get-cell gvar1 (input-var gvar1 gval1 gm))
   (rtmintvars-i gvar1 m)
   (input-vars-e (rtmintvars-i gvar1 m) vals rm)
   (type-i gvar1 m)))
 :hints (("Goal"
          :in-theory nil
          :use ((:instance result-of-input-one-var
                           (var0 gvar1) (var gvar1) (val gval1) (mem gm))
                (:instance lemma-help3
                 (idx (pos-equal-0 gvar1 m)))
                 (:instance
                 rtmintvars-i-is-pos-equal-0-of-retrieve-vars
                 (gvar gvar1))
                (:instance assoc-means-pos-in-range
                           (el gvar1)
                           (l m))
                (:instance
                  m-correspondent-values-implies-equal-values-and-attribus
                  (memgstate gm)
                  (memrstate rm))
                 (:instance input-vars-e-preserves-equal-values-attributes
                            (ll (retrieve-rtmvars m))
                            (gem1 (pos-equal-0 gvar1 m))
                            (type (type-i gvar1 m))
                            (mem rm)
                            (gmem gm)
                            (gvar gvar1)
                            (newv gval1)
                            )))))




(defthm equal-all-values-kept-by-appropriate-input-vars
 (implies
  (and
   (true-listp m)
   (true-listp (retrieve-rtmvars m))
   (true-listp (rtmintvars-i gvar1 m))
   (true-listp vals)
   (no-duplicates-p (append-lists (retrieve-rtmvars m)))
   (equal (len (rtmintvars-i gvar2 m)) (len vals))
   (m-correspondent-values-p m gm rm)
   (equal
    vals
    (apply-direct-rns-to-value-according-to-type
     (updated-cell gvar2 gval2 gm)
     (type-i gvar2 m)))
   (assoc-equal gvar1 m)
   (assoc-equal gvar2 m))
  (equal-values-and-attributes
   (get-cell gvar1 (input-var gvar2 gval2 gm))
   (rtmintvars-i gvar1 m)
   (input-vars-e (rtmintvars-i gvar2 m) vals rm)
   (type-i gvar1 m)))
 :hints (("Goal" :cases ( (equal gvar1 gvar2) ))
         ("Subgoal 2" :use (:instance other-variables-equal-values-attributes-input ))
         ("Subgoal 1" :use (:instance equal-values-kept-by-appropriate-input-vars (gvar1 gvar2) (gval1 gval2)))))




(defthm hlemma1
 (implies
  (and
   (alistp m)
   (in-range idx m))
  (and
   (true-listp m)
   (assoc-equal (car (nth idx m)) m)))
 :rule-classes nil
 :otf-flg t)

(defun correct-wrt-anyarity (m)
  (if (endp m)
      (null m)
    (and
     (correct-type (type-0 m))
     (correct-wrt-anyarity (cdr m)))))


(defthm hlemma2
 (implies
  (and
   (correct-wrt-anyarity m)
   (in-range idx m))
   (true-listp (nth idx m)))
 :hints (("Goal" :in-theory (enable rtmintvars-0)))
 :rule-classes nil)


(defthm equal-all-values-kept-by-appropriate-input-vars-idxed
 (implies
  (and
   (alistp m)
   (correct-wrt-anyarity m)
   (true-listp (retrieve-rtmvars m))
   (true-listp vals)
   (no-duplicates-p (append-lists (retrieve-rtmvars m)))
   (no-duplicates-p (retrieve-gemvars m))
   (equal (len (cdr (nth idx2 m))) (len vals))
   (m-correspondent-values-p m gm rm)
   (equal
    vals
    (apply-direct-rns-to-value-according-to-type
     (updated-cell (car (nth idx2 m)) gval2 gm)
     (type-i-idx m idx2)))
   (in-range idx m)
   (in-range idx2 m))
  (equal-values-and-attributes
   (get-cell (car (nth idx m)) (input-var (car (nth idx2 m)) gval2 gm))
   (cdr (nth idx m))
   (input-vars-e (cdr (nth idx2 m)) vals rm)
   (type-i-idx m idx)))
  :hints (("Goal" :in-theory (union-theories (current-theory 'ground-zero) '((:definition in-range)))
	   :use ( hlemma2
                  (:instance hlemma1 (idx idx))
                  (:instance hlemma1 (idx idx2))
                  (:instance type-i-is-typeidx (idx idx))
                  (:instance type-i-is-typeidx (idx idx2))
		  (:instance rtmintvars-i-is-cdr-of-nth-entry (gvar (car (nth idx m))))
		  (:instance rtmintvars-i-is-cdr-of-nth-entry (gvar (car (nth idx2 m))))
		  (:instance equal-all-values-kept-by-appropriate-input-vars
                             (gvar1 (car (nth idx m)))
                             (gvar2 (car (nth idx2 m))))
		  (:instance no-duplicates-has-pos-equal-right-in-that-place (l m) (idx idx))
		  (:instance no-duplicates-has-pos-equal-right-in-that-place (l m) (idx idx2)))))
  :otf-flg t)



(defthm type-invariance-after-input
 (equal
  (var-type (get-cell v (input-var v2 val2 gm)))
  (var-type (get-cell v gm)) )
 :hints (("Goal" :in-theory (enable put-cell get-cell var-type))))





(defthm m-correspondence-kept-by-appropriate-input-vars-idxed
 (implies
  (and
   (alistp m)
   (correct-wrt-anyarity m)
   (true-listp (retrieve-rtmvars m))
   (true-listp vals)
   (no-duplicates-p (append-lists (retrieve-rtmvars m)))
   (no-duplicates-p (retrieve-gemvars m))
   (equal (len (cdr (nth idx2 m))) (len vals))
   (m-correspondent-values-p m gm rm)
   (equal
    vals
    (apply-direct-rns-to-value-according-to-type
     (updated-cell (car (nth idx2 m)) gval2 gm)
     (type-i-idx m idx2)))
   (in-range idx2 m))
  (m-correspondent-values-p
   m
   (input-var (car (nth idx2 m)) gval2 gm)
   (input-vars-e (cdr (nth idx2 m)) vals rm)))
 :hints (("Goal"
          :in-theory nil
          :use ( (:instance equal-all-values-kept-by-appropriate-input-vars-idxed
				  (idx (bad-idx-eqv-va m
                                                       (input-var (car (nth idx2 m)) gval2 gm)
                                                       (input-vars-e (cdr (nth idx2 m)) vals rm))))
                 (:instance hlemma2 (idx idx2))))
	  ("Goal'" :cases ( (in-range (bad-idx-eqv-va m
                                                      (input-var (car (nth idx2 m)) gval2 gm)
                                                      (input-vars-e (cdr (nth idx2 m)) vals rm)) m) ))
	  ("Subgoal 2"
                       :in-theory '((:forward-chaining alistp-forward-to-true-listp)
                                    (:rewrite if-bad-index-not-in-range-then-m-corr)))
	  ("Subgoal 1"
           :in-theory '((:rewrite if-bad-index-in-range-thne-must-be-different-vs)))))


(defun input-var-seq (vars vals m mem)
 (if (endp vars)
     mem
     (input-var
       (car (nth (car vars) m))
       (car vals)
       (input-var-seq
        (cdr vars)
        (cdr vals)
        m
        mem))))





(defun input-vars-seq (varsseqs valsseqs mem)
 (if (endp varsseqs)
     mem
     (input-vars-e
      (car varsseqs)
      (car valsseqs)
      (input-vars-seq
       (cdr varsseqs)
       (cdr valsseqs)
       mem))))

(defthm invariant1-s
 (implies
  (equal (var-value cell1) (var-value cell2))
  (equal
      (apply-direct-rns-to-value-according-to-type cell1 ty)
      (apply-direct-rns-to-value-according-to-type cell2 ty)))
 :rule-classes nil)


(defthm invariant2-s
 (equal (var-value (updated-cell var val mem1))
        (var-value (updated-cell var val mem2)))
 :hints (("Goal" :in-theory (enable var-value make-cell)))
 :rule-classes nil)

(defthm invariant3-s
 (equal
  (apply-direct-rns-to-value-according-to-type
   (updated-cell
    (car (nth (car vars) m))
    (car vals)
    (input-var-seq (cdr vars) (cdr vals) m gm))
   (type-i-idx m (car vars)))
  (apply-direct-rns-to-value-according-to-type
   (updated-cell
    (car (nth (car vars) m))
    (car vals)
    gm)
   (type-i-idx m (car vars))))
 :hints (("Goal" :use ((:instance invariant1-s
                                  (cell1    (updated-cell
                                             (car (nth (car vars) m))
                                             (car vals)
                                             (input-var-seq (cdr vars) (cdr vals) m gm)))
                                  (cell2    (updated-cell
                                             (car (nth (car vars) m))
                                             (car vals)
                                             gm))
                                  ( ty      (type-i-idx m (car vars))))
                       (:instance invariant2-s
                                  (var (car (nth (car vars) m)))
                                  (val (car vals))
                                  (mem1 (input-var-seq (cdr vars) (cdr vals) m gm))
                                  (mem2 gm)))))
 :rule-classes nil)



(defun correct-encoding (vars vals varsseqs valsseqs m gm)
 (if (endp vars)
     (endp varsseqs)
     (and
      (consp (car varsseqs))
      (true-listp (car varsseqs))
      (in-range (car vars) m)
      (equal (car varsseqs) (cdr (nth (car vars) m)))
      (true-listp (car valsseqs))
      (equal (len (car varsseqs)) (len (car valsseqs)))
      (equal
       (car valsseqs)
       (apply-direct-rns-to-value-according-to-type
        (updated-cell
         (car (nth (car vars) m))
         (car vals)
         gm)
        (type-i-idx m (car vars))))
      (correct-encoding
       (cdr vars)
       (cdr vals)
       (cdr varsseqs)
       (cdr valsseqs)
       m
       gm))))


(defun ind-scheme (vars vals varsseqs valsseqs)
 (if (endp vars)
     (append vars vals varsseqs valsseqs)
     (ind-scheme
      (cdr vars)
      (cdr vals)
      (cdr varsseqs)
      (cdr valsseqs))))





(defthm m-correspondence-kept-by-appropriate-inputs
 (implies
  (and
   (alistp m)
   (correct-wrt-anyarity m)
   (true-listp (retrieve-rtmvars m))
   (no-duplicates-p (append-lists (retrieve-rtmvars m)))
   (no-duplicates-p (retrieve-gemvars m))
   (m-correspondent-values-p m gm rm)
   (correct-encoding vars vals varsseqs valsseqs m gm))
   (m-correspondent-values-p
    m
    (input-var-seq vars vals m gm)
    (input-vars-seq varsseqs valsseqs rm)))
 :hints (("Goal"
          :induct (ind-scheme vars vals varsseqs valsseqs))
         ("Subgoal *1/2"
          :in-theory (current-theory 'ground-zero)
          :use
          ( correct-encoding
            invariant3-s
            (:instance input-var-seq (mem gm))
            (:instance input-vars-seq (mem rm))
            (:instance m-correspondence-kept-by-appropriate-input-vars-idxed
                       (gm (input-var-seq (cdr vars) (cdr vals) m gm))
                       (rm (input-vars-seq (cdr varsseqs) (cdr valsseqs) rm))
                       (idx2 (car vars))
                       (vals (car valsseqs))
                       (gval2 (car vals)))))))




(defthm input-var-preserves-correct-wrt-arity
 (implies
  (correct-wrt-arity m gm)
  (correct-wrt-arity m  (input-var v2 val2 gm)))
 :hints (("Goal" :induct (len m)
          :in-theory (disable result-of-input-one-var correct-type type-0 var-type input-var))))

(defthm input-var-seq-preserves-correct-wrt-arity
 (implies
  (correct-wrt-arity m gm)
  (correct-wrt-arity m  (input-var-seq vs2 vals2 m gm)))
 :hints (("Goal" :induct (input-var-seq vs2 vals2 m gm))
         ("Subgoal *1/2" :in-theory nil
          :use ((:instance input-var-seq (vars vs2) (vals vals2) (mem gm))
                               (:instance input-var-preserves-correct-wrt-arity
                                          (v2 (car (nth (car vs2) m)))
                                          (val2 (car vals2))
                                          (gm (input-var-seq (cdr vs2) (cdr vals2) m gm)))))))




(defthm input-var-doesnot-decrement-vars
 (implies
  (vars-inclusion m gm)
  (vars-inclusion m (input-var anyvar anyval gm)))
 :hints (("Goal" :in-theory (enable put-cell get-cell))))

(defthm input-var-seq-doesnot-decrement-vars
 (implies
  (vars-inclusion m gm)
  (vars-inclusion m (input-var-seq vars vals m gm)))
 :hints (("Goal" :induct (input-var-seq vars vals m gm))
         ("Subgoal *1/2" :use (:instance input-var-doesnot-decrement-vars
                                         (anyvar (car (nth (car vars) m)))
                                         (anyval (car vals))
                                         (gm (input-var-seq (cdr vars) (cdr vals) m gm))))))


(defthm a-var-in-m-appears-in-mem
  (implies
  (and
   (in-range var m)
   (vars-inclusion m mem))
  (assoc-equal (car (nth var m)) mem))
  :rule-classes nil)


(defthm input-existing-var-does-not-increment-vars0
 (implies
  (and
   (vars-inclusion m mem)
   (assoc-equal var mem)
   (vars-inclusion mem m))
  (vars-inclusion
   (input-var var val mem)
   m))
 :hints (("Goal" :in-theory (enable put-cell get-cell)))
 :rule-classes nil)

(defthm input-existing-var-does-not-increment-vars
 (implies
  (and
   (in-range var m)
   (vars-inclusion m mem)
   (vars-inclusion mem m))
  (vars-inclusion
   (input-var (car (nth var m)) val mem)
   m))
 :hints (("Goal" :use ((:instance a-var-in-m-appears-in-mem)
                       (:instance input-existing-var-does-not-increment-vars0
                                  (var (car (nth var m))))))))


(defun in-ranges (vars m)
 (if (endp vars)
     t
     (and (in-range (car vars) m)
          (in-ranges (cdr vars) m))))

(defthm input-exisitng-varseq-doesnot-increment-vars
 (implies
  (and
   (in-ranges vars m)
   (vars-inclusion m gm)
   (vars-inclusion gm m))
  (vars-inclusion (input-var-seq vars vals m gm) m))
 :hints (("Goal" :induct (input-var-seq vars vals m gm))
         ("Subgoal *1/2" :use (:instance input-existing-var-does-not-increment-vars
                                         (var (car vars))
                                         (val (car vals))
                                         (mem (input-var-seq (cdr vars) (cdr vals) m gm))))))

(defthm input-var-invariant-wrt-var-attributes
 (equal (var-attributes vars mem)
        (var-attributes vars (input-var var val mem)))
 :hints (("Goal" :in-theory (enable put-cell get-cell var-attribute make-cell)))
 :rule-classes nil)

(defthm input-varseq-invariant-wrt-var-attributes
 (equal (var-attributes otvars mem)
        (var-attributes otvars (input-var-seq vars vals m mem)))
 :hints (("Goal" :induct (input-var-seq vars vals m mem))
         ("Subgoal *1/2" :use ( (:instance input-var-seq)
                                (:instance input-var-invariant-wrt-var-attributes
                                         (var (car (nth (car vars) m)))
                                         (val (car vals))
                                         (vars otvars)
                                         (mem (input-var-seq (cdr vars) (cdr vals) m mem))))))
 :rule-classes nil)

(defthm put-update-invariant-wrt-var-attributes
  (equal
   (var-attributes otvars mem)
   (var-attributes otvars (put-cell var (updated-cell var val mem) mem)))
  :hints (("Goal"
           :in-theory (enable put-cell get-cell var-attribute make-cell)))
  :rule-classes nil)


(defthm input-vars-e-invariant-wrt-var-attributes
 (equal (var-attributes otvars mem)
        (var-attributes otvars (input-vars-e vars vals mem)))
 :hints (("Goal"  :induct (input-vars-e vars vals mem))
         ("Subgoal *1/2" :use (:instance put-update-invariant-wrt-var-attributes
                                         (var (car vars))
                                         (val (car vals)))))
 :rule-classes nil)

(defthm input-vars-seqs-invariant-wrt-var-attributes
 (equal (var-attributes otvars mem)
        (var-attributes otvars (input-vars-seq varsseqs valsseqs mem)))
 :hints (("Goal"  :induct (input-vars-seq varsseqs valsseqs mem))
         ("Subgoal *1/2" :use (:instance input-vars-e-invariant-wrt-var-attributes
                                         (vars (car varsseqs))
                                         (vals (car valsseqs))
                                         (mem  (input-vars-seq (cdr varsseqs) (cdr valsseqs) mem)))))
 :rule-classes nil)

(defthm input-vars-seqs-preserves-point-to-good-rtm-var-sets
 (implies
  (m-entries-point-to-good-rtm-var-sets m rm)
  (m-entries-point-to-good-rtm-var-sets m (input-vars-seq varsseqs valsseqs rm)))
 :hints (("Goal" :induct (len m))
         ("Subgoal *1/1" :use (:instance input-vars-seqs-invariant-wrt-var-attributes
                                         (otvars (rtmintvars-0 m))
                                         (mem rm)))))


(defthm correct-arity-implies-correct-anyarity
 (implies
  (correct-wrt-arity m gm)
  (correct-wrt-anyarity m))
 :rule-classes nil)


(defthm correct-encoding-implies-in-ranges
 (implies
  (correct-encoding vars vals varsseqs valsseqs m gm)
  (in-ranges vars m))
 :rule-classes nil)


(defthm input-preserves-good-mapping-wrt-memories
 (implies
  (and
   (good-mapping m)
   (correct-encoding vars vals varsseqs valsseqs m gm)
   (good-mapping-wrt-memories m gm rm))
  (good-mapping-wrt-memories m (input-var-seq vars vals m gm) (input-vars-seq varsseqs valsseqs rm)))
 :hints (("Goal"
          :use ( correct-arity-implies-correct-anyarity
                 correct-encoding-implies-in-ranges
                 input-vars-seqs-preserves-point-to-good-rtm-var-sets
                 input-exisitng-varseq-doesnot-increment-vars
                 input-var-seq-doesnot-decrement-vars
                 (:instance input-var-seq-preserves-correct-wrt-arity (vs2 vars) (vals2 vals))
                 m-correspondence-kept-by-appropriate-inputs))))


(defthm a-cell-remains-typed-after-good-put
 (implies
  (and
   (is-mem-cell-p (get-cell anyvar mem))
   (is-mem-cell-p (get-cell var mem))
   (if (equal (var-type (get-cell var mem)) 'bool)
              (my-or-2 (equal val 0) (equal val 1))
              (integerp val)))
  (is-mem-cell-p (get-cell anyvar (input-var var val mem))))
 :hints (("Goal" :in-theory (enable get-cell put-cell my-or-2 var-type var-attribute var-value))))


(defthm updated-cell-is-typed-if-ok
 (implies
  (and
   (is-mem-cell-p (get-cell var mem))
   (if (equal (var-type (get-cell var mem)) 'bool)
              (my-or-2 (equal val 0) (equal val 1))
              (integerp val)))
  (is-mem-cell-p (updated-cell var val mem)))
 :hints (("Goal" :in-theory (enable get-cell put-cell my-or-2 var-type var-attribute var-value))))

(defthm input-okvar-keeps-typed-amem
 (implies
  (and
   (is-typed-amem-p mem)
   (is-mem-cell-p (get-cell var mem))
   (if (equal (var-type (get-cell var mem)) 'bool)
              (my-or-2 (equal val 0) (equal val 1))
              (integerp val)))
  (is-typed-amem-p (input-var var val mem)))
 :hints (("Goal"
          :use
           ( (:instance putting-a-new-cell-preserves-typed-amem
                        (new-cell (updated-cell var val mem))
                        (c        var))
             (:instance updated-cell-is-typed-if-ok)))))

(defun ok-vars (vars vals m mem)
 (if (endp vars)
     t
     (and
      (is-mem-cell-p
       (get-cell (car (nth (car vars) m))
                 (input-var-seq (cdr vars) (cdr vals) m mem)))
      (if (equal (var-type (get-cell (car (nth (car vars) m))
                                     (input-var-seq (cdr vars) (cdr vals) m mem))) 'bool)
          (my-or-2 (equal (car vals) 0) (equal (car vals) 1))
          (integerp (car vals)))
      (ok-vars (cdr vars) (cdr vals) m mem))))

(defthm input-okvar-seq-keeps-typed-amem
 (implies
  (and
   (is-typed-amem-p mem)
   (ok-vars vars vals m mem))
  (is-typed-amem-p (input-var-seq vars vals m mem)))
 :hints (("Goal" :induct (input-var-seq vars vals m mem))
         ("Subgoal *1/2" :use
          ( (:instance ok-vars)
            (:instance input-var-seq)
            (:instance input-okvar-keeps-typed-amem
                       (var (car (nth (car vars) m)))
                       (val (car vals))
                       (mem (input-var-seq (cdr vars) (cdr vals) m mem)))))))

(defun bounded-values (vals)
 (if (endp vals)
     t
     (and (natp (car vals))
          (< (car vals) (prod *rns*))
          (bounded-values (cdr vals)))))

(defthm bounded-input-preserves-boundedness
 (implies
  (and
   (bounded-amem-p mem)
   (bounded-values vals)
   (true-listp vars)
   (true-listp vals)
   (equal (len vars) (len vals)))
  (bounded-amem-p (input-var-seq vars vals m mem)))
 :hints (("Goal" :in-theory (enable var-value get-cell put-cell))))

(defthm input-okvar-preserves-a-mem-cell
 (implies
  (and
   (is-mem-cell-p (get-cell v mem))
   (is-typed-amem-p mem)
   (is-mem-cell-p (get-cell var mem))
   (if (equal (var-type (get-cell var mem)) 'bool)
              (my-or-2 (equal val 0) (equal val 1))
              (integerp val)))
  (is-mem-cell-p (get-cell v (input-var var val mem))))
 :hints (("Goal" :in-theory (enable get-cell put-cell my-or-2 var-value var-attribute var-type))))



(defthm input-var-preserves-gem-instruction
 (implies
  (and
   (gem-instruction-p instr mem)
   (is-typed-amem-p mem)
   (is-mem-cell-p (get-cell var mem))
   (if (equal (var-type (get-cell var mem)) 'bool)
              (my-or-2 (equal val 0) (equal val 1))
              (integerp val)))
  (gem-instruction-p instr (input-var var val mem)))
 :hints (("Goal" :in-theory '((:definition gem-instruction-p))
          :use ( (:instance input-okvar-preserves-a-mem-cell (v (par1 instr)))
                 (:instance input-okvar-preserves-a-mem-cell (v (par2 instr)))
                 (:instance input-okvar-preserves-a-mem-cell (v (par3 instr)))
                 (:instance type-invariance-after-input (v (par1 instr)) (v2 var) (val2 val) (gm mem))
                 (:instance type-invariance-after-input (v (par2 instr)) (v2 var) (val2 val) (gm mem))
                 (:instance type-invariance-after-input (v (par3 instr)) (v2 var) (val2 val) (gm mem))))))

(defthm input-var-preserves-gem-instruction-list
 (implies
  (and
   (gem-instruction-list-p instrlist mem)
   (is-typed-amem-p mem)
   (is-mem-cell-p (get-cell var mem))
   (if (equal (var-type (get-cell var mem)) 'bool)
              (my-or-2 (equal val 0) (equal val 1))
              (integerp val)))
  (gem-instruction-list-p instrlist (input-var var val mem)))
 :hints (("Goal" :induct (gem-instruction-list-p instrlist mem))
         ("Subgoal *1/3" :in-theory '((:definition gem-instruction-list-p)))
         ("Subgoal *1/2" :in-theory '((:definition gem-instruction-list-p))
         :use (:instance input-var-preserves-gem-instruction
                         (instr (car instrlist))))))


(defthm input-var-seq-preserves-gem-instruction-list
 (implies
  (and
   (gem-instruction-list-p instrlist mem)
   (is-typed-amem-p mem)
   (ok-vars vars vals m mem))
  (gem-instruction-list-p instrlist (input-var-seq vars vals m mem)))
 :hints (("Goal" :induct (input-var-seq vars vals m mem))
         ("Subgoal *1/2"
          :in-theory (disable input-var is-mem-cell-p)
          :use
          ( (:instance ok-vars)
            (:instance input-var-seq)
            (:instance input-var-preserves-gem-instruction-list
                       (var (car (nth (car vars) m)))
                       (val (car vals))
                       (mem (input-var-seq (cdr vars) (cdr vals) m mem)))))))




(defthm skkk0 (equal (mem (make-state m p c)) m) )
(defthm skkk1 (equal (pcc (make-state m p c)) p) )
(defthm skkk2 (equal (code (make-state m p c)) c) )
(defthm skkk3 (implies (gem-statep s1) (equal (cdr (make-state m (pcc s1) (code s1))) (cdr s1))))
(defthm skkk4  (implies (gem-statep s1) (consp (cdr (make-state m (pcc s1) (code s1))))))
(defthm skkk5  (implies (gem-statep s1) (integerp (pcc (make-state m (pcc s1) (code s1))))))


(defthm prs01
 (implies
  (and
   (gem-statep gstate)
   (bounded-values vals)
   (true-listp vars)
   (true-listp vals)
   (equal (len vars) (len vals))
   (ok-vars vars vals m (mem gstate)))
  (and
   (consp (make-state (input-var-seq vars vals m (mem gstate)) (pcc gstate) (code gstate)))
   (consp (cdr (make-state (input-var-seq vars vals m (mem gstate)) (pcc gstate) (code gstate))))
   (integerp (pcc (make-state (input-var-seq vars vals m (mem gstate)) (pcc gstate) (code gstate))))))
 :hints (("Goal"
          :do-not-induct t
          :in-theory '((:definition make-state)
                       (:rewrite skkk0) (:rewrite skkk1) (:rewrite skkk2) (:rewrite skkk3))
          :use ((:instance skkk4 (s1 gstate) (m (input-var-seq vars vals m (mem gstate))))
                (:instance skkk5 (s1 gstate) (m (input-var-seq vars vals m (mem gstate))))
                (:instance gem-statep (x gstate))
                (:instance gem-statep (x (make-state (input-var-seq vars vals m (mem gstate)) (pcc gstate) (code gstate)))))))
 :rule-classes nil)




(defthm prs02
 (implies
  (and
   (gem-statep gstate)
   (bounded-values vals)
   (true-listp vars)
   (true-listp vals)
   (equal (len vars) (len vals))
   (ok-vars vars vals m (mem gstate)))
  (and
   (gem-instruction-list-p (code (make-state (input-var-seq vars vals m (mem gstate)) (pcc gstate) (code gstate)))
                           (mem (make-state (input-var-seq vars vals m (mem gstate)) (pcc gstate) (code gstate))))
    (bounded-amem-p (mem (make-state (input-var-seq vars vals m (mem gstate)) (pcc gstate) (code gstate))))
    (is-typed-amem-p (mem (make-state (input-var-seq vars vals m (mem gstate)) (pcc gstate) (code gstate))))))
 :hints (("Goal"
          :do-not-induct t
          :in-theory  '( (:rewrite skkk0) (:rewrite skkk1) (:rewrite skkk2) (:rewrite skkk3))
          :use (
                (:instance gem-statep (x gstate))
                (:instance gem-statep (x (make-state (input-var-seq vars vals m (mem gstate)) (pcc gstate) (code gstate))))
                (:instance input-var-seq-preserves-gem-instruction-list
                           (instrlist (code gstate)) (mem (mem gstate)))
                (:instance bounded-input-preserves-boundedness (mem (mem gstate)))
                (:instance input-okvar-seq-keeps-typed-amem (mem (mem gstate))))))
 :rule-classes nil)


(defun ok-gem-vars-vals (vars vals m mem)
 (and
   (bounded-values vals)
   (true-listp vars)
   (true-listp vals)
   (equal (len vars) (len vals))
   (ok-vars vars vals m mem)))


(defthm ok-vars-preserve-gem-statep
 (implies
  (and
   (gem-statep gstate)
   (ok-gem-vars-vals vars vals m (mem gstate)))
  (gem-statep (make-state (input-var-seq vars vals m (mem gstate)) (pcc gstate) (code gstate))))
 :hints (("Goal"
          :do-not-induct t
          :in-theory  '((:definition ok-gem-vars-vals) (:definition gem-statep))
          :use (prs01 prs02))))



(defun ok-rtm-vars (vars vals mem)
 (if (endp vars)
     t
     (and
      (is-mem-cell-p
       (get-cell (car vars) mem))
      (if (equal (var-type (get-cell (car vars)
                                     mem)) 'bool)
          (my-or-2 (equal (car vals) 0) (equal (car vals) 1))
          (integerp (car vals)))
      (ok-rtm-vars (cdr vars) (cdr vals) (put-cell (car vars) (updated-cell (car vars) (car vals) mem) mem)))))




(defthm ok-rtm-vars-means-input-vars-preserves-typed-mem
 (implies
  (and
   (is-typed-amem-p mem)
   (ok-rtm-vars vars vals mem))
  (is-typed-amem-p (input-vars-e vars vals mem)))
 :hints (("Subgoal *1/2" :use
          ((:instance putting-a-new-cell-preserves-typed-amem
                     (c (car vars))
                     (new-cell (updated-cell (car vars) (car vals) mem)))
          (:instance updated-cell-is-typed-if-ok
                     (var (car vars))
                     (val (car vals)))))))


(defun ok-rtmvarsseq (varsseqs valsseqs mem)
 (if (endp varsseqs)
     t
     (and
      (ok-rtm-vars (car varsseqs) (car valsseqs)
                   (input-vars-seq (cdr varsseqs) (cdr valsseqs) mem))
      (ok-rtmvarsseq (cdr varsseqs) (cdr valsseqs) mem))))

(defthm ok-rtmvarsseqs-kjeeps-typed-amem
  (implies
  (and
   (is-typed-amem-p mem)
   (ok-rtmvarsseq varsseqs valsseqs mem))
  (is-typed-amem-p (input-vars-seq varsseqs valsseqs mem))))



(defthm input-var-preserves-rtm-instruction
 (implies
  (and
   (rtm-instruction-p instr mem)
   (is-typed-amem-p mem)
   (is-mem-cell-p (get-cell var mem))
   (if (equal (var-type (get-cell var mem)) 'bool)
              (my-or-2 (equal val 0) (equal val 1))
              (integerp val)))
  (rtm-instruction-p instr (input-var var val mem)))
 :hints (("Goal" :in-theory '((:definition rtm-instruction-p))
          :use ( (:instance input-okvar-preserves-a-mem-cell (v (par1 instr)))
                 (:instance input-okvar-preserves-a-mem-cell (v (par2 instr)))
                 (:instance input-okvar-preserves-a-mem-cell (v (par3 instr)))
                 (:instance type-invariance-after-input (v (par1 instr)) (v2 var) (val2 val) (gm mem))
                 (:instance type-invariance-after-input (v (par2 instr)) (v2 var) (val2 val) (gm mem))
                 (:instance type-invariance-after-input (v (par3 instr)) (v2 var) (val2 val) (gm mem))))))



(defthm input-vars-preserves-rtm-instruction
 (implies
  (and
   (rtm-instruction-p instr mem)
   (ok-rtm-vars vars vals mem)
   (is-typed-amem-p mem))
  (rtm-instruction-p instr (input-vars-e vars vals mem)))
 :hints (("Goal" :induct (input-vars-e vars vals mem))
         ("Subgoal *1/2"
          :in-theory '((:definition input-var) (:definition input-vars-e))
          :use (ok-rtm-vars
                (:instance input-var-preserves-rtm-instruction
                           (var (car vars))
                           (val (car vals))
                           (mem mem))
                (:instance input-okvar-keeps-typed-amem
                           (var (car vars))
                           (val (car vals))
                           (mem mem))))))



(defthm input-vars-e-preserves-rtm-instruction-list
 (implies
  (and
   (rtm-instruction-list-p instrlist mem)
   (ok-rtm-vars vars vals mem)
   (is-typed-amem-p mem))
  (rtm-instruction-list-p instrlist (input-vars-e vars vals mem)))
 :hints (("Goal" :induct (rtm-instruction-list-p instrlist mem))
         ("Subgoal *1/3" :in-theory '((:definition rtm-instruction-list-p)))
         ("Subgoal *1/2" :in-theory '((:definition rtm-instruction-list-p))
         :use (:instance input-vars-preserves-rtm-instruction
                         (instr (car instrlist))))))


(defthm input-vars-seq-preserves-rtm-instruction-list
 (implies
  (and
   (rtm-instruction-list-p instrlist mem)
   (ok-rtmvarsseq varsseqs valsseqs mem)
   (is-typed-amem-p mem))
  (rtm-instruction-list-p instrlist (input-vars-seq varsseqs valsseqs mem))))



(defthm skkk3r  (implies (rtm-statep s1) (equal (cdr (make-state m (pcc s1) (code s1))) (cdr s1))))
(defthm skkk4r  (implies (rtm-statep s1) (consp (cdr (make-state m (pcc s1) (code s1))))))
(defthm skkk5r  (implies (rtm-statep s1) (integerp (pcc (make-state m (pcc s1) (code s1))))))

(defthm prs03
 (implies
  (rtm-statep rstate)
  (and
   (consp (make-state (input-vars-seq varsseqs valsseqs (mem rstate)) (pcc rstate) (code rstate)))
   (consp (cdr (make-state (input-vars-seq varsseqs valsseqs (mem rstate)) (pcc rstate) (code rstate))))
   (integerp (pcc (make-state (input-vars-seq varsseqs valsseqs (mem rstate)) (pcc rstate) (code rstate))))))
 :hints (("Goal"
          :do-not-induct t
          :in-theory '((:definition make-state)
                       (:rewrite skkk0) (:rewrite skkk1) (:rewrite skkk2) (:rewrite skkk3r))
          :use ((:instance skkk4r (s1 rstate) (m (input-vars-seq varsseqs valsseqs (mem rstate))))
                (:instance skkk5r (s1 rstate) (m (input-vars-seq varsseqs valsseqs (mem rstate))))
                (:instance rtm-statep (x rstate))
                (:instance rtm-statep (x (make-state (input-var-seq vars vals m (mem rstate)) (pcc rstate) (code rstate)))))))
 :rule-classes nil)



(defthm prs04
 (implies
  (and
   (rtm-statep rstate)
   (ok-rtmvarsseq varsseqs valsseqs (mem rstate)))
  (and
   (rtm-instruction-list-p (code (make-state (input-vars-seq varsseqs valsseqs (mem rstate)) (pcc rstate) (code rstate)))
                           (mem (make-state (input-vars-seq varsseqs valsseqs (mem rstate)) (pcc rstate) (code rstate))))
    (is-typed-amem-p (mem (make-state (input-vars-seq varsseqs valsseqs (mem rstate)) (pcc rstate) (code rstate))))))
 :hints (("Goal"
          :do-not-induct t
          :in-theory  '( (:rewrite skkk0) (:rewrite skkk1) (:rewrite skkk2) (:rewrite skkk3r))
          :use (
                (:instance rtm-statep (x rstate))
                (:instance rtm-statep (x (make-state (input-vars-seq varsseqs valsseqs (mem rstate)) (pcc rstate) (code rstate))))
                (:instance input-vars-seq-preserves-rtm-instruction-list
                           (instrlist (code rstate)) (mem (mem rstate)))
                (:instance ok-rtmvarsseqs-kjeeps-typed-amem (mem (mem rstate))))))
 :rule-classes nil)


(defthm ok-rtmvarsseqs-preserve-rtmstatehood
 (implies
  (and
   (rtm-statep rstate)
   (ok-rtmvarsseq varsseqs valsseqs (mem rstate)))
  (rtm-statep (make-state (input-vars-seq varsseqs valsseqs (mem rstate)) (pcc rstate) (code rstate))))
 :hints (("Goal" :in-theory '((:definition rtm-statep))
          :use (prs03 prs04))))







(defthm same-pcc-after-execution-regardelss-of-mem
 (implies
  (and
   (equal (code st) (code st2))
   (equal (pcc st) (pcc st2)))
  (equal
        (pcc (execute-instruction st))
        (pcc (execute-instruction st2)))))



(defun indsc (st1 st2 n)
 (if (zp n)
     nil
     (append st1 st2
      (indsc
       (execute-instruction st1) (execute-instruction st2) (1- n)))))



(defthm listinstr-is-independent-from-mem
 (implies (and
           (equal (pcc st) (pcc st2))
           (equal (code st) (code st2)))
          (equal (listinstr st n) (listinstr st2 n)))
 :hints (("Goal" :induct (indsc st st2 n))
         ("Subgoal *1/2"
          :in-theory nil
          :use ( listinstr
                 (:instance listinstr (st st2))
                 (:instance same-pcc-after-execution-regardelss-of-mem)
                 (:instance execute-instruction-does-not-touch-code)
                 (:instance execute-instruction-does-not-touch-code (st st2)))))
 :rule-classes nil)


(defthm listpars1-independent-from-mem
  (implies
   (and
    (equal (pcc st) (pcc st2))
    (equal (code st) (code st2)))
  (equal (listpars1 st n) (listpars1 st2 n)))
  :hints (("Goal" :in-theory nil
           :use ( listinstr-is-independent-from-mem
                         (:instance pars1-instruction-is-listpars1 (st st))
                         (:instance pars1-instruction-is-listpars1 (st st2))))))



(defun pars2-instructions (listinstr)
  (if (endp listinstr)
      nil
    (cons (par2 (car listinstr))
	  (pars2-instructions (cdr listinstr)))))

(defthm pars2-instruction-is-listpars2
  (equal
   (pars2-instructions (listinstr st n))
   (listpars2 st n)))


(defthm listpars2-independent-from-mem
  (implies
   (and
    (equal (pcc st) (pcc st2))
    (equal (code st) (code st2)))
  (equal (listpars2 st n) (listpars2 st2 n)))
  :hints (("Goal" :in-theory nil
           :use ( listinstr-is-independent-from-mem
                         (:instance pars2-instruction-is-listpars2 (st st))
                         (:instance pars2-instruction-is-listpars2 (st st2))))))


(defun pars3-instructions (listinstr)
  (if (endp listinstr)
      nil
    (cons (par3 (car listinstr))
	  (pars3-instructions (cdr listinstr)))))

(defthm pars3-instruction-is-listpars3
  (equal
   (pars3-instructions (listinstr st n))
   (listpars3 st n)))


(defthm listpars3-independent-from-mem
  (implies
   (and
    (equal (pcc st) (pcc st2))
    (equal (code st) (code st2)))
  (equal (listpars3 st n) (listpars3 st2 n)))
  :hints (("Goal" :in-theory nil
           :use ( listinstr-is-independent-from-mem
                         (:instance pars3-instruction-is-listpars3 (st st))
                         (:instance pars3-instruction-is-listpars3 (st st2))))))


(defun pars4-instructions (listinstr)
  (if (endp listinstr)
      nil
    (cons (par4 (car listinstr))
	  (pars4-instructions (cdr listinstr)))))

(defthm pars4-instruction-is-listpars4
  (equal
   (pars4-instructions (listinstr st n))
   (listpars4 st n)))


(defthm listpars4-independent-from-mem
  (implies
   (and
    (equal (pcc st) (pcc st2))
    (equal (code st) (code st2)))
  (equal (listpars4 st n) (listpars4 st2 n)))
  :hints (("Goal" :in-theory nil
           :use ( listinstr-is-independent-from-mem
                         (:instance pars4-instruction-is-listpars4 (st st))
                         (:instance pars4-instruction-is-listpars4 (st st2))))))


(defthm all-rtm-adds-independent-from-mem
  (implies
   (and
    (equal (pcc st) (pcc st2))
    (equal (code st) (code st2)))
  (equal (all-rtm-adds-for-n-steps st n) (all-rtm-adds-for-n-steps st2 n))))

(defthm all-rtm-subs-independent-from-mem
  (implies
   (and
    (equal (pcc st) (pcc st2))
    (equal (code st) (code st2)))
  (equal (all-rtm-subs-for-n-steps st n) (all-rtm-subs-for-n-steps st2 n))))

(defthm listinstr-independent-from-mem
  (implies
   (and
    (equal (pcc st) (pcc st2))
    (equal (code st) (code st2)))
  (equal (listinstr st n) (listinstr st2 n))))





(defthm same-pcc-after-execution-n-regardelss-of-mem
 (implies
  (and
   (equal (code st) (code st2))
   (equal (pcc st) (pcc st2)))
  (equal
        (pcc (execute-n-instructions st  n))
        (pcc (execute-n-instructions st2 n))))
 :hints (("Goal" :induct (indsc st st2 n))
         ("Subgoal *1/2"
          :in-theory '((:definition execute-n-instructions))
          :use
          (
            (:instance same-pcc-after-execution-regardelss-of-mem (st st))
            (:instance execute-instruction-does-not-touch-code (st st))
            (:instance execute-instruction-does-not-touch-code (st st2))))))


(defun good-translation-induct (gstate rstate gstate2 rstate2)
 (declare (xargs :measure (acl2-count (- (len (code gstate)) (pcc gstate)))))
  (if
      (or (not (integerp (pcc gstate)))
	  (< (pcc gstate) 0)
	  (>= (pcc gstate) (len (code gstate))))
      (append gstate rstate gstate2 rstate2)
    (case (opcode (nth (pcc gstate) (code gstate)))
      (gem-equ
	(good-translation-induct
	 (execute-instruction    gstate                   )
	 (execute-n-instructions rstate (* 2 (len *rns*)) )
	 (execute-instruction    gstate2                   )
	 (execute-n-instructions rstate2 (* 2 (len *rns*)) )
	 ))
      (gem-add
	(good-translation-induct
	 (execute-instruction    gstate             )
	 (execute-n-instructions rstate (len *rns*) )
	 (execute-instruction    gstate2             )
	 (execute-n-instructions rstate2 (len *rns*) )
	 ))
      (gem-sub
	(good-translation-induct
	 (execute-instruction    gstate             )
	 (execute-n-instructions rstate (len *rns*) )
	 (execute-instruction    gstate2             )
	 (execute-n-instructions rstate2 (len *rns*) )
	 ))
      (otherwise nil))))

(defthm good-translation-is-independent-from-mem
 (implies
  (and
   (equal (code gstate) (code gstate2))
   (equal (pcc gstate) (pcc gstate2))
   (equal (code rstate) (code rstate2))
   (equal (pcc rstate) (pcc rstate2))
   (good-translation-gem-rtm gstate rstate m))
  (good-translation-gem-rtm gstate2 rstate2 m))
 :hints (("Goal" :induct (good-translation-induct gstate rstate gstate2 rstate2 ))
         ("Subgoal *1/5" :in-theory '((:definition good-translation-gem-rtm)))
         ("Subgoal *1/4" :in-theory '((:definition good-translation-gem-rtm))
          :use ( (:instance execute-n-instruction-does-not-touch-code (st rstate) (n (len *rns*)))
                 (:instance execute-n-instruction-does-not-touch-code (st rstate2) (n (len *rns*)))
                 (:instance execute-instruction-does-not-touch-code (st gstate))
                 (:instance execute-instruction-does-not-touch-code (st gstate2))
                 (:instance same-pcc-after-execution-n-regardelss-of-mem (st rstate) (st2 rstate2) (n (len *rns*)))
                 (:instance same-pcc-after-execution-regardelss-of-mem (st gstate) (st2 gstate2))
                 (:instance all-rtm-subs-independent-from-mem (st rstate) (st2 rstate2) (n (len *rns*)))
                 (:instance listpars1-independent-from-mem (st rstate) (st2 rstate2) (n (len *rns*)))
                 (:instance listpars2-independent-from-mem (st rstate) (st2 rstate2) (n (len *rns*)))
                 (:instance listpars3-independent-from-mem (st rstate) (st2 rstate2) (n (len *rns*)))
                 (:instance listpars4-independent-from-mem (st rstate) (st2 rstate2) (n (len *rns*)))))
         ("Subgoal *1/3" :in-theory '((:definition good-translation-gem-rtm))
          :use ( (:instance execute-n-instruction-does-not-touch-code (st rstate) (n (len *rns*)))
                 (:instance execute-n-instruction-does-not-touch-code (st rstate2) (n (len *rns*)))
                 (:instance execute-instruction-does-not-touch-code (st gstate))
                 (:instance execute-instruction-does-not-touch-code (st gstate2))
                 (:instance same-pcc-after-execution-n-regardelss-of-mem (st rstate) (st2 rstate2) (n (len *rns*)))
                 (:instance same-pcc-after-execution-regardelss-of-mem (st gstate) (st2 gstate2))
                 (:instance all-rtm-adds-independent-from-mem (st rstate) (st2 rstate2) (n (len *rns*)))
                 (:instance listpars1-independent-from-mem (st rstate) (st2 rstate2) (n (len *rns*)))
                 (:instance listpars2-independent-from-mem (st rstate) (st2 rstate2) (n (len *rns*)))
                 (:instance listpars3-independent-from-mem (st rstate) (st2 rstate2) (n (len *rns*)))
                 (:instance listpars4-independent-from-mem (st rstate) (st2 rstate2) (n (len *rns*)))))
         ("Subgoal *1/2" :in-theory '((:definition good-translation-gem-rtm))
          :use ( (:instance execute-n-instruction-does-not-touch-code (st rstate) (n (* 2 (len *rns*))))
                 (:instance execute-n-instruction-does-not-touch-code (st rstate2) (n (* 2 (len *rns*))))
                 (:instance execute-instruction-does-not-touch-code (st gstate))
                 (:instance execute-instruction-does-not-touch-code (st gstate2))
                 (:instance same-pcc-after-execution-n-regardelss-of-mem (st rstate) (st2 rstate2) (n (* 2 (len *rns*))))
                 (:instance same-pcc-after-execution-regardelss-of-mem (st gstate) (st2 gstate2))
                 (:instance listinstr-independent-from-mem (st rstate) (st2 rstate2) (n (* 2 (len *rns*))))))
         ("Subgoal *1/1" :in-theory '((:definition good-translation-gem-rtm)))))



(defun correct-input (vars vals varsseqs valsseqs m gstate rstate)
 (and
  (ok-rtmvarsseq varsseqs valsseqs (mem rstate))
  (ok-gem-vars-vals vars vals m (mem gstate))
  (correct-encoding vars vals varsseqs valsseqs m (mem gstate))))


(defthm all-properties-hold-after-correct-input0
 (implies
  (and
   (correct-input vars vals varsseqs valsseqs m gstate rstate)
   (good-mapping m)
   (good-mapping-wrt-memories m (mem gstate) (mem rstate))
   (good-translation-gem-rtm gstate rstate m)
   (gem-statep gstate)
   (rtm-statep rstate)
   (>= (pcc gstate) 0)
   (m-correspondent-values-p m (mem gstate) (mem rstate)))
  (and
   (good-mapping-wrt-memories
    m
    (mem (make-state  (input-var-seq vars vals m (mem gstate)) (pcc gstate) (code gstate)))
    (mem (make-state  (input-vars-seq varsseqs valsseqs (mem rstate)) (pcc rstate) (code rstate))))
   (good-translation-gem-rtm
    (make-state  (input-var-seq vars vals m (mem gstate)) (pcc gstate) (code gstate))
    (make-state  (input-vars-seq varsseqs valsseqs (mem rstate)) (pcc rstate) (code rstate))
    m)
   (gem-statep (make-state  (input-var-seq vars vals m (mem gstate)) (pcc gstate) (code gstate)))
   (rtm-statep (make-state  (input-vars-seq varsseqs valsseqs (mem rstate)) (pcc rstate) (code rstate)))
   (>= (pcc (make-state  (input-var-seq vars vals m (mem gstate)) (pcc gstate) (code gstate))) 0)
   (m-correspondent-values-p
    m
    (mem (make-state  (input-var-seq vars vals m (mem gstate)) (pcc gstate) (code gstate)))
    (mem (make-state  (input-vars-seq varsseqs valsseqs (mem rstate)) (pcc rstate) (code rstate))))
))
 :hints (("Goal"
          :in-theory '((:definition correct-input)
                       (:type-prescription retrieve-rtmvars)
                       (:definition good-mapping-wrt-memories)
                       (:definition good-mapping)
                       (:rewrite skkk0)
                       (:rewrite skkk1)
                       (:rewrite skkk2))
          :use (
                ok-rtmvarsseqs-preserve-rtmstatehood
                ok-vars-preserve-gem-statep
                (:instance input-preserves-good-mapping-wrt-memories (gm (mem gstate)) (rm (mem rstate)))
                (:instance correct-arity-implies-correct-anyarity (gm (mem gstate)))
                (:instance m-correspondence-kept-by-appropriate-inputs (gm (mem gstate)) (rm (mem rstate)))
                (:instance good-translation-is-independent-from-mem
                  (gstate2 (make-state  (input-var-seq vars vals m (mem gstate)) (pcc gstate) (code gstate)))
                  (rstate2 (make-state  (input-vars-seq varsseqs valsseqs (mem rstate)) (pcc rstate) (code rstate))))))))


(defun input-gem (vars vals m gstate)
 (make-state  (input-var-seq vars vals m (mem gstate)) (pcc gstate) (code gstate)))

(defun input-rtm (varsseqs valsseqs rstate)
 (make-state  (input-vars-seq varsseqs valsseqs (mem rstate)) (pcc rstate) (code rstate)))



(defthm all-properties-hold-after-correct-input1
 (implies
  (and
   (correct-input vars vals varsseqs valsseqs m gstate rstate)
   (good-mapping m)
   (good-mapping-wrt-memories m (mem gstate) (mem rstate))
   (good-translation-gem-rtm gstate rstate m)
   (gem-statep gstate)
   (rtm-statep rstate)
   (>= (pcc gstate) 0)
   (m-correspondent-values-p m (mem gstate) (mem rstate)))
  (and
   (good-mapping-wrt-memories
    m
    (mem (input-gem vars vals m gstate))
    (mem (input-rtm varsseqs valsseqs rstate)))
   (good-translation-gem-rtm
    (input-gem vars vals m gstate)
    (input-rtm varsseqs valsseqs rstate)
    m)
   (gem-statep (input-gem vars vals m gstate))
   (rtm-statep (input-rtm varsseqs valsseqs rstate))
   (>= (pcc (input-gem vars vals m gstate)) 0)
   (m-correspondent-values-p
    m
    (mem (input-gem vars vals m gstate))
    (mem (input-rtm varsseqs valsseqs rstate)))))
 :hints (("Goal"
          :in-theory nil
          :use (input-gem
                input-rtm
                all-properties-hold-after-correct-input0))))

(defthm all-properties-hold-after-input-and-execution
 (implies
  (and
   (integerp n)
   (>= n 0)
   (correct-input vars vals varsseqs valsseqs m gstate rstate)
   (good-mapping m)
   (good-mapping-wrt-memories m (mem gstate) (mem rstate))
   (good-translation-gem-rtm gstate rstate m)
   (gem-statep gstate)
   (rtm-statep rstate)
   (>= (pcc gstate) 0)
   (m-correspondent-values-p m (mem gstate) (mem rstate)))
  (and
   (good-mapping-wrt-memories
    m
    (mem (execute-n-instructions (input-gem vars vals m gstate) n))
    (mem (execute-n-instructions
          (input-rtm varsseqs valsseqs rstate)
          (correspondent-steps n (input-gem vars vals m gstate)))))
   (good-translation-gem-rtm
    (execute-n-instructions (input-gem vars vals m gstate) n)
    (execute-n-instructions
          (input-rtm varsseqs valsseqs rstate)
          (correspondent-steps n (input-gem vars vals m gstate)))
    m)
   (gem-statep (execute-n-instructions (input-gem vars vals m gstate) n))
   (rtm-statep (execute-n-instructions
                (input-rtm varsseqs valsseqs rstate)
                (correspondent-steps n (input-gem vars vals m gstate))))
   (>= (pcc (execute-n-instructions (input-gem vars vals m gstate) n)) 0)
   (m-correspondent-values-p
    m
    (mem (execute-n-instructions (input-gem vars vals m gstate) n))
    (mem (execute-n-instructions
          (input-rtm varsseqs valsseqs rstate)
          (correspondent-steps n (input-gem vars vals m gstate)))))))
 :hints (("Goal" :in-theory '((:definition good-mapping)
                              (:definition good-mapping-wrt-memories))
          :use ( all-properties-hold-after-correct-input1
                 (:instance m-correspondence-and-other-conditions-kept-execution-on-n
                            (gstate (input-gem vars vals m gstate))
                            (rstate (input-rtm varsseqs valsseqs rstate)))))))

(defun restart-program (gstate)
 (make-state (mem gstate) 0 (code gstate)))

(defthm hh1
 (implies (gem-statep s) (gem-statep (restart-program s)))
 :rule-classes nil)

(defthm hh2
 (implies (rtm-statep s) (rtm-statep (restart-program s)))
 :rule-classes nil)


(defthm hh3
 (implies
  (and
   (good-mapping-wrt-memories m (mem gstate) (mem rstate))
   (good-translation-gem-rtm gstate rstate m)
   (correct-translation gem-program rtm-program m)
   (gem-statep gstate)
   (rtm-statep rstate)
   (m-correspondent-values-p m (mem gstate) (mem rstate)))
  (and
   (>= 0 (pcc (restart-program gstate)))
   (good-mapping-wrt-memories
    m
    (mem (restart-program gstate))
    (mem (restart-program rstate)))
   (m-correspondent-values-p
    m
    (mem (restart-program gstate))
    (mem (restart-program rstate)))))
 :hints (("Goal" :in-theory '(
                              (:definition restart-program)
                              (:rewrite skkk0)
                              (:rewrite skkk1)
                              (:rewrite skkk2))))
          :rule-classes nil)

(defthm hh5
 (and
  (equal (code (restart-program s)) (code s))
  (equal (pcc  (restart-program s)) (pcc (initial-state p)))))

(defthm hh6
 (implies
  (and
   (gem-statep gstate)
   (rtm-statep rstate)
   (equal (code gstate) (code (initial-state gem-program)))
   (equal (code rstate) (code (initial-state rtm-program)))
   (correct-translation gem-program rtm-program m))
  (good-translation-gem-rtm
   (restart-program gstate )
   (restart-program rstate )
   m))
 :hints (("Goal" :in-theory '((:definition make-state)
                              (:definition mem)
                              (:definition pcc)
                              (:definition code)
                              (:definition gem-statep)
                              (:definition rtm-statep)
                              (:definition correct-translation)
                              (:definition restart-program)
                              (:definition initial-state)
                              (:rewrite hh5)
                              (:rewrite skkk0)
                              (:rewrite skkk1)
                              (:rewrite skkk2))
         :use
         ((:instance hh5 (s gstate) (p gem-program))
          (:instance hh5 (s rstate) (p rtm-program))
          (:instance correct-translation (gemprog gem-program) (rtmprog rtm-program))
           (:instance good-translation-is-independent-from-mem
                      (gstate  (initial-state gem-program))
                         (rstate  (initial-state rtm-program))
                         (gstate2 (restart-program gstate ))
                         (rstate2 (restart-program rstate ))))))
 :rule-classes nil)




(defthm all-properties-hold-after-restarting-program
 (implies
  (and
   (equal (code gstate) (code (initial-state gem-program)))
   (equal (code rstate) (code (initial-state rtm-program)))
   (correct-translation gem-program rtm-program m)
   (good-mapping-wrt-memories m (mem gstate) (mem rstate))
   (good-translation-gem-rtm gstate rstate m)
   (correct-translation gem-program rtm-program m)
   (gem-statep gstate)
   (rtm-statep rstate)
   (m-correspondent-values-p m (mem gstate) (mem rstate)))
  (and
   (>= 0 (pcc (restart-program gstate)))
   (good-mapping-wrt-memories
    m
    (mem (restart-program gstate))
    (mem (restart-program rstate)))
    (good-translation-gem-rtm
    (restart-program gstate)
    (restart-program rstate)
    m)
   (gem-statep (restart-program gstate))
   (rtm-statep (restart-program rstate))
   (m-correspondent-values-p
    m
    (mem (restart-program gstate))
    (mem (restart-program rstate)))))
 :hints (("Goal" :in-theory nil
          :use (
                (:instance hh1 (s gstate))
                (:instance hh2 (s rstate))
                hh3
                hh6))))


(defthm execution-after-input-gem-does-not-touch-code
 (equal
  (code (execute-n-instructions (input-gem vars vals m gstate) n))
  (code gstate))
 :hints (("Goal"
          :in-theory (disable execute-n-instructions)
          :use (:instance execute-n-instruction-does-not-touch-code
                          (st (input-gem vars vals m gstate))))))


(defthm execution-after-input-rtm-does-not-touch-code
 (equal
  (code (execute-n-instructions (input-rtm varsseqs valsseqs rstate) n))
  (code rstate))
 :hints (("Goal"
          :in-theory (disable execute-n-instructions)
          :use (:instance execute-n-instruction-does-not-touch-code
                          (st (input-rtm varsseqs valsseqs rstate))))))






(defthm m-correspondence-and-other-conditions-kept-execution-on-n-clean
  (implies
   (and
    (integerp n)
    (>= n 0)
    (good-mapping m)
    (good-mapping-wrt-memories m (mem gstate) (mem rstate))
    (good-translation-gem-rtm gstate rstate m)
    (gem-statep gstate)
    (rtm-statep rstate)
    (>= (pcc gstate) 0)
    (m-correspondent-values-p m (mem gstate) (mem rstate)))
   (and
    (good-mapping-wrt-memories m
                               (mem (execute-n-instructions gstate n))
                               (mem  (execute-n-instructions rstate (correspondent-steps n gstate))))
    (>= (pcc (execute-n-instructions gstate n)) 0)
    (good-translation-gem-rtm
     (execute-n-instructions gstate n)
     (execute-n-instructions rstate (correspondent-steps n gstate)) m)
    (rtm-statep (execute-n-instructions rstate (correspondent-steps n gstate)))
    (gem-statep (execute-n-instructions gstate n))
    (m-correspondent-values-p
     m
     (mem (execute-n-instructions gstate n))
     (mem (execute-n-instructions rstate (correspondent-steps n gstate))))))
  :hints (("Goal" :in-theory '((:definition good-mapping) (:definition good-mapping-wrt-memories))
           :use m-correspondence-and-other-conditions-kept-execution-on-n)))



(defthm trivialities-on-restart
 (and
  (>= (pcc (restart-program st)) 0)
  (equal (code (restart-program st)) (code st))))


(defthm equalities-on-io-clean
 (implies
  (and
   (good-mapping m)
   (good-mapping-wrt-memories m gem-typed-mem rtm-typed-mem)
   (is-typed-amem-p gem-typed-mem)
   (bounded-amem-p gem-typed-mem))
  (equal-memories (decode m (projectio rtm-typed-mem attr)) (projectio gem-typed-mem attr)))
  :hints (("Goal" :use (equalities-on-io fact-bout-rns))))

(defthm sil00
 (implies (gem-statep gstate)
          (and
           (is-typed-amem-p (mem gstate))
           (bounded-amem-p (mem gstate))))
 :rule-classes nil)

(defthm coherent-output-and-properties-hold
 (implies
  (and
   (integerp n)
   (>= n 0)

   (equal (code gstate) (code (initial-state gem-program)))
   (equal (code rstate) (code (initial-state rtm-program)))
   (correct-translation gem-program rtm-program m)

   (correct-input vars vals varsseqs valsseqs m gstate rstate)
   (good-mapping m)
   (good-mapping-wrt-memories m (mem gstate) (mem rstate))
   (good-translation-gem-rtm gstate rstate m)
   (gem-statep gstate)
   (rtm-statep rstate)
   (>= (pcc gstate) 0)   )
  (and
   (equal-memories (decode m (projectio (mem rstate) attr)) (projectio (mem gstate) attr))
   (equal (code (restart-program (execute-n-instructions (input-gem vars vals m gstate) n)))
          (code (initial-state gem-program)))
   (equal (code (restart-program
                 (execute-n-instructions
                  (input-rtm varsseqs valsseqs rstate)
                  (correspondent-steps n (input-gem vars vals m gstate)))))
          (code (initial-state rtm-program)))
   (good-mapping-wrt-memories
    m
    (mem (restart-program (execute-n-instructions (input-gem vars vals m gstate) n)))
    (mem (restart-program
          (execute-n-instructions
           (input-rtm varsseqs valsseqs rstate)
           (correspondent-steps n (input-gem vars vals m gstate))))))
   (good-translation-gem-rtm
    (restart-program (execute-n-instructions (input-gem vars vals m gstate) n))
    (restart-program
     (execute-n-instructions
      (input-rtm varsseqs valsseqs rstate)
      (correspondent-steps n (input-gem vars vals m gstate))))
    m)
   (gem-statep (restart-program (execute-n-instructions (input-gem vars vals m gstate) n)))
   (rtm-statep
    (restart-program
     (execute-n-instructions
                (input-rtm varsseqs valsseqs rstate)
                (correspondent-steps n (input-gem vars vals m gstate)))))
   (>= (pcc (restart-program (execute-n-instructions (input-gem vars vals m gstate) n))) 0)
   (m-correspondent-values-p
    m
    (mem (restart-program (execute-n-instructions (input-gem vars vals m gstate) n)))
    (mem (restart-program
          (execute-n-instructions
           (input-rtm varsseqs valsseqs rstate)
           (correspondent-steps n (input-gem vars vals m gstate))))))))
 :hints (("Goal" :in-theory '((:definition good-mapping-wrt-memories))
          :use ( (:instance equalities-on-io-clean
                            (gem-typed-mem (mem gstate))
                            (rtm-typed-mem (mem rstate)))
                 sil00
                 all-properties-hold-after-correct-input1
                 (:instance trivialities-on-restart (st (execute-n-instructions (input-gem vars vals m gstate) n)))
                 (:instance trivialities-on-restart
                            (st (execute-n-instructions
                                 (input-rtm varsseqs valsseqs rstate)
                                 (correspondent-steps n (input-gem vars vals m gstate)))))
                 (:instance m-correspondence-and-other-conditions-kept-execution-on-n-clean
                            (gstate (input-gem vars vals m gstate))
                            (rstate (input-rtm varsseqs valsseqs rstate)))
                 (:instance all-properties-hold-after-restarting-program
                            (gstate (execute-n-instructions (input-gem vars vals m gstate) n))
                            (rstate (execute-n-instructions
                                     (input-rtm varsseqs valsseqs rstate)
                                     (correspondent-steps n (input-gem vars vals m gstate)))))
                 execution-after-input-gem-does-not-touch-code
                 (:instance execution-after-input-rtm-does-not-touch-code
                            (n (correspondent-steps n (input-gem vars vals m gstate))))))))




(defun equal-output-sequences (rmems gmems)
 (if (or
      (endp rmems)
      (endp gmems))
     t
     (and
      (equal-memories (car rmems) (car gmems))
      (equal-output-sequences (cdr rmems) (cdr gmems)))))


(defun valid-input-sequences (gemseq-seq gemval-seq rtmseq-seq rtmval-seq m gstate rstate n)
 (if (or
      (endp gemseq-seq)
      (endp rtmseq-seq))
     t
     (and
      (correct-input
       (car gemseq-seq)
       (car gemval-seq)
       (car rtmseq-seq)
       (car rtmval-seq)
       m gstate rstate)
      (valid-input-sequences
       (cdr gemseq-seq)
       (cdr gemval-seq)
       (cdr rtmseq-seq)
       (cdr rtmval-seq)
       m
       (restart-program (execute-n-instructions (input-gem (car gemseq-seq) (car gemval-seq) m gstate) n))
       (restart-program (execute-n-instructions
                         (input-rtm (car rtmseq-seq) (car rtmval-seq) rstate)
                         (correspondent-steps n (input-gem (car gemseq-seq) (car gemval-seq) m gstate))))
       n))))


(defun build-gem-output (gemseq-seq gemval-seq m gstate n attr)
 (if (endp gemseq-seq)
     nil
     (cons (projectio (mem gstate) attr)
           (build-gem-output
            (cdr gemseq-seq)
            (cdr gemval-seq)
            m
            (restart-program (execute-n-instructions (input-gem (car gemseq-seq) (car gemval-seq) m gstate) n))
            n
            attr))))

(defun build-rtm-output (rtmseq-seq rtmval-seq m gstate rstate n attr gemseq-seq gemval-seq)
 (if
  (endp rtmseq-seq)
  nil
  (cons (decode m (projectio (mem rstate) attr))
        (build-rtm-output
         (cdr rtmseq-seq)
         (cdr rtmval-seq)
         m
         (restart-program (execute-n-instructions (input-gem (car gemseq-seq) (car gemval-seq) m gstate) n))
         (restart-program
          (execute-n-instructions
           (input-rtm (car rtmseq-seq) (car rtmval-seq) rstate)
           (correspondent-steps n (input-gem (car gemseq-seq) (car gemval-seq) m gstate))))
         n
         attr
         (cdr gemseq-seq)
         (cdr gemval-seq)))))

(defthm many-cycle-semantic-eqv0
 (implies
  (and
   (integerp n)
   (>= n 0)
   (equal (code gstate) (code (initial-state gem-program)))
   (equal (code rstate) (code (initial-state rtm-program)))
   (correct-translation gem-program rtm-program m)
   (good-mapping m)
   (good-mapping-wrt-memories m (mem gstate) (mem rstate))
   (good-translation-gem-rtm gstate rstate m)
   (gem-statep gstate)
   (rtm-statep rstate)
   (>= (pcc gstate) 0)
   (valid-input-sequences gemseq-seq gemval-seq rtmseq-seq rtmval-seq m gstate rstate n))
  (equal-output-sequences
   (build-rtm-output rtmseq-seq rtmval-seq m gstate rstate n attr gemseq-seq gemval-seq)
   (build-gem-output gemseq-seq gemval-seq m gstate n attr)))
 :hints (("Goal" :induct (valid-input-sequences gemseq-seq gemval-seq rtmseq-seq rtmval-seq m gstate rstate n))
         ("Subgoal *1/3" :in-theory '((:definition valid-input-sequences)))
         ("Subgoal *1/2"
          :in-theory
          (union-theories (current-theory 'ground-zero)
                          '((:definition valid-input-sequences)
                            (:definition equal-output-sequences)
                            (:definition build-gem-output)
                            (:definition build-rtm-output)))
          :use (:instance coherent-output-and-properties-hold
                                (vars (car gemseq-seq))
                                (vals (car gemval-seq))
                                (varsseqs (car rtmseq-seq))
                                (valsseqs (car rtmval-seq))))
         ("Subgoal *1/1" :in-theory (union-theories (current-theory 'ground-zero)
                                                    '((:definition build-rtm-output)
                                                      (:definition equal-output-sequences)
                                                      (:definition build-gem-output))))))
























(defthm semantic-eqv
  (let*
      ((gstate (initial-state gem-program))
       (rstate (initial-state rtm-program))
       (n (len (code gstate))))
 (implies

  (and
   (gem-program-p gem-program)
   (rtm-program-p rtm-program)
   (correct-translation gem-program rtm-program m)
   (good-mapping m)
   (good-mapping-wrt-memories m (mem gstate) (mem rstate))
   (valid-input-sequences
    gemseq-seq gemval-seq rtmseq-seq rtmval-seq m gstate rstate n))
  (equal-output-sequences
   (build-rtm-output
    rtmseq-seq rtmval-seq m gstate rstate n attr gemseq-seq gemval-seq)
   (build-gem-output
    gemseq-seq gemval-seq m gstate n attr))))
 :hints (("Goal"
          :in-theory (current-theory 'ground-zero)
          :use
           ((:instance correct-translation
                       (gemprog gem-program)
                       (rtmprog rtm-program))
            (:instance many-cycle-semantic-eqv0
                       (n (len (code (initial-state gem-program))))
                       ;(n (len (code gstate)))
                       (gstate (initial-state gem-program))
                       (rstate (initial-state rtm-program)))
            (:instance simple-fact-about-initial-gemstate (gemprog gem-program))
            (:instance simple-fact-about-initial-rtmstate (rtmprog rtm-program))))))
;
;(defun is-variable-mapping (m gm rm)
; (and
;  (good-mapping m)
;  (good-mapping-wrt-memories m gm rm)))

(defun correct-input-sequences (gemseq-seq rtmseq-seq m gem-program rtm-program)
 (valid-input-sequences (car gemseq-seq)
                        (cdr gemseq-seq)
                        (car rtmseq-seq)
                        (cdr rtmseq-seq)
                        m
                        (initial-state gem-program)
                        (initial-state rtm-program)
                        (len (code (initial-state gem-program)))))



(defun declarations (prog)
 (car prog))

(defun instructs (prog)
 (cdr prog))

(defthm mem-and-code-of-initial-state
 (and
  (equal (mem  (initial-state prog)) (declarations prog))
  (equal (code (initial-state prog)) (instructs    prog))))

(defun gem-output-sequence (gemseq-seq m gem-program)
 (build-gem-output (car gemseq-seq) (cdr gemseq-seq) m
                   (initial-state gem-program)
                   (len (code (initial-state gem-program)))
                   'Output))

(defthm correspondent-steps-independent-from-mem
 (implies
  (and (equal (pcc st1) (pcc st2))
       (equal (code st1) (code st2)))
  (equal (correspondent-steps n st1) (correspondent-steps n st2))))

(defthm correspondent-steps-no-matter-input
 (equal
  (correspondent-steps n (input-gem gemvars gemvals m gstate))
  (correspondent-steps n gstate))
 :hints (("Goal" :use (:instance correspondent-steps-independent-from-mem
                                 (st1 (input-gem gemvars gemvals m gstate))
                                 (st2 gstate)))))


(defun build-rtm-output-clean (rtmseq-seq rtmval-seq m gstate rstate n attr)
 (if
  (endp rtmseq-seq)
  nil
  (cons (decode m (projectio (mem rstate) attr))
        (build-rtm-output-clean
         (cdr rtmseq-seq)
         (cdr rtmval-seq)
         m
         gstate
         (restart-program
          (execute-n-instructions
           (input-rtm (car rtmseq-seq) (car rtmval-seq) rstate)
           (correspondent-steps n gstate)))
         n
         attr))))

(defthm after-restarting-same-code
 (equal
  (code (restart-program (execute-n-instructions (input-gem gemvars gemvals m gstate) n)))
  (code gstate))
 :hints (("Goal"
          :in-theory '((:definition input-gem)
                       (:rewrite skkk2))
          :use ( (:instance execute-n-instruction-does-not-touch-code
                            (st (input-gem gemvars gemvals m gstate)))
                 (:instance trivialities-on-restart
                            (st (execute-n-instructions (input-gem gemvars gemvals m gstate) n)))))))


(defthm another-trivail-restart
 (equal (pcc (restart-program st)) 0))



(defun build-rtm-output-induct (rtmseq-seq rtmval-seq m gstate gstate2 rstate n attr gemseq-seq gemval-seq)
 (if
  (endp rtmseq-seq)
  nil
  (cons (append rtmseq-seq rtmval-seq m gstate gstate2 rstate n attr gemseq-seq gemval-seq)
        (build-rtm-output-induct
         (cdr rtmseq-seq)
         (cdr rtmval-seq)
         m
         (restart-program (execute-n-instructions (input-gem (car gemseq-seq) (car gemval-seq) m gstate) n))
         (restart-program (execute-n-instructions (input-gem (car gemseq-seq) (car gemval-seq) m gstate2) n))
         (restart-program
          (execute-n-instructions
           (input-rtm (car rtmseq-seq) (car rtmval-seq) rstate)
           (correspondent-steps n (input-gem (car gemseq-seq) (car gemval-seq) m gstate))))
         n
         attr
         (cdr gemseq-seq)
         (cdr gemval-seq)))))



(defthm build-rtm-output-independent-from-gem-memory
 (implies
  (and (equal (pcc st1) (pcc st2))
       (equal (code st1) (code st2)))
  (equal
   (build-rtm-output       rtmseq-seq rtmval-seq m st1 rstate n attr gemseq-seq gemval-seq)
   (build-rtm-output       rtmseq-seq rtmval-seq m st2 rstate n attr gemseq-seq gemval-seq)))
 :hints
 (("Goal"
   :induct
   (build-rtm-output-induct rtmseq-seq rtmval-seq m st1 st2 rstate n attr gemseq-seq gemval-seq))
  ("Subgoal *1/2"
          :in-theory '((:definition build-rtm-output)
                       (:rewrite correspondent-steps-no-matter-input)
                       (:rewrite after-restarting-same-code)
                       (:rewrite another-trivail-restart))
          :use (correspondent-steps-independent-from-mem))))



(defun build-rtm-output-induct2
 (rtmseq-seq rtmval-seq m gstate gstate2 rstate n attr gemseq-seq gemval-seq gemseq-seq2 gemval-seq2)
 (if
  (endp rtmseq-seq)
  nil
  (cons (append rtmseq-seq rtmval-seq m gstate gstate2 rstate n attr gemseq-seq gemval-seq gemseq-seq2 gemval-seq2)
        (build-rtm-output-induct2
         (cdr rtmseq-seq)
         (cdr rtmval-seq)
         m
         (restart-program (execute-n-instructions (input-gem (car gemseq-seq) (car gemval-seq) m gstate) n))
         (restart-program (execute-n-instructions (input-gem (car gemseq-seq2) (car gemval-seq2) m gstate2) n))
         (restart-program
          (execute-n-instructions
           (input-rtm (car rtmseq-seq) (car rtmval-seq) rstate)
           (correspondent-steps n (input-gem (car gemseq-seq) (car gemval-seq) m gstate))))
         n
         attr
         (cdr gemseq-seq)
         (cdr gemval-seq)
         (cdr gemseq-seq2)
         (cdr gemval-seq2)))))



(defthm build-rtm-output-independent-from-gem-input
  (equal
   (build-rtm-output rtmseq-seq rtmval-seq m gstate rstate n attr gemseq-seq gemval-seq)
   (build-rtm-output rtmseq-seq rtmval-seq m gstate rstate n attr gemseq-seq2 gemval-seq2))
 :hints (("Goal"
          :induct (build-rtm-output-induct2 rtmseq-seq rtmval-seq m gstate gstate rstate n attr
                                            gemseq-seq gemval-seq gemseq-seq2 gemval-seq2))
         ("Subgoal *1/2"
                         :in-theory '((:definition build-rtm-output)
                                      (:rewrite correspondent-steps-no-matter-input)
                                      (:rewrite another-trivail-restart)
                                      ;(:rewrite build-rtm-output-independent-from-gem-memory)
                                      (:rewrite after-restarting-same-code))
                         :use (:instance build-rtm-output-independent-from-gem-memory
                                         (rtmseq-seq (cdr rtmseq-seq))
                                         (rtmval-seq (cdr rtmval-seq))
                                         (st1 (RESTART-PROGRAM
                                               (EXECUTE-N-INSTRUCTIONS (INPUT-GEM (CAR GEMSEQ-SEQ)
                                                        (CAR GEMVAL-SEQ)
                                                        M GSTATE) N)))
                                         (st2 (RESTART-PROGRAM
                                               (EXECUTE-N-INSTRUCTIONS (INPUT-GEM (CAR GEMSEQ-SEQ2)
                                                        (CAR GEMVAL-SEQ2)
                                                        M GSTATE) N)))
                                         (rstate
                                          (RESTART-PROGRAM
                                           (EXECUTE-N-INSTRUCTIONS (INPUT-RTM (CAR RTMSEQ-SEQ)
                                                                              (CAR RTMVAL-SEQ)
                                                                              RSTATE)
                                                                   (CORRESPONDENT-STEPS N
                                                                                        (INPUT-GEM (CAR GEMSEQ-SEQ)
                                                                                                   (CAR GEMVAL-SEQ)
                                                                                                   M GSTATE)))))
                                         (gemseq-seq (cdr gemseq-seq2))
                                         (gemval-seq (cdr gemval-seq2))))))




(defun rtm-output-sequence (rtmseq-seq m gem-program rtm-program)
 (build-rtm-output (car rtmseq-seq)
                   (cdr rtmseq-seq)
                   m
                   (initial-state gem-program)
                   (initial-state rtm-program)
                   (len (code (initial-state gem-program)))
                   'Output
                   nil
                   nil))




(defthm semantic-eqv2
 (implies
  (and
   (gem-program-p gem-program)
   (rtm-program-p rtm-program)
   (correct-translation gem-program rtm-program m)
   (is-variable-mapping
    m
    (declarations gem-program)
    (declarations rtm-program))
   (correct-input-sequences
    gemseq-seq rtmseq-seq m gem-program rtm-program))
  (equal-output-sequences
   (rtm-output-sequence rtmseq-seq m gem-program rtm-program)
   (gem-output-sequence gemseq-seq m gem-program)))

 :hints (("Goal"
          :in-theory (union-theories (current-theory 'ground-zero)
                                     '((:rewrite mem-and-code-of-initial-state)
                                       (:definition rtm-output-sequence)
                                       (:definition gem-output-sequence)
                                       (:definition correct-input-sequences)
                                       (:definition gem-variables)
                                       (:definition rtm-variables)
                                       (:definition same-vars)
                                       (:definition good-mapping)
                                       (:definition good-mapping-wrt-memories)
                                       (:definition is-variable-mapping)))
          :use ((:instance build-rtm-output-independent-from-gem-input
                           (rtmseq-seq (car rtmseq-seq))
                           (rtmval-seq (cdr rtmseq-seq))
                           (gstate (initial-state gem-program))
                           (rstate (initial-state rtm-program))
                           (n (LEN (CODE (INITIAL-STATE GEM-PROGRAM))))
                           (attr 'Output)
                           (gemseq-seq (car gemseq-seq))
                           (gemval-seq (cdr gemseq-seq))
                           (gemseq-seq2 nil)
                           (gemval-seq2 nil))
                (:instance redefinition-of-m-corr
                           (rtm-vars (declarations rtm-program))
                           (gem-vars (declarations gem-program)))
                (:instance semantic-eqv (attr 'Output)
                                       (gemseq-seq (car gemseq-seq))
                                       (gemval-seq (cdr gemseq-seq))
                                       (rtmseq-seq (car rtmseq-seq))
                                       (rtmval-seq (cdr rtmseq-seq)))))))







(defun semantically-equivalent
       (gem-program rtm-program m gemseq-seq rtmseq-seq)
 (implies
  (correct-input-sequences
   gemseq-seq rtmseq-seq m gem-program rtm-program)
  (equal-output-sequences
   (rtm-output-sequence rtmseq-seq m gem-program rtm-program)
   (gem-output-sequence gemseq-seq m gem-program))))

(defun syntactically-equivalent (gem-program rtm-program m)
  (and
   (gem-program-p gem-program)
   (rtm-program-p rtm-program)
   (is-variable-mapping
    m
    (declarations gem-program)
    (declarations rtm-program))
   (correct-translation gem-program rtm-program m)))



(defthm syntactic-eqv-implies-m-eqv
  (let
   ((gstate (initial-state gem-program))
    (rstate (initial-state rtm-program)))
  (implies
   (and
    (natp n)
    (syntactically-equivalent gem-program rtm-program m))
   (is-variable-mapping
    m
    (mem (execute-n-instructions gstate n))
    (mem (execute-n-instructions rstate (correspondent-steps n gstate))))))
  :hints (("Goal" :use
           ( (:instance simple-fact-about-initial-rtmstate (rtmprog rtm-program))
             (:instance simple-fact-about-initial-gemstate (gemprog gem-program))
             (:instance redefinition-of-m-corr
                        (rtm-vars (declarations rtm-program))
                        (gem-vars (declarations gem-program)))
             (:instance redefinition-of-m-corr
                        (rtm-vars (mem (execute-n-instructions
                                        (initial-state rtm-program)
                                        (correspondent-steps n (initial-state gem-program)))))
                        (gem-vars (mem (execute-n-instructions (initial-state gem-program) n))))
             (:instance m-correspondence-and-other-conditions-kept-execution-on-n
                        (gstate (initial-state gem-program))
                        (rstate (initial-state rtm-program))))
           :in-theory
           '( (:definition natp)
              (:definition syntactically-equivalent)
              (:definition same-vars)
              (:definition correct-translation)
              (:definition gem-variables)
              (:definition rtm-variables)
              (:definition is-variable-mapping)
              (:rewrite mem-and-code-of-initial-state)))))



(in-theory (union-theories  (current-theory 'ground-zero)
                            '((:definition semantically-equivalent)
                              (:definition syntactically-equivalent)
                              (:rewrite semantic-eqv2))))

(defthm syntactic-eqv-implies-semantic-eqv
 (implies
   (syntactically-equivalent gem-program rtm-program m)
   (semantically-equivalent
    gem-program rtm-program m gemseq-seq rtmseq-seq)))



