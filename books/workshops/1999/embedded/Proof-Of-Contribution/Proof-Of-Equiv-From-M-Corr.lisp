;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; Section 4: Definition of m-correspondence
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;;
;;; Definition of mapping-induced correspondence:
;;;
;;; In order for a Gem memory and and Rtm memory to be m-correspondent via m,
;;; the following conditions must hold:
;;;
;;; - Correctness w.r.t. the types of the variables appearing into the memories:
;;;   I.e., m must map boolean Gem variables into single Rtm variables, and integer Gem
;;;   variables into tuples of |*rns*| Rtm variables;
;;;
;;; - Correctness w.r.t. the values and attributes of the variables appearing into the memories:
;;;   for each entry of the mapping,
;;;   the values obtained by direct application of rns to the gem variable of the entry must
;;;   match those of the rtm variables, and
;;;   the attributes of the rtm variables must match that of the rtm variable.
;;;
;;; - A mapping must have every Gem variable within the range of the Gem memory it references
;;;
;;; - A mapping must contain every variable of the Gem memory it references
;;;
;;;
;;; Similar properties to the least two will be needed for the Rtm memories (e.g., every Rtm
;;; variable should be in the range of the Rtm memory), when proving properties about
;;; programs. We will insert them then.
;;;



(in-package "ACL2")

(include-book "CRTcorollaries")

(in-theory (current-theory 'ground-zero))

(include-book "Mapping")


;;;
;;; Subsection 4.1:
;;;
;;; Memories must be correspondent via m in terms of types
;;;



(defun correct-wrt-arity (m gem-typed-mem)
  (if (endp m)
      (null m)
    (and
     (correct-type (type-0 m))
     (equal
      (type-0 m)
      (var-type (get-cell (gemvar-0 m) gem-typed-mem)))
     (correct-wrt-arity (cdr m) gem-typed-mem))))

(defthm correct-arity-all-i-need
 (implies
  (and
   (not (endp m))
   (correct-wrt-arity m gem-typed-mem))
  (and
   (correct-type (type-0 m))
   (equal
    (type-0 m)
    (var-type (get-cell (gemvar-0 m) gem-typed-mem)))
   (not (null (var-attributes (rtmintvars-0 m) rtm-typed-mem)))
   (correct-wrt-arity (cdr m) gem-typed-mem))))



;;
;; Section 4.5:
;;
;; Every entry of the mapping must point to a coherent set of rtm variables, i.e. to a set of of rtm
;; variables which share the same attribute.
;;

(defun get-common-value (l)
  (if (equal-elements (car l) (cdr l))
      (car l)
    'error-value))

(defthm if-every-element-matches-val-then-get-common-value-amounts-to-val
 (implies
  (and
   (true-listp l)
   (not (null l))
   (equal-elements v l))
  (equal (get-common-value l) v)))

(in-theory (disable if-every-element-matches-val-then-get-common-value-amounts-to-val))


(defun m-entries-point-to-good-rtm-var-sets (m rtm-typed-mem)
  (if (endp m)
      (null m)
    (and
     (not (endp (rtmintvars-0 m)))
     (true-listp (rtmintvars-0 m))
     (not (equal 'error-value (get-common-value (var-attributes (rtmintvars-0 m) rtm-typed-mem))))
     (m-entries-point-to-good-rtm-var-sets (cdr m) rtm-typed-mem))))

(in-theory (disable m-entries-point-to-good-rtm-var-sets))



;;;
;;; Subsection 4.6:
;;;
;;; Values and attributes must be correspondent via the mapping.
;;;
;;; In order to allow this definition, we first provide
;;; definitions of transformations of gem values into tuples of rtm values (by *rns*) and
;;; viceversa (by inverse application of *rns*).
;;;
;;; Notice that these transformations are actually just ``stubs'', since we provide a
;;; simplified form of axiomatization of the chinese remainder inversion theorem.
;;; Additional hypothesis (e.g., boundedness of Gem and Rtm integers, and relations between such
;;; bounds) shall (and will) be added and taken into account when proving properties of programs.
;;; In the cureent state of the proof, however, we can limit ourselves to consider 'generic'
;;; transformations of Gem vars into tuples of Rtm vars, and their corresponding generic inverse.
;;;
;;; However, since memories could contain nil cells, we have to lift our transformations, and
;;; the 'simplified axiomatization of CRT', to deal with nils.
;;;
;;; We extend transformations so that nils transform into sequences of nils and viceversa.
;;; We lift the simplified CRT axiomatization to such extended version.
;;;
;;;




(defun make-null-list (l)
 (if (endp l)
     nil
     (cons nil (make-null-list (cdr l)))))

(defthm make-null-list-is-invariant-on-value-slicing (equal (make-null-list rtmvars) (make-null-list (var-values rtmvars rm))))

(in-theory (disable make-null-list-is-invariant-on-value-slicing))

(defun equal-values (val-list-1 val-list-2)
 (equal val-list-1 val-list-2))

(defun build-values-by-rns (gem-value rns)
 (if (endp rns)
     nil
     (cons (mod gem-value (car rns))
           (build-values-by-rns gem-value (cdr rns)))))

(in-theory (enable build-values-by-rns))

(defun mod-extended-for-nil (val1 val2)
 (if (null val1)
     nil
     (mod val1 val2)))

(defun build-values-by-rns-extended-for-nil (gem-value rns)
 (if (endp rns)
     nil
     (cons (mod-extended-for-nil gem-value (car rns))
           (build-values-by-rns-extended-for-nil gem-value (cdr rns)))))

(defthm build-values-by-rns-extended-behaves-standardly-on-non-nils
 (implies
  (not (null gem-value))
  (equal
    (build-values-by-rns-extended-for-nil gem-value rns)
    (build-values-by-rns gem-value rns))))

(defthm build-values-by-rns-extended-for-nils-provides-integers-from-integer
 (implies
  (and
   (integerp val)
   (not (null rns))
   (integer-listp rns))
  (and
   (not (null (build-values-by-rns-extended-for-nil val rns)))
   (integer-listp (build-values-by-rns-extended-for-nil val rns)))))




(defun build-value-by-inverse-rns (rtm-values rns)
 (crtmod rtm-values rns))


(defun build-value-by-inverse-rns-extended-for-nil (rtm-values rns)
 (if
     (integer-listp rtm-values)
     (crtmod rtm-values rns)
   nil))


(defthm build-value-by-inverse-rns-extended-for-nils-behaves-standardly-on-integer-lists
 (implies
  (integer-listp rtm-values)
  (equal
    (build-value-by-inverse-rns-extended-for-nil rtm-values rns)
    (build-value-by-inverse-rns rtm-values rns))))




(defthm crt-inversion-inst
 (implies
  (and
   (rel-prime-moduli rns)
   (natp gem-value)
   (< gem-value (prod rns)))
 (equal
  (build-value-by-inverse-rns (build-values-by-rns gem-value rns) rns)
  gem-value))
 :hints (("Goal" :in-theory (enable crt-inversion))))


(in-theory (enable natp))


(defthm crt-inversion-extended-to-nils-in-integer-case
 (implies
  (and
   (rel-prime-moduli rns)
   (< gem-value (prod rns))
   (not (null rns))
   (integer-listp rns)
   (natp gem-value))
 (equal
  (build-value-by-inverse-rns-extended-for-nil (build-values-by-rns-extended-for-nil gem-value rns) rns)
  gem-value))
 :hints (("goal"
          :use (
                crt-inversion-inst
                build-values-by-rns-extended-behaves-standardly-on-non-nils
                (:instance build-value-by-inverse-rns-extended-for-nils-behaves-standardly-on-integer-lists
			   (rtm-values (build-values-by-rns gem-value rns)))
                (:instance build-values-by-rns-extended-for-nils-provides-integers-from-integer
			   (val gem-value))))))

(defthm crt-inversion-extended-to-nils-in-nil-case
 (implies
  (and
   (rel-prime-moduli rns)
   (not (null rns))
   (integer-listp rns)
   (null gem-value))
 (equal
  (build-value-by-inverse-rns-extended-for-nil (build-values-by-rns-extended-for-nil gem-value rns) rns)
  gem-value)))

(defthm crt-inversion-extended-to-nils
 (implies
  (and
   (rel-prime-moduli rns)
   (integer-listp rns)
   (not (null rns))
  (or
   (null gem-value)
   (and
    (natp gem-value)
    (< gem-value (prod rns)))))
 (equal
  (build-value-by-inverse-rns-extended-for-nil (build-values-by-rns-extended-for-nil gem-value rns) rns)
  gem-value))
 :hints (("goal"
          :cases (
                  (and (not (null gem-value)) (not (and (natp gem-value) (< gem-value (prod rns)))))
                  (null gem-value)
                  (and (natp gem-value) (< gem-value (prod rns)))))
	 ("Subgoal 2" :use crt-inversion-extended-to-nils-in-nil-case)
         ("subgoal 1" :use (:instance crt-inversion-extended-to-nils-in-integer-case))))


(in-theory (disable build-values-by-rns-extended-for-nil
                    build-values-by-rns
                    build-value-by-inverse-rns-extended-for-nil
                    build-value-by-inverse-rns
                    build-values-by-rns-extended-behaves-standardly-on-non-nils
                    build-values-by-rns-extended-for-nils-provides-integers-from-integer
                    build-value-by-inverse-rns-extended-for-nils-behaves-standardly-on-integer-lists
                    crt-inversion-extended-to-nils-in-integer-case
		    crt-inversion-extended-to-nils-in-nil-case))







;;
;; m-correspondence definition w.r.t. values and attributes of memories
;;




(defun apply-direct-rns-to-value-according-to-type (gem-cell type)
 (cond
  ( (equal type 'bool)
    (list (var-value gem-cell)))
  ( (equal type 'int)
    (build-values-by-rns-extended-for-nil (var-value gem-cell) *rns*))
  ( t nil)))



(defun apply-invers-rns-to-values-according-to-type (vals type)
 (cond
  ( (equal type 'bool)
    (car vals) )
  ( (equal type 'int)
    (build-value-by-inverse-rns-extended-for-nil vals *rns*))
  ( t nil )))




(defun invert-cell (rtmvars rtm-typed-mem type)
  (if
     (equal-values
       (var-values     rtmvars rtm-typed-mem)
       (make-null-list rtmvars))
      (apply-invers-rns-to-values-according-to-type
       (var-values rtmvars rtm-typed-mem)
       type)
    (make-cell
     (apply-invers-rns-to-values-according-to-type
      (var-values rtmvars rtm-typed-mem)
      type)
     (get-common-value (var-attributes rtmvars rtm-typed-mem))
     type)))

(defun equal-values-and-attributes (gem-cell rtmvars rtm-typed-mem type)
(and
 (equal-values
  (var-values rtmvars rtm-typed-mem)
  (apply-direct-rns-to-value-according-to-type gem-cell type))
 (equal-elements
  (var-attribute gem-cell)
  (var-attributes rtmvars rtm-typed-mem))))



(defthm apply-direct-rns-unfolding-for-integer-case
 (implies
  (equal type 'int)
  (equal
   (apply-direct-rns-to-value-according-to-type gem-cell type)
   (build-values-by-rns-extended-for-nil (var-value gem-cell) *rns*))))

(defthm apply-direct-rns-unfolding-for-boolean-case
 (implies
  (equal type 'bool)
  (equal
   (apply-direct-rns-to-value-according-to-type gem-cell type)
   (list (var-value gem-cell)))))



(defthm apply-inverse-rns-unfolding-for-integer-case
 (implies
  (equal type 'int)
  (equal (apply-invers-rns-to-values-according-to-type values type)
	 (build-value-by-inverse-rns-extended-for-nil values *rns*))))


(defthm apply-inverse-direct-retrieves-same-value-for-typed-cells
 (implies
  (and
  (rel-prime-moduli *rns*)
  (integer-listp *rns*)
  (not (null *rns*))
   (or
    (equal type 'int)
    (equal type 'bool))
   (or
    (and
     (natp (var-value gem-cell))
     (< (var-value gem-cell) (prod *rns*)))
    (null (var-value gem-cell))))
  (equal
   (apply-invers-rns-to-values-according-to-type
    (apply-direct-rns-to-value-according-to-type gem-cell type) type)
   (var-value gem-cell)))
 :hints (("goal" :cases ( (equal type 'bool)
                          (equal type 'int)))
         ("subgoal 1"
          :in-theory (disable null
                              apply-inverse-rns-unfolding-for-integer-case
                              crt-inversion-extended-to-nils
                              apply-direct-rns-unfolding-for-integer-case
                              apply-direct-rns-to-value-according-to-type
                              var-value
                              apply-invers-rns-to-values-according-to-type
                              build-value-by-inverse-rns-extended-for-nil
                              build-values-by-rns-extended-for-nil)
          :use ((:instance apply-direct-rns-unfolding-for-integer-case)
                (:instance apply-inverse-rns-unfolding-for-integer-case (values (build-values-by-rns-extended-for-nil (var-value gem-cell) *rns*)))
                (:instance crt-inversion-extended-to-nils (rns *rns*) (gem-value (var-value gem-cell)))))))




(defthm inversion-for-empty-cell
 (implies
  (and
   (null cell)
   (equal-values (var-values rtmvars rm) (apply-direct-rns-to-value-according-to-type cell type))
   (correct-type type))
  (and
   (equal-values (var-values rtmvars rm) (make-null-list rtmvars))
   (equal (apply-invers-rns-to-values-according-to-type (var-values rtmvars rm) type) cell)))
 :hints (("goal"
	  :in-theory (enable make-null-list-is-invariant-on-value-slicing)
	  :cases ( (equal type 'bool) (equal type 'int)))))


(in-theory (disable  make-cell))


(defthm ad-hoc-2-for-inversion-of-one-nonempty-cell-by-decode
  (implies
   (and (not (null bui)) (integer-listp bui))
   (not (equal (make-null-list l) bui))))


(defthm ad-hoc-3-for-inversion-of-one-nonempty-cell-by-decode
  (implies
   (integerp (var-value cell))
   (not (equal (make-null-list l) (build-values-by-rns-extended-for-nil (var-value cell) *rns*))))
  :hints (("goal" :use ((:instance build-values-by-rns-extended-for-nils-provides-integers-from-integer
				   (val (var-value cell)) (rns *rns*))
			(:instance ad-hoc-2-for-inversion-of-one-nonempty-cell-by-decode
				   (l l)
				   (bui (build-values-by-rns-extended-for-nil (var-value cell) *rns*)))))))

(defthm nonempty-cell-is-not-mapped-into-nils-by-rns
  (implies
   (and
    (true-listp (var-attributes rtmvars rm))
    (not (null (var-attributes rtmvars rm)))
    (is-mem-cell-p cell)
    (not (null cell))
    (equal-values (var-values rtmvars rm) (apply-direct-rns-to-value-according-to-type cell type))
    (equal-elements (var-attribute cell) (var-attributes rtmvars rm))
    (equal type (var-type cell)))
    (not (equal-values (var-values rtmvars rm) (make-null-list rtmvars))))
 :hints (("goal" :cases ( (equal type 'bool) (equal type 'int)))))



(in-theory (disable my-or-2 my-or-3))

(defthm silly00
  (IMPLIES (AND (TRUE-LISTP CELL6)
		(EQUAL (+ 3 (LEN CELL6)) 3))
	   (NOT CELL6))
  :rule-classes nil)

(defthm reconstruction-of-cell
 (implies
  (is-mem-cell-p cell)
  (equal
   (make-cell
    (var-value cell)
    (var-attribute cell)
    (var-type cell))
   cell))
  :hints (("Subgoal 1.1" :use silly00)
	  ("Subgoal 2.1" :use silly00)
	  ("goal"
	   :in-theory
	   (union-theories (current-theory 'ground-zero)
	   '((:definition is-mem-cell-p)
	     (:definition make-cell)
	     (:definition var-type)
	     (:definition var-value)
	     (:definition var-attribute)))))
  :rule-classes nil)



(defthm nonempty-rtm-vars-which-correspond-to-gem-var-by-values-and-atributes-map-back-to-gem-var
  (implies
   (and
    (rel-prime-moduli *rns*)
    (integer-listp *rns*)
    (not (null *rns*))
    (true-listp (var-attributes rtmvars rm))
    (not (null (var-attributes rtmvars rm)))
    (is-mem-cell-p cell)
    (not (null cell))
    (natp (var-value cell))
    (< (var-value cell) (prod *rns*))
    (equal-values (var-values rtmvars rm) (apply-direct-rns-to-value-according-to-type cell type))
    (equal-elements (var-attribute cell) (var-attributes rtmvars rm))
    (equal type (var-type cell)))
    (equal
     (make-cell
      (apply-invers-rns-to-values-according-to-type (var-values rtmvars rm) type)
      (get-common-value (var-attributes rtmvars rm))
      type)
     cell))
  :hints (("goal" :in-theory '((:definition my-or-2)
			       (:definition is-mem-cell-p)
			       (:definition natp)
			       (:definition equal-values)
			       (:definition is-mem-cell-p))
	          :use (reconstruction-of-cell
			(:instance if-every-element-matches-val-then-get-common-value-amounts-to-val
				  (l (var-attributes rtmvars rm)) (v (var-attribute cell)))
			(:instance apply-inverse-direct-retrieves-same-value-for-typed-cells
				   (type type) (gem-cell cell))))))










(defthm decode-inversion-for-nonempty-gem-cell
  (implies
   (and
    (rel-prime-moduli *rns*)
    (integer-listp *rns*)
    (not (null *rns*))
    (true-listp (var-attributes rtmvars rm))
    (not (null (var-attributes rtmvars rm)))
    (is-mem-cell-p cell)
    (not (null cell))
    (natp (var-value cell))
    (< (var-value cell) (prod *rns*))
    (equal-values (var-values rtmvars rm) (apply-direct-rns-to-value-according-to-type cell type))
    (equal-elements (var-attribute cell) (var-attributes rtmvars rm))
    (equal type (var-type cell)))
   (and
    (not (equal-values (var-values rtmvars rm) (make-null-list rtmvars)))
    (equal
     (make-cell
      (apply-invers-rns-to-values-according-to-type (var-values rtmvars rm) type)
      (get-common-value (var-attributes rtmvars rm))
      type)
     cell)))
  :hints (("goal" :use (nonempty-cell-is-not-mapped-into-nils-by-rns
			nonempty-rtm-vars-which-correspond-to-gem-var-by-values-and-atributes-map-back-to-gem-var))))






(defthm var-attributes-always-true-listp
 (true-listp (var-attributes rtmvars rtm-typed-mem)))

(defun bounded-value (cell)
  (if (null cell)
      t
    (and (natp (var-value cell)) (< (var-value cell) (prod *rns*)))))

(defthm invert-cell-inverts-for-m-correspondents
 (implies
  (and
   (rel-prime-moduli *rns*)
   (integer-listp *rns*)
   (not (null *rns*))
   (not (null (var-attributes rtmvars rtm-typed-mem)))
   (equal type (var-type gem-cell))
   (correct-type type)
   (or (null gem-cell) (is-mem-cell-p gem-cell))
   (bounded-value gem-cell)
   (equal-values-and-attributes gem-cell rtmvars rtm-typed-mem type))
  (equal
   (invert-cell rtmvars rtm-typed-mem type)
   gem-cell))
 :hints (("Goal"
	  :in-theory (disable equal-values)
	  :use ( var-attributes-always-true-listp
		 (:instance decode-inversion-for-nonempty-gem-cell
			    (cell gem-cell)
			    (rm rtm-typed-mem))
		 (:instance inversion-for-empty-cell
			    (cell gem-cell)
			    (rm rtm-typed-mem))))))


(defun is-typed-amem-p (mem)
  (if (endp mem)
      (null mem)
    (and
     (consp (car mem))
     (is-mem-cell-p (cdr (car mem)))
     (is-typed-amem-p (cdr mem)))))

(in-theory (enable get-cell))

(defthm any-cell-of-a-typed-mem-is-nil-or-a-typed-cell
 (implies
  (is-typed-amem-p gem-typed-mem)
  (or
   (and
    (null (assoc-equal v gem-typed-mem))
    (null (get-cell v gem-typed-mem)))
   (is-mem-cell-p (get-cell v gem-typed-mem))))
 :rule-classes nil)








(defun m-correspondent-values-p (m gem-typed-mem rtm-typed-mem)
 (cond
  ( (endp m)
    (null m) )
  ( t
    (and
     (equal-values-and-attributes
      (get-cell (gemvar-0 m) gem-typed-mem)
      (rtmintvars-0 m)
      rtm-typed-mem (type-0 m))
     (m-correspondent-values-p (cdr m)  gem-typed-mem rtm-typed-mem)))))

(defun decode (m rtm-typed-mem)
 (if
  (endp m)
    nil
    (put-cell
     (gemvar-0 m)
     (invert-cell (rtmintvars-0 m) rtm-typed-mem (type-0 m))
     (decode (cdr m) rtm-typed-mem))))


(defthm silly1
     (equal (caar m) (gemvar-0 m)))

(in-theory (disable silly1))

(defthm silly2
  (implies
   (correct-wrt-arity m gem-typed-mem)
   (correct-wrt-arity (cdr m) gem-typed-mem)))

(in-theory (disable silly1 silly2))

(defun bounded-amem-p (mem)
  (if
      (endp mem)
      (null mem)
    (and (bounded-value (cdr (car mem)))
	 (bounded-amem-p (cdr mem)))))

(defthm any-cell-of-bounded-mem-is-bounded
 (implies
  (bounded-amem-p gem-typed-mem)
  (bounded-value (get-cell v gem-typed-mem)))
 :rule-classes nil)

(defthm decode-equals-retrieve-vars
 (implies
  (and
   (rel-prime-moduli *rns*)
   (integer-listp *rns*)
   (not (null *rns*))
   (m-correspondent-values-p m gem-typed-mem rtm-typed-mem)
   (is-typed-amem-p gem-typed-mem)
   (bounded-amem-p gem-typed-mem)
   (correct-wrt-arity m gem-typed-mem))
  (equal
   (decode m rtm-typed-mem)
   (retrieve-vars m gem-typed-mem)))
 :hints (("Goal" :induct (len m))
	 ("Subgoal *1/1"
	  :in-theory nil
	  :use (silly1
		silly2
		decode
		(:instance retrieve-vars (vars m) (mem gem-typed-mem))
		m-correspondent-values-p
		(:instance any-cell-of-a-typed-mem-is-nil-or-a-typed-cell (v (gemvar-0 m)))
		(:instance any-cell-of-bounded-mem-is-bounded (v (gemvar-0 m)))
		correct-arity-all-i-need
		(:instance invert-cell-inverts-for-m-correspondents
			   (rtmvars (rtmintvars-0 m))
			   (gem-cell (get-cell (gemvar-0 m) gem-typed-mem))
			   (type (type-0 m)))))))


(defthm decode-retrieves-gem-memory
 (implies
  (and
   (rel-prime-moduli *rns*)
   (integer-listp *rns*)
   (not (null *rns*))
   (vars-inclusion gem-typed-mem m)
   (vars-inclusion m gem-typed-mem)
   (m-correspondent-values-p m gem-typed-mem rtm-typed-mem)
   (is-typed-amem-p gem-typed-mem)
   (bounded-amem-p gem-typed-mem)
   (correct-wrt-arity m gem-typed-mem))
  (equal-memories (decode m rtm-typed-mem) gem-typed-mem))
 :hints (("Goal" :in-theory (enable retrieving-keeps-equality))))


(defun projectiocell (cell attr)
 (if (null cell)
     cell
     (if (equal (var-attribute cell) attr)
	 cell
         nil )))

(defun projectio (mem attr)
  (if (endp mem)
      nil
      (put-cell (caar mem)
		(projectiocell (cdr (car mem))  attr)
		(projectio (cdr mem) attr))))



(defthm cell-of-projected-mem-is-projected-cell
 (equal
  (get-cell cell (projectio mem attr))
  (projectiocell (get-cell cell mem) attr)))




(defthm projection-of-null-list-is-null-list
 (implies
   (equal-values (var-values l rtm-typed-mem) (make-null-list l))
   (equal-values (var-values l (projectio rtm-typed-mem attr)) (make-null-list l))))


(defthm null-cell-corresponds-to-null-lists-of-values
 (implies
  (and
   (null gem-cell)
   (equal-values-and-attributes gem-cell rtmvars rtm-typed-mem type))
  (equal-values (var-values rtmvars rtm-typed-mem) (make-null-list rtmvars)))
 :hints (("Goal" :in-theory (disable get-cell var-value var-attribute ))))



(defthm project-invert-commute-for-empty-cell
 (implies
  (and
   (null gem-cell)
   (equal-values-and-attributes gem-cell rtmvars rtm-typed-mem type))
 (equal (projectiocell (invert-cell rtmvars rtm-typed-mem type) attr)
	(invert-cell rtmvars (projectio rtm-typed-mem attr) type)))
 :hints (("Goal" :use (null-cell-corresponds-to-null-lists-of-values
		       (:instance projection-of-null-list-is-null-list (l rtmvars))))))



(defthm rtmvars-correspondent-to-nonemptycell-is-not-emptylist
 (implies
  (and
   (not (null (var-attributes rtmvars rtm-typed-mem)))
   (equal type (var-type gem-cell))
   (correct-type type)
   (not (null gem-cell))
   (equal (var-attribute gem-cell) attr)
   (is-mem-cell-p gem-cell)
   (equal-values-and-attributes gem-cell rtmvars rtm-typed-mem type))
  (not
   (equal-values
    (var-values rtmvars rtm-typed-mem)
    (make-null-list rtmvars)))))




(defthm values-remain-the-same-if-correspondent-attrs
 (implies
  (and
   (not (null (var-attributes rtmvars rtm-typed-mem)))
   (equal type (var-type gem-cell))
   (correct-type type)
   (not (null gem-cell))
   (equal (var-attribute gem-cell) attr)
   (is-mem-cell-p gem-cell)
   (equal-values-and-attributes gem-cell rtmvars rtm-typed-mem type))
 (equal
  (var-values rtmvars (projectio rtm-typed-mem attr))
  (var-values rtmvars rtm-typed-mem)))
 :hints (("Goal" :do-not '(generalize))))



(defthm attributes-same-1
 (implies
  (equal-elements attr (var-attributes rtmvars rtm-typed-mem))
     (equal
      (var-attributes rtmvars (projectio rtm-typed-mem attr))
      (var-attributes rtmvars rtm-typed-mem))))




(defthm inversion-2-for-nonempty-projected-on-same-attr
 (implies
  (and
   (not (null (var-attributes rtmvars rtm-typed-mem)))
   (equal type (var-type gem-cell))
   (correct-type type)
   (not (null gem-cell))
   (equal (var-attribute gem-cell) attr)
   (is-mem-cell-p gem-cell)
   (equal-values-and-attributes gem-cell rtmvars rtm-typed-mem type))
 (equal (invert-cell rtmvars (projectio rtm-typed-mem attr) type)
	(invert-cell rtmvars rtm-typed-mem type)))
 :hints (("Goal" :in-theory nil
          ;; modified for Version  2.7 fertilization
	  :use (
                (:instance invert-cell (rtm-typed-mem (projectio rtm-typed-mem attr)))
                invert-cell
                equal-values-and-attributes
                (:instance attributes-same-1 (attr (var-attribute gem-cell)))
                rtmvars-correspondent-to-nonemptycell-is-not-emptylist
                values-remain-the-same-if-correspondent-attrs)
          :expand ((:free (x) (hide x))))))


(defthm inversion-1-for-nonempty-projected-on-different-attr
 (implies
  (and
   (not (null (var-attributes rtmvars rtm-typed-mem)))
   (equal type (var-type gem-cell))
   (correct-type type)
   (not (null gem-cell))
   (not (equal (var-attribute gem-cell) attr))
   (is-mem-cell-p gem-cell)
   (equal-values-and-attributes gem-cell rtmvars rtm-typed-mem type))
 (equal (projectiocell (invert-cell rtmvars rtm-typed-mem type) attr)
	nil)))


(defthm projecting-on-different-attr-gets-nils
 (implies
  (and
   (not (equal (var-attribute gem-cell) attr))
   (equal-values-and-attributes gem-cell rtmvars rtm-typed-mem type))
  (equal-values
   (var-values rtmvars (projectio rtm-typed-mem attr))
   (make-null-list rtmvars))))



(defthm decode-one-entry-of-null-list-is-nil
(implies
 (and
  (true-listp l)
  (not (endp l))
  (equal-values (var-values l rtm-typed-mem) (make-null-list l)))
 (equal (apply-invers-rns-to-values-according-to-type (var-values l rtm-typed-mem) ty) nil))
 :hints(("goal" :in-theory (enable build-value-by-inverse-rns-extended-for-nil))))


(defthm inversion-2-for-nonempty-projected-on-different-attr
 (implies
  (and
   (true-listp rtmvars)
   (not (null rtmvars))
   (not (equal (var-attribute gem-cell) attr))
   (equal-values-and-attributes gem-cell rtmvars rtm-typed-mem type))
 (equal (invert-cell rtmvars (projectio rtm-typed-mem attr) type)
	nil))
 :hints (("Goal" :use
	  ((:instance decode-one-entry-of-null-list-is-nil
		      (l rtmvars)
		      (rtm-typed-mem  (projectio rtm-typed-mem attr))
		      (ty type))
	   (:instance invert-cell (rtm-typed-mem (projectio rtm-typed-mem attr)))
	   projecting-on-different-attr-gets-nils))))




(defthm inversion-for-nonempty-projected-on-different-attr
 (implies
  (and
   (true-listp rtmvars)
   (not (null rtmvars))
   (not (null (var-attributes rtmvars rtm-typed-mem)))
   (equal type (var-type gem-cell))
   (correct-type type)
   (not (null gem-cell))
   (not (equal (var-attribute gem-cell) attr))
   (is-mem-cell-p gem-cell)
   (equal-values-and-attributes gem-cell rtmvars rtm-typed-mem type))
 (equal (projectiocell (invert-cell rtmvars rtm-typed-mem type) attr)
	(invert-cell rtmvars (projectio rtm-typed-mem attr) type)))
 :hints (("Goal"
	  :in-theory nil
	  :use
	  (inversion-1-for-nonempty-projected-on-different-attr
	   inversion-2-for-nonempty-projected-on-different-attr))))





(defthm project-invert-commuting
 (implies
  (and
   (true-listp rtmvars)
   (not (null rtmvars))
   (not (null (var-attributes rtmvars rtm-typed-mem)))
   (or
    (null gem-cell)
    (equal type (var-type gem-cell)))
   (correct-type type)
   (or (null gem-cell) (is-mem-cell-p gem-cell))
   (equal-values-and-attributes gem-cell rtmvars rtm-typed-mem type))
 (equal (projectiocell (invert-cell rtmvars rtm-typed-mem type) attr)
	(invert-cell rtmvars (projectio rtm-typed-mem attr) type)))
 :hints (("Goal" :cases
	  ( (and (not (null gem-cell)) (not (equal (var-attribute gem-cell) attr)))
	    (and (not (null gem-cell)) (equal (var-attribute gem-cell) attr))))
	 ("Subgoal 3" :use project-invert-commute-for-empty-cell)
	 ("Subgoal 2" :use inversion-for-nonempty-projected-on-different-attr)))

(defthm letssimplify
  (implies
  (and
   (true-listp rtmvars)
   (not (null rtmvars)))
   (not (null (var-attributes rtmvars rtm-typed-mem)))))


(defthm project-invert-commuting-better
 (implies
  (and
   (true-listp rtmvars)
   (not (null rtmvars))
   (or
    (null gem-cell)
    (equal type (var-type gem-cell)))
   (correct-type type)
   (or (null gem-cell) (is-mem-cell-p gem-cell))
   (equal-values-and-attributes gem-cell rtmvars rtm-typed-mem type))
 (equal (projectiocell (invert-cell rtmvars rtm-typed-mem type) attr)
	(invert-cell rtmvars (projectio rtm-typed-mem attr) type)))
 :hints (("Goal" :use (letssimplify project-invert-commuting))))



(in-theory (enable
		   m-entries-point-to-good-rtm-var-sets
		   m-correspondent-values-p))

(in-theory (disable gemvar-0 rtmintvars-0))

(defthm lil-helper
 (implies
  (and
   (not (endp m))
   (is-typed-amem-p gem-typed-mem)
   (correct-wrt-arity m gem-typed-mem)
   (m-entries-point-to-good-rtm-var-sets m rtm-typed-mem)
   (m-correspondent-values-p m gem-typed-mem rtm-typed-mem))
  (and
   (or
    (null (get-cell (gemvar-0 m) gem-typed-mem))
    (is-mem-cell-p (get-cell (gemvar-0 m) gem-typed-mem)))
   (true-listp (rtmintvars-0 m))
   (not (null (rtmintvars-0 m)))
   (correct-type (type-0 m))
   (or
    (null (get-cell (gemvar-0 m) gem-typed-mem))
    (equal (type-0 m) (var-type (get-cell (gemvar-0 m) gem-typed-mem))))
   (equal-values-and-attributes
    (get-cell (gemvar-0 m) gem-typed-mem)
    (rtmintvars-0 m)
    rtm-typed-mem
    (type-0 m))
   (correct-wrt-arity (cdr m) gem-typed-mem)
   (m-entries-point-to-good-rtm-var-sets (cdr m) rtm-typed-mem)
   (m-correspondent-values-p (cdr m) gem-typed-mem rtm-typed-mem)))
 :hints (("Goal" :use (:instance any-cell-of-a-typed-mem-is-nil-or-a-typed-cell
				 (v (gemvar-0 m)))))
 :rule-classes nil)



(defun decode-projection (m rtm-typed-mem attr)
  (if (endp m)
      nil
    (put-cell (gemvar-0 m)
	      (projectiocell
	       (invert-cell
		(rtmintvars-0 m)
	        rtm-typed-mem
		(type-0 m))
	       attr)
	      (decode-projection (cdr m) rtm-typed-mem attr))))


(in-theory (enable m-entries-point-to-good-rtm-var-sets))

(defthm project-of-decode-is-decode-projection
  (equal
   (projectio (decode m rtm-typed-mem) attr)
   (decode-projection m rtm-typed-mem attr)))


(defthm decode-projection-is-decode-of-projection
 (implies
  (and
   (is-typed-amem-p gem-typed-mem)
   (correct-wrt-arity m gem-typed-mem)
   (m-entries-point-to-good-rtm-var-sets m rtm-typed-mem)
   (m-correspondent-values-p m gem-typed-mem rtm-typed-mem))
 (equal
  (decode-projection  m rtm-typed-mem attr)
  (decode m (projectio rtm-typed-mem attr))))
 :hints (("Goal"  :induct (len m))
	 ("Subgoal *1/1" :in-theory nil
	  :use (lil-helper
		(:instance decode (rtm-typed-mem  (projectio rtm-typed-mem attr)))
		decode-projection
			       (:instance project-invert-commuting-better
				 (type (type-0 m))
				 (gem-cell (get-cell (gemvar-0 m) gem-typed-mem))
				 (rtmvars (rtmintvars-0 m)))))))



(defthm decode-project-commuting
 (implies
  (and
   (is-typed-amem-p gem-typed-mem)
   (correct-wrt-arity m gem-typed-mem)
   (m-entries-point-to-good-rtm-var-sets m rtm-typed-mem)
   (m-correspondent-values-p m gem-typed-mem rtm-typed-mem))
 (equal
  (projectio (decode m rtm-typed-mem) attr)
  (decode m (projectio rtm-typed-mem attr)))))



(in-theory (disable get-cell put-cell))

(defthm equalwrt-holds-on-project
 (implies
  (equal-wrt-vars m0 m1 m2)
  (equal-wrt-vars m0 (projectio m1 attr) (projectio m2 attr))))

(defthm projectio-keeps-caars
  (same-caars-p m0 (projectio m0 attr))
 :hints (("Goal" :in-theory (enable put-cell))))


(defthm equalwrt-holds-on-project-all
 (implies
  (equal-wrt-vars m0 m1 m2)
  (equal-wrt-vars (projectio m0 attr) m1 m2))
 :hints (("Goal" :use (:instance if-same-caars-same-equality-wrt-vars
				 (vars1 m0)
				 (vars2 (projectio m0 attr))
				 (mem1 m1)
				 (mem2 m2)))))

(defthm equalwrt-holds-on-project-all-all
 (implies
  (equal-wrt-vars m0 m1 m2)
  (equal-wrt-vars (projectio m0 attr) (projectio m1 attr) (projectio m2 attr)))
 :hints (("Goal" :use (:instance if-same-caars-same-equality-wrt-vars
				 (vars1 m0)
				 (vars2 (projectio m0 attr))
				 (mem1 m1)
				 (mem2 m2)))))

(defthm equal-memories-holds-by-projection
 (implies
  (equal-memories m1 m2)
  (equal-memories (projectio m1 attr) (projectio m2 attr))))




(defthm equalities-on-io
 (implies
  (and
   (rel-prime-moduli *rns*)
   (integer-listp *rns*)
   (not (null *rns*))
   (m-entries-point-to-good-rtm-var-sets m rtm-typed-mem)
   (vars-inclusion gem-typed-mem m)
   (vars-inclusion m gem-typed-mem)
   (m-correspondent-values-p m gem-typed-mem rtm-typed-mem)
   (is-typed-amem-p gem-typed-mem)
   (bounded-amem-p gem-typed-mem)
   (correct-wrt-arity m gem-typed-mem))
  (equal-memories (decode m (projectio rtm-typed-mem attr)) (projectio gem-typed-mem attr)))
 :hints (("Goal"
	  :in-theory (enable
		      equal-memories-commutative
		      retrieving-keeps-equality
		      decode-equals-retrieve-vars
		      equal-wrt-vars-reflexive
		      equal-wrt-vars-transitive
		      equalwrt-holds-on-project-all)
	  :use ( (:instance equal-memories-holds-by-projection
			    (m1 (decode m rtm-typed-mem))
			    (m2 gem-typed-mem))))))


(defthm fact-bout-rns-v0
  (and
   (integer-listp *rns*)
   (rel-prime-moduli *rns*)
   (posp-all *rns*)
   (not (null *rns*))
   (natp (prod *rns*))
   (> (prod *rns*) 1))
  :hints (("Goal" :in-theory (enable prod posp rel-prime-moduli rel-prime-all rel-prime g-c-d
  posp-all
  (:executable-counterpart nonneg-int-gcd))))
  :rule-classes nil)

(defun append-lists (list-of-lists)
 (if (endp list-of-lists)
     nil
     (append (car list-of-lists)
             (append-lists (cdr list-of-lists)))))

(defun retrieve-gemvars (m)
  (if
      (endp m)
      nil
    (cons (gemvar-0 m) (retrieve-gemvars (cdr m)))))

(defun retrieve-rtmvars (m)
  (if (endp m)
      nil
    (cons (cdr (car m))
	  (retrieve-rtmvars (cdr m)))))

(defun gem-variables (m) (retrieve-gemvars m))
(defun rtm-variables (m) (append-lists (retrieve-rtmvars m)))

(defun same-vars (m1 m2)
 (and
  (vars-inclusion m1 m2)
  (vars-inclusion m2 m1)))

(defun member-equal-bool (el l)
 (declare (xargs :guard (true-listp l)))
 (cond ((endp l) nil)
       ((equal el (car l)) t)
       (t (member-equal-bool el (cdr l)))))

(defun no-tmp-into-mapping (m)
  (if (endp m)
      t
    (and
     (not (member-equal-bool 'tmp (rtmintvars-0 m)))
     (no-tmp-into-mapping (cdr m)))))

(defun no-duplicates-p (l)
 (if (endp l)
     t
     (and (not (member-equal-bool (car l) (cdr l)))
          (no-duplicates-p (cdr l)))))


(defun apply-direct-rns-to-value-depending-on-type (gemvalue type)
 (cond ( (equal type 'bool) (list gemvalue) )
       ( (equal type 'int)  (build-values-by-rns-extended-for-nil gemvalue *rns*) )
       ( t nil )))

(defun represent-same-values-p (gemvalue rtmvalues type)
 (equal-values
  rtmvalues
  (apply-direct-rns-to-value-depending-on-type gemvalue type)))


(defun m-correspondent-vals-p (m gem-typed-mem rtm-typed-mem)
 (cond
  ( (endp m)
    (null m) )
  ( t
    (and
     (represent-same-values-p
      (var-value (get-cell (gemvar-0 m) gem-typed-mem))
      (var-values (rtmintvars-0 m) rtm-typed-mem)
      (type-0 m))
     (m-correspondent-vals-p (cdr m)  gem-typed-mem rtm-typed-mem)))))


(defun attributes-correspondence (m gem-typed-mem rtm-typed-mem)
  (if (endp m)
      (null m)
    (and
     (not (endp (rtmintvars-0 m)))
     (true-listp (rtmintvars-0 m))
     (not (equal 'error-value (get-common-value (var-attributes (rtmintvars-0 m) rtm-typed-mem))))
     (equal-elements
      (var-attribute (get-cell (gemvar-0 m) gem-typed-mem))
      (var-attributes (rtmintvars-0 m) rtm-typed-mem))
    (attributes-correspondence (cdr m) gem-typed-mem rtm-typed-mem))))


(defthm redefinition-of-m-corr
 (equal
  (and
   (m-entries-point-to-good-rtm-var-sets m rtm-vars)
   (m-correspondent-values-p m gem-vars rtm-vars))
  (and
   (attributes-correspondence m gem-vars rtm-vars)
   (m-correspondent-vals-p m gem-vars rtm-vars)))
 :rule-classes nil)



(defun is-variable-mapping (m gem-vars rtm-vars)
  (and
   (alistp m)
   (no-tmp-into-mapping m)
   (no-duplicates-p (gem-variables m))
   (no-duplicates-p (rtm-variables m))
   (correct-wrt-arity m gem-vars)
   (same-vars gem-vars m)
   (attributes-correspondence m gem-vars rtm-vars)
   (m-correspondent-vals-p m gem-vars rtm-vars)))

(defun output (mem) (projectio mem 'Output))

(defun is-gem-mem-p (mem)
 (and (is-typed-amem-p mem)
      (bounded-amem-p mem)))

(defthm mapping-correspondence-implies-same-outputs
 (implies
  (and
   (is-variable-mapping m gem-mem rtm-mem)
   (is-gem-mem-p gem-mem))
  (equal-memories
   (output gem-mem)
   (decode m (output rtm-mem))))
 :hints (("Goal" :use
          (fact-bout-rns-v0
           (:instance redefinition-of-m-corr
                      (gem-vars gem-mem)
                      (rtm-vars rtm-mem))
           (:instance equalities-on-io
                      (gem-typed-mem gem-mem)
                      (rtm-typed-mem rtm-mem))
           (:instance equal-memories-commutative
                      (mem1 (output gem-mem))
                      (mem2 (decode m (output rtm-mem)))))))
 :rule-classes nil)



(in-theory (disable correct-arity-all-i-need
		    if-every-element-matches-val-then-get-common-value-amounts-to-val
		    make-null-list-is-invariant-on-value-slicing
		    build-values-by-rns-extended-for-nils-provides-integers-from-integer
		    build-value-by-inverse-rns-extended-for-nils-behaves-standardly-on-integer-lists
		    crt-inversion-extended-to-nils-in-integer-case
		    apply-direct-rns-unfolding-for-integer-case
		    apply-direct-rns-unfolding-for-boolean-case
		    apply-inverse-direct-retrieves-same-value-for-typed-cells
		    inversion-for-empty-cell
		    ad-hoc-2-for-inversion-of-one-nonempty-cell-by-decode
		    ad-hoc-3-for-inversion-of-one-nonempty-cell-by-decode
		    nonempty-cell-is-not-mapped-into-nils-by-rns
		    nonempty-rtm-vars-which-correspond-to-gem-var-by-values-and-atributes-map-back-to-gem-var
		    decode-inversion-for-nonempty-gem-cell
		    invert-cell-inverts-for-m-correspondents
		    ;any-cell-of-a-typed-mem-is-nil-or-a-typed-cell
		    silly1
		    silly2
		    decode-equals-retrieve-vars
		    decode-retrieves-gem-memory
		    cell-of-projected-mem-is-projected-cell
		    projection-of-null-list-is-null-list
		    null-cell-corresponds-to-null-lists-of-values
		    project-invert-commute-for-empty-cell
		    rtmvars-correspondent-to-nonemptycell-is-not-emptylist
		    values-remain-the-same-if-correspondent-attrs
		    attributes-same-1
		    inversion-2-for-nonempty-projected-on-different-attr
		    inversion-1-for-nonempty-projected-on-different-attr
		    projecting-on-different-attr-gets-nils
		    decode-one-entry-of-null-list-is-nil
		    inversion-2-for-nonempty-projected-on-different-attr
		    inversion-for-nonempty-projected-on-different-attr
		    project-invert-commuting
		    letssimplify
		    project-invert-commuting-better
		    decode-projection-is-decode-of-projection
		    decode-project-commuting
		    equalwrt-holds-on-project-all
		    equalwrt-holds-on-project-all-all
		    equal-memories-holds-by-projection
		    equalities-on-io))








