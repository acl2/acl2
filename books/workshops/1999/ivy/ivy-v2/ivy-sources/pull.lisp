(in-package "ACL2")

;; The pull books are arranged like this:
;;
;;        pull-top
;;          /  \
;; pull-pulls  pull-sound
;;          \  /
;;          pull
;;
;; This book (pull) has the main definitions and some
;; preservation-of-property theorems.  The top definition
;; is (pull-quants f), which pulls quantifiers to the
;; top of a formula.

(include-book "wfftype")
(include-book "permutations")

;;--------------------------------------
;; Function pull (f) moves quantifiers toward the root of a formula
;; as much as possible, using rules like
;; (or p (all x q)) <=> (all x (or p q)) if x is not free in p.
;; Bound variables are NOT renamed.  If all bound variables are
;; unique, the formula is closed nnf, then all quantifiers should
;; come to the top.  (That property proved elsewhere.)  Here,
;; we define the functions and prove soundness.
;;
;; Pull-top-left pulls quantifiers up from the left side, and
;; pull-top-right from the right side.
;;
;; The first functions I wrote were a little simpler than these.
;; Originally, when pull-top right got to the base case, it called
;; pull-top-left.  Now, they are independent (and the same except for
;; left/right):  we first pull-top-left, then call down-right,
;; which goes back down to the 'and or 'or and calls pull-top-right.
;;
;;     or                      q1                   q1
;;    / \           ->         q2        ->         q2
;;   q1 q3    pull-top-left    or    down-right     q3
;;   q2 q4                    / \  (pull-top-right) q4
;;   A   B                   A  q3                  or
;;                              q4                 / \
;;                               B                A   B
;;
;; I changed to the current version, because I had trouble getting
;; a soundness proof for the original.

(defun pull-top-right (op f g)
  (declare (xargs :guard (and (or (equal op 'and) (equal op 'or))
			      (wff f) (nnfp f)
			      (wff g) (nnfp g))))
  (if (and (or (equal op 'and) (equal op 'or))
	   (wfquant g)
	   (not (free-occurrence (a1 g) f)))
      (list (car g) (a1 g) (pull-top-right op f (a2 g)))
      (list op f g)))

(defun pull-top-left (op f g)
  (declare (xargs :guard (and (or (equal op 'and) (equal op 'or))
			      (wff f) (nnfp f)
			      (wff g) (nnfp f))))
  (if (and (or (equal op 'and) (equal op 'or))
	   (wfquant f)
	   (not (free-occurrence (a1 f) g)))
      (list (car f) (a1 f) (pull-top-left op (a2 f) g))
      (list op f g)))

(defun down-right (f)
  (declare (xargs :guard (and (wff f) (nnfp f))))
  (cond ((wfquant f) (list (car f) (a1 f) (down-right (a2 f))))
	((or (wfand f)
	     (wfor f)) (pull-top-right (car f) (a1 f) (a2 f)))
	(t f)))

;; Beware!  Something about pull, I don't know what, causes
;; rewrite explosions.  Even to get guards verified, I had to
;; disable pull.  In other proofs below, down-right is disabled,
;; which helps somewhat.

(defun pull (f)
  (declare (xargs :guard (and (wff f) (nnfp f))
		  :verify-guards nil))
  (cond ((or (wfand f)
	     (wfor f)) (down-right (pull-top-left (car f)
						  (pull (a1 f))
						  (pull (a2 f)))))
	((wfquant f) (list (car f) (a1 f) (pull (a2 f))))
	(t f)))

;;---------------
;; Prove the the pull functions preserve wff and nnfp, and finally
;; verify guards for pull.

(defthm pull-top-right-wff
  (implies (and (wff f)
		(wff g)
		(or (equal op 'and) (equal op 'or)
		    (equal op 'imp) (equal op 'iff)))
	   (wff (pull-top-right op f g))))

(defthm pull-top-right-nnfp
  (implies (and (nnfp f)
		(nnfp g)
		(or (equal op 'and) (equal op 'or)))
	   (nnfp (pull-top-right op f g)))
  :hints (("Goal"
	   :induct (pull-top-right op f g))))

(defthm pull-top-left-wff
  (implies (and (wff f)
		(wff g)
		(or (equal op 'and) (equal op 'or)
		    (equal op 'imp) (equal op 'iff)))
	   (wff (pull-top-left op f g))))

(defthm pull-top-left-nnfp
  (implies (and (nnfp f)
		(nnfp g)
		(or (equal op 'and) (equal op 'or)))
	   (nnfp (pull-top-left op f g)))
  :hints (("Goal"
	   :induct (pull-top-left op f g))))

(defthm down-right-wff
  (implies (wff f)
	   (wff (down-right f))))

(defthm down-right-nnfp
  (implies (nnfp f)
	   (nnfp (down-right f)))
  :hints (("Goal"
	   :induct (down-right f))))

(defthm pull-wff
  (implies (wff f)
	   (wff (pull f)))
  :hints (("Goal"
           :in-theory (disable down-right))))

(defthm pull-nnfp
  (implies (nnfp f)
	   (nnfp (pull f)))
  :hints (("Goal"
           :in-theory (disable down-right))))

(verify-guards pull
  :hints (("Goal"
           :in-theory (disable pull))))

;;----------------------------------------
;; Here is a wrapper for pull.  This checks the (unnecessary I think) setp
;; condition in the soundness theorem.

(defun pull-quants (f)
  (declare (xargs :guard (and (wff f) (nnfp f))))
  (if (setp (quantified-vars f))
      (pull f)
    f))

(defthm pull-quants-wff
  (implies (wff f)
	   (wff (pull-quants f)))
  :hints (("Goal"
           :in-theory (disable pull))))

(defthm pull-quants-nnfp
  (implies (nnfp f)
	   (nnfp (pull-quants f)))
  :hints (("Goal"
           :in-theory (disable pull))))

;;---------------
;; Show that each pull functions preserves the set of free variables.

(defthm ptr-preserves-free-vars
  (implies (or (equal op 'and) (equal op 'or))
	   (equal (free-vars (pull-top-right op f g))
		  (union-equal (free-vars f) (free-vars g))))
  :hints (("Goal"
	   :induct (pull-top-right op f g))))

(defthm ptl-preserves-free-vars
  (implies (or (equal op 'and) (equal op 'or))
	   (equal (free-vars (pull-top-left op f g))
		  (union-equal (free-vars f) (free-vars g))))
  :hints (("Goal"
	   :induct (pull-top-left op f g))))

(defthm down-right-preserves-free-vars
  (equal (free-vars (down-right f))
	 (free-vars f))
  :hints (("Goal"
	   :induct (down-right f))))

(defthm pull-preserves-free-vars
  (equal (free-vars (pull f))
	 (free-vars f))
  :hints (("Goal"
	   :induct (pull f))))

(defthm pull-quants-preserves-free-vars
  (equal (free-vars (pull-quants f))
	 (free-vars f))
  :hints (("Goal"
	   :do-not-induct t
	   :in-theory (disable pull))))

;;------------------------------------
;; The various operations preserve the set of quantified variables.
;; Note equality for pull-top-right, permutation for the rest.
;; (If the original formula is closed nnf with unique quantified
;; variables, all quantifiers come to the top, then does equality hold.
;; If I had proved this, some later things would have been simpler.)

(defthm ptl-preserves-qvars
  (implies (and (or (equal op 'and) (equal op 'or)))
	   (equal (quantified-vars (pull-top-left op f g))
		  (append (quantified-vars f)
			  (quantified-vars g)))))

(defthm ptr-unique-qvars-2
  (implies (or (equal op 'and) (equal op 'or))
	   (perm (quantified-vars (pull-top-right op f g))
		 (append (quantified-vars f)
			 (quantified-vars g)))))

(defthm down-right-unique-vars-2
  (perm (quantified-vars (down-right f))
	(quantified-vars f)))

(defthm pull-unique-vars-2
  (perm (quantified-vars (pull f))
	(quantified-vars f))
  :hints (("Goal"
           :in-theory (disable down-right set-equal))))

;;---------------------------
;; The pull operations preserve exists-count.

(defthm ptl-preserves-exists-count
  (implies (or (equal op 'and) (equal op 'or))
	   (equal (exists-count (pull-top-left op f g))
		  (+ (exists-count f) (exists-count g))))
  :hints (("Goal"
	   :induct (pull-top-left op f g))))

(defthm ptr-preserves-exists-count
  (implies (or (equal op 'and) (equal op 'or))
	   (equal (exists-count (pull-top-right op f g))
		  (+ (exists-count f) (exists-count g))))
  :hints (("Goal"
	   :induct (pull-top-right op f g))))

(defthm down-right-preserves-exists-count
  (equal (exists-count (down-right f))
	 (exists-count f))
  :hints (("Goal"
	   :induct (down-right f))))

(defthm pull-preserves-exists-count
  (equal (exists-count (pull f))
	 (exists-count f))
  :hints (("Goal"
           :in-theory (disable pull-top-left pull-top-right down-right))))

(defthm pull-quants-preserves-exists-count
  (equal (exists-count (pull-quants f))
	 (exists-count f))
  :hints (("Goal"
           :in-theory (disable pull-top-left pull-top-right down-right))))

;;------------

(defthm pull-quants-setp
  (implies (setp (quantified-vars f))
	   (setp (quantified-vars (pull-quants f))))
  :hints (("Goal"
	   :in-theory (disable pull))))
