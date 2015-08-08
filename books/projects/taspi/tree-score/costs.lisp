(in-package "ACL2")
(include-book "../code/sequences/seqs")

;; A list of scores/costs has elements that are rationals or else nil (denoting infinity.)
(defun rational-or-nil-listp (x)
  (declare (xargs :guard t))
  (if (atom x)
      t
    (and (or (not (car x))
             (rationalp (car x)))
         (rational-or-nil-listp (cdr x)))))

;; A list of rational-or-nil-lists, (for example, a char-scorelist)
(defun rational-or-nil-list-listp (x)
  (declare (xargs :guard t))
  (if (atom x)
      t
    (and (rational-or-nil-listp (car x))
         (rational-or-nil-list-listp (cdr x)))))

;; Functions to add and find minimums when nil is taken to represent infinity
(defun plus-nil-inf (x y)
  (declare (xargs :guard (and (or (not x) (rationalp x))
                              (or (not y) (rationalp y)))))
  (if (and x y)
      (+ x y)
    nil))

(defun min-nil-inf (x y)
  (declare (xargs :guard (and (or (not x) (rationalp x))
                              (or (not y) (rationalp y)))))
  (if x
      (if y
          (if (< x y) x y)
        x)
    y))

;; Minimum of a list (with nil = infinity)
(defun min-list (list)
  (declare (xargs :guard (rational-or-nil-listp list)))
  (if (atom list)
      nil
    (min-nil-inf (car list) (min-list (cdr list)))))


;; Sum of a list (with nil = infinity)
(defun sum-list (list)
  (declare (xargs :guard (rational-or-nil-listp list)))
  (if (atom list)
      0
    (plus-nil-inf (car list) (sum-list (cdr list)))))

(defthm rationalp-min-list
  (implies (and (rational-or-nil-listp list)
                (min-list list))
           (rationalp (min-list list))))

;; Sum (over all elements of the list) of the minimum of all elements in the sublist.
(defun sum-minima (scorelist)
  (declare (xargs :guard (rational-or-nil-list-listp scorelist)
                  :verify-guards nil))
  (if (atom scorelist)
      0
    (plus-nil-inf (min-list (car scorelist))
                  (sum-minima (cdr scorelist)))))

(defthm rationalp-sum-minima
  (implies (and (rational-or-nil-list-listp scorelist)
                (sum-minima scorelist))
           (rationalp (sum-minima scorelist)))
  :hints (("Subgoal *1/4'5'" :in-theory (disable rationalp-min-list)
           :use (:instance rationalp-min-list
                           (list scorelist1)))))

(verify-guards sum-minima)

;; A list where each element is a rational-or-nil-listp of length alphabet-len.  At
;; some node in the tree, we'll have a sequence-scorelist the length of a sequence,
;; which holds, for each character c in the sequence and for each
;; unambiguous state x, the parsimony score contribution of c over that subtree
;; given that the state at the root is x.
;; i.e. the nth entry in the sequence-scorelist will be parsimony score
;; contribution of the nth character c in the sequence.
(defun sequence-scorelistp (x alphabet-len)
  (declare (xargs :guard (acl2-numberp alphabet-len)))
  (if (atom x)
      t
    (and (equal (len (car x)) alphabet-len)
         (rational-or-nil-listp (car x))
         (sequence-scorelistp (cdr x) alphabet-len))))

(defthm char-scorelistp-rational-or-nil-list-listp
  (implies (sequence-scorelistp x n)
           (rational-or-nil-list-listp x)))

(defthm rational-or-nil-listp-make-list-ac
  (implies (and  (rational-or-nil-listp acc)
		 (or (rationalp const)
		     (null const)))
           (rational-or-nil-listp (make-list-ac n const acc))))

(defthm rational-or-nil-listp-const-list-acc
  (implies (and (rational-or-nil-listp acc)
                (or (rationalp const)
                    (null const)))
           (rational-or-nil-listp (hons-make-list-acc n const acc))))

(defthm rational-or-nil-listp-nil-list
  (rational-or-nil-listp (hons-make-list-acc n nil nil)))

(defthm len-const-list-acc
  (implies (natp n)
           (equal (len (hons-make-list-acc n const acc))
                  (+ n (len acc)))))

(defthm len-nil-list
  (implies (natp n)
           (equal (len (hons-make-list-acc n nil nil)) n))
  :hints (("Goal" :use ((:instance len-const-list-acc (const nil) (acc nil))))))

(defthm len-make-list-ac
  (implies (natp n)
	   (equal (len (make-list-ac n const acc))
		  (+ n (len acc)))))

(defun zero-scores (seq)
  (declare (xargs :guard t))
  (if (atom seq)
      nil
    (cons 0 (zero-scores (cdr seq)))))

(defthm zero-scores-len
  (equal (len (zero-scores seq))
         (len seq)))

(defthm zero-scores-rational-or-nil-lisp
  (rational-or-nil-listp (zero-scores seq)))

;; Recognizes a mapping from possible character states
;; to a default scorelist (e.g. *dna-scorelists*)
(defun charstate-scorelist-map-p (x alpha-len)

;;; Legacy doc string replaced Nov. 2014 by auto-generated defxdoc form;
;;; see projects/taspi/taspi-xdoc.lisp.

; ":Doc-Section TASPI
;  Recognizes a well-formed mapping from possible character states to its
;  score list of length alpha-len.~/
;  ~/
;  Arguments:
;     (1) x - a potential character state scorelist
;     (2) alpha-len - the required alphabet length (number of unambiguous
;                     characters)

;  "
  (declare (xargs :guard (acl2-numberp alpha-len)))
  (if (atom x)
      t
    (and (consp (car x))
         (valid-char (caar x))
         (rational-or-nil-listp (cdar x))
         (equal (len (cdar x)) alpha-len)
         (charstate-scorelist-map-p (cdr x) alpha-len))))

(defthm assoc-hqual-state-scorelist-map
  (implies (and (charstate-scorelist-map-p x alpha-len)
                (assoc-hqual key x))
           (and (rational-or-nil-listp (cdr (assoc-hqual key x)))
                (equal (len (cdr (assoc-hqual key x))) alpha-len))))

;; Makes the char-scorelist for a leaf node with sequence seq.  Iterates
;; through seq; for each state, looks it up in the charstate scorelist map cssl-map.  If
;; it's there, uses its value there, otherwise makes a list of all nils.
(defun make-leaf-score-list (seq cssl-map alpha-len)
  (declare (xargs :guard (and (valid-seq seq)
                              (natp alpha-len)
                              (charstate-scorelist-map-p cssl-map alpha-len))))
  (if (atom seq)
      nil
    (let ((scoreList (het (car seq) cssl-map)))
      (cons (if scoreList (cdr scoreList) (hons-make-list-acc alpha-len nil nil))
            (make-leaf-score-list (cdr seq) cssl-map alpha-len)))))

(defthm sequence-scorelistp-make-leaf-score-list
  (implies (and (natp alpha-len)
                (charstate-scorelist-map-p cssl-map alpha-len))
           (sequence-scorelistp (make-leaf-score-list seq cssl-map alpha-len) alpha-len)))

(defthm len-make-leaf-score-list
  (equal (len (make-leaf-score-list seq cssl-map alpha-len))
         (len seq)))

;; Transition cost matrix/mapping of charstates to cost
;; Made a simple list of lists
(defun cost-rowp (x)
  (declare (xargs :guard t))
  (and (consp x)
       (valid-char (car x))
       (rational-or-nil-listp (cdr x))))

(defun cost-matrixp (x)
  (declare (xargs :guard t))
  (if (atom x)
      t
    (and (cost-rowp (car x))
         (cost-matrixp (cdr x)))))

(defun cost-matrixp-nstates (x n)

;;; Legacy doc string replaced Nov. 2014 by auto-generated defxdoc form;
;;; see projects/taspi/taspi-xdoc.lisp.

; ":Doc-Section TASPI
;  Recognizes a well-formed cost matrix with n states.~/
;  ~/
;  Arguments:
;     (1) x - a potential cost matrix
;     (2) n - the number of unambiguous characters

;  "
  (declare (xargs :guard (natp n)))
  (if (atom x)
      t
    (and (consp (car x))
         (valid-char (caar x))
         (rational-or-nil-listp (cdar x ))
         (equal (len (cdar x)) n)
         (cost-matrixp-nstates (cdr x) n))))

(defthm cost-matrixp-nstates-cost-matrixp
  (implies (cost-matrixp-nstates x n)
           (cost-matrixp x)))

(defthm cost-matrix-het
  (implies (and (cost-matrixp x)
                (assoc-hqual key x))
           (rational-or-nil-listp (cdr (assoc-hqual key x)))))

;; Helper functions for testing
(defun make-default-costlist (currstate alphabet)
  (if (atom alphabet)
      nil
    (cons (if (equal (car alphabet) currstate) 0 1)
          (make-default-costlist currstate (cdr alphabet)))))

(defun make-default-cmat (alphabet whole)
  (if (atom alphabet)
      nil
    (cons (cons (car alphabet) (make-default-costlist (car alphabet) whole))
          (make-default-cmat (cdr alphabet) whole))))

(defun make-default-cost-matrix (alphabet)
  (make-default-cmat alphabet alphabet))
