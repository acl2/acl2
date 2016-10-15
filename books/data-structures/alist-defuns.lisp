; Alist-defuns.lisp - definitions of functions in the theory of alists.
; Copyright (C) 1997  Computational Logic, Inc.
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; Written by:  Bill Bevier (bevier@cli.com)
; Computational Logic, Inc.
; 1717 West Sixth Street, Suite 290
; Austin, TX 78703-4776 U.S.A.

(in-package "ACL2")
(deflabel alist-defuns-section)

; * Structure of the Theory
;
; The functions which occur in the alist theory are selected from
; the ACL2 base theory (as defined in axioms.lisp) plus other functions
; which descend from earlier alist libraries.
;
; alist-defuns.lisp contains the definitions of functions which are not
; in the ACL2 base theory.
;
; alist-defthms.lisp contains theorems about the functions in the
; theory. Segregating the theory into two files allows one to load
; only the definitions when one is only interested in running
; simulations.
;
; * General Strategy for Theory Construction
;
; The goal of this theory is to provide useful alist-processing functions
; and useful theorems about those functions.
;
; * Enabled and Disabled functions
;
; We plan to leave all recursive functions enabled. The theorem prover
; is good at deciding when to open recursive functions. An expert user
; can choose to disable them explicitly.
;
; Non-recursive functions are globally disabled by the book alist-defthms.
;
; * Equality
;
; ACL2 (and Common Lisp) support three notions of equality: EQL, EQ and EQUAL.
; One uses EQL or EQ, rather than EQUAL, for efficiency. Many functions
; have three versions, each based on a different equality. ASSOC uses EQL,
; however ASSOC-EQ and ASSOC-EQUAL are also defined.
;
; We have followed this naming convention. When a function relies on equality.
; the default notion is EQL; -EQ and -EQUAL versions of the function are
; also provided.
;
; In list-defthms, the EQL and EQ versions of all functions are re-written to the
; EQUAL version. All interesting rewrite rules about the list functions are
; expressed in terms of the EQUAL versions of list functions.
;
; As a result, one can execute using the EQL or EQ versions, but one will reason
; using the EQUAL version.

; ------------------------------------------------------------
; Definitions
; ------------------------------------------------------------

; Acl2                       In ACL2  type
; ----                       -------  ----
;
; acons                      yes      alist
; append                     yes      alist
; alist-compose (eql)        no       alist
;   alist-compose-eq         no       alist
;   alist-compose-equal      no       alist
; bind (eql)                 no       alist
;   bind-eq                  no       alist
;   bind-equal               no       alist
; bind-all (eql)             no       alist
;   bind-all-eq              no       alist
;   bind-all-equal           no       alist
; bind-pairs (eql)           no       alist
;   bind-pairs-eq            no       alist
;   bind-pairs-equal         no       alist
; domain-restrict (eql)      no       alist
;   domain-restrict-eq       no       alist
;   domain-restrict-equal    no       alist
; pairlis$                   yes      alist
; rembind (eql)              no       alist
;   rembind-eq               no       alist
;   rembind-equal            no       alist
; rembind-all (eql)          no       alist
;   rembind-all-eq           no       alist
;   rembind-all-equal        no       alist
;
; assoc (eql)                yes      cons or NIL
;   assoc-eq                 yes      cons or NIL
;   assoc-equal              yes      cons or NIL
; binding                    no       value or NIL
;   binding-eq               no       value or NIL
;   binding-equal            no       value or NIL
;
; alistp                     yes      boolean
; bound?                     no       boolean
;   bound?-eq                no       boolean
;   bound?-equal             no       boolean
; all-bound? (eql)           no       boolean
;   all-bound?-eq            no       boolean
;   all-bound?-equal         no       boolean
;
; all-bindings (eql)         no       list
;   all-bindings-eq          no       list
;   all-bindings-equal       no       list
; collect-bound (eql)        no       list
;   collect-bound-eq         no       list
;   collect-bound-equal      no       list
; domain                     no       list
; range                      yes      list


(defun bind (x y a)
  "The alist derived from A by binding X to Y."
  (declare (xargs :guard (and (alistp a) (eqlablep x))))
  (cond ((endp a) (list (cons x y)))
	((eql x (car (car a))) (cons (cons x y) (cdr a)))
	(t (cons (car a) (bind x y (cdr a))))))

(defun bind-eq (x y a)
  "The alist derived from A by binding X to Y."
  (declare (xargs :guard (and (alistp a) (symbolp x))))
  (cond ((endp a) (list (cons x y)))
	((eq x (car (car a))) (cons (cons x y) (cdr a)))
	(t (cons (car a) (bind-eq x y (cdr a))))))

(defun bind-equal (x y a)
  "The alist derived from A by binding X to Y."
  (declare (xargs :guard (alistp a)))
  (cond ((endp a) (list (cons x y)))
	((equal x (car (car a))) (cons (cons x y) (cdr a)))
	(t (cons (car a) (bind-equal x y (cdr a))))))

(defun bind-all (keys vals a)
  "The alist whose domain is A's range, and whose range is A's domain."
  (declare (xargs :guard (and (true-listp vals)
			      (eqlable-listp keys)
			      (eqlable-alistp a))))
  (cond ((endp keys) a)
	((endp vals) a)
	(t (bind (car keys) (car vals)
		 (bind-all (cdr keys) (cdr vals) a)))))

(defun bind-all-eq (keys vals a)
  "The alist whose domain is A's range, and whose range is A's domain."
  (declare (xargs :guard (and (true-listp vals)
			      (symbol-listp keys)
			      (symbol-alistp a))))
  (cond ((endp keys) a)
	((endp vals) a)
	(t (bind-eq (car keys) (car vals)
		    (bind-all-eq (cdr keys) (cdr vals) a)))))

(defun bind-all-equal (keys vals a)
  "The alist whose domain is A's range, and whose range is A's domain."
  (declare (xargs :guard (and (true-listp keys)
			      (true-listp vals)
			      (alistp a))))
  (cond ((endp keys) a)
	((endp vals) a)
	(t (bind-equal (car keys) (car vals)
		       (bind-all-equal (cdr keys) (cdr vals) a)))))


(defun binding (x a)
  "The value bound to X in alist A."
  (declare (xargs :guard (and (alistp a)
			      (or (eqlablep x)
				  (eqlable-alistp a)))))
  (cdr (assoc x a)))

(defun binding-eq (x a)
  "The value bound to X in alist A."
  (declare (xargs :guard (and (alistp a)
			      (or (symbolp x)
				  (symbol-alistp a)))))
  (cdr (assoc-eq x a)))

(defun binding-equal (x a)
  "The value bound to X in alist A."
  (declare (xargs :guard (alistp a)))
  (cdr (assoc-equal x a)))

(defun bound? (x a)
  "The value bound to X in alist A."
  (declare (xargs :guard (and (alistp a)
			      (or (eqlablep x) (eqlable-alistp a)))))
  (consp (assoc x a)))

(defun bound?-eq (x a)
  "The value bound to X in alist A."
  (declare (xargs :guard (and (alistp a)
			      (or (symbolp x) (symbol-alistp a)))))
  (consp (assoc-eq x a)))

(defun bound?-equal (x a)
  "The value bound to X in alist A."
  (declare (xargs :guard (alistp a)))
  (consp (assoc-equal x a)))

(defun all-bound? (l a)
  "Are all elements of list L bound in alist A?"
  (declare (xargs :guard (and (true-listp l)
			      (alistp a)
			      (or (eqlable-listp l)
				  (eqlable-alistp a)))))
  (cond ((endp l) t)
	(t (and (bound? (car l) a)
		(all-bound? (cdr l) a)))))

(defun all-bound?-eq (l a)
  "Are all elements of list L bound in alist A?"
  (declare (xargs :guard (and (true-listp l)
			      (alistp a)
			      (or (symbol-listp l)
				  (symbol-alistp a)))))
  (cond ((endp l) t)
	(t (and (bound?-eq (car l) a)
		(all-bound?-eq (cdr l) a)))))

(defun all-bound?-equal (l a)
  "Are all elements of list L bound in alist A?"
  (declare (xargs :guard (and (true-listp l)
			      (alistp a))))
  (cond ((endp l) t)
	(t (and (bound?-equal (car l) a)
		(all-bound?-equal (cdr l) a)))))

(defun all-bindings (l a)
  "The list of bindings of elements of list L in alist A."
  (declare (xargs :guard (and (true-listp l)
			      (alistp a)
			      (or (eqlable-listp l)
				  (eqlable-alistp a)))))
  (cond ((endp l) nil)
	((bound? (car l) a)
	 (cons (binding (car l) a)
	       (all-bindings (cdr l) a)))
	(t (all-bindings (cdr l) a))))

(defun all-bindings-eq (l a)
  "The list of bindings of elements of list L in alist A."
  (declare (xargs :guard (and (true-listp l)
			      (alistp a)
			      (or (symbol-listp l)
				  (symbol-alistp a)))))
  (cond ((endp l) nil)
	((bound?-eq (car l) a)
	 (cons (binding-eq (car l) a)
		 (all-bindings-eq (cdr l) a)))
	(t (all-bindings-eq (cdr l) a))))

(defun all-bindings-equal (l a)
  "The list of bindings of elements of list L in alist A."
  (declare (xargs :guard (and (true-listp l)
			      (alistp a))))
  (cond ((endp l) nil)
	((bound?-equal (car l) a)
	 (cons (binding-equal (car l) a)
	       (all-bindings-equal (cdr l) a)))
	(t (all-bindings-equal (cdr l) a))))

(defun domain (a)
  "The list of CARs of an alist."
  (declare (xargs :guard (alistp a)))
  (strip-cars a))

(defun domain-restrict (l a)
  "An alist containing only those pairs in A whose CAR is in L."
  (declare (xargs :guard (and (eqlable-listp l)
			      (eqlable-alistp a))))
  (cond ((endp a) nil)
	((member (car (car a)) l)
	 (cons (car a) (domain-restrict l (cdr a))))
	(t (domain-restrict l (cdr a)))))

(defun domain-restrict-eq (l a)
  "An alist containing only those pairs in A whose CAR is in L."
  (declare (xargs :guard (and (symbol-listp l)
			      (symbol-alistp a))))
  (cond ((endp a) nil)
	((member-eq (car (car a)) l)
	 (cons (car a) (domain-restrict-eq l (cdr a))))
	(t (domain-restrict-eq l (cdr a)))))

(defun domain-restrict-equal (l a)
  "An alist containing only those pairs in A whose CAR is in L."
  (declare (xargs :guard (and (true-listp l)
			      (alistp a))))
  (cond ((endp a) nil)
	((member-equal (car (car a)) l)
	 (cons (car a) (domain-restrict-equal l (cdr a))))
	(t (domain-restrict-equal l (cdr a)))))

(defun range (a)
  "The list of CDRs of an alist."
  (declare (xargs :guard (alistp a)))
  (strip-cdrs a))

(defun rembind (x a)
  "The alist derived from A by removing any binding of X."
  (declare (xargs :guard (and (alistp a)
			      (or (eqlablep x)
				  (eqlable-alistp a)))))
  (cond ((endp a) nil)
	((eql x (car (car a))) (rembind x (cdr a)))
	(t (cons (car a) (rembind x (cdr a))))))

(defun rembind-eq (x a)
  "The alist derived from A by removing any binding of X."
  (declare (xargs :guard (and (alistp a)
			      (or (symbolp x)
				  (symbol-alistp a)))))
  (cond ((endp a) nil)
	((eq x (car (car a))) (rembind-eq x (cdr a)))
	(t (cons (car a) (rembind-eq x (cdr a))))))

(defun rembind-equal (x a)
  "The alist derived from A by removing any binding of X."
  (declare (xargs :guard (alistp a)))
  (cond ((endp a) nil)
	((equal x (car (car a))) (rembind-equal x (cdr a)))
	(t (cons (car a) (rembind-equal x (cdr a))))))

(defun rembind-all (l a)
  (declare (xargs :Guard (and (eqlable-listp l)
			      (eqlable-alistp a))))
  (cond ((endp l) a)
	(t (rembind (car l) (rembind-all (cdr l) a)))))

(defun rembind-all-eq (l a)
  (declare (xargs :Guard (and (symbol-listp l)
			      (symbol-alistp a))))
  (cond ((endp l) a)
	(t (rembind-eq (car l) (rembind-all-eq (cdr l) a)))))

(defun rembind-all-equal (l a)
  (declare (xargs :Guard (and (true-listp l)
			      (alistp a))))
  (cond ((endp l) a)
	(t (rembind-equal (car l) (rembind-all-equal (cdr l) a)))))

(defun collect-bound (l a)
  "Collect the sublist of L bound in A."
  (declare (xargs :guard (and (eqlable-listp l)
			      (eqlable-alistp a))))
  (cond ((endp l) nil)
	((bound? (car l) a)
	 (cons (car l) (collect-bound (cdr l) a)))
	(t (collect-bound (cdr l) a))))

(defun collect-bound-eq (l a)
  "Collect the sublist of L bound in A."
  (declare (xargs :guard (and (symbol-listp l)
			      (symbol-alistp a))))
  (cond ((endp l) nil)
	((bound?-eq (car l) a)
	 (cons (car l) (collect-bound-eq (cdr l) a)))
	(t (collect-bound-eq (cdr l) a))))

(defun collect-bound-equal (l a)
  "Collect the sublist of L bound in A."
  (declare (xargs :guard (and (true-listp l)
			      (alistp a))))
  (cond ((endp l) nil)
	((bound?-equal (car l) a)
	 (cons (car l) (collect-bound-equal (cdr l) a)))
	(t (collect-bound-equal (cdr l) a))))

(defun bind-pairs (a1 a2)
  (declare (xargs :guard (and (eqlable-alistp a1)
			      (eqlable-alistp a2))))
  (cond ((endp a1) a2)
	(t (bind (caar a1) (cdar a1) (bind-pairs (cdr a1) a2)))))

(defun bind-pairs-eq (a1 a2)
  (declare (xargs :guard (and (symbol-alistp a1)
			      (symbol-alistp a2))))
  (cond ((endp a1) a2)
	(t (bind-eq (caar a1) (cdar a1) (bind-pairs-eq (cdr a1) a2)))))

(defun bind-pairs-equal (a1 a2)
  (declare (xargs :guard (and (alistp a1)
			      (alistp a2))))
  (cond ((endp a1) a2)
	(t (bind-equal (caar a1) (cdar a1) (bind-pairs-equal (cdr a1) a2)))))

(defun alist-compose-domain (dom a1 a2)
  "X is bound to Z in (ALIST-COMPOSE-DOMAIN DOM A1 A2) if X occurs in
   DOM, X is bound in A1, and there exists a Y such that
   (BINDING X A1) = Y, and (BINDING Y A2) = Z."
  (declare (xargs :guard (and (eqlable-listp dom)
			      (eqlable-alistp a1)
			      (eqlable-alistp a2))
		  :verify-guards nil))
  (cond ((endp dom) nil)
	(t (let ((pair1 (assoc (car dom) a1)))
	     (if pair1
		 (let ((pair2 (assoc (cdr pair1) a2)))
		   (if pair2
		       (bind (car dom) (cdr pair2)
				   (alist-compose-domain (cdr dom) a1 a2))
		     (alist-compose-domain (cdr dom) a1 a2)))
	       (alist-compose-domain (cdr dom) a1 a2))))))

(local (defthm alistp-alist-compose-domain
	 (implies (alistp a1)
		  (alistp (alist-compose-domain  dom a1 a2)))))

(local (defthm eqlable-alistp-alist-compose-domain
	 (implies (and (eqlable-listp dom)
		       (alistp a1))
		  (eqlable-alistp (alist-compose-domain  dom a1 a2)))))

(local (defthm eqlable-alistp-bind
	 (implies (and (eqlablep x)
		       (eqlable-alistp a))
		  (eqlable-alistp (bind x y a)))))

(local
 (defthm assoc-consp-or-nil
  (implies (alistp a)
	   (or (consp (assoc x a))
	       (equal (assoc x a) nil)))
  :rule-classes :type-prescription))

(verify-guards alist-compose-domain)

(defun alist-compose (a1 a2)
  "X is bound to Z in (ALIST-COMPOSE A1 A2) if X is bound
   in A1, and there exists a Y such that
  (BINDING X A1) = Y, and (BINDING Y A2) = Z."
  (declare (xargs :guard (and (eqlable-alistp a1)
			      (eqlable-alistp a2))))
  (alist-compose-domain (domain a1) a1 a2))


(defun alist-compose-domain-eq (dom a1 a2)
  "X is bound to Z in (ALIST-COMPOSE-DOMAIN DOM A1 A2) if X occurs in
   DOM, X is bound in A1, and there exists a Y such that
   (BINDING X A1) = Y, and (BINDING Y A2) = Z."
  (declare (xargs :guard (and (symbol-listp dom)
			      (symbol-alistp a1)
			      (symbol-alistp a2))
		  :verify-guards nil))
  (cond ((endp dom) nil)
	(t (let ((pair1 (assoc-eq (car dom) a1)))
	     (if pair1
		 (let ((pair2 (assoc-eq (cdr pair1) a2)))
		   (if pair2
		       (bind-eq (car dom) (cdr pair2)
				   (alist-compose-domain-eq (cdr dom) a1 a2))
		     (alist-compose-domain-eq (cdr dom) a1 a2)))
	       (alist-compose-domain-eq (cdr dom) a1 a2))))))

(local (defthm alistp-alist-compose-domain-eq
	 (implies (alistp a1)
		  (alistp (alist-compose-domain-eq  dom a1 a2)))))

(local (defthm symbol-alistp-alist-compose-domain-eq
	 (implies (and (symbol-listp dom)
		       (alistp a1))
		  (symbol-alistp (alist-compose-domain-eq  dom a1 a2)))))

(local (defthm symbol-alistp-bind-equal
	 (implies (and (symbolp x)
		       (symbol-alistp a))
		  (symbol-alistp (bind-equal x y a)))))

(verify-guards alist-compose-domain-eq)

(defun alist-compose-eq (a1 a2)
  "X is bound to Z in (ALIST-COMPOSE A1 A2) if X is bound
   in A1, and there exists a Y such that
  (BINDING X A1) = Y, and (BINDING Y A2) = Z."
  (declare (xargs :guard (and (symbol-alistp a1)
			      (symbol-alistp a2))))
  (alist-compose-domain-eq (domain a1) a1 a2))


(defun alist-compose-domain-equal (dom a1 a2)
  "X is bound to Z in (ALIST-COMPOSE-DOMAIN DOM A1 A2) if X occurs in
   DOM, X is bound in A1, and there exists a Y such that
   (BINDING X A1) = Y, and (BINDING Y A2) = Z."
  (declare (xargs :guard (and (true-listp dom)
			      (alistp a1)
			      (alistp a2))
		  :verify-guards nil))
  (cond ((endp dom) nil)
	(t (let ((pair1 (assoc-equal (car dom) a1)))
	     (if pair1
		 (let ((pair2 (assoc-equal (cdr pair1) a2)))
		   (if pair2
		       (bind-equal (car dom) (cdr pair2)
				   (alist-compose-domain-equal (cdr dom) a1 a2))
		     (alist-compose-domain-equal (cdr dom) a1 a2)))
	       (alist-compose-domain-equal (cdr dom) a1 a2))))))

(local (defthm alistp-alist-compose-domain-equal
	 (implies (alistp a1)
		  (alistp (alist-compose-domain-equal  dom a1 a2)))))

(local (defthm alistp-bind-equal
	 (implies (alistp a)
		  (alistp (bind-equal x y a)))))

(local
 (defthm assoc-equal-consp-or-nil
  (implies (alistp a)
	   (or (consp (assoc-equal x a))
	       (equal (assoc-equal x a) nil)))
  :rule-classes :type-prescription))

(verify-guards alist-compose-domain-equal)

(defun alist-compose-equal (a1 a2)
  "X is bound to Z in (ALIST-COMPOSE A1 A2) if X is bound
   in A1, and there exists a Y such that
  (BINDING X A1) = Y, and (BINDING Y A2) = Z."
  (declare (xargs :guard (and (alistp a1)
			      (alistp a2))))
  (alist-compose-domain-equal (domain a1) a1 a2))

(deftheory alist-defuns
  (set-difference-theories (current-theory :here)
			   (current-theory 'alist-defuns-section)))


