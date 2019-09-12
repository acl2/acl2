;;; defmul.lisp
;;; Definition of macros DEFMUL and DEFMUL-COMPONENTS, needed to define
;;; well-founded multiset relations induced by well-founded
;;; relations. It needs book "multiset.lisp"
;;; Last Revision: 19-09-00
;;;============================================================================

#| To certify this book:

(in-package "ACL2")

(defpkg "MUL" (union-eq *acl2-exports*
			       (union-eq
				*common-lisp-symbols-from-main-lisp-package*
				'(remove-one multiset-diff ctoa atoc))))


(certify-book "defmul" 1)

|#

;;; To use in your books, simply include it with (include-book "defmul")



(in-package "ACL2")

(include-book "multiset")

(set-verify-guards-eagerness 2)



;;; ****************************************************
;;; DEFINITION OF THE DEFMUL AND DEFMUL-COMPONENTS MACRO
;;; ****************************************************

;;; Given "rel" a well-founded relation on a set A, we generate
;;; the events needed to extend this relation on the set of finite
;;; multisets over A.



;;; ============================================================================
;;; 1. Definition defmul-components
;;; ============================================================================



;;; First: Given "rel" a well-founded relation on a set A, we need to know the
;;;   components needed to extend this relation on the set of finite multisets
;;;   over A:
;;;  - "rel": The well-founded relation defined on A.
;;;  - "mp": The meaure property defining the set A.
;;;  - "fn": The embedding justifying well-foundedness of "rel".
;;;  - "theorem": The theorem name with  rule class
;;;    "well-founded-relation" associated with "rel".
;;;  - "varx", "vary": The variables used in the "theorem".


(defun search-well-founded-relation-theorem (world theorem)
  (declare (xargs :mode :program))
  (getprop theorem 'theorem
	   '(error theorem-not-found)
	   'current-acl2-world
	   world))

(defun destructure-aux-well-founded-relation-rule (term)
  (declare (xargs :mode :program))

  (case-match term

	      (('IF ('IMPLIES (mp x) ('O-P (fn x)))
		    ('IMPLIES ('IF (mp x)
				   ('IF (mp y) (rel x y) ''NIL)
				   ''NIL)
			      ('O< (fn x) (fn y)))
		    ''NIL)
	       (mv mp fn rel x y))

	      (('IF ('O-P (fn x))
		    ('IMPLIES (rel x y)
			      ('O< (fn x) (fn y)))
		    ''NIL)
	       (mv t fn rel x y))

	      (& (mv nil nil nil nil nil))))

(defun components-of-well-founded-relation-rule-fn (rel world)
  (declare (xargs :mode :program))
  (if (eq rel 'o<)
      (list rel nil 'o-p 'o<-fn nil nil)
      (let ((name
	     (cadddr (assoc-eq rel
			       (global-val
				'well-founded-relation-alist world)))))
	(mv-let (nmp nfn nrel nx ny)
		(destructure-aux-well-founded-relation-rule
		 (search-well-founded-relation-theorem world name))
		(list nrel name nmp nfn nx ny)))))

(defun this-symbol-list-is-not-new (symbol-list world)
  (declare (xargs :mode :program))
  (if (endp symbol-list)
      nil
      (if (new-namep (car symbol-list) world)
	  (this-symbol-list-is-not-new (cdr symbol-list) world)
	  (cons (car symbol-list)
		(this-symbol-list-is-not-new (cdr symbol-list) world)))))

(defun packn-in-pkg (lst pkg-witness)
  (declare (xargs :mode :program))
  (intern-in-package-of-symbol (coerce (packn1 lst) 'string) pkg-witness))

(defun defmul-symbols-not-new (list prefix world)
  (declare (xargs :mode :program))
  (let ((n-rel (car list))
	(theorem (cadr list))
	(n-mp (caddr list))
	(n-fn (cadddr list)))
    (let ((rel-bigg
	   (packn-in-pkg (append prefix
				 (list "EXISTS-" n-rel "-BIGGER"))
			 n-rel))
	  (for-exis
	   (packn-in-pkg (append prefix
				 (list "FORALL-EXISTS-" n-rel "-BIGGER"))
			 n-rel))
	  (m-rel
	   (packn-in-pkg (append prefix (list "MUL-" n-rel))
			 n-rel))
	  (map-fn
	   (packn-in-pkg (append prefix (list "MAP-" n-fn "-E0-ORD"))
			 n-fn))
	  (map-fn-op
	   (packn-in-pkg (append prefix (list "MAP-" n-fn "-O-P"))
			 n-fn))
	  (new-mp
	   (packn-in-pkg (append prefix (list n-mp "-TRUE-LISTP"))
			 n-mp))
	  (new-mp-multiset-diff
	   (packn-in-pkg
	    (append prefix (list n-mp "-TRUE-LISTP-MULTISET-DIFF"))
	    n-mp))
	  (cong-name1
	   (packn-in-pkg
	    (append prefix (list "EQUAL-SET-IMPLIES-IFF-FORALL-EXISTS-"
				 n-rel "-BIGGER-1"))
	    n-rel))
	  (cong-name2
	   (packn-in-pkg
	    (append prefix (list "EQUAL-SET-IMPLIES-IFF-FORALL-EXISTS-"
				 n-rel "-BIGGER-2"))
	    n-rel))
	  (n-rewr
	   (packn-in-pkg (append prefix (list theorem "-REWRITE"))
			 n-rel))
	  (mult-th
	   (packn-in-pkg
	    (append prefix
		    (list "MULTISET-EXTENSION-OF-" n-rel "-WELL-FOUNDED"))
	    n-rel)))
      (this-symbol-list-is-not-new
       (list rel-bigg for-exis m-rel map-fn map-fn-op new-mp
	     new-mp-multiset-diff cong-name1 cong-name2 n-rewr mult-th)
       world))))

(defmacro defmul-components (rel &key prefix)
  `(let ((n-rel
	  (car (assoc-eq (quote ,rel)
			 (global-val
			  'well-founded-relation-alist (w state))))))
     (if (eq n-rel nil)
	 (er soft 'defmul-components
	     "The symbol ~x0 is not a well-founded relation. ~
              See :DOC well-founded-relation."
	     (quote ,rel))
         (let ((list (defmul-symbols-not-new
		       (components-of-well-founded-relation-rule-fn
			(quote ,rel) (w state))
		       (if (quote ,prefix) (list (quote ,prefix) "-") nil)
		       (w state))))
	   (if list
	       (if (quote ,prefix)
		   (mv-let
		    (val state)
		    (fmx "~%~%WARNING: The ~#0~[symbol~/symbols~] ~*1 ~
                       ~#0~[is~/are~] defined yet. Perhaps you must ~
                       use the :PREFIX option with a value different from ~
                       ~x2. ~%~%~
                       The list of components is: ~%"
			 (if (= (length list) 1) 0 1)
			 (list "Empty list" "~x*" "~x* and " "~x*, " list)
			 (quote ,prefix))
		    (declare (ignore val))
		    (mv nil (components-of-well-founded-relation-rule-fn
			     (quote ,rel) (w state)) state))
		   (mv-let
		    (val state)
		    (fmx "~%~%WARNING: The ~#0~[symbol~/symbols~] ~*1 ~
                       ~#0~[is~/are~] defined yet. Perhaps you must ~
                       use the :PREFIX option. ~%~%~
                       The list of components is: ~%"
			 (if (= (length list) 1) 0 1)
			 (list "Empty list" "~x*" "~x* and " "~x*, " list))
		    (declare (ignore val))
		    (mv nil (components-of-well-founded-relation-rule-fn
			     (quote ,rel) (w state)) state)))
	       (mv-let
		(val state)
		(fmx "~%~%The list of components is: ~%")
		(declare (ignore val))
		(mv nil (components-of-well-founded-relation-rule-fn
			 (quote ,rel) (w state)) state)))))))


;;; ============================================================================
;;; 2. Definition defmul
;;; ============================================================================


;;; Given "n-rel" a well-founded relation on a set A, and given the
;;;   components needed to extend this relation to the set of finite multisets
;;;   over A:
;;;  - "n-rel": The well-founded relation defined on A.
;;;  - "n-mp": The measure property defining the set A.
;;;  - "n-fn": The embedding justifying the well-foundedness of "rel".
;;;  - "theorem": The theorem name with rule class
;;;     "well-founded-relation" associated with "rel".
;;;  - "varx", "vary": The variables used in the "theorem".
;;; We build:
;;;  - "EXISTS-n-rel-BIGGER": Needed for "MUL-n-rel".
;;;  - "FORALL-EXISTS-n-rel-BIGGER": Needed for "MUL-n-rel".
;;;  - "MUL-n-rel": Well-founded relation on finite multisets over A.
;;;  - "MAP-n-fn-E0-ORD": The embedding justifying the well-foundedness of
;;;    "MUL-n-rel".
;;;  - "n-mp-TRUE-LISTP": The measure property defining the finite
;;;    multisets over A.
;;;  - "theorem-REWRITE": Well-founded relation theorem associated with
;;;    "n-rel", but now as a rewriting rule.
;;;  - "n-mp-TRUE-LISTP-MULTISET-DIFF": Needed for the guards verification of
;;;    "MUL-n-rel".
;;;  - "MULTISET-EXTENSION-OF-n-rel-WELL-FOUNDED": Well-founded relation
;;;    theorem associated with "MUL-n-rel".
;;;  - "EQUAL-SET-IMPLIES-IFF-FORALL-EXISTS-n-rel-BIGGER-1" and
;;;    "EQUAL-SET-IMPLIES-IFF-FORALL-EXISTS-n-rel-BIGGER-2": Some useful
;;;    congruences.


;;; We have to distinguish three cases: The two general forms recognized as
;;;   well-founded relations (the first with an explicit property "mp" and the
;;;   second with this property equal to "t"). The third case is for the
;;;   "e0-ord-<" relation (the primitive well-founded relation over
;;;   "e0-ordinalp").

(defun defmul-events-rel (prefix v-g n-rel n-mp)
  (declare (xargs :mode :program))
  (let ((rel-bigg
	 (packn-in-pkg (append prefix (list "EXISTS-" n-rel "-BIGGER"))
		       n-rel))
	(for-exis
	 (packn-in-pkg (append prefix (list "FORALL-EXISTS-" n-rel "-BIGGER"))
		       n-rel))
	(m-rel
	 (packn-in-pkg (append prefix (list "MUL-" n-rel))
		       n-rel))
	(new-mp
	 (if (eq n-mp t)
	     'TRUE-LISTP
	     (packn-in-pkg (append prefix (list n-mp "-TRUE-LISTP"))
			   n-mp)))
	)
    (list

     `(defun ,rel-bigg (x l)        ; exists-rel-bigger
	(declare (xargs :guard ,(if (eq n-mp t)
				    `(,new-mp l)
				    `(and (,n-mp x) (,new-mp l)))
			:guard-hints
			(("Goal" :hands-off ,(if (eq n-mp t)
						 `(,n-rel)
						 `(,n-rel ,n-mp))))
			:verify-guards ,v-g))
	(cond ((atom l) nil)
	      ((,n-rel x (car l)) t)
	      (t (,rel-bigg x (cdr l)))))

     `(defun ,for-exis (l m)        ; forall-exists-rel-bigger
	(declare (xargs :guard (and (,new-mp l)
				    (,new-mp m))
			:guard-hints
			(("Goal" :hands-off ,(if (eq n-mp t)
						 `()
						 `(,n-mp))))
			:verify-guards ,v-g))
	(if (atom l)
	    t
	    (and (,rel-bigg (car l) m)
		 (,for-exis (cdr l) m))))

     `(defun ,m-rel (n m)           ; mul-rel
	(declare (xargs :guard (and (,new-mp n)
				    (,new-mp m))
			:verify-guards nil))
	(let ((m-n (multiset-diff m n))
	      (n-m (multiset-diff n m)))
	  (and (consp m-n) (,for-exis n-m m-n))))

     )))

(defun defmul-events-fn (prefix v-g n-fn n-mp)
  (declare (xargs :mode :program))
  (let ((map-fn
	 (packn-in-pkg (append prefix (list "MAP-" n-fn "-E0-ORD"))
		       n-fn))
	(map-fn-op
	 (packn-in-pkg (append prefix (list "MAP-" n-fn "-O-P"))
		       n-fn))
	(new-mp
	 (if (eq n-mp t)
	     'TRUE-LISTP
	     (packn-in-pkg (append prefix (list n-mp "-TRUE-LISTP"))
			   n-mp)))
	)
    (list

     `(defun ,map-fn (l)            ; map-fn-e0-ord
	(declare (xargs :guard (,new-mp l)
			:guard-hints
			(("Goal" :hands-off ,(if (eq n-mp t)
						 `()
						 `(,n-mp))))
			:verify-guards ,v-g))
	(if (consp l)
	    (MUL::insert-e0-ord-<
	     (MUL::add1-if-integer
	      ,(if (eq n-fn 'o<-fn)
		   (list 'ctoa '(car l))
		 (list 'ctoa (list n-fn '(car l)))))
	     (,map-fn (cdr l)))
	    0))

     `(defun ,map-fn-op (l)		; map-fn-op
	(declare (xargs :verify-guards nil))
	(atoc (,map-fn l)))

     )))

(defun defmul-events-mp (prefix v-g n-mp)
  (declare (xargs :mode :program))
  (let ((new-mp
	 (packn-in-pkg (append prefix (list n-mp "-TRUE-LISTP"))
		       n-mp))
	)
    (list

     `(defun ,new-mp (l)          ; mp-true-listp
	(declare (xargs :verify-guards ,v-g))
	(if (atom l)
	    (equal l nil)
	    (and (,n-mp (car l))
		 (,new-mp (cdr l)))))

     )))

(defun defmul-events-theorems-t (prefix rule-classes
					theorem n-fn n-rel varx vary)
  (declare (xargs :mode :program))
  (let ((rel-bigg
	 (packn-in-pkg (append prefix (list "EXISTS-" n-rel "-BIGGER"))
		       n-rel))
	(for-exis
	 (packn-in-pkg (append prefix (list "FORALL-EXISTS-" n-rel "-BIGGER"))
		       n-rel))
	(m-rel
	 (packn-in-pkg (append prefix (list "MUL-" n-rel))
		       n-rel))
	(map-fn
	 (packn-in-pkg (append prefix (list "MAP-" n-fn "-E0-ORD"))
		       n-fn))
	(map-fn-op
	 (packn-in-pkg (append prefix (list "MAP-" n-fn "-O-P"))
		       n-fn))
	(n-rewr
	 (packn-in-pkg (append prefix (list theorem "-REWRITE"))
		       n-rel))
	(cong-name1
	 (packn-in-pkg
	  (append prefix (list "EQUAL-SET-IMPLIES-IFF-FORALL-EXISTS-"
			       n-rel "-BIGGER-1"))
	  n-rel))
	(cong-name2
	 (packn-in-pkg
	  (append prefix (list "EQUAL-SET-IMPLIES-IFF-FORALL-EXISTS-"
			       n-rel "-BIGGER-2"))
	  n-rel))
	(mult-th
	 (packn-in-pkg
	  (append prefix (list "MULTISET-EXTENSION-OF-" n-rel "-WELL-FOUNDED"))
	  n-rel))
	)

    (list

     `(local (defthm ,n-rewr
	       (and (o-p (,n-fn ,varx))
		    (implies (,n-rel ,varx ,vary)
			     (o< (,n-fn ,varx) (,n-fn ,vary))))
	       :rule-classes :rewrite
	       :hints (("Goal" :use ,theorem))))

     `(defthm ,mult-th
	(and (implies (true-listp x) (o-p (,map-fn-op x)))
	     (implies (and (true-listp x)
			   (true-listp y)
			   (,m-rel x y))
	       (o< (,map-fn-op x) (,map-fn-op y))))
	:rule-classes ,(extend-rule-classes :WELL-FOUNDED-RELATION
					    rule-classes)
	:hints (("Goal"
		 :use ((:functional-instance
			(:instance
			 MUL::multiset-extension-of-rel-well-founded
			 (MUL::x x) (MUL::y y))
			(MUL::mp-true-listp true-listp)
			(MUL::exists-rel-bigger ,rel-bigg)
			(MUL::forall-exists-rel-bigger ,for-exis)
			(MUL::mul-rel ,m-rel)
			(MUL::map-fn-e0-ord ,map-fn)
			(MUL::map-fn-o-p ,map-fn-op)
			(MUL::rel ,n-rel)
			(MUL::mp (lambda (x) t))
			(MUL::fn ,n-fn)))
		 :hands-off (,n-fn ,n-rel))))

     `(defcong MUL::equal-set iff (,for-exis l m) 1
        :package :legacy
	:event-name ,cong-name1
	:hints (("Goal"
		 :use ((:functional-instance
			(:instance
			 MUL::equal-set-implies-iff-forall-exists-rel-bigger-1
			 (MUL::l l) (MUL::m m))
			(MUL::fn ,n-fn)
			(MUL::mp (lambda (x) t))
			(MUL::rel ,n-rel)
			(MUL::exists-rel-bigger ,rel-bigg)
			(MUL::forall-exists-rel-bigger ,for-exis)))
		 :hands-off (,n-fn ,n-rel))))

     `(defcong MUL::equal-set iff (,for-exis l m) 2
        :package :legacy
	:event-name ,cong-name2
	:hints (("Goal"
		 :use ((:functional-instance
			(:instance
			 MUL::equal-set-implies-iff-forall-exists-rel-bigger-2
			 (MUL::l l) (MUL::m m))
			(MUL::fn ,n-fn)
			(MUL::mp (lambda (x) t))
			(MUL::rel ,n-rel)
			(MUL::exists-rel-bigger ,rel-bigg)
			(MUL::forall-exists-rel-bigger ,for-exis)))
		 :hands-off (,n-fn ,n-rel))))

     )))

(defun defmul-events-theorems-mp (prefix rule-classes
					 theorem n-mp n-fn n-rel varx vary)
  (declare (xargs :mode :program))
  (let ((rel-bigg
	 (packn-in-pkg (append prefix (list "EXISTS-" n-rel "-BIGGER"))
		       n-rel))
	(for-exis
	 (packn-in-pkg (append prefix (list "FORALL-EXISTS-" n-rel "-BIGGER"))
		       n-rel))
	(m-rel
	 (packn-in-pkg (append prefix (list "MUL-" n-rel))
		       n-rel))
	(map-fn
	 (packn-in-pkg (append prefix (list "MAP-" n-fn "-E0-ORD"))
		       n-fn))
	(map-fn-op
	 (packn-in-pkg (append prefix (list "MAP-" n-fn "-O-P"))
		       n-fn))
	(new-mp
	 (packn-in-pkg (append prefix (list n-mp "-TRUE-LISTP"))
		       n-mp))
	(n-rewr
	 (packn-in-pkg (append prefix (list theorem "-REWRITE"))
		       n-rel))
	(new-mp-multiset-diff
	 (packn-in-pkg (append prefix (list n-mp "-TRUE-LISTP-MULTISET-DIFF"))
		       n-mp))
	(cong-name1
	 (packn-in-pkg
	  (append prefix (list "EQUAL-SET-IMPLIES-IFF-FORALL-EXISTS-"
			       n-rel "-BIGGER-1"))
	  n-rel))
	(cong-name2
	 (packn-in-pkg
	  (append prefix (list "EQUAL-SET-IMPLIES-IFF-FORALL-EXISTS-"
			       n-rel "-BIGGER-2"))
	  n-rel))
	(mult-th
	 (packn-in-pkg
	  (append prefix (list "MULTISET-EXTENSION-OF-" n-rel "-WELL-FOUNDED"))
	  n-rel))
	)

    (list

     `(local (defthm ,n-rewr
	       (and (implies (,n-mp ,varx) (o-p (,n-fn ,varx)))
		    (implies (and (,n-mp ,varx)
				  (,n-mp ,vary)
				  (,n-rel ,varx ,vary))
		      (o< (,n-fn ,varx) (,n-fn ,vary))))
	       :rule-classes :rewrite
	       :hints (("Goal" :use ,theorem))))

     `(defthm ,new-mp-multiset-diff
	(implies (,new-mp m)
	  (,new-mp (multiset-diff m n)))
	:hints (("Goal"
		 :use ((:functional-instance
			(:instance
			 MUL::mp-true-listp-multiset-diff
			 (MUL::m m) (MUL::n n))
			(MUL::mp-true-listp ,new-mp)
			(MUL::mp ,n-mp)
			(MUL::fn ,n-fn)
			(MUL::rel ,n-rel)))
		 :hands-off (,n-mp ,n-fn ,n-rel))))

     `(defthm ,mult-th
	(and (implies (,new-mp x) (o-p (,map-fn-op x)))
	     (implies (and (,new-mp x)
			   (,new-mp y)
			   (,m-rel x y))
	       (o< (,map-fn-op x) (,map-fn-op y))))
	:rule-classes ,(extend-rule-classes :WELL-FOUNDED-RELATION
					    rule-classes)
	:hints (("Goal"
		 :use ((:functional-instance
			(:instance
			 MUL::multiset-extension-of-rel-well-founded
			 (MUL::x x) (MUL::y y))
			(MUL::mp-true-listp ,new-mp)
			(MUL::exists-rel-bigger ,rel-bigg)
			(MUL::forall-exists-rel-bigger ,for-exis)
			(MUL::mul-rel ,m-rel)
			(MUL::map-fn-e0-ord ,map-fn)
			(MUL::map-fn-o-p ,map-fn-op)
			(MUL::rel ,n-rel)
			(MUL::mp ,n-mp)
			(MUL::fn ,n-fn)))
		 :hands-off (,n-mp ,n-fn ,n-rel))))

     `(defcong MUL::equal-set iff (,for-exis l m) 1
        :package :legacy
	:event-name ,cong-name1
	:hints (("Goal"
		 :use ((:functional-instance
			(:instance
			 MUL::equal-set-implies-iff-forall-exists-rel-bigger-1
			 (MUL::l l) (MUL::m m))
			(MUL::fn ,n-fn)
			(MUL::mp ,n-mp)
			(MUL::rel ,n-rel)
			(MUL::exists-rel-bigger ,rel-bigg)
			(MUL::forall-exists-rel-bigger ,for-exis)))
		 :hands-off (,n-mp ,n-fn ,n-rel))))

     `(defcong MUL::equal-set iff (,for-exis l m) 2
        :package :legacy
	:event-name ,cong-name2
	:hints (("Goal"
		 :use ((:functional-instance
			(:instance
			 MUL::equal-set-implies-iff-forall-exists-rel-bigger-2
			 (MUL::l l) (MUL::m m))
			(MUL::fn ,n-fn)
			(MUL::mp ,n-mp)
			(MUL::rel ,n-rel)
			(MUL::exists-rel-bigger ,rel-bigg)
			(MUL::forall-exists-rel-bigger ,for-exis)))
		 :hands-off (,n-mp ,n-fn ,n-rel))))

     )))

(defun defmul-events-theorems-ord (prefix rule-classes
					  n-mp n-fn n-rel)
  (declare (xargs :mode :program))
  (let ((rel-bigg
	 (packn-in-pkg (append prefix (list "EXISTS-" n-rel "-BIGGER"))
		       n-rel))
	(for-exis
	 (packn-in-pkg (append prefix (list "FORALL-EXISTS-" n-rel "-BIGGER"))
		       n-rel))
	(m-rel
	 (packn-in-pkg (append prefix (list "MUL-" n-rel))
		       n-rel))
	(map-fn
	 (packn-in-pkg (append prefix (list "MAP-" n-fn "-E0-ORD"))
		       n-fn))
	(map-fn-op
	 (packn-in-pkg (append prefix (list "MAP-" n-fn "-O-P"))
		       n-fn))
	(new-mp
	 (packn-in-pkg (append prefix (list n-mp "-TRUE-LISTP"))
		       n-mp))
	(new-mp-multiset-diff
	 (packn-in-pkg (append prefix (list n-mp "-TRUE-LISTP-MULTISET-DIFF"))
		       n-mp))
	(cong-name1
	 (packn-in-pkg
	  (append prefix (list "EQUAL-SET-IMPLIES-IFF-FORALL-EXISTS-"
			       n-rel "-BIGGER-1"))
	  n-rel))
	(cong-name2
	 (packn-in-pkg
	  (append prefix (list "EQUAL-SET-IMPLIES-IFF-FORALL-EXISTS-"
			       n-rel "-BIGGER-2"))
	  n-rel))
	(mult-th
	 (packn-in-pkg
	  (append prefix (list "MULTISET-EXTENSION-OF-" n-rel "-WELL-FOUNDED"))
	  n-rel))
	)

    (list

     `(defthm ,new-mp-multiset-diff
	(implies (,new-mp m)
	  (,new-mp (multiset-diff m n)))
	:hints (("Goal"
		 :use ((:functional-instance
			(:instance
			 MUL::mp-true-listp-multiset-diff
			 (MUL::m m) (MUL::n n))
			(MUL::mp-true-listp ,new-mp)
			(MUL::mp ,n-mp)
			(MUL::fn (lambda (x) x))
			(MUL::rel ,n-rel)))
		 :hands-off (,n-mp ,n-rel))))

     `(defthm ,mult-th
	(and (implies (,new-mp x) (o-p (,map-fn-op x)))
	     (implies (and (,new-mp x)
			   (,new-mp y)
			   (,m-rel x y))
	       (o< (,map-fn-op x) (,map-fn-op y))))
	:rule-classes ,(extend-rule-classes :WELL-FOUNDED-RELATION
					    rule-classes)
	:hints (("Goal"
		 :use ((:functional-instance
			(:instance
			 MUL::multiset-extension-of-rel-well-founded
			 (MUL::x x) (MUL::y y))
			(MUL::mp-true-listp ,new-mp)
			(MUL::exists-rel-bigger ,rel-bigg)
			(MUL::forall-exists-rel-bigger ,for-exis)
			(MUL::mul-rel ,m-rel)
			(MUL::map-fn-e0-ord ,map-fn)
			(MUL::map-fn-o-p ,map-fn-op)
			(MUL::rel ,n-rel)
			(MUL::mp ,n-mp)
			(MUL::fn (lambda (x) x)))))))

     `(defcong MUL::equal-set iff (,for-exis l m) 1
        :package :legacy
	:event-name ,cong-name1
	:hints (("Goal"
		 :use ((:functional-instance
			(:instance
			 MUL::equal-set-implies-iff-forall-exists-rel-bigger-1
			 (MUL::l l) (MUL::m m))
			(MUL::fn (lambda (x) x))
			(MUL::mp ,n-mp)
			(MUL::rel ,n-rel)
			(MUL::exists-rel-bigger ,rel-bigg)
			(MUL::forall-exists-rel-bigger ,for-exis))))))

     `(defcong MUL::equal-set iff (,for-exis l m) 2
        :package :legacy
	:event-name ,cong-name2
	:hints (("Goal"
		 :use ((:functional-instance
			(:instance
			 MUL::equal-set-implies-iff-forall-exists-rel-bigger-2
			 (MUL::l l) (MUL::m m))
			(MUL::fn (lambda (x) x))
			(MUL::mp ,n-mp)
			(MUL::rel ,n-rel)
			(MUL::exists-rel-bigger ,rel-bigg)
			(MUL::forall-exists-rel-bigger ,for-exis))))))

     )))

(defun defmul-events (list prefix verify-guards rule-classes)
  (declare (xargs :mode :program))
  (let ((n-rel (car list))
	(m-rel (packn-in-pkg (append prefix (list "MUL-" (car list)))
			     (car list)))
	(theorem (cadr list))
	(n-mp (caddr list))
	(n-fn (cadddr list))
	(varx (car (cddddr list)))
	(vary (cadr (cddddr list)))
	(l-prefix (if prefix (list prefix "-") nil)))
    (append
     (if (eq n-mp t)
	 nil
	 (defmul-events-mp l-prefix verify-guards n-mp))
     (defmul-events-rel l-prefix verify-guards n-rel n-mp)
     (defmul-events-fn l-prefix verify-guards n-fn n-mp)
     (cond ((eq n-mp t)
	    (defmul-events-theorems-t l-prefix rule-classes
	      theorem n-fn n-rel varx vary))
	   ((eq n-mp 'o-p)
	    (defmul-events-theorems-ord l-prefix rule-classes
	      n-mp n-fn n-rel))
	   (t
	    (defmul-events-theorems-mp l-prefix rule-classes
	      theorem n-mp n-fn n-rel varx vary)))
     (if (eq verify-guards t)
	 (list `(verify-guards ,m-rel))
	 nil))))

(defmacro defmul (list &key prefix
		       (verify-guards 'nil)
		       (rule-classes '(:WELL-FOUNDED-RELATION)))
  `(encapsulate
    ()
    ,@(defmul-events list prefix verify-guards rule-classes)))

;;; ============================================================================
;;; 3. Documentation
;;; ============================================================================


;;; The following legacy doc string was replaced Nov. 2014 by the
;;; auto-generated defxdoc form below.
; (defdoc defmul
; ":Doc-section defmul
; extends a well-founded relation <rel> to multisets.~/~/
; How to use: To extend a well-founded relation <rel> to multisets we need
;   know:
;   - <rel>: The well-founded relation defined on A.
;   - <theorem>: The theorem with rule class \"well-founded-relation\"
;     associated with <rel>.
;   - <mp>: The measure property defining the set A.
;   - <fn>: The embedding justifying the well-foundedness of <rel>.
;   - <varx>, <vary>: The variables used in the <theorem>.
;   and eval the \"defmul\" macro with the list of these components:
;
;   (defmul (<rel> <theorem> <mp> <fn> <varx> <vary>))
;
; The main non-local events generated by this macro call are:
;
;   - the definitions needed for the multiset relation induced by <rel>:
;     functions exists-<rel>-bigger, forall-exists-<rel>-bigger and
;     mul-<rel>.
;   - the definition of the multiset measure property, <mp>-true-listp.
;   - the definition of mp-<fn>-e0-ord, the embedding function from
;     multisets to ordinals.
;   - the well-foundedness theorem for mul-<rel>, named
;     multiset-extension-of-<rel>-well-founded.
;
; To see the complete list of generated events use :trans1 on a defmul call.
;
; We expect defmul to work without assistance from the user. After the
; above call to defmul, the function mul-<rel> is defined as a
; well-founded relation on multisets of elements satisfying the property
; <mp>, induced by the well-founded relation <rel>. From
; this moment on, mul-<rel> can be used in the admissibility test
; for recursive functions to show that the recursion terminates.
;
;
; This macro has three optionals arguments:
;   :prefix <prefix> : With this argument we can use <prefix> as a prefix for
;     the names of the events builded.
;   :rule-classes <classes> : With this argument we can propose <classes> as
;     additional rule-classes for the well-founded relation theorem
;     associated with the multiset extension. The default value is
;     :well-founded-relation.
;   :verify-guards <expr> : The value of <expr> must be T or NIL. With this
;     argument we can decide when the guards of the functions builded must be
;     verified on definition time.
;
; To know the list of names that we need to supply to a  \"defmul\" call, we
;   have developed a tool to look up the Acl2 \"world\" and print that list:
;
;   (defmul-components <rel>)
;
; This is only an informative tool, not a event. This macro looks up the Acl2
;   \"world\", and informs if some symbols (those that the \"defmul\" macro
;   builds) have been already defined. As the \"defmul\" macro, has one
;   optional argument to propose a prefix:
;   :prefix <prefix> : With this argument we can use <prefix> as a prefix for
;     the names of the events builded.
;
; An example:
;
;   (encapsulate
;    ((my-mp (v) booleanp)
;     (my-rel (v w) booleanp)
;     (my-fn (v) e0-ordinalp))
;
;    (local (defun my-mp (v) (declare (ignore v)) nil))
;    (local (defun my-rel (v w) (declare (ignore v w)) nil))
;    (local (defun my-fn (v) (declare (ignore v)) 1))
;
;    (defthm my-rel-well-founded-relation
;      (and (implies (my-mp v) (e0-ordinalp (my-fn v)))
;   	   (implies (and (my-mp v)
;   			 (my-mp w)
;   			 (my-rel v w))
;   	     (e0-ord-< (my-fn v) (my-fn w))))
;      :rule-classes :well-founded-relation)
;
;    (defun map-my-fn-e0-ord (l)
;      l))
;
;   ; (defmul-components my-rel)
;   ; => WARNING: The symbol MAP-MY-FN-E0-ORD is defined yet. Perhaps you must
;   ;    use the :PREFIX option.
;   ;
;   ;    The list of components is:
;   ;     (MY-REL MY-REL-WELL-FOUNDED-RELATION MY-MP MY-FN V W)
;   ;
;   ; (defmul-components my-rel :prefix new)
;   ; => The list of components is:
;   ;     (MY-REL MY-REL-WELL-FOUNDED-RELATION MY-MP MY-FN V W)
;
;   (defmul (MY-REL MY-REL-WELL-FOUNDED-RELATION MY-MP MY-FN V W)
;     :prefix new :rule-classes :rewrite)
; ~/")

(include-book "xdoc/top" :dir :system)

; Note: Avoided using meta-x fix to format the following, since it is easier
; for a human to read this way.
(defxdoc defmul
  :parents (defmul)
  :short "Extends a well-founded relation &lt;rel&gt; to multisets."
  :long  "<p>How to use: To extend a well-founded relation &lt;rel&gt; to multisets we need
   know:
   - &lt;rel&gt;: The well-founded relation defined on A.
   - &lt;theorem&gt;: The theorem with rule class \"well-founded-relation\"
     associated with &lt;rel&gt;.
   - &lt;mp&gt;: The measure property defining the set A.
   - &lt;fn&gt;: The embedding justifying the well-foundedness of &lt;rel&gt;.
   - &lt;varx&gt;, &lt;vary&gt;: The variables used in the &lt;theorem&gt;.
   and eval the \"defmul\" macro with the list of these components:</p>

 <p>(defmul (&lt;rel&gt; &lt;theorem&gt; &lt;mp&gt; &lt;fn&gt; &lt;varx&gt; &lt;vary&gt;))</p>

 <p>The main non-local events generated by this macro call are:</p>

 <p>- the definitions needed for the multiset relation induced by &lt;rel&gt;:
     functions exists-&lt;rel&gt;-bigger, forall-exists-&lt;rel&gt;-bigger and
     mul-&lt;rel&gt;.
   - the definition of the multiset measure property, &lt;mp&gt;-true-listp.
   - the definition of mp-&lt;fn&gt;-e0-ord, the embedding function from
     multisets to ordinals.
   - the well-foundedness theorem for mul-&lt;rel&gt;, named
     multiset-extension-of-&lt;rel&gt;-well-founded.</p>

 <p>To see the complete list of generated events use :trans1 on a defmul call.</p>

 <p>We expect defmul to work without assistance from the user. After the
 above call to defmul, the function mul-&lt;rel&gt; is defined as a
 well-founded relation on multisets of elements satisfying the property
 &lt;mp&gt;, induced by the well-founded relation &lt;rel&gt;. From
 this moment on, mul-&lt;rel&gt; can be used in the admissibility test
 for recursive functions to show that the recursion terminates.</p>

 <p>This macro has three optionals arguments:
   :prefix &lt;prefix&gt; : With this argument we can use &lt;prefix&gt; as a prefix for
     the names of the events builded.
   :rule-classes &lt;classes&gt; : With this argument we can propose &lt;classes&gt; as
     additional rule-classes for the well-founded relation theorem
     associated with the multiset extension. The default value is
     :well-founded-relation.
   :verify-guards &lt;expr&gt; : The value of &lt;expr&gt; must be T or NIL. With this
     argument we can decide when the guards of the functions builded must be
     verified on definition time. </p>

 <p>To know the list of names that we need to supply to a  \"defmul\" call, we
   have developed a tool to look up the Acl2 \"world\" and print that list:</p>

 <p>(defmul-components &lt;rel&gt;)</p>

 <p>This is only an informative tool, not a event. This macro looks up the Acl2
   \"world\", and informs if some symbols (those that the \"defmul\" macro
   builds) have been already defined. As the \"defmul\" macro, has one
   optional argument to propose a prefix:
   :prefix &lt;prefix&gt; : With this argument we can use &lt;prefix&gt; as a prefix for
     the names of the events builded.</p>

 <p>An example:</p>

 <p>(encapsulate
    ((my-mp (v) booleanp)
     (my-rel (v w) booleanp)
     (my-fn (v) e0-ordinalp))

    (local (defun my-mp (v) (declare (ignore v)) nil))
    (local (defun my-rel (v w) (declare (ignore v w)) nil))
    (local (defun my-fn (v) (declare (ignore v)) 1))

    (defthm my-rel-well-founded-relation
      (and (implies (my-mp v) (e0-ordinalp (my-fn v)))
   	   (implies (and (my-mp v)
   			 (my-mp w)
   			 (my-rel v w))
   	     (e0-ord-&lt; (my-fn v) (my-fn w))))
      :rule-classes :well-founded-relation)

    (defun map-my-fn-e0-ord (l)
      l))

   ; (defmul-components my-rel)
   ; =&gt; WARNING: The symbol MAP-MY-FN-E0-ORD is defined yet. Perhaps you must
   ;    use the :PREFIX option.
   ;
   ;    The list of components is:
   ;     (MY-REL MY-REL-WELL-FOUNDED-RELATION MY-MP MY-FN V W)
   ;
   ; (defmul-components my-rel :prefix new)
   ; =&gt; The list of components is:
   ;     (MY-REL MY-REL-WELL-FOUNDED-RELATION MY-MP MY-FN V W)

   (defmul (MY-REL MY-REL-WELL-FOUNDED-RELATION MY-MP MY-FN V W)
     :prefix new :rule-classes :rewrite)

 </p>")
