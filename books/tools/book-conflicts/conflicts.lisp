(in-package "ACL2")

;; The (analyze-files flist state) function admitted at the bottom of
;; this file analyzes a list of bookdata files and prints out a
;; summary of symbol name conflicts.  The symbol conflicts are of the
;; form:
;;
;; (pkg-symbol-name-listp . book-list)
;;
;; Where book-list is a list of paths to the offending books and
;; pkg-symbol-name-listp is an association list with package names as
;; keys and symbol name lists as values.
;;
;; For example, the conflict:
;;
;; ((("STD" "M0-EXEC" "M0-EXEC-REMOVAL"
;;          "M0-OF-LIST-FIX" "M1-EXEC"
;;          "M1-EXEC-REMOVAL" "M1-OF-LIST-FIX"
;;          "M2-EXEC" "M2-EXEC-REMOVAL"
;;          "M2-OF-LIST-FIX" "M3-EXEC"
;;          "M3-EXEC-REMOVAL" "M3-OF-LIST-FIX"))
;;  "/local/src/acl2-6.4/books/std/util/defmapappend-tests.lisp"
;;  "/local/src/acl2-6.4/books/std/util/defprojection-tests.lisp")
;;
;; says that there is a conflict in the "STD" package between a set of
;; symbols including "M0-EXEC" in the files defmapappend-tests.lisp
;; and defprojection-tests.lisp in the std/util/ books directory.

(include-book "coi/util/defun" :dir :system)
(include-book "bookdata-types")

(encapsulate
    ()

  (local
   (encapsulate
       ()

     (encapsulate
	 ()

       (local
	(defthm equal-double-containment-1
	  (implies
	   (and
	    (characterp x)
	    (characterp y)
	    (equal x y))
	   (not (char< x y)))))

       (local
	(defthm equal-double-containment-2
	  (implies
	   (and
	    (characterp x)
	    (characterp y)
	    (not (char< x y))
	    (not (char< y x)))
	   (equal x y))
	  :rule-classes nil
	  :hints (("Goal" :use ((:instance CODE-CHAR-CHAR-CODE-IS-IDENTITY (c y))
				(:instance CODE-CHAR-CHAR-CODE-IS-IDENTITY (c x)))))))

       (defthmd character-equal-double-containment
	 (implies
	  (and
	   (characterp x)
	   (characterp y))
	  (iff (equal x y)
	       (and (not (char< x y))
		    (not (char< y x)))))
	 :hints (("Goal" :in-theory nil
		  :use (equal-double-containment-2
			equal-double-containment-1
			(:instance equal-double-containment-1 (x y) (y x))))))

       (defthm char<-transitive
	 (implies
	  (and
	   (char< x y)
	   (char< y z))
	  (char< x z)))

       (defthm char<-contra-transitive
	 (implies
	  (and
	   (not (char< x y))
	   (not (char< y z)))
	  (not (char< x z))))

       )

     (defun list-equal (x y)
       (if (and (consp x) (consp y))
	   (and (equal (car x) (car y))
		(list-equal (cdr x) (cdr y)))
	 (and (not (consp x))
	      (not (consp y)))))

     (defthmd equal-to-list-equal
       (implies
	(and
	 (true-listp x)
	 (true-listp y))
	(iff (equal x y)
	     (list-equal x y))))

     (defthm character-listp-implies-true-listp
       (implies
	(character-listp x)
	(true-listp x))
       :rule-classes (:forward-chaining))

     (defthmd character-listp-equal-double-containment
       (implies
	(and
	 (character-listp x)
	 (character-listp y)
	 (natp n))
	(iff (equal x y)
	     (and (null (string<-l x y n))
		  (null (string<-l y x n)))))
       :hints (("Goal" :induct (string<-l x y n)
		:expand ((character-listp x)
			 (character-listp y))
		:in-theory (e/d (string<-l
				 character-listp
				 equal-to-list-equal
				 character-equal-double-containment)
				(char<)))))

     (defthmd string-equal-to-character-list-equal
       (implies
	(and
	 (stringp x)
	 (stringp y))
	(iff (equal x y)
	     (equal (coerce x 'list)
		    (coerce y 'list))))
       :hints (("Goal" :in-theory nil
		:use ((:instance COERCE-INVERSE-2
				 (x x))
		      (:instance COERCE-INVERSE-2
				 (x y))))))

     (defun string<-ll (x y)
       (if (and (consp x) (consp y))
	   (if (equal (car x) (car y))
	       (string<-ll (cdr x) (cdr y))
	     (char< (car x) (car y)))
	 (consp y)))

     (defthm string<-ll-transitive
       (implies
	(and
	 (string<-ll x y)
	 (string<-ll y z))
	(string<-ll x z)))

     (defthm string<-ll-contra-transitive
       (implies
	(and
	 (not (string<-ll x y))
	 (not (string<-ll y z))
	 (character-listp x)
	 (character-listp y)
	 (character-listp z))
	(not (string<-ll x z)))
       :hints (("Goal" :in-theory (e/d (character-equal-double-containment)
				       (char<)))))

     (defthmd string<-l-reduction
       (implies
	(and
	 (character-listp x)
	 (character-listp y)
	 (natp n))
	(iff (string<-l x y n)
	     (string<-ll x y)))
       :hints (("Goal" :in-theory (e/d (character-equal-double-containment string<-l) (char<))
		:expand ((CHARACTER-LISTP X) (CHARACTER-LISTP Y))
		:induct (string<-l x y n))))

     ))

  (defthm string-equal-double-containment
    (implies
     (and
      (stringp x)
      (stringp y))
     (iff (equal x y)
	  (and (not (string< x y))
	       (not (string< y x)))))
    :hints (("Goal" :in-theory (enable
				string<
				string-equal-to-character-list-equal
				character-listp-equal-double-containment
				))))

  (defthm string<-transitive
    (implies
     (and
      (string< x y)
      (string< y z))
     (string< x z))
    :hints (("Goal" :in-theory (enable string<-l-reduction string<))))

  (defthm string<-contra-transitive
    (implies
     (and
      (not (string< x y))
      (not (string< y z)))
     (not (string< x z)))
    :hints (("Goal" :in-theory (enable string<-l-reduction string<))))

  (defthm <-from-not-<-not-equal
    (implies
     (and
      (not (string< x y))
      (stringp x)
      (stringp y)
      (not (equal x y)))
     (string< y x))
    :rule-classes ((:forward-chaining :trigger-terms ((string< x y)))))

  )

;; ------------------------------------------------------------------
;; String union
;; ------------------------------------------------------------------

(defthm string-listp-implies-true-listp
  (implies
   (string-listp list)
   (true-listp list))
  :rule-classes (:forward-chaining))

(defun <-string-all (key list)
  (declare (type (satisfies stringp) key))
  (if (not (consp list)) (null list)
    (and (stringp (car list))
	 (string< key (car list))
	 (<-string-all key (cdr list)))))

(defthm <-string-all-transitive
  (implies
   (and
    (<-string-all b list)
    (string< a b)
    (stringp a)
    (stringp b))
   (<-string-all a list)))

(defun <-string-listp (list)
  (declare (type t list))
  (if (not (consp list)) (null list)
    (and (stringp (car list))
	 (<-string-all (car list) (cdr list))
	 (<-string-listp (cdr list)))))

(defthm <-string-listp-implies-string-listp
  (implies
   (<-string-listp list)
   (string-listp list))
  :rule-classes (:forward-chaining))

(def::un string-insert (a list)
  (declare (xargs :signature ((stringp string-listp) string-listp)))
  (if (endp list) (list a)
    (let ((entry (car list)))
      (if (equal a entry) list
	(if (string< a entry) (cons a list)
	  (cons entry (string-insert a (cdr list))))))))

(defthm member-insert
  (iff (member-equal k (string-insert a list))
       (or (equal k a) (member-equal k list))))

(defthm <-string-all-string-insert
  (implies
   (and
    (string< a x)
    (<-string-all a list)
    (stringp a)
    (stringp x))
   (<-string-all a (string-insert x list))))

(def::signature string-insert (stringp <-string-listp) <-string-listp)

(defun final-string-union (b a x)
  (declare (type string a b)
	   (type (satisfies string-listp) x))
  (if (equal a b) (cons a x)
    (if (string< a b) (cons a (string-insert b x))
      (list* b a x))))

(def::un string-union-rec (a x b y)
  (declare (xargs :signature ((stringp string-listp stringp string-listp) string-listp))
	   (xargs :measure (+ (len x) (len y))))
  (if (and (consp x) (consp y))
      (if (equal a b) (cons a (string-union-rec (car x) (cdr x) (car y) (cdr y)))
	(if (string< a b) (cons a (string-union-rec (car x) (cdr x) b y))
	  (cons b (string-union-rec a x (car y) (cdr y)))))
    (if (consp x) (final-string-union b a x)
      (final-string-union a b y))))

(def::signature string-union-rec (t true-listp t true-listp) true-listp)

(defthm member-string-union-rec
  (iff (member-equal k (string-union-rec a x b y))
       (or (equal k a)
	   (equal k b)
	   (member-equal k x)
	   (member-equal k y))))

(defthm <-string-all-z-string-union-rec
  (implies
   (and
    (stringp a)
    (stringp b)
    (stringp z)
    (<-string-all z x)
    (<-string-all z y)
    (string< z a)
    (string< z b))
   (<-string-all z (string-union-rec a x b y))))

(defthm <-string-listp-string-union-rec
  (implies
   (and
    (stringp a)
    (stringp b)
    (<-string-all a x)
    (<-string-all b y)
    (<-string-listp x)
    (<-string-listp y))
   (<-string-listp (string-union-rec a x b y)))
  :hints (("Goal" :induct (string-union-rec a x b y)
	   :expand (string-union-rec a x b y)))
  :rule-classes (:rewrite
		 (:forward-chaining :trigger-terms ((string-union-rec a x b y)))))

(def::und string-union (x y)
  (declare (xargs :signature ((string-listp string-listp) string-listp)))
  (if (and (consp x) (consp y))
      (string-union-rec (car x) (cdr x) (car y) (cdr y))
    (or x y)))

(def::signature string-union (true-listp true-listp) true-listp
  :hints (("Goal" :in-theory (enable string-union))))

(def::signature string-union (<-string-listp <-string-listp) <-string-listp
  :hints (("Goal" :in-theory (enable string-union))))

(defthm member-string-union
  (implies
   (and (true-listp x) (true-listp y))
   (iff (member-equal k (string-union x y))
	(or (member-equal k x)
	    (member-equal k y))))
  :hints (("Goal" :in-theory (enable string-union))))

(def::un split (n list res)
  (declare (xargs :signature ((natp true-listp true-listp) true-listp true-listp)))
  (if (zp n) (mv list res)
    (split (1- n) (cdr list) (cons (car list) res))))

(def::signature split (t true-listp true-listp) true-listp true-listp)

(defthm not-member-split
  (implies
   (and
    (not (member-equal k list))
    (not (member-equal k res))
    (<= (nfix n) (len list)))
   (and (not (member-equal k (val 0 (split n list res))))
	(not (member-equal k (val 1 (split n list res))))))
  :hints (("Goal" :induct (split n list res))))

(defthm neither-member-split
  (implies
   (and
    (not (member-equal k (val 0 (split n list res))))
    (not (member-equal k (val 1 (split n list res)))))
   (and (not (member-equal k list))
	(not (member-equal k res))))
  :rule-classes (:forward-chaining)
  :hints (("Goal" :induct (split n list res))))

(defthm member-split-or
  (implies
   (member-equal k list)
   (or (member-equal k (val 0 (split n list res)))
       (member-equal k (val 1 (split n list res)))))
  :rule-classes nil
  :hints (("Goal" :induct (split n list res))))

(defthm not-member-split-v0
  (implies
   (not (member-equal k list))
   (not (member-equal k (val 0 (split n list res)))))
  :hints (("Goal" :induct (split n list res))))

(defthm not-member-split-v1-implies
  (implies
   (not (member-equal k (val 1 (split n list res))))
   (not (member-equal k res)))
  :rule-classes (:forward-chaining)
  :hints (("Goal" :induct (split n list res))))

(defthm member-split-v1
  (implies
   (and
    (member-equal k list)
    (not (member-equal k (val 0 (split n list res)))))
   (member-equal k (val 1 (split n list res))))
  :hints (("Goal" :use member-split-or)))

(defthm member-split-v2
  (implies
   (and
    (member-equal k list)
    (not (member-equal k (val 1 (split n list res)))))
   (member-equal k (val 0 (split n list res))))
  :hints (("Goal" :use member-split-or)))

(defthm len-split-1
  (equal (len (val 1 (split n list res)))
	 (+ (nfix n) (len res))))

(defthm len-split-0-nil
  (implies
   (not (consp list))
   (equal (len (val 0 (split n list res)))
	  0)))

(defthm len-split-0
  (equal (len (val 0 (split n list res)))
	 (nfix (- (len list) (nfix n)))))

(defthm string-listp-split
  (implies
   (and
    (string-listp list)
    (string-listp res)
    (natp n)
    (< n (len list)))
   (and (string-listp (val 0 (split n list res)))
	(string-listp (val 1 (split n list res)))))
  :rule-classes (:rewrite
		 (:forward-chaining :trigger-terms ((split n list res)))))

(encapsulate
    ()

  (local (include-book "arithmetic-5/top" :dir :system))

  (defthm ash-upper-bound
    (implies
     (and
      (natp n)
      (< 1 n))
     (< (ash n -1) n))
    :rule-classes (:rewrite
		   :linear
		   (:forward-chaining :trigger-terms ((ash n -1)))))

  (defthm ash-lower-bound
    (implies
     (and
      (natp n)
      (< 1 n))
     (< 0 (ash n -1)))
    :rule-classes (:rewrite
		   :linear
		   (:forward-chaining :trigger-terms ((ash n -1)))))

  )

(in-theory (disable ash))

(defthm linear-n
  (implies
   (and
    (not (zp n))
    (not (equal n 1)))
   (< 1 n))
  :rule-classes :forward-chaining)

(defthm help-me
  (implies
   (< 0 n)
   (<= 0 n)))

(defthm help-please
  (implies
   (< x y)
   (not (< y x))))

(defthm z
  (iff (< (+ x (- y)) 0)
       (< x y)))

(def::un sort-rec (n list)
  (declare (xargs :signature (((lambda (n) (and (natp n) (= n (len list)))) string-listp) string-listp)
		  :signature-hints (("Goal" :induct (sort-rec n list)))
		  :measure (nfix n)))
  (if (or (endp list) (zp n) (= n 1)) list
    (let ((n1 (ash n -1)))
      (let ((n2 (- n n1)))
	(met ((left right) (split n1 list nil))
	  (string-union (sort-rec n2 left)
			(sort-rec n1 right)))))))

(def::signature sort-rec (t true-listp) true-listp)

(defthm <-string-listp-sort-rec
  (implies
   (and
    (natp n)
    (= n (len list))
    (string-listp list))
   (<-string-listp (sort-rec n list)))
  :hints (("Goal" :induct (sort-rec n list)))
  :rule-classes (:rewrite
		 (:forward-chaining :trigger-terms ((sort-rec n list)))))

(defthm member-sort-rec
  (implies
   (and
    (true-listp list)
    (= (nfix n) (len list)))
   (iff (member-equal key (sort-rec n list))
	(member-equal key list))))

(def::und sort-strings (list)
  (declare (xargs :signature ((string-listp) <-string-listp)))
  (sort-rec (len list) list))

(defthm member-sort-strings
  (implies
   (true-listp list)
   (iff (member-equal key (sort-strings list))
	(member-equal key list)))
  :hints (("Goal" :in-theory (enable sort-strings))))

;; ------------------------------------------------------------------
;;
;; ------------------------------------------------------------------

(defun <-string-all-keys (key list)
  (declare (type (satisfies stringp) key))
  (if (not (consp list)) (null list)
    (let ((entry (car list)))
      (and (consp entry)
	   (stringp (car entry))
	   (string< key (car entry))
	   (<-string-all-keys key (cdr list))))))

(defthm <-string-all-keys-transitive
  (implies
   (and
    (<-string-all-keys b list)
    (string< a b)
    (stringp a)
    (stringp b))
   (<-string-all-keys a list)))

(defun <-pkg-symbol-name-listp (list)
  (declare (type t list))
  (if (not (consp list)) (null list)
    (let ((entry (car list)))
      (and (consp entry)
	   (stringp (car entry))
	   (<-string-all-keys (car entry) (cdr list))
	   (<-string-listp (cdr entry))
	   (<-pkg-symbol-name-listp (cdr list))))))

(def::un string-key-update (key value list)
  (declare (xargs :signature ((stringp string-listp pkg-symbol-name-listp) pkg-symbol-name-listp)))
  (if (endp list) (list (cons key value))
    (let ((entry (car list)))
      (if (equal key (car entry)) (acons key (string-union value (cdr entry)) (cdr list))
	(if (string< key (car entry)) (acons key value list)
	  (cons entry (string-key-update key value (cdr list))))))))

(defthm <-string-all-keys-string-key-update
  (implies
   (and
    (string< a x)
    (<-string-all-keys a list)
    (stringp a)
    (stringp x))
   (<-string-all-keys a (string-key-update x value list))))

(def::signature string-key-update (stringp <-string-listp <-pkg-symbol-name-listp) <-pkg-symbol-name-listp)

(def::un sort-pkg-symbol-name-list (list)
  (declare (xargs :signature ((pkg-symbol-name-listp) <-pkg-symbol-name-listp)))
  (if (endp list) nil
    (let ((entry (car list)))
      (let ((value (sort-strings (cdr entry))))
	(let ((res (sort-pkg-symbol-name-list (cdr list))))
	  (string-key-update (car entry) value res))))))

(defun final-pkg-symbol-name-merge (k1 v1 k2 v2 list2)
  (declare (type string k1 k2)
	   (type (satisfies string-listp) v1 v2)
	   (type (satisfies pkg-symbol-name-listp) list2))
  (if (equal k1 k2) (acons k1 (string-union v1 v2) list2)
    (if (string< k2 k1) (acons k2 v2 (string-key-update k1 v1 list2))
      (acons k1 v1 (acons k2 v2 list2)))))

(def::un merge-pkg-symbol-name-list-rec (k1 v1 x k2 v2 y)
  (declare (xargs :signature ((stringp string-listp pkg-symbol-name-listp stringp string-listp pkg-symbol-name-listp)
			      pkg-symbol-name-listp)
		  :signature-hints (("Goal" :induct (merge-pkg-symbol-name-list-rec k1 v1 x k2 v2 y)
				     :expand (merge-pkg-symbol-name-list-rec k1 v1 x k2 v2 y)))
		  :measure (+ (len x) (len y))))
  (if (and (consp x) (consp y))
      (if (equal k1 k2)
	  (acons k1 (string-union v1 v2) (merge-pkg-symbol-name-list-rec (caar x) (cdar x) (cdr x)
								    (caar y) (cdar y) (cdr y)))
	(if (string< k1 k2) (acons k1 v1 (merge-pkg-symbol-name-list-rec (caar x) (cdar x) (cdr x) k2 v2 y))
	  (acons k2 v2 (merge-pkg-symbol-name-list-rec k1 v1 x (caar y) (cdar y) (cdr y)))))
    (if (consp x) (final-pkg-symbol-name-merge k2 v2 k1 v1 x)
      (final-pkg-symbol-name-merge k1 v1 k2 v2 y))))

(defthm <-string-all-z-merge-pkg-symbol-name-list-rec
  (implies
   (and
    (stringp k1)
    (stringp k2)
    (stringp z)
    (<-string-all-keys z x)
    (<-string-all-keys z y)
    (string< z k1)
    (string< z k2))
   (<-string-all-keys z (merge-pkg-symbol-name-list-rec k1 v1 x k2 v2 y))))

(defthm <-pkg-symbol-name-listp-merge-pkg-symbol-name-list-rec
  (implies
   (and
    (stringp k1)
    (<-string-listp v1)
    (<-pkg-symbol-name-listp x)
    (stringp k2)
    (<-string-listp v2)
    (<-pkg-symbol-name-listp y)
    (<-string-all-keys k1 x)
    (<-string-all-keys k2 y))
   (<-pkg-symbol-name-listp (merge-pkg-symbol-name-list-rec k1 v1 x k2 v2 y)))
  :hints (("Goal" :induct (merge-pkg-symbol-name-list-rec k1 v1 x k2 v2 y))))

(def::und merge-pkg-symbol-name-list (list1 list2)
  (declare (xargs :signature ((<-pkg-symbol-name-listp <-pkg-symbol-name-listp) <-pkg-symbol-name-listp)))
  (if (and (consp list1) (consp list2))
      (merge-pkg-symbol-name-list-rec (caar list1) (cdar list1) (cdr list1)
				 (caar list2) (cdar list2) (cdr list2))
    (or list1 list2)))

(def::und process-pkg-symbol-name-list (alist res)
  (declare (xargs :signature ((pkg-symbol-name-listp <-pkg-symbol-name-listp) <-pkg-symbol-name-listp)))
  (if (endp alist) res
    (let ((entry (car alist)))
      (let ((value (sort-strings (cdr entry))))
	(let ((res (string-key-update (car entry) value res)))
	  (process-pkg-symbol-name-list (cdr alist) res))))))

(def::un intersect-<-string (key list)
  (declare (xargs :signature ((stringp string-listp) string-listp string-listp string-listp)))
  (if (endp list) (mv (list key) nil nil)
    (if (equal key (car list)) (mv nil (list key) (cdr list))
      (met ((L I R) (intersect-<-string key (cdr list)))
	(mv L I (cons (car list) R))))))


;; Membership rules ..

;; (defun or*-fn (list)
;;   (if (endp list) 'nil
;;     `(if ,(car list) t
;;        ,(or*-fn (cdr list)))))

;; (defun and*-fn (list)
;;   (if (endp list) 't
;;     `(if ,(car list) ,(and*-fn (cdr list))
;;        nil)))

;; (defmacro or* (&rest args)
;;   (or*-fn args))

;; (defmacro and* (&rest args)
;;   (and*-fn args))

(defthm intersect-<-string-preserves-list-membership
  (implies
   (member-equal z list)
   (or (member-equal z (val 1 (intersect-<-string key list)))
       (member-equal z (val 2 (intersect-<-string key list)))))
  :hints (("Goal" :induct (intersect-<-string key list)))
  :rule-classes ((:forward-chaining
		  :trigger-terms ((member-equal z (val 1 (intersect-<-string key list)))
				  (member-equal z (val 2 (intersect-<-string key list)))))))

(defthm intersect-<-string-preserves-key
  (or (member-equal key (val 0 (intersect-<-string key list)))
      (member-equal key (val 1 (intersect-<-string key list))))
  :hints (("Goal" :induct (intersect-<-string key list)))
  :rule-classes ((:forward-chaining
		  :trigger-terms ((member-equal z (val 0 (intersect-<-string key list)))
				  (member-equal z (val 1 (intersect-<-string key list)))))))

(defthm member-0-intersect-<-string
  (implies
   (member-equal z (val 0 (intersect-<-string key list)))
   (equal z key))
  :rule-classes :forward-chaining)

(defthm member-1-intersect-<-string
  (implies
   (member-equal z (val 1 (intersect-<-string key list)))
   (and  (equal z key)
	 (member-equal z list)))
  :rule-classes :forward-chaining)

(defthm member-2-intersect-<-string
  (implies
   (member-equal z (val 2 (intersect-<-string key list)))
   (and  (member-equal z list)))
  :rule-classes :forward-chaining)

;; Sorted rules ..

(defthm <-string-all-string-intersect-<-string-0
  (implies
   (and
    (string< a x)
    (stringp x))
   (<-string-all a (val 0 (intersect-<-string x list)))))

(defthm <-string-all-string-intersect-<-string-1
  (implies
   (and
    (string< a x)
    (<-string-all a list)
    (stringp x))
   (<-string-all a (val 1 (intersect-<-string x list)))))

(defthm <-string-all-string-intersect-<-string-2
  (implies
   (<-string-all a list)
   (<-string-all a (val 2 (intersect-<-string x list)))))

(def::signature intersect-<-string (stringp <-string-listp) <-string-listp <-string-listp <-string-listp)

;;

(def::und final-intersect-<-string-list-rec (left right x)
  (declare (xargs :signature ((stringp stringp string-listp) string-listp string-listp string-listp)))
  (if (equal left right) (mv nil (list left) x)
    (if (string< left right) (mv (list left) nil (cons right x))
      (met ((L I R) (intersect-<-string left x))
	(mv L I (cons right R))))))

(def::signature final-intersect-<-string-list-rec (stringp (lambda (x) (and (stringp x) (<-string-all right x))) <-string-listp)
  <-string-listp <-string-listp <-string-listp
  :hints (("Goal" :in-theory (enable final-intersect-<-string-list-rec))))

(def::un intersect-<-string-list-rec (a x b y)
  (declare (xargs :signature ((string string-listp string string-listp) string-listp string-listp string-listp)
		  :measure (+ (len x) (len y))))
  (if (and (consp x) (consp y))
      (if (equal a b) (met ((L I R) (intersect-<-string-list-rec (car x) (cdr x) (car y) (cdr y)))
			(mv L (cons a I) R))
	(if (string< a b) (met ((L I R) (intersect-<-string-list-rec (car x) (cdr x) b y))
			    (mv (cons a L) I R))
	  (met ((L I R) (intersect-<-string-list-rec a x (car y) (cdr y)))
	    (mv L I (cons b R)))))
    (if (consp x) (met ((L I R) (final-intersect-<-string-list-rec b a x))
		    (mv R I L))
      (final-intersect-<-string-list-rec a b y))))

;; Membership rules ..

(defthm intersect-<-string-list-rec-preserves-a
  (or (member-equal a (val 0 (intersect-<-string-list-rec a x b y)))
      (member-equal a (val 1 (intersect-<-string-list-rec a x b y))))
  :hints (("Goal" :induct (intersect-<-string-list-rec a x b y)
	   :in-theory (enable final-intersect-<-string-list-rec)))
  :rule-classes ((:forward-chaining
		  :trigger-terms ((member-equal a (val 0 (intersect-<-string-list-rec a x b y)))
				  (member-equal a (val 1 (intersect-<-string-list-rec a x b y)))))))

(defthm intersect-<-string-list-rec-preserves-b
  (or (member-equal b (val 1 (intersect-<-string-list-rec a x b y)))
      (member-equal b (val 2 (intersect-<-string-list-rec a x b y))))
  :hints (("Goal" :induct (intersect-<-string-list-rec a x b y)
	   :in-theory (enable final-intersect-<-string-list-rec)))
  :rule-classes ((:forward-chaining
		  :trigger-terms ((member-equal b (val 1 (intersect-<-string-list-rec a x b y)))
				  (member-equal b (val 2 (intersect-<-string-list-rec a x b y)))))))

(defthm intersect-<-string-list-rec-preserves-x-membership
  (implies
   (member-equal z x)
   (or (member-equal z (val 0 (intersect-<-string-list-rec a x b y)))
       (member-equal z (val 1 (intersect-<-string-list-rec a x b y)))))
  :hints (("Goal" :induct (intersect-<-string-list-rec a x b y)
	   :in-theory (enable final-intersect-<-string-list-rec)))
  :rule-classes ((:forward-chaining
		  :trigger-terms ((member-equal z (val 0 (intersect-<-string-list-rec a x b y)))
				  (member-equal z (val 1 (intersect-<-string-list-rec a x b y)))))))

(defthm intersect-<-string-list-rec-preserves-y-membership
  (implies
   (member-equal z y)
   (or (member-equal z (val 1 (intersect-<-string-list-rec a x b y)))
       (member-equal z (val 2 (intersect-<-string-list-rec a x b y)))))
  :hints (("Goal" :induct (intersect-<-string-list-rec a x b y)
	   :in-theory (enable final-intersect-<-string-list-rec)))
  :rule-classes ((:forward-chaining
		  :trigger-terms ((member-equal z (val 1 (intersect-<-string-list-rec a x b y)))
				  (member-equal z (val 2 (intersect-<-string-list-rec a x b y)))))))


(defthm member-0-intersect-<-string-list-rec
  (implies
   (member-equal z (val 0 (intersect-<-string-list-rec a x b y)))
   (or (equal z a)
       (member-equal z x)))
  :hints (("Goal" :induct (intersect-<-string-list-rec a x b y)
	   :in-theory (enable final-intersect-<-string-list-rec)))
  :rule-classes :forward-chaining)

(encapsulate
    ()

  (local
   (defthm helper
     (implies
      (and
       (member-equal a list)
       (equal a b))
      (member-equal b list))
     :rule-classes :forward-chaining))

  (defthm member-1-intersect-<-string-list-rec
    (implies
     (member-equal z (val 1 (intersect-<-string-list-rec a x b y)))
     (and  (or (equal z a)
	       (member-equal z x))
	   (or (equal z b)
	       (member-equal z y))))
    :hints (("Goal" :induct (intersect-<-string-list-rec a x b y)
	     :in-theory (enable final-intersect-<-string-list-rec)))
    :rule-classes :forward-chaining)

  )

(defthm member-2-intersect-<-string-list-rec
  (implies
   (member-equal z (val 2 (intersect-<-string-list-rec a x b y)))
   (or (equal z b)
       (member-equal z y)))
  :hints (("Goal" :induct (intersect-<-string-list-rec a x b y)
	   :in-theory (enable final-intersect-<-string-list-rec)))
  :rule-classes :forward-chaining)

(defthm <-string-all-string-intersect-<-string-list-rec-0
  (implies
   (and
    (string< z a)
    (stringp a)
    (<-string-all z x))
   (<-string-all z (val 0 (intersect-<-string-list-rec a x b y))))
  :hints (("Goal" :induct (intersect-<-string-list-rec a x b y)
	   :in-theory (enable final-intersect-<-string-list-rec))))

(defthm <-string-all-string-intersect-<-string-list-rec-1
  (implies
   (and
    (string< z a)
    (stringp a)
    (<-string-all z x)
    (string< z b)
    (stringp b)
    (<-string-all z y))
   (<-string-all z (val 1 (intersect-<-string-list-rec a x b y))))
  :hints (("Goal" :induct (intersect-<-string-list-rec a x b y)
	   :in-theory (enable final-intersect-<-string-list-rec))))

(defthm <-string-all-string-intersect-<-string-list-rec-2
  (implies
   (and
    (string< z b)
    (stringp b)
    (<-string-all z y))
   (<-string-all z (val 2 (intersect-<-string-list-rec a x b y))))
  :hints (("Goal" :induct (intersect-<-string-list-rec a x b y)
	   :in-theory (enable final-intersect-<-string-list-rec))))

(defthm string-<-intersect-<-string-list-rec
  (implies
   (and
    (stringp a)
    (<-string-listp x)
    (<-string-all a x)
    (stringp b)
    (<-string-listp y)
    (<-string-all b y))
   (and (<-string-listp (val 0 (intersect-<-string-list-rec a x b y)))
	(<-string-listp (val 1 (intersect-<-string-list-rec a x b y)))
	(<-string-listp (val 2 (intersect-<-string-list-rec a x b y)))))
  :hints (("Goal" :induct (intersect-<-string-list-rec a x b y)
	   :in-theory (enable final-intersect-<-string-list-rec))))

(def::und intersect-<-string-list (x y)
  (declare (xargs :signature ((string-listp string-listp) string-listp string-listp string-listp)))
  (if (and (consp x) (consp y))
      (intersect-<-string-list-rec (car x) (cdr x) (car y) (cdr y))
    (if (consp x) (mv x nil nil)
      (mv nil nil y))))

(def::signature intersect-<-string-list (<-string-listp <-string-listp)
  <-string-listp <-string-listp <-string-listp
  :hints (("Goal" :in-theory (enable intersect-<-string-list))))

;; ---------------------------------------------------------------------------------------

;; The trick in intersecting two pkg-symbol-name-listp is understanding
;; that the association list keys are sorted.

(def::un acons? (key val res)
  (declare (xargs :signature ((string string-listp pkg-symbol-name-listp) pkg-symbol-name-listp)))
  (if val (acons key val res) res))

(def::un intersect-1-pkg-symbol-name-list (k v x)
  (declare (xargs :signature ((string string-listp pkg-symbol-name-listp)
			      pkg-symbol-name-listp pkg-symbol-name-listp pkg-symbol-name-listp)
		  :signature-hints (("Goal" :in-theory (enable pkg-symbol-name-list-entry)))))
  (if (endp x) (mv (acons k v nil) nil nil)
    (let ((entry (car x)))
      (let ((ke (car entry))
	    (kv (cdr entry)))
	(if (equal k ke) (met ((ls is rs) (intersect-<-string-list v kv))
			   (mv (acons? k ls nil)
			       (acons? k is nil)
			       (acons? k rs (cdr x))))
	  (if (string< k ke) (mv (acons k v nil) nil x)
	    (met ((lr ir rr) (intersect-1-pkg-symbol-name-list k v (cdr x)))
	      (mv lr ir (acons ke kv rr)))))))))

(defthm <-string-all-keys-v0-v1-intersect-1-pkg-symbol-name-list
  (implies
   (and
    (stringp k)
    (string< a k))
   (and (<-string-all-keys a (val 0 (intersect-1-pkg-symbol-name-list k v x)))
	(<-string-all-keys a (val 1 (intersect-1-pkg-symbol-name-list k v x))))))

(defthm <-string-all-keys-v2-intersect-1-pkg-symbol-name-list
  (implies
   (and
    (<-string-all-keys a x)
    ;;(<-string-listp x)
    (stringp k)
    (string< a k))
   (<-string-all-keys a (val 2 (intersect-1-pkg-symbol-name-list k v x)))))

(def::signature intersect-1-pkg-symbol-name-list (string <-string-listp <-pkg-symbol-name-listp)
  <-pkg-symbol-name-listp <-pkg-symbol-name-listp <-pkg-symbol-name-listp)

(def::und final-intersect-pkg-symbol-name-listp (bk bv ak av x)
  (declare (xargs :signature ((string string-listp string string-listp pkg-symbol-name-listp)
			      pkg-symbol-name-listp pkg-symbol-name-listp pkg-symbol-name-listp)))
  (if (equal bk ak) (met ((ls is rs) (intersect-<-string-list bv av))
		      (mv (acons? ak ls nil) (acons? ak is nil) (acons? ak rs x)))
    (if (string< bk ak) (mv (acons bk bv nil) nil (acons ak av x))
      (met ((lr ir rr) (intersect-1-pkg-symbol-name-list bk bv x))
	(mv lr ir (acons ak av rr))))))

(def::un intersect-pkg-symbol-name-list-rec (k1 v1 x k2 v2 y)
  (declare (xargs :signature ((string string-listp pkg-symbol-name-listp
			       string string-listp pkg-symbol-name-listp)
			      pkg-symbol-name-listp pkg-symbol-name-listp pkg-symbol-name-listp)
		  :measure (+ (len x) (len y))))
  (if (and (consp x) (consp y))
      (if (equal k1 k2)
	  (met ((ls is rs) (intersect-<-string-list v1 v2))
	    (met ((lr ir rr) (intersect-pkg-symbol-name-list-rec (caar x) (cdar x) (cdr x) (caar y) (cdar y) (cdr y)))
	      (mv (acons? k1 ls lr)
		  (acons? k1 is ir)
		  (acons? k1 rs rr))))
	(if (string< k1 k2)
	    (met ((lr ir rr) (intersect-pkg-symbol-name-list-rec (caar x) (cdar x) (cdr x) k2 v2 y))
	      (mv (acons k1 v1 lr) ir rr))
	  (met ((lr ir rr) (intersect-pkg-symbol-name-list-rec k1 v1 x (caar y) (cdar y) (cdr y)))
	    (mv lr ir (acons k2 v2 rr)))))
    (if (consp x) (met ((lr ir rr) (final-intersect-pkg-symbol-name-listp k2 v2 k1 v1 x))
		    (mv rr ir lr))
      (final-intersect-pkg-symbol-name-listp k1 v1 k2 v2 y))))

(defthm <-string-all-keys-v0-intersect-pkg-symbol-name-list-rec
  (implies
   (and
    (stringp k1)
    (stringp k2)
    (<-pkg-symbol-name-listp x)
    (<-pkg-symbol-name-listp y)
    (<-string-all-keys k1 x)
    (<-string-all-keys k2 y)
    (stringp a)
    (string< a k1))
   (<-string-all-keys a (val 0 (intersect-pkg-symbol-name-list-rec k1 v1 x k2 v2 y))))
  :hints (("Goal" :induct (intersect-pkg-symbol-name-list-rec k1 v1 x k2 v2 y)
	   :do-not-induct t
	   :in-theory (enable final-intersect-pkg-symbol-name-listp))))

(defthm <-string-all-keys-v1-intersect-pkg-symbol-name-list-rec
  (implies
   (and
    (stringp k1)
    (stringp k2)
    (<-pkg-symbol-name-listp x)
    (<-pkg-symbol-name-listp y)
    (<-string-all-keys k1 x)
    (<-string-all-keys k2 y)
    (stringp a)
    (string< a k1)
    (string< a k2))
   (<-string-all-keys a (val 1 (intersect-pkg-symbol-name-list-rec k1 v1 x k2 v2 y))))
  :hints (("Goal" :induct (intersect-pkg-symbol-name-list-rec k1 v1 x k2 v2 y)
	   :do-not-induct t
	   :in-theory (enable final-intersect-pkg-symbol-name-listp))))

(defthm <-string-all-keys-v2-intersect-pkg-symbol-name-list-rec
  (implies
   (and
    (stringp k1)
    (stringp k2)
    (<-pkg-symbol-name-listp x)
    (<-pkg-symbol-name-listp y)
    (<-string-all-keys k1 x)
    (<-string-all-keys k2 y)
    (stringp a)
    (string< a k2))
   (<-string-all-keys a (val 2 (intersect-pkg-symbol-name-list-rec k1 v1 x k2 v2 y))))
  :hints (("goal" :induct (intersect-pkg-symbol-name-list-rec k1 v1 x k2 v2 y)
	   :do-not-induct t
	   :in-theory (enable final-intersect-pkg-symbol-name-listp))))

(defthm <-string-listp-intersect-pkg-symbol-name-list-rec
  (implies
   (and
    (stringp k1)
    (stringp k2)
    (<-pkg-symbol-name-listp x)
    (<-pkg-symbol-name-listp y)
    (<-string-listp v1)
    (<-string-listp v2)
    (<-string-all-keys k1 x)
    (<-string-all-keys k2 y))
   (and
    (<-pkg-symbol-name-listp (val 0 (intersect-pkg-symbol-name-list-rec k1 v1 x k2 v2 y)))
    (<-pkg-symbol-name-listp (val 1 (intersect-pkg-symbol-name-list-rec k1 v1 x k2 v2 y)))
    (<-pkg-symbol-name-listp (val 2 (intersect-pkg-symbol-name-list-rec k1 v1 x k2 v2 y)))))
  :hints (("goal" :induct (intersect-pkg-symbol-name-list-rec k1 v1 x k2 v2 y)
	   :do-not-induct t
	   :in-theory (enable final-intersect-pkg-symbol-name-listp))))

(def::und intersect-pkg-symbol-name-listp (x y)
  (declare (xargs :signature ((pkg-symbol-name-listp pkg-symbol-name-listp)
			       pkg-symbol-name-listp pkg-symbol-name-listp pkg-symbol-name-listp)))
  (if (and (consp x) (consp y))
      (intersect-pkg-symbol-name-list-rec (caar x) (cdar x) (cdr x) (caar y) (cdar y) (cdr y))
    (if (consp x) (mv x nil nil)
      (mv nil nil y))))

(def::signature intersect-pkg-symbol-name-listp (<-pkg-symbol-name-listp <-pkg-symbol-name-listp)
  <-pkg-symbol-name-listp <-pkg-symbol-name-listp <-pkg-symbol-name-listp
  :hints (("Goal" :in-theory (enable intersect-pkg-symbol-name-listp))))

;; ---------------------------------------------------------------------------------------

;; We want everything as complete as possible.

(def::un <-assoc (key graph)
  (declare (xargs :signature ((string <-pkg-symbol-name-listp) <-string-listp)))
  (if (endp graph) nil
    (let ((entry (car graph)))
      (if (equal key (car entry)) (cdr entry)
	(if (string< key (car entry)) nil
	  (<-assoc key (cdr graph)))))))

(def::un elaborate-dependencies (deps graph)
  (declare (xargs :signature ((string-listp <-pkg-symbol-name-listp) <-string-listp)))
  (if (endp deps) nil
    (let ((key (car deps)))
      (let ((res (<-assoc key graph)))
	(string-union (string-insert key res)
		      (elaborate-dependencies (cdr deps) graph))))))

(def::un string-key-update-list (list val res)
  (declare (xargs :signature ((string-listp <-string-listp <-pkg-symbol-name-listp)
			      <-pkg-symbol-name-listp)))
  (if (endp list) res
    (let ((res (string-key-update (car list) val res)))
      (string-key-update-list (cdr list) val res))))

#|
from: ((x<-y)
       (z<-q))
add : (y<-z)
(let ((zfrom (elaborate-dependencies (z) from)))
  ;; (y<-(z q))
  (let ((yto (elaborate-dependencies (y) to)))
    ;; ((y x) <- (z q))
    ))

to: ((y->x)
     (q->z))
add: (z<-y)
(let ((yto (elaborate-dependencies (y) to)))
  ;; (z<-(y x)
  (let ((zfrom (elaborate-dependencies (z) from)))
    ;; ((z q)<-(y x)
    ))

|#

(def::und process-dependencies (key vals from to)
  (declare (xargs :signature ((stringp string-listp <-pkg-symbol-name-listp <-pkg-symbol-name-listp)
			      <-pkg-symbol-name-listp <-pkg-symbol-name-listp)))
  (let ((vals (elaborate-dependencies vals from)))
    (let ((keys (elaborate-dependencies (list key) to)))
      (let ((from (string-key-update-list keys vals from)))
	(let ((to (string-key-update-list vals keys to)))
	  (mv from to))))))

(defund port-prefix (symbol)
  (declare (type symbol symbol))
  (let ((symbol-name (coerce (symbol-name symbol) 'list)))
    (and (< 4 (len symbol-name))
	 (eql (nth 0 symbol-name) #\P)
	 (eql (nth 1 symbol-name) #\O)
	 (eql (nth 2 symbol-name) #\R)
	 (eql (nth 3 symbol-name) #\T))))

(def::und process-bookdata-type (path key data res from to)
  (declare (xargs :signature ((stringp symbolp (lambda (value) (bookdata-key-type key value))
				       <-pkg-symbol-name-listp <-pkg-symbol-name-listp <-pkg-symbol-name-listp)
			      <-pkg-symbol-name-listp <-pkg-symbol-name-listp <-pkg-symbol-name-listp)))
  (if (or (equal key :books)
	  (equal key :port-books))
      (met ((from to) (process-dependencies path data from to))
	(mv res from to))
    ;; We are currently processing only internal symbols.
    ;; We are not doing anything with the portcullus.
    (if (or (port-prefix key) (equal key :pkgs)) (mv res from to)
      (mv (merge-pkg-symbol-name-list (sort-pkg-symbol-name-list data) res) from to))))

(defthm consp-bookdata-key-maps-implies
  (implies
   (and
    (bookdata-key-maps list)
    (consp list))
   (and (consp (cdr list))
	(bookdata-key-map (car list)
			   (cadr list))
	(bookdata-key-maps (cddr list))))
  :rule-classes (:forward-chaining))

(def::und process-bookdata-key-maps (path list res from to)
  (declare (xargs :signature ((stringp bookdata-key-maps <-pkg-symbol-name-listp <-pkg-symbol-name-listp <-pkg-symbol-name-listp)
			      <-pkg-symbol-name-listp <-pkg-symbol-name-listp <-pkg-symbol-name-listp)))
  (if (endp list) (mv res from to)
    (met ((res from to) (process-bookdata-type path (car list) (cadr list) res from to))
      (process-bookdata-key-maps path (cddr list) res from to))))

(defun conflict-entry (entry)
  (declare (type t entry))
  (and (consp entry)
       (<-pkg-symbol-name-listp (car entry))
       (<-string-listp (cdr entry))))

(defthm conflict-entry-implies
  (implies
   (conflict-entry entry)
   (and (consp entry)
	(<-pkg-symbol-name-listp (car entry))
	(<-string-listp (cdr entry))))
  :rule-classes (:forward-chaining))

(defthm implies-conflict-entry
  (implies
   (and (consp entry)
	(<-pkg-symbol-name-listp (car entry))
	(<-string-listp (cdr entry)))
   (conflict-entry entry))
  :rule-classes (:type-prescription :rewrite))

(defun conflict-listp (x)
  (declare (type t x))
  (if (not (consp x)) (null x)
    (let ((entry (car x)))
      (and (conflict-entry entry)
	   (conflict-listp (cdr x))))))

(def::und add-conflict (set plist res)
  (declare (xargs :signature ((<-pkg-symbol-name-listp <-string-listp conflict-listp) conflict-listp)))
  (if (null set) res (acons set plist res)))

(def::und insert-conflict (keys path list res)
  (declare (xargs :signature ((<-pkg-symbol-name-listp stringp conflict-listp conflict-listp) conflict-listp)))
  (if (endp list) (add-conflict keys (list path) res)
    (let ((entry (car list)))
      (let ((set   (car entry))
	    (plist (cdr entry)))
	(met ((subset int subkey) (intersect-pkg-symbol-name-listp set keys))
	  (if (not int) (insert-conflict keys path (cdr list) (cons entry res))
	    (let ((res (add-conflict subset plist res)))
	      (let ((res (add-conflict int (string-insert path plist) res)))
		(insert-conflict subkey path (cdr list) res)))))))))

(def::und process-bookdata (data res from to)
  (declare (xargs :signature ((wf-bookdata conflict-listp <-pkg-symbol-name-listp <-pkg-symbol-name-listp)
			      conflict-listp <-pkg-symbol-name-listp <-pkg-symbol-name-listp)))
  (let ((path (car data))
	(kmap (cdr data)))
    (met ((key from to) (process-bookdata-key-maps path kmap nil from to))
      (mv (insert-conflict key path res nil) from to))))

(def::und process-bookdata-list (list res from to)
  (declare (xargs :signature ((wf-bookdata-listp conflict-listp <-pkg-symbol-name-listp <-pkg-symbol-name-listp)
			      conflict-listp <-pkg-symbol-name-listp <-pkg-symbol-name-listp)))
  (if (endp list) (mv res from to)
    (met ((res from to) (process-bookdata (car list) res from to))
      (process-bookdata-list (cdr list) res from to))))

;; We can use <-pkg-symbol-name-listp to describe graphs, too.

(local
 (encapsulate
     ()

   (def::und bookdata1 ()
     (declare (xargs :signature (() wf-bookdata)))
     (list "/my/book1.lisp"
	   :books `("/my/booka.lisp" "/my/bookb.lisp")
	   :fns   `(("acl2" "plus" "minus" "joe")
		    ("pkg1" "plus" "alpha"))
	   ))

   (def::und bookdata2 ()
     (declare (xargs :signature (() wf-bookdata)))
     (list "/my/book2.lisp"
	   :books `("/my/bookc.lisp" "/my/bookd.lisp")
	   :fns   `(("acl2" "fred" "joe" "zed")
		    ("pkg1" "alpha" "beta")
		    ("pkg2" "plus" "minus"))
	   ))

   (def::und bookdata-list ()
     (declare (xargs :signature (() wf-bookdata-listp)))
     (list (bookdata1) (bookdata2)))

   (defthm instance
     (conflict-listp (val 0 (process-bookdata-list (bookdata-list) nil nil nil))))

   ))

#|
(defun pseudo-conflict-pair (x y from)
  (declare (type string x y)
	   (type (satisfies <-pkg-symbol-name-listp) from))
  (or (member-equal x (<-assoc y from))
      (member-equal y (<-assoc x from))))

(defun pseudo-conflict-list (key list from)
  (declare (type string key)
	   (type (satisfies string-listp) list)
	   (type (satisfies <-pkg-symbol-name-listp) from))
  (if (endp list) t
    (and (pseudo-conflict-pair key (car list) from)
	 (pseudo-conflict-list key (cdr list) from))))

(defun pseudo-conflict (set from)
  (declare (type (satisfies string-listp) set)
	   (type (satisfies <-pkg-symbol-name-listp) from))
  (if (endp set) t
    (and (pseudo-conflict-list (car set) (cdr set) from)
	 (pseudo-conflict (cdr set) from))))
|#

(include-book "str/strtok" :dir :system)

;; If any other entry is in your from set,

(defun same-directory-rec (a x b y)
  (declare (type t x y))
  (if (and (consp x) (consp y))
      (and (equal a b)
	   (same-directory-rec (car x) (cdr x) (car y) (cdr y)))
    (and (null x) (null y))))

(defun same-directory (x y)
  (declare (type t x y))
  (if (and (consp x) (consp y))
      (same-directory-rec (car x) (cdr x) (car y) (cdr y))
    (and (null x) (null y))))

(defun any-same-directory-list (xpath list)
  (declare (type (satisfies string-listp) xpath list))
  (if (endp list) nil
    (or (same-directory xpath (str::strtok (car list) (list *directory-separator*)))
	(any-same-directory-list xpath (cdr list)))))

(defun any-same-directory-set (list)
  (declare (type (satisfies string-listp) list))
  (if (endp list) nil
    (or (any-same-directory-list (str::strtok (car list) (list *directory-separator*)) (cdr list))
	(any-same-directory-set (cdr list)))))

(defun <-member (key list)
  (declare (type string key)
	   (type (satisfies <-string-listp) list))
  (if (endp list) nil
    (let ((entry (car list)))
      (or (equal key entry)
	  (and (string< entry key)
	       (<-member key (cdr list)))))))

(def::un intersect-sets-rec (aset list to)
  (declare (xargs :signature ((string-listp string-listp <-pkg-symbol-name-listp) string-listp)))
  (if (endp list) nil
    (let ((entry (car list)))
      (let ((tset (cons entry (<-assoc (car list) to))))
	(if (intersectp-equal aset tset)
	    (cons entry (intersect-sets-rec aset (cdr list) to))
	  (intersect-sets-rec aset (cdr list) to))))))

(defthm <-string-all-intersect-sets-rec
  (implies
   (<-string-all a list)
   (<-string-all a (intersect-sets-rec aset list to))))

(def::signature intersect-sets-rec (t <-string-listp <-pkg-symbol-name-listp) <-string-listp)

(defthm acl2-count-intersect-sets-rec
  (<= (acl2-count (intersect-sets-rec alist list to))
      (acl2-count list)))

(defun string-list-listp (x)
  (declare (type t x))
  (if (not (consp x)) (null x)
    (and (string-listp (car x))
	 (string-list-listp (cdr x)))))

(def::un intersect-sets (list to)
  (declare (xargs :signature ((string-listp <-pkg-symbol-name-listp) string-list-listp)))
  (if (endp list) nil
    (let ((tset (cons (car list) (<-assoc (car list) to))))
      (let ((set (intersect-sets-rec tset (cdr list) to)))
	(cons (cons (car list) set) (intersect-sets (cdr list) to))))))

(def::signature binary-append (string-listp string-listp) string-listp)

(def::un insert-iset (set list)
  (declare (xargs :signature ((string-listp string-list-listp) string-list-listp)))
  (if (endp list) (list set)
    (let ((entry (car list)))
      (if (intersectp-equal set entry)
	  (insert-iset (append set entry) (cdr list))
	(cons entry (insert-iset set (cdr list)))))))

(def::un max-iset (slist res)
  (declare (xargs :signature ((string-list-listp string-list-listp) string-list-listp)))
  (if (endp slist) res
    (let ((res (insert-iset (car slist) res)))
      (max-iset (cdr slist) res))))

(def::un one-from-each (list)
  (declare (xargs :signature ((string-list-listp) string-listp)))
  (if (endp list) nil
    (let ((entry (car list)))
      (if (consp entry) (cons (car entry) (one-from-each (cdr list)))
	(one-from-each (cdr list))))))

(def::un primitive-paths (list to)
  (declare (xargs :signature ((string-listp <-pkg-symbol-name-listp) <-string-listp)))
  (let ((slist (intersect-sets list to)))
    (let ((slist (max-iset slist nil)))
      (let ((list (one-from-each slist)))
	(sort-strings list)))))

(def::un primitive-conflict-list (clist to res)
  (declare (xargs :signature ((conflict-listp <-pkg-symbol-name-listp conflict-listp) conflict-listp)))
  (if (endp clist) res
    (let ((entry (car clist)))
      (let ((key (car entry))
	    (set (cdr entry)))
	(let ((set (primitive-paths set to)))
	  (primitive-conflict-list (cdr clist) to (acons key set res)))))))

(def::un keep-conflicts (clist)
  (declare (xargs :signature ((conflict-listp) conflict-listp)))
  (if (endp clist) nil
    (let ((entry (car clist)))
      (let ((set (cdr entry)))
	(if (< (len set) 2) (keep-conflicts (cdr clist))
	  (cons entry (keep-conflicts (cdr clist))))))))

(def::un total-same-directory-conflicts (clist res)
  (declare (xargs :signature ((conflict-listp natp) natp)))
  (if (endp clist) res
    (let ((entry (car clist)))
      (let ((set (cdr entry)))
	(let ((res (if (and (<= 2 (len set)) (any-same-directory-set set)) (1+ res) res)))
	  (total-same-directory-conflicts (cdr clist) res))))))

(set-state-ok t)

(defun read-objects-rec (channel res state)
  (declare (xargs :mode :program))
  (met ((eofp obj state) (read-object channel state))
    (if eofp (mv (revappend res nil) state)
      (read-objects-rec channel (cons obj res) state))))

(defun read-objects (channel state)
  (declare (xargs :mode :program))
  (read-objects-rec channel nil state))

(defun file-to-object-list (fname state)
  (declare (xargs :mode :program))
  (met ((channel state) (open-input-channel fname :object state))
    (if (not (open-input-channel-p channel :object state))
	(prog2$ (cw "File ~p0 does not exist~%" fname) (mv nil state))
      (met ((file state) (read-objects channel state))
	(let ((state (close-input-channel channel state)))
	  (mv file state))))))

(def::und identify-conflicts (clist to)
  (declare (xargs :signature ((conflict-listp <-pkg-symbol-name-listp) t)))
  (let ((clist (primitive-conflict-list clist to nil)))
    (let ((clist (keep-conflicts clist)))
      ;; If someone wanted to do something more with the conflict list
      ;; this is where that might happen ..
      (let ((n (len clist)))
	(let ((m (total-same-directory-conflicts clist 0)))
	  (progn$
	   (cw "Conflicts:~%~p0~%" clist)
	   (cw "Total conflicts: ~p0~%" n)
	   (cw "Total same-directory conflicts: ~p0~%" m)
	   ))))))

(defun analyze-files-rec (flist clist from to state)
  (declare (xargs :mode :program))
  (if (endp flist) (prog2$ (identify-conflicts clist to)
			   (mv nil nil state))
    (let ((fname (car flist)))
      (met ((plist state) (file-to-object-list fname state))
	(let ((check (wf-bookdata-listp plist)))
	  (progn$
	   (assert$ check "Malformed book data")
	   (met ((clist from to) (process-bookdata-list plist clist from to))
	     (analyze-files-rec (cdr flist) clist from to state))))))))

(defun analyze-files (flist state)
  (declare (xargs :mode :program))
  (analyze-files-rec flist nil nil nil state))
