#|

Typed records in ACL2

This file contains an enhancement to the ACL2 standard "records" book.
We introduce the macro "defrecord" to define an accessor and updater
function for a record structure with elements of a particular type.
This facility extends somewhat the hypothesis-less theorems of the
standard ACL2 "records" book.  Besides providing a convenient way to
introduce multiple record structures, this macro adds a theorem to the
theorems provided by that book: namely, that the accessor function
returns values of the right "type".

For example,

  (include-book ;; defeat dependency checker
     "XXX/books/misc/records")

  (defun sbp16 (x)
    (declare (xargs :guard t))
    (and
     (integerp x)
     (<= (- (expt 2 15)) x)
     (< x (expt 2 15))))

  (defun fix-sbp16 (x)
    (declare (xargs :guard t))
    (if (sbp16 x) x 0))

  (defrecord sbp :rd getbv :wr putbv :fix fix-sbp16 :typep sbp16)

The "raw" record structure introduced in the standard records book is
used to define records defined using defrecord, and the functions for
accessing and updating a record that are introduced by defrecord are
proved to have many of the same properties as the records in the
standard records book.  In particular, assume that the record
introduced by defrecord has operations (g a r) and (s a v r) that get
and set elements of record r for address a and value v.  We prove the
following lemmas, each of which also holds of "raw" records:

(defthm g-same-s
  (equal (g a (s a v r))
         v))

(defthm g-diff-s
  (implies (not (equal a b))
           (equal (g a (s b v r))
                  (g a r))))

(defthm s-same-g
  (equal (s a (g a r) r)
         r))

(defthm s-same-s
  (equal (s a y (s a x r))
         (s a y r)))

(defthm s-diff-s
  (implies (not (equal a b))
           (equal (s b y (s a x r))
                  (s a x (s b y r))))
  :rule-classes ((:rewrite :loop-stopper ((b a s)))))

In addition, the defrecord macro proves one additional lemma that is
not provable about raw records:

(defthm typep-g
  (typep (g a r)))

for a typep predicate provided by the user.

What makes this implementation of records interesting is that it has
the peculiar property that each of the lemmas has no "type"
hypotheses.  This makes reasoning about operations considerably
easier, but the implementation of the record operations is obscure, to
say the least.  We are interested in providing an implementation to
show that the theorems listed above are consistent.

(Historical Note: Matt Kaufmann of AMD proposed a challenge problem to
the ACL2 list in March, 2000 to define a "get" and "set" function
without hypotheses, based on a request of Rob Sumner's.  Kaufmann
released his version, which uses a bizarre record implementation to
avoid the type hypotheses.  (We posted our independantly-derived
solution to the challenge to the ACL2 list in Mar 2000, which uses a
strikingly similar approach.  Is there basically only one way to
implement these functions?)  An improved version that exploits the
total order of ACL2 objects was developed by Kaufmann and Sumners and
presented at the 2002 ACL2 workshop, and this book is incorporated
into the standard ACL2 books.  In 2002 we realized that we needed data
element type information - for example, that a memory returns only
bit-vectors - and wanted to continue to avoid unnecessary hypotheses.
This led us to create this enhancement.)

David Greve and Matt Wilding
November 2002

|#

(in-package "ACL2")

(include-book "misc/records" :dir :system)

(encapsulate
 ()

 (local
  (encapsulate
   ()

   ;from record.lisp

   (defthm s-aux-is-bounded
     (implies (and (rcdp r)
		   (s-aux a v r)
		   (<< e a)
		   (<< e (caar r)))
	      (<< e (caar (s-aux a v r)))))

   (defthm s-aux-preserves-rcdp
     (implies (rcdp r)
	      (rcdp (s-aux a v r))))

   (defthm rcdp-implies-true-listp
     (implies (rcdp x)
	      (true-listp x))
     :rule-classes (:forward-chaining
		    :rewrite))

   (defthm g-aux-same-s-aux
     (implies (rcdp r)
	      (equal (g-aux a (s-aux a v r))
		     v)))

   (defthm g-aux-diff-s-aux
     (implies (and (rcdp r)
		   (not (equal a b)))
	      (equal (g-aux a (s-aux b v r))
		     (g-aux a r))))

   (defthm s-aux-same-g-aux
     (implies (rcdp r)
	      (equal (s-aux a (g-aux a r) r)
		     r)))

   (defthm s-aux-same-s-aux
     (implies (rcdp r)
	      (equal (s-aux a y (s-aux a x r))
		     (s-aux a y r))))

   (defthm s-aux-diff-s-aux
     (implies (and (rcdp r)
		   (not (equal a b)))
	      (equal (s-aux b y (s-aux a x r))
		     (s-aux a x (s-aux b y r))))
     :rule-classes ((:rewrite :loop-stopper ((b a s)))))

   (defthm s-aux-non-nil-cannot-be-nil
     (implies (and v (rcdp r))
	      (s-aux a v r)))

   (defthm g-aux-is-nil-for-<<
     (implies (and (rcdp r)
		   (<< a (caar r)))
	      (equal (g-aux a r) nil)))

   (in-theory (enable acl2->rcd rcd->acl2))

   (defthm acl2->rcd-rcd->acl2-of-rcdp
     (implies (rcdp x)
	      (equal (acl2->rcd (rcd->acl2 x))
		     x)))

   (defthm acl2->rcd-returns-rcdp
     (rcdp (acl2->rcd x)))

   (defthm acl2->rcd-preserves-equality
     (iff (equal (acl2->rcd x) (acl2->rcd y))
	  (equal x y)))

   (defthm rcd->acl2-acl2->rcd-inverse
     (equal (rcd->acl2 (acl2->rcd x)) x))

   (defthm rcd->acl2-of-record-non-nil
     (implies (and r (rcdp r))
	      (rcd->acl2 r)))

   (in-theory (disable acl2->rcd rcd->acl2))

   (defthm s-aux-preserves-rcdp
     (implies (rcdp r)
	      (rcdp (s-aux a v r))))

   (defthm rcdp-implies-true-listp
     (implies (rcdp x)
	      (true-listp x))
     :rule-classes (:forward-chaining
		    :rewrite))

   ;-------------------------------------------------------------

   (defun s-g-induction (a r1 r2)
     (if (and (or (endp r1) (<< a (caar r1))) t)
	 nil
       (if (equal a (caar r1))
	   (equal r2 r2)
	 (s-g-induction a (cdr r1) (cdr r2)))))

   (defthm s-aux==r-aux-lemma
     (implies (and (rcdp r1)
		   (rcdp r2)
		   (not (equal r1 (s-aux a (g-aux a r1) r2))))
	      (not (equal (s-aux a 0 r2) (s-aux a 0 r1))))
     :hints (("goal" :induct (s-g-induction a r1 r2))))

   (defthm s-aux==r-aux
     (implies (and (syntaxp (not (equal v '(quote 0))))
		   (rcdp r1)
		   (rcdp r2))
	      (iff (equal r1 (s-aux a v r2))
		   (and (equal v (g-aux a r1))
			(equal (s-aux a 0 r2)
			       (s-aux a 0 r1))))))

   (defthm rcd->acl2-preserves-equality
     (implies (and (rcdp x) (rcdp y))
	      (iff (equal (rcd->acl2 x) (rcd->acl2 y))
		   (equal x y)))
     :hints (("goal" :in-theory (enable rcd->acl2))))

   (defthm worht
     (implies (rcdp y)
	      (iff (equal x (rcd->acl2 y))
		   (equal (acl2->rcd x) y))))

   ))

 (defthm s==r
   (implies (syntaxp (not (equal v '(quote 0))))
	    (and (iff (equal (s a v r2) r1)
		      (and (equal v (g a r1))
			   (equal (s a 0 r2)
				  (s a 0 r1))))
		 (iff (equal r1 (s a v r2))
		      (and (equal v (g a r1))
			   (equal (s a 0 r1)
				  (s a 0 r2))))))
   :hints (("goal" :in-theory (e/d (s g)))
	   ))

 (defthm equal-s-record-equality
   (implies
    (and
     (equal rec2 rec1)
     (equal v (g a rec1)))
    (and (iff (equal rec1 (s a v rec2)) t)
	 (iff (equal (s a v rec2) rec1) t))))

 )

(encapsulate
 ()

 (local
  (encapsulate
   ()

   (defthm s-aux-non-nil-cannot-be-nil
     (implies (and v (rcdp r))
	      (s-aux a v r)))

   (defthm cdr-s-aux
     (equal (cdr (s-aux a v r))
	    (cdr (cond ((or (endp r) (<< a (caar r)))
			(if v (cons (cons a v) r) r))
		       ((equal a (caar r))
			(if v (cons (cons a v) (cdr r))
			  (cdr r)))
		       (t (cons (car r) (s-aux a v (cdr r))))))))

   (defun len-len-induction (r1 r2)
     (if (or (endp r1) (endp r2)) nil
       (cons (cons (car r1) (car r2)) (len-len-induction (cdr r1) (cdr r2)))))

   (defthm s-aux-equal-differential
     (implies (and (rcdp rcd1)
		   (rcdp rcd2)
		   (equal (s-aux a v rcd1)
			  (s-aux a v rcd2))
		   (not (equal rcd1 rcd2)))
	      (iff (equal (g-aux a rcd1)
			  (g-aux a rcd2)) nil))
     :hints (("goal" :induct (len-len-induction rcd1 rcd2))))

   (defthm rcd->acl2-preserves-equality
     (implies
      (and
       (rcdp x)
       (rcdp y))
      (iff (equal (rcd->acl2 x) (rcd->acl2 y))
	   (equal x y)))
     :hints (("goal" :in-theory (enable rcd->acl2))))

   (defthm car-s-aux
     (equal (car (s-aux a v r))
	    (car (cond ((or (endp r) (<< a (caar r)))
			(if v (cons (cons a v) r) r))
		       ((equal a (caar r))
			(if v (cons (cons a v) (cdr r))
			  (cdr r)))
		       (t (cons (car r) (s-aux a v (cdr r))))))))

   (defthm s-aux-preserves-rcdp
     (implies
      (rcdp r)
      (rcdp (s-aux a v r))))

   (defthm rcdp-acl2->rcd
     (rcdp (acl2->rcd x))
     :hints (("goal" :in-theory (enable acl2->rcd))))

   (defthm acl2->rcd-preserves-equality
     (implies
      (syntaxp (symbolp x))
      (iff (equal x y)
	   (equal (acl2->rcd x) (acl2->rcd y))))
     :hints (("goal" :in-theory (enable acl2->rcd))))

   (defthm s-equal-differential-g
     (implies (and (equal (s a v rcd1)
			  (s a v rcd2))
		   (not (equal rcd1 rcd2)))
	      (iff (equal (g a rcd1)
			  (g a rcd2)) nil))
     :hints (("goal" :in-theory (enable s g))))

   (defthm s-equal-differential-v
     (implies (and (equal (s a v1 rcd1)
			  (s a v2 rcd2))
		   (not (equal rcd1 rcd2)))
	      (iff (equal v1 v2) t)))

   ))

 (defthm s-equal-differential
   (implies (and (equal (s a v1 rcd1)
			(s a v2 rcd2))
		 (not (equal rcd1 rcd2)))
	    (and (iff (equal v1 v2) t)
		 (iff (equal (g a rcd1)
			     (g a rcd2)) nil)))
   :hints (("goal" :in-theory nil
	    :use ((:instance s-equal-differential-g (v v2))
		  (:instance s-equal-differential-v)))))

 (defthm g-s-differential
   (implies
    (and
     (not (equal rcd1 rcd2))
     (equal (g a rcd1) (g a rcd2)))
    (iff (equal (s a v rcd1)
		(s a v rcd2)) nil))
   :hints (("goal" :in-theory nil
	    :use ((:instance s-equal-differential (v1 v) (v2 v))))))

 )

(defun symbol-list-to-string (list)
  (declare (type (satisfies symbol-listp) list))
  (if (consp list)
      (concatenate 'string (symbol-name (car list)) (symbol-list-to-string (cdr list)))
    ""))

(defmacro join-symbols (witness &rest rst)
  `(intern-in-package-of-symbol (symbol-list-to-string (list ,@rst)) ,witness))

(defmacro defrecord (name &key (rd 'nil) (wr 'nil) (fix 'ifix) (default 'nil) (typep 'integerp))

  (let* ((base name)
	 (default (if (null default) `(,fix nil) default))
	 (rd  (if (null rd) (join-symbols name name '-rd) rd))
	 (wr  (if (null wr) (join-symbols name name '-wr) wr))
	 (wf  (join-symbols name 'wf-  typep))
	 (zp  (join-symbols name typep '-zp))
	 (wf-forward (join-symbols name wf '-forward))
	 )

    `(encapsulate
      ()

      (defun ,zp (x)
	(declare (type t x))
	(equal (,fix x) ,default))

      (defun ,wf (x)
	(declare (type t x))
	(and (consp x)
	     (,typep (car x))
	     (not (,zp (car x)))
	     (not (,wf (cdr x)))))

      (in-theory (disable (,zp) (,wf)))

      (defthm ,wf-forward
	(implies (,wf x)
		 (and (consp x)
		      (,typep (car x))
		      (not (,zp (car x)))
		      (not (,wf (cdr x)))))
	:rule-classes (:forward-chaining))

      (defun ,wr (a v m)
	(declare (type t a v m))
	(let ((x (g a m)))
	  (if (,wf x)
	      (if (,zp v)
		  (s a (cdr x) m)
		(s a (cons (,fix v) (cdr x)) m))
	    (if (,zp v) m
	      (s a (cons (,fix v) x) m)))))

      (defun ,rd (a m)
	(declare (type t a m))
	(let ((x (g a m)))
	  (if (,wf x) (car x)
	    ,default)))


      (defthm ,(join-symbols base rd '-same- wr '-hyps)
	(implies (equal a b)
		 (equal (,rd a (,wr b v r))
			(,fix v))))

      (defthm ,(join-symbols base rd '-diff- wr '-hyps)
	(implies (not (equal a b))
		 (equal (,rd a (,wr b v r))
			(,rd a r))))

      (defthm ,(join-symbols base wr '-same- rd '-hyps)
	(implies (equal a b)
		 (equal (,wr a (,rd b r) r)
			r)))

      (defthm ,(join-symbols base wr '-diff- wr '-hyps)
	(implies (not (equal a b))
		 (equal (,wr b y (,wr a x r))
			(,wr a x (,wr b y r))))
	:rule-classes ((:rewrite :loop-stopper ((b a ,wr)))))

      (defthm ,(join-symbols base wr '-same- wr '-hyps)
	(implies (equal a b)
		 (equal (,wr a y (,wr b x r))
			(,wr a y r))))

      (defthm ,(join-symbols base rd '-of- wr '-redux)
	(equal (,rd a (,wr b v r))
	       (if (equal b a) (,fix v)
		 (,rd a r)))
	:hints (("goal" :in-theory (disable ,fix ,rd ,wr))))

      (defthm ,(join-symbols base wr '-same- rd)
	(equal (,wr a (,rd a r) r)
	       r))

      (defthm ,(join-symbols base wr '-same- wr)
	(equal (,wr a y (,wr a x r))
	       (,wr a y r)))

      (defthm ,(join-symbols base typep '- rd)
	(and (,typep (,rd a r))
	     (equal (,fix (,rd a r))
		    (,rd a r))))

      (defun ,(join-symbols base wr '==r-hyp) (v a r)
	(declare (type t v a r))
	(equal (,fix v) (,rd a r)))

      (defthm ,(join-symbols base wr '==r)
	(implies
	 (and
	  (,(join-symbols base wr '==r-hyp) v a r1)
	  (equal r2 r1))
	 (and (iff (equal r1 (,wr a v r2)) t)
	      (iff (equal (,wr a v r2) r1) t))))

      (defun ,(join-symbols base wr '== wr '-hyp) (v1 v2)
	(declare (type t v1 v2))
	(equal (,fix v1) (,fix v2)))

      (in-theory (disable (,(join-symbols base wr '== wr '-hyp))))

      (defthm ,(join-symbols base wr '== wr)
	(implies
	 (and
	  (equal a1 a2)
	  (,(join-symbols base wr '== wr '-hyp) v1 v2)
	  (equal r2 r1))
	 (iff (equal (,wr a1 v1 r1) (,wr a2 v2 r2)) t)))

      (defthm ,(join-symbols base wr '==r!)
	(implies
	 (syntaxp (not (equal v '(quote 0))))
	 (and (iff (equal r1 (,wr a v r2))
		   (and (equal (,rd a r1) (,fix v))
			(equal (,wr a 0 r1)
			       (,wr a 0 r2))))
	      (iff (equal (,wr a v r2) r1)
		   (and (equal (,fix v) (,rd a r1))
			(equal (,wr a 0 r2)
			       (,wr a 0 r1)))))))

      (in-theory (disable ,(join-symbols base wr '==r!)
			  ,(join-symbols base rd '-of- wr '-redux)
			  ,rd ,wr))

      )))

(defmacro defthing (name &key (rd 'nil) (wr 'nil) (fix 'ifix) (default 'nil) (typep 'integerp))

  (let* ((base name)
	 (default (if (null default) `(,fix nil) default))
	 (rd  (if (null rd) (join-symbols name name '-rd) rd))
	 (wr  (if (null wr) (join-symbols name name '-wr) wr))
	 (wf  (join-symbols name 'wf-  typep))
	 (zp  (join-symbols name typep '-zp))
	 (wf-forward (join-symbols name wf '-forward))
	 )

    `(encapsulate
      ()

      (defun ,zp (x)
	(declare (type t x))
	(equal (,fix x) ,default))

      (defun ,wf (x)
	(declare (type t x))
	(and (consp x)
	     (,typep (car x))
	     (not (,zp (car x)))
	     (not (,wf (cdr x)))))

      (in-theory (disable (,zp) (,wf)))

      (defthm ,wf-forward
	(implies (,wf x)
		 (and (consp x)
		      (,typep (car x))
		      (not (,zp (car x)))
		      (not (,wf (cdr x)))))
	:rule-classes (:forward-chaining))

      (defun ,wr (v x)
	(declare (type t v x))
	(if (,wf x)
	    (if (,zp v)
		(cdr x)
	      (cons (,fix v) (cdr x)))
	  (if (,zp v) x
	    (cons (,fix v) x))))

      (defun ,rd (x)
	(declare (type t x))
	(if (,wf x) (car x)
	  ,default))


      (defthm ,(join-symbols base rd '-same- wr)
	(equal (,rd (,wr v r))
	       (,fix v)))

      (defthm ,(join-symbols base wr '-same- rd)
	(equal (,wr (,rd r) r)
	       r))

      (defthm ,(join-symbols base wr '- wr)
	(equal (,wr y (,wr x r))
	       (,wr y r)))

      (defthm ,(join-symbols base typep '- rd)
	(and (,typep (,rd r))
	     (equal (,fix (,rd r))
		    (,rd r))))

      (defthm ,(join-symbols base wr '==r)
	(implies
	 (syntaxp (not (equal v '(quote 0))))
	 (and (iff (equal r1 (,wr v r2))
		   (and (equal (,rd r1) (,fix v))
			(equal (,wr 0 r1) (,wr 0 r2))))
	      (iff (equal (,wr v r2) r1)
		   (and (equal (,fix v) (,rd r1))
			(equal (,wr 0 r2) (,wr 0 r1)))))))


      (in-theory (disable ,rd ,wr))

      )))
