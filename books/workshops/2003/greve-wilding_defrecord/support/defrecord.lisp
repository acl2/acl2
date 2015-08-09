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

  (include-book  ;; defeat dependency checker
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

(include-book "../../../../misc/records")

(defthm equal-s-record-equality
  (implies
   (and
    (equal rec2 rec1)
    (equal v (g a rec1)))
   (and (iff (equal rec1 (s a v rec2)) t)
	(iff (equal (s a v rec2) rec1) t))))

(defun symbol-list-to-string (list)
  (declare (type (satisfies symbol-listp) list))
  (if (consp list)
      (concatenate 'string (symbol-name (car list)) (symbol-list-to-string (cdr list)))
    ""))

(defmacro join-symbols (witness &rest rst)
  `(intern-in-package-of-symbol (symbol-list-to-string (list ,@rst)) ,witness))

(defmacro defrecord (name &key (rd 'nil) (wr 'nil) (fix 'ifix) (default '0) (typep 'integerp))

  (let* ((base name)
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

      (in-theory (disable ,(join-symbols base rd '-of- wr '-redux)
			  ,rd ,wr))

      )))
