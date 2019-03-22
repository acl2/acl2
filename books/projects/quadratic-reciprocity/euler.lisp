;; David M. Russinoff
;; david@russinoff.com
;; http://www.russinoff.com

(in-package "RTL")

(local (include-book "support/euler"))

(set-enforce-redundancy t)
(set-inhibit-warnings "theory") ; avoid warning in the next event
(local (in-theory nil))

(include-book "fermat")

(defsection euler
  :parents (number-theory)
  :short "This book contains a proof of Euler's Criterion for quadratic residues"
  :long "This book contains a proof of Euler's Criterion for quadratic residues:
 If @('p') is an odd prime and @('m') is not divisible by @('p'), then
@({
   mod(m^((p-1)/2),p) = 1 if m is a quadratic residue mod p
                        p-1 if not.
})

 Along the way, we also prove Wilson's Theorem: If @('p') is prime, then
 @('mod((p-1)!,p) = p-1').

 Finally, as a consequence of Euler's Criterion, we derive the First
 Supplement to the Law of Quadratic Reciprocity: @('-1') is a quadratic
 residue mod @('p') iff @('mod(p,4) = 1').

 The proof depends on Fermat's Theorem:"

"Let @('p') be a prime, let @('m') be relatively prime to @('p'), and let @('0 < j < p').
 Then there exists a unique <tt>j'</tt> such that <tt>0 &lt; j' &lt; p</tt> and
<code>
         mod(j*j',p) = mod(m,p),
</code>
 called the associate of @('j') w.r.t. a mod @('p').
@(def associate)
@(thm associate-property)
@(thm associate-bnds)
@(thm associate-is-unique)
@(thm associate-of-associate)
@(thm associate-equal)
@(thm associate-square)"

(defund associate (j m p)
  (mod (* m (expt j (- p 2))) p))

(defthm associate-property
    (implies (and (primep p)
		  (integerp m)
		  (not (zp j))
		  (< j p)
		  (not (divides p m)))
	     (equal (mod (* (associate j m p) j) p)
		    (mod m p)))
  :rule-classes ())

(defthm associate-bnds
    (implies (and (primep p)
		  (integerp m)
		  (not (zp j))
		  (< j p)
		  (not (divides p m)))
	     (and (not (zp (associate j m p)))
		  (< (associate j m p) p)))
  :rule-classes (:forward-chaining))

(defthm associate-is-unique
    (implies (and (primep p)
		  (integerp m)
		  (not (zp j))
		  (< j p)
		  (not (divides p m))
		  (integerp x)
		  (equal (mod m p) (mod (* j x)	p)))
	     (equal (associate j m p) (mod x p)))
  :rule-classes ())

(defthm associate-of-associate
    (implies (and (primep p)
		  (integerp m)
		  (not (zp j))
		  (< j p)
		  (not (divides p m)))
	     (equal (associate (associate j m p) m p)
		    (mod j p))))

(defthm associate-equal
    (implies (and (primep p)
		  (integerp m)
		  (integerp j)
		  (not (divides p m))
		  (not (zp j))
		  (< j p)
		  (not (zp i))
		  (< i p))
	     (equal (equal (associate j m p) (associate i m p))
		    (equal i j))))

(defthm associate-square
    (implies (and (primep p)
		  (integerp m)
		  (not (divides p m))
		  (not (zp j))
		  (< j p))
	     (iff (= (associate j m p) j)
		  (= (mod (* j j) p) (mod m p))))
  :rule-classes ())

"If there exists @('x') such that @('mod(x*x,p) = mod(m,p)'), then @('m') is said to be
@('m') (quadratic) residue mod @('p')."

(defun find-root (n m p)
  (if (zp n)
      ()
    (if (= (mod (* n n) p) (mod m p))
	n
      (find-root (1- n) m p))))

(defund residue (m p)
  (not (null (find-root (1- p) m p))))

(defthm not-res-no-root-lemma
    (implies (and (not (find-root n m p))
                  (integerp m)
		  (not (zp n))
		  (not (zp j))
		  (<= j n))
	     (not (equal (mod (* j j) p) (mod m p))))
  :rule-classes ())

(defthm not-res-no-root
    (implies (and (primep p)
                  (integerp m)
		  (not (residue m p))
		  (not (zp j))
		  (< j p))
	     (not (equal (mod (* j j) p) (mod m p)))))

(defthm not-res-no-self-associate
    (implies (and (primep p)
		  (integerp m)
		  (not (divides p m))
		  (not (residue m p))
		  (not (zp j))
		  (< j p))
	     (not (equal (associate j m p) j)))
  :rule-classes ())

"If @('m') is a residue mod @('p'), then there are exactly 2 roots of
 @('mod(x*x,p) = mod(m,p)') in the range @('0 < x < p').
@(def root1)
@(thm res-root1)
@(def root2)
@(thm res-root2)
@(thm associate-roots)
@(thm only-2-roots)
@(thm roots-distinct)"

(defun root1 (m p)
  (find-root (1- p) m p))

(defthm res-root1
    (implies (and (primep p)
		  (residue m p))
	     (and (not (zp (root1 m p)))
		  (< (root1 m p) p)
		  (equal (mod (* (root1 m p) (root1 m p)) p) (mod m p))))
  :rule-classes ())

(defun root2 (m p)
  (- p (root1 m p)))

(defthm res-root2
    (implies (and (primep p)
		  (residue m p))
	     (and (not (zp (root2 m p)))
		  (< (root2 m p) p)
		  (equal (mod (* (root2 m p) (root2 m p)) p) (mod m p))))
  :rule-classes ())

(defthm root1-root2
    (implies (and (primep p)
		  (integerp m)
		  (residue m p))
	     (equal (mod (* (root1 m p) (root2 m p)) p)
		    (mod (- m) p))))

(defthm associate-roots
    (implies (and (primep p)
		  (integerp m)
		  (not (divides p m))
		  (residue m p))
	     (and (equal (associate (root1 m p) m p) (root1 m p))
		  (equal (associate (root2 m p) m p) (root2 m p))))
  :rule-classes ())

(defthm only-2-roots
    (implies (and (primep p)
		  (integerp m)
		  (not (divides p m))
		  (residue m p)
		  (not (zp j))
		  (< j p)
		  (= (associate j m p) j))
	     (or (= j (root1 m p))
		 (= j (root2 m p))))
  :rule-classes ())

(defthm roots-distinct
    (implies (and (primep p)
		  (not (= p 2))
		  (residue m p))
	     (not (= (root1 m p) (root2 m p))))
  :rule-classes ())

"For @('0 <= n < p'), we construct a list @('associates(n,m,p)') of distinct integers
between @('1') and @('p-1') with the following properties:
<ul>
  <li>If @('1 <= j <= n'), then @('j') is in @('associates(n,m,p)').</li>
  <li>If @('j') is in @('associates(n,m,p)'), then so is @('associate(j,m,p)').</li>
</ul>
@(def associates)
@(thm member-associates)"


(defun associates (n m p)
  (if (zp n)
      (if (residue m p)
	  (cons (root2 m p)
		(cons (root1 m p) ()))
	())
    (if (member n (associates (1- n) m p))
	(associates (1- n) m p)
      (cons (associate n m p)
	    (cons n (associates (1- n) m p))))))

(defthm member-associates
    (implies (and (primep p)
		  (integerp m)
		  (not (divides p m))
		  (integerp n)
		  (< n p)
		  (not (zp j))
		  (< j p))
	     (iff (member (associate j m p) (associates n m p))
		  (member j (associates n m p)))))

"We shall show that @('associates(p-1,m,p)') is a permutation of @('positives(p-1)').
@(thm subset-positives-associates)
@(thm member-self-associate)
@(thm distinct-positives-associates-lemma)
@(thm distinct-positives-associates)"

(defthm subset-positives-associates
    (subsetp (positives n) (associates n m p)))

(defthm member-self-associate
    (implies (and (primep p)
		  (integerp m)
		  (not (divides p m))
		  (not (zp j))
		  (< j p)
		  (equal (associate j m p) j))
	     (member j (associates n m p))))

(defthm distinct-positives-associates-lemma
    (implies (and (primep p)
		  (not (= p 2))
		  (integerp m)
		  (not (divides p m))
		  (integerp n)
		  (< n p))
	     (distinct-positives (associates n m p) (1- p)))
  :rule-classes ())

(defthm distinct-positives-associates
    (implies (and (primep p)
		  (not (= p 2))
		  (integerp m)
		  (not (divides p m)))
	     (distinct-positives (associates (1- p) m p) (1- p)))
  :rule-classes ())

"We shall require a variation of the pigeonhole principle.
@(thm pigeonhole-principle-2)
@(thm perm-associates-positives)"

(defthm pigeonhole-principle-2
    (implies (and (natp n)
		  (distinct-positives l n)
		  (subsetp (positives n) l))
	     (perm (positives n) l))
  :rule-classes ())

(defthm perm-associates-positives
    (implies (and (primep p)
		  (not (= p 2))
		  (integerp m)
		  (not (divides p m)))
	     (perm (positives (1- p))
		   (associates (1- p) m p)))
  :rule-classes ())

"It follows that the product of @('associates(p-1,m,p)') is @('(p-1)!') and its
length is @('p-1').
@(thm times-list-associates-fact)
@(thm perm-len)
@(thm len-positives)
@(thm len-associates)
@(thm len-associates-even)"

(defthm times-list-associates-fact
    (implies (and (primep p)
		  (not (= p 2))
		  (integerp m)
		  (not (divides p m)))
	     (equal (times-list (associates (1- p) m p))
		    (fact (1- p))))
  :rule-classes ())

(defthm perm-len
    (implies (perm l1 l2)
	     (= (len l1) (len l2)))
  :rule-classes ())

(defthm len-positives
    (equal (len (positives n))
	   (nfix n)))

(defthm len-associates
    (implies (and (primep p)
		  (not (= p 2))
		  (integerp m)
		  (not (divides p m)))
	     (equal (len (associates (+ -1 p) m p))
		    (1- p))))

(defthm len-associates-even
    (implies (and (primep p)
		  (not (= p 2))
		  (integerp m)
		  (not (divides p m))
		  (integerp n)
		  (< n p))
	     (integerp (* 1/2 (len (associates n m p)))))
  :rule-classes (:type-prescription))

"On the other hand, we can compute the product of @('associates(p-1,a,p)') as
follows.
@(thm times-list-associates)"

(defthm times-list-associates
    (implies (and (primep p)
		  (not (= p 2))
		  (integerp m)
		  (not (divides p m))
		  (< n p))
	     (equal (mod (times-list (associates n m p)) p)
		    (if (residue m p)
			(mod (- (expt m (/ (len (associates n m p)) 2))) p)
		      (mod (expt m (/ (len (associates n m p)) 2)) p))))
  :rule-classes ())

"Both Wilson's Theorem and Euler's Criterion now follow easily.
@(thm euler-lemma)
@(thm wilson)
@(thm euler-criterion)"

(defthm euler-lemma
    (implies (and (primep p)
		  (not (= p 2))
		  (integerp m)
		  (not (divides p m)))
	     (equal (mod (fact (1- p)) p)
		    (if (residue m p)
			(mod (- (expt m (/ (1- p) 2))) p)
		      (mod (expt m (/ (1- p) 2)) p))))
  :rule-classes ())

(defthm wilson
  (implies (primep p)
	   (equal (mod (fact (1- p)) p)
		  (1- p)))
  :rule-classes ())

(defthm euler-criterion
    (implies (and (primep p)
		  (not (= p 2))
		  (integerp m)
		  (not (divides p m)))
	     (equal (mod (expt m (/ (1- p) 2)) p)
		    (if (residue m p)
			1
		      (1- p))))
  :rule-classes ())

"The First Supplement is the case @('a = 1')
@(thm first-supplement)"

(defthm first-supplement
    (implies (and (primep p)
		  (not (= p 2)))
	     (iff (residue -1 p)
		  (= (mod p 4) 1)))
  :rule-classes ())

)
