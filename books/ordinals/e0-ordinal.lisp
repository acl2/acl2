#|
this book is here for doing old-style termination proofs. if you
need to use the old ordinals, simply include this book and run
the command

(set-well-founded-relation e0-ord-<)

See the end of this file for documentation of E0-ORD-< and E0-ORDINALP.

|#

(in-package "ACL2")
(include-book "ordinal-definitions")
(local (include-book "ordinal-isomorphism"))

(defun e0-ord-< (x y)

  ":Doc-Section ACL2::ACL2-built-ins

   the old ordering function for ACL2 ordinals~/

   ~l[o<] for the current new ordering function for ACL2 ordinals.~/

   The functions ~c[e0-ordinalp] and ~ilc[e0-ord-<] were replaced in ACL2
   Version_2.8 by ~ilc[o-p] and ~ilc[o<], respectively.  However, books created
   before that version used the earlier functions for termination proofs; the
   old functions might be of use in these cases.  To use the old functions in
   termination proofs, include the community book ~c[books/ordinals/e0-ordinal]
   and execute the event ~c[(set-well-founded-relation e0-ord-<)]
   (~pl[set-well-founded-relation]).  For a more thorough discussion of
   these functions, see the documentation at the end of community book
   ~c[books/ordinals/e0-ordinal.lisp]."

  (declare (xargs :guard t))
  (if (consp x)
      (if (consp y)
          (if (e0-ord-< (car x) (car y))
              t
              (if (equal (car x) (car y))
                  (e0-ord-< (cdr x) (cdr y))
                  nil))
          nil)
      (if (consp y)
          t
          (< (if (real/rationalp x) x 0)
             (if (real/rationalp y) y 0)))))

(defun e0-ordinalp (x)

  ":Doc-Section ACL2::ACL2-built-ins

   the old recognizer for ACL2 ordinals~/

   ~l[o-p] for the current recognizer for ACL2 ordinals.~/

   The functions ~c[e0-ordinalp] and ~ilc[e0-ord-<] were replaced in ACL2
   Version_2.8 by ~ilc[o-p] and ~ilc[o<], respectively.  However, books created
   before that version used the earlier functions for termination proofs; the
   old functions might be of use in these cases.  To use the old functions in
   termination proofs, include the community book ~c[books/ordinals/e0-ordinal]
   and execute the event ~c[(set-well-founded-relation e0-ord-<)]
   (~pl[set-well-founded-relation]).  For a more thorough discussion of
   these functions, see the documentation at the end of community book
   ~c[books/ordinals/e0-ordinal.lisp]."

  (declare (xargs :guard t))
  (if (consp x)
      (and (e0-ordinalp (car x))
           (not (equal (car x) 0))
           (e0-ordinalp (cdr x))
           (or (atom (cdr x))
               (not (e0-ord-< (car x) (cadr x)))))
    (and (integerp x)
         (>= x 0))))

(defun copyn (a n) 
  (declare (xargs :guard (natp n)))
  (if (zp n) 
      nil 
    (cons a (copyn a (1- n)))))

(defun ctoa (x)
  (declare (xargs :guard (o-p x)))
  (if (o-finp x)
      x
    (append (copyn (ctoa (o-first-expt x)) 
		   (o-first-coeff x))
            (ctoa (o-rst x)))))

(defthm ctoa-<-equiv
  (implies (and (o-p x)
		(o-p y))
	   (equal (e0-ord-< (ctoa x)
			    (ctoa y))
		  (o< x y))))

(defthm |oc.x  <=>  oa(ctoa.x)|
   (implies (o-p x) 
	    (e0-ordinalp (ctoa x)))
   :rule-classes ((:forward-chaining)
		  (:rewrite)))

; The following were added by Matt K. for v2-9.  It had previously been the
; case that after including the present book, ob+ is :ideal (guards not
; verified) even though it is called by atoc, which is :common-lisp-compliant
; (guards verified).
(verify-guards ocmp) ; needed for (verify-guards ob+)
(verify-guards ob+)

(defun atoc (a)
  (declare (xargs :guard (e0-ordinalp a)))
  (if (atom a)
      a
    (o+ (omega-term (atoc (car a)) 
		    1)
	(atoc (cdr a)))))

(defthm |oa.x  <=>  oc(atoc.x)|
  (implies (e0-ordinalp x)
	   (o-p (atoc x))))

(defthm atoc-<-equiv
  (implies (and (e0-ordinalp x)
		(e0-ordinalp y))
	   (equal (o< (atoc x)
		      (atoc y))
		  (e0-ord-< x y))))

(defthm e0-ordinal-well-founded-cnf
  (and (implies (e0-ordinalp x) (o-p (atoc x)))
       (implies (and (e0-ordinalp x)                       
                     (e0-ordinalp y)
                     (e0-ord-< x y))
                (o< (atoc x) (atoc y))))
  :rule-classes :well-founded-relation)

(in-theory (disable atoc ctoa))

#|
E0-ORD-<    the well-founded less-than relation on ordinals up to epsilon-0

If x and y are both e0-ordinalps (see *Note E0-ORDINALP::) then
(e0-ord-< x y) is true iff x is strictly less than y.  e0-ord-< is
well-founded on the e0-ordinalps.  When x and y are both nonnegative
integers, e0-ord-< is just the familiar "less than" relation (<).

e0-ord-< plays a key role in the formal underpinnings of the ACL2 logic.
In order for a recursive definition to be admissible it must be proved
to "terminate."  By terminate we mean that the arguments to the function
"get smaller" as the function recurses and this sense of size comparison
must be such that there is no "infinitely descending" sequence of ever
smaller arguments.  That is, the relation used to compare successive
arguments must be well-founded on the domain being measured.

The most basic way ACL2 provides to prove termination requires the user
to supply (perhaps implicitly) a mapping of the argument tuples into the
ordinals with some "measure" expression in such a way that the measures
of the successive argument tuples produced by recursion decrease
according to the relation e0-ord-<.  The validity of this method rests
on the well-foundedness of e0-ord-< on the e0-ordinalps.

Without loss of generality, suppose the definition in question
introduces the function f, with one formal parameter x (which might be a
list of objects).  Then we require that there exist a measure
expression, (m x), that always produces an e0-ordinalp.  Furthermore,
consider any recursive call, (f (d x)), in the body of the definition.
Let hyps be the conjunction terms (each of which is either the test of
an if in the body or else the negation of such a test) describing the
path through the body to the recursive call in question.  Then it must
be a theorem that

       (IMPLIES hyps (E0-ORD-< (m (d x)) (m x))).

When we say e0-ord-< is "well-founded" on the e0-ordinalps we mean that
there is no infinite sequence of e0-ordinalps such that each is smaller
than its predecessor in the sequence.  Thus, the theorems that must be
proved about f when it is introduced establish that it cannot recur
forever because each time a recursive call is taken (m x) gets smaller.
From this, and the syntactic restrictions on definitions, it can be
shown (as on page 44 in "A Computational Logic", Boyer and Moore,
Academic Press, 1979) that there exists a function satisfying the
definition; intuitively, the value assigned to any given x by the
alleged function is that computed by a sufficiently large machine.
Hence, the logic is consistent if the axiom defining f is added.

See *Note E0-ORDINALP:: for a discussion of the ordinals and how to
compare two ordinals.

The definitional principle permits the use of relations other than
e0-ord-< but they must first be proved to be well-founded on some
domain.  See *Note WELL-FOUNDED-RELATION::.  Roughly put, alternative
relations are shown well-founded by providing an order-preserving
mapping from their domain into the ordinals.  See *Note DEFUN:: for
details on how to specify which well-founded relation is to be used.
|#

#|
E0-ORDINALP    a recognizer for the ordinals up to epsilon-0

Using the nonnegative integers and lists we can represent the ordinals
up to epsilon-0.  The ACL2 notion of ordinal is the same as that found
in nqthm-1992 and both are very similar to the development given in "New
Version of the Consistency Proof for Elementary Number Theory" in The
Collected Papers of Gerhard Gentzen, ed. M.E. Szabo, North-Holland
Publishing Company, Amsterdam, 1969, pp 132-213.

The following essay is intended to provide intuition about ordinals.
The truth, of course, lies simply in the ACL2 definitions of e0-ordinalp
and e0-ord-<.

Very intuitively, think of each non-zero natural number as by being
denoted by a series of the appropriate number of strokes, i.e.,

     0             0
     1             |
     2             ||
     3             |||
     4             ||||
     ...           ...

Then "omega," here written as w, is the ordinal that might be written as

     w             |||||...,

i.e., an infinite number of strokes.  Addition here is just
concatenation.  Observe that adding one to the front of w in the picture
above produces w again, which gives rise to a standard definition of w:
w is the least ordinal such that adding another stroke at the beginning
does not change the ordinal.

We denote by w+w or w*2 the "doubly infinite" sequence that we might
write as follows.

     w*2           |||||... |||||... 

One way to think of w*2 is that it is obtained by replacing each stroke
in 2 (||) by w.  Thus, one can imagine w*3, w*4, etc., which leads
ultimately to the idea of "w*w," the ordinal obtained by replacing each
stroke in w by w.  This is also written as "omega squared" or w^2, or:

      2
     w             |||||... |||||... |||||... |||||... |||||... ...

We can analogously construct w^3 by replacing each stroke in w by w^2
(which, it turns out, is the same as replacing each stroke in w^2 by w).
That is, we can construct w^3 as w copies of w^2,

      3              2       2       2       2
     w              w  ...  w  ...  w  ...  w ... ...

Then we can construct w^4 as w copies of w^3, w^5 as w copies of w^4,
etc., ultimately suggesting w^w.  We can then stack omegas, i.e.,
(w^w)^w etc.  Consider the "limit" of all of those stacks, which we
might display as follows.

            .         
           .
          .
         w
        w
       w
      w
     w

That is epsilon-0.

Below we begin listing some ordinals up to epsilon-0; the reader can
fill in the gaps at his or her leisure.  We show in the left column the
conventional notation, using w as "omega," and in the right column the
ACL2 object representing the corresponding ordinal.

       ordinal            ACL2 representation

       0                  0
       1                  1
       2                  2
       3                  3
       ...                ...
       w                 '(1 . 0)
       w+1               '(1 . 1)
       w+2               '(1 . 2)
       ...                ...
       w*2               '(1 1 . 0)
       (w*2)+1           '(1 1 . 1)
       ...                ...
       w*3               '(1 1 1 . 0)
       (w*3)+1           '(1 1 1 . 1)
       ...                ...

        2
       w                 '(2 . 0)
       ...                ...

        2
       w +w*4+3          '(2 1 1 1 1 . 3)
       ...                ...

        3
       w                 '(3 . 0)
       ...                ...


        w
       w                 '((1 . 0) . 0)
       ...                ...

        w  99
       w +w  +4w+3       '((1 . 0) 99 1 1 1 1 . 3)
       ...                ...

         2
        w
       w                 '((2 . 0) . 0)

       ...                ...

         w
        w
       w                 '(((1 . 0) . 0) . 0)
       ...                ...

Observe that the sequence of e0-ordinalps starts with the nonnegative
integers.  This is convenient because it means that if a term, such as a
measure expression for justifying a recursive function (see *Note
E0-ORD-<::) must produce an e0-ordinalp it suffices for it to produce a
nonnegative integer.

The ordinals listed above are listed in ascending order.  This is the
ordering tested by e0-ord-<.

The "epsilon-0 ordinals" of ACL2 are recognized by the recursively
defined function e0-ordinalp.  The base case of the recursion tells us
that nonnegative integers are epsilon-0 ordinals.  Otherwise, an
epsilon-0 ordinal is a cons pair (o1 . o2), where o1 is a non-0
epsilon-0 ordinal, o2 is an epsilon-0 ordinal, and if o2 is not an
integer then its car (which, by the foregoing, must be an epsilon-0
ordinal) is no greater than o1.  Thus, if you think of a (non-integer)
epsilon-0 ordinal as a list, each element is an non-0 epsilon-0 ordinal,
the ordinals are listed in weakly descending order, and the final cdr of
the list is an integer.

The function e0-ord-< compares two epsilon-0 ordinals, x and y.  If both
are integers, e0-ord-< is just x<y.  If one is an integer and the other
is a cons, the integer is the smaller.  Otherwise, the ordinals in their
cars are compared recursively and determines which is smaller unless the
cars are equal, in which case the ordinals in their cdrs are compared.

Fundamental to ACL2 is the fact that e0-ord-< is well-founded on
epsilon-0 ordinals.  That is, there is no "infinitely descending chain"
of such ordinals.  See *Note PROOF-OF-WELL-FOUNDEDNESS::.


|#
