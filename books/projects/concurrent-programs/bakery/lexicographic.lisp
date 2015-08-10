(in-package "ACL2")

#|

  lexicographic.lisp
  ~~~~~~~~~~~~~~~~~~

In this book, we define a lexicographic ordering of pairs, of which the first
one is guaranteed to be an integer. This ordering is used normally in a bakery
implementation. Since the domain of the second element of the pair is unknown,
we use the ACL2 total order for defining the order on this element.

|#

(include-book "misc/total-order" :dir :system)
(include-book "measures")

(defun lex< (p q r s)
  (or (< p r)
      (and (equal p r)
	   (<< q s))))

(defthm lex<-asymmetric
  (implies (lex< a b c d)
	   (not (lex< c d a b))))

(defthm lex<-transitive
  (implies (and (lex< a b c d)
		(lex< c d e f))
	   (lex< a b e f)))

(defthm lex<-total
  (implies (and (natp a)
                (natp c)
		(not (equal b d)))
	   (implies (not (lex< a b c d))
		    (lex< c d a b))))

(defthm lex<-1+-reduction
  (implies (lex< a b c d)
           (lex< (1+ a) b (1+ c) d)))

(in-theory (disable lex<))