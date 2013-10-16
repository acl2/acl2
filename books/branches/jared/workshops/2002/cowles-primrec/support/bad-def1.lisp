; Modified by Robert Krug from John Cowles's book bad-def.lisp.

(in-package "ACL2")

(defstub
    g (*) => *)

(defaxiom g-thm
  (implies (syntaxp (variablep n))
           (equal (g n)
                  (if (equal n 0)
                      nil
                    (cons nil (g (- n 1)))))))

(defthm
    len-cons
    (equal (len (cons x y))(+ 1 (len y))))

(set-irrelevant-formals-ok :warn)

(defun
    induct-hint (k n)
    (if (zp k)
	t
        (induct-hint (- k 1)(- n 1))))

(defthm
    g-at-neg-input
    (implies (and (< n 0)
		  (integerp k))
	     (> (len (g n)) k))
    :rule-classes nil
    :hints (("goal"
	     :induct (induct-hint k n))))


(defthm
    contradiction!!
    nil
    :rule-classes nil
    :hints (("Goal"
	     :use (:instance
		   g-at-neg-input
		   (n -1)
		   (k (len (g -1)))))))
