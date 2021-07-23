(in-package "ACL2")

#|

  merge-intermediate.lisp
  ~~~~~~~~~~~~~~~~~~~~~~~

In this book, we define two other functional versions of qsort. Each goes one
step closer to the actual implementation we defined in programs.lisp, and we
prove the correspondence of each with the precious one. The idea is that in the
functions lower-part and upper-part we defined previously, we never really made
explicit the way the array looks after the split. We do it here using the
function merge-func. We also add a function walk, which explicitly models the
index returned by split-qs.

|#

(include-book "programs")
(include-book "intermediate-to-spec")
(include-book "first-last")

(local
(in-theory (enable len))
)

(defun merge-func (x splitter)
  (declare (xargs :measure (len x)))
  (if (endp x) nil
    (if (and (<<= splitter (first x))
	     (<< (last-val x) splitter))
	(cons (last-val x)
	      (snoc (merge-func (del-last (rest x))
				splitter)
		    (first x)))
	(if (and (<<= splitter (first x))
		 (<<= splitter (last-val x)))
	    (snoc (merge-func (del-last x) splitter)
		  (last-val x))
	  (if (and (<< (first x) splitter)
		   (<< (last-val x) splitter))
	      (cons (first x)
		    (merge-func (rest x) splitter))
	    (cons (first x)
		  (snoc (merge-func (del-last (rest x))
				    splitter)
			(last-val x))))))))

(defun walk (x splitter)
  (if (endp x) 0
    (if (and (<<= splitter (first x))
	     (<< (last-val x) splitter))
	(1+ (walk (del-last (rest x)) splitter))
      (if (and (<<= splitter (first x))
	       (<<= splitter (last-val x)))
	  (walk (del-last x) splitter)
	(if (and (<< (first x) splitter)
		 (<< (last-val x) splitter))
	    (1+ (walk (rest x) splitter))
	  (1+ (walk (del-last (rest x)) splitter)))))))


(defthm walk-is-a-natp
  (natp (walk x splitter)))


(local
(defthm walk-lower-part-reduction
  (equal (len (lower-part x splitter))
         (walk x splitter)))
)

(local
(defthm merge-func-lower-upper-reduction
  (equal (merge-func x splitter)
         (append (lower-part x splitter)
                 (upper-part x splitter))))
)

(local
(defthm reduce-merge-lower-part
  (equal (first-n (walk x splitter)
                  (merge-func x splitter))
         (lower-part x splitter))
  :hints (("Goal"
           :in-theory (disable walk merge-func lower-part upper-part)
           :use ((:instance append-first-reduction-len
                            (n (walk x splitter))
                            (z (merge-func x splitter))
                            (x (lower-part x splitter))
                            (y (upper-part x splitter)))))))
)

(local
(defthm reduce-merge-upper-part
  (equal (last-n (walk x splitter)
                  (merge-func x splitter))
         (upper-part x splitter))
  :hints (("Goal"
           :in-theory (disable walk merge-func lower-part upper-part)
           :use ((:instance append-last-reduction-len
                            (n (walk x splitter))
                            (z (merge-func x splitter))
                            (x (lower-part x splitter))
                            (y (upper-part x splitter)))))))
)

(local
(defthm walk-not-zp-implies-lower-part-consp
  (implies (not (zp (walk x splitter)))
           (consp (lower-part x splitter)))
  :rule-classes :forward-chaining)
)

(local
(defthm walk-zp-implies-lower-part-not-consp
  (implies (zp (walk x splitter))
           (not (consp (lower-part x splitter))))
  :rule-classes :forward-chaining)
)

(local
(in-theory (disable walk-lower-part-reduction
                    first-len-reduction))
)

(local
(in-theory (disable len walk merge-func))
)

(local (in-theory

; Matt K.: Added for v2-9, because of the change to rewrite-clause that avoids
; using forward-chaining facts derived from a literal that has been rewritten.
; Specifically, in order for (:FORWARD-CHAINING
; WALK-NOT-ZP-IMPLIES-LOWER-PART-CONSP) to fire during
; intermediate-in-situ-qsort-fn, we need ZP to stay around.  This disable is
; also needed for intermediate-in-situ-qsort-equal-qsort and perhaps other
; events.

        (disable zp-open)))

(defun intermediate-in-situ-qsort-fn (lst)
  (declare (xargs :measure (len lst)))
  (if (endp lst) nil
    (if (endp (rest lst))
	(list (first lst))
      (let ((merge (merge-func lst (first lst)))
	    (ndx (walk lst (first lst))))
	(if (zp ndx)
	    (cons (first lst)
		  (intermediate-in-situ-qsort-fn (rest lst)))
	  (append (intermediate-in-situ-qsort-fn (first-n ndx merge))
                  (intermediate-in-situ-qsort-fn (last-n ndx merge))))))))

(defthm intermediate-in-situ-qsort-equal-qsort
  (equal (intermediate-in-situ-qsort-fn x)
         (qsort-fn x))
  :hints (("Goal"
           :induct (intermediate-in-situ-qsort-fn x)
           :in-theory (disable reduce-merge-lower-part
                               reduce-merge-upper-part))
          ("Subgoal *1/4"
           :use ((:instance reduce-merge-lower-part
                            (splitter (car x)))
                 (:instance reduce-merge-upper-part
                            (splitter (car x)))))))


(in-theory (disable intermediate-in-situ-qsort-equal-qsort))

(local
(defthm merge-func-is-a-permutation
  (perm (merge-func x splitter)
        x))
)

(defun in-situ-qsort-fn (lst)
  (declare (xargs :measure (len lst)
                  :hints (("Goal"
                           :in-theory (disable
                                       reduce-merge-lower-part
                                       reduce-merge-upper-part
                                       merge-func-lower-upper-reduction))
                          ("Subgoal 3"
                           :in-theory (enable
                                       reduce-merge-lower-part
                                       reduce-merge-upper-part
                                       merge-func-lower-upper-reduction))
                          ("Subgoal 2"
                           :in-theory (enable len)
                           :use ((:instance perm-len-reduction
                                            (x (merge-func lst (car lst)))
                                            (y  lst))))
                           ("Subgoal 1"
                            :in-theory (enable
                                        reduce-merge-lower-part
                                        reduce-merge-upper-part
                                        merge-func-lower-upper-reduction)))))
  (if (endp lst) nil
    (if (endp (rest lst))
	(list (first lst))
      (let ((merge (merge-func lst (first lst)))
	    (ndx (walk lst (first lst))))
	(if (zp ndx)
	    (cons (first merge)
		  (in-situ-qsort-fn (rest merge)))
          (let* ((upper (in-situ-qsort-fn (last-n ndx merge)))
                 (lower (in-situ-qsort-fn (first-n ndx
                                                   merge))))
            (append lower upper)))))))

(local
(defthm append-null-reduction
  (implies (and (equal z (append x y))
                (not (consp x)))
           (equal z y))
  :rule-classes :forward-chaining)
)

(local
(defthm merge-func-equal-x-if-walk-0
  (implies (and (zp (walk x (first x)))
                (true-listp x))
           (equal (merge-func x (first x))
                  x))
  :hints (("Goal"
           :use if-lower-is-endp-upper-is-the-actual-list))
  :rule-classes :forward-chaining)
)

(local
(defthm natp-walk-exploited
  (implies (zp (walk x splitter))
           (equal (walk x splitter)
                  0))
  :rule-classes :forward-chaining)
)

(local
(defthm merge-fn-is-true-listp
  (implies (true-listp x)
           (true-listp (merge-func x splitter)))
  :hints (("Goal"
           :in-theory (enable merge-func))))
)

(local
(in-theory (disable reduce-merge-lower-part
                    reduce-merge-upper-part
                    merge-func-lower-upper-reduction))
)

(local
 (defthm merge-func-equal-x-if-walk-0-rewrite

; Added by Matt K. for v2-9, because forward-chaining rule
; merge-func-equal-x-if-walk-0 is no longer firing during the proof of
; in-situ-equal-intermediate, presumably because of the change to
; rewrite-clause that avoids using forward-chaining facts derived from a
; literal that has been rewritten.

   (implies (and (zp (walk x (first x)))
                 (true-listp x))
            (equal (merge-func x (first x)) x))))

(defthm in-situ-equal-intermediate
  (implies (true-listp x)
           (equal (in-situ-qsort-fn x)
                  (intermediate-in-situ-qsort-fn x))))

(in-theory (disable in-situ-equal-intermediate))
