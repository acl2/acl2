(in-package "ACL2")

#|

  extraction.lisp
  ~~~~~~~~~~~~~~~

Notice that out proof is about (extract-qs lo hi qs). We prove a number of
properties here, for extract-qs, and will be using them randomly. Most of the
properties here are explicitly telling ACL2 how to work with extract-qs.

|#

(include-book "programs")
(include-book "intermediate-program")
(include-book "first-last")

(local
(defthm arith-001
  (implies (and (not (natp (1- hi)))
                (natp hi))
           (equal hi 0))
  :rule-classes :forward-chaining)
)

(defthm extract-qs-expand-to-nil
  (implies (natp x)
           (equal (extract-qs (1+ x) x qs) ()))
  :hints (("Goal" :expand (extract-qs (1+ x) x qs))))

(defthm extract-qs-expand-to-list
  (implies (and (natp x)
                (>= x 0))
           (equal (extract-qs x x qs)
                  (list (objsi x qs))))
  :hints (("Goal" :expand (extract-qs x x qs))))


(defthm extract-qs-decrement-hi
  (implies (and (syntaxp (symbolp hi))
                (natp hi)
                (natp lo)
                (>= hi 0)
                (<= lo hi))
           (equal (extract-qs lo hi qs)
                  (snoc (extract-qs lo (1- hi) qs)
                        (objsi hi  qs)))))

(defthm extract-qs-returns-true-listp
  (true-listp (extract-qs lo hi qs)))


(defthm del-last-snoc-reduction
  (implies (true-listp x)
	   (equal (del-last (snoc x e)) x)))

(defthm last-val-snoc-reduction
  (equal (last-val (snoc x e)) e))

(defthm extract-qs-update-above-reduction
  (implies (and (natp hi)
		(natp i)
		(> i hi))
  (equal (extract-qs lo hi (update-objsi i e qs))
	 (extract-qs lo hi qs))))

(defthm extract-qs-update-below-reduction
  (implies (and (natp lo)
		(natp i)
		(< i lo))
	   (equal (extract-qs lo hi (update-objsi i e qs))
		  (extract-qs lo hi qs))))

(local
(in-theory (disable extract-qs-decrement-hi))
)

(local
(in-theory (enable len))
)

(defthm extract-qs-len-reduction
  (implies (and (natp lo)
                (natp hi)
                (<= lo hi))
           (equal (len (extract-qs lo hi qs))
                  (1+ (- hi lo)))))

(defthm extract-is-append-of-mid
  (implies (and (natp lo)
                (natp mid1)
                (natp hi)
                (<= lo mid1)
                (equal mid2 (1+ mid1))
                (<= mid1 hi))
           (equal (extract-qs lo hi qs)
                  (append (extract-qs lo mid1 qs)
                          (extract-qs mid2 hi qs))))
  :rule-classes nil)

(defthm consp-extract-reduction
  (implies (and (syntaxp (symbolp lo))
                (natp lo)
                (natp hi)
                (<= lo hi))
           (equal (extract-qs lo hi qs)
                  (cons (objsi lo qs)
                        (extract-qs (1+ lo) hi qs)))))

(defthm extract-for-1-element
  (implies (and (not (consp (rest (extract-qs lo hi qs))))
                (consp (extract-qs lo hi qs))
                (natp lo)
                (natp hi))
             (equal lo hi))
  :hints (("Subgoal *1/2"
           :expand (extract-qs (1+ lo) hi qs)))
  :rule-classes :forward-chaining)

(in-theory (disable extract-for-1-element
                    consp-extract-reduction))

