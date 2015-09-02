(in-package "ACL2")

;;; Define basic notions.
(include-book "riemann-defuns")

(include-book "riemann-lemmas")

(defun co-member (a x)
  ;; returns all members of x up to and including a
  (if (consp x)
      (if (equal a (car x))
          (list a)
        (cons (car x) (co-member a (cdr x))))
    nil))

(defthm append-member-co-member
  (implies (true-listp x)
           (equal (append (co-member a x)
                          (cdr (member a x)))
                  x)))

;;; Perhaps the following belongs in riemann-lemmas.lisp, but I'm
;;; concerned about the possibility of looping.
;;; Perhaps it (and len-cdr-map-rcfn-refinement) are not needed at
;;; all.  They orinally appeared just above
;;; riemann-rcfn-refinement-append, which does not need them and has
;;; been moved to riemann-lemmas.lisp.
(defthm cdr-map-rcfn-refinement
  (implies (consp p1)
           (equal (cdr (map-rcfn-refinement p1 p2))
                  (map-rcfn-refinement (cdr p1) p2))))

(defthm len-cdr-map-rcfn-refinement
  (equal (len (cdr (map-rcfn-refinement p1 p2)))
         (len (cdr p1))))

(defthm member-implies-consp-co-member
  (implies (member a x)
           (consp (co-member a x)))
  :rule-classes :forward-chaining)

(defthm car-last-co-member
  (implies (member a x)
           (equal (car (last (co-member a x)))
                  a)))

;;; The following is left here, instead of being moved to
;;; riemann-lemmas.lisp, because it does not appear to be necessary in
;;; general.  It must have been important for some lemma in this file.
(defthm car-member
  (implies (member a x)
           (equal (car (member a x))
                  a)))

;;; For what it's worth, this disable command originally appeared just
;;; before riemann-rcfn-refinement-cdr-2, which has been moved to
;;; riemann-lemmas.lisp.
(in-theory (disable cdr-map-rcfn-refinement cdr-append))

;;; This :forward-chaining rule has a free variable, so it seems to
;;; specialized to be moved to riemann-lemmas.lisp.  See the comment
;;; below about partitionp-member-rewrite.
(defthm partitionp-member
  (implies (and (partitionp p)
                (member a p))
           (partitionp (member a p)))
  :rule-classes :forward-chaining)

(defthm member-cdr-member-implies-member
  (implies (member a (cdr (member b x)))
           (member a x))
  :rule-classes :forward-chaining)

(defthm refinement-implies-member-cadr
  (implies (and (refinement-p p1 p2)
                (consp (cdr p2)))
           (member (cadr p2) p1))
  :hints (("Goal" :expand
           ((refinement-p p1 p2)
            (refinement-p (cdr (member (car p2) p1)) (cdr p2))))))

(defun my-make-list (n elt)
  (if (zp n)
      nil
    (cons elt (my-make-list (1- n) elt))))

(encapsulate
 ()
 (local (include-book "map-rcfn-refinement-cdr-co-member"))
 (defthm map-rcfn-refinement-cdr-co-member
   (implies
    (and (partitionp p1)
         (partitionp p2)
         (consp (cdr p2))
         (strong-refinement-p p1 p2))
    (equal
     (map-rcfn-refinement (cdr (co-member (cadr p2) p1))
                          p2)
     (my-make-list (len (cdr (co-member (cadr p2) p1)))
                   (rcfn (cadr p2)))))))

(defthm consp-co-member
  (equal (consp (co-member a x))
         (consp x)))

(defthm sumlist-map-times-deltas-with-constant
  (implies (true-listp lst)
           (equal (sumlist (map-times (deltas lst)
                                      (cdr (my-make-list (len lst) elt))))
                  (* (- (car (last lst)) (car lst))
                     elt)))
  :hints (("Goal"
; The following hint is needed for Version 3.2, probably because of the change
; documented in note-3-2 as: "ACL2's rewriter now avoids removing certain true
; hypotheses and false conclusions."
           :expand ((my-make-list 1 elt)))))

(defthm len-non-zero
  (implies (consp x)
           (< 0 (len x)))
  :rule-classes :forward-chaining)

(defthm car-my-make-list
  (implies (not (zp n))
           (equal (car (my-make-list n elt))
                  elt))
  :hints (("Goal" :expand (my-make-list n elt))))

(defthm car-co-member
  (equal (car (co-member a x))
         (car x)))

(defthm co-member-open
  (implies (and (not (equal a (car x)))
                (consp x))
           (equal (co-member a x)
                  (cons (car x)
                        (co-member a (cdr x))))))

;;; A forward-chaining version of this has been put in
;;; riemann-lemmas.lisp.  !! So maybe it is no longer necessary here.
(defthm refinement-p-forward-to-member-rewrite
  (implies (and (refinement-p p1 p2)
                (consp p2))
           (member (car p2) p1)))

(defthm equal-riemann-rcfn-refinement-reduction-helper-1-back-2
  (implies (and (partitionp p1)
                (partitionp p2)
                (consp (cdr p2))
                (strong-refinement-p p1 p2))
           (equal (riemann-rcfn-refinement (co-member (cadr p2) p1)
                                           p2)
                  (* (- (cadr p2) (car p2))
                     (rcfn (cadr p2)))))
  ;; Matt K.: The following is needed for v2-8 (I don't know why).
  :hints (("Goal" :in-theory (disable partitionp-implies-first-less-than-second))))

(defthm equal-riemann-rcfn-refinement-reduction-helper-1-back-1
  (implies (and (partitionp p1)
                (partitionp p2)
                (consp (cdr p2))
                (strong-refinement-p p1 p2))
           (equal (riemann-rcfn-refinement (member (cadr p2) p1)
                                           p2)
                  (- (riemann-rcfn-refinement p1 p2)
                     (* (- (cadr p2) (car p2))
                        (rcfn (cadr p2))))))
  :rule-classes nil
  :hints (("Goal"
           :in-theory
           (disable riemann-rcfn-refinement partitionp
                    riemann-rcfn-refinement-append
                    ;; Matt K.: The following is needed for v2-8 (I don't know why).
                    partitionp-implies-first-less-than-second)
           :use
           ((:instance riemann-rcfn-refinement-append
                       (p1 (co-member (cadr p2) p1))
                       (p2 (member (cadr p2) p1))
                       (p3 p2))))))

(defthm equal-riemann-rcfn-refinement-reduction-helper-1
  (implies (and (partitionp p1)
                (partitionp p2)
                (consp (cdr p2))
                (equal (riemann-rcfn-refinement (member (cadr p2) p1)
                                                p2)
                       (riemann-rcfn (cdr p2)))
                (strong-refinement-p p1 p2))
           (equal (riemann-rcfn-refinement p1 p2)
                  (riemann-rcfn p2)))
  :hints (("Goal" :use equal-riemann-rcfn-refinement-reduction-helper-1-back-1)))

;;; AHA!!  This is the consequence of meddling with the methodology.
;;; I believe that what happened was that the proof of
;;; equal-riemann-rcfn-refinement-reduction originally went through
;;; without the following lemma, because partitionp-member was a
;;; :rewrite lemma.  However, partitionp-member was a
;;; :forward-chaining lemma in the book
;;; "riemann-rcfn-refinement-is-riemann-rcfn", so I changed it above
;;; to be a :forward-chaining lemma, and then the proof of
;;; equal-riemann-rcfn-refinement-reduction failed.  I should have
;;; merely changed the name instead.
;;; (Note:  This lemma is included here for historical reasons only.
;;; It is now in riemann-lemmas.lisp as well.)
(defthm partitionp-member-rewrite
  (implies (and (partitionp p)
                (member a p))
           (partitionp (member a p))))

(defthm equal-riemann-rcfn-refinement-reduction
  (implies (and (partitionp p1)
                (partitionp p2)
                (consp (cdr p2))
                (equal (riemann-rcfn-refinement (member (cadr p2) p1)
                                                (cdr p2))
                       (riemann-rcfn (cdr p2)))
                (strong-refinement-p p1 p2))
           (equal (riemann-rcfn-refinement p1 p2)
                  (riemann-rcfn p2)))
  :hints (("Goal" :in-theory
           (disable
            riemann-rcfn-refinement riemann-rcfn member
            riemann-rcfn-refinement-cdr-2)
           :use
           ((:instance
             riemann-rcfn-refinement-cdr-2
             (p1 (member (cadr p2) p1))
             (p2 p2)
             (a (cadr p2)))))))
