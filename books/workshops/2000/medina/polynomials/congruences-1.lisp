(in-package "POL")

(include-book "negation")

;;; --------------------------------------------------
;;; Congruence of equality with polynomial constructor
;;; --------------------------------------------------

(defcong MON::= = (polynomial m p) 1)
(defcong = = (polynomial m p) 2)

;;; -----------------------------------------------
;;; Congruence of equality with polynomial addition
;;; -----------------------------------------------

(encapsulate ()
  (local
    (defthm technical-lemma-1
      (= (+ p1 (nf p2)) (+ p1 p2))))

  (defcong = = (+ p1 p2) 2
    :hints (("Goal"
	     :in-theory (disable technical-lemma-1)
	     :use ((:instance technical-lemma-1 (p2 p2-equiv))
		   technical-lemma-1))))

  (local
    (defthm technical-lemma-2
      (= (+ (nf p1) p2) (+ p1 p2))
      :hints (("Goal"
	       :in-theory (disable =)))))

  (defcong = = (+ p1 p2) 1
    :hints (("Goal"
	     :in-theory (disable technical-lemma-2)
	     :use ((:instance technical-lemma-2 (p1 p1-equiv))
		   technical-lemma-2))))

  (defthm nf-+
    (= (+ (nf p1) (nf p2)) (+ p1 p2))
    :hints (("Goal"
	     :in-theory (disable = technical-lemma-1 technical-lemma-2)
	     :use (technical-lemma-1
		   (:instance technical-lemma-2 (p2 (nf p2))))))))

;;; ------------------------------------
;;; Congruence of equality with negation
;;; ------------------------------------

(encapsulate ()
  (local
    (defthm technical-lemma
      (equal (nf (- p)) (- (nf p)))))

  (defcong = = (- p) 1))
