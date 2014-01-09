;;; This book includes many useful theorems about the factorial
;;; function.

(in-package "ACL2")

(include-book "../arithmetic/factorial")
(include-book "nsa")

; Added by Matt K. for v2-7.
(add-match-free-override :once t)
(set-match-free-default :once)

;;; This is an important theorem.  If n is limited, then so is n!.
;;; The rational is that if (n-1)! is limited, then so is n*(n-1)!.
;;; The induction is valid, since we are only interested in limited
;;; n.

(defthm factorial-limited
  (implies (i-limited n)
	   (i-limited (factorial n)))
  :hints (("Goal" :in-theory (enable factorial))))

;;; Moreover, |n| is never small -- an obvious fact, since it is
;;; always positive and at least equal to 1.

(defthm factorial-not-small
  (not (i-small (factorial n)))
  :hints (("Goal"
	   :use ((:theorem (not (i-small 1)))
		 (:instance small-<-non-small (x (factorial n)) (y 1)))
	   :in-theory (disable small-<-non-small
			       small-if-<-small))
	  ("Subgoal 1"
	   :use ((:instance standard-small-is-zero (x 1)))))
  :otf-flg t)

