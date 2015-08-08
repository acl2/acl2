(in-package "ACL2")

(include-book "land")
(include-book "lior")
(include-book "lxor")
(include-book "lnot") ;BOZO

(local (include-book "../support/stick"))

(set-inhibit-warnings "theory") ; avoid warning in the next event
(local (in-theory nil))

(defthm top-thm-1
  (implies (and (natp n)
                (natp k)
                (< k n)
                (integerp a) ;(bvecp a n)
                (integerp b) ;(bvecp b n)
                )
           (equal (equal (bits (+ a b 1) k 0)
                         0)
		  (equal (bits (lnot (lxor a b n) n) k 0)
                         0)))
  :rule-classes ())

(defund sigm (a b c n)
  (if (= c 0)
      (lnot (lxor a b n) n)
    (lxor a b n)))

(defund kap (a b c n)
  (if (= c 0)
      (* 2 (lior a b n))
    (* 2 (land a b n))))

(defund tau (a b c n)
  (lnot (lxor (sigm a b c n) (kap a b c n) (1+ n)) (1+ n)))

(defthm bvecp-sigm
  (bvecp (sigm a b c n) n)
  :rule-classes (:rewrite (:forward-chaining :trigger-terms ((sigm a b c n)))))

(defthm bvecp-kap
  (implies (and (integerp n) (<= 0 n))
           (bvecp (kap a b c n) (1+ n)))
  :rule-classes (:rewrite (:forward-chaining :trigger-terms ((kap a b c n)))))

(defthm bvecp-tau
  (bvecp (tau a b c n) (1+ n))
  :rule-classes (:rewrite (:forward-chaining :trigger-terms ((tau a b c n)))))

(defthm top-thm-2-old
  (implies (and (natp n)
                (integerp a) ;(bvecp a n)
                (integerp b) ;(bvecp b n)
                (natp k)
                (< k n)
                (or (equal c 0) (equal c 1)))
           (equal (equal (bits (+ a b c) k 0) 0)
		  (equal (bits (tau a b c n) k 0) 0)))
  :rule-classes ())
