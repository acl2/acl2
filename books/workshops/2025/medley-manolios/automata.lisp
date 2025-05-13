#|
 | This file contains the code for our paper ``Cellular Automata
 | Surviving $k$ Steps'' in ACL2-2025.
 |#

(in-package "ACL2S")
(acl2s-defaults :set testing-enabled nil)
(acl2s-defaults :set cgen-timeout 1)
(set-defunc-timeout 1000)
(set-acl2s-property-table-proof-timeout 1000)

#|
 | rule evaluation
 |#

(defdata bit (oneof 0 1))
(defdata ruleNum (range integer (0 <= _ < 256)))

(defdata bv (listof bit))
(defdata bv8 (list bit bit bit bit bit bit bit bit))
(defdata-subtype bv8 bv)
(in-theory (disable bitp))

(local (property bv8-def-prop (x :all)
  (== (bv8p x)
      (^ (bvp x) (= (len x) 8)))
  :rule-classes :definition))
(in-theory (disable bv8p))

(definecd nat2bv (n :nat) :bv
  (let ((r (mod n 2))
        (q (floor n 2)))
    (if (== q 0) (list r) (append (nat2bv q) (list r)))))

(definec leftpad (v :bv s :nat) :bv
  (if (< (len v) s)
    (leftpad (cons 0 v) s)
    v))

(property leftpad-len (v :bv s :nat)
  :h (<= (len v) s)
  :b (= (len (leftpad v s)) s)
  :rule-classes (:linear :rewrite))

(definecd bv8pad (v :bv) :bv8
  :ic (<= (len v) 8)
  (leftpad v 8))

(defmacro rc-helper (v i)
  (if (= i 0)
      `(list '(= ,v ,i))
      `(cons '(= ,v ,i) (rc-helper ,v ,(- i 1)))))
(defmacro rule-cases (v)
  `(rc-helper ,v 255))
(defmacro proof-by-cases (name body)
  `(property ,name (n :ruleNum)
	     :b ,body
	     :hints (("goal"
		      :in-theory (enable ruleNump)
		      :cases ,(rule-cases n)))))

(proof-by-cases len-nat2bv (<= (len (nat2bv n)) 8))

(definecd nat2rule (n :ruleNum) :bv8
  (bv8pad (nat2bv n)))

(proof-by-cases len-nat2rule (= (len (nat2rule n)) 8))
(in-theory (disable ruleNump bv8p))

(definecd eval-rule (rule :ruleNum p q r :bit) :bit
  (let ((x (nat2rule rule))
	(i (- 7 (+ r (* 2 q) (* 4 p)))))
    (nth i x)))

#|
 | rule array
 |#

(defdata ruleArray (listof ruleNum))

;; rule array is stored in row major form.
(definec idxwp (a :ruleArray w row col :nat) :bool
  (^ (< col w) (< (+ col (* row w)) (len a))))

(definec idxw (a :ruleArray w row col :nat) :ruleNum
  :ic (idxwp a w row col)
  (nth (+ col (* row w)) a))

(definec idxp (a :ruleArray x :bv row col :nat) :bool
  (idxwp a (len x) row col))

(definec idx (a :ruleArray x :bv row col :nat) :ruleNum
  :ic (idxp a x row col)
  (idxw a (len x) row col))

(definec board (a :ruleArray x :bv row col :nat) :bit
  (declare (xargs :consider-only-ccms (row)))
  :ic (idxp a x row col)
  (if (= row 0)
      (nth col x)
      (let* ((width (len x))
	     (rowp (- row 1))
	     (p (mod (- col 1) width))
	     (q col)
	     (r (mod (+ col 1) width))
	     (rule (idx a x row col)))
	(eval-rule rule (board a x rowp p) (board a x rowp q) (board a x rowp r)))))

#|
 | survive-k-steps
 |#

(definec row-all-loop (a :ruleArray x :bv row col :nat v :bit) :bool
  (declare (xargs :consider-ccms ((- (len x) col))))
  (v (! (idxp a x row col)) (^ (= (board a x row col) v) (row-all-loop a x row (1+ col) v))))

(definec row-all (a :ruleArray x :bv row :nat v :bit) :bool
  (row-all-loop a x row 0 v))

(definec row-any-loop (a :ruleArray x :bv row col :nat v :bit) :bool
  (declare (xargs :consider-ccms ((- (len x) col))))
  (^ (idxp a x row col) (v (= (board a x row col) v) (row-any-loop a x row (1+ col) v))))

(definec row-any (a :ruleArray x :bv row :nat v :bit) :bool
  (row-any-loop a x row 0 v))

(definec live-upto-k (a :ruleArray x :bv k :nat) :bool
  (v (= k 0) (^ (row-any a x (1- k) 1) (live-upto-k a x (1- k)))))

(definecd one-alive (width :nat) :bv
  :ic (> width 0)
  :oc (== (len (one-alive width)) width)
  (if (= width 1) (list 1) (cons 0 (one-alive (- width 1)))))

(definec survive-k-steps (a :ruleArray width k :nat) :bool
  :ic (> width 0)
  (let ((x (one-alive width)))
    (^ (idxp a x (1+ k) (1- (len x)))
       (live-upto-k a x k)
       (row-all a x k 0)
       (row-all a x (1+ k) 0))))

#|
 | technique 1
 |#

(in-theory (disable evenp oddp natp))

(definec all-odd (a :ruleArray) :bool
  (v (! a) (^ (oddp (car a)) (all-odd (cdr a)))))

(property odd->nth-odd (a :ruleArray i :nat)
  :h (^ (< i (len a)) (all-odd a) a)
  :b (oddp (nth i a)))

(property even->not-all-odd (a :ruleArray x :bv row col :nat)
  :h (^ (idxp a x row col)  (! (oddp (idx a x row col))))
  :b (! (all-odd a))
  :hints (("Goal" :use ((:instance odd->nth-odd (i (+ col (* row (len x)))))))))

(proof-by-cases even-rule (== (= (eval-rule n 0 0 0) 0) (! (oddp n))))

(property even-rule-board (a :ruleArray x :bv row :nat col :nat)
  :h (^ (idxp a x (+ row 1) col)
	(= (board a x row (mod (- col 1) (len x))) 0)
	(= (board a x row col) 0)
	(= (board a x row (mod (+ col 1) (len x))) 0)
	(= (board a x (+ row 1) col) 0))
  :b (! (oddp (idx a x (+ row 1) col)))
  :hints (("Goal" :do-not-induct t :do-not '(preprocess))))

(property row-all-loop-gt (a :ruleArray x :bv row col colp :nat v :bit)
  :h (^ (idxp a x row colp) (row-all-loop a x row col v) (<= col colp))
  :b (row-all-loop a x row colp v))

(property row-all->board (a :ruleArray x :bv row col :nat v :bit)
  :h (^ (idxp a x row col) (row-all a x row v))
  :b (= (board a x row col) v)
  :hints (("Goal" :use ((:instance row-all-loop-gt (col 0) (colp col)))))
  :rule-classes ((:rewrite :backchain-limit-lst 0)))

(in-theory (disable row-all-loop-gt))

(property idxp->col (a :ruleArray x :bv row col colp :nat)
  :h (^ (idxp a x row col) (>= col colp))
  :b (idxp a x row colp)
  :rule-classes ((:rewrite :backchain-limit-lst 0)))

(property idxp->row (a :ruleArray x :bv row col rowp colp :nat)
  :h (^ (idxp a x row col) (> row rowp) (< colp (len x)))
  :b (idxp a x rowp colp)
  :rule-classes ((:rewrite :backchain-limit-lst 0)))

(property mod-helper (x :bv)
  :h x
  :b (<= (mod -1 (len x)) (+ -1 (len x)))
  :rule-classes :forward-chaining)

(in-theory (disable rulearrayp row-all-definition-rule bvp))

;; boss fight
(property all-odd-cannot-stay-dead (a :ruleArray x :bv :cons k :nat)
  :h (^ (idxp a x (+ k 1) (- (len x) 1)) (row-all a x k 0) (row-all a x (+ k 1) 0))
  :b (! (all-odd a))
  :hints (("Goal"
	   :do-not-induct t
	   :in-theory (disable board-definition-rule idx-definition-rule idxp-definition-rule)
	   :use ((:instance idxp->row (row (+ k 1)) (col (- (len x) 1)) (colp (- (len x) 1)) (rowp k))
		 (:instance idxp->col (row (+ k 1)) (col (- (len x) 1)) (colp 0))
		 (:instance idxp->col (row k) (col (- (len x) 1)) (colp 0))
		 (:instance idxp->col (row k) (col (- (len x) 1)) (colp (mod (- 0 1) (len x))))
		 (:instance idxp->col (row k) (col (- (len x) 1)) (colp (mod (+ 0 1) (len x))))
		 (:instance row-all->board (row k) (col 0) (v 0))
		 (:instance row-all->board (row k) (col (mod (- 0 1) (len x))) (v 0))
		 (:instance row-all->board (row k) (col (mod (+ 0 1) (len x))) (v 0))
		 (:instance row-all->board (row (+ k 1)) (col 0) (v 0))
		 (:instance even-rule-board (row k) (col 0))
		 (:instance even->not-all-odd (row (+ k 1)) (col 0))))))

(in-theory (disable mod-helper))

(property technique1 (a :ruleArray w :pos k :nat)
  :h (survive-k-steps a w k)
  :b (! (all-odd a))
  :hints (("Goal" :use ((:instance all-odd-cannot-stay-dead (x (one-alive w)))))))

#|
 | technique 2
 |#

(in-theory (enable evenp oddp natp))

; board row equality

(definec b-row-equal-helper (col row1 row2 :nat a1 a2 :ruleArray x1 x2 :bv) :bool
  (declare (xargs :consider-ccms ((- (len x1) col))))
  (^ (== (idxp a1 x1 row1 col) (idxp a2 x2 row2 col))
     (v (! (idxp a1 x1 row1 col))
	(^ (= (board a1 x1 row1 col) (board a2 x2 row2 col))
	   (b-row-equal-helper (1+ col) row1 row2 a1 a2 x1 x2)))))

(property b-row-equal-helper->board (col colp row1 row2 :nat a1 a2 :ruleArray x1 x2 :bv)
  :h (^ (<= colp col)
	(b-row-equal-helper colp row1 row2 a1 a2 x1 x2)
	(idxp a1 x1 row1 col)
	(idxp a2 x2 row2 col))
  :b (== (board a1 x1 row1 col) (board a2 x2 row2 col))
  :hints (("Goal" :induct (b-row-equal-helper colp row1 row2 a1 a2 x1 x2)))
  :rule-classes ((:rewrite :backchain-limit-lst 0)))

(property b-row-equal-helper->idxp (col colp row1 row2 :nat a1 a2 :ruleArray x1 x2 :bv)
  :h (^ (b-row-equal-helper colp row1 row2 a1 a2 x1 x2)
	(<= colp col))
  :b (== (idxp a1 x1 row1 col) (idxp a2 x2 row2 col))
  :hints (("goal" :induct (b-row-equal-helper colp row1 row2 a1 a2 x1 x2)))
  :rule-classes ((:rewrite :backchain-limit-lst 0)))

(definec b-row-equal (row1 row2 :nat a1 a2 :ruleArray x1 x2 :bv) :bool
  (b-row-equal-helper 0 row1 row2 a1 a2 x1 x2))

(property b-row-equal->idxp (col row1 row2 :nat a1 a2 :ruleArray x1 x2 :bv)
  :h (b-row-equal row1 row2 a1 a2 x1 x2)
  :b (== (idxp a1 x1 row1 col) (idxp a2 x2 row2 col))
  :hints (("goal" :do-not-induct t
		  :case-split-limitations (0 0)
		  :in-theory (disable natp)
		  :use ((:instance b-row-equal-helper->idxp (colp 0))
			(:instance b-row-equal-definition-rule))))
  :rule-classes ((:rewrite :backchain-limit-lst 0)))

(property b-row-equal->board (col row1 row2 :nat a1 a2 :ruleArray x1 x2 :bv)
  :h (^ (idxp a1 x1 row1 col) (idxp a2 x2 row2 col) (b-row-equal row1 row2 a1 a2 x1 x2))
  :b (== (board a1 x1 row1 col) (board a2 x2 row2 col))
  :hints (("Goal"
	   :do-not-induct t
	   :use ((:instance b-row-equal-helper->board (colp 0)))))
  :rule-classes ((:rewrite :backchain-limit-lst 0)))

; rule array row equality

(definec a-row-equal-helper (col row1 row2 w :nat a1 a2 :ruleArray) :bool
  (declare (xargs :consider-ccms ((- w col))))
  (^ (== (idxwp a1 w row1 col) (idxwp a2 w row2 col))
     (v (! (idxwp a1 w row1 col))
	(^ (= (idxw a1 w row1 col) (idxw a2 w row2 col))
	   (a-row-equal-helper (1+ col) row1 row2 w a1 a2)))))

(property a-row-equal-helper->idxwp (col colp row1 row2 w :nat a1 a2 :ruleArray)
  :h (^ (a-row-equal-helper colp row1 row2 w a1 a2)
	(<= colp col))
  :b (== (idxwp a1 w row1 col) (idxwp a2 w row2 col))
  :hints (("goal" :induct (a-row-equal-helper colp row1 row2 w a1 a2)))
  :rule-classes ((:rewrite :backchain-limit-lst 0)))

(property a-row-equal-helper->idxw (col colp row1 row2 w :nat a1 a2 :ruleArray)
  :h (^ (<= colp col)
	(a-row-equal-helper colp row1 row2 w a1 a2)
	(idxwp a1 w row1 col)
	(idxwp a2 w row2 col))
  :b (== (idxw a1 w row1 col) (idxw a2 w row2 col))
  :hints (("goal" :induct (a-row-equal-helper colp row1 row2 w a1 a2)))
  :rule-classes ((:rewrite :backchain-limit-lst 0)))

(definec a-row-equal (row1 row2 w :nat a1 a2 :ruleArray) :bool
  (a-row-equal-helper 0 row1 row2 w a1 a2))

(property a-row-equal->idxwp (col row1 row2 w :nat a1 a2 :ruleArray)
  :h (a-row-equal row1 row2 w a1 a2)
  :b (== (idxwp a1 w row1 col) (idxwp a2 w row2 col))
  :hints (("goal" :do-not-induct t
		  :use ((:instance a-row-equal-helper->idxwp (colp 0)))))
  :rule-classes ((:rewrite :backchain-limit-lst 0)))

(property a-row-equal->idxw (col row1 row2 w :nat a1 a2 :ruleArray)
  :h (^ (idxwp a1 w row1 col) (idxwp a2 w row2 col) (a-row-equal row1 row2 w a1 a2))
  :b (== (idxw a1 w row1 col) (idxw a2 w row2 col))
  :hints (("goal"
	   :do-not-induct t
           :in-theory (disable idxw-definition-rule)
	   :use ((:instance a-row-equal-helper->idxw (colp 0)))))
  :rule-classes ((:rewrite :backchain-limit-lst 0)))

; boss fight 1

(property mod-helper1 (x y :nat)
  :h (!= 0 x)
  :b (natp (mod y x)))

(property mod-helper2 (x y :nat)
  :h (!= 0 x)
  :b (< (mod y x) x))

(property len-helper (a :ruleArray x :bv col row :nat)
  :h (idxp a x (1+ row) col)
  :b (consp x)
  :rule-classes :forward-chaining)

(property rule-array-determines-cell (a1 a2 :ruleArray x1 x2 :bv row1 row2 col :nat)
  :h (^ (= (len x1) (len x2))
	(b-row-equal row1 row2 a1 a2 x1 x2)
	(a-row-equal (1+ row1) (1+ row2) (len x1) a1 a2)
	(idxp a1 x1 (1+ row1) col)
	(idxp a2 x2 (1+ row2) col))
  :b (= (board a1 x1 (1+ row1) col) (board a2 x2 (1+ row2) col))
  :hints (("Goal"
	   :use ((:instance idxp->row (a a1) (x x1) (row (1+ row1)) (colp (mod (1+ col) (len x1))) (rowp row1))
		 (:instance idxp->row (a a2) (x x2) (row (1+ row2)) (colp (mod (1+ col) (len x2))) (rowp row2))
		 (:instance idxp->row (a a1) (x x1) (row (1+ row1)) (colp col) (rowp row1))
		 (:instance idxp->row (a a2) (x x2) (row (1+ row2)) (colp col) (rowp row2))
		 (:instance idxp->row (a a1) (x x1) (row (1+ row1)) (colp (mod (1- col) (len x1))) (rowp row1))
		 (:instance idxp->row (a a2) (x x2) (row (1+ row2)) (colp (mod (1- col) (len x2))) (rowp row2))
		 (:instance a-row-equal->idxw (row1 (1+ row1)) (row2 (1+ row2)) (w (len x1)))
		 (:instance b-row-equal->board (col (mod (1+ col) (len x1))))
		 (:instance b-row-equal->board)
		 (:instance b-row-equal->board (col (mod (1- col) (len x1)))))
	   :do-not-induct t
	   :hands-off (mod)
	   :in-theory (disable row-all->board
			       natp
			       idxp->row
			       idxp->col
			       idxw-definition-rule
			       a-row-equal->idxwp
			       b-row-equal->board
			       a-row-equal-definition-rule
			       b-row-equal-definition-rule))))

(in-theory (disable mod-helper1 mod-helper2 len-helper))

; boss fight 2

(property helper1 (a1 a2 :ruleArray x1 x2 :bv row1 row2 col :nat)
  :h (== (len x1) (len x2))
  (== (== (idxp a1 x1 (+ 1 row1) col) (idxp a2 x2 (+ 1 row2) col))
      (== (idxwp a1 (len x1) (+ 1 row1) col) (idxwp a2 (len x1) (+ 1 row2) col))))

(property rule-array-determines-row-helper (a1 a2 :ruleArray x1 x2 :bv row1 row2 col :nat)
  :h (^ (= (len x1) (len x2))
	(b-row-equal row1 row2 a1 a2 x1 x2)
	(a-row-equal (1+ row1) (1+ row2) (len x1) a1 a2))
  :b (b-row-equal-helper col (1+ row1) (1+ row2) a1 a2 x1 x2)
  :hints (("goal"
	   :induct (b-row-equal-helper col (1+ row1) (1+ row2) a1 a2 x1 x2)
	   :in-theory (disable natp idxw-definition-rule idxwp-definition-rule))
	  ("Subgoal *1/4"
	   :case-split-limitations (0 0)
	   :use ((:instance a-row-equal->idxwp (row1 (1+ row1)) (row2 (1+ row2)) (w (len x1)))
		 (:instance helper1)))
	  ("Subgoal *1/2'"
	   :case-split-limitations (0 0)
	   :in-theory (disable natp)
	   :do-not-induct t
	   :do-not simplify
	   :use ((:instance rule-array-determines-cell)
		 (:instance b-row-equal-helper-definition-rule (row1 (1+ row1)) (row2 (1+ row2)))))))

(in-theory (disable helper1))

(property rule-array-determines-row (a1 a2 :ruleArray x1 x2 :bv row1 row2 :nat)
  :h (^ (= (len x1) (len x2))
	(b-row-equal row1 row2 a1 a2 x1 x2)
	(a-row-equal (1+ row1) (1+ row2) (len x1) a1 a2))
  :b (b-row-equal (1+ row1) (1+ row2) a1 a2 x1 x2)
  :hints (("goal" :in-theory (disable natp b-row-equal-definition-rule)
		  :use ((:instance b-row-equal-definition-rule (row1 (1+ row1)) (row2 (1+ row2)))))))

;; row equality and its implications for row-∀, row-∃

(property b-row-equal->row-all-loop (row1 row2 col :nat a1 a2 :ruleArray x1 x2 :bv v :bit)
  :h (b-row-equal row1 row2 a1 a2 x1 x2)
  :b (== (row-all-loop a1 x1 row1 col v) (row-all-loop a2 x2 row2 col v))
  :hints (("goal"
	   :case-split-limitations (0 0)
	   :in-theory (disable natp)
	   :induct (row-all-loop a1 x1 row1 col v))
	  ("subgoal *1/3"
	   :use ((:instance b-row-equal->idxp)
		 (:instance b-row-equal->board)
		 (:instance row-all-loop-definition-rule (a a1) (x x1) (row row1))
		 (:instance row-all-loop-definition-rule (a a2) (x x2) (row row2))))
	  ("subgoal *1/2"
	   :use ((:instance b-row-equal->idxp)
		 (:instance b-row-equal->board)
		 (:instance row-all-loop-definition-rule (a a1) (x x1) (row row1))
		 (:instance row-all-loop-definition-rule (a a2) (x x2) (row row2))))
	  ("subgoal *1/1"
	   :use ((:instance b-row-equal->idxp)
		 (:instance row-all-loop-definition-rule (a a1) (x x1) (row row1))
		 (:instance row-all-loop-definition-rule (a a2) (x x2) (row row2))))))

(in-theory (disable b-row-equal-definition-rule))

(property b-row-equal->row-all (row1 row2 :nat a1 a2 :ruleArray x1 x2 :bv v :bit)
  :h (b-row-equal row1 row2 a1 a2 x1 x2)
  :b (== (row-all a1 x1 row1 v) (row-all a2 x2 row2 v))
  :hints (("goal" :use ((:instance row-all-definition-rule (a a1) (x x1) (row row1))
			(:instance row-all-definition-rule (a a2) (x x2) (row row2))))))

(property b-row-equal->row-any-loop (row1 row2 col :nat a1 a2 :ruleArray x1 x2 :bv v :bit)
  :h (b-row-equal row1 row2 a1 a2 x1 x2)
  :b (== (row-any-loop a1 x1 row1 col v) (row-any-loop a2 x2 row2 col v))
  :hints (("goal"
	   :case-split-limitations (0 0)
	   :in-theory (disable natp)
	   :induct (row-any-loop a1 x1 row1 col v))
	  ("subgoal *1/3"
	   :use ((:instance b-row-equal->idxp)
		 (:instance row-any-loop-definition-rule (a a1) (x x1) (row row1))
		 (:instance row-any-loop-definition-rule (a a2) (x x2) (row row2))))
	  ("subgoal *1/2"
	   :use ((:instance b-row-equal->idxp)
		 (:instance b-row-equal->board)
		 (:instance row-any-loop-definition-rule (a a1) (x x1) (row row1))
		 (:instance row-any-loop-definition-rule (a a2) (x x2) (row row2))))
	  ("subgoal *1/1"
	   :use ((:instance b-row-equal->board)
		 (:instance b-row-equal->idxp)
		 (:instance row-any-loop-definition-rule (a a1) (x x1) (row row1))
		 (:instance row-any-loop-definition-rule (a a2) (x x2) (row row2))))))

(property b-row-equal->row-any (row1 row2 :nat a1 a2 :ruleArray x1 x2 :bv v :bit)
  :h (b-row-equal row1 row2 a1 a2 x1 x2)
  :b (== (row-any a1 x1 row1 v) (row-any a2 x2 row2 v))
  :hints (("goal" :use ((:instance row-any-definition-rule (a a1) (x x1) (row row1))
			(:instance row-any-definition-rule (a a2) (x x2) (row row2))))))

;; boss fight 3
;;
;; This property is basically what we need to be done, but notably it
;; doesnt guarentee the EXISTANCE of a2 and x2 values satisfying the
;; equality requirements. i.e. it technically could be vacuously true
;; (tho our human brains suspect otherwise).

(property survive-k-steps->live-die-transition (a1 a2 :ruleArray w :pos k :pos x2 :bv)
  :h (^ (survive-k-steps a1 w k)
	(a-row-equal k 1 w a1 a2)
        (b-row-equal (1- k) 0 a1 a2 (one-alive w) x2)
	(= (len x2) w))
  :b (^ (row-any a2 x2 0 1)
        (row-all a2 x2 1 0))
  :hints (("goal" :do-not-induct t
		  :case-split-limitations (0 1)
		  :in-theory (disable natp
				      b-row-equal-definition-rule
				      a-row-equal-definition-rule
				      row-any-definition-rule
				      row-all-definition-rule
				      board-definition-rule
				      row-all->board
				      idxw-definition-rule
				      idxwp-definition-rule)
		  :use ((:instance survive-k-steps-definition-rule (a a1) (width w))
			(:instance live-upto-k-definition-rule (a a1) (x (one-alive w)))
			(:instance rule-array-determines-row (x1 (one-alive w)) (row1 (1- k)) (row2 0))
			(:instance b-row-equal->row-any (row1 (1- k)) (row2 0) (x1 (one-alive w)) (v 1))
			(:instance b-row-equal->row-all (row1 k) (row2 1) (x1 (one-alive w)) (v 0))))))

#|
 | a function which returns the kth row of a board as a bitvector
 |#

(definec b-row-k-helper (a :ruleArray x :bv k col :nat) :bv
  (declare (xargs :consider-ccms ((- (len x) col))))
  (^ (idxp a x k col) (cons (board a x k col) (b-row-k-helper a x k (1+ col)))))

(definec b-row-k (a :ruleArray x :bv k :nat) :bv
  (b-row-k-helper a x k 0))

;; a proof this function preserves board row equality

(property idxp->row-k-len (a :ruleArray x :bv k col colp :nat)
  :h (^ (>= col colp) (idxp a x k col))
  :b (> (len (b-row-k-helper a x k colp)) (- col colp)))

(definec <-i_j-> (i j :nat) :bool (v (= i 0) (<-i_j-> (1- i) (1+ j))))

(property nth-row-k-helper (a :ruleArray x :bv k col i :nat)
  :check-contracts? nil
  :h (idxp a x k (+ i col))
  :b (= (nth i (b-row-k-helper a x k col)) (board a x k (+ i col)))
  :hints (("goal"
	   :in-theory (disable natp board-definition-rule idxp-definition-rule row-all->board)
	   :induct (<-i_j-> i col))
	  ("subgoal *1/2'" :use (:instance idxp->col (row k) (col (+ col i)) (colp col)))))

(property nth-row-k (a :ruleArray x :bv k i :nat)
  :check-contracts? nil
  :h (idxp a x k i)
  :b (= (nth i (b-row-k a x k)) (board a x k i))
  :hints (("goal" :in-theory (disable board-definition-rule row-all->board)
		  :use ((:instance b-row-k-definition-rule)
			(:instance nth-row-k-helper (col 0))))))

(property non-zero-len->idxp (a :ruleArray x :bv k col :nat)
  :h (!= (len (b-row-k-helper a x k col)) 0)
  :b (idxp a x k col))

(property board-idxp->row-k-idxp (a1 a2 :ruleArray x1 :bv k col :nat)
  :h (^ (idxp a1 x1 k col) (>= (len a2) (len x1)))
  :b (idxp a2 (b-row-k-helper a1 x1 k 0) 0 col)
  :hints (("goal" :use ((:instance idxp->row-k-len (colp 0) (a a1) (x x1)))
		  :in-theory (disable b-row-k-helper-definition-rule)))
  :rule-classes ((:rewrite :backchain-limit-lst 0)))

(property next-len-smaller-helper (a :ruleArray x :bv l :pos k col :nat)
  :h (>= (len (b-row-k-helper a x k col)) l)
  :b (>= (len (b-row-k-helper a x k (1+ col))) (1- l))
  :hints (("goal" :in-theory (disable board-definition-rule))))

(property len-implication (a :ruleArray x :bv k col :nat l :pos)
  :h (>= (len (b-row-k-helper a x k col)) l)
  :b (>= (len (b-row-k-helper a x k (+ col (1- l)))) 1)
  :hints (("goal"
	   :in-theory (disable natp
			       posp
			       b-row-k-helper-definition-rule)
	   :induct (<-i_j-> l col))
	  ("subgoal *1/1" :use ((:instance next-len-smaller-helper)))))

(in-theory (disable next-len-smaller-helper))

(property idxp-len-helper (a1 a2 :ruleArray x1 :bv k col :nat)
  :h (idxp a2 (b-row-k-helper a1 x1 k 0) 0 col)
  :b (>= (len (b-row-k-helper a1 x1 k 0)) (1+ col))
  :hints (("goal" :in-theory (disable natp b-row-k-helper-definition-rule))))

(property row-k-idxp->board-idxp (a1 a2 :ruleArray x1 :bv k col :nat)
  :h (idxp a2 (b-row-k-helper a1 x1 k 0) 0 col)
  :b (idxp a1 x1 k col)
  :hints (("goal" :do-not-induct t
		  :in-theory (disable natp b-row-k-helper-definition-rule)
		  :use ((:instance idxp-len-helper)
			(:instance len-implication (a a1) (x x1) (col 0) (l (1+ col))))))
  :rule-classes ((:rewrite :backchain-limit-lst 0)))

(in-theory (disable row-k-idxp->board-idxp board-idxp->row-k-idxp))

(property row-k-idxp==board-idxp (a1 a2 :ruleArray x1 :bv k col :nat)
  :h (>= (len a2) (len x1))
  :b (== (idxp a2 (b-row-k-helper a1 x1 k 0) 0 col) (idxp a1 x1 k col))
  :hints (("goal" :in-theory (disable natp idxp b-row-k-helper-definition-rule)
		  :use ((:instance board-idxp->row-k-idxp)
			(:instance row-k-idxp->board-idxp))))
  :rule-classes ((:rewrite :backchain-limit-lst 0)))

(property b-row-k-idx (a1 a2 :ruleArray x1 :bv k col :nat)
  :h (>= (len a2) (len x1))
  :b (== (idxp a1 x1 k col) (idxp a2 (b-row-k a1 x1 k) 0 col))
  :rule-classes :forward-chaining)

(property board-row-k (a ap :ruleArray x :bv k i :nat)
  :h (^ (idxp a x k i) (>= (len ap) (len x)))
  :b (= (board ap (b-row-k a x k) 0 i) (board a x k i))
  :hints (("goal" :in-theory (disable b-row-k-definition-rule
				      idxp-definition-rule))))

(property b-row-k->b-row-equal-helper (a ap :ruleArray x :bv row col :nat)
  :h (>= (len ap) (len x))
  :b (b-row-equal-helper col row 0 a ap x (b-row-k a x row))
  :hints (("goal" :induct (b-row-equal-helper col row 0 a ap x (b-row-k a x row))
		  :in-theory (disable natp
				      b-row-k-definition-rule
				      board-definition-rule
				      idxp-definition-rule))
	  ("subgoal *1/2''" :use ((:instance b-row-k-idx (a1 a) (a2 ap) (x1 nil) (k row))))))

;; many properties later, our objective..
(property b-row-k->b-row-equal (a ap :ruleArray x :bv row :nat)
  :h (>= (len ap) (len x))
  :b (b-row-equal row 0 a ap x (b-row-k a x row))
  :hints (("goal" :in-theory (disable natp b-row-k-definition-rule)
		  :use ((:instance b-row-equal-definition-rule (row1 row) (row2 0) (a1 a) (a2 ap) (x1 x) (x2 (b-row-k a x row)))))))

;; and finally, two more properties of the length.
(property b-row-k-helper-len (a :ruleArray x :bv k col :nat)
  :h (^ (< col (len x)) (idxp a x k (1- (len x))))
  :b (= (len (b-row-k-helper a x k col)) (- (len x) col))
  :hints (("goal" :in-theory (disable board-definition-rule))))

(property b-row-k-len (a :ruleArray x :bv k :nat)
  :h (v (! x) (idxp a x k (1- (len x))))
  :b (= (len (b-row-k a x k)) (len x))
  :rule-classes ((:rewrite :backchain-limit-lst 0)))

#|
 | a function which returns rows i through k (inclusive) of a rule array.
 |#

(definec i<=_<k (a :ruleArray i k :nat) :ruleArray
  :ic (<= k (len a))
  (^ (< i k) (cons (nth i a) (i<=_<k a (1+ i) k))))

(definec a-row-i-thru-k (a :ruleArray w i k :nat) :ruleArray
  :ic (^ (<= (* (1+ k) w) (len a)) (<= i k))
  (i<=_<k a (* i w) (* (1+ k) w)))

;; a proof this function preserves rule array row equality.

(property i<=_<=k-nth (a :ruleArray i j k :nat)
  :h (^ (< (+ i j) k) (<= k (len a)))
  :b (== (nth j (i<=_<k a i k)) (nth (+ i j) a))
  :hints (("goal" :induct (<-i_j-> j i))))

(property i<=_<k-len (a :ruleArray i k :nat)
  :h (^ (< i k) (<= k (len a)))
  :b (== (len (i<=_<k a i k)) (- k i)))

(property a-row-i-thru-k-len (a :ruleArray w i k :nat)
  :h (^ (<= (* (1+ k) w) (len a)) (<= i k))
  :b (== (len (a-row-i-thru-k a w i k)) (* w (1+ (- k i))))
  :hints (("goal" :use ((:instance i<=_<k-len (i (* i w)) (k (* (1+ k) w)))))))

(property a-row-i-thru-k-idxwp (a :ruleArray w i k j col :nat)
  :h (^ (<= i k) (<= (+ i j) k) (<= (* w (1+ k)) (len a)))
  :b (== (idxwp a w (+ i j) col) (idxwp (a-row-i-thru-k a w i k) w j col)))

(property a-row-i-thru-k-idxw (a :ruleArray w i j k col :nat)
  :h (^ (idxwp a w (+ i j) col) (<= i k) (<= (+ i j) k) (<= (* w (1+ k)) (len a)))
  :b (== (idxw a w (+ i j) col) (idxw (a-row-i-thru-k a w i k) w j col)))

(property a-row-i-thru-k-equal-helper (a :ruleArray w i k j col :nat)
  :h (^ (<= i k) (<= (+ i j) k) (<= (* w (1+ k)) (len a)))
  :b (a-row-equal-helper col (+ i j) j w a (a-row-i-thru-k a w i k)))

(in-theory (disable a-row-i-thru-k-definition-rule))

(property a-row-i-thru-k-equal (a :ruleArray w i k j :nat)
  :h (^ (<= i k) (<= (+ i j) k) (<= (* w (1+ k)) (len a)))
  :b (a-row-equal (+ i j) j w a (a-row-i-thru-k a w i k)))

#|
 | bossfight 4
 |#

(property survive-k-len-a (a :ruleArray w k :pos)
  :h (survive-k-steps a w k)
  :b (<= (* w (+ 1 k)) (len a)))

(property survive-k-len-ap (a :ruleArray w k :pos)
  :h (survive-k-steps a w k)
  :b (<= w (len (a-row-i-thru-k a w (+ -1 k) k)))
  :hints (("goal" :use ((:instance survive-k-len-a)))))

(property survive-k-len-b (a :ruleArray w k :pos)
  :h (survive-k-steps a w k)
  :b (= (len (b-row-k a (one-alive w) (1- k))) w)
  :hints (("goal"
	   :in-theory (disable b-row-k-definition-rule
			       board-definition-rule
			       b-row-equal-definition-rule)
	   :use ((:instance b-row-k-len (x (one-alive w)) (k (1- k)))
		 (:instance survive-k-steps-definition-rule (width w))
		 (:instance idxp->row
			    (row (1+ k))
			    (rowp (1- k))
			    (x (one-alive w))
			    (col (1- (len (one-alive w))))
			    (colp (1- (len (one-alive w)))))))))

(property survive-k-steps->exists-live-die-transition (a :ruleArray w k :pos)
  :h (survive-k-steps a w k)
  :b (let ((ap (a-row-i-thru-k a w (1- k) k))
	   (xp (b-row-k a (one-alive w) (1- k))))
       (^ (row-any ap xp 0 1)
	  (row-all ap xp 1 0)))
  :hints (("goal"
	   :do-not-induct t
	   :in-theory (disable posp
			       b-row-equal-definition-rule
			       a-row-equal-definition-rule
			       survive-k-steps-definition-rule
			       row-any-definition-rule
			       row-all-definition-rule
			       b-row-k-definition-rule)
	   :use ((:instance survive-k-len-a)
		 (:instance survive-k-len-ap)
		 (:instance survive-k-len-b) ; making these forward-chaining causes fail.
		 (:instance a-row-i-thru-k-equal (i (1- k)) (j 1))
		 (:instance b-row-k->b-row-equal (row (1- k)) (x (one-alive w)))
		 (:instance survive-k-steps->live-die-transition (a1 a) (a2 ap) (x2 xp))))))

; At this point we have shown survive-k-steps being solvable for `a`
; implies the existence of another rule array `ap` which is a subset
; of `a`, for which there exists an initial state `xp` such that `xp`
; has a black cell and the second state of the board derived from `ap`
; and `xp` has no black cells.
;
; Next we will introduce the notion of a subset and in turn a
; predicate ɸ which, via proof with a SAT solver, has the property
; (1.) below.
;
; 1. ∀a,x,ɸ(a) -> (! (^ (row-any a x 0 0 1) (row-all a x 1 0 0)))
; 2. (^ ɸ(ap) (= ap (a-row-i-thru-k a))) -> ɸ(a)
;
; Using properties of the subset, we will establish (2.) and in turn
; the following derivation will complete our proof.
;
; ∀a,w,k,sks(a,w,k) -> ∃ap,xp (^ (row-any ap xp 0 0 1) (row-all ap xp 1 0 0))
;                   -> (! ɸ(ap))
;                   -> (! ɸ(a))    {as ap ⊆ a}

(definec subset (a :ruleArray b :ruleArray) :bool
  (v (! a) (^ (in (car a) b) (subset (cdr a) b))))

(property subset-in (a :ruleNum b c :ruleArray)
  :h (^ (in a b) (subset b c))
  :b (in a c))

(property subset-transitive (a b c :ruleArray)
  :h (^ (subset a b) (subset b c))
  :b (subset a c))

(property subset-not-transitive (a b c :ruleArray)
  :h (^ (! (subset a c)) (subset a b))
  :b (! (subset b c)))

(property nth-in (a :ruleArray i :nat)
  :h (< i (len a))
  :b (in (nth i a) a))

(property i<=_<k-subset (a :ruleArray i k :nat)
  :h (<= k (len a))
  :b (subset (i<=_<k a i k) a))

(property a-row-i-thru-k-subset (a :ruleArray w i k :nat)
  :h (^ (<= (* (1+ k) w) (len a)) (<= i k))
  :b (subset (a-row-i-thru-k a w i k) a)
  :hints (("goal" :in-theory (enable a-row-i-thru-k-definition-rule))))

#|
 | final boss
 |
 | for any set of rules `S` and width `W`, we query the SAT solver and
 | ask: is there a rule array `a` containing only elements of S, for
 | which there exists an `x` with at least one black cell, such that
 | there are exclusively white cells in the first row (zero indexed)
 | of the board corresponding to `a` and `x`.
 |
 | if the SAT solver returns UNSAT, then we have, ∀a,x
 |
   (=> (^ (subset a S) (= (len x) W))
       (! (^ (row-any a x 0 0 1) (row-all a x 1 0 0))))
 |
 | as if this was false, then there would be a rule array using the
 | rules in S which transitioned from an initial state with a black
 | cell to a state with exclusively white cells, and the SAT solver
 | would have found this rule array and initial state and returned
 | SAT.
 |#

; Here we introduce a predicate cannot-transition-sat which has the
; same properties as a proof from the SAT solver.
(encapsulate
  ( ((transition-oracle * *) => *) )

  ; in the interest of having a simple witness, we use the trivial
  ; example of inability to transition with no rule array, i.e. S
  ; being the empty set.
  (local (definec transition-oracle (a :ruleArray w :nat) :bool
		  (^ (subset a '()) (= w 1))))

  (property cannot-transition-subset (a ap :ruleArray w :nat)
    :h (^ (subset ap a) (transition-oracle a w))
    :b (transition-oracle ap w))

  (property cannot-transition (a :ruleArray x :bv)
    :h (transition-oracle a (len x))
    :b (! (^ (row-any a x 0 1) (row-all a x 1 0))))
)

(property cannot-transition-contrapositive (a :ruleArray x :bv)
  :h (^ (row-any a x 0 1) (row-all a x 1 0))
  :b (! (transition-oracle a (len x)))
  :hints (("goal" :use ((:instance cannot-transition)))))

(in-theory (disable survive-k-steps-definition-rule
		    subset-definition-rule
		    b-row-k-definition-rule
		    row-any-definition-rule
		    row-all-definition-rule))

(property survive-k->not-transition-oracle (a :ruleArray w k :pos)
  :h (survive-k-steps a w k)
  :b (! (transition-oracle a w))
  :hints (("goal" :do-not-induct t
		  :use ((:instance survive-k-steps->exists-live-die-transition)
			(:instance cannot-transition-contrapositive (a (a-row-i-thru-k a w (+ -1 k) k)) (x (b-row-k a (one-alive w) (+ -1 k))))
			(:instance survive-k-len-a)))))

(property technique2 (a :ruleArray w k :pos)
  :h (transition-oracle a w)
  :b (! (survive-k-steps a w k)))
