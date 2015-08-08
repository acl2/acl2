
(in-package "ACL2")

(include-book "Disjoint-lists")

; The following is commented out starting with v2-7 because a more general
; macro e/d is now part of ACL2.
; (defmacro e/d (enable disable)
;  `(union-theories ',enable (disable ,@disable)))

(defun in-range (idx l)
  (and
   (integerp idx)
   (>= idx 0)
   (< idx (len l))))

(in-theory (enable in-range))
(in-theory (disable mod floor))

(defun mlambda-fn (args form)
  (declare (xargs :guard (symbol-listp args)))
  (cond ((atom form)
	 (cond ((member form args) form)
	       (t (list 'QUOTE form))))
	(t (list 'CONS (mlambda-fn args (car form))
		 (mlambda-fn args (cdr form))))))

(defmacro mlambda (args form)
  (declare (xargs :guard (symbol-listp args)))
  (mlambda-fn args form))


(defmacro qr-guard (x y)
  (mlambda (x y)
    (and (force (rationalp x))
	 (force (rationalp y))
	 (force (not (equal 0 y))))))

(defun type-expected (vars)
  (cond
   ( (and (true-listp vars)
	  (equal (len vars) 1))
     'Bool)
   ( (and (true-listp vars)
	  (equal (len vars) (len *rns*)))
     'Int)
   ( t
     'Wrong-Typing)))


(defthm IN-RANGE-I-ON-M-IMPLIES-IN-RANGE-I-1-ON-CDR-M
                     (IMPLIES (AND (IN-RANGE IDX M)
                                   (NOT (ENDP M))
                                   (NOT (ZP IDX)))
                              (IN-RANGE (1- IDX) (CDR M))))

(defun positivep (v)
  (and
   (integerp v)
   (> v 0)))


(defun positive-list (l)
  (if (endp l)
      (null l)
    (and (positivep (car l))
	 (positive-list (cdr l)))))


(defun boolean-to-int (bool)
  (if bool 1 0))

(defun int-to-bool (int)
  (equal int 1))

(defun make-n-list (el n)
  (if
      (zp n)
      nil
    (cons el (make-n-list el (1- n)))))

(defun eventually-make-list (l n)
  (if (equal (len l) 1)
      (make-n-list (car l) n)
    l))

(defun double-induct (idx n)
  (if (zp idx)  (+ idx n)
    (double-induct (1- idx) (1- n))))

(defthm el-of-makelist-is-el
 (implies
  (and
   (integerp n)
   (in-range idx (make-n-list el n)))
  (equal
   (nth idx (make-n-list el n))
   el))
 :hints (("Goal" :induct (double-induct idx n))
	 ("Subgoal *1/1" :use make-n-list)))






(in-theory (disable my-or-3 my-or-2))





(defun opcode (ins) (nth 0 ins))
(defun par1   (ins) (nth 1 ins))
(defun par2   (ins) (nth 2 ins))
(defun par3   (ins) (nth 3 ins))
(defun par4   (ins) (nth 4 ins))


(defun mem  (s) (car  s))
(defun pcc  (s) (cadr s))
(defun code (s) (cddr  s))

(defun make-state (mem pcc code)
  (cons mem (cons pcc code)))


(defun initial-state (prog)
  (make-state (car prog) 0 (cdr prog)))






(defun gem-instruction-p (instr mem)
  (and
   (true-listp instr)
   (or
    (and
     (equal (opcode instr) 'gem-add)
     (equal (len instr) 4)
     (is-mem-cell-p (get-cell (par1 instr) mem))
     (is-mem-cell-p (get-cell (par2 instr) mem))
     (is-mem-cell-p (get-cell (par3 instr) mem))
     (equal (var-type (get-cell (par1 instr) mem)) 'Int) )
    (and
     (equal (opcode instr) 'gem-sub)
     (equal (len instr) 4)
     (is-mem-cell-p (get-cell (par1 instr) mem))
     (is-mem-cell-p (get-cell (par2 instr) mem))
     (is-mem-cell-p (get-cell (par3 instr) mem))
     (equal (var-type (get-cell (par1 instr) mem)) 'Int)
     (equal (var-type (get-cell (par2 instr) mem)) 'Int)
     (equal (var-type (get-cell (par3 instr) mem)) 'Int) )
    (and
     (equal (opcode instr) 'gem-equ)
     (equal (len instr) 4)
     (is-mem-cell-p (get-cell (par1 instr) mem))
     (is-mem-cell-p (get-cell (par2 instr) mem))
     (is-mem-cell-p (get-cell (par3 instr) mem))
     (equal (var-type (get-cell (par1 instr) mem)) 'Bool) )
     )))


(defun gem-instruction-list-p (instlist mem)
  (if
      (endp instlist)
      (null instlist)
    (and
     (gem-instruction-p (car instlist) mem)
     (gem-instruction-list-p (cdr instlist) mem))))


(defun gem-program-p (prog)
  (and
   (true-listp prog)
   (equal (len prog) 2)
   (is-typed-amem-p (car prog))
   (bounded-amem-p  (car prog))
   (gem-instruction-list-p (cdr prog) (car prog))))


(defun gem-statep (x)
  (and (consp x)
       (consp (cdr x))
       (integerp (pcc x))
       (is-typed-amem-p (mem x))
       (bounded-amem-p (mem x))     ;;; new
       (gem-instruction-list-p (code x) (mem x))))


(defthm nth-instruction-of-gem-list-is-gem-instruction
 (implies
  (gem-instruction-list-p gl mem)
  (or
   (null (nth idx gl))
   (gem-instruction-p (nth idx gl) mem)))
 :hints (("Goal" :in-theory (disable gem-instruction-p)))
 :rule-classes nil)

(defthm an-instruction-of-gem-program-is-null-or-gem-instruction
 (implies
  (gem-statep st)
  (or
   (null (nth (pcc st) (code st)))
   (gem-instruction-p (nth (pcc st) (code st)) (mem st))))
 :hints (("Goal" :in-theory (disable code mem pcc gem-instruction-list-p gem-instruction-p)
	 :use (:instance nth-instruction-of-gem-list-is-gem-instruction
			 (gl (code st))
			 (idx (pcc st))
			 (mem (mem st)))))
 :rule-classes nil)











(defun rtm-instruction-p (instr mem)
  (and
   (true-listp instr)
   (or
    (and
     (equal (opcode instr) 'rtm-add)
     (equal (len instr) 4)
     (is-mem-cell-p (get-cell (par1 instr) mem))
     (is-mem-cell-p (get-cell (par2 instr) mem))
     (is-mem-cell-p (get-cell (par3 instr) mem))
     (equal (var-type (get-cell (par1 instr) mem)) 'Int)
     (equal (var-type (get-cell (par2 instr) mem)) 'Int)
     (equal (var-type (get-cell (par3 instr) mem)) 'Int)
     (positivep (par4 instr)))
    (and
     (equal (opcode instr) 'rtm-sub)
     (equal (len instr) 4)
     (is-mem-cell-p (get-cell (par1 instr) mem))
     (is-mem-cell-p (get-cell (par2 instr) mem))
     (is-mem-cell-p (get-cell (par3 instr) mem))
     (equal (var-type (get-cell (par1 instr) mem)) 'Int)
     (equal (var-type (get-cell (par2 instr) mem)) 'Int)
     (equal (var-type (get-cell (par3 instr) mem)) 'Int)
     (positivep (par4 instr)))
    (and
     (equal (opcode instr) 'rtm-equ)
     (equal (len instr) 4)
     (is-mem-cell-p (get-cell (par1 instr) mem))
     (is-mem-cell-p (get-cell (par2 instr) mem))
     (is-mem-cell-p (get-cell (par3 instr) mem))
     (equal (var-type (get-cell (par1 instr) mem)) 'Int)
     (equal (var-type (get-cell (par2 instr) mem)) 'Int)
     (equal (var-type (get-cell (par3 instr) mem)) 'Int))
    (and
     (equal (opcode instr) 'rtm-or)
     (equal (len instr) 4)
     (is-mem-cell-p (get-cell (par1 instr) mem))
     (is-mem-cell-p (get-cell (par2 instr) mem))
     (is-mem-cell-p (get-cell (par3 instr) mem))
     (equal (var-type (get-cell (par1 instr) mem)) 'Int)
     (equal (var-type (get-cell (par2 instr) mem)) 'Int)
     (equal (var-type (get-cell (par3 instr) mem)) 'Int))
    (and
     (equal (opcode instr) 'rtm-and)
     (equal (len instr) 4)
     (is-mem-cell-p (get-cell (par1 instr) mem))
     (is-mem-cell-p (get-cell (par2 instr) mem))
     (is-mem-cell-p (get-cell (par3 instr) mem))
     (equal (var-type (get-cell (par1 instr) mem)) 'Int)
     (equal (var-type (get-cell (par2 instr) mem)) 'Int)
     (equal (var-type (get-cell (par3 instr) mem)) 'Int)))))

(defun rtm-instruction-list-p (instlist mem)
  (if
      (endp instlist)
      (null instlist)
    (and
     (rtm-instruction-p (car instlist) mem)
     (rtm-instruction-list-p (cdr instlist) mem))))


(defun rtm-program-p (prog)
  (and
   (true-listp prog)
   (equal (len prog) 2)
   (is-typed-amem-p (car prog))
   (rtm-instruction-list-p (cdr prog) (car prog))))




(defun rtm-statep (x)
  (and (consp x)
       (consp (cdr x))
       (integerp (pcc x))
       (is-typed-amem-p (mem x))
       (rtm-instruction-list-p (code x) (mem x))))







(defthm nth-instruction-of-rtm-list-is-rtm-instruction
 (implies
  (rtm-instruction-list-p gl mem)
  (or
   (null (nth idx gl))
   (rtm-instruction-p (nth idx gl) mem)))
 :hints (("Goal" :in-theory (disable rtm-instruction-p)))
 :rule-classes nil)

(defthm an-instruction-of-rtm-program-is-null-or-rtm-instruction
 (implies
  (rtm-statep st)
  (or
   (null (nth (pcc st) (code st)))
   (rtm-instruction-p (nth (pcc st) (code st)) (mem st))))
 :hints (("Goal" :in-theory (disable code mem pcc rtm-instruction-list-p rtm-instruction-p)
	 :use (:instance nth-instruction-of-rtm-list-is-rtm-instruction
			 (gl (code st))
			 (idx (pcc st))
			 (mem (mem st)))))
 :rule-classes nil)






(defun sum-and-update (c1 c2 c3 prime mem)
  (make-cell
   (mod
    (+
     (var-value (get-cell c2 mem))
     (var-value (get-cell c3 mem)))
    prime)
   (var-attribute (get-cell c1 mem))
   (var-type (get-cell c1 mem))))


(DEFUN SUM-AND-UPDATE-NOREST  (C1 C2 C3 MEM)
  (MAKE-CELL (mod
	      (+ (VAR-VALUE (GET-CELL C2 MEM))
		 (VAR-VALUE (GET-CELL C3 MEM)))
	      (prod *rns*))
  (VAR-ATTRIBUTE (GET-CELL C1 MEM))
  (VAR-TYPE (GET-CELL C1 MEM))))

(defun sub-and-update (c1 c2 c3 prime mem)
  (make-cell
   (mod
    (-
     (var-value (get-cell c2 mem))
     (var-value (get-cell c3 mem)))
    prime)
   (var-attribute (get-cell c1 mem))
   (var-type (get-cell c1 mem))))


(DEFUN SUB-AND-UPDATE-NOREST  (C1 C2 C3 MEM)
  (MAKE-CELL (mod
	      (- (VAR-VALUE (GET-CELL C2 MEM))
		 (VAR-VALUE (GET-CELL C3 MEM)))
	      (prod *rns*))
  (VAR-ATTRIBUTE (GET-CELL C1 MEM))
  (VAR-TYPE (GET-CELL C1 MEM))))



(defun and-update (c1 c2 c3 mem)
  (make-cell
   (boolean-to-int
    (and
     (int-to-bool (var-value (get-cell c2 mem)))
     (int-to-bool (var-value (get-cell c3 mem)))))
   (var-attribute (get-cell c1 mem))
   (var-type (get-cell c1 mem))))

(defun or-update (c1 c2 c3 mem)
  (make-cell
   (boolean-to-int
    (or
     (int-to-bool (var-value (get-cell c2 mem)))
     (int-to-bool (var-value (get-cell c3 mem)))))
   (var-attribute (get-cell c1 mem))
   (var-type (get-cell c1 mem))))

(defun gen-eq-update (c1 c2 c3 mem)
  (make-cell
   (boolean-to-int
    (equal
     (var-value (get-cell c2 mem))
     (var-value (get-cell c3 mem))))
   (var-attribute (get-cell c1 mem))
   (var-type (get-cell c1 mem))))





(defthm sum-and-update-returns-a-mem-cell
 (implies
  (and
   (equal (var-type (get-cell c1 mem)) 'Int) ; This is added to account for booleans
   (is-mem-cell-p (get-cell c1 mem))
   (is-mem-cell-p (get-cell c2 mem))
   (is-mem-cell-p (get-cell c3 mem))
   (positivep prime))
  (is-mem-cell-p (sum-and-update c1 c2 c3 prime mem)))
 :hints (("Goal" :in-theory (enable mod make-cell var-type var-attribute var-value)))
 :rule-classes :forward-chaining)

#|
(defthm gcd-unfold
 (equal (g-c-d x y)
	(IF (ZP X)
	    Y
	    (IF (ZP Y)
		X
		(IF (<= X Y)
		    (G-C-D X (- Y X))
		    (G-C-D (- X Y) Y)))))
  :hints (("Goal" :in-theory (enable g-c-d nonneg-int-gcd
				     (:executable-counterpart nonneg-int-gcd)
				     (:induction nonneg-int-gcd)))))
|#


(defthm posp-all-unfold
  (equal (posp-all l)
	 (IF (ENDP L)
	     T
	     (AND (POSP (CAR L))
		  (POSP-ALL (CDR L)))))
  :hints (("Goal" :in-theory (enable posp-all))))

(defun integer>1-listp (l)
  (if (endp l)
      (null l)
    (and (integerp (car l))
	 (> (car l) 1)
	 (integer>1-listp (cdr l)))))


(defthm int>1-unfold
  (equal (integer>1-listp l)
	 (IF (ENDP L)
	     (NULL L)
	     (AND (INTEGERP (CAR L))
		  (> (CAR L) 1)
		  (INTEGER>1-LISTP (CDR L))))))


(defthm fact-bout-rns
  (and
   (integer-listp *rns*)
   (rel-prime-moduli *rns*)
   (posp-all *rns*)
   (integer>1-listp *rns*)
   (not (null *rns*))
   (natp (prod *rns*))
   (> (prod *rns*) 1))
  :hints (("Goal" :in-theory (enable prod posp rel-prime-moduli rel-prime-all rel-prime g-c-d (:executable-counterpart nonneg-int-gcd))))
  :rule-classes nil)

(in-theory (disable
	    ;gcd-unfold
	    posp-all-unfold int>1-unfold))

(defthm greater-one-means-greater-zero
  (implies (integer>1-listp rns) (posp-all rns))
  :hints (("Goal"
	   :in-theory (enable posp-all posp)))
  :rule-classes nil)

(DEFTHM SILS1A
  (IMPLIES (AND (POSP M) (INTEGERP A))
	   (NATP (MOD A M)))
  :HINTS
  (("Goal" :IN-THEORY
    '((:REWRITE INTEGERP-MOD-EXP)
      (:DEFINITION NATP)
      (:DEFINITION POSP))
    :USE
    ((:INSTANCE MOD-TYPE-EXP (X A) (Y M))
     (:INSTANCE MOD-=-0-EXP (X A) (Y M)))))
  :rule-classes nil)

(defthm sum-and-update-norest-returns-a-mem-cell
 (implies
  (and
   (equal (var-type (get-cell c1 mem)) 'Int)
   (is-mem-cell-p (get-cell c1 mem))
   (is-mem-cell-p (get-cell c2 mem))
   (is-mem-cell-p (get-cell c3 mem)))
  (and
   (is-mem-cell-p (sum-and-update-norest c1 c2 c3 mem))
   (bounded-value (sum-and-update-norest c1 c2 c3 mem))
   (equal (var-type (sum-and-update-norest c1 c2 c3 mem)) 'Int))   )
 :hints (("Goal"
	  :use (fact-bout-rns
		(:instance sils1a
			   (a (+ (var-value (get-cell c2 mem)) (var-value (get-cell c3 mem))))
			   (m (prod *rns*)))
		(:instance mod-bounds-exp
			  (x (+ (var-value (get-cell c2 mem)) (var-value (get-cell c3 mem))))
			  (y (prod *rns*))))
	  :in-theory (enable posp make-cell var-type var-attribute var-value)))
 :rule-classes :forward-chaining)


(defthm sub-and-update-returns-a-mem-cell
 (implies
  (and
   (equal (var-type (get-cell c1 mem)) 'Int)
   (is-mem-cell-p (get-cell c1 mem))
   (is-mem-cell-p (get-cell c2 mem))
   (is-mem-cell-p (get-cell c3 mem))
   (positivep prime) )
  (is-mem-cell-p (sub-and-update c1 c2 c3 prime mem)))
 :hints (("Goal" :in-theory (enable mod make-cell var-type var-attribute var-value)))
 :rule-classes :forward-chaining)


(defthm sub-and-update-norest-returns-a-mem-cell
 (implies
  (and
   (equal (var-type (get-cell c1 mem)) 'Int)
   (is-mem-cell-p (get-cell c1 mem))
   (is-mem-cell-p (get-cell c2 mem))
   (is-mem-cell-p (get-cell c3 mem)))
  (and
   (is-mem-cell-p (sub-and-update-norest c1 c2 c3 mem))
   (bounded-value (sub-and-update-norest c1 c2 c3 mem))
   (equal (var-type (sub-and-update-norest c1 c2 c3 mem)) 'Int))   )
 :hints (("Goal"
	  :use (fact-bout-rns
		(:instance sils1a
			   (a (- (var-value (get-cell c2 mem)) (var-value (get-cell c3 mem))))
			   (m (prod *rns*)))
		(:instance mod-bounds-exp
			  (x (- (var-value (get-cell c2 mem)) (var-value (get-cell c3 mem))))
			  (y (prod *rns*))))
	  :in-theory (enable posp make-cell var-type var-attribute var-value)))
 :rule-classes :forward-chaining)


(defthm and-update-returns-a-mem-cell
 (implies
  (and
   (is-mem-cell-p (get-cell c1 mem))
   (is-mem-cell-p (get-cell c2 mem))
   (is-mem-cell-p (get-cell c3 mem)))
  (is-mem-cell-p (and-update c1 c2 c3 mem)))
 :hints (("Goal" :in-theory (enable my-or-2 make-cell var-type var-attribute var-value)))
 :rule-classes :forward-chaining)

(defthm or-update-returns-a-mem-cell
 (implies
  (and
   (is-mem-cell-p (get-cell c1 mem))
   (is-mem-cell-p (get-cell c2 mem))
   (is-mem-cell-p (get-cell c3 mem)))
  (is-mem-cell-p (or-update c1 c2 c3 mem)))
 :hints (("Goal" :in-theory (enable my-or-2 make-cell var-type var-attribute var-value)))
 :rule-classes :forward-chaining)

(defthm gen-eq-update-returns-a-mem-cell
 (implies
  (and
   (is-mem-cell-p (get-cell c1 mem))
   (is-mem-cell-p (get-cell c2 mem))
   (is-mem-cell-p (get-cell c3 mem)))
  (and
   (bounded-value (gen-eq-update c1 c2 c3 mem))
   (is-mem-cell-p (gen-eq-update c1 c2 c3 mem))))
 :hints (("Goal"
	  :use (fact-bout-rns
		(:instance sils1a
			   (a (boolean-to-int (equal (var-value (get-cell c2 mem)) (var-value (get-cell c3 mem)))))
			   (m (prod *rns*)))
		(:instance mod-bounds-exp
			  (x (boolean-to-int (equal (var-value (get-cell c2 mem)) (var-value (get-cell c3 mem)))))
			  (y (prod *rns*))))
	  :in-theory (enable posp my-or-2 make-cell var-type var-attribute var-value)))
 :rule-classes :forward-chaining)











(defun gem-add (a b c s)
  (make-state
   (put-cell a
	     (sum-and-update-norest a b c (mem s))
	     (mem s))
   (1+ (pcc s))
   (code s)))

(defun gem-sub (a b c s)
  (make-state
   (put-cell a
	     (sub-and-update-norest a b c (mem s))
	     (mem s))
   (1+ (pcc s))
   (code s)))

(defun rtm-add (a b c d s)
  (make-state
   (put-cell a
	     (sum-and-update a b c d (mem s))
	     (mem s))
   (1+ (pcc s))
   (code s)))

(defun rtm-sub (a b c d s)
  (make-state
   (put-cell a
	     (sub-and-update a b c d (mem s))
	     (mem s))
   (1+ (pcc s))
   (code s)))


(defun rtm-and (a b c s)
  (make-state
   (put-cell a
	     (and-update a b c (mem s))
	     (mem s))
   (1+ (pcc s))
   (code s)))

(defun rtm-or (a b c s)
  (make-state
   (put-cell a
	     (or-update a b c (mem s))
	     (mem s))
   (1+ (pcc s))
   (code s)))

(defun generic-eql (a b c s)
  (make-state
   (put-cell a
	     (gen-eq-update a b c (mem s))
	     (mem s))
   (1+ (pcc s))
   (code s)))



(defun execute-instruction (st)
  (let
      ((op (opcode (nth (pcc st) (code st))))
       (ins (nth (pcc st) (code st))))
  (case op
	(gem-add  (gem-add     (par1 ins) (par2 ins) (par3 ins) st))
	(gem-sub  (gem-sub     (par1 ins) (par2 ins) (par3 ins) st))
	(gem-equ  (generic-eql (par1 ins) (par2 ins) (par3 ins) st))
	(rtm-add  (rtm-add     (par1 ins) (par2 ins) (par3 ins) (par4 ins) st))
	(rtm-sub  (rtm-sub     (par1 ins) (par2 ins) (par3 ins) (par4 ins) st))
	(rtm-and  (rtm-and     (par1 ins) (par2 ins) (par3 ins) st))
	(rtm-or   (rtm-or      (par1 ins) (par2 ins) (par3 ins) st))
	(rtm-equ  (generic-eql (par1 ins) (par2 ins) (par3 ins) st))
        (otherwise st))))


(defun execute-n-instructions (st n)
 (if
      (zp n)
      st
    (execute-n-instructions
     (execute-instruction st)
     (1- n))))



(defthm instruction-incrementing-pvv
 (implies
  (>= (pcc st) 0)
  (>= (pcc (execute-instruction st)) 0)))




(defthm in-range-instruction-is-gem-instruction
 (implies
  (and
   (in-range pcc code)
   (gem-instruction-list-p code mem))
  (gem-instruction-p (nth pcc code) mem))
 :hints (("Goal" :in-theory (disable gem-instruction-p)))
 :rule-classes :forward-chaining)



(defthm in-range-instruction-is-rtmm-instruction
 (implies
  (and
   (in-range pcc code)
   (rtm-instruction-list-p code mem))
  (rtm-instruction-p (nth pcc code) mem))
 :hints (("Goal" :in-theory (disable rtm-instruction-p)))
 :rule-classes :forward-chaining)





(defthm null-not-in-range
 (implies
  (and
   (integerp idx)
   (>= idx 0)
   (not (in-range idx l)))
  (null (nth idx l)))
 :rule-classes :forward-chaining)

(defthm pcc-not-in-range-means-null-instruction
  (implies
   (and
    (or
     (gem-statep st)
     (rtm-statep st))
    (>= (pcc st) 0)
    (not (in-range (pcc st) (code st))))
   (null (nth (pcc st) (code st))))
  :hints (("Goal" :cases ( (gem-statep st) (rtm-statep st))))
  :rule-classes :forward-chaining)

(defthm null-opcode-implies-execution-does-not-touch-state
  (implies
   (null (nth (pcc st) (code st)))
   (equal (execute-instruction st) st)))

(defthm execute-not-in-range-instruction-retrieves-same-state
  (implies
   (and
    (or
     (gem-statep st)
     (rtm-statep st) )
    (>= (pcc st) 0)
    (not (in-range (pcc st) (code st))))
   (equal (execute-instruction st) st))
  :hints (("Goal" :cases ( (gem-statep st) (rtm-statep st) ))
	  ("Subgoal 2" :use ((:instance gem-statep (x st))
			     null-opcode-implies-execution-does-not-touch-state
			     pcc-not-in-range-means-null-instruction))
	  ("Subgoal 1" :use ((:instance rtm-statep (x st))
			     null-opcode-implies-execution-does-not-touch-state
			     pcc-not-in-range-means-null-instruction))))

(in-theory (disable null-opcode-implies-execution-does-not-touch-state
		    execute-not-in-range-instruction-retrieves-same-state))


(defthm execute-instruction-does-not-touch-code (equal (code (execute-instruction st)) (code st)))

(defthm execute-n-instruction-does-not-touch-code (equal (code (execute-n-instructions st n)) (code st)))

(defthm execute-n-instruction-decomposition
 (implies
  (and
   (integerp n1)
   (integerp n2)
   (>= n1 0)
   (>= n2 0))
 (equal
  (execute-n-instructions st (+ n1 n2))
  (execute-n-instructions (execute-n-instructions st n1) n2)))
 :hints (("Goal" :in-theory (disable execute-instruction member-equal))))


(defthm putting-a-new-cell-preserves-typed-amem
 (implies
  (and
   (is-typed-amem-p mem)
   (is-mem-cell-p new-cell))
  (is-typed-amem-p (put-cell c new-cell mem)))
:hints (("Goal" :in-theory (enable put-cell))))

(defthm no-influence-of-putting-mem-cells
 (implies
  (and
   (is-mem-cell-p cell)
   (is-mem-cell-p (get-cell c1 mem)))
  (is-mem-cell-p (get-cell c1 (put-cell pos cell mem))))
 :hints ( ("Goal" :in-theory (enable put-cell get-cell) )))


(defthm putting-a-new-bounded-cell-preserves-boundedness
 (implies
  (and
   (bounded-amem-p mem)
   (bounded-value new-cell))
  (bounded-amem-p (put-cell c new-cell mem)))
:hints (("Goal" :in-theory (enable put-cell))))

(defthm no-influence-of-putting-bounded-cells
 (implies
  (and
   (bounded-value cell)
   (bounded-value (get-cell c1 mem)))
  (bounded-value (get-cell c1 (put-cell pos cell mem))))
 :hints ( ("Goal" :in-theory (enable put-cell get-cell) )))



(defthm putting-an-existing-cell-does-not-change-var-inclusion-right
 (implies
  (is-mem-cell-p (get-cell v mem))
  (iff (vars-inclusion m mem) (vars-inclusion m (put-cell v anyvalue mem))))
 :hints (("Goal" :in-theory (enable put-cell get-cell is-mem-cell-p))))

(defthm  putting-an-existing-cell-does-not-change-var-inclusion-left
 (implies
  (is-mem-cell-p (get-cell v mem))
  (iff (vars-inclusion mem m) (vars-inclusion (put-cell v anyvalue mem) m)))
 :hints (("Goal" :in-theory (enable put-cell get-cell is-mem-cell-p))))



(defthm execute-instruction-is-type-and-attribute-invariant-on-any-var
 (and
 (equal (var-attribute (get-cell cell (mem st)))
	(var-attribute (get-cell cell (mem (execute-instruction st)))))
 (equal (var-type (get-cell cell (mem st)))
	(var-type (get-cell cell (mem (execute-instruction st))))))
 :hints (("Goal" :in-theory (enable put-cell get-cell make-cell mem make-state var-attribute var-type))))



(in-theory (disable
	    putting-an-existing-cell-does-not-change-var-inclusion-left
	    putting-an-existing-cell-does-not-change-var-inclusion-right
	    ))






;;(ld "Properties-of-Execute-Gem-Instruction-New.lisp" :ld-error-action :error)



(defthm any-mem-cell-is-conserved-after-execute-instruction-on-gemstate
 (implies (and
	   (gem-statep st)
	   (is-mem-cell-p (get-cell anycell (mem st))))
	  (is-mem-cell-p (get-cell anycell (mem (execute-instruction st)))))
:hints (("Goal" :cases ( (null (nth (pcc st) (code st))) (gem-instruction-p (nth (pcc st) (code st)) (mem st))))
	("Subgoal 3" :use an-instruction-of-gem-program-is-null-or-gem-instruction)
	("Subgoal 1" :use (execute-instruction
			   (:instance sum-and-update-norest-returns-a-mem-cell
				      (c1 (par1 (nth (pcc st) (code st))))
				      (c2 (par2 (nth (pcc st) (code st))))
				      (c3 (par3 (nth (pcc st) (code st))))
				      (mem (mem st)))
			   (:instance sub-and-update-norest-returns-a-mem-cell
				      (c1 (par1 (nth (pcc st) (code st))))
				      (c2 (par2 (nth (pcc st) (code st))))
				      (c3 (par3 (nth (pcc st) (code st))))
				      (mem (mem st)))
			   (:instance gen-eq-update-returns-a-mem-cell
				      (c1 (par1 (nth (pcc st) (code st))))
				      (c2 (par2 (nth (pcc st) (code st))))
				      (c3 (par3 (nth (pcc st) (code st))))
				      (mem (mem st))))
	 :in-theory (disable bounded-value put-cell get-cell execute-instruction
			     sum-and-update-norest sub-and-update-norest gen-eq-update
			     par1 par2 par3 par4 member-equal nth rtm-add rtm-sub is-mem-cell-p))))

(defthm any-bounded-cell-is-bounded-after-execute-instruction-on-gemstate
 (implies (and
	   (gem-statep st)
	   (bounded-value (get-cell anycell (mem st))))
	  (bounded-value (get-cell anycell (mem (execute-instruction st)))))
:hints (("Goal" :cases ( (null (nth (pcc st) (code st))) (gem-instruction-p (nth (pcc st) (code st)) (mem st))))
	("Subgoal 3" :use an-instruction-of-gem-program-is-null-or-gem-instruction)
	("Subgoal 1" :use (execute-instruction
			   (:instance sum-and-update-norest-returns-a-mem-cell
				      (c1 (par1 (nth (pcc st) (code st))))
				      (c2 (par2 (nth (pcc st) (code st))))
				      (c3 (par3 (nth (pcc st) (code st))))
				      (mem (mem st)))
			   (:instance sub-and-update-norest-returns-a-mem-cell
				      (c1 (par1 (nth (pcc st) (code st))))
				      (c2 (par2 (nth (pcc st) (code st))))
				      (c3 (par3 (nth (pcc st) (code st))))
				      (mem (mem st)))
			   (:instance gen-eq-update-returns-a-mem-cell
				      (c1 (par1 (nth (pcc st) (code st))))
				      (c2 (par2 (nth (pcc st) (code st))))
				      (c3 (par3 (nth (pcc st) (code st))))
				      (mem (mem st))))
	 :in-theory (disable bounded-value put-cell get-cell execute-instruction bounded-value
			     sum-and-update-norest sub-and-update-norest gen-eq-update
			     par1 par2 par3 par4 member-equal nth rtm-add rtm-sub is-mem-cell-p))))

#|
(defthm execute-instruction-is-type-and-attribute-invariant-on-any-var
 (and
 (equal (var-attribute (get-cell cell (mem st)))
	(var-attribute (get-cell cell (mem (execute-instruction st)))))
 (equal (var-type (get-cell cell (mem st)))
	(var-type (get-cell cell (mem (execute-instruction st))))))
 :hints (("Goal" :in-theory (enable put-cell get-cell make-cell mem make-state var-attribute var-type))))
|#

(defthm any-gem-instruction-is-conserved-by-execution
 (implies
  (and
   (gem-statep st)
   (gem-instruction-p  instr (mem st)))
 (gem-instruction-p instr (mem (execute-instruction st))))
  :hints (("Goal"
	   :in-theory '((:definition gem-instruction-p))
	   :use
	   (
	     (:instance any-mem-cell-is-conserved-after-execute-instruction-on-gemstate
			(anycell  (par1 instr)))
	     (:instance any-mem-cell-is-conserved-after-execute-instruction-on-gemstate
			(anycell  (par2 instr)))
	     (:instance any-mem-cell-is-conserved-after-execute-instruction-on-gemstate
			(anycell  (par3 instr)))
	     (:instance execute-instruction-is-type-and-attribute-invariant-on-any-var
			(cell  (par1 instr)))
	     (:instance execute-instruction-is-type-and-attribute-invariant-on-any-var
			(cell  (par2 instr)))
	     (:instance execute-instruction-is-type-and-attribute-invariant-on-any-var
			(cell  (par3 instr)))))))



(defthm a-gem-instruction-list-is-such-after-execute-instruction
 (implies
  (and
   (gem-statep st)
   (gem-instruction-list-p  instrlist (mem st)))
 (gem-instruction-list-p instrlist (mem (execute-instruction st))))
  :hints (("Goal"
	   :induct  (gem-instruction-list-p  instrlist (mem st)) ;(len instrlist)
	   :in-theory (disable execute-instruction))
	  ("Subgoal *1/3" :use (:instance gem-instruction-list-p  (instlist instrlist) (mem (mem st))))
	  ("Subgoal *1/2"
	   :in-theory (union-theories (current-theory 'ground-zero) '((:definition gem-instruction-list-p)))
	   :use (:instance any-gem-instruction-is-conserved-by-execution (instr (car instrlist))))))




(defthm execute-gem-retrieves-a-memory
  (implies
   (and
    (gem-statep st)
    (gem-instruction-p (nth (pcc st) (code st)) (mem st)))
   (and
    (bounded-amem-p (mem (execute-instruction st)))
    (is-typed-amem-p (mem (execute-instruction st)))))
  :hints (("Goal"
	   :in-theory (disable is-mem-cell-p sum-and-update-norest sub-and-update-norest gen-eq-update)
	   :use (
		 (:instance gen-eq-update-returns-a-mem-cell
			    (c1 (par1 (nth (pcc st) (code st))))
			    (c2 (par2 (nth (pcc st) (code st))))
			    (c3 (par3 (nth (pcc st) (code st))))
			    (mem (mem st)))
		 (:instance sum-and-update-norest-returns-a-mem-cell
			    (c1 (par1 (nth (pcc st) (code st))))
			    (c2 (par2 (nth (pcc st) (code st))))
			    (c3 (par3 (nth (pcc st) (code st))))
			    (mem (mem st)))
		 (:instance sub-and-update-norest-returns-a-mem-cell
			    (c1 (par1 (nth (pcc st) (code st))))
			    (c2 (par2 (nth (pcc st) (code st))))
			    (c3 (par3 (nth (pcc st) (code st))))
			    (mem (mem st)))))))



(defthm executing-gem-instruction-retrieves-a-gem-state-from-gem-state
  (implies
   (gem-statep st)
   (gem-statep (execute-instruction st)))
  :hints (("Goal" :cases ( (null (nth (pcc st) (code st))) (gem-instruction-p (nth (pcc st) (code st)) (mem st))))
	  ("Subgoal 3" :use an-instruction-of-gem-program-is-null-or-gem-instruction)
	  ("Subgoal 1"
	  :use (
		(:instance a-gem-instruction-list-is-such-after-execute-instruction (instrlist (code st)))
		(:instance execute-gem-retrieves-a-memory))
  :in-theory (disable sum-and-update-norest sub-and-update-norest gen-eq-update gem-instruction-p
			      par1 par2 par3 par4 member-equal nth))))





(defthm executing-gem-instruction-preserves-correctness-wrt-arity
 (implies
  (and
   (gem-statep st)
   (correct-wrt-arity m (mem st)))
  (correct-wrt-arity  m (mem (execute-instruction st))))
 :hints (("Goal" :in-theory (disable correct-type  gemvar-0 var-type gem-statep pcc nth execute-instruction type-0))
	 ("Subgoal *1/3" :use (:instance execute-instruction-is-type-and-attribute-invariant-on-any-var (cell (gemvar-0 m))))))





(defthm executing-gem-instruction-keeps-vars-inclusion-right
 (implies
  (gem-statep st)
  (iff (vars-inclusion m (mem st)) (vars-inclusion m (mem (execute-instruction st)))))
  :hints (("Goal" :cases ( (null (nth (pcc st) (code st))) (gem-instruction-p (nth (pcc st) (code st)) (mem st))))
	  ("Subgoal 3" :use an-instruction-of-gem-program-is-null-or-gem-instruction)
	  ("Subgoal 1" :in-theory (disable par1 par2 par3 par4 sum-and-update-norest opcode code pcc member-equal nth)
	   :cases  ( (equal (opcode (nth (pcc st) (code st))) 'gem-equ)
		     (equal (opcode (nth (pcc st) (code st))) 'gem-add)
		     (equal (opcode (nth (pcc st) (code st))) 'gem-sub)))
	  ("Subgoal 1.3" :in-theory '((:rewrite car-cons)
				      (:definition make-state)
				      (:definition mem)
				      (:definition generic-eql)
				      (:definition execute-instruction)
				      (:definition gem-instruction-p))
	   :use			       (:instance putting-an-existing-cell-does-not-change-var-inclusion-right
					 (mem (mem st))
					 (v (par1 (nth (pcc st) (code st))))
					 (anyvalue (gen-eq-update
						    (par1 (nth (pcc st) (code st)))
						    (par2 (nth (pcc st) (code st)))
						    (par3 (nth (pcc st) (code st)))
						    (mem st)))))
	  ("Subgoal 1.2" :in-theory '((:rewrite car-cons)
				      (:definition make-state)
				      (:definition mem)
				      (:definition gem-add)
				      (:definition execute-instruction)
				      (:definition gem-instruction-p))
	   :use			       (:instance putting-an-existing-cell-does-not-change-var-inclusion-right
					 (mem (mem st))
					 (v (par1 (nth (pcc st) (code st))))
					 (anyvalue (sum-and-update-norest
						    (par1 (nth (pcc st) (code st)))
						    (par2 (nth (pcc st) (code st)))
						    (par3 (nth (pcc st) (code st)))
						    (mem st)))))
	  ("Subgoal 1.1" :in-theory '((:rewrite car-cons)
				      (:definition make-state)
				      (:definition mem)
				      (:definition gem-sub)
				      (:definition execute-instruction)
				      (:definition gem-instruction-p))
	   :use			       (:instance putting-an-existing-cell-does-not-change-var-inclusion-right
					 (mem (mem st))
					 (v (par1 (nth (pcc st) (code st))))
					 (anyvalue (sub-and-update-norest
						    (par1 (nth (pcc st) (code st)))
						    (par2 (nth (pcc st) (code st)))
						    (par3 (nth (pcc st) (code st)))
						    (mem st)))))))

(defthm executing-gem-instruction-keeps-vars-inclusion-left
 (implies
  (gem-statep st)
  (iff (vars-inclusion (mem st) m) (vars-inclusion (mem (execute-instruction st)) m)))
  :hints (("Goal" :cases ( (null (nth (pcc st) (code st))) (gem-instruction-p (nth (pcc st) (code st)) (mem st))))
	  ("Subgoal 3" :use an-instruction-of-gem-program-is-null-or-gem-instruction)
	  ("Subgoal 1" :in-theory (disable par1 par2 par3 par4 sum-and-update-norest opcode code pcc member-equal nth)
	   :cases  ( (equal (opcode (nth (pcc st) (code st))) 'gem-equ)
		     (equal (opcode (nth (pcc st) (code st))) 'gem-add)
		     (equal (opcode (nth (pcc st) (code st))) 'gem-sub)))
	  ("Subgoal 1.3" :in-theory '((:rewrite car-cons)
				      (:definition make-state)
				      (:definition mem)
				      (:definition generic-eql)
				      (:definition execute-instruction)
				      (:definition gem-instruction-p))
	   :use			       (:instance putting-an-existing-cell-does-not-change-var-inclusion-left
					 (mem (mem st))
					 (v (par1 (nth (pcc st) (code st))))
					 (anyvalue (gen-eq-update
						    (par1 (nth (pcc st) (code st)))
						    (par2 (nth (pcc st) (code st)))
						    (par3 (nth (pcc st) (code st)))
						    (mem st)))))
	  ("Subgoal 1.2" :in-theory '((:rewrite car-cons)
				      (:definition make-state)
				      (:definition mem)
				      (:definition gem-add)
				      (:definition execute-instruction)
				      (:definition gem-instruction-p))
	   :use			       (:instance putting-an-existing-cell-does-not-change-var-inclusion-left
					 (mem (mem st))
					 (v (par1 (nth (pcc st) (code st))))
					 (anyvalue (sum-and-update-norest
						    (par1 (nth (pcc st) (code st)))
						    (par2 (nth (pcc st) (code st)))
						    (par3 (nth (pcc st) (code st)))
						    (mem st)))))
	  ("Subgoal 1.1" :in-theory '((:rewrite car-cons)
				      (:definition make-state)
				      (:definition mem)
				      (:definition gem-sub)
				      (:definition execute-instruction)
				      (:definition gem-instruction-p))
	   :use			       (:instance putting-an-existing-cell-does-not-change-var-inclusion-left
					 (mem (mem st))
					 (v (par1 (nth (pcc st) (code st))))
					 (anyvalue (sub-and-update-norest
						    (par1 (nth (pcc st) (code st)))
						    (par2 (nth (pcc st) (code st)))
						    (par3 (nth (pcc st) (code st)))
						    (mem st)))))))


;;(ld "Properties-of-Execute-n-Rtm-Instructions-New.lisp" :ld-error-action :error)



(defthm any-mem-cell-is-conserved-after-execute-instruction-on-rtmstate
 (implies (and
	   (rtm-statep st)
	   (is-mem-cell-p (get-cell anycell (mem st))))
	  (is-mem-cell-p (get-cell anycell (mem (execute-instruction st)))))
:hints (("Goal" :cases ( (null (nth (pcc st) (code st))) (rtm-instruction-p (nth (pcc st) (code st)) (mem st))))
	("Subgoal 3" :use an-instruction-of-rtm-program-is-null-or-rtm-instruction)
	("Subgoal 1" :use (execute-instruction
			   (:instance gen-eq-update-returns-a-mem-cell
				      (c1 (par1 (nth (pcc st) (code st))))
				      (c2 (par2 (nth (pcc st) (code st))))
				      (c3 (par3 (nth (pcc st) (code st))))
				      (mem (mem st)))
			   (:instance and-update-returns-a-mem-cell
				      (c1 (par1 (nth (pcc st) (code st))))
				      (c2 (par2 (nth (pcc st) (code st))))
				      (c3 (par3 (nth (pcc st) (code st))))
				      (mem (mem st)))
			   (:instance or-update-returns-a-mem-cell
				      (c1 (par1 (nth (pcc st) (code st))))
				      (c2 (par2 (nth (pcc st) (code st))))
				      (c3 (par3 (nth (pcc st) (code st))))
				      (mem (mem st)))
			   (:instance sum-and-update-returns-a-mem-cell
				      (c1 (par1 (nth (pcc st) (code st))))
				      (c2 (par2 (nth (pcc st) (code st))))
				      (c3 (par3 (nth (pcc st) (code st))))
				      (prime (par4 (nth (pcc st) (code st))))
				      (mem (mem st)))
			   (:instance sub-and-update-returns-a-mem-cell
				      (c1 (par1 (nth (pcc st) (code st))))
				      (c2 (par2 (nth (pcc st) (code st))))
				      (c3 (par3 (nth (pcc st) (code st))))
				      (prime (par4 (nth (pcc st) (code st))))
				      (mem (mem st))))
	 :in-theory (disable put-cell get-cell execute-instruction
			     sum-and-update sub-and-update and-update or-update gen-eq-update
			     par1 par2 par3 par4 member-equal nth gem-add gem-sub is-mem-cell-p))))


(defthm any-rtm-instruction-is-conserved-by-execution
 (implies
  (and
   (rtm-statep st)
   (rtm-instruction-p  instr (mem st)))
 (rtm-instruction-p instr (mem (execute-instruction st))))
  :hints (("Goal"
	   :in-theory '((:definition rtm-instruction-p))
	   :use
	   (
	     (:instance any-mem-cell-is-conserved-after-execute-instruction-on-rtmstate
			(anycell  (par1 instr)))
	     (:instance any-mem-cell-is-conserved-after-execute-instruction-on-rtmstate
			(anycell  (par2 instr)))
	     (:instance any-mem-cell-is-conserved-after-execute-instruction-on-rtmstate
			(anycell  (par3 instr)))
	     (:instance any-mem-cell-is-conserved-after-execute-instruction-on-rtmstate
			(anycell  (par4 instr)))
	     (:instance execute-instruction-is-type-and-attribute-invariant-on-any-var
			(cell  (par1 instr)))
	     (:instance execute-instruction-is-type-and-attribute-invariant-on-any-var
			(cell  (par2 instr)))
	     (:instance execute-instruction-is-type-and-attribute-invariant-on-any-var
			(cell  (par3 instr)))
	     (:instance execute-instruction-is-type-and-attribute-invariant-on-any-var
			(cell  (par4 instr)))))))



(defthm a-rtm-instruction-list-is-such-after-execute-instruction
 (implies
  (and
   (rtm-statep st)
   (rtm-instruction-list-p  instrlist (mem st)))
 (rtm-instruction-list-p instrlist (mem (execute-instruction st))))
  :hints (("Goal"
	   :induct  (rtm-instruction-list-p  instrlist (mem st))
	   :in-theory (disable execute-instruction))
	  ("Subgoal *1/3" :use (:instance rtm-instruction-list-p  (instlist instrlist) (mem (mem st))))
	  ("Subgoal *1/2"
	   :in-theory (union-theories (current-theory 'ground-zero) '((:definition rtm-instruction-list-p)))
	   :use (:instance any-rtm-instruction-is-conserved-by-execution (instr (car instrlist))))))


(defthm execute-rtm-retrieves-a-memory
  (implies
   (and
    (rtm-statep st)
    (rtm-instruction-p (nth (pcc st) (code st)) (mem st)))
   (is-typed-amem-p (mem (execute-instruction st))))
  :hints (("Goal"
	   :in-theory (disable is-mem-cell-p
			       and-update or-update gen-eq-update sum-and-update sub-and-update )
	   :use (
		 (:instance gen-eq-update-returns-a-mem-cell
			    (c1 (par1 (nth (pcc st) (code st))))
			    (c2 (par2 (nth (pcc st) (code st))))
			    (c3 (par3 (nth (pcc st) (code st))))
			    (mem (mem st)))
		 (:instance or-update-returns-a-mem-cell
			    (c1 (par1 (nth (pcc st) (code st))))
			    (c2 (par2 (nth (pcc st) (code st))))
			    (c3 (par3 (nth (pcc st) (code st))))
			    (mem (mem st)))
		 (:instance and-update-returns-a-mem-cell
			    (c1 (par1 (nth (pcc st) (code st))))
			    (c2 (par2 (nth (pcc st) (code st))))
			    (c3 (par3 (nth (pcc st) (code st))))
			    (mem (mem st)))
		 (:instance sum-and-update-returns-a-mem-cell
			    (c1 (par1 (nth (pcc st) (code st))))
			    (c2 (par2 (nth (pcc st) (code st))))
			    (c3 (par3 (nth (pcc st) (code st))))
			    (prime (par4 (nth (pcc st) (code st))))
			    (mem (mem st)))
		 (:instance sub-and-update-returns-a-mem-cell
			    (c1 (par1 (nth (pcc st) (code st))))
			    (c2 (par2 (nth (pcc st) (code st))))
			    (c3 (par3 (nth (pcc st) (code st))))
			    (prime (par4 (nth (pcc st) (code st))))
			    (mem (mem st)))))))



(defthm executing-rtm-instruction-retrieves-a-rtm-state-from-rtm-state
  (implies
   (rtm-statep st)
   (rtm-statep (execute-instruction st)))
  :hints (("Goal" :cases ( (null (nth (pcc st) (code st))) (rtm-instruction-p (nth (pcc st) (code st)) (mem st))))
	  ("Subgoal 3" :use an-instruction-of-rtm-program-is-null-or-rtm-instruction)
	  ("Subgoal 1"
	  :use (
		(:instance a-rtm-instruction-list-is-such-after-execute-instruction (instrlist (code st)))
		(:instance execute-rtm-retrieves-a-memory))
  :in-theory (disable sum-and-update sub-and-update and-update or-update gen-eq-update
		      rtm-instruction-p
		      par1 par2 par3 par4 member-equal nth))))





(defthm executing-rtm-instruction-is-attributes-invariant
  (implies
   (rtm-statep st)
   (equal
    (var-attributes vars (mem st))
    (var-attributes  vars (mem (execute-instruction st)))))
 :hints (("Goal" :in-theory (disable par1 par2 par3 par4 member-equal nth))
	 ("Subgoal *1/2" :use (:instance execute-instruction-is-type-and-attribute-invariant-on-any-var
					 (cell (car vars))))))



(defthm executing-rtm-instruction-keeps-m-pointing-to-rtm-var-sets
 (implies
  (and
   (rtm-statep st)
   (m-entries-point-to-good-rtm-var-sets m (mem st)))
  (m-entries-point-to-good-rtm-var-sets m (mem (execute-instruction st))))
 :hints (("Goal" :in-theory (disable par1 par2 par3 par4 member-equal nth))
	 ("Subgoal *1/3" :use (:instance executing-rtm-instruction-is-attributes-invariant
					 (vars (rtmintvars-0 m))))))

















(defun listpars1 (st n)
  (if (zp n)
      nil
    (cons (par1 (nth (pcc st) (code st)))
	  (listpars1 (execute-instruction st) (1- n)))))

(defun listpars2 (st n)
  (if (zp n)
      nil
    (cons (par2 (nth (pcc st) (code st)))
	  (listpars2 (execute-instruction st) (1- n)))))

(defun listpars3 (st n)
  (if (zp n)
      nil
    (cons (par3 (nth (pcc st) (code st)))
	  (listpars3 (execute-instruction st) (1- n)))))

(defun listpars4 (st n)
  (if (zp n)
      nil
    (cons (par4 (nth (pcc st) (code st)))
	  (listpars4 (execute-instruction st) (1- n)))))




(defthm lemma12-lp1r
  (equal (cdr (listpars1 st n)) (listpars1 (execute-instruction st) (1- n)))
:hints (("Goal" :in-theory (disable execute-instruction))))


(defthm lemma12-lp2r
  (equal (cdr (listpars2 st n)) (listpars2 (execute-instruction st) (1- n)))
  :hints (("Goal" :in-theory (disable execute-instruction))))


(defthm lemma12-lp3r
  (equal (cdr (listpars3 st n)) (listpars3 (execute-instruction st) (1- n)))
  :hints (("Goal" :in-theory (disable execute-instruction))))


(defthm lemma12-lp4r
  (equal (cdr (listpars4 st n)) (listpars4 (execute-instruction st) (1- n)))
  :hints (("Goal" :in-theory (disable execute-instruction))))

(defthm length-of-listpars1-n-is-n
 (implies
  (and
   (integerp n)
   (>= n 0))
  (equal (len (listpars1 st n)) n))
 :hints (("Goal" :in-theory (disable execute-instruction nth par1 pcc code member-equal))))

(defthm length-of-listpars2-n-is-n
 (implies
  (and
   (integerp n)
   (>= n 0))
  (equal (len (listpars2 st n)) n))
 :hints (("Goal" :in-theory (disable execute-instruction nth par2 pcc code member-equal))))

(defthm length-of-listpars3-n-is-n
 (implies
  (and
   (integerp n)
   (>= n 0))
  (equal (len (listpars3 st n)) n))
 :hints (("Goal" :in-theory (disable execute-instruction))))

(defthm length-of-listpars4-n-is-n
 (implies
  (and
   (integerp n)
   (>= n 0))
  (equal (len (listpars4 st n)) n))
 :hints (("Goal" :in-theory (disable execute-instruction))))














(defthm only-par1-is-involved
 (implies
  (and
   (or
    (null (nth (pcc gstate) (code gstate)))
    (equal (opcode (nth (pcc gstate) (code gstate))) 'gem-equ)
    (equal (opcode (nth (pcc gstate) (code gstate))) 'gem-add)
    (equal (opcode (nth (pcc gstate) (code gstate))) 'gem-sub))
  (not (equal var (par1 (nth (pcc gstate) (code gstate))))) )
  (equal (get-cell var (mem gstate)) (get-cell var (mem (execute-instruction gstate)))))
 :hints (("Goal" :in-theory (disable sum-and-update sub-and-update gen-eq-update nth mod))))

(defthm only-par1-is-involved-rtm
 (implies
  (and
   (or
    (null (nth (pcc gstate) (code gstate)))
    (equal (opcode (nth (pcc gstate) (code gstate))) 'rtm-and)
    (equal (opcode (nth (pcc gstate) (code gstate))) 'rtm-or)
    (equal (opcode (nth (pcc gstate) (code gstate))) 'rtm-equ)
    (equal (opcode (nth (pcc gstate) (code gstate))) 'rtm-add)
    (equal (opcode (nth (pcc gstate) (code gstate))) 'rtm-sub))
  (not (equal var (par1 (nth (pcc gstate) (code gstate))))) )
  (equal (get-cell var (mem gstate)) (get-cell var (mem (execute-instruction gstate)))))
 :hints (("Goal" :in-theory (disable sum-and-update sub-and-update gen-eq-update nth mod))))




















(in-theory (enable build-values-by-rns))


(in-theory (disable mod floor))





(defun rtmintvars-i (gvar m) (cdr (assoc-equal gvar m)))

(DEFUN TYPE-I (gvar M)
  (COND ((AND (TRUE-LISTP (RTMINTVARS-I gvar M))
	      (EQUAL (LEN (RTMINTVARS-I gvar M)) 1))
	 'BOOL)
	((AND (TRUE-LISTP (RTMINTVARS-I gvar M))
	      (EQUAL (LEN (RTMINTVARS-I gvar M))
		     (LEN *RNS*)))
	 'INT)
	(T 'WRONG-TYPING)))

(defthm type-i-is-vartyper
 (implies
  (and
   (assoc-equal gvar1 m)
   (true-listp m)
   (correct-wrt-arity m mem))
  (equal (type-i gvar1 m) (var-type (get-cell gvar1 mem))))
 :hints (("Goal" :in-theory (enable
			     var-type gemvar-0 rtmintvars-0 var-type type-i type-0))))

(defthm type-i-is-type-expected
 (implies
  (and
   (assoc-equal gvar m)
   (true-listp m)
   (correct-wrt-arity m mem))
  (equal
   (type-i gvar m)
   (type-expected (rtmintvars-i gvar m)))))

(defun pos-equal-0 (el l)
  (cond
   ( (endp l)           0 )
   ( (equal el (caar l)) 0 )
   (t                   (1+ (pos-equal-0 el (cdr l))))))

(defthm assoc-means-pos-in-range
  (implies (assoc-equal el l) (in-range (pos-equal-0 el l) l))
  :rule-classes :forward-chaining)



(defun retrieve-gemvars (m)
  (if
      (endp m)
      nil
    (cons (gemvar-0 m) (retrieve-gemvars (cdr m)))))


(defthm retrieve-gemvars-same-len
 (implies
  (true-listp m)
  (equal (len (retrieve-gemvars m)) (len m))))

(defthm equal-nth-of-retrieve-car-of-nth
  (equal (nth idx (retrieve-gemvars m)) (car (nth idx m)))
 :hints (("Goal" :in-theory (enable gemvar-0))))


(defthm no-duplicates-whose-caar-is-nth-idx-means-idx-is-0
(IMPLIES (AND (NOT (ENDP L))
              (EQUAL (CAR (NTH IDX L)) (CAAR L))
              (TRUE-LISTP L)
	      (in-range idx l)
              (NO-DUPLICATES-P (RETRIEVE-GEMVARS L)))
         (EQUAL idx 0))
:hints (("Goal"
	 :in-theory (union-theories (current-theory 'ground-zero)
				    '((:definition in-range)
				      (:definition len)
				      (:rewrite equal-nth-of-retrieve-car-of-nth)))
	 :use
	 (
	   (:instance retrieve-gemvars-same-len (m l))
	   (:instance no-dup-3 (l (retrieve-gemvars l)) (idx2 0)))))
:rule-classes nil)


(defthm subgoal12
(IMPLIES (AND (NOT (ENDP L))
              (EQUAL (CAR (NTH IDX L)) (CAAR L))
              (TRUE-LISTP L)
              (< (POS-EQUAL-0 (CAR (NTH IDX L)) L)
                 (LEN L))
              (INTEGERP IDX)
              (<= 0 IDX)
              (< IDX (LEN L))
              (NO-DUPLICATES-P (RETRIEVE-GEMVARS L)))
         (EQUAL (POS-EQUAL-0 (CAR (NTH IDX L)) L)
                IDX))
:hints (("Goal"
	 :use no-duplicates-whose-caar-is-nth-idx-means-idx-is-0)))


(defthm no-duplicates-has-pos-equal-right-in-that-place
 (implies
  (and
   (true-listp l)
   (in-range idx l)
   (no-duplicates-p (retrieve-gemvars l)))
  (equal (pos-equal-0 (car (nth idx l)) l) idx))
 :hints (("Goal" :in-theory (enable gemvar-0))
	 ("Subgoal *1/2" :use subgoal12)))





(defthm rtmintvars-i-is-cdr-of-nth-entry
 (equal (rtmintvars-i gvar m)
	(cdr (nth (pos-equal-0 gvar m) m))))



(defun type-i-idx (m idx)
  (COND ((AND (TRUE-LISTP (cdr (nth idx m)))
	      (EQUAL (LEN (cdr (nth idx m))) 1))
	 'BOOL)
	((AND (TRUE-LISTP (cdr (nth idx m)))
	      (EQUAL (LEN (cdr (nth idx m)))
		     (LEN *RNS*)))
	 'INT)
	(T 'WRONG-TYPING)))

(defun listinstr (st n)
  (if (zp n)
      nil
    (cons (nth (pcc st) (code st))
	  (listinstr (execute-instruction st) (1- n)))))

(defthm inclusion-trans
  (implies
   (and
    (vars-inclusion m1 m2)
    (assoc-equal v m1))
   (assoc-equal v m2)))

(defthm correct-wrt-arity-has-rtmintvars-i-tl
 (implies
  (correct-wrt-arity m mem)
  (true-listp (rtmintvars-i gvar1 m)))
 :hints (("Goal" :in-theory (enable correct-wrt-arity type-0 gemvar-0 rtmintvars-0 correct-type))))

(defun rtm-eq-and (v1 v2 tmp res)
(list
 (list 'rtm-equ tmp v1 v2)
 (list 'rtm-and res tmp res)))

(defun rtm-eq-or (v1 v2 tmp res)
(list
 (list 'rtm-equ tmp v1 v2)
 (list 'rtm-or  res tmp tmp)))

(defun equality-trans2 (listvars1 listvars2 tmp res)
  (if (endp listvars1)
      nil
    (append
     (rtm-eq-and (car listvars1) (car listvars2) tmp res)
     (equality-trans2 (cdr listvars1) (cdr listvars2) tmp res))))

(defun equality-trans3 (listvars1 listvars2 tmp res)
    (append
     (rtm-eq-or (car listvars1) (car listvars2) tmp res)
     (equality-trans2 (cdr listvars1) (cdr listvars2) tmp res)))

(defun all-rtm-adds-for-n-steps (st n)
  (declare (xargs :measure (acl2-count n)))
  (if (zp n)
      t
    (and
     (equal (opcode (nth (pcc st) (code st))) 'rtm-add)
     (all-rtm-adds-for-n-steps (execute-instruction st) (1- n)))))

(defun all-rtm-subs-for-n-steps (st n)
  (declare (xargs :measure (acl2-count n)))
  (if (zp n)
      t
    (and
     (equal (opcode (nth (pcc st) (code st))) 'rtm-sub)
     (all-rtm-subs-for-n-steps (execute-instruction st) (1- n)))))


(defun good-translation-gem-rtm (gstate rstate m)
 (declare (xargs :measure (acl2-count (- (len (code gstate)) (pcc gstate)))))
  (if
      (or (not (integerp (pcc gstate)))
	  (< (pcc gstate) 0)
	  (>= (pcc gstate) (len (code gstate))))
      (>= (pcc rstate) (len (code rstate)))
    (case (opcode (nth (pcc gstate) (code gstate)))
      (gem-equ
       (and
	(in-range (pcc rstate) (code rstate))
	(equal (listinstr     rstate (* 2 (len *rns*)) )
	       (equality-trans3
		(eventually-make-list (rtmintvars-i (par2 (nth (pcc gstate) (code gstate))) m) (len *rns*))
		(eventually-make-list (rtmintvars-i (par3 (nth (pcc gstate) (code gstate))) m) (len *rns*))
		'tmp
		(car (rtmintvars-i (par1 (nth (pcc gstate) (code gstate))) m))))
	(not (equal
	      (par1 (nth (pcc gstate) (code gstate)))
	      (par2 (nth (pcc gstate) (code gstate)))))
	(not (equal
	      (par1 (nth (pcc gstate) (code gstate)))
	      (par3 (nth (pcc gstate) (code gstate)))))
	(good-translation-gem-rtm
	 (execute-instruction    gstate                   )
	 (execute-n-instructions rstate (* 2 (len *rns*)) )
	 m)))
      (gem-add
       (and
	(in-range (pcc rstate) (code rstate))
	(all-rtm-adds-for-n-steps rstate (len *rns*) )
	(equal (listpars1     rstate (len *rns*) )
	       (rtmintvars-i (par1 (nth (pcc gstate) (code gstate))) m))
	(equal (listpars2     rstate (len *rns*) )
	       (eventually-make-list (rtmintvars-i (par2 (nth (pcc gstate) (code gstate))) m) (len *rns*))) ;new
	(equal (listpars3     rstate (len *rns*) )
	       (eventually-make-list (rtmintvars-i (par3 (nth (pcc gstate) (code gstate))) m) (len *rns*))) ;new
	(equal (listpars4     rstate (len *rns*) ) *rns*)
	(good-translation-gem-rtm
	 (execute-instruction    gstate             )
	 (execute-n-instructions rstate (len *rns*) )
	 m)))
      (gem-sub ;;;gem-add
       (and
	(in-range (pcc rstate) (code rstate))
	(all-rtm-subs-for-n-steps rstate (len *rns*) )
	(equal (listpars1     rstate (len *rns*) )
	       (rtmintvars-i (par1 (nth (pcc gstate) (code gstate))) m))
	(equal (listpars2     rstate (len *rns*) )
	       (eventually-make-list (rtmintvars-i (par2 (nth (pcc gstate) (code gstate))) m) (len *rns*))) ;new
	(equal (listpars3     rstate (len *rns*) )
	       (eventually-make-list (rtmintvars-i (par3 (nth (pcc gstate) (code gstate))) m) (len *rns*))) ;new
	(equal (listpars4     rstate (len *rns*) ) *rns*)
	(good-translation-gem-rtm
	 (execute-instruction    gstate             )
	 (execute-n-instructions rstate (len *rns*) )
	 m)))
      (otherwise nil))))





(defun equal-get-cells (lcell mem1 mem2)
  (if (endp lcell)
      (null lcell)
    (and
     (equal (get-cell (car lcell) mem1) (get-cell (car lcell) mem2))
     (equal-get-cells (cdr lcell) mem1 mem2))))

(defthm equal-get-cells-implies-equal-parts-of-cells
 (implies
  (equal-get-cells lcell mem1 mem2)
  (and
   (equal
    (var-attributes lcell mem1)
    (var-attributes lcell mem2))
   (equal
    (var-values lcell mem1)
    (var-values lcell mem2)))))


(defthm equal-get-cells-implies-equal-values-and-attributes-still-works
 (implies
  (equal-get-cells lcell mem1 mem2)
  (iff
   (equal-values-and-attributes gemcell lcell mem1 type)
   (equal-values-and-attributes gemcell lcell mem2 type))))


(defun idx-different-cell (l mem1 mem2)
  (cond
   ( (endp l) 0)
   ( (not (equal (get-cell (car l) mem1) (get-cell (car l) mem2))) 0 )
   (t (1+ (idx-different-cell (cdr l) mem1 mem2)))))



(defthm if-bad-index-in-range-then-cells-must-be-different
 (implies
  (in-range (idx-different-cell l mem1 mem2) l)
  (not (equal
	(get-cell (nth (idx-different-cell l mem1 mem2) l) mem1)
	(get-cell (nth (idx-different-cell l mem1 mem2) l) mem2))))
 :rule-classes :forward-chaining)


(defthm if-bad-index-not-in-range-then-every-equal
 (implies (and (true-listp l)
	       (not (in-range (idx-different-cell l mem1 mem2) l)))
	  (equal-get-cells l mem1 mem2)))






(in-theory (enable gemvar-0 rtmintvars-0))

(defthm m-correspondent-values-implies-equal-values-and-attribus
 (implies
  (and
   (true-listp m)
   (m-correspondent-values-p m memgstate memrstate)
   (assoc-equal gvar1 m))
  (equal-values-and-attributes
   (get-cell gvar1 memgstate)
   (rtmintvars-i gvar1 m)
   memrstate
   (type-i gvar1 m)))
:hints (("Goal" :in-theory (disable equal-values-and-attributes))))

(in-theory (disable gemvar-0 rtmintvars-0))


(defun retrieve-rtmvars (m)
  (if (endp m)
      nil
    (cons (cdr (car m))
	  (retrieve-rtmvars (cdr m)))))


(defthm rtmintvars-i-is-pos-equal-0-of-retrieve-vars
  (equal (rtmintvars-i gvar m)
	 (nth (pos-equal-0 gvar m) (retrieve-rtmvars m))))


(defthm lemma-help2
  (implies
   (true-listp m)
   (equal (len m) (len (retrieve-rtmvars m))))
  :rule-classes nil)

(defthm lemma-help3
  (implies
   (true-listp m)
    (iff (in-range idx m) (in-range idx (retrieve-rtmvars m))))
  :hints (("Goal" :use lemma-help2))
  :rule-classes nil)

(defthm lemma-help4
  (implies
   (and
    (assoc-equal gvar1 m)
    (not (equal gvar1 gvar2)))
   (not (equal (pos-equal-0 gvar1 m) (pos-equal-0 gvar2 m)))))

(defthm lemma1-different-vars-do-not-belong
  (implies
   (and
    (true-listp m)
    (no-duplicates-p (append-lists (retrieve-rtmvars m)))
    (assoc-equal gvar1 m)
    (assoc-equal gvar2 m)
    (not (equal gvar1 gvar2))
    (in-range idx1 (rtmintvars-i gvar1 m)))
  (not (member-equal-bool (nth idx1 (rtmintvars-i gvar1 m))
		     (rtmintvars-i gvar2 m))))
  :hints (("Goal"
	   :in-theory '((:type-prescription retrieve-rtmvars)
			(:definition in-range)
			(:rewrite in-range-is-member-eq-bool))
	   :use (
		 lemma-help4
		 (:instance lemma-help3 (idx (pos-equal-0 gvar1 m)))
		 (:instance lemma-help3 (idx (pos-equal-0 gvar2 m)))
		 (:instance generalized-disjunctivity-unordered-2
			    (el1 (nth idx1 (nth (pos-equal-0 gvar1 m) (retrieve-rtmvars m))))
			    (ll (retrieve-rtmvars m))
			    (idx1 (pos-equal-0 gvar1 m))
			    (idx2 (pos-equal-0 gvar2 m)))
		 (:instance assoc-means-pos-in-range (el gvar1) (l m))
		 (:instance assoc-means-pos-in-range (el gvar2) (l m))
		 (:instance rtmintvars-i-is-pos-equal-0-of-retrieve-vars (gvar gvar1))
		 (:instance rtmintvars-i-is-pos-equal-0-of-retrieve-vars (gvar gvar2))))))


(defthm teorema-main-con-pcc-in-range-su-variabile-non-interessata
 (implies
  (and
   (gem-statep gstate)
   (rtm-statep rstate)
   (in-range (pcc gstate) (code gstate))
   (in-range (pcc rstate) (code rstate))
   (not (equal gvar1 (par1 (nth (pcc gstate) (code gstate))))))
  (equal
   (get-cell gvar1 (mem (execute-instruction gstate)))
   (get-cell gvar1 (mem gstate))))
 :hints (("Goal" :use (:instance only-par1-is-involved (var gvar1)))))


(defun bad-idx-eqv-va (m gem-mem rtm-mem)
  (cond
   ( (endp m)
     0 )
   ( (not (equal-values-and-attributes
	   (get-cell (gemvar-0 m) gem-mem)
	   (rtmintvars-0 m)
	   rtm-mem
	   (type-0 m)))
     0 )
   (t (1+ (bad-idx-eqv-va (cdr m) gem-mem rtm-mem)))))

(defthm if-bad-index-in-range-thne-must-be-different-mc
 (implies
   (in-range (bad-idx-eqv-va m gem-mem rtm-mem) m)
  (not (m-correspondent-values-p m gem-mem rtm-mem)))
 :hints (("Goal" :in-theory (enable gemvar-0))))

(defthm if-bad-index-in-range-thne-must-be-different-vs
 (implies
   (in-range (bad-idx-eqv-va m gem-mem rtm-mem) m)
  (not
   (equal-values-and-attributes
    (get-cell (car (nth (bad-idx-eqv-va m gem-mem rtm-mem) m))  gem-mem)
    (cdr (nth (bad-idx-eqv-va m gem-mem rtm-mem) m))
    rtm-mem
    (type-i-idx m (bad-idx-eqv-va m gem-mem rtm-mem)))))
 :hints (("Goal" :in-theory (e/d (type-0 gemvar-0 rtmintvars-0)
				 (var-attribute var-attributes apply-direct-rns-to-value-according-to-type
						var-values-of-1-variable-is-one-element-list-of-var-value
						var-values equal-values
						)))))


(defthm if-bad-index-not-in-range-then-m-corr
  (implies
   (and
    (true-listp m)
    (not (in-range (bad-idx-eqv-va m gem-mem rtm-mem) m)))
    (m-correspondent-values-p m gem-mem rtm-mem))
  :hints (("Goal" :in-theory (e/d (gemvar-0)
			  ((:type-prescription retrieve-rtmvars)
			   retrieve-rtmvars)))))

(defthm execute-n-instructions-keeps-rtm-state-and-points-to-good
 (implies
  (and
   (rtm-statep st)
   (m-entries-point-to-good-rtm-var-sets m (mem st)))
  (and
   (rtm-statep (execute-n-instructions st n))
   (m-entries-point-to-good-rtm-var-sets m (mem (execute-n-instructions st n)))))
 :hints (("Goal" :induct (execute-n-instructions st n) )
	 ("Subgoal *1/2"
	  :in-theory '((:definition execute-n-instructions)
		       (:rewrite executing-rtm-instruction-keeps-m-pointing-to-rtm-var-sets)
		       (:rewrite executing-rtm-instruction-retrieves-a-rtm-state-from-rtm-state)))))


;;(ld "Proof-Of-Plus.lisp" :ld-error-action :error)

(in-theory (enable
	    (:executable-counterpart build-values-by-rns)
	    (:type-prescription build-values-by-rns)
	    (:induction build-values-by-rns)
	    (:definition build-values-by-rns)
	    posp-all posp mod mod-+-exp mod-prod-makes-same-residues))

(in-theory (disable mod floor))

(defun sum-list (vl2 vl3 rns)
  (if (endp vl2)
      nil
       (cons (mod (+ (car vl2) (car vl3)) (car rns))
	     (sum-list (cdr vl2) (cdr vl3) (cdr rns)))))

(defthm sum-correspondence-by-put-list
 (implies
  (and
   (integerp gval1)
   (integerp gval2)
   (posp-all rns))
   (equal (build-values-by-rns (+ gval1 gval2) rns)
	  (sum-list
	   (build-values-by-rns gval1 rns)
	   (build-values-by-rns gval2 rns)
	   rns)))
   :hints (("Goal" :induct t)))




(defthm sum-correspondence-by-put-list-2-fin
 (implies
  (and
   (integerp gval1)
   (integerp gval2)
   (posp-all rns))
  (equal (build-values-by-rns (mod (+ gval1 gval2) (prod rns)) rns)
	 (sum-list
	  (build-values-by-rns  gval1 rns)
	  (build-values-by-rns  gval2 rns)
	 rns))))

(in-theory (disable mod-prod-makes-same-residues))



(in-theory (disable mod floor mod-+-exp mod-prod-makes-same-residues))







(defthm sum-correspondence-by-put-list-h
 (implies
  (and
   (integerp gval1)
   (integerp gval2)
   (integer>1-listp rns))
   (equal (build-values-by-rns (mod (+ gval1 gval2) (prod rns)) rns)
	  (sum-list
	   (build-values-by-rns gval1 rns)
	   (build-values-by-rns gval2 rns)
	   rns)))
   :hints (("Goal" :use (sum-correspondence-by-put-list-2-fin greater-one-means-greater-zero))))



(defthm a-boolean-has-same-rnss-than-list-of-itself
 (implies
  (and
   (integerp val)
   (or (equal val 0) (equal val 1))
   (integer>1-listp rns))
  (equal
   (build-values-by-rns val rns)
   (make-n-list val (len rns))))
 :hints (("Goal" :in-theory (enable mod-x-y-=-x-exp))))




(defthm sum-correspondence-by-put-list-on-boolean
 (implies
  (and
   (integerp gval1)
   (integerp gval2)
   (or (equal gval2 0) (equal gval2 1))
   (integer>1-listp rns))
   (equal (build-values-by-rns (mod (+ gval1 gval2) (prod rns)) rns)
	  (sum-list
	   (build-values-by-rns gval1 rns)
	   (make-n-list gval2 (len rns))
	   rns)))
 :hints (("Goal" :in-theory nil
	  :use (sum-correspondence-by-put-list-h
		(:instance a-boolean-has-same-rnss-than-list-of-itself (val gval2))))))



(defun equal-sum-and-updates (reslist par1list par2list par3list primelist mem memafterputs)
  (if (endp reslist)
      (null reslist)
    (and
     (equal
      (get-cell (car reslist) memafterputs)
      (sum-and-update
       (car par1list)
       (car par2list)
       (car par3list)
       (car primelist)
       mem))
     (equal-sum-and-updates
      (cdr reslist)
      (cdr par1list)
      (cdr par2list)
      (cdr par3list)
      (cdr primelist)
      mem
      memafterputs))))





(defthm equal-sum-and-updates-have-same-attributes
 (implies
  (and
   (true-listp rtmvars1)
   (true-listp rtmvarsres)
   (equal (len rtmvars1) (len rtmvarsres))
   (equal-sum-and-updates rtmvarsres rtmvars1 rtmvars2 rtmvars3 rns rtmmem rtmmemafter))
  (equal (var-attributes rtmvarsres rtmmemafter) (var-attributes rtmvars1 rtmmem))))

(in-theory (enable sum-list))

(defthm equal-sum-and-updates-have-values-that-are-sum-lists
  (implies
   (and
    (equal (len rtmvars1) (len rtmvarsres))
    (equal (len rtmvars2) (len rtmvarsres))
    (equal (len rtmvars3) (len rtmvarsres))
    (equal-sum-and-updates rtmvarsres rtmvars1 rtmvars2 rtmvars3 rns rtmmem rtmmemafter))
   (equal (var-values rtmvarsres rtmmemafter)
	 (sum-list
	  (var-values rtmvars2 rtmmem)
	  (var-values rtmvars3 rtmmem)
	  rns)))
 :hints ( ("Subgoal *1/2" :in-theory (enable var-value get-cell make-cell))))





(defthm behaviour-of-sum-and-update-norest
 (and
  (equal
   (var-attribute (sum-and-update-norest c1 c2 c3 mem))
   (var-attribute (get-cell c1 mem)))
  (equal
   (var-value (sum-and-update-norest c1 c2 c3 mem))
   (mod
    (+
     (var-value (get-cell c2 mem))
     (var-value (get-cell c3 mem)))
    (prod *rns*)))
  (equal
   (var-type (sum-and-update-norest c1 c2 c3 mem))
   (var-type (get-cell c1 mem))))
 :hints (("Goal" :in-theory (enable var-type var-value var-attribute make-cell))))




(defthm defexpansion
  (implies
   (not (null (var-value gcell)))
  (equal
   (equal-values-and-attributes gcell rtmvars rtmmem 'Int)
   (and
    (equal-values (var-values rtmvars rtmmem)
		  (build-values-by-rns (var-value gcell) *rns*))
    (equal-elements (var-attribute gcell)
		    (var-attributes rtmvars rtmmem)))))
  :hints (("Goal" :in-theory '((:definition equal-values-and-attributes)
			       (:definition apply-direct-rns-to-value-according-to-type))
	   :use (:instance build-values-by-rns-extended-behaves-standardly-on-non-nils
			   (gem-value (var-value gcell))
			   (rns *rns*)))))


(defthm if-gem-is-sum-and-update-inf-every-rtm-var-is-sum-and-update-then-equal-values-is-kept
 (implies
  (and
   (true-listp rtmvars1)
   (true-listp rtmvarsres)
   (equal (len rtmvars1) (len rtmvarsres))
   (equal (len rtmvars2) (len rtmvarsres))
   (equal (len rtmvars3) (len rtmvarsres))
   (not (null (var-value (get-cell gvar1 gemmem))))
   (integerp (var-value (get-cell gvar2 gemmem)))
   (integerp (var-value (get-cell gvar3 gemmem)))
   (equal-sum-and-updates rtmvarsres rtmvars1 rtmvars2 rtmvars3 *rns* rtmmem rtmmemafter)
   (equal-values-and-attributes (get-cell gvar1 gemmem) rtmvars1 rtmmem 'Int)
   (equal-values-and-attributes (get-cell gvar2 gemmem) rtmvars2 rtmmem 'Int)
   (equal-values-and-attributes (get-cell gvar3 gemmem) rtmvars3 rtmmem 'Int))
  (equal-values-and-attributes
   (sum-and-update-norest gvar1 gvar2 gvar3 gemmem)
   rtmvarsres
   rtmmemafter
   'Int))
 :hints (("Goal"
	  :in-theory (union-theories (current-theory 'ground-zero)
				     '(
				       (:definition integer>1-listp)
				       (:definition equal-values)
				       (:rewrite defexpansion)))
	  :use (
		(:instance greater-one-means-greater-zero (rns *rns*))
		(:instance equal-sum-and-updates-have-values-that-are-sum-lists (rns *rns*))
		(:instance equal-sum-and-updates-have-same-attributes           (rns *rns*))
		(:instance sum-correspondence-by-put-list-h
			   (gval1 (var-value (get-cell gvar2 gemmem)))
			   (gval2 (var-value (get-cell gvar3 gemmem)))
			   (rns *rns*))
		(:instance behaviour-of-sum-and-update-norest
			   (c1 gvar1)
			   (c2 gvar2)
			   (c3 gvar3)
			   (mem gemmem)))))
 )







(defthm if-a-var-value-is-same-then-var-values-are-list-of
 (implies
  (equal (var-value (get-cell (car rtmvars) rtmmem)) (var-value gcell))
  (equal-values (var-values (make-n-list (car rtmvars) (len rns)) rtmmem)
		(make-n-list (var-value gcell) (len rns)))))

(defthm if-a-var-attribute-is-same-then-var-attributes-are-list-of
 (implies
  (equal (var-attribute (get-cell (car rtmvars) rtmmem)) (var-attribute gcell))
  (equal-elements
   (var-attribute gcell)
   (var-attributes (make-n-list (car rtmvars) (len rns)) rtmmem))))



(defthm defexpansion-bool-values
  (implies
    (or (equal (var-value gcell) 0)
	(equal (var-value gcell) 1))
  (implies
   (equal-values-and-attributes gcell rtmvars rtmmem 'Bool)
   (equal-values (var-values (make-n-list (car rtmvars) (len *rns*)) rtmmem)
		  (build-values-by-rns (var-value gcell) *rns*))))
  :hints (("Goal" :use ( (:instance if-a-var-value-is-same-then-var-values-are-list-of
				    (rns *rns*))))))




(defthm equal-values-on-list-entails-equality-on-first-els
 (implies
  (and
   (integerp n)
   (> n 0)
  (equal-values (var-values (make-n-list el n) mem)
		(make-n-list val n)))
  (equal-values (var-values (list el) mem)
		(list val)))
 :hints (("Subgoal *1/3'" :use ( (:instance make-n-list (el el) (n 1))
                                 (:instance make-n-list (el val) (n 1)) ))))


(defthm cell-types
  (implies
   (is-mem-cell-p gcell)
   (or
    (equal (var-type gcell) 'Bool)
    (equal (var-type gcell) 'Int)))
  :hints (("Goal" :in-theory (enable my-or-2)))
  :rule-classes nil)

(defthm bool-cell
  (implies
   (and
    (is-mem-cell-p gcell)
    (equal (var-type gcell) 'Bool))
   (and
    (integerp (var-value gcell))
    (or (equal (var-value gcell) 0)
	(equal (var-value gcell) 1))))
  :rule-classes nil)

(defthm int-cell
  (implies
   (and
    (is-mem-cell-p gcell)
    (equal (var-type gcell) 'Int))
   (integerp (var-value gcell)))
  :rule-classes nil)


(defthm defexpansion-bool-values-inv
  (implies
   (and
    (is-mem-cell-p gcell)
    (equal (var-type gcell) 'Bool)
    (equal (type-expected rtmvars) (var-type gcell)))
  (implies
   (equal-values (var-values (eventually-make-list rtmvars (len *rns*)) rtmmem)
		 (build-values-by-rns (var-value gcell) *rns*))
   (equal-values
    (var-values rtmvars rtmmem)
    (apply-direct-rns-to-value-according-to-type gcell (var-type gcell)))))
  :hints (("Goal" :use (bool-cell
			(:instance equal-values-on-list-entails-equality-on-first-els
				   (mem rtmmem)
				   (n (len *rns*))
				   (el (car rtmvars))
				   (val (var-value gcell)))
			(:instance a-boolean-has-same-rnss-than-list-of-itself
				   (val (var-value gcell)) (rns *rns*))))))




(defthm defexpansion-bool-attrs-1
  (implies
   (equal-values-and-attributes gcell rtmvars rtmmem 'Bool)
   (equal (var-attribute (get-cell (car rtmvars) rtmmem)) (var-attribute gcell))))


(defthm defexpansion-bool-attrs
  (implies
   (equal-values-and-attributes gcell rtmvars rtmmem 'Bool)
   (equal-elements
    (var-attribute gcell)
    (var-attributes (make-n-list (car rtmvars) (len *rns*)) rtmmem)))
  :hints (("Goal" :use ( defexpansion-bool-attrs-1
			 (:instance if-a-var-attribute-is-same-then-var-attributes-are-list-of
				    (rns *rns*))))))


(defthm defexpansion-bool-attrs-inv-1
  (implies
   (equal (type-expected rtmvars) 'Bool)
   (equal
    (var-attributes rtmvars rtmmem)
    (list (var-attribute (get-cell (car rtmvars) rtmmem)))))
  :hints (("Subgoal 1'" :use (:theorem (implies
				  (and (true-listp rtmvars2)
				       (equal (+ 1 (len rtmvars2)) 1))
				  (endp rtmvars2)))))
  :otf-flg t)

(defthm defexpansion-bool-attrs-inv-2
  (implies
   (and
    (equal (type-expected rtmvars) 'Bool)
    (equal val (var-attribute (get-cell (car rtmvars) rtmmem))))
   (equal-elements val (var-attributes rtmvars rtmmem))))


(defthm defexpansion-bool-attrs-inv-3
  (implies
   (and
    (integerp n)
    (> n 0))
  (implies
   (equal-elements
    val
    (var-attributes (make-n-list car-rtmvars n) rtmmem))
   (equal
    val
    (var-attribute (get-cell car-rtmvars rtmmem)))))
  :hints (("Subgoal *1/3'" :use (:instance make-n-list (el car-rtmvars) (n 1))))
  :rule-classes nil)


(defthm defexpansion-bool-attrs-inv
  (implies
   (and
    (equal (var-type gcell) 'Bool)
    (equal (type-expected rtmvars) (var-type gcell)))
  (implies
   (equal-elements
    (var-attribute gcell)
    (var-attributes (make-n-list (car rtmvars) (len *rns*)) rtmmem))
   (equal-elements
    (var-attribute gcell)
    (var-attributes rtmvars rtmmem))))
  :hints (("Goal" :use
	   ( defexpansion-bool-attrs-inv-1
	     defexpansion-bool-attrs-inv-2
	     (:instance defexpansion-bool-attrs-inv-3
			(n (len *rns*))
			(car-rtmvars (car rtmvars))
			(val (var-attribute gcell)))))))

(defthm defexpansion-bool
  (implies
   (and
    (is-mem-cell-p gcell)
    (equal (var-type gcell) 'Bool)
    (equal (type-expected rtmvars) (var-type gcell)))
  (equal
   (equal-values-and-attributes gcell rtmvars rtmmem 'Bool)
   (and
    (equal-values (var-values (make-n-list (car rtmvars) (len *rns*)) rtmmem)
		  (build-values-by-rns (var-value gcell) *rns*))
    (equal-elements
     (var-attribute gcell)
     (var-attributes (make-n-list (car rtmvars) (len *rns*)) rtmmem)))))
  :hints (("Goal" :use
	   ( bool-cell
	     defexpansion-bool-attrs
	     defexpansion-bool-values
	     defexpansion-bool-attrs-inv
	     defexpansion-bool-values-inv))))





(defthm defexpansion-generic-bool
  (implies
   (and
    (is-mem-cell-p gcell)
    (equal (var-type gcell) 'Bool)
    (equal (type-expected rtmvars) (var-type gcell)))
  (equal
   (equal-values-and-attributes gcell rtmvars rtmmem (var-type gcell))
   (and
    (equal-values (var-values (eventually-make-list rtmvars (len *rns*)) rtmmem)
		  (build-values-by-rns (var-value gcell) *rns*))
    (equal-elements (var-attribute gcell)
		    (var-attributes (eventually-make-list rtmvars (len *rns*)) rtmmem)))))
  :hints (("Goal" :in-theory (union-theories (current-theory 'ground-zero)
					     '((:definition type-expected)
					       (:definition eventually-make-list)))
					     :use (defexpansion-bool bool-cell))))

(defthm defexpansion-generic-int
  (implies
   (and
    (is-mem-cell-p gcell)
    (equal (var-type gcell) 'Int)
    (equal (type-expected rtmvars) (var-type gcell)))
  (equal
   (equal-values-and-attributes gcell rtmvars rtmmem (var-type gcell))
   (and
    (equal-values (var-values (eventually-make-list rtmvars (len *rns*)) rtmmem)
		  (build-values-by-rns (var-value gcell) *rns*))
    (equal-elements (var-attribute gcell)
		    (var-attributes (eventually-make-list rtmvars (len *rns*)) rtmmem)))))
  :hints (("Goal" :in-theory (union-theories (current-theory 'ground-zero)
					     '((:definition type-expected)
					       (:definition eventually-make-list)))
					     :use (defexpansion int-cell))))




(defthm defexpansion-generic
  (implies
   (and
    (is-mem-cell-p gcell)
    (equal (type-expected rtmvars) (var-type gcell)))
  (equal
    (equal-values-and-attributes gcell rtmvars rtmmem (var-type gcell))
   (and
    (equal-values (var-values (eventually-make-list rtmvars (len *rns*)) rtmmem)
		  (build-values-by-rns (var-value gcell) *rns*))
    (equal-elements (var-attribute gcell)
		    (var-attributes (eventually-make-list rtmvars (len *rns*)) rtmmem)))))
  :hints (("Goal"
	  :cases ( (equal (var-type gcell) 'Bool)
		   (equal (var-type gcell) 'Int) ))
	  ("Subgoal 3" :use cell-types)
	  ("Subgoal 2" :use defexpansion-generic-bool)
	  ("Subgoal 1" :use defexpansion-generic-int)))






(defthm if-gem-is-sum-and-update-inf-every-rtm-var-is-sum-and-update-then-equal-values-is-kept-g
 (implies
  (and
   (true-listp rtmvars1)
   (true-listp rtmvarsres)
   (equal (len rtmvars1)                                     (len rtmvarsres))
   (equal (len (eventually-make-list rtmvars2 (len *rns*)))  (len rtmvarsres))
   (equal (len (eventually-make-list rtmvars3 (len *rns*)))  (len rtmvarsres))
   (equal (var-type (get-cell gvar2 gemmem)) (type-expected rtmvars2))
   (equal (var-type (get-cell gvar3 gemmem)) (type-expected rtmvars3))
   (is-mem-cell-p (get-cell gvar1 gemmem))
   (equal (var-type (get-cell gvar1 gemmem)) 'Int)
   (is-mem-cell-p (get-cell gvar2 gemmem))
   (is-mem-cell-p (get-cell gvar3 gemmem))
   (equal-sum-and-updates
    rtmvarsres
    rtmvars1
    (eventually-make-list rtmvars2 (len *rns*))
    (eventually-make-list rtmvars3 (len *rns*))
    *rns* rtmmem rtmmemafter)
   (equal-values-and-attributes (get-cell gvar1 gemmem) rtmvars1 rtmmem 'Int)
   (equal-values-and-attributes (get-cell gvar2 gemmem) rtmvars2 rtmmem (var-type (get-cell gvar2 gemmem)))
   (equal-values-and-attributes (get-cell gvar3 gemmem) rtmvars3 rtmmem (var-type (get-cell gvar3 gemmem))))
  (equal-values-and-attributes
   (sum-and-update-norest gvar1 gvar2 gvar3 gemmem)
   rtmvarsres
   rtmmemafter
   'Int))
 :hints (("Goal"
	  :in-theory (union-theories (current-theory 'ground-zero)
				     '((:definition integer>1-listp)
				       (:definition equal-values)
				       (:definition is-mem-cell-p)
				       (:rewrite defexpansion)))
	  :use (
		(:instance defexpansion-generic
			   (gcell (get-cell gvar2 gemmem))
			   (rtmvars rtmvars2))
		(:instance defexpansion-generic
			   (gcell (get-cell gvar3 gemmem))
			   (rtmvars rtmvars3))
		(:instance equal-sum-and-updates-have-values-that-are-sum-lists
			   (rtmvars2 (eventually-make-list rtmvars2 (len *rns*)))
			   (rtmvars3 (eventually-make-list rtmvars3 (len *rns*)))
			   (rns *rns*))
		(:instance equal-sum-and-updates-have-same-attributes
			   (rtmvars2 (eventually-make-list rtmvars2 (len *rns*)))
			   (rtmvars3 (eventually-make-list rtmvars3 (len *rns*)))
			   (rns *rns*))
		(:instance sum-correspondence-by-put-list-h
			   (gval1 (var-value (get-cell gvar2 gemmem)))
			   (gval2 (var-value (get-cell gvar3 gemmem)))
			   (rns *rns*))
		(:instance behaviour-of-sum-and-update-norest
			   (c1 gvar1)
			   (c2 gvar2)
			   (c3 gvar3)
			   (mem gemmem))))))





(in-theory (disable sum-list sum-correspondence-by-put-list
		    equal-sum-and-updates-have-same-attributes
		    equal-sum-and-updates-have-values-that-are-sum-lists
		    behaviour-of-sum-and-update-norest
		    defexpansion
		    if-a-var-value-is-same-then-var-values-are-list-of
		    if-a-var-attribute-is-same-then-var-attributes-are-list-of
		    defexpansion-generic-bool
		    defexpansion-generic-int
		    defexpansion-generic
		    defexpansion-bool-values-inv
		    defexpansion-bool-values
		    defexpansion-bool-attrs-inv
		    defexpansion-bool-attrs-inv-1
		    defexpansion-bool-attrs-inv-2
		    defexpansion-bool-attrs
		    defexpansion-bool-attrs-1
		    equal-values-on-list-entails-equality-on-first-els
		    ))





(defun execute-n-rtm-adds (st n)
  (if
      (zp n)
      st
    (execute-n-rtm-adds
     (rtm-add
      (par1 (nth (pcc st) (code st)))
      (par2 (nth (pcc st) (code st)))
      (par3 (nth (pcc st) (code st)))
      (par4 (nth (pcc st) (code st)))
     st)
     (1- n))))


(defthm all-rtm-adds-means-only-adds-are-executed
 (implies
  (all-rtm-adds-for-n-steps st n)
  (equal
   (execute-n-rtm-adds st n)
   (execute-n-instructions st n)))
 :hints (("Goal" :in-theory (disable rtm-add member-equal nth par1 par2 par3))))


(defun adds-list-n (l1 l2 l3 l4 mem n)
  (if (zp n)
      mem
    (adds-list-n (cdr l1) (cdr l2) (cdr l3) (cdr l4)
	       (put-cell
		(car l1)
		(sum-and-update
		 (car l1)
		 (car l2)
		 (car l3)
		 (car l4)
		 mem)
		mem)
	       (1- n))))







(in-theory (disable member-equal))


(in-theory (enable make-cell))



(defthm execute-n-rtm-adds-tantamount-to-add-list-n
 (implies
  (and
   (all-rtm-adds-for-n-steps st n)
   (>= (pcc st) 0)
   (rtm-statep st))
  (equal
   (mem (execute-n-rtm-adds st n))
   (adds-list-n
    (listpars1 st n)
    (listpars2 st n)
    (listpars3 st n)
    (listpars4 st n)
    (mem st)
    n)))
 :hints
	 (("Goal" :induct t )
	  ("Subgoal *1/2.2" :in-theory '((:definition all-rtm-adds-for-n-steps)
					 (:definition execute-instruction)
					 (:definition rtm-add)
					 (:definition make-state)
					 (:definition mem))
	   )
	  ("Subgoal *1/2"
		   :use ( execute-n-rtm-adds
			  (:instance adds-list-n
				     (l1 (listpars1 st n))
				     (l2 (listpars2 st n))
				     (l3 (listpars3 st n))
				     (l4 (listpars4 st n))
				     (mem (mem st)))
			  lemma12-lp1r lemma12-lp2r lemma12-lp3r lemma12-lp4r
			  (:theorem
			   (IMPLIES (AND (ALL-RTM-ADDS-FOR-N-STEPS ST N)
					 (>= (pcc st) 0)
					 (not (zp n)))
				    (equal (mem (execute-instruction st))
					   (PUT-CELL (CAR (LISTPARS1 ST N))
						     (SUM-AND-UPDATE (CAR (LISTPARS1 ST N))
								     (CAR (LISTPARS2 ST N))
								     (CAR (LISTPARS3 ST N))
								     (CAR (LISTPARS4 ST N))
								     (MEM ST))
						     (MEM ST)))))
			  executing-rtm-instruction-retrieves-a-rtm-state-from-rtm-state
			  instruction-incrementing-pvv))))


(in-theory (disable lemma12-lp1r  lemma12-lp2r lemma12-lp3r lemma12-lp4r ))










(defun adds-list-e (c1 c2 c3 c4 mem)
  (if
      (endp c1)
      mem
    (adds-list-e
     (cdr c1)
     (cdr c2)
     (cdr c3)
     (cdr c4)
     (put-cell (car c1) (sum-and-update (car c1) (car c2) (car c3) (car c4) mem) mem))))



(defthm adds-list-e-is-adds-list-n
  (equal (adds-list-e c1 c2 c3 c4 mem) (adds-list-n c1 c2 c3 c4 mem (len c1)))
  :rule-classes nil)



(defthm execute-n-instructions-tantamount-to-add-list-e
 (implies
  (and
   (integerp n)
   (>= n 0)
   (all-rtm-adds-for-n-steps st n)
   (>= (pcc st) 0)
   (rtm-statep st))
  (equal
   (mem (execute-n-instructions st n))
   (adds-list-e
    (listpars1 st n)
    (listpars2 st n)
    (listpars3 st n)
    (listpars4 st n)
    (mem st))))
 :hints (("Goal" :in-theory nil
	  :use ((:instance adds-list-e-is-adds-list-n
			   (c1 (listpars1 st n))
			   (c2 (listpars2 st n))
			   (c3 (listpars3 st n))
			   (c4 (listpars4 st n))
			   (mem (mem st)))
		execute-n-rtm-adds-tantamount-to-add-list-n
		all-rtm-adds-means-only-adds-are-executed
		length-of-listpars1-n-is-n))))










(defthm not-in-list-untouched-by-adds-list-e
  (implies
   (not (member-equal-bool v l1))
   (equal (get-cell v (adds-list-e l1 l2 l3 l4 mem)) (get-cell v mem)))
  :hints (("Goal" :in-theory (disable sum-and-update))))

(defthm not-in-list-untouched-by-adds-list-e-1
  (implies
   (not (member-equal-bool (car l1) (cdr l1)))
   (equal (get-cell (car l1) (adds-list-e (cdr l1) (cdr l2) (cdr l3) (cdr l4) mem))
	  (get-cell (car l1) mem))))


(defthm sum-and-update-independent-from-firstbn
 (implies
  (and
   (not (member-equal-bool (nth idx l1) (firstn idx l1)))
   (not (member-equal-bool (nth idx l2) (firstn idx l1)))
   (not (member-equal-bool (nth idx l3) (firstn idx l1))))
  (equal (sum-and-update
	  (nth idx l1)
	  (nth idx l2)
	  (nth idx l3)
	  (nth idx l4)
	  (adds-list-e (firstn idx l1) (firstn idx l2) (firstn idx l3) (firstn idx l4) mem))
	 (sum-and-update
	  (nth idx l1)
	  (nth idx l2)
	  (nth idx l3)
	  (nth idx l4)
	  mem))))



(defthm adds-list-decomp
 (implies
  (and
   (in-range idx l1)
   (in-range idx l2)
   (in-range idx l3)
   (in-range idx l4))
  (equal
   (adds-list-e l1 l2 l3 l4 mem)
   (adds-list-e (nthcdr idx l1) (nthcdr idx l2) (nthcdr idx l3) (nthcdr idx l4)
		(adds-list-e (firstn idx l1) (firstn idx l2) (firstn idx l3) (firstn idx l4) mem))))
 :hints (("Goal" :in-theory (disable sum-and-update))))


(defthm if-el-does-not-appear-after-its-position-then-adds-list-e-produces-its-sum
 (implies
  (and
   (not (member-equal-bool (nth idx l1) (cdr (nthcdr idx l1))))
   (in-range idx l1)
   (in-range idx l2)
   (in-range idx l3)
   (in-range idx l4))
  (equal
   (get-cell (nth idx l1) (adds-list-e l1 l2 l3 l4 mem))
   (sum-and-update
     (nth idx l1)
     (nth idx l2)
     (nth idx l3)
     (nth idx l4)
     (adds-list-e (firstn idx l1) (firstn idx l2) (firstn idx l3) (firstn idx l4) mem))))
  :hints (("Goal" :in-theory (disable sum-and-update))))




(defthm rtm-variable-of-adds-list-e-is-sum-of-correspondent-variables
  (implies
   (and
    (positive-list rns)
    (true-listp ll)
    (no-duplicates-p (append-lists ll))
    (in-range gem1 ll)
    (in-range gem2 ll)
    (in-range gem3 ll)
    (in-range idx (nth gem1 ll))
    (in-range idx (nth gem2 ll))
    (in-range idx (nth gem3 ll))
    (in-range idx rns))
   (equal
    (get-cell (nth idx (nth gem1 ll)) (adds-list-e (nth gem1 ll) (nth gem2 ll) (nth gem3 ll) rns mem))
    (sum-and-update (nth idx (nth gem1 ll)) (nth idx (nth gem2 ll)) (nth idx (nth gem3 ll)) (nth idx rns) mem)))
  :hints (("Goal" :in-theory (disable sum-and-update)
	   :use (
		 (:instance no-duplicates-all-implies-no-duplicates-one (idx1 gem1))
		 (:instance no-duplicates-means-an-element-does-not-appear-after-its-position (l (nth gem1 ll)))
		 if-el-does-not-appear-after-its-position-then-adds-list-e-produces-its-sum
		 (:instance adds-list-decomp
			    (l1 (nth gem1 ll)) (l2 (nth gem2 ll)) (l3 (nth gem3 ll)))
		 (:instance sum-and-update-independent-from-firstbn
			    (l1 (nth gem1 ll)) (l2 (nth gem2 ll)) (l3 (nth gem3 ll)))))))



(defun index-different-sum-and-updates (rtmvarsres rtmvars1 rtmvars2 rtmvars3 rns mem mem-after-add)
  (cond
   ( (endp rtmvarsres)
     0 )
   ( (not (equal (get-cell (car rtmvarsres) mem-after-add)
		 (sum-and-update (car rtmvars1) (car rtmvars2) (car rtmvars3) (car rns) mem)))
     0 )
   ( t
     (1+ (index-different-sum-and-updates
	  (cdr rtmvarsres)
	  (cdr rtmvars1)
	  (cdr rtmvars2)
	  (cdr rtmvars3)
	  (cdr rns)
	  mem
	  mem-after-add)))))

(defthm if-bad-index-in-range-thne-must-be-nonsumandupdate
  (let ((bad-idx (index-different-sum-and-updates rtmvarsres rtmvars1 rtmvars2 rtmvars3 rns mem mem-after-add)))
    (implies
     (in-range bad-idx rtmvarsres)
     (not (equal
	   (get-cell (nth bad-idx rtmvarsres) mem-after-add)
           (sum-and-update
	    (nth bad-idx rtmvars1)
	    (nth bad-idx rtmvars2)
	    (nth bad-idx rtmvars3)
	    (nth bad-idx rns)
	    mem)))))
 :hints (("Goal" :in-theory (disable get-cell sum-and-update))))


(defthm if-bad-index-not-in-range-then-every-equalsumandupdate
  (let ((bad-idx (index-different-sum-and-updates rtmvarsres rtmvars1 rtmvars2 rtmvars3 rns mem mem-after-add)))
    (implies (and (true-listp rtmvarsres)
		  (not (in-range bad-idx rtmvarsres)))
	  (equal-sum-and-updates rtmvarsres rtmvars1 rtmvars2 rtmvars3 rns mem mem-after-add))))


(defthm rtm-variable-of-adds-list-e-is-sum-and-updates
  (implies
   (and
    (positive-list rns)
    (true-listp ll)
    (no-duplicates-p (append-lists ll))
    (equal (len (nth gem1 ll)) (len (nth gem2 ll)))
    (equal (len (nth gem1 ll)) (len (nth gem3 ll)))
    (equal (len (nth gem1 ll)) (len rns))
    (in-range gem1 ll)
    (in-range gem2 ll)
    (in-range gem3 ll)
    (true-listp (nth gem1 ll)))
   (equal-sum-and-updates (nth gem1 ll) (nth gem1 ll) (nth gem2 ll) (nth gem3 ll) rns mem
    (adds-list-e (nth gem1 ll) (nth gem2 ll) (nth gem3 ll) rns mem)))
  :hints (("Goal" :use (:instance rtm-variable-of-adds-list-e-is-sum-of-correspondent-variables
				  (idx (index-different-sum-and-updates
					(nth gem1 ll)
					(nth gem1 ll)
					(nth gem2 ll)
					(nth gem3 ll)
					rns
					mem
					(adds-list-e (nth gem1 ll) (nth gem2 ll) (nth gem3 ll) rns mem)))))
	  ("Goal'" :cases ( (in-range (index-different-sum-and-updates
				      (nth gem1 ll)
				      (nth gem1 ll)
				      (nth gem2 ll)
				      (nth gem3 ll)
				      rns
				      mem
				      (adds-list-e (nth gem1 ll) (nth gem2 ll) (nth gem3 ll) rns mem))
				     (nth gem1 ll)) ) )
	  ("Subgoal 1" :in-theory '((:definition in-range)
				    (:rewrite if-bad-index-in-range-thne-must-be-nonsumandupdate)))
	  ("Subgoal 2" :in-theory '((:rewrite if-bad-index-not-in-range-then-every-equalsumandupdate)))))




(defthm any-element-of-make-list-does-not-appear-into-other-lists
 (implies
  (and
   (integerp n)
   (true-listp ll)
   (no-duplicates-p (append-lists ll))
   (in-range gem1 ll)
   (in-range gem2 ll)
   (not (equal gem1 gem2))
   (equal (len (nth gem1 ll)) 1)
   (in-range idx (make-n-list (car (nth gem1 ll)) n)))
  (not (member-equal-bool
	(nth idx (make-n-list (car (nth gem1 ll)) n))
	(nth gem2 ll))))
 :hints (("Goal" :use
	  (
	   (:instance
	    el-of-makelist-is-el
	    (el (car (nth gem1 ll))))
	   (:instance generalized-disjunctivity-unordered-2
		      (idx1 gem1) (idx2 gem2) (el1 (car (nth gem1 ll)))))))
 :otf-flg t)

(defthm firstns-do-not-cotain-el-of-make-n-list-if-diff
 (implies
  (and
   (integerp n)
   (true-listp ll)
   (no-duplicates-p (append-lists ll))
   (in-range gem1 ll)
   (in-range gem2 ll)
   (not (equal gem1 gem2))
   (equal (len (nth gem1 ll)) 1)
   (in-range idx (make-n-list (car (nth gem1 ll)) n)))
  (not (member-equal-bool
	(nth idx (make-n-list (car (nth gem1 ll)) n))
	(firstn idx (nth gem2 ll)))))
 :hints (("Goal" :use
	  (
	   (:instance no-member-holds-on-firstn
		      (el (nth idx (make-n-list (car (nth gem1 ll)) n)))
		      (l (nth gem2 ll)))
	   any-element-of-make-list-does-not-appear-into-other-lists))))



(defthm rtm-variable-of-adds-list-e-is-sum-of-correspondent-variables-when-var-3-is-boolean
  (implies
   (and
    (integerp n)
    (positive-list rns)
    (true-listp ll)
    (no-duplicates-p (append-lists ll))
    (in-range gem1 ll)
    (in-range gem2 ll)
    (in-range gem3 ll)
    (not (equal gem1 gem3))
    (equal (len (nth gem3 ll)) 1)
    (in-range idx (nth gem1 ll))
    (in-range idx (nth gem2 ll))
    (in-range idx (make-n-list (car (nth gem3 ll)) n))
    (in-range idx rns))
   (equal
    (get-cell (nth idx (nth gem1 ll))
	      (adds-list-e
	       (nth gem1 ll)
	       (nth gem2 ll)
	       (make-n-list (car (nth gem3 ll)) n)
	       rns mem))
    (sum-and-update
     (nth idx (nth gem1 ll))
     (nth idx (nth gem2 ll))
     (nth idx (make-n-list (car (nth gem3 ll)) n))
     (nth idx rns) mem)))
  :hints (("Goal" :in-theory (disable sum-and-update)
	   :use (
		 (:instance firstns-do-not-cotain-el-of-make-n-list-if-diff (gem1 gem3) (gem2 gem1))
		 (:instance no-duplicates-all-implies-no-duplicates-one (idx1 gem1))
		 (:instance no-duplicates-means-an-element-does-not-appear-after-its-position (l (nth gem1 ll)))
		 (:instance adds-list-decomp
			    (l1 (nth gem1 ll))
			    (l2 (nth gem2 ll))
			    (l3 (make-n-list (car (nth gem3 ll)) n))
			    (l4 rns))
		 (:instance sum-and-update-independent-from-firstbn
			    (l1 (nth gem1 ll))
			    (l2 (nth gem2 ll))
			    (l3 (make-n-list (car (nth gem3 ll)) n))
			    (l4 rns))))))

(defthm rtm-variable-of-adds-list-e-is-sum-of-correspondent-variables-when-var-2-is-boolean
  (implies
   (and
    (integerp n)
    (positive-list rns)
    (true-listp ll)
    (no-duplicates-p (append-lists ll))
    (in-range gem1 ll)
    (in-range gem2 ll)
    (in-range gem3 ll)
    (not (equal gem1 gem2))
    (equal (len (nth gem2 ll)) 1)
    (in-range idx (nth gem1 ll))
    (in-range idx (nth gem3 ll))
    (in-range idx (make-n-list (car (nth gem2 ll)) n))
    (in-range idx rns))
   (equal
    (get-cell (nth idx (nth gem1 ll))
	      (adds-list-e
	       (nth gem1 ll)
	       (make-n-list (car (nth gem2 ll)) n)
	       (nth gem3 ll)
	       rns mem))
    (sum-and-update
     (nth idx (nth gem1 ll))
     (nth idx (make-n-list (car (nth gem2 ll)) n))
     (nth idx (nth gem3 ll))
     (nth idx rns) mem)))
  :hints (("Goal" :in-theory (disable sum-and-update)
	   :use (
		 (:instance firstns-do-not-cotain-el-of-make-n-list-if-diff (gem1 gem2) (gem2 gem1))
		 (:instance no-duplicates-all-implies-no-duplicates-one (idx1 gem1))
		 (:instance no-duplicates-means-an-element-does-not-appear-after-its-position (l (nth gem1 ll)))
		 (:instance adds-list-decomp
			    (l1 (nth gem1 ll))
			    (l2 (make-n-list (car (nth gem2 ll)) n))
			    (l3 (nth gem3 ll))
			    (l4 rns))
		 (:instance sum-and-update-independent-from-firstbn
			    (l1 (nth gem1 ll))
			    (l2 (make-n-list (car (nth gem2 ll)) n))
			    (l3 (nth gem3 ll))
			    (l4 rns))))))

(defthm rtm-variable-of-adds-list-e-is-sum-of-correspondent-variables-when-var-2and3-are-boolean
  (implies
   (and
    (integerp n)
    (positive-list rns)
    (true-listp ll)
    (no-duplicates-p (append-lists ll))
    (in-range gem1 ll)
    (in-range gem2 ll)
    (in-range gem3 ll)
    (not (equal gem1 gem2))
    (not (equal gem1 gem3))
    (equal (len (nth gem2 ll)) 1)
    (equal (len (nth gem3 ll)) 1)
    (in-range idx (nth gem1 ll))
    (in-range idx (make-n-list (car (nth gem2 ll)) n))
    (in-range idx (make-n-list (car (nth gem3 ll)) n))
    (in-range idx rns))
   (equal
    (get-cell (nth idx (nth gem1 ll))
	      (adds-list-e
	       (nth gem1 ll)
	       (make-n-list (car (nth gem2 ll)) n)
	       (make-n-list (car (nth gem3 ll)) n)
	       rns mem))
    (sum-and-update
     (nth idx (nth gem1 ll))
     (nth idx (make-n-list (car (nth gem2 ll)) n))
     (nth idx (make-n-list (car (nth gem3 ll)) n))
     (nth idx rns) mem)))
  :hints (("Goal" :in-theory (disable sum-and-update)
	   :use (
		 (:instance firstns-do-not-cotain-el-of-make-n-list-if-diff (gem1 gem2) (gem2 gem1))
		 (:instance firstns-do-not-cotain-el-of-make-n-list-if-diff (gem1 gem3) (gem2 gem1))
		 (:instance no-duplicates-all-implies-no-duplicates-one (idx1 gem1))
		 (:instance no-duplicates-means-an-element-does-not-appear-after-its-position (l (nth gem1 ll)))
		 (:instance adds-list-decomp
			    (l1 (nth gem1 ll))
			    (l2 (make-n-list (car (nth gem2 ll)) n))
			    (l3 (make-n-list (car (nth gem3 ll)) n))
			    (l4 rns))
		 (:instance sum-and-update-independent-from-firstbn
			    (l1 (nth gem1 ll))
			    (l2 (make-n-list (car (nth gem2 ll)) n))
			    (l3 (make-n-list (car (nth gem3 ll)) n))
			    (l4 rns))))))




(defthm rtm-variable-of-adds-list-e-is-sum-of-correspondent-variables-with-all-vars-types
  (implies
   (and
    (integerp n)
    (positive-list rns)
    (true-listp ll)
    (no-duplicates-p (append-lists ll))
    (in-range gem1 ll)
    (in-range gem2 ll)
    (in-range gem3 ll)
    (not (equal (len (nth gem1 ll)) 1))
    (in-range idx (nth gem1 ll))
    (in-range idx (eventually-make-list (nth gem2 ll) n))
    (in-range idx (eventually-make-list (nth gem3 ll) n))
    (in-range idx rns))
   (equal
    (get-cell (nth idx (nth gem1 ll))
	      (adds-list-e
	       (nth gem1 ll)
	       (eventually-make-list (nth gem2 ll) n)
	       (eventually-make-list (nth gem3 ll) n)
	       rns mem))
    (sum-and-update
     (nth idx (nth gem1 ll))
     (nth idx (eventually-make-list (nth gem2 ll) n))
     (nth idx (eventually-make-list (nth gem3 ll) n))
     (nth idx rns) mem)))
  :hints (("Goal" :in-theory (union-theories (current-theory 'ground-zero)
						  '((:definition eventually-make-list)))
	  :cases
	   ( (and (not (equal (len (nth gem3 ll)) 1))      (equal (len (nth gem2 ll)) 1))
	     (and      (equal (len (nth gem3 ll)) 1)  (not (equal (len (nth gem2 ll)) 1)))
	     (and (not (equal (len (nth gem3 ll)) 1)) (not (equal (len (nth gem2 ll)) 1)))
	     (and      (equal (len (nth gem3 ll)) 1)       (equal (len (nth gem2 ll)) 1))))
	  ("Subgoal 4"
	   :use rtm-variable-of-adds-list-e-is-sum-of-correspondent-variables-when-var-2-is-boolean)
	  ("Subgoal 3"
	   :use rtm-variable-of-adds-list-e-is-sum-of-correspondent-variables-when-var-3-is-boolean)
	  ("Subgoal 2"
	   :use rtm-variable-of-adds-list-e-is-sum-of-correspondent-variables)
	  ("Subgoal 1"
	   :use rtm-variable-of-adds-list-e-is-sum-of-correspondent-variables-when-var-2and3-are-boolean)))



(defthm sum-and-updates-holding-for-every-variable-type
  (implies
   (and
    (integerp n)
    (not (equal (len (nth gem1 ll)) 1))
    (positive-list rns)
    (true-listp ll)
    (no-duplicates-p (append-lists ll))
    (equal (len (nth gem1 ll)) (len (eventually-make-list (nth gem2 ll) n)))
    (equal (len (nth gem1 ll)) (len (eventually-make-list (nth gem3 ll) n)))
    (equal (len (nth gem1 ll)) (len rns))
    (in-range gem1 ll)
    (in-range gem2 ll)
    (in-range gem3 ll)
    (true-listp (nth gem1 ll)))
   (equal-sum-and-updates
    (nth gem1 ll)
    (nth gem1 ll)
    (eventually-make-list (nth gem2 ll) n)
    (eventually-make-list (nth gem3 ll) n)
    rns mem
    (adds-list-e
     (nth gem1 ll)
     (eventually-make-list (nth gem2 ll) n)
     (eventually-make-list (nth gem3 ll) n)
     rns mem)))
  :hints (("Goal" :use (:instance rtm-variable-of-adds-list-e-is-sum-of-correspondent-variables-with-all-vars-types
				  (idx (index-different-sum-and-updates
					(nth gem1 ll)
					(nth gem1 ll)
					(eventually-make-list (nth gem2 ll) n)
					(eventually-make-list (nth gem3 ll) n)
					rns
					mem
					(adds-list-e
					 (nth gem1 ll)
					 (eventually-make-list (nth gem2 ll) n)
					 (eventually-make-list (nth gem3 ll) n)
					 rns mem)))))
	  ("Goal'" :cases ( (in-range (index-different-sum-and-updates
				      (nth gem1 ll)
				      (nth gem1 ll)
				      (eventually-make-list (nth gem2 ll) n)
				      (eventually-make-list (nth gem3 ll) n)
				      rns
				      mem
				      (adds-list-e
				       (nth gem1 ll)
				       (eventually-make-list (nth gem2 ll) n)
				       (eventually-make-list (nth gem3 ll) n)
				       rns mem))
				     (nth gem1 ll)) ) )
	  ("Subgoal 1" :in-theory '((:definition in-range)
		       		    (:rewrite if-bad-index-in-range-thne-must-be-nonsumandupdate)))
	  ("Subgoal 2" :in-theory '((:rewrite if-bad-index-not-in-range-then-every-equalsumandupdate)))))



(defthm lemma2-only-adds-in-rtm-add
  (implies
   (and
    (gem-statep gstate)
    (rtm-statep rstate)
    (in-range (pcc gstate) (code gstate))
    (in-range (pcc rstate) (code rstate))
    (equal (opcode (nth (pcc gstate) (code gstate))) 'gem-add)
    (good-translation-gem-rtm gstate rstate m))
   (all-rtm-adds-for-n-steps rstate (len *rns*)))
  :hints (("Goal" :expand
	   ( (good-translation-gem-rtm gstate rstate m)
	     (gem-statep gstate)
	     (rtm-statep rstate)
	     (in-range (pcc gstate) (code gstate))
	     (in-range (pcc rstate) (code rstate)))
	   :in-theory nil))
  :rule-classes nil)


(defthm cells-untouched-by-execute-on-other-cell-add
 (implies
  (and
   (integerp n)
   (>= n 0)
   (all-rtm-adds-for-n-steps st n)
   (>= (pcc st) 0)
   (rtm-statep st)
   (not (member-equal-bool v (listpars1 st n))))
  (equal (get-cell v (mem st))
	 (get-cell v (mem (execute-n-instructions st n)))))
 :hints (("Goal"
	  :use (execute-n-instructions-tantamount-to-add-list-e
		(:instance not-in-list-untouched-by-adds-list-e
				  (v v)
				  (l1 (listpars1 st n))
				  (l2 (listpars2 st n))
				  (l3 (listpars3 st n))
				  (l4 (listpars4 st n))
				  (mem (mem st)))))))


(defthm rtm-variable-of-other-cell-untouched-add
  (implies
   (and
    (equal (opcode (nth (pcc gstate) (code gstate))) 'gem-add)
    (>= (pcc rstate) 0)
    (rtm-statep rstate)
    (good-translation-gem-rtm gstate rstate m)
    (in-range (pcc gstate) (code gstate))
    (assoc-equal (par1 (nth (pcc gstate) (code gstate))) m)
    (true-listp m)
    (no-duplicates-p (append-lists (retrieve-rtmvars m)))
    (assoc-equal gvar1 m)
    (not (equal gvar1 (par1 (nth (pcc gstate) (code gstate)))))
    (in-range idx1 (rtmintvars-i gvar1 m)))
   (equal (get-cell (nth idx1 (rtmintvars-i gvar1 m)) (mem rstate))
	  (get-cell (nth idx1 (rtmintvars-i gvar1 m)) (mem (execute-n-instructions rstate (len *rns*))))))
  :hints (("Goal" :in-theory (current-theory 'ground-zero)
	   :expand (     (in-range (pcc gstate) (code gstate))
			 (good-translation-gem-rtm gstate rstate m) )
	   :use (
		 (:instance lemma1-different-vars-do-not-belong  (gvar2 (par1 (nth (pcc gstate) (code gstate)))))
		 (:instance cells-untouched-by-execute-on-other-cell-add (st rstate) (n (len *rns*))
			    (v (nth idx1 (rtmintvars-i gvar1 m))))))))

(defthm rtm-variables-of-other-cell-untouched-add
  (implies
   (and
    (equal (opcode (nth (pcc gstate) (code gstate))) 'gem-add)
    (>= (pcc rstate) 0)
    (rtm-statep rstate)
    (good-translation-gem-rtm gstate rstate m)
    (in-range (pcc gstate) (code gstate))
    (assoc-equal (par1 (nth (pcc gstate) (code gstate))) m)
    (true-listp m)
    (no-duplicates-p (append-lists (retrieve-rtmvars m)))
    (assoc-equal gvar1 m)
    (true-listp (rtmintvars-i gvar1 m))
    (not (equal gvar1 (par1 (nth (pcc gstate) (code gstate))))))
   (equal-get-cells
          (rtmintvars-i gvar1 m) (mem rstate) (mem (execute-n-instructions rstate (len *rns*)))))
  :hints (("Goal" :in-theory nil
	   :use ( (:instance rtm-variable-of-other-cell-untouched-add
			     (idx1 (idx-different-cell
				    (rtmintvars-i gvar1 m)
				    (mem rstate)
				    (mem (execute-n-instructions rstate (len *rns*)))))) ))
	  ("Goal'" :cases ( (in-range
			     (idx-different-cell
				    (rtmintvars-i gvar1 m)
				    (mem rstate)
				    (mem (execute-n-instructions rstate (len *rns*))))
			     (rtmintvars-i gvar1 m))))
	  ("Subgoal 2" :in-theory '((:rewrite if-bad-index-not-in-range-then-every-equal)))
	  ("Subgoal 1" :in-theory '((:forward-chaining if-bad-index-in-range-then-cells-must-be-different)))))




(defthm properies-of-type-and-existence-of-current-args-add
 (implies
  (and
   (gem-statep gstate)
   (in-range (pcc gstate) (code gstate))
   (equal (opcode (nth (pcc gstate) (code gstate))) 'gem-add))
  (and
   (equal (var-type (get-cell (par1 (nth (pcc gstate) (code gstate))) (mem gstate))) 'Int)
   (assoc-equal (par1 (nth (pcc gstate) (code gstate))) (mem gstate))
   (assoc-equal (par2 (nth (pcc gstate) (code gstate))) (mem gstate))
   (assoc-equal (par3 (nth (pcc gstate) (code gstate))) (mem gstate))))
  :hints (("Goal" :in-theory (enable get-cell)
	   :use (:instance in-range-instruction-is-gem-instruction
			   (pcc (pcc gstate))
			   (code (code gstate))
			   (mem (mem gstate)))))
  :rule-classes nil)


(defthm par1-of-current-instruction-is-into-mapping-add
 (implies
  (and
   (vars-inclusion (mem gstate) m)
   (gem-statep gstate)
   (equal (opcode (nth (pcc gstate) (code gstate))) 'gem-add)
   (in-range (pcc gstate) (code gstate)))
  (assoc-equal (par1 (nth (pcc gstate) (code gstate))) m))
 :hints (("Goal" :in-theory (enable get-cell)
	 :use (properies-of-type-and-existence-of-current-args-add
	       (:instance inclusion-trans
			  (v (par1 (nth (pcc gstate) (code gstate))))
			  (m1 (mem gstate))
			  (m2 m))
	       (:instance in-range-instruction-is-gem-instruction
				 (pcc (pcc gstate))
				 (code (code gstate))
				 (mem (mem gstate)))))))



(defthm teorema-main-con-pcc-in-range-su-variabile-non-interessata-final-add
 (implies
  (and
   (equal (opcode (nth (pcc gstate) (code gstate))) 'gem-add)
   (good-translation-gem-rtm gstate rstate m)
   (vars-inclusion (mem gstate) m)
   (true-listp m)
   (assoc-equal gvar1 m)
   (gem-statep gstate)
   (rtm-statep rstate)
   (in-range (pcc gstate) (code gstate))
   (in-range (pcc rstate) (code rstate))
   (not (equal gvar1 (par1 (nth (pcc gstate) (code gstate)))))
   (m-correspondent-values-p m (mem gstate) (mem rstate))
   (no-duplicates-p (append-lists (retrieve-rtmvars m)))
   (correct-wrt-arity m (mem gstate)))
  (equal-values-and-attributes
   (get-cell gvar1 (mem (execute-instruction gstate)))
   (rtmintvars-i gvar1 m)
   (mem (execute-n-instructions rstate (len *rns*)))
   (type-i gvar1 m)))
 :hints (("Goal"
	  :in-theory '((:definition good-translation-gem-rtm))
	  :use (
		par1-of-current-instruction-is-into-mapping-add
		(:instance correct-wrt-arity-has-rtmintvars-i-tl (mem (mem gstate)))
		(:instance m-correspondent-values-implies-equal-values-and-attribus
			   (memgstate (mem gstate)) (memrstate (mem rstate)))
		(:instance in-range (idx (pcc gstate)) (l (code gstate)))
		(:instance in-range (idx (pcc rstate)) (l (code rstate)))
		rtm-variables-of-other-cell-untouched-add
		teorema-main-con-pcc-in-range-su-variabile-non-interessata
		(:instance equal-get-cells-implies-equal-values-and-attributes-still-works
			   (gemcell (get-cell gvar1 (mem gstate)))
			   (lcell (rtmintvars-i gvar1 m))
			   (mem1 (mem rstate))
			   (mem2 (mem (execute-n-instructions rstate (len *rns*))))
			   (type (type-i gvar1 m)))))))


(defthm teorema-main-con-pcc-in-range-su-variabile-interessata-add
 (implies
  (and
   (gem-statep gstate)
   (rtm-statep rstate)
   (in-range (pcc gstate) (code gstate))
   (in-range (pcc rstate) (code rstate))
   (equal (opcode (nth (pcc gstate) (code gstate))) 'gem-add)
   (good-translation-gem-rtm gstate rstate m))
  (equal
   (mem (execute-n-instructions rstate (len *rns*)))
   (adds-list-e
    (rtmintvars-i (par1 (nth (pcc gstate) (code gstate))) m)
    (eventually-make-list (rtmintvars-i (par2 (nth (pcc gstate) (code gstate))) m) (len *rns*)) ;new
    (eventually-make-list (rtmintvars-i (par3 (nth (pcc gstate) (code gstate))) m) (len *rns*)) ;new
    *rns*
    (mem rstate))))
  :hints (("Goal"
	   :in-theory (union-theories (current-theory 'ground-zero) '((:definition in-range)))
	   :use (good-translation-gem-rtm
		 lemma2-only-adds-in-rtm-add
		 (:instance execute-n-instructions-tantamount-to-add-list-e
			    (n (len *rns*))
			    (st rstate)))))
  :rule-classes nil)




(defthm posinrg-add
  (implies
   (and
    (vars-inclusion (mem gstate) m)
    (gem-statep gstate)
    (equal (opcode (nth (pcc gstate) (code gstate))) 'gem-add)
    (in-range (pcc gstate) (code gstate)))
   (and
    (in-range (pos-equal-0 (par1 (nth (pcc gstate) (code gstate))) m) m)
    (in-range (pos-equal-0 (par2 (nth (pcc gstate) (code gstate))) m) m)
    (in-range (pos-equal-0 (par3 (nth (pcc gstate) (code gstate))) m) m)))
   :hints (("Goal"
	    :use (properies-of-type-and-existence-of-current-args-add
			(:instance inclusion-trans (m1 (mem gstate)) (m2 m)
				   (v (par1 (nth (pcc gstate) (code gstate)))))
			(:instance inclusion-trans (m1 (mem gstate)) (m2 m)
				   (v (par2 (nth (pcc gstate) (code gstate)))))
			(:instance inclusion-trans (m1 (mem gstate)) (m2 m)
				   (v (par3 (nth (pcc gstate) (code gstate)))))
			(:instance assoc-means-pos-in-range
				   (el (par1 (nth (pcc gstate) (code gstate))))
				   (l m))
			(:instance assoc-means-pos-in-range
				   (el (par2 (nth (pcc gstate) (code gstate))))
				   (l m))
			(:instance assoc-means-pos-in-range
				   (el (par3 (nth (pcc gstate) (code gstate))))
				   (l m)))))
   :rule-classes nil)

(defthm eqlenss-add
  (implies
   (and
    (gem-statep gstate)
    (rtm-statep rstate)
    (in-range (pcc gstate) (code gstate))
    (in-range (pcc rstate) (code rstate))
    (equal (opcode (nth (pcc gstate) (code gstate))) 'gem-add)
    (good-translation-gem-rtm gstate rstate m))
   (and
    (equal (len (rtmintvars-i (par1 (nth (pcc gstate) (code gstate))) m)) (len *rns*))
    (equal (len (eventually-make-list (rtmintvars-i (par2 (nth (pcc gstate) (code gstate))) m) (len *rns*))) (len *rns*))
    (equal (len (eventually-make-list (rtmintvars-i (par3 (nth (pcc gstate) (code gstate))) m) (len *rns*))) (len *rns*))))
  :hints (("Goal"
	   :in-theory (union-theories (current-theory 'ground-zero) '((:definition in-range)))
	   :use
	   (
	    good-translation-gem-rtm
	    (:instance length-of-listpars1-n-is-n (st rstate) (n (len *rns*)))
	    (:instance length-of-listpars2-n-is-n (st rstate) (n (len *rns*)))
	    (:instance length-of-listpars3-n-is-n (st rstate) (n (len *rns*))))))
  :rule-classes nil)


(defthm equal-sum-and-updates-after-n-instr
  (implies
   (and
    (true-listp m)
    (correct-wrt-arity m (mem gstate))
    (gem-statep gstate)
    (rtm-statep rstate)
    (vars-inclusion (mem gstate) m)
    (in-range (pcc gstate) (code gstate))
    (in-range (pcc rstate) (code rstate))
    (equal (opcode (nth (pcc gstate) (code gstate))) 'gem-add)
    (good-translation-gem-rtm gstate rstate m)
    (no-duplicates-p (append-lists (retrieve-rtmvars m)))
    (assoc-equal gvar1 m)
    (equal gvar1 (par1 (nth (pcc gstate) (code gstate)))))
   (equal-sum-and-updates
    (rtmintvars-i gvar1 m)
    (rtmintvars-i (par1 (nth (pcc gstate) (code gstate))) m)
    (eventually-make-list (rtmintvars-i (par2 (nth (pcc gstate) (code gstate))) m) (len *rns*)) ;new
    (eventually-make-list (rtmintvars-i (par3 (nth (pcc gstate) (code gstate))) m) (len *rns*)) ;new
    *rns*
    (mem rstate)
    (mem (execute-n-instructions rstate (len *rns*)))))
  :hints (("Goal"
	   :in-theory (union-theories (current-theory 'ground-zero)
				      '((:type-prescription retrieve-rtmvars)
					(:definition positive-list)
					(:definition positivep)
					(:definition in-range)))
	   :use
	   (
	     (:instance correct-wrt-arity-has-rtmintvars-i-tl (mem (mem gstate)))
	     (:instance sum-and-updates-holding-for-every-variable-type
			(n (len *rns*))
			(ll (retrieve-rtmvars m))
			(rns *rns*)
			(gem1 (pos-equal-0 (par1 (nth (pcc gstate) (code gstate))) m))
			(gem2 (pos-equal-0 (par2 (nth (pcc gstate) (code gstate))) m))
			(gem3 (pos-equal-0 (par3 (nth (pcc gstate) (code gstate))) m))
			(mem (mem rstate)))
	     lemma-help2
	     eqlenss-add
	     posinrg-add
	     teorema-main-con-pcc-in-range-su-variabile-interessata-add
	     (:instance rtmintvars-i-is-pos-equal-0-of-retrieve-vars
			(gvar (par1 (nth (pcc gstate) (code gstate)))))
	     (:instance rtmintvars-i-is-pos-equal-0-of-retrieve-vars
			(gvar (par2 (nth (pcc gstate) (code gstate)))))
	     (:instance rtmintvars-i-is-pos-equal-0-of-retrieve-vars
			(gvar (par3 (nth (pcc gstate) (code gstate)))))
	     (:instance rtmintvars-i-is-pos-equal-0-of-retrieve-vars
			(gvar (par4 (nth (pcc gstate) (code gstate)))))))))


(defthm equal-sum-and-update-norest-afetr-one-instr
  (implies
   (and
    (gem-statep gstate)
    (in-range (pcc gstate) (code gstate))
    (good-translation-gem-rtm gstate rstate m)
    (equal (opcode (nth (pcc gstate) (code gstate))) 'gem-add)
    (equal gvar1 (par1 (nth (pcc gstate) (code gstate))))
    (equal gvar2 (par2 (nth (pcc gstate) (code gstate))))
    (equal gvar3 (par3 (nth (pcc gstate) (code gstate)))))
   (equal (get-cell gvar1 (mem (execute-instruction gstate)))
	  (sum-and-update-norest gvar1 gvar2 gvar3 (mem gstate))))
  :hints (("Goal" :in-theory (e/d (put-cell get-cell)
				  (par1 par2 par3 par4 opcode pcc code nth gem-instruction-list-p
					gen-eq-update sum-and-update sub-and-update sub-and-update-norest sum-and-update-norest))))
  :rule-classes nil)


(DEFTHM mem-cellity-of-current-gem-args-add
  (IMPLIES
   (AND (GEM-STATEP GSTATE)
	(equal (opcode (nth (pcc gstate) (code gstate))) 'gem-add)
	(IN-RANGE (PCC GSTATE) (CODE GSTATE)))
   (AND (is-mem-cell-p (get-cell  (PAR1 (NTH (PCC GSTATE) (CODE GSTATE))) (mem gstate)))
	(is-mem-cell-p (get-cell  (PAR2 (NTH (PCC GSTATE) (CODE GSTATE))) (mem gstate)))
	(is-mem-cell-p (get-cell  (PAR3 (NTH (PCC GSTATE) (CODE GSTATE))) (mem gstate)))))
  :HINTS
  (("Goal"
    :USE
    (:INSTANCE IN-RANGE-INSTRUCTION-IS-GEM-INSTRUCTION
	       (PCC (PCC GSTATE))
	       (CODE (CODE GSTATE))
	       (MEM (MEM GSTATE))))))



(defthm type-is-for-pars-add
 (implies
   (and
    (true-listp m)
    (vars-inclusion (mem gstate) m)
    (gem-statep gstate)
    (correct-wrt-arity m (mem gstate))
    (equal (opcode (nth (pcc gstate) (code gstate))) 'gem-add)
    (equal gvar1 (par1 (nth (pcc gstate) (code gstate))))
    (equal gvar2 (par2 (nth (pcc gstate) (code gstate))))
    (equal gvar3 (par3 (nth (pcc gstate) (code gstate))))
    (in-range (pcc gstate) (code gstate)))
   (equal (type-i gvar1 m) 'int))
 :hints (("Goal"
	  :in-theory (disable type-i-is-type-expected rtmintvars-i-is-pos-equal-0-of-retrieve-vars)
	  :use ( properies-of-type-and-existence-of-current-args-add
		 (:instance type-i-is-vartyper (gvar1 gvar1))
		 (:instance type-i-is-vartyper (gvar1 gvar2))
		 (:instance type-i-is-vartyper (gvar1 gvar3))
		 (:instance inclusion-trans (m1 (mem gstate)) (m2 m)
			    (v (par1 (nth (pcc gstate) (code gstate)))))
		 (:instance inclusion-trans (m1 (mem gstate)) (m2 m)
			    (v (par2 (nth (pcc gstate) (code gstate)))))
		 (:instance inclusion-trans (m1 (mem gstate)) (m2 m)
			    (v (par3 (nth (pcc gstate) (code gstate))))))))
 :rule-classes nil)


(defthm m-correspondence-kept-on-same-gvar-add
  (implies
   (and
    (good-translation-gem-rtm gstate rstate m)
    (equal (opcode (nth (pcc gstate) (code gstate))) 'gem-add)
    (equal gvar1 (par1 (nth (pcc gstate) (code gstate))))
    (true-listp m)
    (correct-wrt-arity m (mem gstate))
    (gem-statep gstate)
    (rtm-statep rstate)
    (vars-inclusion (mem gstate) m)
    (in-range (pcc gstate) (code gstate))
    (in-range (pcc rstate) (code rstate))
    (no-duplicates-p (append-lists (retrieve-rtmvars m)))
    (assoc-equal gvar1 m)
    (m-correspondent-values-p m (mem gstate) (mem rstate)))
  (equal-values-and-attributes
   (get-cell gvar1 (mem (execute-instruction gstate)))
   (rtmintvars-i gvar1 m)
   (mem (execute-n-instructions rstate (len *rns*)))
   (type-i gvar1 m)))
  :hints (("Goal"  :in-theory nil
	   :use (
		 properies-of-type-and-existence-of-current-args-add
		 mem-cellity-of-current-gem-args-add
		 good-translation-gem-rtm
		 (:instance type-i-is-vartyper (gvar1 gvar1) (mem (mem gstate)))
		 (:instance type-i-is-vartyper (gvar1 (par2 (nth (pcc gstate) (code gstate)))) (mem (mem gstate)))
		 (:instance type-i-is-vartyper (gvar1 (par3 (nth (pcc gstate) (code gstate)))) (mem (mem gstate)))
		 (:instance type-i-is-type-expected (gvar  gvar1) (mem (mem gstate)))
		 (:instance type-i-is-type-expected (gvar  (par2 (nth (pcc gstate) (code gstate)))) (mem (mem gstate)))
		 (:instance type-i-is-type-expected (gvar  (par3 (nth (pcc gstate) (code gstate)))) (mem (mem gstate)))
		 (:instance inclusion-trans (m1 (mem gstate)) (m2 m)
			    (v (par1 (nth (pcc gstate) (code gstate)))))
		 (:instance inclusion-trans (m1 (mem gstate)) (m2 m)
			    (v (par2 (nth (pcc gstate) (code gstate)))))
		 (:instance inclusion-trans (m1 (mem gstate)) (m2 m)
			    (v (par3 (nth (pcc gstate) (code gstate)))))
		  (:instance
		   equal-sum-and-update-norest-afetr-one-instr
		   (gvar2 (par2 (nth (pcc gstate) (code gstate))))
		   (gvar3 (par3 (nth (pcc gstate) (code gstate))))
		   )
		  eqlenss-add
		  (:instance correct-wrt-arity-has-rtmintvars-i-tl (mem (mem gstate)))
		  (:instance type-is-for-pars-add
		   (gvar2 (par2 (nth (pcc gstate) (code gstate))))
		   (gvar3 (par3 (nth (pcc gstate) (code gstate)))))
		  (:instance m-correspondent-values-implies-equal-values-and-attribus
			     (memgstate (mem gstate)) (memrstate (mem rstate))
			     (gvar1 gvar1))
		  (:instance m-correspondent-values-implies-equal-values-and-attribus
			     (memgstate (mem gstate)) (memrstate (mem rstate))
			     (gvar1 (par2 (nth (pcc gstate) (code gstate)))))
		  (:instance m-correspondent-values-implies-equal-values-and-attribus
			     (memgstate (mem gstate)) (memrstate (mem rstate))
			     (gvar1 (par3 (nth (pcc gstate) (code gstate)))))
		  equal-sum-and-updates-after-n-instr
		  (:instance
		   if-gem-is-sum-and-update-inf-every-rtm-var-is-sum-and-update-then-equal-values-is-kept-g
		   (gvar2 (par2 (nth (pcc gstate) (code gstate))))
		   (gvar3 (par3 (nth (pcc gstate) (code gstate))))
		   (rtmvars1   (rtmintvars-i gvar1 m))
		   (rtmvars2   (rtmintvars-i (par2 (nth (pcc gstate) (code gstate))) m))
		   (rtmvars3   (rtmintvars-i (par3 (nth (pcc gstate) (code gstate))) m))
		   (rtmvarsres (rtmintvars-i gvar1 m))
		   (gemmem (mem gstate))
		   (rtmmem (mem rstate))
		   (rtmmemafter (mem (execute-n-instructions rstate (len *rns*)))))))))


(defthm equal-values-correspondence-kept-by-any-execution-add
  (implies
   (and
    (equal (opcode (nth (pcc gstate) (code gstate))) 'gem-add)
    (good-translation-gem-rtm gstate rstate m)
    (true-listp m)
    (correct-wrt-arity m (mem gstate))
    (gem-statep gstate)
    (rtm-statep rstate)
    (vars-inclusion (mem gstate) m)
    (in-range (pcc gstate) (code gstate))
    (in-range (pcc rstate) (code rstate))
    (no-duplicates-p (append-lists (retrieve-rtmvars m)))
    (assoc-equal gvar1 m)
    (m-correspondent-values-p m (mem gstate) (mem rstate)))
  (equal-values-and-attributes
   (get-cell gvar1 (mem (execute-instruction gstate)))
   (rtmintvars-i gvar1 m)
   (mem (execute-n-instructions rstate (len *rns*)))
   (type-i gvar1 m)))
  :hints (("Goal" :use (m-correspondence-kept-on-same-gvar-add
			teorema-main-con-pcc-in-range-su-variabile-non-interessata-final-add))))



(defthm equal-values-correspondence-kept-by-any-execution-idxed-add
  (implies
   (and
    (equal (opcode (nth (pcc gstate) (code gstate))) 'gem-add)
    (no-duplicates-p (retrieve-gemvars m))
    (good-translation-gem-rtm gstate rstate m)
    (alistp m)
    (correct-wrt-arity m (mem gstate))
    (gem-statep gstate)
    (rtm-statep rstate)
    (vars-inclusion (mem gstate) m)
    (in-range (pcc gstate) (code gstate))
    (in-range (pcc rstate) (code rstate))
    (no-duplicates-p (append-lists (retrieve-rtmvars m)))
    (in-range idx m)
    (m-correspondent-values-p m (mem gstate) (mem rstate)))
  (equal-values-and-attributes
   (get-cell (car (nth idx m)) (mem (execute-instruction gstate)))
   (cdr (nth idx m))
   (mem (execute-n-instructions rstate (len *rns*)))
   (type-i-idx m idx)))
  :hints (("Goal" :in-theory (union-theories (current-theory 'ground-zero) '((:definition in-range)))
	   :use ( (:theorem
		   (implies
		    (and
		     (alistp m)
		     (in-range idx m))
		    (and
		     (true-listp m)
		     (assoc-equal (car (nth idx m)) m))))
		  type-i-idx
		  (:instance type-i (gvar (car (nth idx m))))
		  (:instance rtmintvars-i-is-cdr-of-nth-entry (gvar (car (nth idx m))))
		  (:instance equal-values-correspondence-kept-by-any-execution-add (gvar1 (car (nth idx m))))
		  (:instance no-duplicates-has-pos-equal-right-in-that-place (l m)))))
  :otf-flg t)

(defthm m-correspondence-kept-by-any-execution-idxed-add
  (implies
   (and
    (equal (opcode (nth (pcc gstate) (code gstate))) 'gem-add)
    (no-duplicates-p (retrieve-gemvars m))
    (good-translation-gem-rtm gstate rstate m)
    (alistp m)
    (correct-wrt-arity m (mem gstate))
    (gem-statep gstate)
    (rtm-statep rstate)
    (vars-inclusion (mem gstate) m)
    (in-range (pcc gstate) (code gstate))
    (in-range (pcc rstate) (code rstate))
    (no-duplicates-p (append-lists (retrieve-rtmvars m)))
    (m-correspondent-values-p m (mem gstate) (mem rstate)))
  (m-correspondent-values-p
   m
   (mem (execute-instruction gstate))
   (mem (execute-n-instructions rstate (len *rns*)))))
  :hints (("Goal" :use (:instance equal-values-correspondence-kept-by-any-execution-idxed-add
				  (idx (bad-idx-eqv-va m
						       (mem (execute-instruction gstate))
						       (mem (execute-n-instructions rstate (len *rns*)))))))
	  ("Goal'" :cases ( (in-range (bad-idx-eqv-va m (mem (execute-instruction gstate))
						       (mem (execute-n-instructions rstate (len *rns*)))) m)))
	  ("Subgoal 2" :in-theory '((:forward-chaining alistp-forward-to-true-listp)
				    (:rewrite if-bad-index-not-in-range-then-m-corr)))
	  ("Subgoal 1" :in-theory '((:rewrite if-bad-index-in-range-thne-must-be-different-vs)))))




(defthm m-correspondence-and-other-conditions-kept-by-any-execution-add
  (implies
   (and
    (alistp m)
    (equal (opcode (nth (pcc gstate) (code gstate))) 'gem-add)
    (no-duplicates-p (retrieve-gemvars m))
    (no-duplicates-p (append-lists (retrieve-rtmvars m)))
    (good-translation-gem-rtm gstate rstate m)
    (correct-wrt-arity m (mem gstate))
    (gem-statep gstate)
    (rtm-statep rstate)
    (vars-inclusion (mem gstate) m)
    (vars-inclusion m (mem gstate))
    (in-range (pcc gstate) (code gstate))
    (in-range (pcc rstate) (code rstate))
    (m-entries-point-to-good-rtm-var-sets m (mem rstate))
    (m-correspondent-values-p m (mem gstate) (mem rstate)))
   (and
    (good-translation-gem-rtm (execute-instruction gstate) (execute-n-instructions rstate (len *rns*)) m)
    (rtm-statep (execute-n-instructions rstate (len *rns*)))
    (m-entries-point-to-good-rtm-var-sets m (mem (execute-n-instructions rstate (len *rns*))))
    (gem-statep (execute-instruction gstate))
    (correct-wrt-arity m (mem (execute-instruction gstate)))
    (vars-inclusion (mem (execute-instruction gstate)) m)
    (vars-inclusion m (mem (execute-instruction gstate)))
    (m-correspondent-values-p
     m
     (mem (execute-instruction gstate))
     (mem (execute-n-instructions rstate (len *rns*))))))
:hints (("Goal"
	 :in-theory (disable
		     rtm-statep gem-statep
		     pcc code opcode
		     execute-instruction rtmintvars-i par1 par2 par3 nth len member-equal)
	 :use
	 (m-correspondence-kept-by-any-execution-idxed-add
	  good-translation-gem-rtm
	  (:instance execute-n-instructions-keeps-rtm-state-and-points-to-good
		     (st rstate) (n (len *rns*)))
	  (:instance executing-gem-instruction-retrieves-a-gem-state-from-gem-state (st gstate))
	  (:instance executing-gem-instruction-preserves-correctness-wrt-arity (st gstate))
	  (:instance executing-gem-instruction-keeps-vars-inclusion-right      (st gstate))
	  (:instance executing-gem-instruction-keeps-vars-inclusion-left       (st gstate))))))











;;(ld "Proof-Of-Minus.lisp" :ld-error-action :error)


(in-theory (enable
	    (:executable-counterpart build-values-by-rns)
	    (:type-prescription build-values-by-rns)
	    (:induction build-values-by-rns)
	    (:definition build-values-by-rns)
	    posp-all posp mod mod-- mod-prod-makes-same-residues))

(in-theory (disable mod floor))

(defun sub-list (vl2 vl3 rns)
  (if (endp vl2)
      nil
       (cons (mod (- (car vl2) (car vl3)) (car rns))
	     (sub-list (cdr vl2) (cdr vl3) (cdr rns)))))


(defthm sub-correspondence-by-put-list
 (implies
  (and
   (integerp gval1)
   (integerp gval2)
   (posp-all rns))
   (equal (build-values-by-rns (- gval1 gval2) rns)
	  (sub-list
	   (build-values-by-rns gval1 rns)
	   (build-values-by-rns gval2 rns)
	   rns)))
   :hints (("Goal" :induct t)))




(in-theory (disable mod floor))

(defthm sub-correspondence-by-put-list-2-fin
 (implies
  (and
   (integerp gval1)
   (integerp gval2)
   (posp-all rns))
  (equal (build-values-by-rns (mod (- gval1 gval2) (prod rns)) rns)
	 (sub-list
	  (build-values-by-rns  gval1 rns)
	  (build-values-by-rns  gval2 rns)
	 rns)))
 :hints (("Goal" :in-theory (disable sum-correspondence-by-put-list-2-fin sum-correspondence-by-put-list)
	  :use (sub-correspondence-by-put-list
		(:instance mod-prod-makes-same-residues (x (- gval1 gval2)))))))



(in-theory (disable mod floor mod-- mod-prod-makes-same-residues))


(defthm sub-correspondence-by-put-list-h
 (implies
  (and
   (integerp gval1)
   (integerp gval2)
   (integer>1-listp rns))
   (equal (build-values-by-rns (mod (- gval1 gval2) (prod rns)) rns)
	  (sub-list
	   (build-values-by-rns gval1 rns)
	   (build-values-by-rns gval2 rns)
	   rns)))
   :hints (("Goal" :use (sub-correspondence-by-put-list-2-fin greater-one-means-greater-zero))))




(defthm a-boolean-has-same-rnss-than-list-of-itself
 (implies
  (and
   (integerp val)
   (or (equal val 0) (equal val 1))
   (integer>1-listp rns))
  (equal
   (build-values-by-rns val rns)
   (make-n-list val (len rns)))))



(defthm sub-correspondence-by-put-list-on-boolean
 (implies
  (and
   (integerp gval1)
   (integerp gval2)
   (or (equal gval2 0) (equal gval2 1))
   (integer>1-listp rns))
   (equal (build-values-by-rns (mod (- gval1 gval2) (prod rns)) rns)
	  (sub-list
	   (build-values-by-rns gval1 rns)
	   (make-n-list gval2 (len rns))
	   rns)))
 :hints (("Goal" :in-theory nil
	  :use (sub-correspondence-by-put-list-h
		(:instance a-boolean-has-same-rnss-than-list-of-itself (val gval2))))))

(in-theory (disable mod--))


(defun equal-sub-and-updates (reslist par1list par2list par3list primelist mem memafterputs)
  (if (endp reslist)
      (null reslist)
    (and
     (equal
      (get-cell (car reslist) memafterputs)
      (sub-and-update
       (car par1list)
       (car par2list)
       (car par3list)
       (car primelist)
       mem))
     (equal-sub-and-updates
      (cdr reslist)
      (cdr par1list)
      (cdr par2list)
      (cdr par3list)
      (cdr primelist)
      mem
      memafterputs))))





(defthm equal-sub-and-updates-have-same-attributes
 (implies
  (and
   (true-listp rtmvars1)
   (true-listp rtmvarsres)
   (equal (len rtmvars1) (len rtmvarsres))
   (equal-sub-and-updates rtmvarsres rtmvars1 rtmvars2 rtmvars3 rns rtmmem rtmmemafter))
  (equal (var-attributes rtmvarsres rtmmemafter) (var-attributes rtmvars1 rtmmem)))
 :hints (("Goal" :in-theory (enable var-attribute make-cell))))

;(in-theory (enable sub-list))

(defthm equal-sub-and-updates-have-values-that-are-sub-lists
  (implies
   (and
    (equal (len rtmvars1) (len rtmvarsres))
    (equal (len rtmvars2) (len rtmvarsres))
    (equal (len rtmvars3) (len rtmvarsres))
    (equal-sub-and-updates rtmvarsres rtmvars1 rtmvars2 rtmvars3 rns rtmmem rtmmemafter))
   (equal (var-values rtmvarsres rtmmemafter)
	 (sub-list
	  (var-values rtmvars2 rtmmem)
	  (var-values rtmvars3 rtmmem)
	  rns)))
 :hints ( ("Subgoal *1/2" :in-theory (enable var-value get-cell make-cell))))





(defthm behaviour-of-sub-and-update-norest
 (and
  (equal
   (var-attribute (sub-and-update-norest c1 c2 c3 mem))
   (var-attribute (get-cell c1 mem)))
  (equal
   (var-value (sub-and-update-norest c1 c2 c3 mem))
   (mod
    (-
     (var-value (get-cell c2 mem))
     (var-value (get-cell c3 mem)))
    (prod *rns*)))
  (equal
   (var-type (sub-and-update-norest c1 c2 c3 mem))
   (var-type (get-cell c1 mem))))
 :hints (("Goal" :in-theory (enable var-type var-value var-attribute make-cell))))




(defthm defexpansion-sub
  (implies
   (not (null (var-value gcell)))
  (equal
   (equal-values-and-attributes gcell rtmvars rtmmem 'Int)
   (and
    (equal-values (var-values rtmvars rtmmem)
		  (build-values-by-rns (var-value gcell) *rns*))
    (equal-elements (var-attribute gcell)
		    (var-attributes rtmvars rtmmem)))))
  :hints (("Goal" :in-theory '((:definition equal-values-and-attributes)
			       (:definition apply-direct-rns-to-value-according-to-type))
	   :use (:instance build-values-by-rns-extended-behaves-standardly-on-non-nils
			   (gem-value (var-value gcell))
			   (rns *rns*)))))





(defthm if-gem-is-sub-and-update-inf-every-rtm-var-is-sub-and-update-then-equal-values-is-kept
 (implies
  (and
   (true-listp rtmvars1)
   (true-listp rtmvarsres)
   (equal (len rtmvars1) (len rtmvarsres))
   (equal (len rtmvars2) (len rtmvarsres))
   (equal (len rtmvars3) (len rtmvarsres))
   (not (null (var-value (get-cell gvar1 gemmem))))
   (integerp (var-value (get-cell gvar2 gemmem)))
   (integerp (var-value (get-cell gvar3 gemmem)))
   (equal-sub-and-updates rtmvarsres rtmvars1 rtmvars2 rtmvars3 *rns* rtmmem rtmmemafter)
   (equal-values-and-attributes (get-cell gvar1 gemmem) rtmvars1 rtmmem 'Int)
   (equal-values-and-attributes (get-cell gvar2 gemmem) rtmvars2 rtmmem 'Int)
   (equal-values-and-attributes (get-cell gvar3 gemmem) rtmvars3 rtmmem 'Int))
  (equal-values-and-attributes
   (sub-and-update-norest gvar1 gvar2 gvar3 gemmem)
   rtmvarsres
   rtmmemafter
   'Int))
 :hints (("Goal"
	  :in-theory (union-theories (current-theory 'ground-zero)
				     '(
				       (:definition integer>1-listp)
				       (:definition equal-values)
				       (:rewrite defexpansion-sub)))
	  :use (
		(:instance greater-one-means-greater-zero (rns *rns*))
		(:instance equal-sub-and-updates-have-values-that-are-sub-lists (rns *rns*))
		(:instance equal-sub-and-updates-have-same-attributes           (rns *rns*))
		(:instance sub-correspondence-by-put-list-h
			   (gval1 (var-value (get-cell gvar2 gemmem)))
			   (gval2 (var-value (get-cell gvar3 gemmem)))
			   (rns *rns*))
		(:instance behaviour-of-sub-and-update-norest
			   (c1 gvar1)
			   (c2 gvar2)
			   (c3 gvar3)
			   (mem gemmem)))))
 )












(defthm if-gem-is-sub-and-update-inf-every-rtm-var-is-sub-and-update-then-equal-values-is-kept-g
 (implies
  (and
   (true-listp rtmvars1)
   (true-listp rtmvarsres)
   (equal (len rtmvars1)                                     (len rtmvarsres))
   (equal (len (eventually-make-list rtmvars2 (len *rns*)))  (len rtmvarsres))
   (equal (len (eventually-make-list rtmvars3 (len *rns*)))  (len rtmvarsres))
   (equal (var-type (get-cell gvar2 gemmem)) (type-expected rtmvars2))
   (equal (var-type (get-cell gvar3 gemmem)) (type-expected rtmvars3))
   (is-mem-cell-p (get-cell gvar1 gemmem))
   (equal (var-type (get-cell gvar1 gemmem)) 'Int)
   (is-mem-cell-p (get-cell gvar2 gemmem))
   (is-mem-cell-p (get-cell gvar3 gemmem))
   (equal-sub-and-updates
    rtmvarsres
    rtmvars1
    (eventually-make-list rtmvars2 (len *rns*))
    (eventually-make-list rtmvars3 (len *rns*))
    *rns* rtmmem rtmmemafter)
   (equal-values-and-attributes (get-cell gvar1 gemmem) rtmvars1 rtmmem 'Int)
   (equal-values-and-attributes (get-cell gvar2 gemmem) rtmvars2 rtmmem (var-type (get-cell gvar2 gemmem)))
   (equal-values-and-attributes (get-cell gvar3 gemmem) rtmvars3 rtmmem (var-type (get-cell gvar3 gemmem))))
  (equal-values-and-attributes
   (sub-and-update-norest gvar1 gvar2 gvar3 gemmem)
   rtmvarsres
   rtmmemafter
   'Int))
 :hints (("Goal"
	  :in-theory (union-theories (current-theory 'ground-zero)
				     '((:definition integer>1-listp)
				       (:definition equal-values)
				       (:definition is-mem-cell-p)
				       (:rewrite defexpansion-sub)))
	  :use (
		(:instance defexpansion-generic
			   (gcell (get-cell gvar2 gemmem))
			   (rtmvars rtmvars2))
		(:instance defexpansion-generic
			   (gcell (get-cell gvar3 gemmem))
			   (rtmvars rtmvars3))
		(:instance equal-sub-and-updates-have-values-that-are-sub-lists
			   (rtmvars2 (eventually-make-list rtmvars2 (len *rns*)))
			   (rtmvars3 (eventually-make-list rtmvars3 (len *rns*)))
			   (rns *rns*))
		(:instance equal-sub-and-updates-have-same-attributes
			   (rtmvars2 (eventually-make-list rtmvars2 (len *rns*)))
			   (rtmvars3 (eventually-make-list rtmvars3 (len *rns*)))
			   (rns *rns*))
		(:instance sub-correspondence-by-put-list-h
			   (gval1 (var-value (get-cell gvar2 gemmem)))
			   (gval2 (var-value (get-cell gvar3 gemmem)))
			   (rns *rns*))
		(:instance behaviour-of-sub-and-update-norest
			   (c1 gvar1)
			   (c2 gvar2)
			   (c3 gvar3)
			   (mem gemmem))))))





(in-theory (disable sub-list sub-correspondence-by-put-list
		    sub-correspondence-by-put-list-h
		    sub-correspondence-by-put-list-2-fin
		    equal-sub-and-updates-have-same-attributes
		    equal-sub-and-updates-have-values-that-are-sub-lists
		    behaviour-of-sub-and-update-norest
		    defexpansion
		    if-a-var-value-is-same-then-var-values-are-list-of
		    if-a-var-attribute-is-same-then-var-attributes-are-list-of
		    defexpansion-generic-bool
		    defexpansion-generic-int
		    defexpansion-generic
		    defexpansion-bool-values-inv
		    defexpansion-bool-values
		    defexpansion-bool-attrs-inv
		    defexpansion-bool-attrs-inv-1
		    defexpansion-bool-attrs-inv-2
		    defexpansion-bool-attrs
		    defexpansion-bool-attrs-1
		    equal-values-on-list-entails-equality-on-first-els
		    ))





(defun execute-n-rtm-subs (st n)
  (if
      (zp n)
      st
    (execute-n-rtm-subs
     (rtm-sub
      (par1 (nth (pcc st) (code st)))
      (par2 (nth (pcc st) (code st)))
      (par3 (nth (pcc st) (code st)))
      (par4 (nth (pcc st) (code st)))
     st)
     (1- n))))


(defthm all-rtm-subs-means-only-subs-are-executed
 (implies
  (all-rtm-subs-for-n-steps st n)
  (equal
   (execute-n-rtm-subs st n)
   (execute-n-instructions st n)))
 :hints (("Goal" :in-theory (disable rtm-sub member-equal nth par1 par2 par3))))


(defun subs-list-n (l1 l2 l3 l4 mem n)
  (if (zp n)
      mem
    (subs-list-n (cdr l1) (cdr l2) (cdr l3) (cdr l4)
	       (put-cell
		(car l1)
		(sub-and-update
		 (car l1)
		 (car l2)
		 (car l3)
		 (car l4)
		 mem)
		mem)
	       (1- n))))







(in-theory (disable member-equal))


(in-theory (enable make-cell))



(defthm execute-n-rtm-subs-tantamount-to-sub-list-n
 (implies
  (and
   (all-rtm-subs-for-n-steps st n)
   (>= (pcc st) 0)
   (rtm-statep st))
  (equal
   (mem (execute-n-rtm-subs st n))
   (subs-list-n
    (listpars1 st n)
    (listpars2 st n)
    (listpars3 st n)
    (listpars4 st n)
    (mem st)
    n)))
 :hints
	 (("Goal" :induct t )
	  ("Subgoal *1/2.2" :in-theory '((:definition all-rtm-subs-for-n-steps)
					 (:definition execute-instruction)
					 (:definition rtm-sub)
					 (:definition make-state)
					 (:definition mem))
	   )
	  ("Subgoal *1/2"
		   :use ( execute-n-rtm-subs
			  (:instance subs-list-n
				     (l1 (listpars1 st n))
				     (l2 (listpars2 st n))
				     (l3 (listpars3 st n))
				     (l4 (listpars4 st n))
				     (mem (mem st)))
			  lemma12-lp1r lemma12-lp2r lemma12-lp3r lemma12-lp4r
			  (:theorem
			   (IMPLIES (AND (ALL-RTM-SUBS-FOR-N-STEPS ST N)
					 (>= (pcc st) 0)
					 (not (zp n)))
				    (equal (mem (execute-instruction st))
					   (PUT-CELL (CAR (LISTPARS1 ST N))
						     (SUB-AND-UPDATE (CAR (LISTPARS1 ST N))
								     (CAR (LISTPARS2 ST N))
								     (CAR (LISTPARS3 ST N))
								     (CAR (LISTPARS4 ST N))
								     (MEM ST))
						     (MEM ST)))))
			  executing-rtm-instruction-retrieves-a-rtm-state-from-rtm-state
			  instruction-incrementing-pvv))))


(in-theory (disable lemma12-lp1r  lemma12-lp2r lemma12-lp3r lemma12-lp4r ))










(defun subs-list-e (c1 c2 c3 c4 mem)
  (if
      (endp c1)
      mem
    (subs-list-e
     (cdr c1)
     (cdr c2)
     (cdr c3)
     (cdr c4)
     (put-cell (car c1) (sub-and-update (car c1) (car c2) (car c3) (car c4) mem) mem))))



(defthm subs-list-e-is-subs-list-n
  (equal (subs-list-e c1 c2 c3 c4 mem) (subs-list-n c1 c2 c3 c4 mem (len c1)))
  :rule-classes nil)



(defthm execute-n-instructions-tantamount-to-sub-list-e
 (implies
  (and
   (integerp n)
   (>= n 0)
   (all-rtm-subs-for-n-steps st n)
   (>= (pcc st) 0)
   (rtm-statep st))
  (equal
   (mem (execute-n-instructions st n))
   (subs-list-e
    (listpars1 st n)
    (listpars2 st n)
    (listpars3 st n)
    (listpars4 st n)
    (mem st))))
 :hints (("Goal" :in-theory nil
	  :use ((:instance subs-list-e-is-subs-list-n
			   (c1 (listpars1 st n))
			   (c2 (listpars2 st n))
			   (c3 (listpars3 st n))
			   (c4 (listpars4 st n))
			   (mem (mem st)))
		execute-n-rtm-subs-tantamount-to-sub-list-n
		all-rtm-subs-means-only-subs-are-executed
		length-of-listpars1-n-is-n))))










(defthm not-in-list-untouched-by-subs-list-e
  (implies
   (not (member-equal-bool v l1))
   (equal (get-cell v (subs-list-e l1 l2 l3 l4 mem)) (get-cell v mem)))
  :hints (("Goal" :in-theory (disable sub-and-update))))

(defthm not-in-list-untouched-by-subs-list-e-1
  (implies
   (not (member-equal-bool (car l1) (cdr l1)))
   (equal (get-cell (car l1) (subs-list-e (cdr l1) (cdr l2) (cdr l3) (cdr l4) mem))
	  (get-cell (car l1) mem))))


(defthm sub-and-update-independent-from-firstbn
 (implies
  (and
   (not (member-equal-bool (nth idx l1) (firstn idx l1)))
   (not (member-equal-bool (nth idx l2) (firstn idx l1)))
   (not (member-equal-bool (nth idx l3) (firstn idx l1))))
  (equal (sub-and-update
	  (nth idx l1)
	  (nth idx l2)
	  (nth idx l3)
	  (nth idx l4)
	  (subs-list-e (firstn idx l1) (firstn idx l2) (firstn idx l3) (firstn idx l4) mem))
	 (sub-and-update
	  (nth idx l1)
	  (nth idx l2)
	  (nth idx l3)
	  (nth idx l4)
	  mem))))



(defthm subs-list-decomp
 (implies
  (and
   (in-range idx l1)
   (in-range idx l2)
   (in-range idx l3)
   (in-range idx l4))
  (equal
   (subs-list-e l1 l2 l3 l4 mem)
   (subs-list-e (nthcdr idx l1) (nthcdr idx l2) (nthcdr idx l3) (nthcdr idx l4)
		(subs-list-e (firstn idx l1) (firstn idx l2) (firstn idx l3) (firstn idx l4) mem))))
 :hints (("Goal" :in-theory (disable sub-and-update))))


(defthm if-el-does-not-appear-after-its-position-then-subs-list-e-produces-its-sub
 (implies
  (and
   (not (member-equal-bool (nth idx l1) (cdr (nthcdr idx l1))))
   (in-range idx l1)
   (in-range idx l2)
   (in-range idx l3)
   (in-range idx l4))
  (equal
   (get-cell (nth idx l1) (subs-list-e l1 l2 l3 l4 mem))
   (sub-and-update
     (nth idx l1)
     (nth idx l2)
     (nth idx l3)
     (nth idx l4)
     (subs-list-e (firstn idx l1) (firstn idx l2) (firstn idx l3) (firstn idx l4) mem))))
  :hints (("Goal" :in-theory (disable sub-and-update))))




(defthm rtm-variable-of-subs-list-e-is-sub-of-correspondent-variables
  (implies
   (and
    (positive-list rns)
    (true-listp ll)
    (no-duplicates-p (append-lists ll))
    (in-range gem1 ll)
    (in-range gem2 ll)
    (in-range gem3 ll)
    (in-range idx (nth gem1 ll))
    (in-range idx (nth gem2 ll))
    (in-range idx (nth gem3 ll))
    (in-range idx rns))
   (equal
    (get-cell (nth idx (nth gem1 ll)) (subs-list-e (nth gem1 ll) (nth gem2 ll) (nth gem3 ll) rns mem))
    (sub-and-update (nth idx (nth gem1 ll)) (nth idx (nth gem2 ll)) (nth idx (nth gem3 ll)) (nth idx rns) mem)))
  :hints (("Goal" :in-theory (disable sub-and-update)
	   :use (
		 (:instance no-duplicates-all-implies-no-duplicates-one (idx1 gem1))
		 (:instance no-duplicates-means-an-element-does-not-appear-after-its-position (l (nth gem1 ll)))
		 if-el-does-not-appear-after-its-position-then-subs-list-e-produces-its-sub
		 (:instance subs-list-decomp
			    (l1 (nth gem1 ll)) (l2 (nth gem2 ll)) (l3 (nth gem3 ll)))
		 (:instance sub-and-update-independent-from-firstbn
			    (l1 (nth gem1 ll)) (l2 (nth gem2 ll)) (l3 (nth gem3 ll)))))))



(defun index-different-sub-and-updates (rtmvarsres rtmvars1 rtmvars2 rtmvars3 rns mem mem-after-sub)
  (cond
   ( (endp rtmvarsres)
     0 )
   ( (not (equal (get-cell (car rtmvarsres) mem-after-sub)
		 (sub-and-update (car rtmvars1) (car rtmvars2) (car rtmvars3) (car rns) mem)))
     0 )
   ( t
     (1+ (index-different-sub-and-updates
	  (cdr rtmvarsres)
	  (cdr rtmvars1)
	  (cdr rtmvars2)
	  (cdr rtmvars3)
	  (cdr rns)
	  mem
	  mem-after-sub)))))

(defthm if-bad-index-in-range-thne-must-be-nonsubandupdate
  (let ((bad-idx (index-different-sub-and-updates rtmvarsres rtmvars1 rtmvars2 rtmvars3 rns mem mem-after-sub)))
    (implies
     (in-range bad-idx rtmvarsres)
     (not (equal
	   (get-cell (nth bad-idx rtmvarsres) mem-after-sub)
           (sub-and-update
	    (nth bad-idx rtmvars1)
	    (nth bad-idx rtmvars2)
	    (nth bad-idx rtmvars3)
	    (nth bad-idx rns)
	    mem)))))
 :hints (("Goal" :in-theory (disable get-cell sub-and-update))))


(defthm if-bad-index-not-in-range-then-every-equalsubandupdate
  (let ((bad-idx (index-different-sub-and-updates rtmvarsres rtmvars1 rtmvars2 rtmvars3 rns mem mem-after-sub)))
    (implies (and (true-listp rtmvarsres)
		  (not (in-range bad-idx rtmvarsres)))
	  (equal-sub-and-updates rtmvarsres rtmvars1 rtmvars2 rtmvars3 rns mem mem-after-sub))))


(defthm rtm-variable-of-subs-list-e-is-sub-and-updates
  (implies
   (and
    (positive-list rns)
    (true-listp ll)
    (no-duplicates-p (append-lists ll))
    (equal (len (nth gem1 ll)) (len (nth gem2 ll)))
    (equal (len (nth gem1 ll)) (len (nth gem3 ll)))
    (equal (len (nth gem1 ll)) (len rns))
    (in-range gem1 ll)
    (in-range gem2 ll)
    (in-range gem3 ll)
    (true-listp (nth gem1 ll)))
   (equal-sub-and-updates (nth gem1 ll) (nth gem1 ll) (nth gem2 ll) (nth gem3 ll) rns mem
    (subs-list-e (nth gem1 ll) (nth gem2 ll) (nth gem3 ll) rns mem)))
  :hints (("Goal" :use (:instance rtm-variable-of-subs-list-e-is-sub-of-correspondent-variables
				  (idx (index-different-sub-and-updates
					(nth gem1 ll)
					(nth gem1 ll)
					(nth gem2 ll)
					(nth gem3 ll)
					rns
					mem
					(subs-list-e (nth gem1 ll) (nth gem2 ll) (nth gem3 ll) rns mem)))))
	  ("Goal'" :cases ( (in-range (index-different-sub-and-updates
				      (nth gem1 ll)
				      (nth gem1 ll)
				      (nth gem2 ll)
				      (nth gem3 ll)
				      rns
				      mem
				      (subs-list-e (nth gem1 ll) (nth gem2 ll) (nth gem3 ll) rns mem))
				     (nth gem1 ll)) ) )
	  ("Subgoal 1" :in-theory '((:definition in-range)
				    (:rewrite if-bad-index-in-range-thne-must-be-nonsubandupdate)))
	  ("Subgoal 2" :in-theory '((:rewrite if-bad-index-not-in-range-then-every-equalsubandupdate)))))




(defthm any-element-of-make-list-does-not-appear-into-other-lists
 (implies
  (and
   (integerp n)
   (true-listp ll)
   (no-duplicates-p (append-lists ll))
   (in-range gem1 ll)
   (in-range gem2 ll)
   (not (equal gem1 gem2))
   (equal (len (nth gem1 ll)) 1)
   (in-range idx (make-n-list (car (nth gem1 ll)) n)))
  (not (member-equal-bool
	(nth idx (make-n-list (car (nth gem1 ll)) n))
	(nth gem2 ll))))
 :hints (("Goal" :use
	  (
	   (:instance
	    el-of-makelist-is-el
	    (el (car (nth gem1 ll))))
	   (:instance generalized-disjunctivity-unordered-2
		      (idx1 gem1) (idx2 gem2) (el1 (car (nth gem1 ll)))))))
 :otf-flg t)

(defthm firstns-do-not-cotain-el-of-make-n-list-if-diff
 (implies
  (and
   (integerp n)
   (true-listp ll)
   (no-duplicates-p (append-lists ll))
   (in-range gem1 ll)
   (in-range gem2 ll)
   (not (equal gem1 gem2))
   (equal (len (nth gem1 ll)) 1)
   (in-range idx (make-n-list (car (nth gem1 ll)) n)))
  (not (member-equal-bool
	(nth idx (make-n-list (car (nth gem1 ll)) n))
	(firstn idx (nth gem2 ll)))))
 :hints (("Goal" :use
	  (
	   (:instance no-member-holds-on-firstn
		      (el (nth idx (make-n-list (car (nth gem1 ll)) n)))
		      (l (nth gem2 ll)))
	   any-element-of-make-list-does-not-appear-into-other-lists))))



(defthm rtm-variable-of-subs-list-e-is-sub-of-correspondent-variables-when-var-3-is-boolean
  (implies
   (and
    (integerp n)
    (positive-list rns)
    (true-listp ll)
    (no-duplicates-p (append-lists ll))
    (in-range gem1 ll)
    (in-range gem2 ll)
    (in-range gem3 ll)
    (not (equal gem1 gem3))
    (equal (len (nth gem3 ll)) 1)
    (in-range idx (nth gem1 ll))
    (in-range idx (nth gem2 ll))
    (in-range idx (make-n-list (car (nth gem3 ll)) n))
    (in-range idx rns))
   (equal
    (get-cell (nth idx (nth gem1 ll))
	      (subs-list-e
	       (nth gem1 ll)
	       (nth gem2 ll)
	       (make-n-list (car (nth gem3 ll)) n)
	       rns mem))
    (sub-and-update
     (nth idx (nth gem1 ll))
     (nth idx (nth gem2 ll))
     (nth idx (make-n-list (car (nth gem3 ll)) n))
     (nth idx rns) mem)))
  :hints (("Goal" :in-theory (disable sub-and-update)
	   :use (
		 (:instance firstns-do-not-cotain-el-of-make-n-list-if-diff (gem1 gem3) (gem2 gem1))
		 (:instance no-duplicates-all-implies-no-duplicates-one (idx1 gem1))
		 (:instance no-duplicates-means-an-element-does-not-appear-after-its-position (l (nth gem1 ll)))
		 (:instance subs-list-decomp
			    (l1 (nth gem1 ll))
			    (l2 (nth gem2 ll))
			    (l3 (make-n-list (car (nth gem3 ll)) n))
			    (l4 rns))
		 (:instance sub-and-update-independent-from-firstbn
			    (l1 (nth gem1 ll))
			    (l2 (nth gem2 ll))
			    (l3 (make-n-list (car (nth gem3 ll)) n))
			    (l4 rns))))))

(defthm rtm-variable-of-subs-list-e-is-sub-of-correspondent-variables-when-var-2-is-boolean
  (implies
   (and
    (integerp n)
    (positive-list rns)
    (true-listp ll)
    (no-duplicates-p (append-lists ll))
    (in-range gem1 ll)
    (in-range gem2 ll)
    (in-range gem3 ll)
    (not (equal gem1 gem2))
    (equal (len (nth gem2 ll)) 1)
    (in-range idx (nth gem1 ll))
    (in-range idx (nth gem3 ll))
    (in-range idx (make-n-list (car (nth gem2 ll)) n))
    (in-range idx rns))
   (equal
    (get-cell (nth idx (nth gem1 ll))
	      (subs-list-e
	       (nth gem1 ll)
	       (make-n-list (car (nth gem2 ll)) n)
	       (nth gem3 ll)
	       rns mem))
    (sub-and-update
     (nth idx (nth gem1 ll))
     (nth idx (make-n-list (car (nth gem2 ll)) n))
     (nth idx (nth gem3 ll))
     (nth idx rns) mem)))
  :hints (("Goal" :in-theory (disable sub-and-update)
	   :use (
		 (:instance firstns-do-not-cotain-el-of-make-n-list-if-diff (gem1 gem2) (gem2 gem1))
		 (:instance no-duplicates-all-implies-no-duplicates-one (idx1 gem1))
		 (:instance no-duplicates-means-an-element-does-not-appear-after-its-position (l (nth gem1 ll)))
		 (:instance subs-list-decomp
			    (l1 (nth gem1 ll))
			    (l2 (make-n-list (car (nth gem2 ll)) n))
			    (l3 (nth gem3 ll))
			    (l4 rns))
		 (:instance sub-and-update-independent-from-firstbn
			    (l1 (nth gem1 ll))
			    (l2 (make-n-list (car (nth gem2 ll)) n))
			    (l3 (nth gem3 ll))
			    (l4 rns))))))

(defthm rtm-variable-of-subs-list-e-is-sub-of-correspondent-variables-when-var-2and3-are-boolean
  (implies
   (and
    (integerp n)
    (positive-list rns)
    (true-listp ll)
    (no-duplicates-p (append-lists ll))
    (in-range gem1 ll)
    (in-range gem2 ll)
    (in-range gem3 ll)
    (not (equal gem1 gem2))
    (not (equal gem1 gem3))
    (equal (len (nth gem2 ll)) 1)
    (equal (len (nth gem3 ll)) 1)
    (in-range idx (nth gem1 ll))
    (in-range idx (make-n-list (car (nth gem2 ll)) n))
    (in-range idx (make-n-list (car (nth gem3 ll)) n))
    (in-range idx rns))
   (equal
    (get-cell (nth idx (nth gem1 ll))
	      (subs-list-e
	       (nth gem1 ll)
	       (make-n-list (car (nth gem2 ll)) n)
	       (make-n-list (car (nth gem3 ll)) n)
	       rns mem))
    (sub-and-update
     (nth idx (nth gem1 ll))
     (nth idx (make-n-list (car (nth gem2 ll)) n))
     (nth idx (make-n-list (car (nth gem3 ll)) n))
     (nth idx rns) mem)))
  :hints (("Goal" :in-theory (disable sub-and-update)
	   :use (
		 (:instance firstns-do-not-cotain-el-of-make-n-list-if-diff (gem1 gem2) (gem2 gem1))
		 (:instance firstns-do-not-cotain-el-of-make-n-list-if-diff (gem1 gem3) (gem2 gem1))
		 (:instance no-duplicates-all-implies-no-duplicates-one (idx1 gem1))
		 (:instance no-duplicates-means-an-element-does-not-appear-after-its-position (l (nth gem1 ll)))
		 (:instance subs-list-decomp
			    (l1 (nth gem1 ll))
			    (l2 (make-n-list (car (nth gem2 ll)) n))
			    (l3 (make-n-list (car (nth gem3 ll)) n))
			    (l4 rns))
		 (:instance sub-and-update-independent-from-firstbn
			    (l1 (nth gem1 ll))
			    (l2 (make-n-list (car (nth gem2 ll)) n))
			    (l3 (make-n-list (car (nth gem3 ll)) n))
			    (l4 rns))))))




(defthm rtm-variable-of-subs-list-e-is-sub-of-correspondent-variables-with-all-vars-types
  (implies
   (and
    (integerp n)
    (positive-list rns)
    (true-listp ll)
    (no-duplicates-p (append-lists ll))
    (in-range gem1 ll)
    (in-range gem2 ll)
    (in-range gem3 ll)
    (not (equal (len (nth gem1 ll)) 1))
    (in-range idx (nth gem1 ll))
    (in-range idx (eventually-make-list (nth gem2 ll) n))
    (in-range idx (eventually-make-list (nth gem3 ll) n))
    (in-range idx rns))
   (equal
    (get-cell (nth idx (nth gem1 ll))
	      (subs-list-e
	       (nth gem1 ll)
	       (eventually-make-list (nth gem2 ll) n)
	       (eventually-make-list (nth gem3 ll) n)
	       rns mem))
    (sub-and-update
     (nth idx (nth gem1 ll))
     (nth idx (eventually-make-list (nth gem2 ll) n))
     (nth idx (eventually-make-list (nth gem3 ll) n))
     (nth idx rns) mem)))
  :hints (("Goal" :in-theory (union-theories (current-theory 'ground-zero)
						  '((:definition eventually-make-list)))
	  :cases
	   ( (and (not (equal (len (nth gem3 ll)) 1))      (equal (len (nth gem2 ll)) 1))
	     (and      (equal (len (nth gem3 ll)) 1)  (not (equal (len (nth gem2 ll)) 1)))
	     (and (not (equal (len (nth gem3 ll)) 1)) (not (equal (len (nth gem2 ll)) 1)))
	     (and      (equal (len (nth gem3 ll)) 1)       (equal (len (nth gem2 ll)) 1))))
	  ("Subgoal 4"
	   :use rtm-variable-of-subs-list-e-is-sub-of-correspondent-variables-when-var-2-is-boolean)
	  ("Subgoal 3"
	   :use rtm-variable-of-subs-list-e-is-sub-of-correspondent-variables-when-var-3-is-boolean)
	  ("Subgoal 2"
	   :use rtm-variable-of-subs-list-e-is-sub-of-correspondent-variables)
	  ("Subgoal 1"
	   :use rtm-variable-of-subs-list-e-is-sub-of-correspondent-variables-when-var-2and3-are-boolean)))



(defthm sub-and-updates-holding-for-every-variable-type
  (implies
   (and
    (integerp n)
    (not (equal (len (nth gem1 ll)) 1))
    (positive-list rns)
    (true-listp ll)
    (no-duplicates-p (append-lists ll))
    (equal (len (nth gem1 ll)) (len (eventually-make-list (nth gem2 ll) n)))
    (equal (len (nth gem1 ll)) (len (eventually-make-list (nth gem3 ll) n)))
    (equal (len (nth gem1 ll)) (len rns))
    (in-range gem1 ll)
    (in-range gem2 ll)
    (in-range gem3 ll)
    (true-listp (nth gem1 ll)))
   (equal-sub-and-updates
    (nth gem1 ll)
    (nth gem1 ll)
    (eventually-make-list (nth gem2 ll) n)
    (eventually-make-list (nth gem3 ll) n)
    rns mem
    (subs-list-e
     (nth gem1 ll)
     (eventually-make-list (nth gem2 ll) n)
     (eventually-make-list (nth gem3 ll) n)
     rns mem)))
  :hints (("Goal" :use (:instance rtm-variable-of-subs-list-e-is-sub-of-correspondent-variables-with-all-vars-types
				  (idx (index-different-sub-and-updates
					(nth gem1 ll)
					(nth gem1 ll)
					(eventually-make-list (nth gem2 ll) n)
					(eventually-make-list (nth gem3 ll) n)
					rns
					mem
					(subs-list-e
					 (nth gem1 ll)
					 (eventually-make-list (nth gem2 ll) n)
					 (eventually-make-list (nth gem3 ll) n)
					 rns mem)))))
	  ("Goal'" :cases ( (in-range (index-different-sub-and-updates
				      (nth gem1 ll)
				      (nth gem1 ll)
				      (eventually-make-list (nth gem2 ll) n)
				      (eventually-make-list (nth gem3 ll) n)
				      rns
				      mem
				      (subs-list-e
				       (nth gem1 ll)
				       (eventually-make-list (nth gem2 ll) n)
				       (eventually-make-list (nth gem3 ll) n)
				       rns mem))
				     (nth gem1 ll)) ) )
	  ("Subgoal 1" :in-theory '((:definition in-range)
		       		    (:rewrite if-bad-index-in-range-thne-must-be-nonsubandupdate)))
	  ("Subgoal 2" :in-theory '((:rewrite if-bad-index-not-in-range-then-every-equalsubandupdate)))))



(defthm lemma2-only-subs-in-rtm-sub
  (implies
   (and
    (gem-statep gstate)
    (rtm-statep rstate)
    (in-range (pcc gstate) (code gstate))
    (in-range (pcc rstate) (code rstate))
    (equal (opcode (nth (pcc gstate) (code gstate))) 'gem-sub)
    (good-translation-gem-rtm gstate rstate m))
   (all-rtm-subs-for-n-steps rstate (len *rns*)))
  :hints (("Goal" :expand
	   ( (good-translation-gem-rtm gstate rstate m)
	     (gem-statep gstate)
	     (rtm-statep rstate)
	     (in-range (pcc gstate) (code gstate))
	     (in-range (pcc rstate) (code rstate)))
	   :in-theory nil))
  :rule-classes nil)


(defthm cells-untouched-by-execute-on-other-cell-sub
 (implies
  (and
   (integerp n)
   (>= n 0)
   (all-rtm-subs-for-n-steps st n)
   (>= (pcc st) 0)
   (rtm-statep st)
   (not (member-equal-bool v (listpars1 st n))))
  (equal (get-cell v (mem st))
	 (get-cell v (mem (execute-n-instructions st n)))))
 :hints (("Goal"
	  :use (execute-n-instructions-tantamount-to-sub-list-e
		(:instance not-in-list-untouched-by-subs-list-e
				  (v v)
				  (l1 (listpars1 st n))
				  (l2 (listpars2 st n))
				  (l3 (listpars3 st n))
				  (l4 (listpars4 st n))
				  (mem (mem st)))))))


(defthm rtm-variable-of-other-cell-untouched-sub
  (implies
   (and
    (equal (opcode (nth (pcc gstate) (code gstate))) 'gem-sub)
    (>= (pcc rstate) 0)
    (rtm-statep rstate)
    (good-translation-gem-rtm gstate rstate m)
    (in-range (pcc gstate) (code gstate))
    (assoc-equal (par1 (nth (pcc gstate) (code gstate))) m)
    (true-listp m)
    (no-duplicates-p (append-lists (retrieve-rtmvars m)))
    (assoc-equal gvar1 m)
    (not (equal gvar1 (par1 (nth (pcc gstate) (code gstate)))))
    (in-range idx1 (rtmintvars-i gvar1 m)))
   (equal (get-cell (nth idx1 (rtmintvars-i gvar1 m)) (mem rstate))
	  (get-cell (nth idx1 (rtmintvars-i gvar1 m)) (mem (execute-n-instructions rstate (len *rns*))))))
  :hints (("Goal" :in-theory (current-theory 'ground-zero)
	   :expand (     (in-range (pcc gstate) (code gstate))
			 (good-translation-gem-rtm gstate rstate m) )
	   :use (
		 (:instance lemma1-different-vars-do-not-belong  (gvar2 (par1 (nth (pcc gstate) (code gstate)))))
		 (:instance cells-untouched-by-execute-on-other-cell-sub (st rstate) (n (len *rns*))
			    (v (nth idx1 (rtmintvars-i gvar1 m))))))))

(defthm rtm-variables-of-other-cell-untouched-sub
  (implies
   (and
    (equal (opcode (nth (pcc gstate) (code gstate))) 'gem-sub)
    (>= (pcc rstate) 0)
    (rtm-statep rstate)
    (good-translation-gem-rtm gstate rstate m)
    (in-range (pcc gstate) (code gstate))
    (assoc-equal (par1 (nth (pcc gstate) (code gstate))) m)
    (true-listp m)
    (no-duplicates-p (append-lists (retrieve-rtmvars m)))
    (assoc-equal gvar1 m)
    (true-listp (rtmintvars-i gvar1 m))
    (not (equal gvar1 (par1 (nth (pcc gstate) (code gstate))))))
   (equal-get-cells
          (rtmintvars-i gvar1 m) (mem rstate) (mem (execute-n-instructions rstate (len *rns*)))))
  :hints (("Goal" :in-theory nil
	   :use ( (:instance rtm-variable-of-other-cell-untouched-sub
			     (idx1 (idx-different-cell
				    (rtmintvars-i gvar1 m)
				    (mem rstate)
				    (mem (execute-n-instructions rstate (len *rns*)))))) ))
	  ("Goal'" :cases ( (in-range
			     (idx-different-cell
				    (rtmintvars-i gvar1 m)
				    (mem rstate)
				    (mem (execute-n-instructions rstate (len *rns*))))
			     (rtmintvars-i gvar1 m))))
	  ("Subgoal 2" :in-theory '((:rewrite if-bad-index-not-in-range-then-every-equal)))
	  ("Subgoal 1" :in-theory '((:forward-chaining if-bad-index-in-range-then-cells-must-be-different)))))




(defthm properies-of-type-and-existence-of-current-args-sub
 (implies
  (and
   (gem-statep gstate)
   (in-range (pcc gstate) (code gstate))
   (equal (opcode (nth (pcc gstate) (code gstate))) 'gem-sub))
  (and
   (equal (var-type (get-cell (par1 (nth (pcc gstate) (code gstate))) (mem gstate))) 'Int)
   (assoc-equal (par1 (nth (pcc gstate) (code gstate))) (mem gstate))
   (assoc-equal (par2 (nth (pcc gstate) (code gstate))) (mem gstate))
   (assoc-equal (par3 (nth (pcc gstate) (code gstate))) (mem gstate))))
  :hints (("Goal" :in-theory (enable get-cell)
	   :use (:instance in-range-instruction-is-gem-instruction
			   (pcc (pcc gstate))
			   (code (code gstate))
			   (mem (mem gstate)))))
  :rule-classes nil)


(defthm par1-of-current-instruction-is-into-mapping-sub
 (implies
  (and
   (vars-inclusion (mem gstate) m)
   (gem-statep gstate)
   (equal (opcode (nth (pcc gstate) (code gstate))) 'gem-sub)
   (in-range (pcc gstate) (code gstate)))
  (assoc-equal (par1 (nth (pcc gstate) (code gstate))) m))
 :hints (("Goal" :in-theory (enable get-cell)
	 :use (properies-of-type-and-existence-of-current-args-sub
	       (:instance inclusion-trans
			  (v (par1 (nth (pcc gstate) (code gstate))))
			  (m1 (mem gstate))
			  (m2 m))
	       (:instance in-range-instruction-is-gem-instruction
				 (pcc (pcc gstate))
				 (code (code gstate))
				 (mem (mem gstate)))))))



(defthm teorema-main-con-pcc-in-range-su-variabile-non-interessata-final-sub
 (implies
  (and
   (equal (opcode (nth (pcc gstate) (code gstate))) 'gem-sub)
   (good-translation-gem-rtm gstate rstate m)
   (vars-inclusion (mem gstate) m)
   (true-listp m)
   (assoc-equal gvar1 m)
   (gem-statep gstate)
   (rtm-statep rstate)
   (in-range (pcc gstate) (code gstate))
   (in-range (pcc rstate) (code rstate))
   (not (equal gvar1 (par1 (nth (pcc gstate) (code gstate)))))
   (m-correspondent-values-p m (mem gstate) (mem rstate))
   (no-duplicates-p (append-lists (retrieve-rtmvars m)))
   (correct-wrt-arity m (mem gstate)))
  (equal-values-and-attributes
   (get-cell gvar1 (mem (execute-instruction gstate)))
   (rtmintvars-i gvar1 m)
   (mem (execute-n-instructions rstate (len *rns*)))
   (type-i gvar1 m)))
 :hints (("Goal"
	  :in-theory '((:definition good-translation-gem-rtm))
	  :use (
		par1-of-current-instruction-is-into-mapping-sub
		(:instance correct-wrt-arity-has-rtmintvars-i-tl (mem (mem gstate)))
		(:instance m-correspondent-values-implies-equal-values-and-attribus
			   (memgstate (mem gstate)) (memrstate (mem rstate)))
		(:instance in-range (idx (pcc gstate)) (l (code gstate)))
		(:instance in-range (idx (pcc rstate)) (l (code rstate)))
		rtm-variables-of-other-cell-untouched-sub
		teorema-main-con-pcc-in-range-su-variabile-non-interessata
		(:instance equal-get-cells-implies-equal-values-and-attributes-still-works
			   (gemcell (get-cell gvar1 (mem gstate)))
			   (lcell (rtmintvars-i gvar1 m))
			   (mem1 (mem rstate))
			   (mem2 (mem (execute-n-instructions rstate (len *rns*))))
			   (type (type-i gvar1 m)))))))


(defthm teorema-main-con-pcc-in-range-su-variabile-interessata-sub
 (implies
  (and
   (gem-statep gstate)
   (rtm-statep rstate)
   (in-range (pcc gstate) (code gstate))
   (in-range (pcc rstate) (code rstate))
   (equal (opcode (nth (pcc gstate) (code gstate))) 'gem-sub)
   (good-translation-gem-rtm gstate rstate m))
  (equal
   (mem (execute-n-instructions rstate (len *rns*)))
   (subs-list-e
    (rtmintvars-i (par1 (nth (pcc gstate) (code gstate))) m)
    (eventually-make-list (rtmintvars-i (par2 (nth (pcc gstate) (code gstate))) m) (len *rns*)) ;new
    (eventually-make-list (rtmintvars-i (par3 (nth (pcc gstate) (code gstate))) m) (len *rns*)) ;new
    *rns*
    (mem rstate))))
  :hints (("Goal"
	   :in-theory (union-theories (current-theory 'ground-zero) '((:definition in-range)))
	   :use (good-translation-gem-rtm
		 lemma2-only-subs-in-rtm-sub
		 (:instance execute-n-instructions-tantamount-to-sub-list-e
			    (n (len *rns*))
			    (st rstate)))))
  :rule-classes nil)




(defthm posinrg-sub
  (implies
   (and
    (vars-inclusion (mem gstate) m)
    (gem-statep gstate)
    (equal (opcode (nth (pcc gstate) (code gstate))) 'gem-sub)
    (in-range (pcc gstate) (code gstate)))
   (and
    (in-range (pos-equal-0 (par1 (nth (pcc gstate) (code gstate))) m) m)
    (in-range (pos-equal-0 (par2 (nth (pcc gstate) (code gstate))) m) m)
    (in-range (pos-equal-0 (par3 (nth (pcc gstate) (code gstate))) m) m)))
   :hints (("Goal"
	    :use (properies-of-type-and-existence-of-current-args-sub
			(:instance inclusion-trans (m1 (mem gstate)) (m2 m)
				   (v (par1 (nth (pcc gstate) (code gstate)))))
			(:instance inclusion-trans (m1 (mem gstate)) (m2 m)
				   (v (par2 (nth (pcc gstate) (code gstate)))))
			(:instance inclusion-trans (m1 (mem gstate)) (m2 m)
				   (v (par3 (nth (pcc gstate) (code gstate)))))
			(:instance assoc-means-pos-in-range
				   (el (par1 (nth (pcc gstate) (code gstate))))
				   (l m))
			(:instance assoc-means-pos-in-range
				   (el (par2 (nth (pcc gstate) (code gstate))))
				   (l m))
			(:instance assoc-means-pos-in-range
				   (el (par3 (nth (pcc gstate) (code gstate))))
				   (l m)))))
   :rule-classes nil)

(defthm eqlenss-sub
  (implies
   (and
    (gem-statep gstate)
    (rtm-statep rstate)
    (in-range (pcc gstate) (code gstate))
    (in-range (pcc rstate) (code rstate))
    (equal (opcode (nth (pcc gstate) (code gstate))) 'gem-sub)
    (good-translation-gem-rtm gstate rstate m))
   (and
    (equal (len (rtmintvars-i (par1 (nth (pcc gstate) (code gstate))) m)) (len *rns*))
    (equal (len (eventually-make-list (rtmintvars-i (par2 (nth (pcc gstate) (code gstate))) m) (len *rns*))) (len *rns*))
    (equal (len (eventually-make-list (rtmintvars-i (par3 (nth (pcc gstate) (code gstate))) m) (len *rns*))) (len *rns*))))
  :hints (("Goal"
	   :in-theory (union-theories (current-theory 'ground-zero) '((:definition in-range)))
	   :use
	   (
	    good-translation-gem-rtm
	    (:instance length-of-listpars1-n-is-n (st rstate) (n (len *rns*)))
	    (:instance length-of-listpars2-n-is-n (st rstate) (n (len *rns*)))
	    (:instance length-of-listpars3-n-is-n (st rstate) (n (len *rns*))))))
  :rule-classes nil)


(defthm equal-sub-and-updates-after-n-instr
  (implies
   (and
    (true-listp m)
    (correct-wrt-arity m (mem gstate))
    (gem-statep gstate)
    (rtm-statep rstate)
    (vars-inclusion (mem gstate) m)
    (in-range (pcc gstate) (code gstate))
    (in-range (pcc rstate) (code rstate))
    (equal (opcode (nth (pcc gstate) (code gstate))) 'gem-sub)
    (good-translation-gem-rtm gstate rstate m)
    (no-duplicates-p (append-lists (retrieve-rtmvars m)))
    (assoc-equal gvar1 m)
    (equal gvar1 (par1 (nth (pcc gstate) (code gstate)))))
   (equal-sub-and-updates
    (rtmintvars-i gvar1 m)
    (rtmintvars-i (par1 (nth (pcc gstate) (code gstate))) m)
    (eventually-make-list (rtmintvars-i (par2 (nth (pcc gstate) (code gstate))) m) (len *rns*)) ;new
    (eventually-make-list (rtmintvars-i (par3 (nth (pcc gstate) (code gstate))) m) (len *rns*)) ;new
    *rns*
    (mem rstate)
    (mem (execute-n-instructions rstate (len *rns*)))))
  :hints (("Goal"
	   :in-theory (union-theories (current-theory 'ground-zero)
				      '((:type-prescription retrieve-rtmvars)
					(:definition positive-list)
					(:definition positivep)
					(:definition in-range)))
	   :use
	   (
	     (:instance correct-wrt-arity-has-rtmintvars-i-tl (mem (mem gstate)))
	     (:instance sub-and-updates-holding-for-every-variable-type
			(n (len *rns*))
			(ll (retrieve-rtmvars m))
			(rns *rns*)
			(gem1 (pos-equal-0 (par1 (nth (pcc gstate) (code gstate))) m))
			(gem2 (pos-equal-0 (par2 (nth (pcc gstate) (code gstate))) m))
			(gem3 (pos-equal-0 (par3 (nth (pcc gstate) (code gstate))) m))
			(mem (mem rstate)))
	     lemma-help2
	     eqlenss-sub
	     posinrg-sub
	     teorema-main-con-pcc-in-range-su-variabile-interessata-sub
	     (:instance rtmintvars-i-is-pos-equal-0-of-retrieve-vars
			(gvar (par1 (nth (pcc gstate) (code gstate)))))
	     (:instance rtmintvars-i-is-pos-equal-0-of-retrieve-vars
			(gvar (par2 (nth (pcc gstate) (code gstate)))))
	     (:instance rtmintvars-i-is-pos-equal-0-of-retrieve-vars
			(gvar (par3 (nth (pcc gstate) (code gstate)))))
	     (:instance rtmintvars-i-is-pos-equal-0-of-retrieve-vars
			(gvar (par4 (nth (pcc gstate) (code gstate)))))))))


(defthm equal-sub-and-update-norest-afetr-one-instr
  (implies
   (and
    (gem-statep gstate)
    (in-range (pcc gstate) (code gstate))
    (good-translation-gem-rtm gstate rstate m)
    (equal (opcode (nth (pcc gstate) (code gstate))) 'gem-sub)
    (equal gvar1 (par1 (nth (pcc gstate) (code gstate))))
    (equal gvar2 (par2 (nth (pcc gstate) (code gstate))))
    (equal gvar3 (par3 (nth (pcc gstate) (code gstate)))))
   (equal (get-cell gvar1 (mem (execute-instruction gstate)))
	  (sub-and-update-norest gvar1 gvar2 gvar3 (mem gstate))))
  :hints (("Goal" :in-theory (e/d (put-cell get-cell)
				  (par1 par2 par3 par4 opcode pcc code nth gem-instruction-list-p
					gen-eq-update sub-and-update sub-and-update sub-and-update-norest sub-and-update-norest))))
  :rule-classes nil)


(DEFTHM mem-cellity-of-current-gem-args-sub
  (IMPLIES
   (AND (GEM-STATEP GSTATE)
	(equal (opcode (nth (pcc gstate) (code gstate))) 'gem-sub)
	(IN-RANGE (PCC GSTATE) (CODE GSTATE)))
   (AND (is-mem-cell-p (get-cell  (PAR1 (NTH (PCC GSTATE) (CODE GSTATE))) (mem gstate)))
	(is-mem-cell-p (get-cell  (PAR2 (NTH (PCC GSTATE) (CODE GSTATE))) (mem gstate)))
	(is-mem-cell-p (get-cell  (PAR3 (NTH (PCC GSTATE) (CODE GSTATE))) (mem gstate)))))
  :HINTS
  (("Goal"
    :USE
    (:INSTANCE IN-RANGE-INSTRUCTION-IS-GEM-INSTRUCTION
	       (PCC (PCC GSTATE))
	       (CODE (CODE GSTATE))
	       (MEM (MEM GSTATE))))))



(defthm type-is-for-pars-sub
 (implies
   (and
    (true-listp m)
    (vars-inclusion (mem gstate) m)
    (gem-statep gstate)
    (correct-wrt-arity m (mem gstate))
    (equal (opcode (nth (pcc gstate) (code gstate))) 'gem-sub)
    (equal gvar1 (par1 (nth (pcc gstate) (code gstate))))
    (equal gvar2 (par2 (nth (pcc gstate) (code gstate))))
    (equal gvar3 (par3 (nth (pcc gstate) (code gstate))))
    (in-range (pcc gstate) (code gstate)))
   (equal (type-i gvar1 m) 'int))
 :hints (("Goal"
	  :in-theory (disable type-i-is-type-expected rtmintvars-i-is-pos-equal-0-of-retrieve-vars)
	  :use ( properies-of-type-and-existence-of-current-args-sub
		 (:instance type-i-is-vartyper (gvar1 gvar1))
		 (:instance type-i-is-vartyper (gvar1 gvar2))
		 (:instance type-i-is-vartyper (gvar1 gvar3))
		 (:instance inclusion-trans (m1 (mem gstate)) (m2 m)
			    (v (par1 (nth (pcc gstate) (code gstate)))))
		 (:instance inclusion-trans (m1 (mem gstate)) (m2 m)
			    (v (par2 (nth (pcc gstate) (code gstate)))))
		 (:instance inclusion-trans (m1 (mem gstate)) (m2 m)
			    (v (par3 (nth (pcc gstate) (code gstate))))))))
 :rule-classes nil)


(defthm m-correspondence-kept-on-same-gvar-sub
  (implies
   (and
    (good-translation-gem-rtm gstate rstate m)
    (equal (opcode (nth (pcc gstate) (code gstate))) 'gem-sub)
    (equal gvar1 (par1 (nth (pcc gstate) (code gstate))))
    (true-listp m)
    (correct-wrt-arity m (mem gstate))
    (gem-statep gstate)
    (rtm-statep rstate)
    (vars-inclusion (mem gstate) m)
    (in-range (pcc gstate) (code gstate))
    (in-range (pcc rstate) (code rstate))
    (no-duplicates-p (append-lists (retrieve-rtmvars m)))
    (assoc-equal gvar1 m)
    (m-correspondent-values-p m (mem gstate) (mem rstate)))
  (equal-values-and-attributes
   (get-cell gvar1 (mem (execute-instruction gstate)))
   (rtmintvars-i gvar1 m)
   (mem (execute-n-instructions rstate (len *rns*)))
   (type-i gvar1 m)))
  :hints (("Goal"  :in-theory nil
	   :use (
		 properies-of-type-and-existence-of-current-args-sub
		 mem-cellity-of-current-gem-args-sub
		 good-translation-gem-rtm
		 (:instance type-i-is-vartyper (gvar1 gvar1) (mem (mem gstate)))
		 (:instance type-i-is-vartyper (gvar1 (par2 (nth (pcc gstate) (code gstate)))) (mem (mem gstate)))
		 (:instance type-i-is-vartyper (gvar1 (par3 (nth (pcc gstate) (code gstate)))) (mem (mem gstate)))
		 (:instance type-i-is-type-expected (gvar  gvar1) (mem (mem gstate)))
		 (:instance type-i-is-type-expected (gvar  (par2 (nth (pcc gstate) (code gstate)))) (mem (mem gstate)))
		 (:instance type-i-is-type-expected (gvar  (par3 (nth (pcc gstate) (code gstate)))) (mem (mem gstate)))
		 (:instance inclusion-trans (m1 (mem gstate)) (m2 m)
			    (v (par1 (nth (pcc gstate) (code gstate)))))
		 (:instance inclusion-trans (m1 (mem gstate)) (m2 m)
			    (v (par2 (nth (pcc gstate) (code gstate)))))
		 (:instance inclusion-trans (m1 (mem gstate)) (m2 m)
			    (v (par3 (nth (pcc gstate) (code gstate)))))
		  (:instance
		   equal-sub-and-update-norest-afetr-one-instr
		   (gvar2 (par2 (nth (pcc gstate) (code gstate))))
		   (gvar3 (par3 (nth (pcc gstate) (code gstate))))
		   )
		  eqlenss-sub
		  (:instance correct-wrt-arity-has-rtmintvars-i-tl (mem (mem gstate)))
		  (:instance type-is-for-pars-sub
		   (gvar2 (par2 (nth (pcc gstate) (code gstate))))
		   (gvar3 (par3 (nth (pcc gstate) (code gstate)))))
		  (:instance m-correspondent-values-implies-equal-values-and-attribus
			     (memgstate (mem gstate)) (memrstate (mem rstate))
			     (gvar1 gvar1))
		  (:instance m-correspondent-values-implies-equal-values-and-attribus
			     (memgstate (mem gstate)) (memrstate (mem rstate))
			     (gvar1 (par2 (nth (pcc gstate) (code gstate)))))
		  (:instance m-correspondent-values-implies-equal-values-and-attribus
			     (memgstate (mem gstate)) (memrstate (mem rstate))
			     (gvar1 (par3 (nth (pcc gstate) (code gstate)))))
		  equal-sub-and-updates-after-n-instr
		  (:instance
		   if-gem-is-sub-and-update-inf-every-rtm-var-is-sub-and-update-then-equal-values-is-kept-g
		   (gvar2 (par2 (nth (pcc gstate) (code gstate))))
		   (gvar3 (par3 (nth (pcc gstate) (code gstate))))
		   (rtmvars1   (rtmintvars-i gvar1 m))
		   (rtmvars2   (rtmintvars-i (par2 (nth (pcc gstate) (code gstate))) m))
		   (rtmvars3   (rtmintvars-i (par3 (nth (pcc gstate) (code gstate))) m))
		   (rtmvarsres (rtmintvars-i gvar1 m))
		   (gemmem (mem gstate))
		   (rtmmem (mem rstate))
		   (rtmmemafter (mem (execute-n-instructions rstate (len *rns*)))))))))


(defthm equal-values-correspondence-kept-by-any-execution-sub
  (implies
   (and
    (equal (opcode (nth (pcc gstate) (code gstate))) 'gem-sub)
    (good-translation-gem-rtm gstate rstate m)
    (true-listp m)
    (correct-wrt-arity m (mem gstate))
    (gem-statep gstate)
    (rtm-statep rstate)
    (vars-inclusion (mem gstate) m)
    (in-range (pcc gstate) (code gstate))
    (in-range (pcc rstate) (code rstate))
    (no-duplicates-p (append-lists (retrieve-rtmvars m)))
    (assoc-equal gvar1 m)
    (m-correspondent-values-p m (mem gstate) (mem rstate)))
  (equal-values-and-attributes
   (get-cell gvar1 (mem (execute-instruction gstate)))
   (rtmintvars-i gvar1 m)
   (mem (execute-n-instructions rstate (len *rns*)))
   (type-i gvar1 m)))
  :hints (("Goal" :use (m-correspondence-kept-on-same-gvar-sub
			teorema-main-con-pcc-in-range-su-variabile-non-interessata-final-sub))))



(defthm equal-values-correspondence-kept-by-any-execution-idxed-sub
  (implies
   (and
    (equal (opcode (nth (pcc gstate) (code gstate))) 'gem-sub)
    (no-duplicates-p (retrieve-gemvars m))
    (good-translation-gem-rtm gstate rstate m)
    (alistp m)
    (correct-wrt-arity m (mem gstate))
    (gem-statep gstate)
    (rtm-statep rstate)
    (vars-inclusion (mem gstate) m)
    (in-range (pcc gstate) (code gstate))
    (in-range (pcc rstate) (code rstate))
    (no-duplicates-p (append-lists (retrieve-rtmvars m)))
    (in-range idx m)
    (m-correspondent-values-p m (mem gstate) (mem rstate)))
  (equal-values-and-attributes
   (get-cell (car (nth idx m)) (mem (execute-instruction gstate)))
   (cdr (nth idx m))
   (mem (execute-n-instructions rstate (len *rns*)))
   (type-i-idx m idx)))
  :hints (("Goal" :in-theory (union-theories (current-theory 'ground-zero) '((:definition in-range)))
	   :use ( (:theorem
		   (implies
		    (and
		     (alistp m)
		     (in-range idx m))
		    (and
		     (true-listp m)
		     (assoc-equal (car (nth idx m)) m))))
		  type-i-idx
		  (:instance type-i (gvar (car (nth idx m))))
		  (:instance rtmintvars-i-is-cdr-of-nth-entry (gvar (car (nth idx m))))
		  (:instance equal-values-correspondence-kept-by-any-execution-sub (gvar1 (car (nth idx m))))
		  (:instance no-duplicates-has-pos-equal-right-in-that-place (l m)))))
  :otf-flg t)

(defthm m-correspondence-kept-by-any-execution-idxed-sub
  (implies
   (and
    (equal (opcode (nth (pcc gstate) (code gstate))) 'gem-sub)
    (no-duplicates-p (retrieve-gemvars m))
    (good-translation-gem-rtm gstate rstate m)
    (alistp m)
    (correct-wrt-arity m (mem gstate))
    (gem-statep gstate)
    (rtm-statep rstate)
    (vars-inclusion (mem gstate) m)
    (in-range (pcc gstate) (code gstate))
    (in-range (pcc rstate) (code rstate))
    (no-duplicates-p (append-lists (retrieve-rtmvars m)))
    (m-correspondent-values-p m (mem gstate) (mem rstate)))
  (m-correspondent-values-p
   m
   (mem (execute-instruction gstate))
   (mem (execute-n-instructions rstate (len *rns*)))))
  :hints (("Goal" :use (:instance equal-values-correspondence-kept-by-any-execution-idxed-sub
				  (idx (bad-idx-eqv-va m
						       (mem (execute-instruction gstate))
						       (mem (execute-n-instructions rstate (len *rns*)))))))
	  ("Goal'" :cases ( (in-range (bad-idx-eqv-va m (mem (execute-instruction gstate))
						       (mem (execute-n-instructions rstate (len *rns*)))) m)))
	  ("Subgoal 2" :in-theory '((:forward-chaining alistp-forward-to-true-listp)
				    (:rewrite if-bad-index-not-in-range-then-m-corr)))
	  ("Subgoal 1" :in-theory '((:rewrite if-bad-index-in-range-thne-must-be-different-vs)))))




(defthm m-correspondence-and-other-conditions-kept-by-any-execution-sub
  (implies
   (and
    (alistp m)
    (equal (opcode (nth (pcc gstate) (code gstate))) 'gem-sub)
    (no-duplicates-p (retrieve-gemvars m))
    (no-duplicates-p (append-lists (retrieve-rtmvars m)))
    (good-translation-gem-rtm gstate rstate m)
    (correct-wrt-arity m (mem gstate))
    (gem-statep gstate)
    (rtm-statep rstate)
    (vars-inclusion (mem gstate) m)
    (vars-inclusion m (mem gstate))
    (in-range (pcc gstate) (code gstate))
    (in-range (pcc rstate) (code rstate))
    (m-entries-point-to-good-rtm-var-sets m (mem rstate))
    (m-correspondent-values-p m (mem gstate) (mem rstate)))
   (and
    (good-translation-gem-rtm (execute-instruction gstate) (execute-n-instructions rstate (len *rns*)) m)
    (rtm-statep (execute-n-instructions rstate (len *rns*)))
    (m-entries-point-to-good-rtm-var-sets m (mem (execute-n-instructions rstate (len *rns*))))
    (gem-statep (execute-instruction gstate))
    (correct-wrt-arity m (mem (execute-instruction gstate)))
    (vars-inclusion (mem (execute-instruction gstate)) m)
    (vars-inclusion m (mem (execute-instruction gstate)))
    (m-correspondent-values-p
     m
     (mem (execute-instruction gstate))
     (mem (execute-n-instructions rstate (len *rns*))))))
:hints (("Goal"
	 :in-theory (disable
		     rtm-statep gem-statep
		     pcc code opcode
		     execute-instruction rtmintvars-i par1 par2 par3 nth len member-equal)
	 :use
	 (m-correspondence-kept-by-any-execution-idxed-sub
	  good-translation-gem-rtm
	  (:instance execute-n-instructions-keeps-rtm-state-and-points-to-good
		     (st rstate) (n (len *rns*)))
	  (:instance executing-gem-instruction-retrieves-a-gem-state-from-gem-state (st gstate))
	  (:instance executing-gem-instruction-preserves-correctness-wrt-arity (st gstate))
	  (:instance executing-gem-instruction-keeps-vars-inclusion-right      (st gstate))
	  (:instance executing-gem-instruction-keeps-vars-inclusion-left       (st gstate))))))







;;(ld "Proof-Of-Comparison.lisp" :ld-error-action :error)



(defthm listinstr-of-2-unfolding-f
 (equal
  (listinstr st 2)
  (list
   (nth (pcc st) (code st))
   (nth (pcc (execute-instruction st)) (code (execute-instruction st)))))
 :hints (("Goal"
	  :in-theory (current-theory 'ground-zero)
	  :use ( (:instance listinstr (n 2))
		 (:instance listinstr (st (execute-instruction st)) (n 1))
		 (:instance listinstr (st (execute-instruction (execute-instruction st))) (n 0))))))



(defthm listinstr-of-2-has-the-two-instructions
 (implies
  (equal (listinstr st 2)
	 (rtm-eq-and v1 v2 tmp res))
  (and
   (equal (nth (pcc st) (code st))
	  (list 'rtm-equ tmp v1 v2))
   (equal (nth (pcc (execute-instruction st)) (code (execute-instruction st)))
	  (list 'rtm-and res tmp res))))
 :hints (("Goal" :in-theory (current-theory 'ground-zero)
	  :use (rtm-eq-and
		listinstr-of-2-unfolding-f ))))

(defthm listinstr-of-2-has-the-two-opcodes
 (implies
  (equal (listinstr st 2)
	 (rtm-eq-and v1 v2 tmp res))
  (and
   (equal (opcode (nth (pcc st) (code st))) 'rtm-equ)
   (equal (par1   (nth (pcc st) (code st)))        tmp)
   (equal (par2   (nth (pcc st) (code st)))        v1)
   (equal (par3   (nth (pcc st) (code st)))        v2)
   (equal (opcode (nth (pcc (execute-instruction st)) (code (execute-instruction st)))) 'rtm-and)
   (equal (par1   (nth (pcc (execute-instruction st)) (code (execute-instruction st)))) res)
   (equal (par2   (nth (pcc (execute-instruction st)) (code (execute-instruction st)))) tmp)
   (equal (par3   (nth (pcc (execute-instruction st)) (code (execute-instruction st)))) res)))
 :hints (("Goal" :in-theory (union-theories (current-theory 'ground-zero)
					    '((:definition par1)
					      (:definition par2)
					      (:definition par3)
					      (:definition opcode)))
	  :use (listinstr-of-2-has-the-two-instructions
		(:instance
		 (:theorem  (and
			     (equal (nth 0 (list a b c d)) a)
			     (equal (nth 1 (list a b c d)) b)
			     (equal (nth 2 (list a b c d)) c)
			     (equal (nth 3 (list a b c d)) d)))
		 (a 'rtm-equ)
		 (b tmp)
		 (c v1)
		 (d v2))
		(:instance
		 (:theorem  (and
			     (equal (nth 0 (list a b c d)) a)
			     (equal (nth 1 (list a b c d)) b)
			     (equal (nth 2 (list a b c d)) c)
			     (equal (nth 3 (list a b c d)) d)))
		 (a 'rtm-and)
		 (b res)
		 (c tmp)
		 (d res))))))



(defthm listinstr-of-2-or-the-two-instructions
 (implies
  (equal (listinstr st 2)
	 (rtm-eq-or v1 v2 tmp res))
  (and
   (equal (nth (pcc st) (code st))
	  (list 'rtm-equ tmp v1 v2))
   (equal (nth (pcc (execute-instruction st)) (code (execute-instruction st)))
	  (list 'rtm-or res tmp tmp))))
 :hints (("Goal" :in-theory (current-theory 'ground-zero)
	  :use (rtm-eq-or
		listinstr-of-2-unfolding-f ))))

(defthm listinstr-of-2-or-has-the-two-opcodes
 (implies
  (equal (listinstr st 2)
	 (rtm-eq-or v1 v2 tmp res))
  (and
   (equal (opcode (nth (pcc st) (code st)))   'rtm-equ)
   (equal (par1   (nth (pcc st) (code st)))        tmp)
   (equal (par2   (nth (pcc st) (code st)))         v1)
   (equal (par3   (nth (pcc st) (code st)))         v2)
   (equal (opcode (nth (pcc (execute-instruction st)) (code (execute-instruction st)))) 'rtm-or)
   (equal (par1   (nth (pcc (execute-instruction st)) (code (execute-instruction st)))) res)
   (equal (par2   (nth (pcc (execute-instruction st)) (code (execute-instruction st)))) tmp)
   (equal (par3   (nth (pcc (execute-instruction st)) (code (execute-instruction st)))) tmp)))
 :hints (("Goal" :in-theory (union-theories (current-theory 'ground-zero)
					    '((:definition par1)
					      (:definition par2)
					      (:definition par3)
					      (:definition opcode)))
	  :use (listinstr-of-2-or-the-two-instructions
		(:instance
		 (:theorem  (and
			     (equal (nth 0 (list a b c d)) a)
			     (equal (nth 1 (list a b c d)) b)
			     (equal (nth 2 (list a b c d)) c)
			     (equal (nth 3 (list a b c d)) d)))
		 (a 'rtm-equ)
		 (b tmp)
		 (c v1)
		 (d v2))
		(:instance
		 (:theorem  (and
			     (equal (nth 0 (list a b c d)) a)
			     (equal (nth 1 (list a b c d)) b)
			     (equal (nth 2 (list a b c d)) c)
			     (equal (nth 3 (list a b c d)) d)))
		 (a 'rtm-or)
		 (b res)
		 (c tmp)
		 (d tmp))))))





(defthm one-steps-of-execution
 (implies
   (equal (listinstr st 2)
	  (rtm-eq-and v1 v2 tmp res))
    (equal (execute-instruction st)
	   (generic-eql tmp v1 v2 st)))
  :hints (("Goal"
	   :in-theory '((:definition execute-instruction))
	   :use (listinstr-of-2-has-the-two-opcodes))))

(defthm two-steps-of-execution
 (implies
   (equal (listinstr st 2)
	  (rtm-eq-and v1 v2 tmp res))
    (equal (execute-instruction (execute-instruction st))
	   (rtm-and res tmp res (generic-eql tmp v1 v2 st))))
  :hints (("Goal"
	   :in-theory '((:definition execute-instruction))
	   :use (listinstr-of-2-has-the-two-opcodes))))


; Note: Below I have disabled a couple of names.  This was not in the
; original script.  In the conversion from Version 2.5 to 2.6, we
; added the case-split-limitations and choked it down from (nil nil)
; -- the old default -- to something smaller.  The first proof to
; break was two-steps-inertia, below.  In analyzing why it broke, I
; realized that two-steps-of-execution was being :USEd but not
; DISABLEd.  So it could be rewritten away.  Disabling it, however,
; had no good effect.  Then I realized that it could be rewritten away
; by proving it again, which meant using the definition of
; execute-instruction.  So I disabled that too.  And voila, the proof
; happens very quickly, without significant case analysis -- certainly
; without approaching the case-split-limitations.  You will see a
; similar pair of disables once more below.

(defthm two-steps-inertia
 (implies
  (and
   (equal (listinstr st 2)
	  (rtm-eq-and v1 v2 tmp res))
   (not (equal tmp vx1))
   (not (equal res vx1)))
  (equal (get-cell vx1 (mem (execute-instruction (execute-instruction st))))
	 (get-cell vx1 (mem st))))
 :hints (("Goal" :in-theory (disable execute-instruction     ; (See note above.)
                                     two-steps-of-execution  ; (See note above.)
                                     opcode one-steps-of-execution;par1 par2 par3 pcc code
				     gem-add gem-sub rtm-add rtm-sub and-update gen-eq-update)
	  :use (two-steps-of-execution))))



(defthm two-steps-inertia-on-sequence-of-vars
 (implies
  (and
   (equal (listinstr st 2) (rtm-eq-and v1 v2 tmp res))
   (not (member-equal-bool tmp listvars1))
   (not (member-equal-bool res listvars1)))
  (equal
   (var-values listvars1 (mem st))
   (var-values listvars1 (mem (execute-instruction (execute-instruction st))))))
 :hints (("Goal"
	  :induct    (var-values listvars1 (mem st))
	  :in-theory (disable listinstr-of-2-unfolding-f
			      two-steps-of-execution execute-instruction one-steps-of-execution))
	 ("Subgoal *1/2" :use (:instance two-steps-inertia (vx1 (car listvars1))))))


(defthm two-steps-res
 (implies
  (and
   (equal (listinstr st 2)
	  (rtm-eq-and v1 v2 tmp res))
   (not (equal tmp v1))
   (not (equal tmp v2))
   (not (equal res v1))
   (not (equal res v2))
   (not (equal tmp res)))
  (equal (var-value (get-cell res (mem (rtm-and res tmp res (generic-eql tmp v1 v2 st)))))
	 (boolean-to-int
	  (and
	   (int-to-bool
	    (boolean-to-int (equal (var-value (get-cell v1 (mem st)))
				   (var-value (get-cell v2 (mem st))))))
	   (int-to-bool (var-value (get-cell res (mem st))))))))
 :hints (("Goal"
	  :in-theory (e/d
	  (make-cell put-cell get-cell var-value)
	  (opcode one-steps-of-execution execute-instruction
		  int-to-bool boolean-to-int
		  gem-add gem-sub rtm-add rtm-sub )))))


(defthm one-steps-of-execution-or
 (implies
   (equal (listinstr st 2)
	  (rtm-eq-or v1 v2 tmp res))
    (equal (execute-instruction st)
	   (generic-eql tmp v1 v2 st)))
  :hints (("Goal"
	   :in-theory '((:definition execute-instruction))
	   :use (listinstr-of-2-or-has-the-two-opcodes))))

(defthm two-steps-of-execution-or
 (implies
   (equal (listinstr st 2)
	  (rtm-eq-or v1 v2 tmp res))
    (equal (execute-instruction (execute-instruction st))
	   (rtm-or res tmp tmp (generic-eql tmp v1 v2 st))))
  :hints (("Goal"
	   :in-theory '((:definition execute-instruction))
	   :use (listinstr-of-2-or-has-the-two-opcodes))))


(defthm two-steps-inertia-or
 (implies
  (and
   (equal (listinstr st 2)
	  (rtm-eq-or v1 v2 tmp res))
   (not (equal tmp vx1))
   (not (equal res vx1)))
  (equal (get-cell vx1 (mem (execute-instruction (execute-instruction st))))
	 (get-cell vx1 (mem st))))
 :hints (("Goal" :in-theory (disable execute-instruction       ; (See note above.)
                                     two-steps-of-execution-or ; (See note above.)
                                     opcode one-steps-of-execution-or ;par1 par2 par3 pcc code
				     gem-add gem-sub rtm-add rtm-sub and-update gen-eq-update or-update)
	  :use (two-steps-of-execution-or))))



(defthm two-steps-inertia-on-sequence-of-vars-or
 (implies
  (and
   (equal (listinstr st 2) (rtm-eq-or v1 v2 tmp res))
   (not (member-equal-bool tmp listvars1))
   (not (member-equal-bool res listvars1)))
  (equal
   (var-values listvars1 (mem st))
   (var-values listvars1 (mem (execute-instruction (execute-instruction st))))))
 :hints (("Goal"
	  :induct    (var-values listvars1 (mem st))
	  :in-theory (disable listinstr-of-2-unfolding-f
			      two-steps-of-execution-or execute-instruction one-steps-of-execution-or))
	 ("Subgoal *1/2" :use (:instance two-steps-inertia-or (vx1 (car listvars1))))))


(defthm two-steps-res-or
 (implies
  (and
   (equal (listinstr st 2)
	  (rtm-eq-or v1 v2 tmp res))
   (not (equal tmp v1))
   (not (equal tmp v2))
   (not (equal res v1))
   (not (equal res v2))
   (not (equal tmp res)))
  (equal (var-value (get-cell res (mem (rtm-or res tmp tmp (generic-eql tmp v1 v2 st)))))
	 (boolean-to-int
	  (equal (var-value (get-cell v1 (mem st)))
		 (var-value (get-cell v2 (mem st)))))))
 :hints (("Goal"
	  :use (:theorem
		(equal
		 (or
		  (int-to-bool
		   (boolean-to-int (equal (var-value (get-cell v1 (mem st)))
					  (var-value (get-cell v2 (mem st))))))
		  (int-to-bool
		   (boolean-to-int (equal (var-value (get-cell v1 (mem st)))
					  (var-value (get-cell v2 (mem st)))))))
		 (equal (var-value (get-cell v1 (mem st)))
			(var-value (get-cell v2 (mem st))))))
	  :in-theory (e/d
	  (make-cell put-cell get-cell var-value)
	  (opcode one-steps-of-execution-or execute-instruction
		  int-to-bool boolean-to-int
		  gem-add gem-sub rtm-add rtm-sub )))))



(defthm execute-instruction-2-unfolding
  (equal
   (execute-n-instructions st 2)
   (execute-instruction (execute-instruction st)))
  :hints (("Goal"
	   :in-theory (current-theory 'ground-zero)
	   :use
	   ((:instance execute-n-instructions (n 2))
	    (:instance execute-n-instructions (st (execute-instruction st)) (n 1))
	    (:instance execute-n-instructions (st (execute-instruction (execute-instruction st))) (n 0))))))



(defthm two-steps-res-2
 (implies
  (and
   (equal (listinstr st 2)
	  (rtm-eq-and v1 v2 tmp res))
   (not (equal tmp v1))
   (not (equal tmp v2))
   (not (equal res v1))
   (not (equal res v2))
   (not (equal tmp res)))
  (equal (var-value (get-cell res (mem (execute-n-instructions st 2))))
	 (boolean-to-int
	  (and
	   (equal (var-value (get-cell v1 (mem st)))
		  (var-value (get-cell v2 (mem st))))
	   (int-to-bool (var-value (get-cell res (mem st))))))))
 :hints (("Goal" :in-theory '((:definition int-to-bool)
			      (:definition boolean-to-int))
	  :use (two-steps-res two-steps-of-execution execute-instruction-2-unfolding))))


(defthm two-steps-res-or-2
 (implies
  (and
   (equal (listinstr st 2)
	  (rtm-eq-or v1 v2 tmp res))
   (not (equal tmp v1))
   (not (equal tmp v2))
   (not (equal res v1))
   (not (equal res v2))
   (not (equal tmp res)))
  (equal (var-value (get-cell res (mem (execute-n-instructions st 2))))
	 (boolean-to-int
	  (equal (var-value (get-cell v1 (mem st)))
		 (var-value (get-cell v2 (mem st)))))))
 :hints (("Goal" :in-theory '((:definition int-to-bool)
			      (:definition boolean-to-int))
	  :use (two-steps-res-or two-steps-of-execution-or execute-instruction-2-unfolding))))


(defthm int-bool-int-cancellation
     (equal (int-to-bool (boolean-to-int  (equal v1 v2))) (equal v1 v2)))

(defthm bool-int-bool-cancellation
  (implies
   (or (equal res 0) (equal res 1))
  (equal (boolean-to-int (int-to-bool res)) res)))

(defun eq-values (listvars1 listvars2 res mem n)
  (if (zp n)
      res
    (eq-values
     (cdr listvars1)
     (cdr listvars2)
     (boolean-to-int
      (and
       (equal (var-value (get-cell (car listvars1) mem))
	      (var-value (get-cell (car listvars2) mem)))
       (int-to-bool res)))
     mem
     (1- n))))


(defun equal-lv (listvars1 listvars2 mem n)
  (declare (xargs :measure (acl2-count n)))
  (if (zp n)
      t
    (and
     (equal
      (var-value (get-cell (car listvars1) mem))
      (var-value (get-cell (car listvars2) mem)))
     (equal-lv (cdr listvars1) (cdr listvars2) mem (1- n)))))


(defthm case-zero
  (equal (eq-values listvars1 listvars2 0 mem n) 0))

(defthm case-one
  (equal (eq-values listvars1 listvars2 1 mem n) (boolean-to-int (equal-lv listvars1 listvars2 mem n))))

(defthm eq-values-is-equal-lv
 (implies
  (and
   (or (equal res 0) (equal res 1))
   (equal n (len listvars2))
   (equal n (len listvars1)))
  (equal
   (eq-values listvars1 listvars2 res mem n)
   (boolean-to-int
    (and
     (equal-lv listvars1 listvars2 mem n)
     (int-to-bool res)))))
 :hints (("Goal" :in-theory (disable int-to-bool boolean-to-int))))


(defthm equal-lv-is-equal-values
 (implies
  (and
   (equal n (len listvars1))
   (equal n (len listvars2)))
  (equal
   (equal-lv listvars1 listvars2 mem n)
   (equal-values
    (var-values listvars1 mem)
    (var-values listvars2 mem)))))


(defthm eq-values-is-equal-values
 (implies
  (and
   (or (equal res 0) (equal res 1))
   (equal n (len listvars2))
   (equal n (len listvars1)))
  (equal
   (eq-values listvars1 listvars2 res mem n)
   (boolean-to-int
    (and
     (equal-values
      (var-values listvars1 mem)
      (var-values listvars2 mem))
     (int-to-bool res))))))


(defun induct-support (listvars1 listvars2 tmp res st)
  (if
      (endp listvars1)
      nil
    (cons (list (car listvars1) (car listvars2) tmp res (pcc st))
	  (induct-support
	   (cdr listvars1)
	   (cdr listvars2)
	   tmp
	   res
	   (execute-n-instructions st 2)))))

(defthm support-1
 (implies
  (and
   (not (endp listvars1))
   (not (member-equal-bool tmp listvars1))
   (not (member-equal-bool tmp listvars2))
   (not (member-equal-bool res listvars1))
   (not (member-equal-bool res listvars2)))
  (and
   (not (member-equal-bool tmp (cdr listvars1)))
   (not (member-equal-bool tmp (cdr listvars2)))
   (not (member-equal-bool res (cdr listvars1)))
   (not (member-equal-bool res (cdr listvars2))))))

(defthm listinstr-is-decomposed
 (implies
  (and
   (integerp n)
   (>= n 0))
  (equal
   (listinstr (execute-n-instructions st n) m)
   (nthcdr n (listinstr st (+ n m)))))
 :hints (("Goal"
	  :induct (execute-n-instructions st n)
	  :in-theory (disable execute-instruction))))

(defthm nthcdr-2-unfolding
  (equal (nthcdr 2 l) (cddr l)))

(defthm nthcdr2ofeqtrans2
 (implies
  (not (endp listvars1))
  (equal
   (equality-trans2 (cdr listvars1) (cdr listvars2) tmp res)
   (nthcdr 2 (equality-trans2 listvars1 listvars2 tmp res))))
 :hints (("Goal" :use
	  ( (:instance nthcdr-2-unfolding
		       (l (equality-trans2 listvars1 listvars2 tmp res)))
	    equality-trans2)
	  :in-theory (union-theories (current-theory 'ground-zero) '((:definition rtm-eq-and))))))

(in-theory (disable nthcdr-2-unfolding nthcdr2ofeqtrans2 listinstr-is-decomposed))

(defthm support-2a
 (implies
   (not (endp listvars1))
   (equal (listinstr (execute-n-instructions st 2) (* 2 (len (cdr listvars1))))
	  (nthcdr 2 (listinstr st (* 2 (len listvars1))))))
 :hints (("Goal"
	  :use (
		(:instance listinstr-is-decomposed
			  (n 2)
			  (m (* 2 (len (cdr listvars1))))))
	  :in-theory (disable execute-instruction execute-instruction-2-unfolding is-mem-cell-p))))

(defthm support-2
 (implies
  (and
   (not (endp listvars1))
   (equal (listinstr st (* 2 (len listvars1)))
	  (equality-trans2 listvars1 listvars2 tmp res)))
   (equal (listinstr (execute-n-instructions st 2) (* 2 (len (cdr listvars1))))
	  (equality-trans2 (cdr listvars1) (cdr listvars2) tmp res)))
 :hints (("Goal"
	  :in-theory nil
	  :use (nthcdr2ofeqtrans2 support-2a))))



(defthm listinstr-append
 (implies
  (and
   (integerp n)
   (integerp m)
   (>= m 0)
   (>= n 0))
  (equal
   (listinstr st (+ m n))
   (append (listinstr st m)
	 (listinstr (execute-n-instructions st m) n))))
 :hints (("Goal"
	  :in-theory (disable execute-instruction))))

(defthm silly-00
 (implies
  (and
   (equal l (append l1 l2))
   (>= (len l1) 2))
  (and
   (equal (car l1) (car l))
   (equal (cadr l1) (cadr l)))))

(defthm length-of-listintr
  (implies
   (and
    (integerp n)
    (>= n 0))
   (equal (len (listinstr st n)) n)))

(defthm first-2-instr-are-same-if-many
 (implies
  (and
   (integerp le)
   (>= le 2))
   (and
    (equal (car (listinstr st 2))  (car  (listinstr st le)))
    (equal (cadr (listinstr st 2)) (cadr (listinstr st le)))))
 :hints (("Goal" :in-theory (current-theory 'ground-zero)
	  :use
	  (
	   (:theorem (implies (integerp le) (equal (+ 2 -2 le) le)))
	   (:instance silly-00
		      (l1 (listinstr st 2))
		      (l2 (listinstr (execute-n-instructions st 2) (- le 2)))
		      (l (listinstr st le)))
	   (:instance length-of-listintr (n 2))
	   (:instance listinstr-append
		      (m 2)
		      (n (- le 2)))))))


(defthm first-2-instr-are-same-if-many-inst
 (implies
  (not (endp listvars1))
  (and
   (equal (car (listinstr st 2))  (car  (listinstr st (* 2 (len listvars1)))))
   (equal (cadr (listinstr st 2)) (cadr (listinstr st (* 2 (len listvars1)))))))
 :hints (("Goal"
	  :in-theory (current-theory 'ground-zero)
	  :use (:instance first-2-instr-are-same-if-many (le (* 2 (len listvars1))))))
 :otf-flg t)



(defthm first-two-instructions-are-eq-and
 (implies
  (and
   (not (endp listvars1))
   (equal (listinstr st (* 2 (len listvars1)))
	  (equality-trans2 listvars1 listvars2 tmp res)))
  (equal (listinstr st 2) (rtm-eq-and (car listvars1) (car listvars2) tmp res)))
 :hints (("Goal"
	  :in-theory (disable execute-instruction)
	  :use first-2-instr-are-same-if-many-inst)))



(defthm support-3a
 (implies
  (and
   (equal (listinstr st (* 2 (len listvars1)))
	  (equality-trans2 listvars1 listvars2 tmp res))
   (not (endp listvars1))
   (not (endp listvars2))
   (not (member-equal-bool tmp listvars1))
   (not (member-equal-bool tmp listvars2))
   (not (member-equal-bool res listvars1))
   (not (member-equal-bool res listvars2))
   (not (equal tmp res)))
  (equal
   (eq-values
    listvars1
    listvars2
    (var-value (get-cell res (mem st)))
    (mem st)
    (len listvars1))
   (eq-values
    (cdr listvars1)
    (cdr listvars2)
    (var-value (get-cell res (mem (execute-n-instructions st 2))))
    (mem st)
    (len (cdr listvars1)))))
 :hints (("Goal"
	  :in-theory (disable listinstr-append listinstr-of-2-unfolding-f
			      execute-instruction one-steps-of-execution execute-instruction-2-unfolding)
	  :use
	  (first-two-instructions-are-eq-and
	   (:instance two-steps-res-2 (v1 (car listvars1)) (v2 (car listvars2)))))))





(defthm support-3
 (implies
  (and
   (equal (listinstr st (* 2 (len listvars1)))
	  (equality-trans2 listvars1 listvars2 tmp res))
   (not (endp listvars1))
   (not (endp listvars2))
   (equal (len listvars1) (len listvars2))
   (not (member-equal-bool tmp listvars1))
   (not (member-equal-bool tmp listvars2))
   (not (member-equal-bool res listvars1))
   (not (member-equal-bool res listvars2))
   (not (equal tmp res)))
  (equal
   (eq-values
    listvars1
    listvars2
    (var-value (get-cell res (mem st)))
    (mem st)
    (len listvars1))
   (eq-values
    (cdr listvars1)
    (cdr listvars2)
    (var-value (get-cell res (mem (execute-n-instructions st 2))))
    (mem (execute-instruction (execute-instruction st)))
    (len (cdr listvars1)))))
 :hints (("Goal"
	  :in-theory (disable listinstr-append listinstr-of-2-unfolding-f
			      execute-instruction one-steps-of-execution execute-instruction-2-unfolding)
	  :use
	  (first-two-instructions-are-eq-and
	   (:instance two-steps-inertia-on-sequence-of-vars
		      (v1 (car listvars1))
		      (v2 (car listvars2))
		      (listvars1 (cdr listvars1)))
	   (:instance two-steps-inertia-on-sequence-of-vars
		      (v1 (car listvars1))
		      (v2 (car listvars2))
		      (listvars1 (cdr listvars2)))
	   (:instance two-steps-res-2 (v1 (car listvars1)) (v2 (car listvars2)))))))








(defthm value-of-result-after-executing-2n-instr
 (implies
  (and
   (not (member-equal-bool tmp listvars1))
   (not (member-equal-bool tmp listvars2))
   (not (member-equal-bool res listvars1))
   (not (member-equal-bool res listvars2))
   (equal (len listvars1) (len listvars2))
   (not (equal tmp res))
   (equal (listinstr st (* 2 (len listvars1)))
	  (equality-trans2 listvars1 listvars2 tmp res)))
 (equal
  (var-value
   (get-cell
    res
    (mem (execute-n-instructions st (* 2 (len listvars1))))))
  (eq-values
   listvars1
   listvars2
   (var-value (get-cell res (mem st)))
   (mem st)
   (len listvars1))))
 :hints (("Goal"
	  :in-theory (disable execute-instruction is-mem-cell-p)
	  :induct (induct-support listvars1 listvars2 tmp res st))
	 ("Subgoal *1/2" :use (support-1 support-2 support-3))))


(defthm value-of-result-after-executing-2n-instr-fin
 (implies
  (and
   (not (member-equal-bool tmp listvars1))
   (not (member-equal-bool tmp listvars2))
   (not (member-equal-bool res listvars1))
   (not (member-equal-bool res listvars2))
   (equal (len listvars1) (len listvars2))
   (or
    (equal (var-value (get-cell res (mem st))) 0)
    (equal (var-value (get-cell res (mem st))) 1))
   (not (equal tmp res))
   (equal (listinstr st (* 2 (len listvars1)))
	  (equality-trans2 listvars1 listvars2 tmp res)))
 (equal
  (var-value
   (get-cell
    res
    (mem (execute-n-instructions st (* 2 (len listvars1))))))
  (boolean-to-int
   (and
    (equal-values
     (var-values listvars1 (mem st))
     (var-values listvars2 (mem st)))
    (int-to-bool (var-value (get-cell res (mem st))))))))
 :hints (("Goal"
	  :in-theory (disable execute-instruction is-mem-cell-p)
	  :use (value-of-result-after-executing-2n-instr))))
(defthm nthcdr2ofeqtrans3
  (equal
   (equality-trans2 (cdr listvars1) (cdr listvars2) tmp res)
   (nthcdr 2 (equality-trans3 listvars1 listvars2 tmp res)))
 :hints (("Goal" :use
	  ( (:instance nthcdr-2-unfolding
		       (l (equality-trans3 listvars1 listvars2 tmp res)))
	    equality-trans3)
	  :in-theory (union-theories (current-theory 'ground-zero) '((:definition rtm-eq-or))))))

(in-theory (disable nthcdr-2-unfolding nthcdr2ofeqtrans3 listinstr-is-decomposed))


(defthm support-2b
 (implies
  (and
   (not (endp listvars1))
   (equal (listinstr st (* 2 (len listvars1)))
	  (equality-trans3 listvars1 listvars2 tmp res)))
   (equal (listinstr (execute-n-instructions st 2) (* 2 (len (cdr listvars1))))
	  (equality-trans2 (cdr listvars1) (cdr listvars2) tmp res)))
 :hints (("Goal"
	  :in-theory nil
	  :use (nthcdr2ofeqtrans3 support-2a))))



(defthm first-two-instructions-are-eq-or
 (implies
  (and
   (not (endp listvars1))
   (equal (listinstr st (* 2 (len listvars1)))
	  (equality-trans3 listvars1 listvars2 tmp res)))
  (equal (listinstr st 2) (rtm-eq-or (car listvars1) (car listvars2) tmp res)))
 :hints (("Goal"
	  :in-theory (disable nthcdr nthcdr2ofeqtrans3 execute-instruction
                              ;; v2-6 mod:
                              listinstr-append)
	  :use first-2-instr-are-same-if-many-inst)))




(defthm support4
 (implies
  (not (endp listvars1))
  (EQUAL
   (EXECUTE-N-INSTRUCTIONS (EXECUTE-N-INSTRUCTIONS ST 2) (* 2 (LEN (CDR LISTVARS1))))
   (EXECUTE-N-INSTRUCTIONS ST (* 2 (LEN LISTVARS1)))))
 :hints (("Goal"
	  :in-theory (current-theory 'ground-zero)
	  :use
	  (:instance execute-n-instruction-decomposition
		     (n1 2)
		     (n2 (* 2 (1- (len listvars1))))))
	 ("Subgoal 1"
	  :use ((:theorem (equal (+ -2 2   (* 2 (LEN (CDR LISTVARS1))))
             				   (* 2 (LEN (CDR LISTVARS1)))))
		(:theorem (equal (+ 2      (* 2 (LEN (CDR LISTVARS1))))
				 (+ 2 -2 2 (* 2 (LEN (CDR LISTVARS1))))))))))


(defthm value-of-result-after-executing-2n-+2instr-fin
 (implies
  (and
   (not (member-equal-bool tmp listvars1))
   (not (member-equal-bool tmp listvars2))
   (not (member-equal-bool res listvars1))
   (not (member-equal-bool res listvars2))
   (equal (len listvars1) (len listvars2))
   (not (endp listvars1))
   (not (equal tmp res))
   (equal (listinstr st (* 2 (len listvars1)))
	  (equality-trans3 listvars1 listvars2 tmp res)))
 (equal
  (var-value
   (get-cell
    res
    (mem (execute-n-instructions st (* 2 (len listvars1))))))
  (boolean-to-int
   (and
    (equal-values
     (var-values (cdr listvars1) (mem (execute-n-instructions st 2)))
     (var-values (cdr listvars2) (mem (execute-n-instructions st 2))))
    (int-to-bool
     (boolean-to-int
      (equal (var-value (get-cell (car listvars1) (mem st)))
	     (var-value (get-cell (car listvars2) (mem st))))))))))
 :hints (("Goal"
	  :in-theory (union-theories (current-theory 'ground-zero)
				     '((:definition member-equal-bool)
				       (:definition boolean-to-int)))
	  :use
	  (
	   support-2b
	   support4
	   first-two-instructions-are-eq-or
	   (:instance value-of-result-after-executing-2n-instr-fin
		      (st (execute-n-instructions st 2))
		      (listvars1 (cdr listvars1))
		      (listvars2 (cdr listvars2)))
	   (:instance two-steps-res-or-2
		      (v1 (car listvars1))
		      (v2 (car listvars2)))))))


(defthm at-the-end-equality-on-all
 (implies
  (and
   (not (endp listvars1))
   (equal (len listvars1) (len listvars2)))
  (equal
   (boolean-to-int
    (equal-values
     (var-values listvars1 (mem st ))
     (var-values listvars2 (mem st ))))
   (boolean-to-int
    (and
     (equal-values
      (var-values (cdr listvars1) (mem st ))
      (var-values (cdr listvars2) (mem st )))
     (int-to-bool
      (boolean-to-int
       (equal (var-value (get-cell (car listvars1) (mem st)))
	      (var-value (get-cell (car listvars2) (mem st)))))))))))







(defthm value-of-result-after-executing-2n-+2instr-finale
 (implies
  (and
   (not (member-equal-bool tmp listvars1))
   (not (member-equal-bool tmp listvars2))
   (not (member-equal-bool res listvars1))
   (not (member-equal-bool res listvars2))
   (equal (len listvars1) (len listvars2))
   (not (endp listvars1))
   (not (equal tmp res))
   (equal (listinstr st (* 2 (len listvars1)))
	  (equality-trans3 listvars1 listvars2 tmp res)))
 (equal
  (var-value
   (get-cell
    res
    (mem (execute-n-instructions st (* 2 (len listvars1))))))
  (boolean-to-int
    (equal-values
     (var-values  listvars1 (mem st ))
     (var-values  listvars2 (mem st ))))))
 :hints (("Goal"
	  :in-theory
	  (union-theories (current-theory 'ground-zero)
				     '((:rewrite execute-instruction-2-unfolding)
				       (:definition member-equal-bool)))
	  :use (
		(:instance two-steps-inertia-on-sequence-of-vars-or
			   (v1 (car listvars1))
			   (v2 (car listvars2))
			   (listvars1 (cdr listvars1)))
		(:instance two-steps-inertia-on-sequence-of-vars-or
			   (v1 (car listvars1))
			   (v2 (car listvars2))
			   (listvars1 (cdr listvars2)))
		first-two-instructions-are-eq-or
		value-of-result-after-executing-2n-+2instr-fin
		at-the-end-equality-on-all))))


(in-theory (disable
listinstr-of-2-unfolding-f listinstr-of-2-has-the-two-instructions listinstr-of-2-has-the-two-opcodes
listinstr-of-2-or-the-two-instructions listinstr-of-2-or-has-the-two-opcodes
one-steps-of-execution two-steps-of-execution two-steps-inertia
two-steps-inertia-on-sequence-of-vars two-steps-res
one-steps-of-execution-or two-steps-of-execution-or two-steps-inertia-or
two-steps-inertia-on-sequence-of-vars-or two-steps-res-or
execute-instruction-2-unfolding two-steps-res-2 two-steps-res-or-2
int-bool-int-cancellation bool-int-bool-cancellation case-zero case-one
equal-lv-is-equal-values eq-values-is-equal-values
support-1 listinstr-is-decomposed nthcdr-2-unfolding support-2a support-2
listinstr-append silly-00 length-of-listintr
first-2-instr-are-same-if-many first-2-instr-are-same-if-many-inst
first-two-instructions-are-eq-and support-3a support-3
value-of-result-after-executing-2n-instr value-of-result-after-executing-2n-instr-fin
equality-trans3 nthcdr2ofeqtrans3 support-2b
first-two-instructions-are-eq-or support4
value-of-result-after-executing-2n-+2instr-fin
at-the-end-equality-on-all value-of-result-after-executing-2n-+2instr-finale))

(defun pars1-instructions (listinstr)
  (if (endp listinstr)
      nil
    (cons (par1 (car listinstr))
	  (pars1-instructions (cdr listinstr)))))

(defthm pars1-instruction-is-listpars1
  (equal
   (pars1-instructions (listinstr st n))
   (listpars1 st n)))



(defun eqtr2 (l1 tmp res)
  (if
      (endp l1)
      nil
    (append (list tmp res) (eqtr2 (cdr l1) tmp res))))

(defun eqtr3 (l1 tmp res)
  (append (list tmp res) (eqtr2 (cdr l1) tmp res)))

(defthm cgr1 (equal (pars1-instructions (equality-trans2 l1 l2 tmp res)) (eqtr2 l1 tmp res)))

(defthm pars1iappend
  (equal (pars1-instructions (append l1 l2))
	 (append (pars1-instructions l1) (pars1-instructions l2))))

(defthm parsi-instructions-of-eq3-are-eqtr3
  (equal (pars1-instructions (equality-trans3 l1 l2 tmp res)) (eqtr3 l1 tmp res))
     :hints (("Subgoal 2" :in-theory nil)
	     ("Goal" :use (eqtr3
			   (:instance pars1iappend
				      (l1 (rtm-eq-or (car l1) (car l2 ) tmp res))
				      (l2 (equality-trans2 (cdr l1) (cdr l2) tmp res)))
			   (:instance cgr1 (l1 (cdr l1)) (l2 (cdr l2)))
			   (:theorem (equal (pars1-instructions (rtm-eq-or (car l1) (car l2) tmp res)) (list tmp res)))
			   (:instance equality-trans3 (listvars1 l1) (listvars2 l2))))))


(defthm only-tmp-res-into-eqtr3
 (implies
  (and
   (not (equal v tmp))
   (not (equal v res)))
  (not (member-equal-bool v (eqtr3 l1 tmp res))))
 :otf-flg t)





(defthm equality-trans3-has-par1-made-of-tmp-res
  (implies
   (and
    (not (equal v tmp))
    (not (equal v res))
    (equal
     (listinstr st n)
     (equality-trans3 l1 l2 tmp res)))
  (not (member-equal-bool v (listpars1 st n))))
:hints (("Goal" :in-theory nil
	 :use (pars1-instruction-is-listpars1
	       parsi-instructions-of-eq3-are-eqtr3
	       only-tmp-res-into-eqtr3))))








(DEFUN LISTOPCODES (ST N)
                    (IF (ZP N)
                        NIL
                        (CONS (OPCODE (NTH (PCC ST) (CODE ST)))
                              (LISTOPCODES (EXECUTE-INSTRUCTION ST)
                                         (1- N)))))
(defun all-par1ops (opcodes)
  (if (endp opcodes)
      t
    (and
     (or
      (equal (car opcodes) 'rtm-and)
      (equal (car opcodes) 'rtm-or)
      (equal (car opcodes) 'rtm-equ)
      (equal (car opcodes) 'rtm-add)
      (equal (car opcodes) 'rtm-sub))
     (all-par1ops (cdr opcodes)))))

(defun all-par1opso (st n)
  (declare (xargs :measure (acl2-count n)))
  (if (zp n)
      t
    (and
     (or
      (null (NTH (PCC ST) (CODE ST)))
      (equal  (OPCODE (NTH (PCC ST) (CODE ST))) 'rtm-and)
      (equal  (OPCODE (NTH (PCC ST) (CODE ST))) 'rtm-or)
      (equal  (OPCODE (NTH (PCC ST) (CODE ST))) 'rtm-equ)
      (equal  (OPCODE (NTH (PCC ST) (CODE ST))) 'rtm-add)
      (equal  (OPCODE (NTH (PCC ST) (CODE ST))) 'rtm-sub))
     (all-par1opso (execute-instruction st) (1- n)))))



(defthm if-only-par1-involving-ops-are-there-then-other-vars-are-untouched
 (implies
  (and
   (all-par1opso st n)
   (not (member-equal-bool v (listpars1 st n))))
  (equal (get-cell v (mem st)) (get-cell v (mem (execute-n-instructions st n)))))
 :hints (("Goal" :in-theory (disable execute-instruction))
	 ("Subgoal *1/2" :use (:instance only-par1-is-involved-rtm
					 (gstate st)
					 (var v)))))




(defun pars1-opcodes (listinstr)
  (if (endp listinstr)
      nil
    (cons (opcode (car listinstr))
	  (pars1-opcodes (cdr listinstr)))))

(defthm pars1-opcodes-is-listopcodes
  (equal
   (pars1-opcodes (listinstr st n))
   (listopcodes st n)))

(defun eqtr2o (l1)
  (if
      (endp l1)
      nil
    (append (list 'rtm-equ 'rtm-and) (eqtr2o (cdr l1)))))

(defun eqtr3o (l1)
  (append (list 'rtm-equ 'rtm-or) (eqtr2o (cdr l1))))

(defthm cgr2 (equal (pars1-opcodes (equality-trans2 l1 l2 tmp res)) (eqtr2o l1)))

(defthm pars1oappend
  (equal (pars1-opcodes (append l1 l2))
	 (append (pars1-opcodes l1) (pars1-opcodes l2))))

(defthm parsi-opcodes-of-eq3-are-eqtr3o
  (equal (pars1-opcodes (equality-trans3 l1 l2 tmp res)) (eqtr3o l1))
     :hints (("Subgoal 2" :in-theory nil)
	     ("Goal" :use (eqtr3o
			   (:instance pars1oappend
				      (l1 (rtm-eq-or (car l1) (car l2 ) tmp res))
				      (l2 (equality-trans2 (cdr l1) (cdr l2) tmp res)))
			   (:instance cgr2 (l1 (cdr l1)) (l2 (cdr l2)))
			   (:theorem (equal (pars1-opcodes (rtm-eq-or (car l1) (car l2) tmp res)) (list 'rtm-equ 'rtm-or)))
			   (:instance equality-trans3 (listvars1 l1) (listvars2 l2))))))


(defthm eqtr3o-makes-par1-instrs
  (all-par1ops (eqtr3o l))
  :otf-flg t)



(defthm opcodes-on-par1-imply-instructions-on-par1
 (implies
  (all-par1ops (pars1-opcodes (listinstr st n)))
  (all-par1opso st n)))

(defthm if-instructions-are-trans3-and-v-non-in-par1-v-untouched
 (implies
  (and
   (equal (listinstr st n)
	  (equality-trans3 l1 l2 tmp res))
   (not (member-equal-bool v (listpars1 st n))))
  (equal
   (get-cell v (mem st))
   (get-cell v (mem (execute-n-instructions st n)))))
 :hints (("Goal"
	  :in-theory nil
	  :use
	  (opcodes-on-par1-imply-instructions-on-par1
	   pars1-opcodes-is-listopcodes
	   parsi-opcodes-of-eq3-are-eqtr3o
	   (:instance eqtr3o-makes-par1-instrs (l l1))
	   if-only-par1-involving-ops-are-there-then-other-vars-are-untouched))))


(defthm equality-trans3-means-touching-just-tmp-res
  (implies
   (and
    (not (equal v tmp))
    (not (equal v res))
    (equal
     (listinstr st n)
     (equality-trans3 l1 l2 tmp res)))
  (equal
   (get-cell v (mem st))
   (get-cell v (mem (execute-n-instructions st n)))))
  :hints (("Goal"
	   :use
	   (if-instructions-are-trans3-and-v-non-in-par1-v-untouched
	    equality-trans3-has-par1-made-of-tmp-res))))





(in-theory (disable
	    pars1-instructions  pars1-instruction-is-listpars1
	    eqtr2 eqtr3 cgr1 pars1iappend parsi-instructions-of-eq3-are-eqtr3
	    only-tmp-res-into-eqtr3 equality-trans3-has-par1-made-of-tmp-res
	    all-par1ops all-par1opso
	    if-only-par1-involving-ops-are-there-then-other-vars-are-untouched
	    pars1-opcodes pars1-opcodes-is-listopcodes
	    eqtr2o eqtr3o cgr2 pars1oappend parsi-opcodes-of-eq3-are-eqtr3o
	    eqtr3o-makes-par1-instrs opcodes-on-par1-imply-instructions-on-par1
	    if-instructions-are-trans3-and-v-non-in-par1-v-untouched))



(defthm lemma2-only-adds-in-rtm-equ
  (implies
   (and
    (gem-statep gstate)
    (rtm-statep rstate)
    (in-range (pcc gstate) (code gstate))
    (in-range (pcc rstate) (code rstate))
    (equal (opcode (nth (pcc gstate) (code gstate))) 'gem-equ)
    (good-translation-gem-rtm gstate rstate m))
   (and
    (equal (listinstr     rstate (* 2 (len *rns*)) )
	   (equality-trans3
	    (eventually-make-list (rtmintvars-i (par2 (nth (pcc gstate) (code gstate))) m) (len *rns*))
	    (eventually-make-list (rtmintvars-i (par3 (nth (pcc gstate) (code gstate))) m) (len *rns*))
	    'tmp
	    (car (rtmintvars-i (par1 (nth (pcc gstate) (code gstate))) m))))
    (not (equal
	  (par1 (nth (pcc gstate) (code gstate)))
	  (par2 (nth (pcc gstate) (code gstate)))))
    (not (equal
	  (par1 (nth (pcc gstate) (code gstate)))
	  (par3 (nth (pcc gstate) (code gstate)))))))
  :hints (("Goal" :expand
	   ( (good-translation-gem-rtm gstate rstate m)
	     (gem-statep gstate)
	     (rtm-statep rstate)
	     (in-range (pcc gstate) (code gstate))
	     (in-range (pcc rstate) (code rstate)))
	   :in-theory nil))
  :rule-classes nil)



(defthm lemma1-different-vars-do-not-belong-ref
  (implies
   (and
    (true-listp m)
    (not (endp (rtmintvars-i gvar2 m)))
    (no-duplicates-p (append-lists (retrieve-rtmvars m)))
    (assoc-equal gvar1 m)
    (assoc-equal gvar2 m)
    (not (equal gvar1 gvar2))
    (in-range idx1 (rtmintvars-i gvar1 m)))
  (not (equal (nth idx1 (rtmintvars-i gvar1 m))
		     (car (rtmintvars-i gvar2 m)))))
  :hints (("Goal" :in-theory nil
	   :use (lemma1-different-vars-do-not-belong
			(:instance member-equal-bool
				   (el (nth idx1 (rtmintvars-i gvar1 m)))
				   (l (rtmintvars-i gvar2 m)))))))

(defun no-tmp-into-mapping (m)
  (if (endp m)
      t
    (and
     (not (member-equal-bool 'tmp (rtmintvars-0 m)))
     (no-tmp-into-mapping (cdr m)))))

(defthm a-variable-is-never-tmp
  (implies
   (and
    (no-tmp-into-mapping m)
    (assoc-equal gvar1 m)
    (in-range idx1 (rtmintvars-i gvar1 m)))
   (not (equal (nth idx1 (rtmintvars-i gvar1 m)) 'tmp)))
  :hints (("Goal" :in-theory (enable rtmintvars-0))))


(defthm an-m-entry-is-never-nil
 (implies
  (and
    (true-listp m)
    (m-entries-point-to-good-rtm-var-sets m rtm-mem)
    (assoc-equal var m))
  (not (endp (rtmintvars-i var m))))
 :hints (("Goal" :in-theory (enable rtmintvars-0))))


(defthm rtm-variable-of-other-cell-untouched-equ
  (implies
   (and
    (equal (opcode (nth (pcc gstate) (code gstate))) 'gem-equ)
    (>= (pcc rstate) 0)
    (rtm-statep rstate)
    (no-tmp-into-mapping m)
    (m-entries-point-to-good-rtm-var-sets m (mem rstate))
    (good-translation-gem-rtm gstate rstate m)
    (in-range (pcc gstate) (code gstate))
    (assoc-equal (par1 (nth (pcc gstate) (code gstate))) m)
    (true-listp m)
    (no-duplicates-p (append-lists (retrieve-rtmvars m)))
    (assoc-equal gvar1 m)
    (not (equal gvar1 (par1 (nth (pcc gstate) (code gstate)))))
    (in-range idx1 (rtmintvars-i gvar1 m)))
   (equal (get-cell (nth idx1 (rtmintvars-i gvar1 m)) (mem rstate))
	  (get-cell (nth idx1 (rtmintvars-i gvar1 m)) (mem (execute-n-instructions rstate (* 2 (len *rns*)))))))
  :hints (("Goal" :in-theory (current-theory 'ground-zero)
	   :expand (     (in-range (pcc gstate) (code gstate))
			 (good-translation-gem-rtm gstate rstate m) )
	   :use (
		 (:instance a-variable-is-never-tmp (gvar1 gvar1))
		 (:instance an-m-entry-is-never-nil
			    (rtm-mem (mem rstate))
			    (var (par1 (nth (pcc gstate) (code gstate)))))
		 (:instance equality-trans3-means-touching-just-tmp-res
			    (v (nth idx1 (rtmintvars-i gvar1 m)))
			    (l1 (eventually-make-list (rtmintvars-i (par2 (nth (pcc gstate) (code gstate))) m) (len *rns*)))
			    (l2 (eventually-make-list (rtmintvars-i (par3 (nth (pcc gstate) (code gstate))) m) (len *rns*)))
			    (st rstate)
			    (tmp 'tmp)
			    (res (car (rtmintvars-i (par1 (nth (pcc gstate) (code gstate))) m)))
			    (n (* 2 (len *rns*))))
		 (:instance lemma1-different-vars-do-not-belong-ref  (gvar2 (par1 (nth (pcc gstate) (code gstate)))))))))



(defthm rtm-variables-of-other-cell-untouched-equ
  (implies
   (and
    (equal (opcode (nth (pcc gstate) (code gstate))) 'gem-equ)
    (no-tmp-into-mapping m)
    (m-entries-point-to-good-rtm-var-sets m (mem rstate))
    (>= (pcc rstate) 0)
    (rtm-statep rstate)
    (good-translation-gem-rtm gstate rstate m)
    (in-range (pcc gstate) (code gstate))
    (assoc-equal (par1 (nth (pcc gstate) (code gstate))) m)
    (true-listp m)
    (no-duplicates-p (append-lists (retrieve-rtmvars m)))
    (assoc-equal gvar1 m)
    (true-listp (rtmintvars-i gvar1 m))
    (not (equal gvar1 (par1 (nth (pcc gstate) (code gstate))))))
   (equal-get-cells
          (rtmintvars-i gvar1 m) (mem rstate) (mem (execute-n-instructions rstate (* 2 (len *rns*))))))
  :hints (("Goal" :in-theory nil
	   :use ( (:instance rtm-variable-of-other-cell-untouched-equ
			     (idx1 (idx-different-cell
				    (rtmintvars-i gvar1 m)
				    (mem rstate)
				    (mem (execute-n-instructions rstate (* 2 (len *rns*)))))) )))
	  ("Goal'" :cases ( (in-range
			     (idx-different-cell
				    (rtmintvars-i gvar1 m)
				    (mem rstate)
				    (mem (execute-n-instructions rstate (* 2 (len *rns*)))))
			     (rtmintvars-i gvar1 m))))
	  ("Subgoal 2" :in-theory '((:rewrite if-bad-index-not-in-range-then-every-equal)))
	  ("Subgoal 1" :in-theory '((:forward-chaining if-bad-index-in-range-then-cells-must-be-different)))))



(defthm properies-of-type-and-existence-of-current-args-equ
 (implies
  (and
   (gem-statep gstate)
   (in-range (pcc gstate) (code gstate))
   (equal (opcode (nth (pcc gstate) (code gstate))) 'gem-equ))
  (and
   (equal (var-type (get-cell (par1 (nth (pcc gstate) (code gstate))) (mem gstate))) 'Bool)
   (assoc-equal (par1 (nth (pcc gstate) (code gstate))) (mem gstate))
   (assoc-equal (par2 (nth (pcc gstate) (code gstate))) (mem gstate))
   (assoc-equal (par3 (nth (pcc gstate) (code gstate))) (mem gstate))))
  :hints (("Goal" :in-theory (enable get-cell)
	   :use (:instance in-range-instruction-is-gem-instruction
			   (pcc (pcc gstate))
			   (code (code gstate))
			   (mem (mem gstate)))))
  :rule-classes nil)


(defthm par1-of-current-instruction-is-into-mapping-equ
 (implies
  (and
   (vars-inclusion (mem gstate) m)
   (gem-statep gstate)
   (equal (opcode (nth (pcc gstate) (code gstate))) 'gem-equ)
   (in-range (pcc gstate) (code gstate)))
  (assoc-equal (par1 (nth (pcc gstate) (code gstate))) m))
 :hints (("Goal" :in-theory (enable get-cell)
	 :use (properies-of-type-and-existence-of-current-args-equ
	       (:instance inclusion-trans
			  (v (par1 (nth (pcc gstate) (code gstate))))
			  (m1 (mem gstate))
			  (m2 m))
	       (:instance in-range-instruction-is-gem-instruction
				 (pcc (pcc gstate))
				 (code (code gstate))
				 (mem (mem gstate)))))))




(defthm teorema-main-con-pcc-in-range-su-variabile-non-interessata-final-equ
 (implies
  (and
   (equal (opcode (nth (pcc gstate) (code gstate))) 'gem-equ)
   (no-tmp-into-mapping m)
   (m-entries-point-to-good-rtm-var-sets m (mem rstate))
   (good-translation-gem-rtm gstate rstate m)
   (vars-inclusion (mem gstate) m)
   (true-listp m)
   (assoc-equal gvar1 m)
   (gem-statep gstate)
   (rtm-statep rstate)
   (in-range (pcc gstate) (code gstate))
   (in-range (pcc rstate) (code rstate))
   (not (equal gvar1 (par1 (nth (pcc gstate) (code gstate)))))
   (m-correspondent-values-p m (mem gstate) (mem rstate))
   (no-duplicates-p (append-lists (retrieve-rtmvars m)))
   (correct-wrt-arity m (mem gstate)))
  (equal-values-and-attributes
   (get-cell gvar1 (mem (execute-instruction gstate)))
   (rtmintvars-i gvar1 m)
   (mem (execute-n-instructions rstate (* 2 (len *rns*))))
   (type-i gvar1 m)))
 :hints (("Goal"
	  :in-theory '((:definition good-translation-gem-rtm))
	  :use (
		par1-of-current-instruction-is-into-mapping-equ
		(:instance correct-wrt-arity-has-rtmintvars-i-tl (mem (mem gstate)))
		(:instance m-correspondent-values-implies-equal-values-and-attribus
			   (memgstate (mem gstate)) (memrstate (mem rstate)))
		(:instance in-range (idx (pcc gstate)) (l (code gstate)))
		(:instance in-range (idx (pcc rstate)) (l (code rstate)))
		rtm-variables-of-other-cell-untouched-equ
		teorema-main-con-pcc-in-range-su-variabile-non-interessata
		(:instance equal-get-cells-implies-equal-values-and-attributes-still-works
			   (gemcell (get-cell gvar1 (mem gstate)))
			   (lcell (rtmintvars-i gvar1 m))
			   (mem1 (mem rstate))
			   (mem2 (mem (execute-n-instructions rstate (* 2 (len *rns*)))))
			   (type (type-i gvar1 m)))))))


(defthm posinrg-equ
  (implies
   (and
    (vars-inclusion (mem gstate) m)
    (gem-statep gstate)
    (equal (opcode (nth (pcc gstate) (code gstate))) 'gem-equ)
    (in-range (pcc gstate) (code gstate)))
    (and
     (in-range (pos-equal-0 (par1 (nth (pcc gstate) (code gstate))) m) m)
     (in-range (pos-equal-0 (par2 (nth (pcc gstate) (code gstate))) m) m)
     (in-range (pos-equal-0 (par3 (nth (pcc gstate) (code gstate))) m) m)))
   :hints (("Goal" :use (properies-of-type-and-existence-of-current-args-equ
			(:instance inclusion-trans (m1 (mem gstate)) (m2 m)
				   (v (par1 (nth (pcc gstate) (code gstate)))))
			(:instance inclusion-trans (m1 (mem gstate)) (m2 m)
				   (v (par2 (nth (pcc gstate) (code gstate)))))
			(:instance inclusion-trans (m1 (mem gstate)) (m2 m)
				   (v (par3 (nth (pcc gstate) (code gstate)))))
			(:instance assoc-means-pos-in-range
				   (el (par1 (nth (pcc gstate) (code gstate))))
				   (l m))
			(:instance assoc-means-pos-in-range
				   (el (par2 (nth (pcc gstate) (code gstate))))
				   (l m))
			(:instance assoc-means-pos-in-range
				   (el (par3 (nth (pcc gstate) (code gstate))))
				   (l m)))))
   :rule-classes nil)


(defthm equal-eq-update-norest-afetr-one-instr
  (implies
   (and
    (gem-statep gstate)
    (in-range (pcc gstate) (code gstate))
    (equal (opcode (nth (pcc gstate) (code gstate))) 'gem-equ)
    (good-translation-gem-rtm gstate rstate m)
    (equal gvar1 (par1 (nth (pcc gstate) (code gstate))))
    (equal gvar2 (par2 (nth (pcc gstate) (code gstate))))
    (equal gvar3 (par3 (nth (pcc gstate) (code gstate)))))
   (equal (get-cell gvar1 (mem (execute-instruction gstate)))
	  (gen-eq-update gvar1 gvar2 gvar3 (mem gstate))))
  :hints (("Goal" :in-theory (e/d (put-cell get-cell)
				  (par1 par2 par3 par4 opcode pcc code nth gem-instruction-list-p
					gen-eq-update sum-and-update sub-and-update sub-and-update-norest sum-and-update-norest))))
  :rule-classes nil)

(DEFTHM mem-cellity-of-current-gem-args-equ
  (IMPLIES
   (AND (GEM-STATEP GSTATE)
	(equal (opcode (nth (pcc gstate) (code gstate))) 'gem-equ)
	(IN-RANGE (PCC GSTATE) (CODE GSTATE)))
   (AND (is-mem-cell-p (get-cell  (PAR1 (NTH (PCC GSTATE) (CODE GSTATE))) (mem gstate)))
	(is-mem-cell-p (get-cell  (PAR2 (NTH (PCC GSTATE) (CODE GSTATE))) (mem gstate)))
	(is-mem-cell-p (get-cell  (PAR3 (NTH (PCC GSTATE) (CODE GSTATE))) (mem gstate)))))
  :HINTS
  (("Goal"
    :USE
    (:INSTANCE IN-RANGE-INSTRUCTION-IS-GEM-INSTRUCTION
	       (PCC (PCC GSTATE))
	       (CODE (CODE GSTATE))
	       (MEM (MEM GSTATE))))))




(DEFTHM
  VAR-ATTRIBUTES-OF-1-VARIABLE-IS-ONE-ELEMENT-LIST-OF-VAR-ATTRIBUTE
  (IMPLIES (AND (TRUE-LISTP VARS)
		(EQUAL (LEN VARS) 1))
	   (EQUAL (VAR-ATTRIBUTES VARS MEM)
		  (LIST (VAR-ATTRIBUTE (GET-CELL (CAR VARS) MEM)))))
  :HINTS
  (("Subgoal *1/2.2"
    :USE
    (:THEOREM (IMPLIES (AND (TRUE-LISTP VARS)
			    (EQUAL (LEN VARS) 1))
		       (AND (EQUAL (LEN (CDR VARS)) 0)
			    (TRUE-LISTP (CDR VARS))))))))


(defthm equal-values-and-attributes-in-boolean-case
 (implies
  (equal (type-expected rtmvars) 'Bool)
  (equal
   (equal-values-and-attributes gcell rtmvars rtmmem 'Bool)
   (and
    (equal
     (var-value (get-cell (car rtmvars) rtmmem))
     (var-value gcell))
    (equal
     (var-attribute gcell)
     (var-attribute (get-cell (car rtmvars) rtmmem)))))))





(defthm type-is-for-pars-equ
 (implies
   (and
    (true-listp m)
    (vars-inclusion (mem gstate) m)
    (gem-statep gstate)
    (correct-wrt-arity m (mem gstate))
    (equal gvar1 (par1 (nth (pcc gstate) (code gstate))))
    (equal gvar2 (par2 (nth (pcc gstate) (code gstate))))
    (equal gvar3 (par3 (nth (pcc gstate) (code gstate))))
    (equal (opcode (nth (pcc gstate) (code gstate))) 'gem-equ)
    (in-range (pcc gstate) (code gstate)))
   (equal (type-i gvar1 m) 'bool))
 :hints (("Goal"
	  :in-theory nil ;(current-theory 'ground-zero)
	  :use ( properies-of-type-and-existence-of-current-args-equ
		 (:instance type-i-is-vartyper (gvar1 gvar1) (mem (mem gstate)))
		 (:instance inclusion-trans (m1 (mem gstate)) (m2 m)
			    (v (par1 (nth (pcc gstate) (code gstate))))))))
:rule-classes nil)





(defthm goal15
(IMPLIES
 (INTEGERP VAR-VALUE-GCELL2)
 (EQUAL (BUILD-VALUES-BY-RNS-EXTENDED-FOR-NIL VAR-VALUE-GCELL2
					      '(11 13 15 17 19))
	(LIST (MOD VAR-VALUE-GCELL2 11)
	      (MOD VAR-VALUE-GCELL2 13)
	      (MOD VAR-VALUE-GCELL2 15)
	      (MOD VAR-VALUE-GCELL2 17)
	      (MOD VAR-VALUE-GCELL2 19))))
:hints (("Goal" :use (
		      (:instance build-values-by-rns-extended-for-nil
				 (gem-value VAR-VALUE-GCELL2)
				 (rns '(11 13 15 17 19)))
		      (:instance build-values-by-rns-extended-for-nil
				 (gem-value VAR-VALUE-GCELL2)
				 (rns '(13 15 17 19)))
		      (:instance build-values-by-rns-extended-for-nil
				 (gem-value VAR-VALUE-GCELL2)
				 (rns '(15 17 19)))
		      (:instance build-values-by-rns-extended-for-nil
				 (gem-value VAR-VALUE-GCELL2)
				 (rns '(17 19)))
		      (:instance build-values-by-rns-extended-for-nil
				 (gem-value VAR-VALUE-GCELL2)
				 (rns '(19)))
		      (:instance build-values-by-rns-extended-for-nil
				 (gem-value VAR-VALUE-GCELL2)
				 (rns nil)))))
:rule-classes nil)

(defthm var-values-of-n-list
 (equal
  (var-values (make-n-list gvar n) mem)
  (make-n-list (var-value (get-cell gvar mem)) n))
 :rule-classes nil)

(defthm make-n-list-expansion-5
 (equal
  (make-n-list el 5)
  (list el el el el el))
 :hints (("Goal" :use
	  ( (:instance make-n-list (n 5))
 	    (:instance make-n-list (n 4))
	    (:instance make-n-list (n 3))
	    (:instance make-n-list (n 2))
	    (:instance make-n-list (n 1))
	    (:instance make-n-list (n 0)) ) ))
 :rule-classes nil)



(defthm subgoal41
(IMPLIES
 (EQUAL (VAR-VALUE (GET-CELL RTMINTVARS-I-GVAR3 RTMMEM))
                     1)
         (EQUAL (VAR-VALUES (MAKE-N-LIST RTMINTVARS-I-GVAR3 5)
                            RTMMEM)
                '(1 1 1 1 1)))
:hints (("Goal" :use ( (:instance make-n-list-expansion-5 (el (VAR-VALUE (GET-CELL RTMINTVARS-I-GVAR3 RTMMEM))))
		       (:instance var-values-of-n-list
				  (gvar RTMINTVARS-I-GVAR3)
				  (n 5)
				  (mem rtmmem)))))
:rule-classes nil)

(defthm subgoal21
(IMPLIES
 (EQUAL (VAR-VALUE (GET-CELL RTMINTVARS-I-GVAR3 RTMMEM))
                     0)
         (EQUAL (VAR-VALUES (MAKE-N-LIST RTMINTVARS-I-GVAR3 5)
                            RTMMEM)
                '(0 0 0 0 0)))
:hints (("Goal" :use ( (:instance make-n-list-expansion-5 (el (VAR-VALUE (GET-CELL RTMINTVARS-I-GVAR3 RTMMEM))))
		       (:instance var-values-of-n-list
				  (gvar RTMINTVARS-I-GVAR3)
				  (n 5)
				  (mem rtmmem)))))
:rule-classes nil)



(defthm var-values-of-evmakelist-is-rns-anyway
 (implies
  (and
   (is-mem-cell-p gcell2)
   (equal (type-expected rtmintvars-i-gvar2) (var-type gcell2))
   (equal-values-and-attributes gcell2 rtmintvars-i-gvar2 rtmmem (var-type gcell2)))
  (equal
   (var-values (eventually-make-list rtmintvars-i-gvar2 (len *rns*)) rtmmem)
   (build-values-by-rns (var-value gcell2) *rns*)))
 :hints (("Goal" :in-theory (enable my-or-2))
	 ("Subgoal 5'''" :use (:instance goal15 (var-value-gcell2 (var-value gcell2))))
; fcd/Satriani v3.7 Moore - used to Subgoal 4.1
	 ("Subgoal 1.1" :use subgoal41)
; fcd/Satriani v3.7 Moore - used to Subgoal 2.1
	 ("Subgoal 3.1" :use subgoal21)))



(defthm ax-on-rns-values
  (implies
   (and
    (natp gval1)
    (< gval1 (prod *rns*))
    (natp gval2)
    (< gval2 (prod *rns*))
    (not (equal gval1 gval2)))
   (not (equal (build-values-by-rns gval1 *rns*) (build-values-by-rns gval2 *rns*))))
  :hints (("Goal" :use ( fact-bout-rns
			 (:instance crt-inversion (val gval1) (rns *rns*))
			 (:instance crt-inversion (val gval2) (rns *rns*))))))

(defthm hlp1
  (implies
   (and
    (is-mem-cell-p cell)
    (bounded-value cell))
   (and
    (natp (var-value cell))
    (< (var-value cell) (prod *rns*))))
  :rule-classes nil)

(defthm equal-equality-of-var-values-euqlity-of-evlists
 (implies
  (and
   (is-mem-cell-p gcell2)
   (is-mem-cell-p gcell3)
   (bounded-value gcell2)
   (bounded-value gcell3)
   (equal (type-expected rtmintvars-i-gvar2) (var-type gcell2))
   (equal (type-expected rtmintvars-i-gvar3) (var-type gcell3))
   (equal-values-and-attributes gcell2 rtmintvars-i-gvar2 rtmmem (var-type gcell2))
   (equal-values-and-attributes gcell3 rtmintvars-i-gvar3 rtmmem (var-type gcell3)))
 (equal
  (equal
   (var-value gcell2)
   (var-value gcell3) )
  (equal
   (var-values (eventually-make-list rtmintvars-i-gvar2  (len *rns*)) rtmmem)
   (var-values (eventually-make-list rtmintvars-i-gvar3  (len *rns*)) rtmmem))))
 :hints (("Goal"
	  :in-theory nil
	  :use
	  ( (:instance hlp1 (cell gcell2))
	    (:instance hlp1 (cell gcell3))
	    (:instance ax-on-rns-values
		       (gval1 (var-value gcell2))
		       (gval2 (var-value gcell3)))
	    (:instance var-values-of-evmakelist-is-rns-anyway
		       (gcell2 gcell2)
		       (rtmintvars-i-gvar2 rtmintvars-i-gvar2))
	    (:instance var-values-of-evmakelist-is-rns-anyway
		       (gcell2 gcell3)
		       (rtmintvars-i-gvar2 rtmintvars-i-gvar3))))))

(in-theory (disable ax-on-rns-values))





(defthm length-of-makelist-n
 (implies
  (and
   (integerp n)
   (>= n 0))
  (equal (len (make-n-list l n)) n)))

(defthm if-type-exepcted-is-ok-eventually-always-has-len-of-rns
 (implies
  (my-or-2
   (equal (type-expected l) 'Bool)
   (equal (type-expected l) 'Int))
  (equal (len (eventually-make-list l (len *rns*))) (len *rns*))))

(defthm tmp-never-appears
  (implies
   (and
    (no-tmp-into-mapping m)
    (assoc-equal gvar1 m))
   (not (member-equal-bool 'tmp (eventually-make-list (rtmintvars-i gvar1 m) n))))
  :hints (("Goal" :in-theory (enable rtmintvars-0))))

(defthm tmp-never-appears-simple
  (implies
   (and
    (no-tmp-into-mapping m)
    (assoc-equal gvar1 m))
   (not (member-equal-bool 'tmp (rtmintvars-i gvar1 m) )))
  :hints (("Goal" :in-theory (enable rtmintvars-0))))

(defthm type-of-a-mem-cell
  (implies
   (is-mem-cell-p cell)
   (my-or-2
    (equal (var-type cell) 'Bool)
    (equal (var-type cell) 'Int)))
  :hints (("Goal" :in-theory (enable my-or-2)))
  :rule-classes nil)


(defthm sillllly
 (equal (make-n-list l1 1) (list l1))
 :hints (("Goal" :use (:instance make-n-list (el l1) (n 1))))
 :rule-classes nil)

; Added by Matt K. for v3-5.  Heuristic changes to linear arithmetic were
; preventing the next lemma, not-member-equal-bool-holds-on-ev, from going
; through.  But the original proof involved generalization and three levels of
; induction, so rather than investigate further, we'll just prove the following
; lemma.  With it, the proof of not-member-equal-bool-holds-on-ev goes through
; without :hints.
(local
 (defthm helper-from-matt-k
   (implies (not (equal el l1))
            (not (member-equal-bool el (make-n-list l1 n))))))

(defthm not-member-equal-bool-holds-on-ev
 (implies
  (and
   (integerp n)
   (> n 0)
   (not (member-equal-bool el l)))
  (not (member-equal-bool el (eventually-make-list l n))))
 :hints (("Subgoal *1.1/4''" :use sillllly) ; Modified for v2-6 by Matt K.
	 ("Subgoal *1.1/4.1"  :use sillllly))
 :rule-classes nil)

(defthm not-memb-1
 (implies
  (and
   (true-listp m)
   (equal (len (rtmintvars-i gvar1 m)) 1)
   (assoc-equal gvar1 m)
   (assoc-equal gvar2 m)
   (no-duplicates-p (append-lists (retrieve-rtmvars m)))
   (not (equal gvar1 gvar2)))
  (not (member-equal-bool
	(car (rtmintvars-i gvar1 m))
	(rtmintvars-i gvar2 m))))
 :hints (("Goal"
	  :use ( (:instance lemma1-different-vars-do-not-belong (idx1 0)))))
 :rule-classes nil)

(defthm not-memb-2
 (implies
  (and
   (true-listp m)
   (equal (len (rtmintvars-i gvar1 m)) 1)
   (assoc-equal gvar1 m)
   (assoc-equal gvar2 m)
   (no-duplicates-p (append-lists (retrieve-rtmvars m)))
   (not (equal gvar1 gvar2)))
  (not (member-equal-bool
	(car (rtmintvars-i gvar1 m))
	(eventually-make-list (rtmintvars-i gvar2 m) (len *rns*)))))
 :hints (("Goal"
	  :use ( not-memb-1
		 (:instance not-member-equal-bool-holds-on-ev
			    (el (car (rtmintvars-i gvar1 m)))
			    (l (rtmintvars-i gvar2 m))
			    (n (len *rns*))))))
 :rule-classes nil)


(defthm eq-and-update-behaviour
  (and
   (equal
    (var-value (gen-eq-update c1 c2 c3 mem))
    (boolean-to-int (equal
		     (var-value (get-cell c2 mem))
		     (var-value (get-cell c3 mem)))))
   (equal
    (var-attribute (gen-eq-update c1 c2 c3 mem))
    (var-attribute (get-cell c1 mem))))
  :hints (("Goal" :in-theory (enable var-value var-attribute))))


(defthm var-attribute-of-a-var-is-same-after-n-steps
 (implies
  (rtm-statep st)
  (equal (var-attribute (get-cell anyvar (mem st)))
	 (var-attribute (get-cell anyvar (mem (execute-n-instructions st n))))))
 :hints (("Goal"
	  :induct (execute-n-instructions st n)
	  :in-theory (disable rtm-statep execute-instruction))
	 ("Subgoal *1/2"
	  :use
	  (
	   (:instance execute-instruction-is-type-and-attribute-invariant-on-any-var (cell anyvar))
	   executing-rtm-instruction-retrieves-a-rtm-state-from-rtm-state))))


(defthm bool-to-int-strip
 (iff
  (equal (boolean-to-int (equal a b)) (boolean-to-int (equal-values c d)))
  (equal (equal a b) (equal c d))))


(defthm equal-equality-of-var-values-euqlity-of-evlists-2
 (implies
  (and
   (is-mem-cell-p gcell2)
   (is-mem-cell-p gcell3)
   (bounded-value gcell2)
   (bounded-value gcell3)
   (equal (type-expected rtmintvars-i-gvar2) (var-type gcell2))
   (equal (type-expected rtmintvars-i-gvar3) (var-type gcell3))
   (equal-values-and-attributes gcell2 rtmintvars-i-gvar2 rtmmem (var-type gcell2))
   (equal-values-and-attributes gcell3 rtmintvars-i-gvar3 rtmmem (var-type gcell3)))
 (equal
  (boolean-to-int
   (equal
    (var-value gcell2)
    (var-value gcell3) ))
  (boolean-to-int
   (equal-values
    (var-values (eventually-make-list rtmintvars-i-gvar2  (len *rns*)) rtmmem)
    (var-values (eventually-make-list rtmintvars-i-gvar3  (len *rns*)) rtmmem)))))
 :hints (("Goal"
	  :in-theory nil
	  :use
	  ((:instance bool-to-int-strip
		     (a (var-value gcell2))
		     (b (var-value gcell3))
		     (c (var-values (eventually-make-list rtmintvars-i-gvar2  (len *rns*)) rtmmem))
		     (d (var-values (eventually-make-list rtmintvars-i-gvar3  (len *rns*)) rtmmem)))
		     equal-equality-of-var-values-euqlity-of-evlists))))



(defthm sil-support-2
 (implies
  (and
   (integerp n)
   (> n 0)
   (or
    (equal (type-expected l) 'Bool)
    (equal (type-expected l) 'Int)))
   (not (endp (eventually-make-list l n))))
 :hints (("Subgoal *1.1/3'" :use sillllly))
 :otf-flg t)

(defthm sil-support-3
 (implies
  (my-or-2
   (equal (type-expected l) 'Bool)
   (equal (type-expected l) 'Int))
   (not (endp (eventually-make-list l (len *rns*)))))
 :hints (("Goal" :use (:instance sil-support-2 (n (len *rns*))))))


(defthm not-in-car-if-no-memb
 (implies
  (and
   (equal (len l) 1)
   (not (member-equal-bool 'tmp l)))
  (not (equal 'tmp (car l)))))

(defthm sil-support-1
 (implies
  (equal (type-i gvar1 m) 'bool)
  (equal  (LEN (RTMINTVARS-I gvar1 m)) 1)))


(defthm bounded-are-bounded
 (implies
  (and
   (bounded-amem-p mem)
   (assoc-equal cell mem))
  (bounded-value (get-cell cell mem)))
 :hints (("Goal" :in-theory (enable get-cell)))
 :rule-classes nil)




(defthm m-correspondence-kept-on-same-gvar-equ
 (implies
  (and
    (NOT (ENDP (EVENTUALLY-MAKE-LIST
                    (RTMINTVARS-I (PAR2 (NTH (PCC GSTATE) (CODE GSTATE)))
                                  M)
                    (LEN '(11 13 15 17 19)))))
    (NOT (EQUAL 'TMP
                (CAR (RTMINTVARS-I (PAR1 (NTH (PCC GSTATE) (CODE GSTATE)))
                                   M))))
    (EQUAL (LEN (RTMINTVARS-I (PAR1 (NTH (PCC GSTATE) (CODE GSTATE))) M)) 1)
   (equal (opcode (nth (pcc gstate) (code gstate))) 'gem-equ)
   (no-tmp-into-mapping m)
   (good-translation-gem-rtm gstate rstate m)
   (vars-inclusion (mem gstate) m)
   (true-listp m)
   (assoc-equal gvar1 m)
   (gem-statep gstate)
   (rtm-statep rstate)
   (in-range (pcc gstate) (code gstate))
   (in-range (pcc rstate) (code rstate))
   (equal gvar1 (par1 (nth (pcc gstate) (code gstate))))
   (m-correspondent-values-p m (mem gstate) (mem rstate))
   (no-duplicates-p (append-lists (retrieve-rtmvars m)))
   (correct-wrt-arity m (mem gstate)))
  (equal-values-and-attributes
   (get-cell gvar1 (mem (execute-instruction gstate)))
   (rtmintvars-i gvar1 m)
   (mem (execute-n-instructions rstate (* 2 (len *rns*))))
   (type-i gvar1 m)))
 :hints (("Goal" :in-theory nil
	  :use (
		(:instance gem-statep (x gstate))
		(:instance bounded-are-bounded (cell (par2 (nth (pcc gstate) (code gstate)))) (mem (mem gstate)))
		(:instance bounded-are-bounded (cell (par3 (nth (pcc gstate) (code gstate)))) (mem (mem gstate)))
		(:instance  eq-and-update-behaviour
			    (c1 gvar1)
			    (c2 (par2 (nth (pcc gstate) (code gstate))))
			    (c3 (par3 (nth (pcc gstate) (code gstate))))
			    (mem (mem gstate)))
		(:instance var-attribute-of-a-var-is-same-after-n-steps
			    (st rstate)
			    (anyvar (car  (rtmintvars-i (par1 (nth (pcc gstate) (code gstate))) m)))
			    (n (* 2 (len *rns*))))
		 (:instance in-range (idx (pcc gstate)) (l (code gstate)))
		 (:instance not-memb-2
			    (gvar1 (par1 (nth (pcc gstate) (code gstate))))
			    (gvar2 (par2 (nth (pcc gstate) (code gstate)))))
		 (:instance not-memb-2
			    (gvar1 (par1 (nth (pcc gstate) (code gstate))))
			    (gvar2 (par3 (nth (pcc gstate) (code gstate)))))
		 (:instance type-of-a-mem-cell (cell (get-cell (par2 (nth (pcc gstate) (code gstate))) (mem gstate))))
		 (:instance type-of-a-mem-cell (cell (get-cell (par3 (nth (pcc gstate) (code gstate))) (mem gstate))))
		 properies-of-type-and-existence-of-current-args-equ
		 mem-cellity-of-current-gem-args-equ
		 good-translation-gem-rtm
		 (:instance tmp-never-appears (n (len *rns*)) (gvar1 (par2 (nth (pcc gstate) (code gstate)))))
		 (:instance tmp-never-appears (n (len *rns*)) (gvar1 (par3 (nth (pcc gstate) (code gstate)))))
		 (:instance if-type-exepcted-is-ok-eventually-always-has-len-of-rns
			    (l (rtmintvars-i (par2 (nth (pcc gstate) (code gstate))) m)))
		 (:instance if-type-exepcted-is-ok-eventually-always-has-len-of-rns
			    (l (rtmintvars-i (par3 (nth (pcc gstate) (code gstate))) m)))
		 (:instance type-i-is-vartyper (gvar1 gvar1) (mem (mem gstate)))
		 (:instance type-i-is-vartyper (gvar1 (par2 (nth (pcc gstate) (code gstate)))) (mem (mem gstate)))
		 (:instance type-i-is-vartyper (gvar1 (par3 (nth (pcc gstate) (code gstate)))) (mem (mem gstate)))
		 (:instance type-i-is-type-expected (gvar  gvar1) (mem (mem gstate)))
		 (:instance type-i-is-type-expected (gvar  (par2 (nth (pcc gstate) (code gstate)))) (mem (mem gstate)))
		 (:instance type-i-is-type-expected (gvar  (par3 (nth (pcc gstate) (code gstate)))) (mem (mem gstate)))
		 (:instance inclusion-trans (m1 (mem gstate)) (m2 m)
			    (v (par1 (nth (pcc gstate) (code gstate)))))
		 (:instance inclusion-trans (m1 (mem gstate)) (m2 m)
			    (v (par2 (nth (pcc gstate) (code gstate)))))
		 (:instance inclusion-trans (m1 (mem gstate)) (m2 m)
			    (v (par3 (nth (pcc gstate) (code gstate)))))
		  (:instance
		   equal-eq-update-norest-afetr-one-instr
		   (gvar2 (par2 (nth (pcc gstate) (code gstate))))
		   (gvar3 (par3 (nth (pcc gstate) (code gstate))))
		   )
		  (:instance type-is-for-pars-equ
		   (gvar2 (par2 (nth (pcc gstate) (code gstate))))
		   (gvar3 (par3 (nth (pcc gstate) (code gstate)))))
		  (:instance equal-values-and-attributes-in-boolean-case
			     (rtmvars (rtmintvars-i gvar1 m))
			     (gcell (get-cell gvar1 (mem gstate)))
			     (rtmmem (mem rstate)))
		  (:instance equal-values-and-attributes-in-boolean-case
			     (rtmvars (rtmintvars-i gvar1 m))
			     (gcell (get-cell gvar1 (mem (execute-instruction gstate))))
			     (rtmmem (mem (execute-n-instructions rstate (* 2 (len *rns*))))))
		  (:instance m-correspondent-values-implies-equal-values-and-attribus
			     (memgstate (mem gstate)) (memrstate (mem rstate))
			     (gvar1 (par1 (nth (pcc gstate) (code gstate)))))
		  (:instance m-correspondent-values-implies-equal-values-and-attribus
			     (memgstate (mem gstate)) (memrstate (mem rstate))
			     (gvar1 (par2 (nth (pcc gstate) (code gstate)))))
		  (:instance m-correspondent-values-implies-equal-values-and-attribus
			     (memgstate (mem gstate)) (memrstate (mem rstate))
			     (gvar1 (par3 (nth (pcc gstate) (code gstate)))))
		  (:instance value-of-result-after-executing-2n-+2instr-finale
			     (tmp 'tmp)
			     (res (car  (rtmintvars-i (par1 (nth (pcc gstate) (code gstate))) m)))
			     (listvars1 (eventually-make-list (rtmintvars-i (par2 (nth (pcc gstate) (code gstate))) m) (len *rns*)))
			     (listvars2 (eventually-make-list (rtmintvars-i (par3 (nth (pcc gstate) (code gstate))) m) (len *rns*)))
			     (st rstate))
		  (:instance equal-equality-of-var-values-euqlity-of-evlists-2
			     (gcell2 (get-cell (par2 (nth (pcc gstate) (code gstate))) (mem gstate)))
			     (gcell3 (get-cell (par3 (nth (pcc gstate) (code gstate))) (mem gstate)))
			     (rtmintvars-i-gvar2 (rtmintvars-i (par2 (nth (pcc gstate) (code gstate))) m))
			     (rtmintvars-i-gvar3 (rtmintvars-i (par3 (nth (pcc gstate) (code gstate))) m))
			     (rtmmem (mem rstate)))))))


(defthm m-correspondence-kept-on-same-gvar-equ-supp
 (implies
  (and
   (equal (opcode (nth (pcc gstate) (code gstate))) 'gem-equ)
   (no-tmp-into-mapping m)
   (equal gvar1 (par1 (nth (pcc gstate) (code gstate))))
   (assoc-equal gvar1 m)
   (vars-inclusion (mem gstate) m)
   (true-listp m)
   (gem-statep gstate)
   (rtm-statep rstate)
   (in-range (pcc gstate) (code gstate))
   (in-range (pcc rstate) (code rstate))
   (no-duplicates-p (append-lists (retrieve-rtmvars m)))
   (correct-wrt-arity m (mem gstate)))
  (and
   (NOT (ENDP (EVENTUALLY-MAKE-LIST
	       (RTMINTVARS-I (PAR2 (NTH (PCC GSTATE) (CODE GSTATE)))
			     M)
	       (LEN '(11 13 15 17 19)))))
   (NOT (EQUAL 'TMP
             (CAR (RTMINTVARS-I (PAR1 (NTH (PCC GSTATE) (CODE GSTATE)))
				  M))))
   (EQUAL (LEN (RTMINTVARS-I (PAR1 (NTH (PCC GSTATE) (CODE GSTATE))) M)) 1)))
 :hints (("Goal" :in-theory  nil
	  :use (
		(:instance sil-support-3 (l (RTMINTVARS-I (PAR2 (NTH (PCC GSTATE) (CODE GSTATE))) M) ))
		(:instance not-in-car-if-no-memb (l (RTMINTVARS-I (PAR1 (NTH (PCC GSTATE) (CODE GSTATE))) m)))
		(:instance sil-support-1 (gvar1 (PAR1 (NTH (PCC GSTATE) (CODE GSTATE)))))
		(:instance in-range (idx (pcc gstate)) (l (code gstate)))
		(:instance type-of-a-mem-cell (cell (get-cell (par2 (nth (pcc gstate) (code gstate))) (mem gstate))))
		(:instance type-of-a-mem-cell (cell (get-cell (par3 (nth (pcc gstate) (code gstate))) (mem gstate))))
		(:instance inclusion-trans (m1 (mem gstate)) (m2 m)
			   (v (par1 (nth (pcc gstate) (code gstate)))))
		(:instance inclusion-trans (m1 (mem gstate)) (m2 m)
			    (v (par2 (nth (pcc gstate) (code gstate)))))
		(:instance inclusion-trans (m1 (mem gstate)) (m2 m)
			   (v (par3 (nth (pcc gstate) (code gstate)))))
		 properies-of-type-and-existence-of-current-args-equ
		 mem-cellity-of-current-gem-args-equ
		 (:instance tmp-never-appears-simple  (gvar1 (par1 (nth (pcc gstate) (code gstate)))))
		 (:instance type-i-is-vartyper (gvar1 gvar1) (mem (mem gstate)))
		 (:instance type-i-is-vartyper (gvar1 (par2 (nth (pcc gstate) (code gstate)))) (mem (mem gstate)))
		 (:instance type-i-is-vartyper (gvar1 (par3 (nth (pcc gstate) (code gstate)))) (mem (mem gstate)))
		 (:instance type-i-is-type-expected (gvar  gvar1) (mem (mem gstate)))
		 (:instance type-i-is-type-expected (gvar  (par2 (nth (pcc gstate) (code gstate)))) (mem (mem gstate)))
		 (:instance type-i-is-type-expected (gvar  (par3 (nth (pcc gstate) (code gstate)))) (mem (mem gstate)))
		 (:instance inclusion-trans (m1 (mem gstate)) (m2 m)
			    (v (par1 (nth (pcc gstate) (code gstate)))))
		 (:instance inclusion-trans (m1 (mem gstate)) (m2 m)
			    (v (par2 (nth (pcc gstate) (code gstate)))))
		 (:instance inclusion-trans (m1 (mem gstate)) (m2 m)
			    (v (par3 (nth (pcc gstate) (code gstate)))))
		 (:instance type-is-for-pars-equ
			    (gvar2 (par2 (nth (pcc gstate) (code gstate))))
			    (gvar3 (par3 (nth (pcc gstate) (code gstate)))))))))



(defthm equal-values-correspondence-kept-by-any-execution-equ
  (implies
   (and
   (equal (opcode (nth (pcc gstate) (code gstate))) 'gem-equ)
   (no-tmp-into-mapping m)
   (good-translation-gem-rtm gstate rstate m)
   (vars-inclusion (mem gstate) m)
   (true-listp m)
   (assoc-equal gvar1 m)
   (gem-statep gstate)
   (rtm-statep rstate)
   (in-range (pcc gstate) (code gstate))
   (in-range (pcc rstate) (code rstate))
   (m-correspondent-values-p m (mem gstate) (mem rstate))
   (M-ENTRIES-POINT-TO-GOOD-RTM-VAR-SETS M (MEM RSTATE))
   (no-duplicates-p (append-lists (retrieve-rtmvars m)))
   (correct-wrt-arity m (mem gstate)))
  (equal-values-and-attributes
   (get-cell gvar1 (mem (execute-instruction gstate)))
   (rtmintvars-i gvar1 m)
   (mem (execute-n-instructions rstate (* 2 (len *rns*))))
   (type-i gvar1 m)))
  :hints (("Goal" :in-theory nil
	   :use (m-correspondence-kept-on-same-gvar-equ
		 m-correspondence-kept-on-same-gvar-equ-supp
		 teorema-main-con-pcc-in-range-su-variabile-non-interessata-final-equ))))


(defthm rtmintvars-i-iscdrnth
 (implies
  (and
   (true-listp m)
   (in-range idx m)
   (no-duplicates-p (retrieve-gemvars m)))
  (equal (rtmintvars-i (car (nth idx m)) m)
	 (cdr (nth idx m))))
 :hints (("Goal"
	  :in-theory nil
	  :use (
	  (:instance no-duplicates-has-pos-equal-right-in-that-place (l m))
	  (:instance  rtmintvars-i-is-cdr-of-nth-entry (gvar (car (nth idx m))))))))

(defthm type-i-is-typeidx
 (implies
  (and
   (true-listp m)
   (in-range idx m)
   (no-duplicates-p (retrieve-gemvars m)))
  (equal (type-i (car (nth idx m)) m)
	 (type-i-idx m idx))))



(defthm equal-values-correspondence-kept-by-any-execution-idxed-equ
  (implies
   (and
   (equal (opcode (nth (pcc gstate) (code gstate))) 'gem-equ)
   (no-tmp-into-mapping m)
   (good-translation-gem-rtm gstate rstate m)
   (vars-inclusion (mem gstate) m)
   (alistp m)
   (in-range idx m)
   (gem-statep gstate)
   (rtm-statep rstate)
   (in-range (pcc gstate) (code gstate))
   (in-range (pcc rstate) (code rstate))
   (m-correspondent-values-p m (mem gstate) (mem rstate))
   (M-ENTRIES-POINT-TO-GOOD-RTM-VAR-SETS M (MEM RSTATE))
   (no-duplicates-p (retrieve-gemvars m))
   (no-duplicates-p (append-lists (retrieve-rtmvars m)))
   (correct-wrt-arity m (mem gstate)))
  (equal-values-and-attributes
   (get-cell (car (nth idx m)) (mem (execute-instruction gstate)))
   (cdr (nth idx m))
   (mem (execute-n-instructions rstate (* 2 (len *rns*))))
   (type-i-idx m idx)))
  :hints (("Subgoal 2" :in-theory nil)
	  ("Goal" :in-theory (union-theories (current-theory 'ground-zero)
					     '((:definition in-range)))
	   :use ( (:theorem
		   (implies
		    (and
		     (alistp m)
		     (in-range idx m))
		    (and
		     (true-listp m)
		     (assoc-equal (car (nth idx m)) m))))

		  rtmintvars-i-iscdrnth
		  type-i-is-typeidx
		  (:instance equal-values-correspondence-kept-by-any-execution-equ (gvar1 (car (nth idx m)))))))
  :otf-flg t)




(defthm m-correspondence-kept-by-any-execution-idxed-equ
  (implies
   (and
   (equal (opcode (nth (pcc gstate) (code gstate))) 'gem-equ)
   (no-tmp-into-mapping m)
   (good-translation-gem-rtm gstate rstate m)
   (vars-inclusion (mem gstate) m)
   (alistp m)
   (gem-statep gstate)
   (rtm-statep rstate)
   (in-range (pcc gstate) (code gstate))
   (in-range (pcc rstate) (code rstate))
   (m-correspondent-values-p m (mem gstate) (mem rstate))
   (M-ENTRIES-POINT-TO-GOOD-RTM-VAR-SETS M (MEM RSTATE))
   (no-duplicates-p (retrieve-gemvars m))
   (no-duplicates-p (append-lists (retrieve-rtmvars m)))
   (correct-wrt-arity m (mem gstate)))
  (m-correspondent-values-p
   m
   (mem (execute-instruction gstate))
   (mem (execute-n-instructions rstate (* 2 (len *rns*))))))
  :hints (("Goal" :use (:instance equal-values-correspondence-kept-by-any-execution-idxed-equ
				  (idx (bad-idx-eqv-va m
						       (mem (execute-instruction gstate))
						       (mem (execute-n-instructions rstate (* 2 (len *rns*))))))))
	  ("Goal'" :cases ( (in-range (bad-idx-eqv-va m (mem (execute-instruction gstate))
						       (mem (execute-n-instructions rstate (* 2 (len *rns*))))) m)))
	  ("Subgoal 2" :in-theory '((:forward-chaining alistp-forward-to-true-listp)
				    (:rewrite if-bad-index-not-in-range-then-m-corr)))
	  ("Subgoal 1" :in-theory '((:rewrite if-bad-index-in-range-thne-must-be-different-vs)))))



(defthm m-correspondence-and-other-conditions-kept-by-any-execution-idxed-equ
  (implies
   (and
    (equal (opcode (nth (pcc gstate) (code gstate))) 'gem-equ)
    (no-tmp-into-mapping m)
    (good-translation-gem-rtm gstate rstate m)
    (vars-inclusion (mem gstate) m)
    (vars-inclusion m (mem gstate))
    (alistp m)
    (gem-statep gstate)
    (rtm-statep rstate)
    (in-range (pcc gstate) (code gstate))
    (in-range (pcc rstate) (code rstate))
    (m-correspondent-values-p m (mem gstate) (mem rstate))
    (M-ENTRIES-POINT-TO-GOOD-RTM-VAR-SETS M (MEM RSTATE))
    (no-duplicates-p (retrieve-gemvars m))
    (no-duplicates-p (append-lists (retrieve-rtmvars m)))
    (correct-wrt-arity m (mem gstate)))
   (and
    (good-translation-gem-rtm (execute-instruction gstate) (execute-n-instructions rstate (* 2 (len *rns*))) m)
    (rtm-statep (execute-n-instructions rstate (* 2 (len *rns*))))
    (m-entries-point-to-good-rtm-var-sets m (mem (execute-n-instructions rstate (* 2 (len *rns*)))))
    (gem-statep (execute-instruction gstate))
    (correct-wrt-arity m (mem (execute-instruction gstate)))
    (vars-inclusion (mem (execute-instruction gstate)) m)
    (vars-inclusion m (mem (execute-instruction gstate)))
    (m-correspondent-values-p
     m
     (mem (execute-instruction gstate))
     (mem (execute-n-instructions rstate (* 2 (len *rns*)))))))
  :hints (("Goal"
	   :in-theory ;nil
	   (disable
		       rtm-statep gem-statep
		       pcc code opcode
		       execute-instruction rtmintvars-i par1 par2 par3 nth len member-equal)
	   :use
	   (m-correspondence-kept-by-any-execution-idxed-equ
	    good-translation-gem-rtm
	    (:instance execute-n-instructions-keeps-rtm-state-and-points-to-good
		       (st rstate) (n (* 2 (len *rns*))))
	    (:instance executing-gem-instruction-retrieves-a-gem-state-from-gem-state (st gstate))
	    (:instance executing-gem-instruction-preserves-correctness-wrt-arity (st gstate))
	    (:instance executing-gem-instruction-keeps-vars-inclusion-right      (st gstate))
	    (:instance executing-gem-instruction-keeps-vars-inclusion-left       (st gstate))))))



(encapsulate
 ()
;;; Modified 12/24/2014 to avoid the nu-rewriter, which is being eliminated.
; (set-nu-rewriter-mode nil) ; to avoid skip-proofs below
 (defthm after-n-instructions-out-of-range-rtmstate-untouched
   (implies
    (and
     (rtm-statep rstate)
     (>= (pcc rstate) (len (code rstate))))
    (equal (execute-n-instructions rstate n) rstate))
   :hints (("Goal" :in-theory (enable execute-not-in-range-instruction-retrieves-same-state)))))



(defun correspondent-steps-to-current-gem-instruction (gstate)
    (case (opcode (nth (pcc gstate) (code gstate)))
      (gem-add  (len *rns*))
      (gem-sub  (len *rns*))
      (gem-equ  (* 2 (len *rns*)))
      (otherwise 0)))



(defun correspondent-steps (n gstate)
  (if (zp n)
      0
    (+ (correspondent-steps-to-current-gem-instruction gstate)
       (correspondent-steps (1- n) (execute-instruction gstate)))))





(defthm m-correspondence-and-other-conditions-kept-by-out-of-range-execution-2
  (implies
   (and
    (alistp m)
    (no-duplicates-p (retrieve-gemvars m))
    (no-duplicates-p (append-lists (retrieve-rtmvars m)))
    (good-translation-gem-rtm gstate rstate m)
    (correct-wrt-arity m (mem gstate))
    (gem-statep gstate)
    (rtm-statep rstate)
    (vars-inclusion (mem gstate) m)
    (vars-inclusion m (mem gstate))
    (not (in-range (pcc gstate) (code gstate)))
    (>= (pcc gstate) 0)
    (>= (pcc rstate) (len (code rstate)))
    (m-entries-point-to-good-rtm-var-sets m (mem rstate))
    (m-correspondent-values-p m (mem gstate) (mem rstate)))
   (and
    (good-translation-gem-rtm
     (execute-instruction gstate)
     (execute-n-instructions rstate
			     (correspondent-steps-to-current-gem-instruction gstate)) m)
    (rtm-statep (execute-n-instructions rstate (correspondent-steps-to-current-gem-instruction gstate)))
    (m-entries-point-to-good-rtm-var-sets
     m
     (mem (execute-n-instructions rstate (correspondent-steps-to-current-gem-instruction gstate))))
    (gem-statep (execute-instruction gstate))
    (correct-wrt-arity m (mem (execute-instruction gstate)))
    (vars-inclusion (mem (execute-instruction gstate)) m)
    (vars-inclusion m (mem (execute-instruction gstate)))
    (m-correspondent-values-p
     m
     (mem (execute-instruction gstate))
     (mem (execute-n-instructions rstate (correspondent-steps-to-current-gem-instruction gstate))))))
  :hints (("Goal"
	   :in-theory '((in-range))
	   :use
	   (
	    (:instance after-n-instructions-out-of-range-rtmstate-untouched
		       (n (correspondent-steps-to-current-gem-instruction gstate)))
	     (:instance execute-not-in-range-instruction-retrieves-same-state (st gstate))))))





(defthm m-correspondence-and-other-conditions-kept-execution-2
  (implies
   (and
    (alistp m)
    (no-tmp-into-mapping m)
    (no-duplicates-p (retrieve-gemvars m))
    (no-duplicates-p (append-lists (retrieve-rtmvars m)))
    (good-translation-gem-rtm gstate rstate m)
    (correct-wrt-arity m (mem gstate))
    (gem-statep gstate)
    (rtm-statep rstate)
    (vars-inclusion (mem gstate) m)
    (vars-inclusion m (mem gstate))
    (>= (pcc gstate) 0)
    (m-entries-point-to-good-rtm-var-sets m (mem rstate))
    (m-correspondent-values-p m (mem gstate) (mem rstate)))
   (and
    (>= (pcc (execute-instruction gstate)) 0)
    (good-translation-gem-rtm
     (execute-instruction gstate)
     (execute-n-instructions rstate (correspondent-steps-to-current-gem-instruction gstate)) m)
    (rtm-statep (execute-n-instructions rstate (correspondent-steps-to-current-gem-instruction gstate)))
    (m-entries-point-to-good-rtm-var-sets
     m
     (mem (execute-n-instructions rstate (correspondent-steps-to-current-gem-instruction gstate))))
    (gem-statep (execute-instruction gstate))
    (correct-wrt-arity m (mem (execute-instruction gstate)))
    (vars-inclusion (mem (execute-instruction gstate)) m)
    (vars-inclusion m (mem (execute-instruction gstate)))
    (m-correspondent-values-p
     m
     (mem (execute-instruction gstate))
     (mem (execute-n-instructions rstate (correspondent-steps-to-current-gem-instruction gstate))))))
   :hints (("Goal" :in-theory '((:definition in-range))
	    :use ((:instance instruction-incrementing-pvv (st gstate))
			 correspondent-steps-to-current-gem-instruction
			 good-translation-gem-rtm
			 m-correspondence-and-other-conditions-kept-by-out-of-range-execution-2
			 m-correspondence-and-other-conditions-kept-by-any-execution-add
			 m-correspondence-and-other-conditions-kept-by-any-execution-sub
			 m-correspondence-and-other-conditions-kept-by-any-execution-idxed-equ))))














(defun parallel-exec (gstate rstate n)
  (if (zp n)
      (list gstate rstate)
    (parallel-exec
     (execute-instruction gstate)
     (execute-n-instructions rstate (correspondent-steps-to-current-gem-instruction gstate))
     (1- n))))












(defthm m-correspondence-and-other-conditions-kept-execution-on-n
  (implies
   (and
    (integerp n)
    (>= n 0)
    (alistp m)
    (no-duplicates-p (retrieve-gemvars m))
    (no-duplicates-p (append-lists (retrieve-rtmvars m)))
    (no-tmp-into-mapping m)
    (good-translation-gem-rtm gstate rstate m)
    (correct-wrt-arity m (mem gstate))
    (gem-statep gstate)
    (rtm-statep rstate)
    (vars-inclusion (mem gstate) m)
    (vars-inclusion m (mem gstate))
    (>= (pcc gstate) 0)
    (m-entries-point-to-good-rtm-var-sets m (mem rstate))
    (m-correspondent-values-p m (mem gstate) (mem rstate)))
   (and
    (>= (pcc (execute-n-instructions gstate n)) 0)
    (good-translation-gem-rtm
     (execute-n-instructions gstate n)
     (execute-n-instructions rstate (correspondent-steps n gstate)) m)
    (rtm-statep (execute-n-instructions rstate (correspondent-steps n gstate)))
    (m-entries-point-to-good-rtm-var-sets
     m
     (mem (execute-n-instructions rstate (correspondent-steps n gstate))))
    (gem-statep (execute-n-instructions gstate n))
    (correct-wrt-arity m (mem (execute-n-instructions gstate n)))
    (vars-inclusion (mem (execute-n-instructions gstate n)) m)
    (vars-inclusion m (mem (execute-n-instructions gstate n)))
    (m-correspondent-values-p
     m
     (mem (execute-n-instructions gstate n))
     (mem (execute-n-instructions rstate (correspondent-steps n gstate))))))
  :hints (("Goal" :in-theory
	   ;(current-theory 'ground-zero)
	   (disable executing-gem-instruction-preserves-correctness-wrt-arity
				      execute-instruction-is-type-and-attribute-invariant-on-any-var
				      ;executing-gem-instruction-is-type-attribute-invariant
				      executing-gem-instruction-keeps-vars-inclusion-left
				      executing-gem-instruction-keeps-vars-inclusion-right
				      execute-n-instructions-keeps-rtm-state-and-points-to-good
				      correspondent-steps-to-current-gem-instruction
				      execute-n-instructions-tantamount-to-add-list-e
				      m-correspondence-and-other-conditions-kept-by-any-execution-add
				      m-correspondence-and-other-conditions-kept-by-any-execution-sub
				      m-correspondence-and-other-conditions-kept-by-any-execution-idxed-equ
				      m-correspondence-and-other-conditions-kept-by-out-of-range-execution-2
				      executing-gem-instruction-retrieves-a-gem-state-from-gem-state
				      executing-rtm-instruction-retrieves-a-rtm-state-from-rtm-state
				      instruction-incrementing-pvv
				      good-translation-gem-rtm
				      all-rtm-adds-for-n-steps
				      null-opcode-implies-execution-does-not-touch-state
				      bad-idx-eqv-va
				      mem pcc code opcode retrieve-rtmvars gem-statep rtm-statep execute-instruction)
	  :induct (parallel-exec gstate rstate n))
	  ("Subgoal *1/2" :use
	   (
	    (:instance execute-n-instruction-decomposition
		      (n1 (correspondent-steps (1- n) gstate))
		      (n2 (correspondent-steps-to-current-gem-instruction gstate))
		      (st rstate))
	    (:instance m-correspondence-and-other-conditions-kept-execution-2
		       (gstate (execute-instruction gstate))
		       (rstate (execute-n-instructions rstate (correspondent-steps-to-current-gem-instruction gstate))))))))




(defthm simple-fact-about-initial-gemstate
 (implies
  (gem-program-p gemprog)
 (and
  (>= (pcc (initial-state gemprog)) 0)
  (gem-statep (initial-state gemprog)))))

(defthm simple-fact-about-initial-rtmstate
 (implies
  (rtm-program-p rtmprog)
 (and
  (>= (pcc (initial-state rtmprog)) 0)
  (rtm-statep (initial-state rtmprog)))))


(defun good-mapping (m)
  (and
   (alistp m)
   (no-tmp-into-mapping m)
   (no-duplicates-p (retrieve-gemvars m))
   (no-duplicates-p (append-lists (retrieve-rtmvars m)))))

(defun good-mapping-wrt-memories (m mem-gstate mem-rstate)
  (and
   (correct-wrt-arity m mem-gstate)
   (vars-inclusion mem-gstate m)
   (vars-inclusion m mem-gstate)
   (m-entries-point-to-good-rtm-var-sets m mem-rstate)
   (m-correspondent-values-p m mem-gstate mem-rstate)))




(defun correct-translation (gemprog rtmprog m)
  (good-translation-gem-rtm (initial-state gemprog) (initial-state rtmprog) m))


(defthm execution-of-correctly-translated-gem-and-rtm-yields-same-output
  (let
      ((gstate (initial-state gemprog))
       (rstate (initial-state rtmprog))
       (n (len (code gstate))))
  (implies
   (and
    (gem-program-p gemprog)
    (rtm-program-p rtmprog)
    (good-mapping m)
    (good-mapping-wrt-memories m (mem gstate) (mem rstate))
    (correct-translation gemprog rtmprog m))
   (equal-memories
    (decode m (projectio (mem (execute-n-instructions rstate (correspondent-steps n gstate))) attr))
    (projectio (mem (execute-n-instructions gstate n)) attr))))
  :hints (("Goal"
	   :in-theory (union-theories (current-theory 'ground-zero)
				      '((:rewrite equalities-on-io)
					(:definition correct-translation)
					(:definition good-mapping-wrt-memories)
					(:definition gem-statep)
					(:definition rtm-statep)
					(:definition good-mapping)))
	   :use
	   (
	    fact-bout-rns
	    simple-fact-about-initial-rtmstate
	    simple-fact-about-initial-gemstate
	    (:instance m-correspondence-and-other-conditions-kept-execution-on-n
		       (gstate (initial-state gemprog))
		       (rstate (initial-state rtmprog))
		       (n (len (code gstate))))))))


