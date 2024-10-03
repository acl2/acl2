;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; MI-inv.lisp
; Author  Jun Sawada, University of Texas at Austin
;
;  This book defines a three stage pipelined multiplier.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(in-package "ACL2")

(include-book "b-ops-aux-def")
(include-book "basic-def")


(deflabel begin-def-multiplier)

;; (Logical) shift left by 1-bit. 
(defun shift-1 (val)
  (declare (xargs :guard (word-p val)))
  (word (logcons 0 val)))

;; A shifted value generator.
;; In C specification:
;; (shifter n m1 m2) = ((0x1<<n)&m1) ? m2<<n : 0
(defun shifter (n multiplicand multiplier)
  (declare (xargs :guard (and (integerp n) (>= n 0)
			      (word-p multiplicand)
			      (word-p multiplier))))
  (b-if (logbit n multiplier) 
	(word (logapp n 0 multiplicand))
	0))
  

;; A carry save adder is defined by CSA-out and CSA-carry.  A carry
;; save adder takes three bit vectors and returns a sum vector and a
;; carry vector, whose values are represented by functions CSA-out and
;; CSA-carry, respectively.  Intuitively CSA-out and CSA-carry
;; satisfy:
;; (CSA-out x y z) + ((CSA-carry x y z) << 1) = x + y + z.
;; For a precise argument, see the lemma CSA-is-adder in
;; multiplier.lisp.
(defun CSA-out (val1 val2 carry)
  (declare (xargs :guard (and (word-p val1) (word-p val2) (word-p carry))))
  (logxor (logxor val1 val2) carry))

(defun CSA-carry (val1 val2 carry)
  (declare (xargs :guard (and (word-p val1) (word-p val2) (word-p carry))))
  (logior (logand val1 val2)
	  (logior (logand val1 carry)
		  (logand val2 carry))))

(defthm shift-1-word-p
    (word-p (shift-1 x)))

(defthm word-p-shifter
    (word-p (shifter n val1 val2)))

(defthm word-p-CSA-out 
    (implies (and (word-p val1)
		  (word-p val2)
		  (word-p carry))
	     (word-p (CSA-out val1 val2 carry))))

(defthm word-p-CSA-carry
    (implies (and (word-p val1)
		  (word-p val2)
		  (word-p carry))
	     (word-p (CSA-carry val1 val2 carry))))

(in-theory (disable word-p-CSA-out word-p-CSA-carry shift-1 shifter))

#|				  
The following figure shows our Wallace Tree Multiplier implementation.
The product is calculated by three phases:

1 A Shifted Vector Generator outputs 16 shifted bit vectors.
2 Six layers of CSA's add the 16 shifted vectors into two vectors.
3 A carry propagate adder adds the last two vectors into the final result.

The multiplier is pipelined into three stages.  However, these stages are
not aligned to the three phases of the multiplier shown above.  The
first stage ML1 generates shifted vectors and uses three layers of
CSA's to output six partial sums.  The next stage ML2 further
adds the sums using additional three layers of CSA's and outputs two
partial sums.  The final stage ML3 adds the two partial sums to
the final result.

Our 16-bit multiplier throws away the most significant 16bits of
32bits full product.  So, the adders and the internal busses have only
16-bit widths.

From the structure of the multiplier, we can guess how the ML1/ML2 and
ML2/ML3 latches should look like.  Latch ML1/ML2 should be able to
hold six 16-bit partial sums, while ML2/ML3 must be able to hold two
partial sums.  Note also that output values from the CSA's in the ML1
stage depend on the multiplicand and multiplier supplied from an
earlier stage while the values from CSA's in ML2 depend on the six
partial sums supplied from ML1/ML2.

						 
             ( multiplier, multiplicand)          DC/EX  latch		 
       __________________|_____________________	 
       | | |   | | |   | | |   | | |   | | |  |  
      151413  121110   9 8 7   6 5 4   3 2 1  0	 shifted vectors
       | | |   | | |   | | |   | | |   | | |  |
       | | |   | | |   | | |   | | |   | | |  |
       C S A   C S A   C S A   C S A   C S A  |
       	| |	| |     | |     | |     | |  / 
	| |     | |     | |     | |     | | |
	| |      \ \   /   \   / /      | | |
	 \ \      | | |     | | |       | | |
	  \ \     | | |     | | |       | | |
	   \ \    C S A     C S A       C S A             	           
	    \ \	   | | 	     | |       	 | |
	     \ \   | |	     | |         | |
	      \ \  |  \     / /         / /
	       | | |   \   / /         / /  
	       | | |    | | |	      /	/   
	       | | |    | | |        / /
               C S A    C S A       / /
	        | |      | |       / /
	        | |      | |      / /
	         \ \     | |   	 / /
	          \ \   /  |  	/ /
       	       	   | | |    \  | |
		   | | |     | | |  
                  s1s2s3    s4s5s6   ML1/ML2 latch
		   | | |     | | |
        	   C S A     C S A
        	    | |       | |  
        	    |  \      | |  
        	    |  	\    / /   
                    |    \  | |   
        	     \    | | |	  
        	      \   | | |	  
 		       \  C S A	  
 		        \  | |	  
 		         | | |	  
 		         | | |	  
                         C S A	  
		          | |	  
                         s1 s2   ML2/ML3  latch
		          | |	  
                          CPA	  
		           |
		           |
		           
|#		                     
;; We define the output values of CSA's of the multiplier in the
;; following dozens of definitions.  Function are named CSA-i-j-out or
;; CSA-i-j-carry, where i and j are integer indices.  CSA-i-j-out is
;; the sum vector output by the j'th CSA in the i'th CSA's layer of
;; the multiplier, while CSA-i-j-carry is the carry vector by the same
;; CSA.
;;
;; Arguments vary depending on the value of i.  If i is less than or
;; equal to 3, then the function takes multiplicand and multiplier as
;; their argument.  Because the CSA represented by the function is
;; placed in stage ML1, the output value of the CSA is determined by
;; the multiplier and multiplicand supplied from an earlier stage.  If
;; i is larger than 3, the corresponding CSA is in stage ML2.  So the
;; output of the CSA depends of the six partial sums supplied from the
;; ML1/ML2 latch.

;; We see that the first layer of multiplier outputs partial sums of
;; the shifted vectors.
(defun CSA-1-1-out (multiplicand multiplier)
  (declare (xargs :guard (and (word-p multiplicand) (word-p multiplier))))
  (CSA-out (shifter 15 multiplicand multiplier)
	   (shifter 14 multiplicand multiplier)
	   (shifter 13 multiplicand multiplier)))

(defun CSA-1-2-out (multiplicand multiplier)
  (declare (xargs :guard (and (word-p multiplicand) (word-p multiplier))))
  (CSA-out (shifter 12 multiplicand multiplier)
	   (shifter 11 multiplicand multiplier)
	   (shifter 10 multiplicand multiplier)))

(defun CSA-1-3-out (multiplicand multiplier)
  (declare (xargs :guard (and (word-p multiplicand) (word-p multiplier))))
  (CSA-out (shifter 9 multiplicand multiplier)
	   (shifter 8 multiplicand multiplier)
	   (shifter 7 multiplicand multiplier)))

(defun CSA-1-4-out (multiplicand multiplier)
  (declare (xargs :guard (and (word-p multiplicand) (word-p multiplier))))
  (CSA-out (shifter 6 multiplicand multiplier)
	   (shifter 5 multiplicand multiplier)
	   (shifter 4 multiplicand multiplier)))

(defun CSA-1-5-out (multiplicand multiplier)
  (declare (xargs :guard (and (word-p multiplicand) (word-p multiplier))))
  (CSA-out (shifter 3 multiplicand multiplier)
	   (shifter 2 multiplicand multiplier)
	   (shifter 1 multiplicand multiplier)))

(defun CSA-1-1-carry (multiplicand multiplier)
  (declare (xargs :guard (and (word-p multiplicand) (word-p multiplier))))
  (CSA-carry (shifter 15 multiplicand multiplier)
	     (shifter 14 multiplicand multiplier)
	     (shifter 13 multiplicand multiplier)))

(defun CSA-1-2-carry (multiplicand multiplier)
  (declare (xargs :guard (and (word-p multiplicand) (word-p multiplier))))
  (CSA-carry (shifter 12 multiplicand multiplier)
	     (shifter 11 multiplicand multiplier)
	     (shifter 10 multiplicand multiplier)))

(defun CSA-1-3-carry (multiplicand multiplier)
  (declare (xargs :guard (and (word-p multiplicand) (word-p multiplier))))
  (CSA-carry (shifter 9 multiplicand multiplier)
	     (shifter 8 multiplicand multiplier)
	     (shifter 7 multiplicand multiplier)))

(defun CSA-1-4-carry (multiplicand multiplier)
  (declare (xargs :guard (and (word-p multiplicand) (word-p multiplier))))
  (CSA-carry (shifter 6 multiplicand multiplier)
	     (shifter 5 multiplicand multiplier)
	     (shifter 4 multiplicand multiplier)))

(defun CSA-1-5-carry (multiplicand multiplier)
  (declare (xargs :guard (and (word-p multiplicand) (word-p multiplier))))
  (CSA-carry (shifter 3 multiplicand multiplier)
	     (shifter 2 multiplicand multiplier)
	     (shifter 1 multiplicand multiplier)))

(defthm word-p-CSA-1-1-o
    (implies (and (word-p multiplicand)
		  (word-p multiplier))
	     (word-p (CSA-1-1-out multiplicand multiplier))))

(defthm word-p-CSA-1-2-o
    (implies (and (word-p multiplicand)
		  (word-p multiplier))
	     (word-p (CSA-1-2-out multiplicand multiplier))))

(defthm word-p-CSA-1-3-o
    (implies (and (word-p multiplicand)
		  (word-p multiplier))
	     (word-p (CSA-1-3-out multiplicand multiplier))))

(defthm word-p-CSA-1-4-o
    (implies (and (word-p multiplicand)
		  (word-p multiplier))
	     (word-p (CSA-1-4-out multiplicand multiplier))))

(defthm word-p-CSA-1-5-o
    (implies (and (word-p multiplicand)
		  (word-p multiplier))
	     (word-p (CSA-1-5-out multiplicand multiplier))))

(defthm word-p-CSA-1-1-c
    (implies (and (word-p multiplicand)
		  (word-p multiplier))
	     (word-p (CSA-1-1-carry multiplicand multiplier))))

(defthm word-p-CSA-1-2-c
    (implies (and (word-p multiplicand)
		  (word-p multiplier))
	     (word-p (CSA-1-2-carry multiplicand multiplier))))

(defthm word-p-CSA-1-3-c
    (implies (and (word-p multiplicand)
		  (word-p multiplier))
	     (word-p (CSA-1-3-carry multiplicand multiplier))))

(defthm word-p-CSA-1-4-c
    (implies (and (word-p multiplicand)
		  (word-p multiplier))
	     (word-p (CSA-1-4-carry multiplicand multiplier))))

(defthm word-p-CSA-1-5-c
    (implies (and (word-p multiplicand)
		  (word-p multiplier))
	     (word-p (CSA-1-5-carry multiplicand multiplier))))

(in-theory (disable CSA-1-1-out CSA-1-1-carry
		    CSA-1-2-out CSA-1-2-carry
		    CSA-1-3-out CSA-1-3-carry
		    CSA-1-4-out CSA-1-4-carry
		    CSA-1-5-out CSA-1-5-carry))

;; The second layer outputs the CSA sums and carries of the output values
;; of the first layer CSA's.
(defun CSA-2-1-out (multiplicand multiplier)
  (declare (xargs :guard (and (word-p multiplicand) (word-p multiplier))))
  (CSA-out (CSA-1-2-out multiplicand multiplier)
	   (shift-1 (CSA-1-2-carry multiplicand multiplier))
	   (CSA-1-3-out multiplicand multiplier)))

(defun CSA-2-2-out (multiplicand multiplier)
  (declare (xargs :guard (and (word-p multiplicand) (word-p multiplier))))
  (CSA-out (shift-1 (CSA-1-3-carry multiplicand multiplier))
	   (CSA-1-4-out multiplicand multiplier)
	   (shift-1 (CSA-1-4-carry multiplicand multiplier))))

(defun CSA-2-3-out (multiplicand multiplier)
  (declare (xargs :guard (and (word-p multiplicand) (word-p multiplier))))
  (CSA-out (CSA-1-5-out multiplicand multiplier)
	   (shift-1 (CSA-1-5-carry multiplicand multiplier))
	   (shifter 0 multiplicand multiplier)))

(defun CSA-2-1-carry (multiplicand multiplier)
  (declare (xargs :guard (and (word-p multiplicand) (word-p multiplier))))
  (CSA-carry (CSA-1-2-out multiplicand multiplier)
	     (shift-1 (CSA-1-2-carry multiplicand multiplier))
	     (CSA-1-3-out multiplicand multiplier)))

(defun CSA-2-2-carry (multiplicand multiplier)
  (declare (xargs :guard (and (word-p multiplicand) (word-p multiplier))))
  (CSA-carry (shift-1 (CSA-1-3-carry multiplicand multiplier))
	     (CSA-1-4-out multiplicand multiplier)
	     (shift-1 (CSA-1-4-carry multiplicand multiplier))))

(defun CSA-2-3-carry (multiplicand multiplier)
  (declare (xargs :guard (and (word-p multiplicand) (word-p multiplier))))
  (CSA-carry (CSA-1-5-out multiplicand multiplier)
	     (shift-1 (CSA-1-5-carry multiplicand multiplier))
	     (shifter 0 multiplicand multiplier)))

(defthm word-p-CSA-2-1-o
    (implies (and (word-p multiplicand)
		  (word-p multiplier))
	     (word-p (CSA-2-1-out multiplicand multiplier))))

(defthm word-p-CSA-2-2-o
    (implies (and (word-p multiplicand)
		  (word-p multiplier))
	     (word-p (CSA-2-2-out multiplicand multiplier))))

(defthm word-p-CSA-2-3-o
    (implies (and (word-p multiplicand)
		  (word-p multiplier))
	     (word-p (CSA-2-3-out multiplicand multiplier))))

(defthm word-p-CSA-2-1-c
    (implies (and (word-p multiplicand)
		  (word-p multiplier))
	     (word-p (CSA-2-1-carry multiplicand multiplier))))

(defthm word-p-CSA-2-2-c
    (implies (and (word-p multiplicand)
		  (word-p multiplier))
	     (word-p (CSA-2-2-carry multiplicand multiplier))))

(defthm word-p-CSA-2-3-c
    (implies (and (word-p multiplicand)
		  (word-p multiplier))
	     (word-p (CSA-2-3-carry multiplicand multiplier))))

(in-theory (disable CSA-2-1-out CSA-2-1-carry
		    CSA-2-2-out CSA-2-2-carry
		    CSA-2-3-out CSA-2-3-carry))

(defun CSA-3-1-out (multiplicand multiplier)
  (declare (xargs :guard (and (word-p multiplicand) (word-p multiplier))))
  (CSA-out (CSA-1-1-out multiplicand multiplier)
	   (shift-1 (CSA-1-1-carry multiplicand multiplier))
	   (CSA-2-1-out multiplicand multiplier)))

(defun CSA-3-2-out (multiplicand multiplier)
  (declare (xargs :guard (and (word-p multiplicand) (word-p multiplier))))
  (CSA-out (shift-1 (CSA-2-1-carry multiplicand multiplier))
	   (CSA-2-2-out multiplicand multiplier)
	   (shift-1 (CSA-2-2-carry multiplicand multiplier))))

(defun CSA-3-1-carry (multiplicand multiplier)
  (declare (xargs :guard (and (word-p multiplicand) (word-p multiplier))))
  (CSA-carry (CSA-1-1-out multiplicand multiplier)
	     (shift-1 (CSA-1-1-carry multiplicand multiplier))
	     (CSA-2-1-out multiplicand multiplier)))

(defun CSA-3-2-carry (multiplicand multiplier)
  (declare (xargs :guard (and (word-p multiplicand) (word-p multiplier))))
  (CSA-carry (shift-1 (CSA-2-1-carry multiplicand multiplier))
	     (CSA-2-2-out multiplicand multiplier)
	     (shift-1 (CSA-2-2-carry multiplicand multiplier))))

(defthm word-p-CSA-3-1-o
    (implies (and (word-p multiplicand)
		  (word-p multiplier))
	     (word-p (CSA-3-1-out multiplicand multiplier))))

(defthm word-p-CSA-3-2-o
    (implies (and (word-p multiplicand)
		  (word-p multiplier))
	     (word-p (CSA-3-2-out multiplicand multiplier))))

(defthm word-p-CSA-3-1-c
    (implies (and (word-p multiplicand)
		  (word-p multiplier))
	     (word-p (CSA-3-1-carry multiplicand multiplier))))

(defthm word-p-CSA-3-2-c
    (implies (and (word-p multiplicand)
		  (word-p multiplier))
	     (word-p (CSA-3-2-carry multiplicand multiplier))))

(in-theory (disable CSA-3-1-out CSA-3-1-carry
		    CSA-3-2-out CSA-3-2-carry))

;; ML1 generates six partial sums of the shifted vectors. ML1-sum1
;; through ML12-sum6 calculates these values. 
(defun ML1-sum1 (ra rb)
  (declare (xargs :guard (and (word-p ra) (word-p rb))))
  (CSA-3-1-out ra rb))

(defun ML1-sum2 (ra rb)
  (declare (xargs :guard (and (word-p ra) (word-p rb))))
  (shift-1 (CSA-3-1-carry ra rb)))

(defun ML1-sum3 (ra rb)
  (declare (xargs :guard (and (word-p ra) (word-p rb))))
  (CSA-3-2-out ra rb))

(defun ML1-sum4 (ra rb)
  (declare (xargs :guard (and (word-p ra) (word-p rb))))
  (shift-1 (CSA-3-2-carry ra rb)))

(defun ML1-sum5 (ra rb)
  (declare (xargs :guard (and (word-p ra) (word-p rb))))
  (CSA-2-3-out ra rb))

(defun ML1-sum6 (ra rb)
  (declare (xargs :guard (and (word-p ra) (word-p rb))))
  (shift-1 (CSA-2-3-carry ra rb)))

(defthm word-p-ML1-sum1
    (implies (and (word-p ra) (word-p rb))
	     (word-p (ML1-sum1 ra rb))))
(defthm word-p-ML1-sum2
    (implies (and (word-p ra) (word-p rb))
	     (word-p (ML1-sum2 ra rb))))
(defthm word-p-ML1-sum3
    (implies (and (word-p ra) (word-p rb))
	     (word-p (ML1-sum3 ra rb))))
(defthm word-p-ML1-sum4
    (implies (and (word-p ra) (word-p rb))
	     (word-p (ML1-sum4 ra rb))))
(defthm word-p-ML1-sum5
    (implies (and (word-p ra) (word-p rb))
	     (word-p (ML1-sum5 ra rb))))
(defthm word-p-ML1-sum6
    (implies (and (word-p ra) (word-p rb))
	     (word-p (ML1-sum6 ra rb))))

;; CSA-4-j-{out,carry} takes six partial sums which are generated by
;; CSA-3-j-{out,carry}'s.  In the pipeline configuration, these sums 
;; are once stored in the first latch
(defun CSA-4-1-out (s1 s2 s3 s4 s5 s6)
  (declare (xargs :guard (and (word-p s1) (word-p s2) (word-p s3)
			      (word-p s4) (word-p s5) (word-p s6)))
; Matt K. mod: Added necessary ignorable declaration.
           (ignorable s4 s5 s6))
  (CSA-out s1 s2 s3))

(defun CSA-4-1-carry (s1 s2 s3 s4 s5 s6)
  (declare (xargs :guard (and (word-p s1) (word-p s2) (word-p s3)
			      (word-p s4) (word-p s5) (word-p s6)))
; Matt K. mod: Added necessary ignorable declaration.
           (ignorable s4 s5 s6))
  (CSA-carry s1 s2 s3))

(defun CSA-4-2-out (s1 s2 s3 s4 s5 s6)
  (declare (xargs :guard (and (word-p s1) (word-p s2) (word-p s3)
			      (word-p s4) (word-p s5) (word-p s6)))
; Matt K. mod: Added necessary ignorable declaration.
           (ignorable s1 s2 s3))
  (CSA-out s4 s5 s6))

(defun CSA-4-2-carry (s1 s2 s3 s4 s5 s6)
  (declare (xargs :guard (and (word-p s1) (word-p s2) (word-p s3)
			      (word-p s4) (word-p s5) (word-p s6)))
; Matt K. mod: Added necessary ignorable declaration.
           (ignorable s1 s2 s3))
  (CSA-carry s4 s5 s6))

(defthm word-p-CSA-4-1-o 
    (implies (and (word-p s1) (word-p s2) (word-p s3)
		  (word-p s4) (word-p s5) (word-p s6))
	     (word-p (CSA-4-1-out s1 s2 s3 s4 s5 s6))))

(defthm word-p-CSA-4-1-c 
    (implies (and (word-p s1) (word-p s2) (word-p s3)
		  (word-p s4) (word-p s5) (word-p s6))
	     (word-p (CSA-4-1-carry s1 s2 s3 s4 s5 s6))))

(defthm word-p-CSA-4-2-o 
    (implies (and (word-p s1) (word-p s2) (word-p s3)
		  (word-p s4) (word-p s5) (word-p s6))
	     (word-p (CSA-4-2-out s1 s2 s3 s4 s5 s6))))

(defthm word-p-CSA-4-2-c 
    (implies (and (word-p s1) (word-p s2) (word-p s3)
		  (word-p s4) (word-p s5) (word-p s6))
	     (word-p (CSA-4-2-carry s1 s2 s3 s4 s5 s6))))

(in-theory (disable CSA-4-1-out
		    CSA-4-1-carry
		    CSA-4-2-out
		    CSA-4-2-carry))

(defun CSA-5-1-out (s1 s2 s3 s4 s5 s6)
  (declare (xargs :guard (and (word-p s1) (word-p s2) (word-p s3)
			      (word-p s4) (word-p s5) (word-p s6))))
  (CSA-out (shift-1 (CSA-4-1-carry s1 s2 s3 s4 s5 s6))
	   (CSA-4-2-out s1 s2 s3 s4 s5 s6)
	   (shift-1 (CSA-4-2-carry s1 s2 s3 s4 s5 s6))))

(defun CSA-5-1-carry (s1 s2 s3 s4 s5 s6)
  (declare (xargs :guard (and (word-p s1) (word-p s2) (word-p s3)
			      (word-p s4) (word-p s5) (word-p s6))))
  (CSA-carry (shift-1 (CSA-4-1-carry s1 s2 s3 s4 s5 s6))
	     (CSA-4-2-out s1 s2 s3 s4 s5 s6)
	     (shift-1 (CSA-4-2-carry s1 s2 s3 s4 s5 s6))))

(defthm word-p-CSA-5-1-o 
    (implies (and (word-p s1) (word-p s2) (word-p s3)
		  (word-p s4) (word-p s5) (word-p s6))
	     (word-p (CSA-5-1-out s1 s2 s3 s4 s5 s6))))

(defthm word-p-CSA-5-1-c 
    (implies (and (word-p s1) (word-p s2) (word-p s3)
		  (word-p s4) (word-p s5) (word-p s6))
	     (word-p (CSA-5-1-carry s1 s2 s3 s4 s5 s6))))

(in-theory (disable CSA-5-1-out CSA-5-1-carry))

(defun CSA-6-1-out (s1 s2 s3 s4 s5 s6)
  (declare (xargs :guard (and (word-p s1) (word-p s2) (word-p s3)
			      (word-p s4) (word-p s5) (word-p s6))))
  (CSA-out (CSA-4-1-out s1 s2 s3 s4 s5 s6)
	   (CSA-5-1-out s1 s2 s3 s4 s5 s6)
	   (shift-1 (CSA-5-1-carry s1 s2 s3 s4 s5 s6))))

(defun CSA-6-1-carry (s1 s2 s3 s4 s5 s6)
  (declare (xargs :guard (and (word-p s1) (word-p s2) (word-p s3)
			      (word-p s4) (word-p s5) (word-p s6))))
  (CSA-carry (CSA-4-1-out s1 s2 s3 s4 s5 s6)
	     (CSA-5-1-out s1 s2 s3 s4 s5 s6)
	     (shift-1 (CSA-5-1-carry s1 s2 s3 s4 s5 s6))))

(defthm word-p-CSA-6-1-o 
    (implies (and (word-p s1) (word-p s2) (word-p s3)
		  (word-p s4) (word-p s5) (word-p s6))
	     (word-p (CSA-6-1-out s1 s2 s3 s4 s5 s6))))

(defthm word-p-CSA-6-2-c 
    (implies (and (word-p s1) (word-p s2) (word-p s3)
		  (word-p s4) (word-p s5) (word-p s6))
	     (word-p (CSA-6-1-carry s1 s2 s3 s4 s5 s6))))

(in-theory (disable CSA-6-1-out CSA-6-1-carry))

;; ML2-sum1 and ML2-sum2 are two partial sums from the sixth layer of
;; CSA tree.  These sums are stored in the second latch, then added by a
;; ripple carry adder in stage ML3.
(defun ML2-sum1 (s1 s2 s3 s4 s5 s6)
  (declare (xargs :guard (and (word-p s1) (word-p s2) (word-p s3)
			      (word-p s4) (word-p s5) (word-p s6))))
  (CSA-6-1-out s1 s2 s3 s4 s5 s6))

(defun ML2-sum2 (s1 s2 s3 s4 s5 s6)
  (declare (xargs :guard (and (word-p s1) (word-p s2) (word-p s3)
			      (word-p s4) (word-p s5) (word-p s6))))
  (shift-1 (CSA-6-1-carry s1 s2 s3 s4 s5 s6)))

(defthm word-p-ML2-sum1
    (implies (and (word-p s1) (word-p s2) (word-p s3)
		  (word-p s4) (word-p s5) (word-p s6))
	     (word-p (ML2-sum1 s1 s2 s3 s4 s5 s6))))

(defthm word-p-ML2-sum2
    (implies (and (word-p s1) (word-p s2) (word-p s3)
		  (word-p s4) (word-p s5) (word-p s6))
	     (word-p (ML2-sum2 s1 s2 s3 s4 s5 s6))))

(deflabel end-def-multiplier)

;; The next state of latch ML1/ML2. ML1/ML2 latch eagerly stores the
;; output from the first stage of multiplier, even if the MULT
;; instruction is not issued.

(defstructure ML1-data
  (sum1 (:assert (word-p sum1) :rewrite))
  (sum2 (:assert (word-p sum2) :rewrite))
  (sum3 (:assert (word-p sum3) :rewrite))
  (sum4 (:assert (word-p sum4) :rewrite))
  (sum5 (:assert (word-p sum5) :rewrite))
  (sum6 (:assert (word-p sum6) :rewrite))
  (:options :guards))

(defstructure ML2-data
  (sum1 (:assert (word-p sum1) :rewrite))
  (sum2 (:assert (word-p sum2) :rewrite))
  (:options :guards))

(defun ML1-output (x y)
  (declare (xargs :guard (and (word-p x) (word-p y))))
  (ML1-data (ML1-sum1 x y)
	    (ML1-sum2 x y)
	    (ML1-sum3 x y)
	    (ML1-sum4 x y)
	    (ML1-sum5 x y)
	    (ML1-sum6 x y)))

;; The next state of latch ML2/ML3. ML2/ML3 stores two partial sums
;; from the second stage of the multiplier.
(defun ML2-output (data)
  (declare (xargs :guard (ML1-data-p data)))
  (ML2-data (ML2-sum1 (ML1-data-sum1 data) (ML1-data-sum2 data)
		      (ML1-data-sum3 data) (ML1-data-sum4 data)
		      (ML1-data-sum5 data) (ML1-data-sum6 data))
	    (ML2-sum2 (ML1-data-sum1 data) (ML1-data-sum2 data)
		      (ML1-data-sum3 data) (ML1-data-sum4 data)
		      (ML1-data-sum5 data) (ML1-data-sum6 data))))

(defthm ML1-data-p-ML1-output
    (implies (and (word-p x) (word-p y))
	     (ML1-data-p (ML1-output x y))))

(defthm ML2-data-p-ML2-output
    (implies (ML1-data-p data)
	     (ML2-data-p (ML2-output data))))

;; ML-output defines the output from the multiplier.  Precisely
;; speaking, this is the output from stage ML3.  ML3 adds the two
;; partial sums in ML2/ML3 with a ripple carry adder.  In our
;; specification, we simply express the ripple carry adder with
;; the function +.
(defun ML3-output (data)
  (declare (xargs :guard (ML2-data-p data)))
  (word (+ (ML2-data-sum1 data) (ML2-data-sum2 data))))

(deftheory def-multiplier
    (set-difference-theories (function-theory 'end-def-multiplier)
			     (function-theory 'begin-def-multiplier)))
