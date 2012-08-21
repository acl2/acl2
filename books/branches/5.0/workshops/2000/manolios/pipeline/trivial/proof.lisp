(in-package "ACL2")

; *******************CHANGE********************
; This file is very different from Sawada's file, however, the same
; final theorems, namely commutative-diagram and liveness are proved.
; In addition, we prove the theorem ma-is-bad which shows that the ma
; machine we proved satisfies Sawada's variant of the Burch and Dill
; notion of correctness is in fact incorrect as it never changes the
; ISA visible components of the state.
; *******************CHANGE********************

(include-book "model")

(in-theory (enable ISA-def MA-def MA-sig-p))

(defun num-insts (MA sig-list n)
  (declare (ignore MA sig-list n))
  0)

;  Correctness diagram.
(defthm commutative-diagram
    (implies (and (MA-state-p MA)
		  (MA-sig-listp sig-list)
		  (<= n (len sig-list))
		  (b1p (flushed? MA))
		  (b1p (flushed? (MA-stepn MA sig-list n))))
	     (equal (proj (MA-stepn MA sig-list n))
		    (ISA-stepn (proj MA)
			       (num-insts MA sig-list n)))))

; The number of the cycles to flush the pipeline.
(defun flush-cycles (MA)
  (declare (ignore MA))
  1)

(defun zeros (n)
  (if (zp n)
      nil
    (cons 0 (zeros (1- n)))))

(in-theory (enable b-nor b1p ma-stepn))

(defthm liveness
    (implies (MA-state-p MA)
	     (b1p (flushed? (MA-stepn MA
				      (zeros (flush-cycles MA))
				      (flush-cycles MA)))))
    :hints (("goal" :expand ((ma-stepn ma '(0) 1)))))

(defthm ma-is-bad
  (implies (ma-state-p ma)
	   (and (equal (ma-pc (ma-stepn ma x n))
		       (ma-pc ma))
		(equal (ma-regs (ma-stepn ma x n))
		       (ma-regs ma))
		(equal (ma-mem (ma-stepn ma x n))
		       (ma-mem ma)))))
