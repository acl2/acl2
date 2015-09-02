;;;***************************************************************
;;;Proof of Correctness of a Floating Point Multiplier

;;;David M. Russinoff
;;;Advanced Micro Devices, Inc.
;;;February, 1999
;;;***************************************************************

;;This file contains the definition required for the statement of the
;;correctness theorem, and a description of our plan for proving it.

(in-package "ACL2")

;;The following four books are included:

;;(1) A package written by J Moore that makes arithmetic proofs
;;somewhat easier:

(include-book "../../../rtl/rel1/support/fp")

;;(2) The floating point library:

(include-book "../../../rtl/rel1/lib1/top")

;;(3) Definitions of the functions used in the RTL:

(include-book "rtl")

;;(4) The definition of the multiplier:

(include-book "fmul")


;;Extended precision format, used internally by the multiplier:

(defun extfmt () '(64 15))

;;An abbreviation for the rational number represented by a given
;;bit vector in the extended format:

(defun hat (z) (decode z (extfmt)))

;;The rounding mode represented by the input parameter RC:

(defun mode (rc)
  (case rc
    (0 'near)
    (1 'minf)
    (2 'inf)
    (3 'trunc)))

;;The precision represented by the input parameter PC:

(defun precision (pc)
  (case pc
    (0 24)
    (1 53)))

(in-theory (disable extfmt hat mode precision))

;;The statement of correctness:

;;(defthm correctness-of-fmul
;;    (let ((ideal (rnd (* (hat x) (hat y))
;;		        (mode rc)
;;		        (precision pc)))
;;	    (z (fmul x y rc pc)))
;;      (implies (and (normal-encoding-p x (extfmt))
;;		      (normal-encoding-p b (extfmt))
;;		      (member rc (list 0 1 2 3))
;;		      (member pc (list 0 1))
;;		      (repp ideal (extfmt)))
;;	         (and (normal-encoding-p z (extfmt))
;;		      (= (hat z) ideal)))))

;;Our plan for proving the above theorem, based on functional
;;instantiation, is outlined below.

;;First, we introduce the following two definitions:

(defun input-spec (x y rc pc)
  (and (normal-encoding-p x (extfmt))
       (normal-encoding-p y (extfmt))
       (member rc (list 0 1 2 3))
       (member pc (list 0 1))
       (repp (rnd (* (hat x) (hat y)) (mode rc) (precision pc))
	     (extfmt))))

(defun output-spec (x y rc pc)
  (let ((z (fmul x y rc pc)))
    (and (normal-encoding-p z (extfmt))
	 (= (hat z)
	    (rnd (* (hat x) (hat y))
		 (mode rc)
		 (precision pc))))))

(in-theory (disable input-spec output-spec))

;;The inputs (X*), (Y*), (RC*), and (PC*) are constrained to
;;satisfy the input specification:

(encapsulate ((x* () t) (y* () t) (rc* () t) (pc* () t))
  (local (defun x* () (encode 1 (extfmt))))
  (local (defun y* () (encode 1 (extfmt))))
  (local (defun rc* () 0))
  (local (defun pc* () 1))
  (defthm input-spec* (input-spec (x*) (y*) (rc*) (pc*)))
  (in-theory (disable input-spec*)))

;;Once these constrained functions have been introduced, the "fmul*"
;;book may be loaded.  This book defines a constant function S*
;;corresponding to each signal S.  The value of this function, (S*),
;;represents the value of the signal that results from the inputs
;;(X*), (Y*), (RC*), and (PC*).  In fact, the following theorem is
;;proved for the output signal Z:

;;(DEFTHM FMUL-STAR-EQUIVALENCE
;;        (EQUAL (Z*)
;;               (FMUL (X*) (Y*) (RC*) (PC*)))
;;        :RULE-CLASSES NIL)
;;
;;Now suppose that we are able to prove this theorem:
;;
;;(defthm z*-spec
;;    (and (normal-encoding-p (z*) (extfmt))
;;	 (= (hat (z*))
;;	    (rnd (* (hat (x*)) (hat (y*)))
;;		 (mode (rc*))
;;		 (precision (pc*)))))
;;  :rule-classes())
;;
;;Then the desired correctness theorem can be derived as follows:
;;
;;(defthm output-spec*
;;    (output-spec (x*) (y*) (rc*) (pc*))
;;  :hints (("Goal" :in-theory (enable output-spec)
;;                  :use (z*-spec fmul-star-equivalence))))
;;
;;(defthm fmul-input-output
;;    (implies (input-spec x y rc pc)
;;	       (output-spec x y rc pc))
;;  :hints (("Goal" :in-theory (enable input-spec*)
;;                  :use ((:functional-instance output-spec*
;;			    (x* (lambda () (if (input-spec x y rc pc) x (x*))))
;;			    (y* (lambda () (if (input-spec x y rc pc) y (y*))))
;;			    (rc* (lambda () (if (input-spec x y rc pc) rc (rc*))))
;;			    (pc* (lambda () (if (input-spec x y rc pc) pc (pc*))))))))
;;  :rule-classes ())
;;
;;(defthm CORRECTNESS-OF-FMUL
;;    (let ((ideal (rnd (* (hat x) (hat y))
;;		        (mode rc)
;;		        (precision pc)))
;;	    (z (fmul x y rc pc)))
;;      (implies (and (normal-encoding-p x (extfmt))
;;		      (normal-encoding-p y (extfmt))
;;		      (member rc (list 0 1 2 3))
;;		      (member pc (list 0 1))
;;		      (repp ideal (extfmt)))
;;	         (and (normal-encoding-p z (extfmt))
;;		      (= (hat z) ideal))))
;;  :hints (("Goal" :in-theory (enable input-spec output-spec)
;;                  :use (fmul-input-output))))
;;
;;Thus, our goal will be to prove the above theorem Z*-SPEC.