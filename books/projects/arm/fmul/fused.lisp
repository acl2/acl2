(in-package "RTL")

(include-book "final")

(defthmd fused-10
  (implies (and (denormp (opa) (dp))
                (= (fzp) 1))
	   (zerp (opaz) (dp)))
  :hints (("Goal" :in-theory (enable fzp opaz zencode expw sigf sigw cat dp sgnf zerp)
                  :use ((:instance bitn-0-1 (x (opa)) (n 63))))))

(defthmd fused-11
  (implies (and (denormp (opb) (dp))
                (= (fzp) 1))
	   (zerp (opbz) (dp)))
  :hints (("Goal" :in-theory (enable fzp opbz zencode expw sigf sigw cat dp sgnf zerp)
                  :use ((:instance bitn-0-1 (x (opb)) (n 63))))))

(defthmd fused-12
  (implies (and (= (fused) 1) (not (specialp)))
           (not (fmul64-fused-special-p (opa) (opb) (fzp))))
  :hints (("Goal" :in-theory (enable specialp snanp qnanp)
                  :use (fused-10 fused-11 a-class b-class))))

(in-theory (disable fmul64-fused-special-p))

(defthmd fused-13
  (implies (and (= (fused) 1) (not (specialp)))
           (equal (flags-b) 0))
  :hints (("Goal" :in-theory (enable fzp specialp b-flags)
                  :use (fused-10 fused-11 a-class b-class))))

(defthmd fused-14
  (implies (and (= (fused) 1) (not (specialp)))
           (and (not (snanp (opa) (dp)))
	        (not (snanp (opb) (dp)))
	        (not (fzerp (opa) (fzp)))
	        (not (fzerp (opb) (fzp)))
		(not (inf-times-zero (opa) (opb) (fzp)))))
  :hints (("Goal" :in-theory (enable fzp specialp b-flags)
                  :use (fused-10 fused-11 a-class b-class))))

(in-theory (disable inf-times-zero fzerp))

(defthmd fused-15
  (implies (and (= (fused) 1) (not (specialp)))
           (and (equal (prodinfzero) 0)
                (equal (infnanzero) 0)
                (equal (bitn (flags) 7) 0)
                (equal (bitn (flags) 6) 0)
                (equal (bitn (flags) 5) 0)
                (equal (bitn (flags) 3) 0)
                (equal (bitn (flags) 2) 0)
                (equal (bitn (flags) 1) 0)
                (equal (bitn (flags) 0) 0)))
  :hints (("Goal" :in-theory (enable specialp flags-fma fused-13 prodinfzero infnanzero flags))))

(defthmd fused-16
  (implies (and (= (fused) 1) (not (specialp)))
           (and (equal (a) (decode (opa) (dp)))
	        (equal (b) (decode (opb) (dp)))))
  :hints (("Goal" :in-theory (enable a b specialp))))

(defthmd expovfl-0-1
  (implies (and (= (fused) 1) (not (specialp)))
           (bitp (expovfl)))
  :hints (("Goal" :in-theory (enable expovfl specialp))))

(defthmd not-specialp-fused
  (implies (and (= (fused) 1) (not (specialp)))
           (fmul64-fused-spec (opa) (opb) (fzp) (dnp) (data) (flags)
                             (prodinfzero) (infnanzero) (expovfl)))
  :hints (("Goal" :use (expovfl-0-1 a-nonzero b-nonzero fused-expofvl fused-normal fused-subnormal)
                  :in-theory (enable specialp signa-rewrite signb-rewrite sign data data-fma fused-12 fused-14 fused-15 fused-16))))

(defthmd fmul64-fused-main
  (implies (= (fused) 1)
           (fmul64-fused-spec (opa) (opb) (fzp) (dnp) (data) (flags)
                             (prodinfzero) (infnanzero) (expovfl)))
  :hints (("Goal" :use (specialp-fused not-specialp-fused))))

(in-theory (disable fmul64-fused-spec))

(defthmd fmul64-fused-lemma-to-be-functionally-instantiated
  (let ((dnp (bitn (rin) 25))
        (fzp (bitn (rin) 24))
        (rmode (bits (rin) 23 22)))
    (mv-let (data flags prodinfzero infnanzero expovfl) (fmul64 (opa) (opb) fzp dnp rmode 1)
	(implies (= (fused) 1)
                 (fmul64-fused-spec (opa) (opb) fzp dnp data flags prodinfzero infnanzero expovfl))))
  :hints (("Goal" :use (fmul64-fused-main fmul64-lemma)
                  :in-theory (enable fzp dnp rmode))))

(defthm fmul64-fused-correct
  (implies (input-constraints opa opb rin)
           (let ((dnp (bitn rin 25))
                 (fzp (bitn rin 24))
                 (rmode (bits rin 23 22)))
             (mv-let (data flags prodinfzero infnanzero expovfl) (fmul64 opa opb fzp dnp rmode 1)
               (fmul64-fused-spec opa opb fzp dnp data flags prodinfzero infnanzero expovfl))))
  :rule-classes ()
  :hints (("Goal" :use ((:functional-instance fmul64-fused-lemma-to-be-functionally-instantiated
                         (opa (lambda () (if (ic) opa (opa))))
                         (opb (lambda () (if (ic) opb (opb))))
                         (rin (lambda () (if (ic) rin (rin))))
			 (fused (lambda () (if (ic) 1 (fused)))))))
          ("Subgoal 2" :use (bitp-fused))
          ("Subgoal 1" :use (input-constraints-lemma))))



