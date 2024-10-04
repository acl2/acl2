;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; MAETT-lemmas2.lisp
; Author  Jun Sawada, University of Texas at Austin
;
;  This book contains various lemmas about the FM9801 and its MAETT
;  abstraction. This book is a continuation of MAETT-lemmas2.lisp.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "MA2-lemmas")
(include-book "invariants-def")
(include-book "MAETT-lemmas1")

(deflabel begin-MAETT-lemmas2)

;  Index
;   Lemmas about relations between MT and MA
;     relations between exception events
;     (this part occupies 60% of the whole file)
;   Lemmas about micro-architecture satisfying invariants.
;   Lemmas about stages after step-INST, again.
;   Lemmas about no-commit-inst-p and no-dispatched-inst-p
;   Lemmas about MT-non-commit-trace and MT-non-retire-trace.
;   Lemmas about commit again.
;   Lemmas about MT-CMI-p
;   Lemmas about MT-no-jmp-exintr-before

;;;;;;;;;;;;;;;;;;Lemmas about MT and MA;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;    Field lemmas
;    Lemmas about ROB and instructions in it.
;    Instruction specific properties about INST fields
;    Relations about INST predicates such as INST-cause-jmp, INST-exintr-now
;       INST-start-specultv?
;    Other lemmas
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; IFU field lemmas
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(deflabel begin-IFU-field-lemmas)
(defthm IFU-valid-if-inst-in
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-in i MT)
		  (IFU-stg-p (INST-stg i)))
	     (equal (IFU-valid? (MA-IFU MA)) 1))
  :hints (("Goal" :in-theory (e/d (inst-inv-def
				   equal-b1p-converter)
				  (INST-INV-IF-INST-IN))
		  :use (:instance INST-INV-IF-INST-IN))))

(defthm IFU-pc-INST-pc
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-in i MT)
		  (IFU-stg-p (INST-stg i))
		  (not (b1p (inst-specultv? i)))
		  (or (not (b1p (INST-modified? i)))
		      (b1p (INST-first-modified? i))))
	     (equal (IFU-pc (MA-IFU MA))
		    (INST-pc i)))
  :hints (("Goal" :in-theory (e/d (inst-inv-def
				   INST-pc
				   equal-b1p-converter)
				  (INST-INV-IF-INST-IN))
		  :use (:instance INST-INV-IF-INST-IN))))

(defthm IFU-pc-INST-pc-2
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (uniq-inst-at-stg '(IFU) MT)
		  (not (b1p (inst-specultv? (INST-at-stg '(IFU) MT))))
		  (or (not (b1p (INST-modified? (INST-at-stg '(IFU) MT))))
		      (b1p (INST-first-modified? (INST-at-stg '(IFU) MT)))))
	     (equal (IFU-pc (MA-IFU MA))
		    (INST-pc (INST-at-stg '(IFU) MT))))
  :hints (("Goal" :use (:instance IFU-pc-INST-pc
				  (i (INST-at-stg '(IFU) MT))))))

(defthm IFU-word-INST-word
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-in i MT)
		  (IFU-stg-p (INST-stg i))
		  (not (b1p (inst-specultv? i)))
		  (not (b1p (INST-modified? i)))
		  (not (INST-fetch-error-detected-p I)))
	     (equal (IFU-word (MA-IFU MA))
		    (INST-word I)))
  :hints (("Goal" :in-theory (e/d (inst-inv-def
				   equal-b1p-converter)
				  (INST-INV-IF-INST-IN))
		  :use (:instance INST-INV-IF-INST-IN))))

(defthm IFU-word-INST-word-if-fetch-error
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-in i MT)
		  (IFU-stg-p (INST-stg i))
		  (not (b1p (inst-specultv? i)))
		  (not (b1p (INST-modified? i)))
		  (INST-fetch-error-detected-p I))
	     (equal (IFU-word (MA-IFU MA)) 0))
  :hints (("Goal" :in-theory (e/d (inst-inv-def
				   equal-b1p-converter)
				  (INST-INV-IF-INST-IN))
		  :use (:instance INST-INV-IF-INST-IN))))

(defthm IFU-word-INST-word-2
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (uniq-inst-at-stg '(IFU) MT)
		  (not (b1p (inst-specultv? (INST-at-stg '(IFU) MT))))
		  (not (b1p (INST-modified? (INST-at-stg '(IFU) MT)))))
	     (equal (IFU-WORD (MA-IFU MA))
		    (IF (INST-fetch-error-detected-p (INST-at-stg '(IFU) MT))
			0 (INST-word (INST-at-stg '(IFU) MT)))))
  :hints (("Goal" :restrict ((IFU-word-INST-word
			      ((i (INST-at-stg '(IFU) MT))))
			     (IFU-word-INST-word-if-fetch-error
			      ((i (INST-at-stg '(IFU) MT))))))))

(defthm IFU-excpt-INST-excpt
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-in i MT)
		  (IFU-stg-p (INST-stg i))
		  (not (b1p (inst-specultv? i)))
		  (not (b1p (INST-modified? i))))
	     (equal (IFU-excpt (MA-IFU MA))
		    (INST-excpt-flags i)))
  :hints (("Goal" :in-theory (e/d (inst-inv-def
				   equal-b1p-converter)
				  (INST-INV-IF-INST-IN))
		  :use (:instance INST-INV-IF-INST-IN))))
(deflabel end-IFU-field-lemmas)
(deftheory IFU-field-lemmas
    (set-difference-theories (universal-theory 'begin-IFU-field-lemmas)
			     (universal-theory 'end-IFU-field-lemmas)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; End of IFU field lemmas
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; DQ field lemmas
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(deflabel begin-DQ-DE0-field-lemmas)

(defthm DQ-DE0-valid-if-inst-in
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-in i MT)
		  (equal (INST-stg i) '(DQ 0)))
	     (equal (DE-valid? (DQ-DE0 (MA-DQ MA))) 1))
  :hints (("Goal" :in-theory (e/d (inst-inv-def
				   equal-b1p-converter)
				  (INST-INV-IF-INST-IN))
		  :use (:instance INST-INV-IF-INST-IN))))

(defthm DQ-DE1-valid-if-inst-in
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-in i MT)
		  (equal (INST-stg i) '(DQ 1)))
	     (equal (DE-valid? (DQ-DE1 (MA-DQ MA))) 1))
  :hints (("Goal" :in-theory (e/d (inst-inv-def
				   equal-b1p-converter)
				  (INST-INV-IF-INST-IN))
		  :use (:instance INST-INV-IF-INST-IN))))

(defthm DQ-DE2-valid-if-inst-in
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-in i MT)
		  (equal (INST-stg i) '(DQ 2)))
	     (equal (DE-valid? (DQ-DE2 (MA-DQ MA))) 1))
  :hints (("Goal" :in-theory (e/d (inst-inv-def
				   equal-b1p-converter)
				  (INST-INV-IF-INST-IN))
		  :use (:instance INST-INV-IF-INST-IN))))

(defthm DQ-DE3-valid-if-inst-in
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-in i MT)
		  (equal (INST-stg i) '(DQ 3)))
	     (equal (DE-valid? (DQ-DE3 (MA-DQ MA))) 1))
  :hints (("Goal" :in-theory (e/d (inst-inv-def
				   equal-b1p-converter)
				  (INST-INV-IF-INST-IN))
		  :use (:instance INST-INV-IF-INST-IN))))

(defthm uniq-inst-at-stg-DQ-MT-DQ-len-minus-1
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (not (equal (MT-DQ-len MT) 0)))
	     (uniq-inst-at-stg (list 'DQ (1- (MT-DQ-len MT))) MT))
  :hints (("Goal" :cases ((equal (MT-DQ-len MT) 1) (equal (MT-DQ-len MT) 2)
			  (equal (MT-DQ-len MT) 3) (equal (MT-DQ-len MT) 4)))
	  (when-found (uniq-inst-at-stg '(DQ 0) MT)
		      (:cases ((b1p (DE-valid? (DQ-DE0 (MA-DQ MA)))))))
	  (when-found (uniq-inst-at-stg '(DQ 1) MT)
		      (:cases ((b1p (DE-valid? (DQ-DE1 (MA-DQ MA)))))))
	  (when-found (uniq-inst-at-stg '(DQ 2) MT)
		      (:cases ((b1p (DE-valid? (DQ-DE2 (MA-DQ MA)))))))
	  (when-found (uniq-inst-at-stg '(DQ 3) MT)
		      (:cases ((b1p (DE-valid? (DQ-DE3 (MA-DQ MA)))))))))

(defthm DQ-DE0-cntlv-=-inst-cntlv-1
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-in i MT) (equal (INST-stg i) '(DQ 0))
		  (not (b1p (inst-specultv? i)))
		  (not (b1p (INST-modified? i)))
		  (not (INST-fetch-error-detected-p i)))
	     (equal (DE-cntlv (DQ-DE0 (MA-DQ MA)))
		    (INST-cntlv i)))
  :hints (("goal" :in-theory (e/d (inst-inv-def
				   INST-excpt-detected-p
				   equal-b1p-converter)
				  (INST-INV-IF-INST-IN))
		  :use (:instance INST-INV-IF-INST-IN))))

(defthm DQ-DE0-cntlv-=-inst-cntlv-2
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (uniq-INST-at-stg '(DQ 0) MT)
		  (not (b1p (inst-specultv? (INST-at-stg '(DQ 0) MT))))
		  (not (b1p (INST-modified? (INST-at-stg '(DQ 0) MT))))
		  (not (INST-fetch-error-detected-p (INST-at-stg '(DQ 0) MT))))
	     (equal (DE-cntlv (DQ-DE0 (MA-DQ MA)))
		    (INST-cntlv (INST-at-stg '(DQ 0) MT))))
  :hints (("goal" :use (:instance DQ-DE0-cntlv-=-inst-cntlv-1
				  (i (INST-at-stg '(DQ 0) MT))))))

(defthm DQ-DE0-cntlv-=-inst-cntlv-1-if-fetch-error
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-in i MT) (equal (INST-stg i) '(DQ 0))
		  (not (b1p (inst-specultv? i)))
		  (not (b1p (INST-modified? i)))
		  (INST-fetch-error-detected-p i))
	     (equal (DE-cntlv (DQ-DE0 (MA-DQ MA)))
		    (decode 0 (INST-br-predict? i))))
  :hints (("goal" :in-theory (e/d (inst-inv-def
				   INST-excpt-detected-p
				   equal-b1p-converter)
				  (INST-INV-IF-INST-IN))
		  :use (:instance INST-INV-IF-INST-IN))))

(defthm DQ-DE0-PC-=-inst-pc
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-in i MT) (equal (INST-stg i) '(DQ 0))
		  (not (b1p (inst-specultv? i)))
		  (or (not (b1p (INST-modified? i)))
		      (b1p (INST-first-modified? i))))
	     (equal (DE-pc (DQ-DE0 (MA-DQ MA)))
		    (INST-pc i)))
  :hints (("goal" :in-theory (e/d (inst-inv-def
				   INST-excpt-detected-p
				   INST-pc
				   equal-b1p-converter)
				  (INST-INV-IF-INST-IN))
		  :use (:instance INST-INV-IF-INST-IN))))

(defthm DQ-DE0-PC-=-inst-pc-2
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (uniq-INST-at-stg '(DQ 0) MT)
		  (not (b1p (inst-specultv? (INST-at-stg '(DQ 0) MT))))
		  (or (not (b1p (INST-modified? (INST-at-stg '(DQ 0) MT))))
		      (b1p (INST-first-modified? (INST-at-stg '(DQ 0) MT)))))
	     (equal (DE-PC (DQ-DE0 (MA-DQ MA)))
		    (INST-pc (INST-at-stg '(DQ 0) MT))))
  :hints (("goal" :use (:instance DQ-DE0-PC-=-inst-pc
				  (i (INST-at-stg '(DQ 0) MT))))))

(defthm DQ-DE0-RC-=-inst-rc
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-in i MT) (equal (INST-stg i) '(DQ 0))
		  (not (b1p (inst-specultv? i)))
		  (not (b1p (INST-modified? i)))
		  (not (INST-fetch-error-detected-p i)))
	     (equal (DE-RC (DQ-DE0 (MA-DQ MA)))
		    (INST-rc i)))
  :hints (("goal" :in-theory (e/d (inst-inv-def
				   INST-excpt-detected-p
				   INST-rc
				   equal-b1p-converter)
				  (INST-INV-IF-INST-IN))
		  :use (:instance INST-INV-IF-INST-IN))))

(defthm DQ-DE0-RC-=-inst-rc-2
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (uniq-INST-at-stg '(DQ 0) MT)
		  (not (b1p (inst-specultv? (INST-at-stg '(DQ 0) MT))))
		  (not (b1p (INST-modified? (INST-at-stg '(DQ 0) MT))))
		  (not (INST-fetch-error-detected-p (INST-at-stg '(DQ 0) MT))))
	     (equal (DE-RC (DQ-DE0 (MA-DQ MA)))
		    (INST-rc (INST-at-stg '(DQ 0) MT))))
  :hints (("goal" :use (:instance DQ-DE0-RC-=-inst-rc
				  (i (INST-at-stg '(DQ 0) MT))))))

(defthm DQ-DE0-RA-=-inst-ra
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-in i MT) (equal (INST-stg i) '(DQ 0))
		  (not (b1p (inst-specultv? i)))
		  (not (b1p (INST-modified? i)))
		  (not (INST-fetch-error-detected-p i)))
	     (equal (DE-RA (DQ-DE0 (MA-DQ MA)))
		    (INST-ra i)))
  :hints (("goal" :in-theory (e/d (inst-inv-def
				   INST-excpt-detected-p
				   INST-ra
				   equal-b1p-converter)
				  (INST-INV-IF-INST-IN))
		  :use (:instance INST-INV-IF-INST-IN))))

(defthm DQ-DE0-RA-=-inst-ra-2
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (uniq-INST-at-stg '(DQ 0) MT)
		  (not (b1p (inst-specultv? (INST-at-stg '(DQ 0) MT))))
		  (not (b1p (INST-modified? (INST-at-stg '(DQ 0) MT))))
		  (not (INST-fetch-error-detected-p (INST-at-stg '(DQ 0) MT))))
	     (equal (DE-RA (DQ-DE0 (MA-DQ MA)))
		    (INST-ra (INST-at-stg '(DQ 0) MT))))
  :hints (("goal" :use (:instance DQ-DE0-RA-=-inst-ra
				  (i (INST-at-stg '(DQ 0) MT))))))

(defthm DQ-DE0-RB-=-inst-rb
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-in i MT) (equal (INST-stg i) '(DQ 0))
		  (not (b1p (inst-specultv? i)))
		  (not (b1p (INST-modified? i)))
		  (not (INST-fetch-error-detected-p i)))
	     (equal (DE-RB (DQ-DE0 (MA-DQ MA)))
		    (INST-rb i)))
  :hints (("goal" :in-theory (e/d (inst-inv-def
				   INST-excpt-detected-p
				   INST-rb
				   equal-b1p-converter)
				  (INST-INV-IF-INST-IN))
		  :use (:instance INST-INV-IF-INST-IN))))

(defthm DQ-DE0-RB-=-inst-rb-2
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (uniq-INST-at-stg '(DQ 0) MT)
		  (not (b1p (inst-specultv? (INST-at-stg '(DQ 0) MT))))
		  (not (b1p (INST-modified? (INST-at-stg '(DQ 0) MT))))
		  (not (INST-fetch-error-detected-p (INST-at-stg '(DQ 0) MT))))
	     (equal (DE-RB (DQ-DE0 (MA-DQ MA)))
		    (INST-rb (INST-at-stg '(DQ 0) MT))))
  :hints (("goal" :use (:instance DQ-DE0-RB-=-inst-rb
				  (i (INST-at-stg '(DQ 0) MT))))))

(defthm DQ-DE0-IM-=-inst-im
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-in i MT) (equal (INST-stg i) '(DQ 0))
		  (not (b1p (inst-specultv? i)))
		  (not (b1p (INST-modified? i)))
		  (not (INST-fetch-error-detected-p i)))
	     (equal (DE-IM (DQ-DE0 (MA-DQ MA)))
		    (INST-im i)))
  :hints (("goal" :in-theory (e/d (inst-inv-def
				   INST-im
				   INST-excpt-detected-p
				   equal-b1p-converter)
				  (INST-INV-IF-INST-IN))
		  :use (:instance INST-INV-IF-INST-IN))))

(defthm DQ-DE0-im-=-inst-im-2
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (uniq-INST-at-stg '(DQ 0) MT)
		  (not (b1p (inst-specultv? (INST-at-stg '(DQ 0) MT))))
		  (not (b1p (INST-modified? (INST-at-stg '(DQ 0) MT))))
		  (not (INST-fetch-error-detected-p (INST-at-stg '(DQ 0) MT))))
	     (equal (DE-IM (DQ-DE0 (MA-DQ MA)))
		    (INST-im (INST-at-stg '(DQ 0) MT))))
  :hints (("goal" :use (:instance DQ-DE0-im-=-inst-im
				  (i (INST-at-stg '(DQ 0) MT))))))

(defthm DQ-DE0-br-target-=-inst-br-target
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-in i MT) (equal (INST-stg i) '(DQ 0))
		  (not (b1p (inst-specultv? i)))
		  (not (b1p (INST-modified? i)))
		  (not (INST-fetch-error-detected-p i)))
	     (equal (DE-BR-target (DQ-DE0 (MA-DQ MA)))
		    (INST-br-target i)))
  :hints (("goal" :in-theory (e/d (inst-inv-def
				   INST-excpt-detected-p
				   equal-b1p-converter)
				  (INST-INV-IF-INST-IN))
		  :use (:instance INST-INV-IF-INST-IN))))

(defthm DQ-DE0-br-target-=-inst-br-target-2
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (uniq-INST-at-stg '(DQ 0) MT)
		  (not (b1p (inst-specultv? (INST-at-stg '(DQ 0) MT))))
		  (not (b1p (INST-modified? (INST-at-stg '(DQ 0) MT))))
		  (not (INST-fetch-error-detected-p (INST-at-stg '(DQ 0) MT))))
	     (equal (DE-BR-target (DQ-DE0 (MA-DQ MA)))
		    (INST-br-target (INST-at-stg '(DQ 0) MT))))
  :hints (("goal" :use (:instance DQ-DE0-BR-target-=-inst-br-target
				  (i (INST-at-stg '(DQ 0) MT))))))

(defthm DQ-DE0-excpt-=-INST-excpt-flags
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-in i MT) (equal (INST-stg i) '(DQ 0))
		  (not (b1p (inst-specultv? i)))
		  (not (b1p (INST-modified? i))))
	     (equal (DE-excpt (DQ-DE0 (MA-DQ MA)))
		    (INST-excpt-flags i)))
  :hints (("goal" :in-theory (e/d (inst-inv-def
				   INST-excpt-detected-p
				   equal-b1p-converter)
				  (INST-INV-IF-INST-IN))
		  :use (:instance INST-INV-IF-INST-IN))))

(defthm DQ-DE0-excpt-=-inst-excpt-flags-2
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (uniq-INST-at-stg '(DQ 0) MT)
		  (not (b1p (inst-specultv? (INST-at-stg '(DQ 0) MT))))
		  (not (b1p (INST-modified? (INST-at-stg '(DQ 0) MT)))))
	     (equal (DE-excpt (DQ-DE0 (MA-DQ MA)))
		    (INST-excpt-flags (INST-at-stg '(DQ 0) MT))))
  :hints (("goal" :use (:instance DQ-DE0-excpt-=-INST-excpt-flags
				  (i (INST-at-stg '(DQ 0) MT))))))
(deflabel end-DQ-DE0-field-lemmas)
(deftheory DQ-DE0-field-lemmas
    (set-difference-theories (universal-theory 'end-DQ-DE0-field-lemmas)
			     (universal-theory 'begin-DQ-DE0-field-lemmas)))

;;;;;;;;;;;;End of DQ field lemmas;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;Field of Dispatch Output;;;;;;;;;;;;;;;;;;;;;;;;;;;
; The cntlv of a dispatched instruction is represented with INST-cntlv
; of an instruction i at (DQ 0).
(defthm dispatch-cntlv-INST-cntlv
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-p i) (INST-in i MT)
		  (equal (INST-stg i) '(DQ 0))
		  (not (b1p (inst-specultv? i)))
		  (not (b1p (INST-modified? i)))
		  (not (INST-fetch-error-detected-p i)))
	     (equal (dispatch-cntlv MA) (INST-cntlv i)))
  :hints (("goal" :in-theory (enable dispatch-cntlv)
		  :cases ((INST-fetch-error-detected-p i)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(deflabel begin-INST-types-at-execution-units)
; Only a certain type of instruction can be in an execution unit in a
; reachable state.  For instance, only an integer unit instruction can
; be in the Integer Unit, but not a multiply instruction or branch
; instruction.
(defthm INST-IU-if-IU-stg-p
    (implies (and (inv MT MA)
		  (IU-stg-p (INST-stg i))
		  (not (b1p (inst-specultv? i)))
		  (not (b1p (INST-modified? i)))
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-in i MT) (INST-p i))
	     (equal (INST-IU? i) 1))
  :hints (("goal" :in-theory (e/d (inst-inv-def equal-b1p-converter
						IU-stg-p)
				  (INST-inv-if-INST-in))
		  :use (:instance INST-inv-if-INST-in))))

(defthm INST-MU-if-MU-stg-p
    (implies (and (inv MT MA)
		  (MU-stg-p (INST-stg i))
		  (not (b1p (inst-specultv? i)))
		  (not (b1p (INST-modified? i)))
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-in i MT) (INST-p i))
	     (equal (INST-MU? i) 1))
  :hints (("goal" :in-theory (e/d (inst-inv-def equal-b1p-converter
						MU-stg-p)
				  (INST-inv-if-INST-in))
		  :use (:instance INST-inv-if-INST-in))))

(defthm INST-BU-if-BU-stg-p
    (implies (and (inv MT MA)
		  (BU-stg-p (INST-stg i))
		  (not (b1p (inst-specultv? i)))
		  (not (b1p (INST-modified? i)))
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-in i MT) (INST-p i))
	     (equal (INST-BU? i) 1))
  :hints (("goal" :in-theory (e/d (inst-inv-def equal-b1p-converter
						BU-stg-p)
				  (INST-inv-if-INST-in))
		  :use (:instance INST-inv-if-INST-in))))

(defthm INST-LSU-if-LSU-stg-p
    (implies (and (inv MT MA)
		  (LSU-stg-p (INST-stg i))
		  (not (b1p (inst-specultv? i)))
		  (not (b1p (INST-modified? i)))
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-in i MT) (INST-p i))
	     (equal (INST-LSU? i) 1))
  :hints (("goal" :in-theory (e/d (inst-inv-def equal-b1p-converter
						LSU-stg-p)
				  (INST-inv-if-INST-in))
		  :use (:instance INST-inv-if-INST-in))))
(deflabel end-INST-types-at-execution-units)

(deftheory INST-types-at-execution-units
    (set-difference-theories
     (universal-theory 'end-INST-types-at-execution-units)
     (universal-theory 'begin-INST-types-at-execution-units)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;  IU RS field lemmas
(deflabel begin-IU-RS-field-lemmas)
(defthm IU-RS0-valid-if-INST-in
    (implies (and (inv MT MA)
		  (INST-in i MT)
		  (equal (INST-stg i) '(IU RS0))
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-p i))
	     (equal (RS-valid? (IU-RS0 (MA-IU MA))) 1))
  :hints (("goal" :in-theory (e/d (inst-inv-def equal-b1p-converter)
				  (INST-inv-if-INST-in))
		  :use (:instance INST-inv-if-INST-in))))

(defthm IU-RS1-valid-if-INST-in
    (implies (and (inv MT MA)
		  (INST-in i MT)
		  (equal (INST-stg i) '(IU RS1))
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-p i))
	     (equal (RS-valid? (IU-RS1 (MA-IU MA))) 1))
  :hints (("goal" :in-theory (e/d (inst-inv-def equal-b1p-converter)
				  (INST-inv-if-INST-in))
		  :use (:instance INST-inv-if-INST-in))))

(defthm uniq-inst-at-IU-RS0-if-valid
    (implies (and (inv MT MA)
		  (b1p (RS-valid? (IU-RS0 (MA-IU MA))))
		  (MA-state-p MA) (MAETT-p MT))
	     (uniq-INST-at-stg '(IU RS0) MT))
  :hints (("goal" :in-theory (enable inv no-stage-conflict
				     no-IU-stg-conflict))))

(defthm uniq-inst-at-IU-RS1-if-valid
    (implies (and (inv MT MA)
		  (b1p (RS-valid? (IU-RS1 (MA-IU MA))))
		  (MA-state-p MA) (MAETT-p MT))
	     (uniq-INST-at-stg '(IU RS1) MT))
  :hints (("goal" :in-theory (enable inv no-stage-conflict
				     no-IU-stg-conflict))))

(defthm no-inst-at-IU-RS0
    (implies (and (inv MT MA)
		  (not (b1p (RS-valid? (IU-RS0 (MA-IU MA)))))
		  (MA-state-p MA) (MAETT-p MT))
	     (no-INST-at-stg '(IU RS0) MT))
  :hints (("goal" :in-theory (enable inv no-stage-conflict
				     no-IU-stg-conflict))))

(defthm no-inst-at-IU-RS1
    (implies (and (inv MT MA)
		  (not (b1p (RS-valid? (IU-RS1 (MA-IU MA)))))
		  (MA-state-p MA) (MAETT-p MT))
	     (no-INST-at-stg '(IU RS1) MT))
  :hints (("goal" :in-theory (enable inv no-stage-conflict
				     no-IU-stg-conflict))))

(defthm not-INST-excpt-detected-p-if-IU-stg-p
    (implies (and (inv MT MA)
		  (IU-stg-p (INST-stg i))
		  (not (b1p (inst-specultv? i)))
		  (not (b1p (INST-modified? i)))
		  (INST-in i MT)
		  (MAETT-p MT) (MA-state-p MA))
	     (not (INST-excpt-detected-p i)))
  :hints (("goal" :in-theory (e/d (inst-inv-def equal-b1p-converter
						IU-stg-p)
				  (INST-inv-if-INST-in))
		  :use (:instance INST-inv-if-INST-in))))

(defthm IU-RS0-op-=-inst-IU-op
    (implies (and (inv MT MA)
		  (INST-in i MT)
		  (equal (INST-stg i) '(IU RS0))
		  (not (b1p (inst-specultv? i)))
		  (not (b1p (INST-modified? i)))
		  (MAETT-p MT) (MA-state-p MA))
	     (equal (RS-op (IU-RS0 (MA-IU MA)))
		    (INST-IU-op? i)))
  :hints (("goal" :in-theory (e/d (inst-inv-def equal-b1p-converter)
				  (INST-inv-if-INST-in))
		  :use (:instance INST-inv-if-INST-in))))

(defthm IU-RS0-op-=-inst-IU-op-2
    (implies (and (inv MT MA)
		  (uniq-inst-at-stg '(IU RS0) MT)
		  (not (b1p (inst-specultv?
			     (inst-at-stg '(IU RS0) MT))))
		  (not (b1p (INST-modified?
			     (inst-at-stg '(IU RS0) MT))))
		  (MAETT-p MT) (MA-state-p MA))
	     (equal (RS-op (IU-RS0 (MA-IU MA)))
		    (INST-IU-op? (inst-at-stg '(IU RS0) MT))))
  :hints (("goal" :in-theory (e/d (inst-inv-def equal-b1p-converter)
				  (INST-inv-if-INST-in))
		  :use (:instance INST-inv-if-INST-in
				  (i (inst-at-stg '(IU RS0) MT))))))

(defthm IU-RS1-op-=-inst-IU-op
    (implies (and (inv MT MA)
		  (INST-in i MT)
		  (equal (INST-stg i) '(IU RS1))
		  (not (b1p (inst-specultv? i)))
		  (not (b1p (INST-modified? i)))
		  (MAETT-p MT) (MA-state-p MA))
	     (equal (RS-op (IU-RS1 (MA-IU MA)))
		    (INST-IU-op? i)))
  :hints (("goal" :in-theory (e/d (inst-inv-def equal-b1p-converter)
				  (INST-inv-if-INST-in))
		  :use (:instance INST-inv-if-INST-in))))

(defthm IU-RS1-op-=-inst-IU-op-2
    (implies (and (inv MT MA)
		  (uniq-inst-at-stg '(IU RS1) MT)
		  (not (b1p (inst-specultv?
			     (inst-at-stg '(IU RS1) MT))))
		  (not (b1p (INST-modified?
			     (inst-at-stg '(IU RS1) MT))))
		  (MAETT-p MT) (MA-state-p MA))
	     (equal (RS-op (IU-RS1 (MA-IU MA)))
		    (INST-IU-op? (inst-at-stg '(IU RS1) MT))))
  :hints (("goal" :in-theory (e/d (inst-inv-def equal-b1p-converter)
				  (INST-inv-if-INST-in))
		  :use (:instance INST-inv-if-INST-in
				  (i (inst-at-stg '(IU RS1) MT))))))

(defthm IU-RS0-tag-=-inst-tag
    (implies (and (inv MT MA)
		  (INST-in i MT)
		  (equal (INST-stg i) '(IU RS0))
		  (MAETT-p MT) (MA-state-p MA))
	     (equal (RS-tag (IU-RS0 (MA-IU MA)))
		    (INST-tag i)))
  :hints (("goal" :in-theory (e/d (inst-inv-def equal-b1p-converter)
				  (INST-inv-if-INST-in))
		  :use (:instance INST-inv-if-INST-in))))

(defthm IU-RS0-tag-=-inst-tag-2
    (implies (and (inv MT MA)
		  (uniq-inst-at-stg '(IU RS0) MT)
		  (MAETT-p MT) (MA-state-p MA))
	     (equal (RS-tag (IU-RS0 (MA-IU MA)))
		    (INST-tag (INST-at-stg '(IU RS0) MT))))
  :hints (("goal" :in-theory (e/d (inst-inv-def equal-b1p-converter)
				  (INST-inv-if-INST-in))
		  :use (:instance INST-inv-if-INST-in
				  (i (INST-at-stg '(IU RS0) MT))))))

(defthm IU-RS-tag-=-inst-tag
    (implies (and (inv MT MA)
		  (INST-in i MT)
		  (equal (INST-stg i) '(IU RS1))
		  (MAETT-p MT) (MA-state-p MA))
	     (equal (RS-tag (IU-RS1 (MA-IU MA)))
		    (INST-tag i)))
  :hints (("goal" :in-theory (e/d (inst-inv-def equal-b1p-converter)
				  (INST-inv-if-INST-in))
		  :use (:instance INST-inv-if-INST-in))))

(defthm IU-RS-tag-=-inst-tag-2
    (implies (and (inv MT MA)
		  (uniq-inst-at-stg '(IU RS1) MT)
		  (MAETT-p MT) (MA-state-p MA))
	     (equal (RS-tag (IU-RS1 (MA-IU MA)))
		    (INST-tag (INST-at-stg '(IU RS1) MT))))
  :hints (("goal" :in-theory (e/d (inst-inv-def equal-b1p-converter)
				  (INST-inv-if-INST-in))
		  :use (:instance INST-inv-if-INST-in
				  (i (INST-at-stg '(IU RS1) MT))))))

(defthm IU-RS0-val1-=-INST-src-val1
    (implies (and (inv MT MA)
		  (INST-in i MT)
		  (equal (INST-stg i) '(IU RS0))
		  (not (b1p (inst-specultv? i)))
		  (not (b1p (INST-modified? i)))
		  (b1p (RS-ready1? (IU-RS0 (MA-IU MA))))
		  (MAETT-p MT) (MA-state-p MA))
	     (equal (RS-val1 (IU-RS0 (MA-IU MA)))
		    (INST-src-val1 i)))
  :hints (("goal" :in-theory (e/d (inst-inv-def equal-b1p-converter)
				  (INST-inv-if-INST-in))
		  :use (:instance INST-inv-if-INST-in))))

(defthm IU-RS0-val1-=-INST-src-val1-2
    (implies (and (inv MT MA)
		  (uniq-inst-at-stg '(IU RS0) MT)
		  (not (b1p (inst-specultv?
			     (inst-at-stg '(IU RS0) MT))))
		  (not (b1p (INST-modified?
			     (inst-at-stg '(IU RS0) MT))))
		  (b1p (RS-ready1? (IU-RS0 (MA-IU MA))))
		  (MAETT-p MT) (MA-state-p MA))
	     (equal (RS-val1 (IU-RS0 (MA-IU MA)))
		    (INST-src-val1
		     (inst-at-stg '(IU RS0) MT))))
  :hints (("goal" :in-theory (e/d (inst-inv-def equal-b1p-converter)
				  (INST-inv-if-INST-in))
		  :use (:instance INST-inv-if-INST-in
				  (i (inst-at-stg '(IU RS0) MT))))))

(defthm IU-RS1-val1-=-INST-src-val1
    (implies (and (inv MT MA)
		  (INST-in i MT)
		  (equal (INST-stg i) '(IU RS1))
		  (not (b1p (inst-specultv? i)))
		  (not (b1p (INST-modified? i)))
		  (b1p (RS-ready1? (IU-RS1 (MA-IU MA))))
		  (MAETT-p MT) (MA-state-p MA))
	     (equal (RS-val1 (IU-RS1 (MA-IU MA)))
		    (INST-src-val1 i)))
  :hints (("goal" :in-theory (e/d (inst-inv-def equal-b1p-converter)
				  (INST-inv-if-INST-in))
		  :use (:instance INST-inv-if-INST-in))))

(defthm IU-RS1-val1-=-INST-src-val1-2
    (implies (and (inv MT MA)
		  (uniq-inst-at-stg '(IU RS1) MT)
		  (not (b1p (inst-specultv?
			     (INST-at-stg '(IU RS1) MT))))
		  (not (b1p (INST-modified?
			     (INST-at-stg '(IU RS1) MT))))
		  (b1p (RS-ready1? (IU-RS1 (MA-IU MA))))
		  (MAETT-p MT) (MA-state-p MA))
	     (equal (RS-val1 (IU-RS1 (MA-IU MA)))
		    (INST-src-val1 (INST-at-stg '(IU RS1) MT))))
  :hints (("goal" :in-theory (e/d (inst-inv-def equal-b1p-converter)
				  (INST-inv-if-INST-in))
		  :use (:instance INST-inv-if-INST-in
				  (i (INST-at-stg '(IU RS1) MT))))))

(defthm IU-RS0-val2-=-INST-src-val2
    (implies (and (inv MT MA)
		  (INST-in i MT)
		  (equal (INST-stg i) '(IU RS0))
		  (not (b1p (inst-specultv? i)))
		  (not (b1p (INST-modified? i)))
		  (b1p (RS-ready2? (IU-RS0 (MA-IU MA))))
		  (not (b1p (INST-IU-op? i)))
		  (MAETT-p MT) (MA-state-p MA))
	     (equal (RS-val2 (IU-RS0 (MA-IU MA)))
		    (INST-src-val2 i)))
  :hints (("goal" :in-theory (e/d (inst-inv-def equal-b1p-converter)
				  (INST-inv-if-INST-in))
		  :use (:instance INST-inv-if-INST-in))))

(defthm IU-RS0-val2-=-INST-src-val2-2
    (implies (and (inv MT MA)
		  (uniq-inst-at-stg '(IU RS0) MT)
		  (not (b1p (inst-specultv?
			     (INST-at-stg '(IU RS0) MT))))
		  (not (b1p (INST-modified?
			     (INST-at-stg '(IU RS0) MT))))
		  (b1p (RS-ready2? (IU-RS0 (MA-IU MA))))
		  (not (b1p (INST-IU-op?
			     (INST-at-stg '(IU RS0) MT))))
		  (MAETT-p MT) (MA-state-p MA))
	     (equal (RS-val2 (IU-RS0 (MA-IU MA)))
		    (INST-src-val2 (INST-at-stg '(IU RS0) MT))))
  :hints (("goal" :in-theory (e/d (inst-inv-def equal-b1p-converter)
				  (INST-inv-if-INST-in))
		  :use (:instance INST-inv-if-INST-in
				  (i (INST-at-stg '(IU RS0) MT))))))

(defthm IU-RS1-val2-=-INST-src-val2
    (implies (and (inv MT MA)
		  (INST-in i MT)
		  (equal (INST-stg i) '(IU RS1))
		  (not (b1p (inst-specultv? i)))
		  (not (b1p (INST-modified? i)))
		  (b1p (RS-ready2? (IU-RS1 (MA-IU MA))))
		  (not (b1p (INST-IU-op? i)))
		  (MAETT-p MT) (MA-state-p MA))
	     (equal (RS-val2 (IU-RS1 (MA-IU MA)))
		    (INST-src-val2 i)))
  :hints (("goal" :in-theory (e/d (inst-inv-def equal-b1p-converter)
				  (INST-inv-if-INST-in))
		  :use (:instance INST-inv-if-INST-in))))

(defthm IU-RS1-val2-=-INST-src-val2-2
    (implies (and (inv MT MA)
		  (uniq-inst-at-stg '(IU RS1) MT)
		  (not (b1p (inst-specultv?
			     (inst-at-stg  '(IU RS1) MT))))
		  (not (b1p (INST-modified?
			     (inst-at-stg  '(IU RS1) MT))))
		  (b1p (RS-ready2? (IU-RS1 (MA-IU MA))))
		  (not (b1p (INST-IU-op?
			     (inst-at-stg  '(IU RS1) MT))))
		  (MAETT-p MT) (MA-state-p MA))
	     (equal (RS-val2 (IU-RS1 (MA-IU MA)))
		    (INST-src-val2 (inst-at-stg  '(IU RS1) MT))))
  :hints (("goal" :in-theory (e/d (inst-inv-def equal-b1p-converter)
				  (INST-inv-if-INST-in))
		  :use (:instance INST-inv-if-INST-in
				  (i (inst-at-stg  '(IU RS1) MT))))))

(deflabel end-IU-RS-field-lemmas)
(deftheory IU-RS-field-lemmas
    (set-difference-theories
     (universal-theory 'end-IU-RS-field-lemmas)
     (universal-theory 'begin-IU-RS-field-lemmas)))

(deftheory IU-RS-field-INST-at-lemmas
    '(IU-RS0-op-=-inst-IU-op-2 IU-RS1-op-=-inst-IU-op-2
      IU-RS0-tag-=-inst-tag-2 IU-RS-tag-=-inst-tag-2
      IU-RS0-val1-=-INST-src-val1-2 IU-RS1-val1-=-INST-src-val1-2
      IU-RS0-val2-=-INST-src-val2-2 IU-RS1-val2-=-INST-src-val2-2))
(in-theory (disable IU-RS-field-INST-at-lemmas))

;;;;;;;;;;;;;;;;;;;;BU field lemmas;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(deflabel begin-BU-RS-field-lemmas)
(defthm BU-RS0-valid-if-INST-in
    (implies (and (inv MT MA)
		  (INST-in i MT)
		  (equal (INST-stg i) '(BU RS0))
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-p i))
	     (equal (BU-RS-valid? (BU-RS0 (MA-BU MA))) 1))
  :hints (("goal" :in-theory (e/d (inst-inv-def equal-b1p-converter)
				  (INST-inv-if-INST-in))
		  :use (:instance INST-inv-if-INST-in))))

(defthm BU-RS1-valid-if-INST-in
    (implies (and (inv MT MA)
		  (INST-in i MT)
		  (equal (INST-stg i) '(BU RS1))
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-p i))
	     (equal (BU-RS-valid? (BU-RS1 (MA-BU MA))) 1))
  :hints (("goal" :in-theory (e/d (inst-inv-def equal-b1p-converter)
				  (INST-inv-if-INST-in))
		  :use (:instance INST-inv-if-INST-in))))

(defthm uniq-inst-at-BU-RS0-if-valid
    (implies (and (inv MT MA)
		  (b1p (BU-RS-valid? (BU-RS0 (MA-BU MA))))
		  (MA-state-p MA) (MAETT-p MT))
	     (uniq-INST-at-stg '(BU RS0) MT))
  :hints (("goal" :in-theory (enable inv no-stage-conflict
				     no-BU-stg-conflict))))

(defthm uniq-inst-at-BU-RS1-if-valid
    (implies (and (inv MT MA)
		  (b1p (BU-RS-valid? (BU-RS1 (MA-BU MA))))
		  (MA-state-p MA) (MAETT-p MT))
	     (uniq-INST-at-stg '(BU RS1) MT))
  :hints (("goal" :in-theory (enable inv no-stage-conflict
				     no-BU-stg-conflict))))

(defthm no-inst-at-BU-RS0
    (implies (and (inv MT MA)
		  (not (b1p (BU-RS-valid? (BU-RS0 (MA-BU MA)))))
		  (MA-state-p MA) (MAETT-p MT))
	     (no-INST-at-stg '(BU RS0) MT))
  :hints (("goal" :in-theory (enable inv no-stage-conflict
				     no-BU-stg-conflict))))

(defthm no-inst-at-BU-RS1
    (implies (and (inv MT MA)
		  (not (b1p (BU-RS-valid? (BU-RS1 (MA-BU MA)))))
		  (MA-state-p MA) (MAETT-p MT))
	     (no-INST-at-stg '(BU RS1) MT))
  :hints (("goal" :in-theory (enable inv no-stage-conflict
				     no-BU-stg-conflict))))

(defthm BU-RS0-tag-=-inst-tag
    (implies (and (inv MT MA)
		  (INST-in i MT)
		  (equal (INST-stg i) '(BU RS0))
		  (MAETT-p MT) (MA-state-p MA))
	     (equal (BU-RS-tag (BU-RS0 (MA-BU MA)))
		    (INST-tag i)))
  :hints (("goal" :in-theory (e/d (inst-inv-def equal-b1p-converter)
				  (INST-inv-if-INST-in))
		  :use (:instance INST-inv-if-INST-in))))

(defthm BU-RS0-tag-=-inst-tag-2
    (implies (and (inv MT MA)
		  (uniq-inst-at-stg '(BU RS0) MT)
		  (MAETT-p MT) (MA-state-p MA))
	     (equal (BU-RS-tag (BU-RS0 (MA-BU MA)))
		    (INST-tag (INST-at-stg '(BU RS0) MT))))
  :hints (("goal" :in-theory (e/d (inst-inv-def equal-b1p-converter)
				  (INST-inv-if-INST-in))
		  :use (:instance INST-inv-if-INST-in
				  (i (INST-at-stg '(BU RS0) MT))))))

(defthm BU-RS-tag-=-inst-tag
    (implies (and (inv MT MA)
		  (INST-in i MT)
		  (equal (INST-stg i) '(BU RS1))
		  (MAETT-p MT) (MA-state-p MA))
	     (equal (BU-RS-tag (BU-RS1 (MA-BU MA)))
		    (INST-tag i)))
  :hints (("goal" :in-theory (e/d (inst-inv-def equal-b1p-converter)
				  (INST-inv-if-INST-in))
		  :use (:instance INST-inv-if-INST-in))))

(defthm BU-RS-tag-=-inst-tag-2
    (implies (and (inv MT MA)
		  (uniq-inst-at-stg '(BU RS1) MT)
		  (MAETT-p MT) (MA-state-p MA))
	     (equal (BU-RS-tag (BU-RS1 (MA-BU MA)))
		    (INST-tag (INST-at-stg '(BU RS1) MT))))
  :hints (("goal" :in-theory (e/d (inst-inv-def equal-b1p-converter)
				  (INST-inv-if-INST-in))
		  :use (:instance INST-inv-if-INST-in
				  (i (INST-at-stg '(BU RS1) MT))))))

(defthm BU-RS0-val-=-INST-src-val1
    (implies (and (inv MT MA)
		  (INST-in i MT)
		  (equal (INST-stg i) '(BU RS0))
		  (b1p (BU-RS-ready? (BU-RS0 (MA-BU MA))))
		  (not (b1p (inst-specultv? i)))
		  (not (b1p (INST-modified? i)))
		  (MAETT-p MT) (MA-state-p MA))
	     (equal (BU-RS-val (BU-RS0 (MA-BU MA)))
		    (INST-src-val3 i)))
  :hints (("goal" :in-theory (e/d (inst-inv-def equal-b1p-converter)
				  (INST-inv-if-INST-in))
		  :use (:instance INST-inv-if-INST-in))))

(defthm BU-RS0-val-=-INST-src-val1-2
    (implies (and (inv MT MA)
		  (uniq-inst-at-stg '(BU RS0) MT)
		  (b1p (BU-RS-ready? (BU-RS0 (MA-BU MA))))
		  (not (b1p (inst-specultv?
			     (INST-at-stg '(BU RS0) MT))))
		  (not (b1p (INST-modified?
			     (INST-at-stg '(BU RS0) MT))))
		  (MAETT-p MT) (MA-state-p MA))
	     (equal (BU-RS-val (BU-RS0 (MA-BU MA)))
		    (INST-src-val3 (INST-at-stg '(BU RS0) MT))))
  :hints (("goal" :in-theory (e/d (inst-inv-def equal-b1p-converter)
				  (INST-inv-if-INST-in))
		  :use (:instance INST-inv-if-INST-in
				  (i (INST-at-stg '(BU RS0) MT))))))

(defthm BU-RS1-val-=-INST-src-val1
    (implies (and (inv MT MA)
		  (INST-in i MT)
		  (equal (INST-stg i) '(BU RS1))
		  (b1p (BU-RS-ready? (BU-RS1 (MA-BU MA))))
		  (not (b1p (inst-specultv? i)))
		  (not (b1p (INST-modified? i)))
		  (MAETT-p MT) (MA-state-p MA))
	     (equal (BU-RS-val (BU-RS1 (MA-BU MA)))
		    (INST-src-val3 i)))
  :hints (("goal" :in-theory (e/d (inst-inv-def equal-b1p-converter)
				  (INST-inv-if-INST-in))
		  :use (:instance INST-inv-if-INST-in))))

(defthm BU-RS1-val-=-INST-src-val1-2
    (implies (and (inv MT MA)
		  (uniq-inst-at-stg '(BU RS1) MT)
		  (b1p (BU-RS-ready? (BU-RS1 (MA-BU MA))))
		  (not (b1p (inst-specultv?
			     (INST-at-stg '(BU RS1) MT))))
		  (not (b1p (INST-modified?
			     (INST-at-stg '(BU RS1) MT))))
		  (MAETT-p MT) (MA-state-p MA))
	     (equal (BU-RS-val (BU-RS1 (MA-BU MA)))
		    (INST-src-val3 (INST-at-stg '(BU RS1) MT))))
  :hints (("goal" :in-theory (e/d (inst-inv-def equal-b1p-converter)
				  (INST-inv-if-INST-in))
		  :use (:instance INST-inv-if-INST-in
				  (i (INST-at-stg '(BU RS1) MT))))))

(deflabel end-BU-RS-field-lemmas)
(deftheory BU-RS-field-lemmas
    (set-difference-theories
     (universal-theory 'end-BU-RS-field-lemmas)
     (universal-theory 'begin-BU-RS-field-lemmas)))
(deftheory BU-RS-field-INST-at-lemmas
    '(BU-RS0-tag-=-inst-tag-2 BU-RS-tag-=-inst-tag-2
      BU-RS1-val-=-INST-src-val1-2 BU-RS0-val-=-INST-src-val1-2))
(in-theory (disable BU-RS-field-INST-at-lemmas))

;;;;;;;;;;;;;;;;;;;;;MU field lemmas;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(deflabel begin-MU-field-lemmas)
(deflabel begin-MU-RS-field-lemmas)

(defthm MU-RS0-valid-if-INST-in
    (implies (and (inv MT MA)
		  (INST-in i MT)
		  (equal (INST-stg i) '(MU RS0))
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-p i))
	     (equal (RS-valid? (MU-RS0 (MA-MU MA))) 1))
  :hints (("goal" :in-theory (e/d (inst-inv-def equal-b1p-converter)
				  (INST-inv-if-INST-in))
		  :use (:instance INST-inv-if-INST-in))))

(defthm MU-RS1-valid-if-INST-in
    (implies (and (inv MT MA)
		  (INST-in i MT)
		  (equal (INST-stg i) '(MU RS1))
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-p i))
	     (equal (RS-valid? (MU-RS1 (MA-MU MA))) 1))
  :hints (("goal" :in-theory (e/d (inst-inv-def equal-b1p-converter)
				  (INST-inv-if-INST-in))
		  :use (:instance INST-inv-if-INST-in))))

(defthm uniq-inst-at-MU-RS0-if-valid
    (implies (and (inv MT MA)
		  (b1p (RS-valid? (MU-rs0 (MA-MU MA))))
		  (MA-state-p MA) (MAETT-p MT))
	     (uniq-INST-at-stg '(MU RS0) MT))
  :hints (("goal" :in-theory (enable inv no-stage-conflict
				     no-MU-stg-conflict))))

(defthm uniq-inst-at-MU-RS1-if-valid
    (implies (and (inv MT MA)
		  (b1p (RS-valid? (MU-rs1 (MA-MU MA))))
		  (MA-state-p MA) (MAETT-p MT))
	     (uniq-INST-at-stg '(MU RS1) MT))
  :hints (("goal" :in-theory (enable inv no-stage-conflict
				     no-MU-stg-conflict))))

(defthm no-inst-at-MU-RS0
    (implies (and (inv MT MA)
		  (not (b1p (RS-valid? (MU-rs0 (MA-MU MA)))))
		  (MA-state-p MA) (MAETT-p MT))
	     (no-INST-at-stg '(MU RS0) MT))
  :hints (("goal" :in-theory (enable inv no-stage-conflict
				     no-MU-stg-conflict))))

(defthm no-inst-at-MU-RS1
    (implies (and (inv MT MA)
		  (not (b1p (RS-valid? (MU-rs1 (MA-MU MA)))))
		  (MA-state-p MA) (MAETT-p MT))
	     (no-INST-at-stg '(MU RS1) MT))
  :hints (("goal" :in-theory (enable inv no-stage-conflict
				     no-MU-stg-conflict))))

(defthm MU-RS0-tag-=-inst-tag
    (implies (and (inv MT MA)
		  (INST-in i MT)
		  (equal (INST-stg i) '(MU RS0))
		  (MAETT-p MT) (MA-state-p MA))
	     (equal (RS-tag (MU-RS0 (MA-MU MA)))
		    (INST-tag i)))
  :hints (("goal" :in-theory (e/d (inst-inv-def equal-b1p-converter)
				  (INST-inv-if-INST-in))
		  :use (:instance INST-inv-if-INST-in))))

(defthm MU-RS0-tag-=-inst-tag-2
    (implies (and (inv MT MA)
		  (uniq-inst-at-stg '(MU RS0) MT)
		  (MAETT-p MT) (MA-state-p MA))
	     (equal (RS-tag (MU-RS0 (MA-MU MA)))
		    (INST-tag (INST-at-stg '(MU RS0) MT))))
  :hints (("goal" :in-theory (e/d (inst-inv-def equal-b1p-converter)
				  (INST-inv-if-INST-in))
		  :use (:instance INST-inv-if-INST-in
				  (i (INST-at-stg '(MU RS0) MT))))))

(defthm MU-RS-tag-=-inst-tag
    (implies (and (inv MT MA)
		  (INST-in i MT)
		  (equal (INST-stg i) '(MU RS1))
		  (MAETT-p MT) (MA-state-p MA))
	     (equal (RS-tag (MU-RS1 (MA-MU MA)))
		    (INST-tag i)))
  :hints (("goal" :in-theory (e/d (inst-inv-def equal-b1p-converter)
				  (INST-inv-if-INST-in))
		  :use (:instance INST-inv-if-INST-in))))

(defthm MU-RS-tag-=-inst-tag-2
    (implies (and (inv MT MA)
		  (uniq-inst-at-stg '(MU RS1) MT)
		  (MAETT-p MT) (MA-state-p MA))
	     (equal (RS-tag (MU-RS1 (MA-MU MA)))
		    (INST-tag (INST-at-stg '(MU RS1) MT))))
  :hints (("goal" :in-theory (e/d (inst-inv-def equal-b1p-converter)
				  (INST-inv-if-INST-in))
		  :use (:instance INST-inv-if-INST-in
				  (i (INST-at-stg '(MU RS1) MT))))))

(defthm MU-RS0-val1-=-INST-src-val1
    (implies (and (inv MT MA)
		  (INST-in i MT)
		  (equal (INST-stg i) '(MU RS0))
		  (b1p (RS-ready1? (MU-RS0 (MA-MU MA))))
		  (not (b1p (inst-specultv? i)))
		  (not (b1p (INST-modified? i)))
		  (MAETT-p MT) (MA-state-p MA))
	     (equal (RS-val1 (MU-RS0 (MA-MU MA))) (INST-src-val1 i)))
  :hints (("goal" :in-theory (e/d (inst-inv-def equal-b1p-converter)
				  (INST-inv-if-INST-in))
		  :use (:instance INST-inv-if-INST-in))))

(defthm MU-RS0-val1-=-INST-src-val1-2
    (implies (and (inv MT MA)
		  (uniq-inst-at-stg '(MU RS0) MT)
		  (b1p (RS-ready1? (MU-RS0 (MA-MU MA))))
		  (not (b1p (inst-specultv?
			     (INST-at-stg '(MU RS0) MT))))
		  (not (b1p (INST-modified?
			     (INST-at-stg '(MU RS0) MT))))
		  (MAETT-p MT) (MA-state-p MA))
	     (equal (RS-val1 (MU-RS0 (MA-MU MA)))
		    (INST-src-val1 (INST-at-stg '(MU RS0) MT))))
  :hints (("goal" :in-theory (e/d (inst-inv-def equal-b1p-converter)
				  (INST-inv-if-INST-in))
		  :use (:instance INST-inv-if-INST-in
				  (i (INST-at-stg '(MU RS0) MT))))))

(defthm MU-RS1-val1-=-INST-src-val1
    (implies (and (inv MT MA)
		  (INST-in i MT)
		  (equal (INST-stg i) '(MU RS1))
		  (b1p (RS-ready1? (MU-RS1 (MA-MU MA))))
		  (not (b1p (inst-specultv? i)))
		  (not (b1p (INST-modified? i)))
		  (MAETT-p MT) (MA-state-p MA))
	     (equal (RS-val1 (MU-RS1 (MA-MU MA))) (INST-src-val1 i)))
  :hints (("goal" :in-theory (e/d (inst-inv-def equal-b1p-converter)
				  (INST-inv-if-INST-in))
		  :use (:instance INST-inv-if-INST-in))))

(defthm MU-RS1-val1-=-INST-src-val1-2
    (implies (and (inv MT MA)
		  (uniq-inst-at-stg '(MU RS1) MT)
		  (b1p (RS-ready1? (MU-RS1 (MA-MU MA))))
		  (not (b1p (inst-specultv?
			     (INST-at-stg '(MU RS1) MT))))
		  (not (b1p (INST-modified?
			     (INST-at-stg '(MU RS1) MT))))
		  (MAETT-p MT) (MA-state-p MA))
	     (equal (RS-val1 (MU-RS1 (MA-MU MA)))
		    (INST-src-val1 (INST-at-stg '(MU RS1) MT))))
  :hints (("goal" :in-theory (e/d (inst-inv-def equal-b1p-converter)
				  (INST-inv-if-INST-in))
		  :use (:instance INST-inv-if-INST-in
				  (i (INST-at-stg '(MU RS1) MT))))))

(defthm MU-RS0-val2-=-INST-src-val2
    (implies (and (inv MT MA)
		  (INST-in i MT)
		  (equal (INST-stg i) '(MU RS0))
		  (b1p (RS-ready2? (MU-RS0 (MA-MU MA))))
		  (not (b1p (inst-specultv? i)))
		  (not (b1p (INST-modified? i)))
		  (MAETT-p MT) (MA-state-p MA))
	     (equal (RS-val2 (MU-RS0 (MA-MU MA))) (INST-src-val2 i)))
  :hints (("goal" :in-theory (e/d (inst-inv-def equal-b1p-converter)
				  (INST-inv-if-INST-in))
		  :use (:instance INST-inv-if-INST-in))))

(defthm MU-RS0-val2-=-INST-src-val2-2
    (implies (and (inv MT MA)
		  (uniq-inst-at-stg '(MU RS0) MT)
		  (b1p (RS-ready2? (MU-RS0 (MA-MU MA))))
		  (not (b1p (inst-specultv?
			     (INST-at-stg '(MU RS0) MT))))
		  (not (b1p (INST-modified?
			     (INST-at-stg '(MU RS0) MT))))
		  (MAETT-p MT) (MA-state-p MA))
	     (equal (RS-val2 (MU-RS0 (MA-MU MA)))
		    (INST-src-val2 (INST-at-stg '(MU RS0) MT))))
  :hints (("goal" :in-theory (e/d (inst-inv-def equal-b1p-converter)
				  (INST-inv-if-INST-in))
		  :use (:instance INST-inv-if-INST-in
				  (i (INST-at-stg '(MU RS0) MT))))))

(defthm MU-RS1-val2-=-INST-src-val2
    (implies (and (inv MT MA)
		  (INST-in i MT)
		  (equal (INST-stg i) '(MU RS1))
		  (b1p (RS-ready2? (MU-RS1 (MA-MU MA))))
		  (not (b1p (inst-specultv? i)))
		  (not (b1p (INST-modified? i)))
		  (MAETT-p MT) (MA-state-p MA))
	     (equal (RS-val2 (MU-RS1 (MA-MU MA))) (INST-src-val2 i)))
  :hints (("goal" :in-theory (e/d (inst-inv-def equal-b1p-converter)
				  (INST-inv-if-INST-in))
		  :use (:instance INST-inv-if-INST-in))))

(defthm MU-RS1-val2-=-INST-src-val2-2
    (implies (and (inv MT MA)
		  (uniq-inst-at-stg '(MU RS1) MT)
		  (b1p (RS-ready2? (MU-RS1 (MA-MU MA))))
		  (not (b1p (inst-specultv?
			     (INST-at-stg '(MU RS1) MT))))
		  (not (b1p (INST-modified?
			     (INST-at-stg '(MU RS1) MT))))
		  (MAETT-p MT) (MA-state-p MA))
	     (equal (RS-val2 (MU-RS1 (MA-MU MA)))
		    (INST-src-val2 (INST-at-stg '(MU RS1) MT))))
  :hints (("goal" :in-theory (e/d (inst-inv-def equal-b1p-converter)
				  (INST-inv-if-INST-in))
		  :use (:instance INST-inv-if-INST-in
				  (i (INST-at-stg '(MU RS1) MT))))))

(deflabel end-MU-RS-field-lemmas)
(deftheory MU-RS-field-inst-at-lemmas
    '(MU-RS0-tag-=-inst-tag-2 MU-RS-tag-=-inst-tag-2
      MU-RS0-val1-=-INST-src-val1-2 MU-RS1-val1-=-INST-src-val1-2
      MU-RS0-val2-=-INST-src-val2-2 MU-RS1-val2-=-INST-src-val2-2))
(in-theory (disable MU-RS-field-inst-at-lemmas))

(deflabel begin-MU-latch-field-lemmas)

(defthm MU-lch1-valid-if-INST-in
    (implies (and (inv MT MA)
		  (INST-in i MT)
		  (equal (INST-stg i) '(MU lch1))
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-p i))
	     (equal (MU-latch1-valid? (MU-lch1 (MA-MU MA))) 1))
  :hints (("goal" :in-theory (e/d (inst-inv-def equal-b1p-converter)
				  (INST-inv-if-INST-in))
		  :use (:instance INST-inv-if-INST-in))))

(defthm uniq-inst-at-MU-lch1-if-valid
    (implies (and (inv MT MA)
		  (b1p (MU-latch1-valid? (MU-lch1 (MA-MU MA))))
		  (MA-state-p MA) (MAETT-p MT))
	     (uniq-INST-at-stg '(MU lch1) MT))
  :hints (("goal" :in-theory (enable inv no-stage-conflict
				     no-MU-stg-conflict))))
(defthm no-inst-at-MU-lch1
    (implies (and (inv MT MA)
		  (not (b1p (MU-latch1-valid? (MU-lch1 (MA-MU MA)))))
		  (MA-state-p MA) (MAETT-p MT))
	     (no-INST-at-stg '(MU lch1) MT))
  :hints (("goal" :in-theory (enable inv no-stage-conflict
				     no-MU-stg-conflict))))

(defthm MU-lch1-tag-=-inst-tag
    (implies (and (inv MT MA)
		  (INST-in i MT)
		  (equal (INST-stg i) '(MU lch1))
		  (MAETT-p MT) (MA-state-p MA))
	     (equal (MU-latch1-tag (MU-lch1 (MA-MU MA)))
		    (INST-tag i)))
  :hints (("goal" :in-theory (e/d (inst-inv-def equal-b1p-converter)
				  (INST-inv-if-INST-in))
		  :use (:instance INST-inv-if-INST-in))))

(defthm MU-lch1-tag-=-inst-tag-2
    (implies (and (inv MT MA)
		  (uniq-inst-at-stg '(MU lch1) MT)
		  (MAETT-p MT) (MA-state-p MA))
	     (equal (MU-latch1-tag (MU-lch1 (MA-MU MA)))
		    (INST-tag (INST-at-stg '(MU lch1) MT))))
  :hints (("goal" :in-theory (e/d (inst-inv-def equal-b1p-converter)
				  (INST-inv-if-INST-in))
		  :use (:instance INST-inv-if-INST-in
				  (i (INST-at-stg '(MU lch1) MT))))))

(defthm MU-lch1-data-=-ML1-output
    (implies (and (inv MT MA)
		  (INST-in i MT)
		  (equal (INST-stg i) '(MU lch1))
		  (not (b1p (inst-specultv? i)))
		  (not (b1p (INST-modified? i)))
		  (MAETT-p MT) (MA-state-p MA))
	     (equal (MU-latch1-data (MU-lch1 (MA-MU MA)))
		    (ML1-output (INST-src-val1 i) (INST-src-val2 i))))
  :hints (("goal" :in-theory (e/d (inst-inv-def equal-b1p-converter)
				  (INST-inv-if-INST-in))
		  :use (:instance INST-inv-if-INST-in))))

(defthm MU-lch1-data-=-ML1-output-2
    (implies (and (inv MT MA)
		  (uniq-inst-at-stg '(MU lch1) MT)
		  (not (b1p (inst-specultv?
			     (INST-at-stg '(MU lch1) MT))))
		  (not (b1p (INST-modified?
			     (INST-at-stg '(MU lch1) MT))))
		  (MAETT-p MT) (MA-state-p MA))
	     (equal (MU-latch1-data (MU-lch1 (MA-MU MA)))
		    (ML1-output (INST-src-val1 (INST-at-stg '(MU lch1) MT))
				(INST-src-val2 (INST-at-stg '(MU lch1) MT)))))
  :hints (("goal" :in-theory (e/d (inst-inv-def equal-b1p-converter)
				  (INST-inv-if-INST-in))
		  :use (:instance INST-inv-if-INST-in
				  (i (INST-at-stg '(MU lch1) MT))))))
(deftheory MU-lch1-field-INST-at-lemmas
    '(MU-lch1-tag-=-inst-tag-2 MU-lch1-data-=-ML1-output-2))
(in-theory (disable MU-lch1-field-INST-at-lemmas))

(defthm MU-lch2-valid-if-INST-in
    (implies (and (inv MT MA)
		  (INST-in i MT)
		  (equal (INST-stg i) '(MU lch2))
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-p i))
	     (equal (MU-latch2-valid? (MU-lch2 (MA-MU MA))) 1))
  :hints (("goal" :in-theory (e/d (inst-inv-def equal-b1p-converter)
				  (INST-inv-if-INST-in))
		  :use (:instance INST-inv-if-INST-in))))

(defthm uniq-inst-at-MU-lch2-if-valid
    (implies (and (inv MT MA)
		  (b1p (MU-latch2-valid? (MU-lch2 (MA-MU MA))))
		  (MA-state-p MA) (MAETT-p MT))
	     (uniq-INST-at-stg '(MU lch2) MT))
  :hints (("goal" :in-theory (enable inv no-stage-conflict
				     no-MU-stg-conflict))))

(defthm no-inst-at-MU-lch2
    (implies (and (inv MT MA)
		  (not (b1p (MU-latch2-valid? (MU-lch2 (MA-MU MA)))))
		  (MA-state-p MA) (MAETT-p MT))
	     (no-INST-at-stg '(MU lch2) MT))
  :hints (("goal" :in-theory (enable inv no-stage-conflict
				     no-MU-stg-conflict))))
(defthm MU-lch2-tag-=-inst-tag
    (implies (and (inv MT MA)
		  (INST-in i MT)
		  (equal (INST-stg i) '(MU lch2))
		  (MAETT-p MT) (MA-state-p MA))
	     (equal (MU-latch2-tag (MU-lch2 (MA-MU MA)))
		    (INST-tag i)))
  :hints (("goal" :in-theory (e/d (inst-inv-def equal-b1p-converter)
				  (INST-inv-if-INST-in))
		  :use (:instance INST-inv-if-INST-in))))

(defthm MU-lch2-tag-=-inst-tag-2
    (implies (and (inv MT MA)
		  (uniq-inst-at-stg '(MU lch2) MT)
		  (MAETT-p MT) (MA-state-p MA))
	     (equal (MU-latch2-tag (MU-lch2 (MA-MU MA)))
		    (INST-tag (INST-at-stg '(MU lch2) MT))))
  :hints (("goal" :in-theory (e/d (inst-inv-def equal-b1p-converter)
				  (INST-inv-if-INST-in))
		  :use (:instance INST-inv-if-INST-in
				  (i (INST-at-stg '(MU lch2) MT))))))

(defthm MU-lch2-data-=-ML2-output-ML2-output
    (implies (and (inv MT MA)
		  (INST-in i MT)
		  (equal (INST-stg i) '(MU lch2))
		  (not (b1p (inst-specultv? i)))
		  (not (b1p (INST-modified? i)))
		  (MAETT-p MT) (MA-state-p MA))
	     (equal (MU-latch2-data (MU-lch2 (MA-MU MA)))
		    (ML2-output (ML1-output (INST-src-val1 i)
					    (INST-src-val2 i)))))
  :hints (("goal" :in-theory (e/d (inst-inv-def equal-b1p-converter)
				  (INST-inv-if-INST-in))
		  :use (:instance INST-inv-if-INST-in))))

(defthm MU-lch2-data-=-ML2-output-ML2-output-2
    (implies (and (inv MT MA)
		  (uniq-inst-at-stg '(MU lch2) MT)
		  (not (b1p (inst-specultv?
			     (INST-at-stg '(MU lch2) MT))))
		  (not (b1p (INST-modified?
			     (INST-at-stg '(MU lch2) MT))))
		  (MAETT-p MT) (MA-state-p MA))
	     (equal (MU-latch2-data (MU-lch2 (MA-MU MA)))
		    (ML2-output
		     (ML1-output (INST-src-val1
				  (INST-at-stg '(MU lch2) MT))
				 (INST-src-val2
				  (INST-at-stg '(MU lch2) MT))))))
  :hints (("goal" :in-theory (e/d (inst-inv-def equal-b1p-converter)
				  (INST-inv-if-INST-in))
		  :use (:instance INST-inv-if-INST-in
				  (i (INST-at-stg '(MU lch2) MT))))))
(deflabel end-MU-field-lemmas)
(deftheory MU-field-lemmas
    (set-difference-theories
     (universal-theory 'end-MU-field-lemmas)
     (universal-theory 'begin-MU-field-lemmas)))
(deftheory MU-lch2-field-INST-at-lemmas
    '(MU-lch2-tag-=-inst-tag-2 MU-lch2-data-=-ML2-output-ML2-output-2))
(in-theory (disable MU-lch2-field-INST-at-lemmas))

(deftheory MU-field-INST-at-lemmas
    (union-theories (theory 'MU-RS-field-INST-at-lemmas)
    (union-theories (theory 'MU-lch1-field-INST-at-lemmas)
		    (theory 'MU-lch2-field-INST-at-lemmas))))

;;;;;;;;;;;;;;;;;;;;;;; LSU field lemmas;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(deflabel begin-LSU-field-lemmas)

(deflabel begin-LSU-RS-field-lemmas)

(defthm LSU-RS0-valid-if-INST-in
    (implies (and (inv MT MA)
		  (INST-in i MT)
		  (equal (INST-stg i) '(LSU RS0))
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-p i))
	     (equal (LSU-RS-valid? (LSU-RS0 (MA-LSU MA))) 1))
  :hints (("goal" :in-theory (e/d (inst-inv-def equal-b1p-converter)
				  (INST-inv-if-INST-in))
		  :use (:instance INST-inv-if-INST-in))))

(defthm LSU-RS1-valid-if-INST-in
    (implies (and (inv MT MA)
		  (INST-in i MT)
		  (equal (INST-stg i) '(LSU RS1))
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-p i))
	     (equal (LSU-RS-valid? (LSU-RS1 (MA-LSU MA))) 1))
  :hints (("goal" :in-theory (e/d (inst-inv-def equal-b1p-converter)
				  (INST-inv-if-INST-in))
		  :use (:instance INST-inv-if-INST-in))))

(defthm uniq-inst-at-LSU-RS0-if-valid
    (implies (and (inv MT MA)
		  (b1p (LSU-RS-valid? (LSU-rs0 (MA-LSU MA))))
		  (MA-state-p MA) (MAETT-p MT))
	     (uniq-INST-at-stg '(LSU RS0) MT))
  :hints (("goal" :in-theory (enable inv no-stage-conflict
				     no-LSU-stg-conflict))))

(defthm uniq-inst-at-LSU-RS1-if-valid
    (implies (and (inv MT MA)
		  (b1p (LSU-RS-valid? (LSU-rs1 (MA-LSU MA))))
		  (MA-state-p MA) (MAETT-p MT))
	     (uniq-INST-at-stg '(LSU RS1) MT))
  :hints (("goal" :in-theory (enable inv no-stage-conflict
				     no-LSU-stg-conflict))))

(defthm no-inst-at-LSU-RS0
    (implies (and (inv MT MA)
		  (not (b1p (LSU-RS-valid? (LSU-rs0 (MA-LSU MA)))))
		  (MA-state-p MA) (MAETT-p MT))
	     (no-INST-at-stg '(LSU RS0) MT))
  :hints (("goal" :in-theory (enable inv no-stage-conflict
				     no-LSU-stg-conflict))))

(defthm no-inst-at-LSU-RS1
    (implies (and (inv MT MA)
		  (not (b1p (LSU-RS-valid? (LSU-rs1 (MA-LSU MA)))))
		  (MA-state-p MA) (MAETT-p MT))
	     (no-INST-at-stg '(LSU RS1) MT))
  :hints (("goal" :in-theory (enable inv no-stage-conflict
				     no-LSU-stg-conflict))))

(defthm not-INST-excpt-detected-p-if-LSU-RS0
    (implies (and (inv MT MA)
		  (equal (INST-stg i) '(LSU RS0))
		  (not (b1p (inst-specultv? i)))
		  (not (b1p (INST-modified? i)))
		  (INST-in i MT)
		  (MAETT-p MT) (MA-state-p MA))
	     (not (INST-excpt-detected-p i)))
  :hints (("goal" :in-theory (e/d (inst-inv-def equal-b1p-converter)
				  (INST-inv-if-INST-in))
		  :use (:instance INST-inv-if-INST-in))))

(defthm not-INST-excpt-detected-p-if-LSU-RS1
    (implies (and (inv MT MA)
		  (equal (INST-stg i) '(LSU RS1))
		  (not (b1p (inst-specultv? i)))
		  (not (b1p (INST-modified? i)))
		  (INST-in i MT)
		  (MAETT-p MT) (MA-state-p MA))
	     (not (INST-excpt-detected-p i)))
  :hints (("goal" :in-theory (e/d (inst-inv-def equal-b1p-converter)
				  (INST-inv-if-INST-in))
		  :use (:instance INST-inv-if-INST-in))))

(defthm not-LSU-RS0-op-if-not-LSU-RS-rdy1
    (implies (and (inv MT MA)
		  (not (b1p (LSU-RS-rdy1? (LSU-RS0 (MA-LSU MA)))))
		  (INST-in i MT)
		  (equal (INST-stg i) '(LSU RS0))
		  (not (b1p (inst-specultv? i)))
		  (not (b1p (INST-modified? i)))
		  (MAETT-p MT) (MA-state-p MA))
	     (equal (INST-LSU-op? i) 0))
  :hints (("goal" :in-theory (e/d (inst-inv-def equal-b1p-converter)
				  (INST-inv-if-INST-in))
		  :use (:instance INST-inv-if-INST-in))))

(defthm not-LSU-RS1-op-if-not-LSU-RS-rdy1
    (implies (and (inv MT MA)
		  (not (b1p (LSU-RS-rdy1? (LSU-RS1 (MA-LSU MA)))))
		  (INST-in i MT)
		  (equal (INST-stg i) '(LSU RS1))
		  (not (b1p (inst-specultv? i)))
		  (not (b1p (INST-modified? i)))
		  (MAETT-p MT) (MA-state-p MA))
	     (equal (INST-LSU-op? i) 0))
  :hints (("goal" :in-theory (e/d (inst-inv-def equal-b1p-converter)
				  (INST-inv-if-INST-in))
		  :use (:instance INST-inv-if-INST-in))))

(defthm LSU-RS0-op-=-inst-LSU-op
    (implies (and (inv MT MA)
		  (INST-in i MT)
		  (equal (INST-stg i) '(LSU RS0))
		  (not (b1p (inst-specultv? i)))
		  (not (b1p (INST-modified? i)))
		  (MAETT-p MT) (MA-state-p MA))
	     (equal (LSU-RS-op (LSU-RS0 (MA-LSU MA)))
		    (INST-LSU-op? i)))
  :hints (("goal" :in-theory (e/d (inst-inv-def equal-b1p-converter)
				  (INST-inv-if-INST-in))
		  :use (:instance INST-inv-if-INST-in))))

(defthm LSU-RS0-op-=-inst-LSU-op-2
    (implies (and (inv MT MA)
		  (uniq-inst-at-stg '(LSU RS0) MT)
		  (not (b1p (inst-specultv?
			     (inst-at-stg '(LSU RS0) MT))))
		  (not (b1p (INST-modified?
			     (inst-at-stg '(LSU RS0) MT))))
		  (MAETT-p MT) (MA-state-p MA))
	     (equal (LSU-RS-op (LSU-RS0 (MA-LSU MA)))
		    (INST-LSU-op? (inst-at-stg '(LSU RS0) MT))))
  :hints (("goal" :in-theory (e/d (inst-inv-def equal-b1p-converter)
				  (INST-inv-if-INST-in))
		  :use (:instance INST-inv-if-INST-in
				  (i (inst-at-stg '(LSU RS0) MT))))))

(defthm LSU-RS1-op-=-inst-LSU-op
    (implies (and (inv MT MA)
		  (INST-in i MT)
		  (equal (INST-stg i) '(LSU RS1))
		  (not (b1p (inst-specultv? i)))
		  (not (b1p (INST-modified? i)))
		  (MAETT-p MT) (MA-state-p MA))
	     (equal (LSU-RS-op (LSU-RS1 (MA-LSU MA)))
		    (INST-LSU-op? i)))
  :hints (("goal" :in-theory (e/d (inst-inv-def equal-b1p-converter)
				  (INST-inv-if-INST-in))
		  :use (:instance INST-inv-if-INST-in))))

(defthm LSU-RS1-op-=-inst-LSU-op-2
    (implies (and (inv MT MA)
		  (uniq-inst-at-stg '(LSU RS1) MT)
		  (not (b1p (inst-specultv?
			     (inst-at-stg '(LSU RS1) MT))))
		  (not (b1p (INST-modified?
			     (inst-at-stg '(LSU RS1) MT))))
		  (MAETT-p MT) (MA-state-p MA))
	     (equal (LSU-RS-op (LSU-RS1 (MA-LSU MA)))
		    (INST-LSU-op? (inst-at-stg '(LSU RS1) MT))))
  :hints (("goal" :in-theory (e/d (inst-inv-def equal-b1p-converter)
				  (INST-inv-if-INST-in))
		  :use (:instance INST-inv-if-INST-in
				  (i (inst-at-stg '(LSU RS1) MT))))))

(defthm LSU-RS0-ld-st-=-inst-ld-st
    (implies (and (inv MT MA)
		  (INST-in i MT)
		  (equal (INST-stg i) '(LSU RS0))
		  (not (b1p (inst-specultv? i)))
		  (not (b1p (INST-modified? i)))
		  (MAETT-p MT) (MA-state-p MA))
	     (equal (LSU-RS-ld-st? (LSU-RS0 (MA-LSU MA)))
		    (INST-ld-st? i)))
  :hints (("goal" :in-theory (e/d (inst-inv-def equal-b1p-converter)
				  (INST-inv-if-INST-in))
		  :use (:instance INST-inv-if-INST-in))))

(defthm LSU-RS0-ld-st-=-inst-ld-st-2
    (implies (and (inv MT MA)
		  (uniq-inst-at-stg '(LSU RS0) MT)
		  (not (b1p (inst-specultv?
			     (inst-at-stg '(LSU RS0) MT))))
		  (not (b1p (INST-modified?
			     (inst-at-stg '(LSU RS0) MT))))
		  (MAETT-p MT) (MA-state-p MA))
	     (equal (LSU-RS-ld-st? (LSU-RS0 (MA-LSU MA)))
		    (INST-ld-st? (inst-at-stg '(LSU RS0) MT))))
  :hints (("goal" :in-theory (e/d (inst-inv-def equal-b1p-converter)
				  (INST-inv-if-INST-in))
		  :use (:instance INST-inv-if-INST-in
				  (i (inst-at-stg '(LSU RS0) MT))))))

(defthm LSU-RS1-ld-st-=-inst-ld-st
    (implies (and (inv MT MA)
		  (INST-in i MT)
		  (equal (INST-stg i) '(LSU RS1))
		  (not (b1p (inst-specultv? i)))
		  (not (b1p (INST-modified? i)))
		  (MAETT-p MT) (MA-state-p MA))
	     (equal (LSU-RS-ld-st? (LSU-RS1 (MA-LSU MA)))
		    (INST-ld-st? i)))
  :hints (("goal" :in-theory (e/d (inst-inv-def equal-b1p-converter)
				  (INST-inv-if-INST-in))
		  :use (:instance INST-inv-if-INST-in))))

(defthm LSU-RS1-ld-st-=-inst-ld-st-2
    (implies (and (inv MT MA)
		  (uniq-inst-at-stg '(LSU RS1) MT)
		  (not (b1p (inst-specultv?
			     (inst-at-stg '(LSU RS1) MT))))
		  (not (b1p (INST-modified?
			     (inst-at-stg '(LSU RS1) MT))))
		  (MAETT-p MT) (MA-state-p MA))
	     (equal (LSU-RS-ld-st? (LSU-RS1 (MA-LSU MA)))
		    (INST-ld-st? (inst-at-stg '(LSU RS1) MT))))
  :hints (("goal" :in-theory (e/d (inst-inv-def equal-b1p-converter)
				  (INST-inv-if-INST-in))
		  :use (:instance INST-inv-if-INST-in
				  (i (inst-at-stg '(LSU RS1) MT))))))

(defthm LSU-RS0-tag-=-inst-tag
    (implies (and (inv MT MA)
		  (INST-in i MT)
		  (equal (INST-stg i) '(LSU RS0))
		  (MAETT-p MT) (MA-state-p MA))
	     (equal (LSU-RS-tag (LSU-RS0 (MA-LSU MA)))
		    (INST-tag i)))
  :hints (("goal" :in-theory (e/d (inst-inv-def equal-b1p-converter)
				  (INST-inv-if-INST-in))
		  :use (:instance INST-inv-if-INST-in))))

(defthm LSU-RS0-tag-=-inst-tag-2
    (implies (and (inv MT MA)
		  (uniq-inst-at-stg '(LSU RS0) MT)
		  (MAETT-p MT) (MA-state-p MA))
	     (equal (LSU-RS-tag (LSU-RS0 (MA-LSU MA)))
		    (INST-tag (INST-at-stg '(LSU RS0) MT))))
  :hints (("goal" :in-theory (e/d (inst-inv-def equal-b1p-converter)
				  (INST-inv-if-INST-in))
		  :use (:instance INST-inv-if-INST-in
				  (i (INST-at-stg '(LSU RS0) MT))))))

(defthm LSU-RS-tag-=-inst-tag
    (implies (and (inv MT MA)
		  (INST-in i MT)
		  (equal (INST-stg i) '(LSU RS1))
		  (MAETT-p MT) (MA-state-p MA))
	     (equal (LSU-RS-tag (LSU-RS1 (MA-LSU MA)))
		    (INST-tag i)))
  :hints (("goal" :in-theory (e/d (inst-inv-def equal-b1p-converter)
				  (INST-inv-if-INST-in))
		  :use (:instance INST-inv-if-INST-in))))

(defthm LSU-RS-tag-=-inst-tag-2
    (implies (and (inv MT MA)
		  (uniq-inst-at-stg '(LSU RS1) MT)
		  (MAETT-p MT) (MA-state-p MA))
	     (equal (LSU-RS-tag (LSU-RS1 (MA-LSU MA)))
		    (INST-tag (INST-at-stg '(LSU RS1) MT))))
  :hints (("goal" :in-theory (e/d (inst-inv-def equal-b1p-converter)
				  (INST-inv-if-INST-in))
		  :use (:instance INST-inv-if-INST-in
				  (i (INST-at-stg '(LSU RS1) MT))))))

(defthm LSU-RS0-val1-=-INST-src-val1
    (implies (and (inv MT MA)
		  (INST-in i MT)
		  (equal (INST-stg i) '(LSU RS0))
		  (b1p (LSU-RS-rdy1? (LSU-RS0 (MA-LSU MA))))
		  (not (b1p (inst-specultv? i)))
		  (not (b1p (INST-modified? i)))
		  (MAETT-p MT) (MA-state-p MA))
	     (equal (LSU-RS-val1 (LSU-RS0 (MA-LSU MA))) (INST-src-val1 i)))
  :hints (("goal" :in-theory (e/d (inst-inv-def equal-b1p-converter)
				  (INST-inv-if-INST-in))
		  :use (:instance INST-inv-if-INST-in))))

(defthm LSU-RS0-val1-=-INST-src-val1-2
    (implies (and (inv MT MA)
		  (uniq-inst-at-stg '(LSU RS0) MT)
		  (b1p (LSU-RS-rdy1? (LSU-RS0 (MA-LSU MA))))
		  (not (b1p (inst-specultv?
			     (INST-at-stg '(LSU RS0) MT))))
		  (not (b1p (INST-modified?
			     (INST-at-stg '(LSU RS0) MT))))
		  (MAETT-p MT) (MA-state-p MA))
	     (equal (LSU-RS-val1 (LSU-RS0 (MA-LSU MA)))
		    (INST-src-val1 (INST-at-stg '(LSU RS0) MT))))
  :hints (("goal" :in-theory (e/d (inst-inv-def equal-b1p-converter)
				  (INST-inv-if-INST-in))
		  :use (:instance INST-inv-if-INST-in
				  (i (INST-at-stg '(LSU RS0) MT))))))

(defthm LSU-RS1-val1-=-INST-src-val1
    (implies (and (inv MT MA)
		  (INST-in i MT)
		  (equal (INST-stg i) '(LSU RS1))
		  (b1p (LSU-RS-rdy1? (LSU-RS1 (MA-LSU MA))))
		  (not (b1p (inst-specultv? i)))
		  (not (b1p (INST-modified? i)))
		  (MAETT-p MT) (MA-state-p MA))
	     (equal (LSU-RS-val1 (LSU-RS1 (MA-LSU MA))) (INST-src-val1 i)))
  :hints (("goal" :in-theory (e/d (inst-inv-def equal-b1p-converter)
				  (INST-inv-if-INST-in))
		  :use (:instance INST-inv-if-INST-in))))

(defthm LSU-RS1-val1-=-INST-src-val1-2
    (implies (and (inv MT MA)
		  (uniq-inst-at-stg '(LSU RS1) MT)
		  (b1p (LSU-RS-rdy1? (LSU-RS1 (MA-LSU MA))))
		  (not (b1p (inst-specultv?
			     (INST-at-stg '(LSU RS1) MT))))
		  (not (b1p (INST-modified?
			     (INST-at-stg '(LSU RS1) MT))))
		  (MAETT-p MT) (MA-state-p MA))
	     (equal (LSU-RS-val1 (LSU-RS1 (MA-LSU MA)))
		    (INST-src-val1 (INST-at-stg '(LSU RS1) MT))))
  :hints (("goal" :in-theory (e/d (inst-inv-def equal-b1p-converter)
				  (INST-inv-if-INST-in))
		  :use (:instance INST-inv-if-INST-in
				  (i (INST-at-stg '(LSU RS1) MT))))))

(defthm LSU-RS0-val2-=-INST-src-val2
    (implies (and (inv MT MA)
		  (INST-in i MT)
		  (equal (INST-stg i) '(LSU RS0))
		  (b1p (LSU-RS-rdy2? (LSU-RS0 (MA-LSU MA))))
		  (not (b1p (inst-specultv? i)))
		  (not (b1p (INST-modified? i)))
		  (MAETT-p MT) (MA-state-p MA))
	     (equal (LSU-RS-val2 (LSU-RS0 (MA-LSU MA))) (INST-src-val2 i)))
  :hints (("goal" :in-theory (e/d (inst-inv-def equal-b1p-converter)
				  (INST-inv-if-INST-in))
		  :use (:instance INST-inv-if-INST-in))))

(defthm LSU-RS0-val2-=-INST-src-val2-2
    (implies (and (inv MT MA)
		  (uniq-inst-at-stg '(LSU RS0) MT)
		  (b1p (LSU-RS-rdy2? (LSU-RS0 (MA-LSU MA))))
		  (not (b1p (inst-specultv?
			     (INST-at-stg '(LSU RS0) MT))))
		  (not (b1p (INST-modified?
			     (INST-at-stg '(LSU RS0) MT))))
		  (MAETT-p MT) (MA-state-p MA))
	     (equal (LSU-RS-val2 (LSU-RS0 (MA-LSU MA)))
		    (INST-src-val2 (INST-at-stg '(LSU RS0) MT))))
  :hints (("goal" :in-theory (e/d (inst-inv-def equal-b1p-converter)
				  (INST-inv-if-INST-in))
		  :use (:instance INST-inv-if-INST-in
				  (i (INST-at-stg '(LSU RS0) MT))))))

(defthm LSU-RS1-val2-=-INST-src-val2
    (implies (and (inv MT MA)
		  (INST-in i MT)
		  (equal (INST-stg i) '(LSU RS1))
		  (b1p (LSU-RS-rdy2? (LSU-RS1 (MA-LSU MA))))
		  (not (b1p (inst-specultv? i)))
		  (not (b1p (INST-modified? i)))
		  (MAETT-p MT) (MA-state-p MA))
	     (equal (LSU-RS-val2 (LSU-RS1 (MA-LSU MA))) (INST-src-val2 i)))
  :hints (("goal" :in-theory (e/d (inst-inv-def equal-b1p-converter)
				  (INST-inv-if-INST-in))
		  :use (:instance INST-inv-if-INST-in))))

(defthm LSU-RS1-val2-=-INST-src-val2-2
    (implies (and (inv MT MA)
		  (uniq-inst-at-stg '(LSU RS1) MT)
		  (b1p (LSU-RS-rdy2? (LSU-RS1 (MA-LSU MA))))
		  (not (b1p (inst-specultv?
			     (INST-at-stg '(LSU RS1) MT))))
		  (not (b1p (INST-modified?
			     (INST-at-stg '(LSU RS1) MT))))
		  (MAETT-p MT) (MA-state-p MA))
	     (equal (LSU-RS-val2 (LSU-RS1 (MA-LSU MA)))
		    (INST-src-val2 (INST-at-stg '(LSU RS1) MT))))
  :hints (("goal" :in-theory (e/d (inst-inv-def equal-b1p-converter)
				  (INST-inv-if-INST-in))
		  :use (:instance INST-inv-if-INST-in
				  (i (INST-at-stg '(LSU RS1) MT))))))

(defthm LSU-RS0-val3-=-INST-src-val3
    (implies (and (inv MT MA)
		  (INST-in i MT)
		  (equal (INST-stg i) '(LSU RS0))
		  (b1p (LSU-RS-rdy3? (LSU-RS0 (MA-LSU MA))))
		  (not (b1p (inst-specultv? i)))
		  (not (b1p (INST-modified? i)))
		  (MAETT-p MT) (MA-state-p MA))
	     (equal (LSU-RS-val3 (LSU-RS0 (MA-LSU MA))) (INST-src-val3 i)))
  :hints (("goal" :in-theory (e/d (inst-inv-def equal-b1p-converter)
				  (INST-inv-if-INST-in))
		  :use (:instance INST-inv-if-INST-in))))

(defthm LSU-RS0-val3-=-INST-src-val3-2
    (implies (and (inv MT MA)
		  (uniq-inst-at-stg '(LSU RS0) MT)
		  (b1p (LSU-RS-rdy3? (LSU-RS0 (MA-LSU MA))))
		  (not (b1p (inst-specultv?
			     (INST-at-stg '(LSU RS0) MT))))
		  (not (b1p (INST-modified?
			     (INST-at-stg '(LSU RS0) MT))))
		  (MAETT-p MT) (MA-state-p MA))
	     (equal (LSU-RS-val3 (LSU-RS0 (MA-LSU MA)))
		    (INST-src-val3 (INST-at-stg '(LSU RS0) MT))))
  :hints (("goal" :in-theory (e/d (inst-inv-def equal-b1p-converter)
				  (INST-inv-if-INST-in))
		  :use (:instance INST-inv-if-INST-in
				  (i (INST-at-stg '(LSU RS0) MT))))))

(defthm LSU-RS1-val3-=-INST-src-val3
    (implies (and (inv MT MA)
		  (INST-in i MT)
		  (equal (INST-stg i) '(LSU RS1))
		  (b1p (LSU-RS-rdy3? (LSU-RS1 (MA-LSU MA))))
		  (not (b1p (inst-specultv? i)))
		  (not (b1p (INST-modified? i)))
		  (MAETT-p MT) (MA-state-p MA))
	     (equal (LSU-RS-val3 (LSU-RS1 (MA-LSU MA))) (INST-src-val3 i)))
  :hints (("goal" :in-theory (e/d (inst-inv-def equal-b1p-converter)
				  (INST-inv-if-INST-in))
		  :use (:instance INST-inv-if-INST-in))))

(defthm LSU-RS1-val3-=-INST-src-val3-2
    (implies (and (inv MT MA)
		  (uniq-inst-at-stg '(LSU RS1) MT)
		  (b1p (LSU-RS-rdy3? (LSU-RS1 (MA-LSU MA))))
		  (not (b1p (inst-specultv?
			     (INST-at-stg '(LSU RS1) MT))))
		  (not (b1p (INST-modified?
			     (INST-at-stg '(LSU RS1) MT))))
		  (MAETT-p MT) (MA-state-p MA))
	     (equal (LSU-RS-val3 (LSU-RS1 (MA-LSU MA)))
		    (INST-src-val3 (INST-at-stg '(LSU RS1) MT))))
  :hints (("goal" :in-theory (e/d (inst-inv-def equal-b1p-converter)
				  (INST-inv-if-INST-in))
		  :use (:instance INST-inv-if-INST-in
				  (i (INST-at-stg '(LSU RS1) MT))))))

(deflabel end-LSU-RS-field-lemmas)
(deftheory LSU-RS-field-inst-at-lemmas
    '(LSU-RS0-op-=-inst-LSU-op-2 LSU-RS1-op-=-inst-LSU-op-2
      LSU-RS0-ld-st-=-inst-ld-st-2 LSU-RS1-ld-st-=-inst-ld-st-2
      LSU-RS0-tag-=-inst-tag-2 LSU-RS-tag-=-inst-tag-2
      LSU-RS0-val1-=-INST-src-val1-2 LSU-RS1-val1-=-INST-src-val1-2
      LSU-RS0-val2-=-INST-src-val2-2 LSU-RS1-val2-=-INST-src-val2-2
      LSU-RS0-val3-=-INST-src-val3-2 LSU-RS1-val3-=-INST-src-val3-2))
(in-theory (disable LSU-RS-field-inst-at-lemmas))

(deflabel begin-LSU-wbuf-field-lemmas)
(defthm LSU-wbuf0-valid-if-INST-in
    (implies (and (inv MT MA)
		  (INST-in i MT)
		  (wbuf0-stg-p (INST-stg i))
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-p i))
	     (equal (wbuf-valid? (LSU-wbuf0 (MA-LSU MA))) 1))
  :hints (("goal" :in-theory (e/d (inst-inv-def equal-b1p-converter
						wbuf0-stg-p)
				  (INST-inv-if-INST-in))
		  :use (:instance INST-inv-if-INST-in))))

(defthm LSU-wbuf1-valid-if-INST-in
    (implies (and (inv MT MA)
		  (INST-in i MT)
		  (wbuf1-stg-p (INST-stg i))
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-p i))
	     (equal (wbuf-valid? (LSU-wbuf1 (MA-LSU MA))) 1))
  :hints (("goal" :in-theory (e/d (inst-inv-def equal-b1p-converter
						wbuf1-stg-p)
				  (INST-inv-if-INST-in))
		  :use (:instance INST-inv-if-INST-in))))

(defthm uniq-inst-at-LSU-wbuf0-if-valid
    (implies (and (inv MT MA)
		  (b1p (wbuf-valid? (LSU-wbuf0 (MA-LSU MA))))
		  (MA-state-p MA) (MAETT-p MT))
	     (uniq-INST-at-stgs '((LSU wbuf0) (LSU wbuf0 lch)
				  (complete wbuf0) (commit wbuf0))
				MT))
  :hints (("goal" :in-theory (enable inv no-stage-conflict
				     no-LSU-stg-conflict))))

(defthm uniq-inst-at-LSU-wbuf1-if-valid
    (implies (and (inv MT MA)
		  (b1p (wbuf-valid? (LSU-wbuf1 (MA-LSU MA))))
		  (MA-state-p MA) (MAETT-p MT))
	     (uniq-INST-at-stgs '((LSU wbuf1) (LSU wbuf1 lch)
				  (complete wbuf1) (commit wbuf1))
				MT))
  :hints (("goal" :in-theory (enable inv no-stage-conflict
				     no-LSU-stg-conflict))))

(defthm no-inst-at-LSU-wbuf0
    (implies (and (inv MT MA)
		  (not (b1p (wbuf-valid? (LSU-wbuf0 (MA-LSU MA)))))
		  (MA-state-p MA) (MAETT-p MT))
	     (no-INST-at-stgs '((LSU wbuf0) (LSU wbuf0 lch)
				(complete wbuf0) (commit wbuf0))
			      MT))
  :hints (("goal" :in-theory (enable inv no-stage-conflict
				     no-LSU-stg-conflict))))

(defthm no-inst-at-LSU-wbuf1
    (implies (and (inv MT MA)
		  (not (b1p (wbuf-valid? (LSU-wbuf1 (MA-LSU MA)))))
		  (MA-state-p MA) (MAETT-p MT))
	     (no-INST-at-stgs '((LSU wbuf1) (LSU wbuf1 lch)
				(complete wbuf1) (commit wbuf1))
			      MT))
  :hints (("goal" :in-theory (enable inv no-stage-conflict
				     no-LSU-stg-conflict))))
(encapsulate nil
(local
(defthm uniq-wbuf0-inst-help-help
    (implies (and (member-equal i trace)
		  (wbuf0-stg-p (INST-stg i)))
	     (not (no-inst-at-stgs-in-trace '((LSU wbuf0)
					      (LSU wbuf0 lch)
					      (complete wbuf0)
					      (commit wbuf0)) trace)))
  :hints (("goal" :in-theory (enable wbuf0-stg-p)))))

(local
(defthm uniq-wbuf0-inst-help
    (implies (and (uniq-inst-at-stgs-in-trace '((LSU wbuf0)
						(LSU wbuf0 lch)
						(complete wbuf0)
						(commit wbuf0)) trace)
		  (member-equal i trace)
		  (member-equal j trace)
		  (wbuf0-stg-p (INST-stg i)) (wbuf0-stg-p (INST-stg j)))
	     (equal i j))
  :hints (("Goal" :in-theory (enable wbuf0-stg-p)))
  :rule-classes nil))

(defthm uniq-wbuf0-inst
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i)
		  (INST-in j MT) (INST-p j)
		  (MAETT-p MT) (MA-state-p MA)
		  (wbuf0-stg-p (INST-stg i)) (wbuf0-stg-p (INST-stg j)))
	     (equal i j))
  :hints (("goal" :use ((:instance uniq-wbuf0-inst-help
				   (trace (MT-trace MT)))
			(:instance UNIQ-INST-AT-LSU-WBUF0-IF-VALID))
		  :in-theory (enable uniq-inst-at-stgs INST-in)
		  :restrict ((LSU-WBUF0-VALID-IF-INST-IN ((i i))))))
  :rule-classes nil)
)

(encapsulate nil
(local
(defthm uniq-wbuf1-inst-help-help
    (implies (and (member-equal i trace)
		  (wbuf1-stg-p (INST-stg i)))
	     (not (no-inst-at-stgs-in-trace '((LSU wbuf1)
					      (LSU wbuf1 lch)
					      (complete wbuf1)
					      (commit wbuf1)) trace)))
  :hints (("goal" :in-theory (enable wbuf1-stg-p)))))

(local
(defthm uniq-wbuf1-inst-help
    (implies (and (uniq-inst-at-stgs-in-trace '((LSU wbuf1)
						(LSU wbuf1 lch)
						(complete wbuf1)
						(commit wbuf1)) trace)
		  (member-equal i trace)
		  (member-equal j trace)
		  (wbuf1-stg-p (INST-stg i)) (wbuf1-stg-p (INST-stg j)))
	     (equal i j))
  :hints (("Goal" :in-theory (enable wbuf1-stg-p)))
  :rule-classes nil))

(defthm uniq-wbuf1-inst
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i)
		  (INST-in j MT) (INST-p j)
		  (wbuf1-stg-p (INST-stg i)) (wbuf1-stg-p (INST-stg j))
		  (MAETT-p MT) (MA-state-p MA))
	     (equal i j))
  :hints (("goal" :use ((:instance uniq-wbuf1-inst-help
				   (trace (MT-trace MT)))
			(:instance UNIQ-INST-AT-LSU-WBUF1-IF-VALID))
		  :in-theory (enable uniq-inst-at-stgs INST-in)
		  :restrict ((LSU-WBUF1-VALID-IF-INST-IN ((i i))))))
  :rule-classes nil)
)

(defthm LSU-wbuf0-complete-if-INST-in
    (implies (and (inv MT MA)
		  (INST-in i MT)
		  (equal (INST-stg i) '(LSU wbuf0))
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-p i))
	     (equal (wbuf-complete? (LSU-wbuf0 (MA-LSU MA))) 0))
  :hints (("goal" :in-theory (e/d (inst-inv-def equal-b1p-converter)
				  (INST-inv-if-INST-in))
		  :use (:instance INST-inv-if-INST-in))))

(defthm LSU-wbuf1-complete-if-INST-in
    (implies (and (inv MT MA)
		  (INST-in i MT)
		  (equal (INST-stg i) '(LSU wbuf1))
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-p i))
	     (equal (wbuf-complete? (LSU-wbuf1 (MA-LSU MA))) 0))
  :hints (("goal" :in-theory (e/d (inst-inv-def equal-b1p-converter)
				  (INST-inv-if-INST-in))
		  :use (:instance INST-inv-if-INST-in))))

(defthm LSU-wbuf0-commit-if-INST-in
    (implies (and (inv MT MA)
		  (INST-in i MT)
		  (or (equal (INST-stg i) '(LSU wbuf0))
		      (equal (INST-stg i) '(LSU wbuf0 lch))
		      (equal (INST-stg i) '(complete wbuf0)))
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-p i))
	     (equal (wbuf-commit? (LSU-wbuf0 (MA-LSU MA))) 0))
  :hints (("goal" :in-theory (e/d (inst-inv-def equal-b1p-converter)
				  (INST-inv-if-INST-in))
		  :use (:instance INST-inv-if-INST-in))))

(defthm LSU-wbuf1-commit-if-INST-in
    (implies (and (inv MT MA)
		  (INST-in i MT)
		  (or (equal (INST-stg i) '(LSU wbuf1))
		      (equal (INST-stg i) '(LSU wbuf1 lch))
		      (equal (INST-stg i) '(complete wbuf1)))
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-p i))
	     (equal (wbuf-commit? (LSU-wbuf1 (MA-LSU MA))) 0))
  :hints (("goal" :in-theory (e/d (inst-inv-def equal-b1p-converter)
				  (INST-inv-if-INST-in))
		  :use (:instance INST-inv-if-INST-in))))

(defthm LSU-wbuf1-complete-if-inst-at-LSU-wbuf0
    (implies (and (inv MT MA)
		  (uniq-INST-at-stg '(LSU wbuf0) MT)
		  (MAETT-p MT) (MA-state-p MA))
	     (equal (wbuf-commit? (LSU-wbuf0 (MA-LSU MA))) 0))
  :hints (("goal" :restrict
		  ((LSU-wbuf0-commit-if-INST-in
		    ((i (INST-at-stg '(LSU wbuf0) MT))))))))

(defthm LSU-wbuf1-complete-if-inst-at-LSU-wbuf0-lch
    (implies (and (inv MT MA)
		  (uniq-INST-at-stg '(LSU wbuf0 lch) MT)
		  (MAETT-p MT) (MA-state-p MA))
	     (equal (wbuf-commit? (LSU-wbuf0 (MA-LSU MA))) 0))
  :hints (("goal" :restrict
		  ((LSU-wbuf0-commit-if-INST-in
		    ((i (INST-at-stg '(LSU wbuf0 lch) MT))))))))

(defthm LSU-wbuf1-complete-if-inst-at-complete-wbuf0
    (implies (and (inv MT MA)
		  (uniq-INST-at-stg '(complete wbuf0) MT)
		  (MAETT-p MT) (MA-state-p MA))
	     (equal (wbuf-commit? (LSU-wbuf0 (MA-LSU MA))) 0))
  :hints (("goal" :restrict
		  ((LSU-wbuf0-commit-if-INST-in
		    ((i (INST-at-stg '(complete wbuf0) MT))))))))

(defthm LSU-wbuf1-complete-if-inst-at-LSU-wbuf1
    (implies (and (inv MT MA)
		  (uniq-INST-at-stg '(LSU wbuf1) MT)
		  (MAETT-p MT) (MA-state-p MA))
	     (equal (wbuf-commit? (LSU-wbuf1 (MA-LSU MA))) 0))
  :hints (("goal" :restrict
		  ((LSU-wbuf1-commit-if-INST-in
		    ((i (INST-at-stg '(LSU wbuf1) MT))))))))

(defthm LSU-wbuf1-complete-if-inst-at-LSU-wbuf1-lch
    (implies (and (inv MT MA)
		  (uniq-INST-at-stg '(LSU wbuf1 lch) MT)
		  (MAETT-p MT) (MA-state-p MA))
	     (equal (wbuf-commit? (LSU-wbuf1 (MA-LSU MA))) 0))
  :hints (("goal" :restrict
		  ((LSU-wbuf1-commit-if-INST-in
		    ((i (INST-at-stg '(LSU wbuf1 lch) MT))))))))

(defthm LSU-wbuf1-complete-if-inst-at-complete-wbuf1
    (implies (and (inv MT MA)
		  (uniq-INST-at-stg '(complete wbuf1) MT)
		  (MAETT-p MT) (MA-state-p MA))
	     (equal (wbuf-commit? (LSU-wbuf1 (MA-LSU MA))) 0))
  :hints (("goal" :restrict
		  ((LSU-wbuf1-commit-if-INST-in
		    ((i (INST-at-stg '(complete wbuf1) MT))))))))
		      

(defthm LSU-wbuf0-=-inst-tag
    (implies (and (inv MT MA)
		  (INST-in i MT)
		  (or (equal (INST-stg i) '(LSU wbuf0))
		      (equal (INST-stg i) '(LSU wbuf0 lch))
		      (equal (INST-stg i) '(complete wbuf0)))
		  (MAETT-p MT) (MA-state-p MA))
	     (equal (wbuf-tag (LSU-wbuf0 (MA-LSU MA)))
		    (INST-tag i)))
  :hints (("goal" :in-theory (e/d (inst-inv-def equal-b1p-converter)
				  (INST-inv-if-INST-in))
		  :use (:instance INST-inv-if-INST-in))))

(defthm LSU-wbuf1-=-inst-tag
    (implies (and (inv MT MA)
		  (INST-in i MT)
		  (or (equal (INST-stg i) '(LSU wbuf1))
		      (equal (INST-stg i) '(LSU wbuf1 lch))
		      (equal (INST-stg i) '(complete wbuf1)))
		  (MAETT-p MT) (MA-state-p MA))
	     (equal (wbuf-tag (LSU-wbuf1 (MA-LSU MA)))
		    (INST-tag i)))
  :hints (("goal" :in-theory (e/d (inst-inv-def equal-b1p-converter)
				  (INST-inv-if-INST-in))
		  :use (:instance INST-inv-if-INST-in))))

(defthm not-INST-excpt-detected-p-if-LSU-wbuf0
    (implies (and (inv MT MA)
		  (equal (INST-stg i) '(LSU wbuf0))
		  (not (b1p (inst-specultv? i)))
		  (not (b1p (INST-modified? i)))
		  (INST-in i MT)
		  (MAETT-p MT) (MA-state-p MA))
	     (not (INST-excpt-detected-p i)))
  :hints (("goal" :in-theory (e/d (inst-inv-def equal-b1p-converter)
				  (INST-inv-if-INST-in))
		  :use (:instance INST-inv-if-INST-in))))

(defthm not-INST-excpt-detected-p-if-LSU-wbuf1
    (implies (and (inv MT MA)
		  (equal (INST-stg i) '(LSU wbuf1))
		  (not (b1p (inst-specultv? i)))
		  (not (b1p (INST-modified? i)))
		  (INST-in i MT)
		  (MAETT-p MT) (MA-state-p MA))
	     (not (INST-excpt-detected-p i)))
  :hints (("goal" :in-theory (e/d (inst-inv-def equal-b1p-converter)
				  (INST-inv-if-INST-in))
		  :use (:instance INST-inv-if-INST-in))))

(defthm LSU-wbuf0-addr-=-INST-store-addr
    (implies (and (inv MT MA)
		  (INST-in i MT)
		  (wbuf0-stg-p (INST-stg i))
		  (not (b1p (inst-specultv? i)))
		  (not (b1p (INST-modified? i)))
		  (MAETT-p MT) (MA-state-p MA))
	     (equal (wbuf-addr (LSU-wbuf0 (MA-LSU MA)))
		    (INST-store-addr i)))
  :hints (("goal" :in-theory (e/d (inst-inv-def equal-b1p-converter
						wbuf0-stg-p)
				  (INST-inv-if-INST-in))
		  :use (:instance INST-inv-if-INST-in))))

(defthm LSU-wbuf1-addr-=-INST-store-addr
    (implies (and (inv MT MA)
		  (INST-in i MT)
		  (wbuf1-stg-p (INST-stg i))
		  (not (b1p (inst-specultv? i)))
		  (not (b1p (INST-modified? i)))
		  (MAETT-p MT) (MA-state-p MA))
	     (equal (wbuf-addr (LSU-wbuf1 (MA-LSU MA)))
		    (INST-store-addr i)))
  :hints (("goal" :in-theory (e/d (inst-inv-def equal-b1p-converter
						wbuf1-stg-p)
				  (INST-inv-if-INST-in))
		  :use (:instance INST-inv-if-INST-in))))

(defthm LSU-wbuf0-addr-=-INST-store-addr-2
    (let ((i (INST-at-stgs '((LSU wbuf0) (LSU wbuf0 lch)
			     (complete wbuf0) (commit wbuf0))
			   MT)))
      (implies (and (inv MT MA)
		    (uniq-inst-at-stgs  '((LSU wbuf0)
					  (LSU wbuf0 lch)
					  (complete wbuf0)
					  (commit wbuf0)) MT)
		    (not (b1p (inst-specultv? i)))
		    (not (b1p (INST-modified? i)))
		    (MAETT-p MT) (MA-state-p MA))
	       (equal (wbuf-addr (LSU-wbuf0 (MA-LSU MA)))
		      (INST-store-addr i))))
  :hints (("goal" :in-theory (e/d (inst-inv-def equal-b1p-converter)
				  (INST-inv-if-INST-in))
		  :use ((:instance INST-inv-if-INST-in
				   (i (INST-at-stgs '((LSU wbuf0)
						      (LSU wbuf0 lch)
						      (complete wbuf0)
						      (commit wbuf0))
						    MT)))
			(:instance INST-is-at-one-of-the-stages
				   (i (INST-at-stgs '((LSU wbuf0)
						      (LSU wbuf0 lch)
						      (complete wbuf0)
						      (commit wbuf0))
						    MT)))))))

(defthm LSU-wbuf1-addr-=-INST-store-addr-2
    (let ((i (INST-at-stgs '((LSU wbuf1) (LSU wbuf1 lch)
			     (complete wbuf1) (commit wbuf1))
			   MT)))
      (implies (and (inv MT MA)
		    (uniq-inst-at-stgs  '((LSU wbuf1)
					  (LSU wbuf1 lch)
					  (complete wbuf1)
					  (commit wbuf1)) MT)
		    (not (b1p (inst-specultv? i)))
		    (not (b1p (INST-modified? i)))
		    (MAETT-p MT) (MA-state-p MA))
	       (equal (wbuf-addr (LSU-wbuf1 (MA-LSU MA)))
		      (INST-store-addr i))))
  :hints (("goal" :in-theory (e/d (inst-inv-def equal-b1p-converter)
				  (INST-inv-if-INST-in))
		  :use ((:instance INST-inv-if-INST-in
				   (i (INST-at-stgs '((LSU wbuf1)
						      (LSU wbuf1 lch)
						      (complete wbuf1)
						      (commit wbuf1))
						    MT)))
			(:instance INST-is-at-one-of-the-stages
				   (i (INST-at-stgs '((LSU wbuf1)
						      (LSU wbuf1 lch)
						      (complete wbuf1)
						      (commit wbuf1))
						    MT)))))))

(defthm LSU-wbuf0-val-=-INST-src-val3
    (implies (and (inv MT MA)
		  (INST-in i MT)
		  (wbuf0-stg-p (INST-stg i))
		  (not (b1p (inst-specultv? i)))
		  (not (b1p (INST-modified? i)))
		  (MAETT-p MT) (MA-state-p MA))
	     (equal (wbuf-val (LSU-wbuf0 (MA-LSU MA)))
		    (INST-src-val3 i)))
  :hints (("goal" :in-theory (e/d (inst-inv-def equal-b1p-converter
						wbuf0-stg-p)
				  (INST-inv-if-INST-in))
		  :use (:instance INST-inv-if-INST-in))))

(defthm LSU-wbuf1-val-=-INST-src-val3
    (implies (and (inv MT MA)
		  (INST-in i MT)		  
		  (wbuf1-stg-p (INST-stg i))
		  (not (b1p (inst-specultv? i)))
		  (not (b1p (INST-modified? i)))
		  (MAETT-p MT) (MA-state-p MA))
	     (equal (wbuf-val (LSU-wbuf1 (MA-LSU MA)))
		    (INST-src-val3 i)))
  :hints (("goal" :in-theory (e/d (inst-inv-def equal-b1p-converter
						wbuf1-stg-p)
				  (INST-inv-if-INST-in))
		  :use (:instance INST-inv-if-INST-in))))

(defthm LSU-wbuf0-val-=-INST-src-val3-2
    (let ((i (INST-at-stgs '((LSU wbuf0) (LSU wbuf0 lch)
			     (complete wbuf0) (commit wbuf0))
			   MT)))
      (implies (and (inv MT MA)
		    (uniq-inst-at-stgs  '((LSU wbuf0)
					  (LSU wbuf0 lch)
					  (complete wbuf0)
					  (commit wbuf0)) MT)
		    (not (b1p (inst-specultv? i)))
		    (not (b1p (INST-modified? i)))
		    (MAETT-p MT) (MA-state-p MA))
	       (equal (wbuf-val (LSU-wbuf0 (MA-LSU MA)))
		      (INST-src-val3 i))))
  :hints (("goal" :in-theory (e/d (inst-inv-def equal-b1p-converter)
				  (INST-inv-if-INST-in))
		  :use ((:instance INST-inv-if-INST-in
				   (i (INST-at-stgs '((LSU wbuf0)
						      (LSU wbuf0 lch)
						      (complete wbuf0)
						      (commit wbuf0))
						    MT)))
			(:instance INST-is-at-one-of-the-stages
				   (i (INST-at-stgs '((LSU wbuf0)
						      (LSU wbuf0 lch)
						      (complete wbuf0)
						      (commit wbuf0))
						    MT)))))))

(defthm LSU-wbuf1-val-=-INST-src-val3-2
    (let ((i (INST-at-stgs '((LSU wbuf1) (LSU wbuf1 lch)
			     (complete wbuf1) (commit wbuf1))
			   MT)))
      (implies (and (inv MT MA)
		    (uniq-inst-at-stgs  '((LSU wbuf1)
					  (LSU wbuf1 lch)
					  (complete wbuf1)
					  (commit wbuf1)) MT)
		    (not (b1p (inst-specultv? i)))
		    (not (b1p (INST-modified? i)))
		    (MAETT-p MT) (MA-state-p MA))
	       (equal (wbuf-val (LSU-wbuf1 (MA-LSU MA)))
		      (INST-src-val3 i))))
  :hints (("goal" :in-theory (e/d (inst-inv-def equal-b1p-converter)
				  (INST-inv-if-INST-in))
		  :use ((:instance INST-inv-if-INST-in
				   (i (INST-at-stgs '((LSU wbuf1)
						      (LSU wbuf1 lch)
						      (complete wbuf1)
						      (commit wbuf1))
						    MT)))
			(:instance INST-is-at-one-of-the-stages
				   (i (INST-at-stgs '((LSU wbuf1)
						      (LSU wbuf1 lch)
						      (complete wbuf1)
						      (commit wbuf1))
						    MT)))))))

(deflabel end-LSU-wbuf-field-lemmas)
(deftheory LSU-wbuf-field-inst-at-lemmas
    '(LSU-wbuf0-addr-=-INST-store-addr-2 LSU-wbuf1-addr-=-INST-store-addr-2
      LSU-wbuf0-val-=-INST-src-val3-2 LSU-wbuf1-val-=-INST-src-val3-2))

(deflabel begin-LSU-rbuf-field-lemmas)
(defthm LSU-rbuf-valid-if-INST-in
    (implies (and (inv MT MA)
		  (INST-in i MT)
		  (equal (INST-stg i) '(LSU rbuf))
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-p i))
	     (equal (rbuf-valid? (LSU-rbuf (MA-LSU MA))) 1))
  :hints (("goal" :in-theory (e/d (inst-inv-def equal-b1p-converter)
				  (INST-inv-if-INST-in))
		  :use (:instance INST-inv-if-INST-in))))

(defthm uniq-inst-at-LSU-rbuf-if-valid
    (implies (and (inv MT MA)
		  (b1p (rbuf-valid? (LSU-rbuf (MA-LSU MA))))
		  (MA-state-p MA) (MAETT-p MT))
	     (uniq-INST-at-stg '(LSU rbuf) MT))
  :hints (("goal" :in-theory (enable inv no-stage-conflict
				     no-LSU-stg-conflict))))
(defthm no-inst-at-LSU-rbuf
    (implies (and (inv MT MA)
		  (not (b1p (rbuf-valid? (LSU-rbuf (MA-LSU MA)))))
		  (MA-state-p MA) (MAETT-p MT))
	     (no-INST-at-stg '(LSU rbuf) MT))
  :hints (("goal" :in-theory (enable inv no-stage-conflict
				     no-LSU-stg-conflict))))

(defthm LSU-rbuf-tag-=-inst-tag
    (implies (and (inv MT MA)
		  (INST-in i MT)
		  (equal (INST-stg i) '(LSU rbuf))
		  (MAETT-p MT) (MA-state-p MA))
	     (equal (rbuf-tag (LSU-rbuf (MA-LSU MA)))
		    (INST-tag i)))
  :hints (("goal" :in-theory (e/d (inst-inv-def equal-b1p-converter)
				  (INST-inv-if-INST-in))
		  :use (:instance INST-inv-if-INST-in))))

(defthm not-INST-excpt-detected-p-if-LSU-rbuf
    (implies (and (inv MT MA)
		  (equal (INST-stg i) '(LSU rbuf))
		  (not (b1p (inst-specultv? i)))
		  (not (b1p (INST-modified? i)))
		  (INST-in i MT)
		  (MAETT-p MT) (MA-state-p MA))
	     (not (INST-excpt-detected-p i)))
  :hints (("goal" :in-theory (e/d (inst-inv-def equal-b1p-converter)
				  (INST-inv-if-INST-in))
		  :use (:instance INST-inv-if-INST-in))))

(defthm LSU-rbuf-addr-=-INST-load-addr
    (implies (and (inv MT MA)
		  (equal (INST-stg i) '(LSU rbuf))
		  (not (b1p (inst-specultv? i)))
		  (not (b1p (INST-modified? i)))
		  (INST-in i MT)
		  (MAETT-p MT) (MA-state-p MA))
	     (equal (rbuf-addr (LSU-rbuf (MA-LSU MA)))
		    (INST-load-addr i)))
  :hints (("goal" :in-theory (e/d (inst-inv-def equal-b1p-converter)
				  (INST-inv-if-INST-in))
		  :use (:instance INST-inv-if-INST-in))))

(deflabel end-LSU-rbuf-field-lemmas)

(defthm LSU-lch-valid-if-INST-in
    (implies (and (inv MT MA)
		  (INST-in i MT)
		  (or (equal (INST-stg i) '(LSU lch))
		      (equal (INST-stg i) '(LSU wbuf0 lch))
		      (equal (INST-stg i) '(LSU wbuf1 lch)))
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-p i))
	     (equal (LSU-latch-valid? (LSU-lch (MA-LSU MA))) 1))
  :hints (("goal" :in-theory (e/d (inst-inv-def equal-b1p-converter)
				  (INST-inv-if-INST-in))
		  :use (:instance INST-inv-if-INST-in))))

(defthm uniq-inst-at-LSU-lch-if-valid
    (implies (and (inv MT MA)
		  (b1p (LSU-latch-valid? (LSU-lch (MA-LSU MA))))
		  (MA-state-p MA) (MAETT-p MT))
	     (uniq-INST-at-stgs '((LSU lch) (LSU wbuf0 lch)
				  (LSU wbuf1 lch))
				MT))
  :hints (("goal" :in-theory (enable inv no-stage-conflict
				     no-LSU-stg-conflict))))

(defthm no-inst-at-LSU-lch
    (implies (and (inv MT MA)
		  (not (b1p (LSU-latch-valid? (LSU-lch (MA-LSU MA)))))
		  (MA-state-p MA) (MAETT-p MT))
	     (no-INST-at-stgs '((LSU lch) (LSU wbuf0 lch)
				(LSU wbuf1 lch))
			      MT))
  :hints (("goal" :in-theory (enable inv no-stage-conflict
				     no-LSU-stg-conflict))))

(defthm LSU-lch-=-inst-tag
    (implies (and (inv MT MA)
		  (INST-in i MT)
		  (or (equal (INST-stg i) '(LSU lch))
		      (equal (INST-stg i) '(LSU wbuf0 lch))
		      (equal (INST-stg i) '(LSU wbuf1 lch)))
		  (MAETT-p MT) (MA-state-p MA))
	     (equal (LSU-latch-tag (LSU-lch (MA-LSU MA)))
		    (INST-tag i)))
  :hints (("goal" :in-theory (e/d (inst-inv-def equal-b1p-converter)
				  (INST-inv-if-INST-in))
		  :use (:instance INST-inv-if-INST-in))))

(defthm LSU-lch-=-inst-tag-2
    (implies (and (inv MT MA)
		  (uniq-inst-at-stgs '((LSU lch) (LSU wbuf0 lch)
				       (LSU wbuf1 lch))
				     MT)
		  (MAETT-p MT) (MA-state-p MA))
	     (equal (LSU-latch-tag (LSU-lch (MA-LSU MA)))
		    (INST-tag (INST-at-stgs '((LSU lch)
					      (LSU wbuf0 lch)
					      (LSU wbuf1 lch)) MT))))
  :hints (("goal" :in-theory (e/d (inst-inv-def equal-b1p-converter)
				  (INST-inv-if-INST-in))
		  :use (:instance INST-inv-if-INST-in
				  (i (INST-at-stgs '((LSU lch)
						     (LSU wbuf0 lch)
						     (LSU wbuf1 lch))
						   MT))))))

(defthm LSU-load-if-at-LSU-rbuf-lch
    (implies (and (inv MT MA)
		  (INST-in i MT)
		  (or (equal (INST-stg i) '(LSU rbuf))
		      (equal (INST-stg i) '(LSU lch)))
		  (not (b1p (inst-specultv? i)))
		  (not (b1p (INST-modified? i)))
		  (MAETT-p MT) (MA-state-p MA))
	     (equal (INST-load? i) 1))
  :hints (("goal" :in-theory (e/d (inst-inv-def equal-b1p-converter)
				  (INST-inv-if-INST-in))
		  :use (:instance INST-inv-if-INST-in))))
(in-theory (disable LSU-load-if-at-LSU-rbuf-lch))

(defthm LSU-load-INST-at-LSU-lch-2
    (implies (and (inv MT MA)
		  (uniq-INST-at-stg '(LSU lch) MT)
		  (not (b1p (inst-specultv?
			     (INST-at-stg '(LSU lch) MT))))
		  (not (b1p (INST-modified?
			     (INST-at-stg '(LSU lch) MT))))
		  (MAETT-p MT) (MA-state-p MA))
	     (equal (INST-load? (INST-at-stg '(LSU lch) MT)) 1))
  :hints (("goal" :in-theory (e/d (inst-inv-def equal-b1p-converter)
				  (INST-inv-if-INST-in))
		  :use (:instance INST-inv-if-INST-in
				  (i (INST-at-stg '(LSU lch) MT))))))

(defthm LSU-store-if-at-LSU-wbuf
    (implies (and (inv MT MA)
		  (INST-in i MT)
		  (or (equal (INST-stg i) '(LSU wbuf0))
		      (equal (INST-stg i) '(LSU wbuf1))
		      (equal (INST-stg i) '(LSU wbuf0 lch))
		      (equal (INST-stg i) '(LSU wbuf1 lch))
		      (equal (INST-stg i) '(complete wbuf0))
		      (equal (INST-stg i) '(complete wbuf1))
		      (equal (INST-stg i) '(commit wbuf0))
		      (equal (INST-stg i) '(commit wbuf1)))
		  (not (b1p (inst-specultv? i)))
		  (not (b1p (INST-modified? i)))
		  (MAETT-p MT) (MA-state-p MA))
	     (equal (INST-store? i) 1))
  :hints (("goal" :in-theory (e/d (inst-inv-def equal-b1p-converter)
				  (INST-inv-if-INST-in))
		  :use (:instance INST-inv-if-INST-in))))
(in-theory (disable LSU-store-if-at-LSU-wbuf))

(defthm LSU-lch-excpt-=-INST-excpt-flags
    (implies (and (inv MT MA)
		  (INST-in i MT)
		  (or (equal (INST-stg i) '(LSU lch))
		      (equal (INST-stg i) '(LSU wbuf0 lch))
		      (equal (INST-stg i) '(LSU wbuf1 lch)))
		  (not (b1p (inst-specultv? i)))
		  (not (b1p (INST-modified? i)))
		  (MAETT-p MT) (MA-state-p MA))
	     (equal (LSU-latch-excpt (LSU-lch (MA-LSU MA)))
		    (INST-excpt-flags i)))
  :hints (("goal" :in-theory (e/d (inst-inv-def equal-b1p-converter)
				  (INST-inv-if-INST-in))
		  :use (:instance INST-inv-if-INST-in))))

(defthm LSU-lch-excpt-=-INST-excpt-flags-2
    (let ((i (INST-at-stgs '((LSU lch)
			     (LSU wbuf0 lch)
			     (LSU wbuf1 lch)) MT)))
      (implies (and (inv MT MA)
		    (uniq-inst-at-stgs '((LSU lch)
					 (LSU wbuf0 lch)
					 (LSU wbuf1 lch))
				       MT)
		    (not (b1p (inst-specultv? i)))
		    (not (b1p (INST-modified? i)))
		    (MAETT-p MT) (MA-state-p MA))
	       (equal (LSU-latch-tag (LSU-lch (MA-LSU MA)))
		      (INST-tag i))))
  :hints (("goal" :in-theory (e/d (inst-inv-def equal-b1p-converter)
				  (INST-inv-if-INST-in))
		  :use (:instance INST-inv-if-INST-in
				  (i (INST-at-stgs '((LSU lch)
						     (LSU wbuf0 lch)
						     (LSU wbuf1 lch))
						   MT))))))

(defthm LSU-latch-val-=-INST-dest-val
    (implies (and (inv MT MA)
		  (INST-in i MT)
		  (equal (INST-stg i) '(LSU lch))
		  (not (b1p (inst-specultv? i)))
		  (not (b1p (INST-modified? i)))
		  (not (INST-load-accs-error-detected-p i))
		  (MAETT-p MT) (MA-state-p MA))
	     (equal (LSU-latch-val (LSU-lch (MA-LSU MA)))
		    (INST-dest-val i)))
  :hints (("goal" :in-theory (e/d (inst-inv-def equal-b1p-converter)
				  (INST-inv-if-INST-in))
		  :use (:instance INST-inv-if-INST-in))))

(defthm LSU-latch-val-=-INST-dest-val-2
    (implies (and (inv MT MA)
		  (uniq-inst-at-stg '(LSU lch) MT)
		  (not (b1p (inst-specultv?
			     (INST-at-stg '(LSU lch) MT))))
		  (not (b1p (INST-modified?
			     (INST-at-stg '(LSU lch) MT))))
		  (not (INST-load-accs-error-detected-p
			(INST-at-stg '(LSU lch) MT)))
		  (MAETT-p MT) (MA-state-p MA))
	     (equal (LSU-latch-val (LSU-lch (MA-LSU MA)))
		    (INST-dest-val (INST-at-stg '(LSU lch) MT))))
  :hints (("goal" :in-theory (e/d (inst-inv-def equal-b1p-converter)
				  (INST-inv-if-INST-in))
		  :use (:instance INST-inv-if-INST-in
				  (i (INST-at-stg '(LSU lch) MT))))))

(deflabel end-LSU-field-lemmas)
(deftheory LSU-field-lemmas
    (set-difference-theories
     (universal-theory 'end-LSU-field-lemmas)
     (universal-theory 'begin-LSU-field-lemmas)))

(deftheory LSU-field-INST-at-lemmas
    '(LSU-lch-=-inst-tag-2 LSU-load-INST-at-LSU-lch-2
      LSU-lch-excpt-=-INST-excpt-flags-2
      LSU-latch-val-=-INST-dest-val-2))
(in-theory (disable LSU-field-INST-at-lemmas))

;;;;;;;;;;;;;;;;Order of LSU instructions ;;;;;;;;;;;;;;;;;
(defthm not-LSU-rbuf-wbuf0-if-not-wbuf-valid
    (implies (and (inv MT MA)
		  (b1p (rbuf-valid? (LSU-rbuf (MA-LSU MA))))
		  (b1p (rbuf-wbuf0? (LSU-rbuf (MA-LSU MA))))
		  (MAETT-p MT) (MA-state-p MA))
	     (b1p (wbuf-valid? (LSU-wbuf0 (MA-LSU MA)))))
  :rule-classes
  ((:rewrite)
   (:rewrite :corollary
	     (implies (and (inv MT MA)
			   (b1p (rbuf-valid? (LSU-rbuf (MA-LSU MA))))
			   (not (b1p (wbuf-valid? (LSU-wbuf0 (MA-LSU MA)))))
			   (MAETT-p MT) (MA-state-p MA))
		      (not (b1p (rbuf-wbuf0? (LSU-rbuf (MA-LSU MA))))))))
  :hints (("goal" :in-theory (enable inv consistent-MA-p
				     consistent-LSU-p))))

(defthm not-LSU-rbuf-wbuf1-if-not-wbuf-valid
    (implies (and (inv MT MA)
		  (b1p (rbuf-valid? (LSU-rbuf (MA-LSU MA))))
		  (b1p (rbuf-wbuf1? (LSU-rbuf (MA-LSU MA))))
		  (MAETT-p MT) (MA-state-p MA))
	     (b1p (wbuf-valid? (LSU-wbuf1 (MA-LSU MA)))))
  :rule-classes
  ((:rewrite)
   (:rewrite :corollary
	     (implies (and (inv MT MA)
			   (b1p (rbuf-valid? (LSU-rbuf (MA-LSU MA))))
			   (not (b1p (wbuf-valid? (LSU-wbuf1 (MA-LSU MA)))))
			   (MAETT-p MT) (MA-state-p MA))
		      (not (b1p (rbuf-wbuf1? (LSU-rbuf (MA-LSU MA))))))))
  :hints (("goal" :in-theory (enable inv consistent-MA-p
				     consistent-LSU-p))))

(defthm in-order-wbuf0-rbuf-p-MT-trace
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (b1p (rbuf-valid? (LSU-rbuf (MA-LSU MA))))
		  (b1p (wbuf-valid? (LSU-wbuf0 (MA-LSU MA))))
		  (b1p (rbuf-wbuf0? (LSU-rbuf (MA-LSU MA)))))
	     (in-order-wbuf0-rbuf-p (MT-trace MT)))
  :hints (("goal" :in-theory (enable inv in-order-LSU-inst-p
				     in-order-load-store-p))))

(defthm in-order-rbuf-wbuf0-p-MT-trace
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (b1p (rbuf-valid? (LSU-rbuf (MA-LSU MA))))
		  (b1p (wbuf-valid? (LSU-wbuf0 (MA-LSU MA))))
		  (not (b1p (rbuf-wbuf0? (LSU-rbuf (MA-LSU MA))))))
	     (in-order-rbuf-wbuf0-p (MT-trace MT)))
  :hints (("goal" :in-theory (enable inv in-order-LSU-inst-p
				     in-order-load-store-p))))

(defthm in-order-wbuf1-rbuf-p-MT-trace
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (b1p (rbuf-valid? (LSU-rbuf (MA-LSU MA))))
		  (b1p (wbuf-valid? (LSU-wbuf1 (MA-LSU MA))))
		  (b1p (rbuf-wbuf1? (LSU-rbuf (MA-LSU MA)))))
	     (in-order-wbuf1-rbuf-p (MT-trace MT)))
  :hints (("goal" :in-theory (enable inv in-order-LSU-inst-p
				     in-order-load-store-p))))

(defthm in-order-rbuf-wbuf1-p-MT-trace
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (b1p (rbuf-valid? (LSU-rbuf (MA-LSU MA))))
		  (b1p (wbuf-valid? (LSU-wbuf1 (MA-LSU MA))))
		  (not (b1p (rbuf-wbuf1? (LSU-rbuf (MA-LSU MA))))))
	     (in-order-rbuf-wbuf1-p (MT-trace MT)))
  :hints (("goal" :in-theory (enable inv in-order-LSU-inst-p
				     in-order-load-store-p))))

(encapsulate nil
(local
 (defthm INST-in-order-p-LSU-RS1-RS0-help-help
     (implies (and (member-equal i trace)
		   (equal (INST-stg i) '(LSU RS1)))
	      (not (no-inst-at-stg-in-trace '(LSU RS1) trace)))))

(local
(defthm INST-in-order-p-LSU-RS1-RS0-help
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (subtrace-p trace MT) (INST-listp trace)
		  (IN-order-LSU-RS-p trace MA)
		  (member-equal i trace)
		  (equal (INST-stg j) '(LSU RS0))
		  (member-equal j trace)
		  (equal (INST-stg i) '(LSU RS1))
		  (b1p (LSU-RS1-head? (MA-LSU MA))))
	     (member-in-order i j trace))
  :hints (("Goal" :in-theory (enable member-in-order*)))))

(defthm INST-in-order-p-LSU-RS1-RS0
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-in i MT) (INST-p i)
		  (equal (INST-stg j) '(LSU RS0))
		  (INST-in j MT) (INST-p j)
		  (equal (INST-stg i) '(LSU RS1))
		  (b1p (LSU-RS1-head? (MA-LSU MA))))
	     (INST-in-order-p i j MT))
  :hints (("Goal" :in-theory (enable inv IN-ORDER-LSU-INST-P
				     INST-in
				     INST-in-order-p
				     IN-ORDER-LSU-RS-P)
		  :restrict ((INST-in-order-p-LSU-RS1-RS0-help
			      ((MT MT) (MA MA)))))))
)

(encapsulate nil
(local
 (defthm INST-in-order-p-LSU-RS0-RS1-help-help
     (implies (and (member-equal i trace)
		   (equal (INST-stg i) '(LSU RS0)))
	      (not (no-inst-at-stg-in-trace '(LSU RS0) trace)))))

(local
(defthm INST-in-order-p-LSU-RS0-RS1-help
    (implies (and (inv MT MA)
		  (subtrace-p trace MT) (INST-listp trace)
		  (MAETT-p MT) (MA-state-p MA)
		  (IN-order-LSU-RS-p trace MA)
		  (member-equal i trace)
		  (equal (INST-stg i) '(LSU RS0))
		  (member-equal j trace)
		  (equal (INST-stg j) '(LSU RS1))
		  (not (b1p (LSU-RS1-head? (MA-LSU MA)))))
	     (member-in-order i j trace))
  :hints (("Goal" :in-theory (enable member-in-order*)))))

(defthm INST-in-order-p-LSU-RS0-RS1
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-in i MT) (INST-p i)
		  (equal (INST-stg i) '(LSU RS0))
		  (INST-in j MT) (INST-p j)
		  (equal (INST-stg j) '(LSU RS1))
		  (not (b1p (LSU-RS1-head? (MA-LSU MA)))))
	     (INST-in-order-p i j MT))
  :hints (("Goal" :in-theory (enable inv IN-ORDER-LSU-INST-P
				     IN-ORDER-LSU-RS-P
				     INST-in-order-p INST-in )
		  :restrict ((INST-in-order-p-LSU-RS0-RS1-help
			      ((MA MA) (MT MT)))))))
)

(in-theory (disable INST-in-order-p-LSU-RS1-RS0
		    INST-in-order-p-LSU-RS0-RS1))

(encapsulate nil
(local
 (defthm not-LSU-issued-stg-p-if-member-equal
     (implies (and (LSU-issued-stg-p (INST-stg i))
		   (no-issued-LSU-inst-p trace))
	      (not (member-equal i trace)))))

(local
(defthm INST-in-order-p-LSU-issued-RS-help
    (implies (and (in-order-LSU-issue-p trace)
		  (member-equal i trace)
		  (LSU-issued-stg-p (INST-stg i))
		  (member-equal j trace)
		  (or (equal (INST-stg j) '(LSU RS0))
		      (equal (INST-stg j) '(LSU RS1))))
	     (member-in-order i j trace))
  :hints (("goal" :in-theory (enable member-in-order*)))))

(defthm INST-in-order-p-LSU-issued-RS
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i)
		  (LSU-issued-stg-p (INST-stg i))
		  (INST-in j MT) (INST-p j)
		  (or (equal (INST-stg j) '(LSU RS0))
		      (equal (INST-stg j) '(LSU RS1))))
	     (inst-in-order-p i j MT))
  :hints (("goal" :in-theory (enable inst-in-order-p INST-in
				     inv in-order-LSU-inst-p))))
)
(in-theory (disable INST-in-order-p-LSU-issued-RS))

(encapsulate nil
(local
(defthm not-no-inst-at-stg-in-trace-if-member-equal
    (implies (and (member-equal i trace)
		  (equal (INST-stg i) stg))
	     (not (no-inst-at-stg-in-trace stg trace)))))

(local
(defthm not-no-inst-at-wbuf0-p-if-member-equal
    (implies (and (member-equal i trace)
		  (wbuf0-stg-p (INST-stg i)))
	     (not (no-inst-at-wbuf0-p trace)))))

(local
(defthm not-no-inst-at-wbuf1-p-if-member-equal
    (implies (and (member-equal i trace)
		  (wbuf1-stg-p (INST-stg i)))
	     (not (no-inst-at-wbuf1-p trace)))))

(local
(defthm INST-in-order-p-rbuf-wbuf0-help-help
    (implies (and (in-order-rbuf-wbuf0-p trace)
		  (member-equal i trace)
		  (equal (INST-stg i) '(LSU rbuf))
		  (member-equal j trace)
		  (wbuf0-stg-p (INST-stg j)))
	     (member-in-order i j trace))
  :hints (("goal" :in-theory (enable member-in-order*)))))

(local
(defthm INST-in-order-p-rbuf-wbuf0-help
    (implies (and (inv MT MA)
		  (in-order-rbuf-wbuf0-p (MT-trace MT))
		  (INST-in i MT) (INST-p i)
		  (equal (INST-stg i) '(LSU rbuf))
		  (INST-in j MT) (INST-p j)
		  (wbuf0-stg-p (INST-stg j))
		  (not (b1p (rbuf-wbuf0? (LSU-rbuf (MA-LSU MA)))))
		  (MAETT-p MT) (MA-state-p MA))
	     (INST-in-order-p i j MT))
  :hints (("goal" :in-theory (enable INST-in-order-p INST-in)))
  :rule-classes nil))

(defthm INST-in-order-p-rbuf-wbuf0
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i)
		  (equal (INST-stg i) '(LSU rbuf))
		  (INST-in j MT) (INST-p j)
		  (wbuf0-stg-p (INST-stg j))
		  (not (b1p (rbuf-wbuf0? (LSU-rbuf (MA-LSU MA)))))
		  (MAETT-p MT) (MA-state-p MA))
	     (INST-in-order-p i j MT))
  :hints (("goal" :use (:instance INST-in-order-p-rbuf-wbuf0-help)
		  :restrict ((LSU-RBUF-VALID-IF-INST-IN
			      ((i i)))))))

(local
(defthm INST-in-order-p-wbuf0-rbuf-help-help
    (implies (and (in-order-wbuf0-rbuf-p trace)
		  (member-equal i trace)
		  (equal (INST-stg i) '(LSU rbuf))
		  (member-equal j trace)
		  (wbuf0-stg-p (INST-stg j)))
	     (member-in-order j i trace))
  :hints (("goal" :in-theory (enable member-in-order*)))))

(local
(defthm INST-in-order-p-wbuf0-rbuf-help
    (implies (and (inv MT MA)
		  (in-order-wbuf0-rbuf-p (MT-trace MT))
		  (INST-in i MT) (INST-p i)
		  (equal (INST-stg i) '(LSU rbuf))
		  (INST-in j MT) (INST-p j)
		  (wbuf0-stg-p (INST-stg j))
		  (b1p (rbuf-wbuf0? (LSU-rbuf (MA-LSU MA))))
		  (MAETT-p MT) (MA-state-p MA))
	     (INST-in-order-p j i MT))
  :hints (("goal" :in-theory (enable INST-in-order-p INST-in)))
  :rule-classes nil))

(defthm INST-in-order-p-wbuf0-rbuf
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i)
		  (wbuf0-stg-p (INST-stg i))
		  (INST-in j MT) (INST-p j)
		  (equal (INST-stg j) '(LSU rbuf))
		  (b1p (rbuf-wbuf0? (LSU-rbuf (MA-LSU MA))))
		  (MAETT-p MT) (MA-state-p MA))
	     (INST-in-order-p i j MT))
  :hints (("goal" :use (:instance INST-in-order-p-wbuf0-rbuf-help
				  (i j) (j i))
		  :restrict ((LSU-RBUF-VALID-IF-INST-IN
			      ((i j)))))))
(local
(defthm INST-in-order-p-rbuf-wbuf1-help-help
    (implies (and (in-order-rbuf-wbuf1-p trace)
		  (member-equal i trace)
		  (equal (INST-stg i) '(LSU rbuf))
		  (member-equal j trace)
		  (wbuf1-stg-p (INST-stg j)))
	     (member-in-order i j trace))
  :hints (("goal" :in-theory (enable member-in-order*)))))

(local
(defthm INST-in-order-p-rbuf-wbuf1-help
    (implies (and (inv MT MA)
		  (in-order-rbuf-wbuf1-p (MT-trace MT))
		  (INST-in i MT) (INST-p i)
		  (equal (INST-stg i) '(LSU rbuf))
		  (INST-in j MT) (INST-p j)
		  (wbuf1-stg-p (INST-stg j))
		  (not (b1p (rbuf-wbuf1? (LSU-rbuf (MA-LSU MA)))))
		  (MAETT-p MT) (MA-state-p MA))
	     (INST-in-order-p i j MT))
  :hints (("goal" :in-theory (enable INST-in-order-p INST-in)))
  :rule-classes nil))

(defthm INST-in-order-p-rbuf-wbuf1
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i)
		  (equal (INST-stg i) '(LSU rbuf))
		  (INST-in j MT) (INST-p j)
		  (wbuf1-stg-p (INST-stg j))
		  (not (b1p (rbuf-wbuf1? (LSU-rbuf (MA-LSU MA)))))
		  (MAETT-p MT) (MA-state-p MA))
	     (INST-in-order-p i j MT))
  :hints (("goal" :use (:instance INST-in-order-p-rbuf-wbuf1-help)
		  :restrict ((LSU-RBUF-VALID-IF-INST-IN
			      ((i i)))))))

(local
(defthm INST-in-order-p-wbuf1-rbuf-help-help
    (implies (and (in-order-wbuf1-rbuf-p trace)
		  (member-equal i trace)
		  (equal (INST-stg i) '(LSU rbuf))
		  (member-equal j trace)
		  (wbuf1-stg-p (INST-stg j)))
	     (member-in-order j i trace))
  :hints (("goal" :in-theory (enable member-in-order*)))))

(local
(defthm INST-in-order-p-wbuf1-rbuf-help
    (implies (and (inv MT MA)
		  (in-order-wbuf1-rbuf-p (MT-trace MT))
		  (INST-in i MT) (INST-p i)
		  (equal (INST-stg i) '(LSU rbuf))
		  (INST-in j MT) (INST-p j)
		  (wbuf1-stg-p (INST-stg j))
		  (b1p (rbuf-wbuf1? (LSU-rbuf (MA-LSU MA))))
		  (MAETT-p MT) (MA-state-p MA))
	     (INST-in-order-p j i MT))
  :hints (("goal" :in-theory (enable INST-in-order-p INST-in)))
  :rule-classes nil))

(defthm INST-in-order-p-wbuf1-rbuf
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i)
		  (wbuf1-stg-p (INST-stg i))
		  (INST-in j MT) (INST-p j)
		  (equal (INST-stg j) '(LSU rbuf))
		  (b1p (rbuf-wbuf1? (LSU-rbuf (MA-LSU MA))))
		  (MAETT-p MT) (MA-state-p MA))
	     (INST-in-order-p i j MT))
  :hints (("goal" :use (:instance INST-in-order-p-wbuf1-rbuf-help
				  (i j) (j i))
		  :restrict ((LSU-RBUF-VALID-IF-INST-IN
			      ((i j)))))))
)

(in-theory (disable INST-in-order-p-wbuf0-rbuf
		    INST-in-order-p-rbuf-wbuf0
		    INST-in-order-p-wbuf1-rbuf
		    INST-in-order-p-rbuf-wbuf1))

(encapsulate nil
(local
 (defthm not-no-inst-at-wbuf0-if-member-equal
     (implies (and (member-equal i trace)
		   (wbuf0-stg-p (INST-stg i)))
	      (not (no-inst-at-wbuf0-p trace)))))

(local
(defthm INST-in-order-p-wbuf0-wbuf1-help
    (implies (and (distinct-member-p trace)
		  (in-order-wb-trace-p trace)
		  (member-equal i trace)
		  (wbuf0-stg-p (INST-stg i))
		  (member-equal j trace)
		  (wbuf1-stg-p (INST-stg j)))
	     (member-in-order i j trace))
  :hints (("goal" :in-theory (enable member-in-order*)))))

(defthm INST-in-order-p-wbuf0-wbuf1
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i)
		  (wbuf0-stg-p (INST-stg i))
		  (INST-in j MT) (INST-p j)
		  (wbuf1-stg-p (INST-stg j))
		  (MAETT-p MT) (MA-state-p MA))
	     (INST-in-order-p i j MT))
  :hints (("goal" :in-theory (enable INST-in-order-p INST-in inv
				     weak-inv MT-distinct-INST-p
				     in-order-LSU-inst-p))))
)
(in-theory (disable INST-in-order-p-wbuf0-wbuf1))

(encapsulate nil
(local
 (defthm not-no-retired-stored-p-if-member-equal
     (implies (and (member-equal i trace)
		   (retire-stg-p (INST-stg i))
		   (b1p (INST-store? i)))
	      (not (no-retired-store-p trace)))))

(local
(defthm INST-in-order-p-retire-wbuf0-help
    (implies (and (in-order-WB-retire-p trace)
		  (member-equal i trace)
		  (retire-stg-p (INST-stg i))
		  (b1p (INST-store? i))
		  (member-equal j trace)
		  (wbuf0-stg-p (INST-stg j)))
	     (member-in-order i j trace))
  :hints (("goal" :in-theory (enable member-in-order*)))))

(defthm INST-in-order-p-retire-wbuf0
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-in i MT) (INST-p i)
		  (retire-stg-p (INST-stg i))
		  (b1p (INST-store? i))
		  (INST-in j MT) (INST-p j)
		  (wbuf0-stg-p (INST-stg j)))
	     (INST-in-order-p i j MT))
  :hints (("goal" :in-theory (enable inv in-order-LSU-inst-p
				     INST-in INST-in-order-p))))
)
(in-theory (disable INST-in-order-p-retire-wbuf0))

(defthm INST-in-order-p-retire-wbuf1
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i)
		  (retire-stg-p (INST-stg i))
		  (b1p (INST-store? i))
		  (INST-in j MT) (INST-p j)
		  (wbuf1-stg-p (INST-stg j))
		  (MAETT-p MT) (MA-state-p MA))
	     (INST-in-order-p i j MT))
  :hints (("goal" :restrict (((:rewrite INST-IN-ORDER-TRANSITIVITY . 1)
			      ((j (inst-at-stgs '((LSU WBUF0)
						  (LSU WBUF0 LCH)
						  (COMPLETE WBUF0)
						  (COMMIT WBUF0)) MT)))))
		  :in-theory (enable inst-in-order-p-retire-wbuf0
				     inst-in-order-p-wbuf0-wbuf1))))
(in-theory (disable INST-in-order-p-retire-wbuf1))

(defthm INST-in-order-p-retired-store-non-retired
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i)
		  (retire-stg-p (INST-stg i))
		  (b1p (INST-store? i))		  
		  (INST-in j MT) (INST-p j)
		  (not (retire-stg-p (INST-stg j)))
		  (MAETT-p MT) (MA-state-p MA))
	     (INST-in-order-p i j MT))
  :hints (("goal" :use ((:instance INST-is-at-one-of-the-stages (i j)))
		  :in-theory (e/d (commit-stg-p
				   INST-in-order-p-retire-wbuf0
				   INST-in-order-p-retire-wbuf1)
				  (INST-is-at-one-of-the-stages)))))

(in-theory (disable INST-in-order-p-retired-store-non-retired))

(encapsulate nil
(local
 (defthm no-retired-store-p-cdr-help
     (implies (and (in-order-wb-retire-p trace)
		   (tail-p sub trace)
		   (consp sub)
		   (equal (INST-stg (car sub)) '(commit wbuf0)))
	      (no-retired-store-p (cdr sub)))))

(defthm no-retired-store-p-cdr
    (implies (and (inv MT MA)
		  (subtrace-p trace MT)
		  (consp trace)
		  (equal (INST-stg (car trace)) '(commit wbuf0)))
	     (no-retired-store-p (cdr trace)))
  :hints (("goal" :in-theory (enable inv IN-ORDER-LSU-INST-P
				     subtrace-p))))
)

(defthm retire-stg-p-car-if-member-inst-at-commit-wbuf0
    (implies (and (inv MT MA)
		  (member-equal i (cdr trace))
		  (INST-in i MT) (INST-p i)
		  (subtrace-p trace MT)
		  (INST-listp trace)
		  (equal (INST-stg i) '(commit wbuf0))
		  (MAETT-p MT) (MA-state-p MA))
	     (retire-stg-p (INST-stg (car trace))))
  :hints (("goal" :use ((:instance inst-is-at-one-of-the-stages
				   (i (car trace)))
			(:instance INST-IN-ORDER-P-WBUF0-WBUF1
				   (i i) (j (car trace)))
			(:instance INST-at-stg-inst-stg-commit (i i))
			(:instance INST-at-stg-inst-stg-commit
				   (i (car trace))))
		  :in-theory (enable commit-stg-p)
		  :do-not-induct t)))
;;; End of the theory of LSU instructions 

;;;;;;;;;;;;;;;;;;complete field lemmas;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(defthm LSU-wbuf0-complete-if-complete-INST-in
    (implies (and (inv MT MA)
		  (INST-in i MT)
		  (or (equal (INST-stg i) '(LSU wbuf0 lch))
		      (equal (INST-stg i) '(complete wbuf0))
		      (equal (INST-stg i) '(commit wbuf0)))
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-p i))
	     (equal (wbuf-complete? (LSU-wbuf0 (MA-LSU MA))) 1))
  :hints (("goal" :in-theory (e/d (inst-inv-def equal-b1p-converter)
				  (INST-inv-if-INST-in))
		  :use (:instance INST-inv-if-INST-in))))

(defthm LSU-wbuf1-complete-if-complete-INST-in
    (implies (and (inv MT MA)
		  (INST-in i MT)
		  (or (equal (INST-stg i) '(LSU wbuf1 lch))
		      (equal (INST-stg i) '(complete wbuf1))
		      (equal (INST-stg i) '(commit wbuf1)))
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-p i))
	     (equal (wbuf-complete? (LSU-wbuf1 (MA-LSU MA))) 1))
  :hints (("goal" :in-theory (e/d (inst-inv-def equal-b1p-converter)
				  (INST-inv-if-INST-in))
		  :use (:instance INST-inv-if-INST-in))))

(defthm not-INST-store-if-complete
    (implies (and (inv MT MA)
		  (equal (INST-stg i) '(complete))
		  (not (b1p (inst-specultv? i)))
		  (not (b1p (INST-modified? i)))
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-in i MT) (INST-p i)
		  (not (INST-fetch-error-detected-p i))
		  (not (INST-decode-error-detected-p i)))
	     (equal (INST-store? i) 0))
  :hints (("goal" :in-theory (e/d (inst-inv-def equal-b1p-converter)
				  (INST-inv-if-INST-in))
		  :use (:instance INST-inv-if-INST-in))))
(in-theory (disable not-INST-store-if-complete))	     
;;;;;;;;;;;;;;;;Commit field lemmas;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(defthm LSU-wbuf0-commit-if-commit-INST-in
    (implies (and (inv MT MA)
		  (INST-in i MT)
		  (equal (INST-stg i) '(commit wbuf0))
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-p i))
	     (equal (wbuf-commit? (LSU-wbuf0 (MA-LSU MA))) 1))
  :hints (("goal" :in-theory (e/d (inst-inv-def equal-b1p-converter)
				  (INST-inv-if-INST-in))
		  :use (:instance INST-inv-if-INST-in))))

(defthm LSU-wbuf1-commit-if-commit-INST-in
    (implies (and (inv MT MA)
		  (INST-in i MT)
		  (equal (INST-stg i) '(commit wbuf1))
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-p i))
	     (equal (wbuf-commit? (LSU-wbuf1 (MA-LSU MA))) 1))
  :hints (("goal" :in-theory (e/d (inst-inv-def equal-b1p-converter)
				  (INST-inv-if-INST-in))
		  :use (:instance INST-inv-if-INST-in))))

(defthm LSU-wbuf0-commit-if-commit-INST-in-2
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (uniq-inst-at-stg '(commit wbuf0) MT))
	     (equal (wbuf-commit? (LSU-wbuf0 (MA-LSU MA))) 1))
  :hints (("Goal" :use (:instance LSU-WBUF0-COMMIT-IF-COMMIT-INST-IN
				  (i (inst-at-stg '(commit wbuf0) MT)))
		  :in-theory (disable LSU-WBUF0-COMMIT-IF-COMMIT-INST-IN))))

(defthm LSU-wbuf1-commit-if-commit-INST-in-2
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (uniq-inst-at-stg '(commit wbuf1) MT))
	     (equal (wbuf-commit? (LSU-wbuf1 (MA-LSU MA))) 1))
  :hints (("Goal" :use (:instance LSU-WBUF1-COMMIT-IF-COMMIT-INST-IN
				  (i (inst-at-stg '(commit wbuf1) MT)))
		  :in-theory (disable LSU-WBUF1-COMMIT-IF-COMMIT-INST-IN))))

(defthm uniq-inst-at-stg-LSU-wbuf0
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (not (b1p (wbuf-complete? (LSU-wbuf0 (MA-LSU MA)))))
		  (b1p (wbuf-valid? (LSU-wbuf0 (MA-LSU MA)))))
	     (uniq-inst-at-stg '(LSU wbuf0) MT))
  :hints (("goal" :use
		  ((:instance UNIQ-INST-AT-LSU-WBUF0-IF-VALID)
		   (:instance uniq-inst-at-stgs*
			      (stgs '((LSU WBUF0)
				      (LSU WBUF0 LCH)
				      (COMPLETE WBUF0)
				      (COMMIT WBUF0))))
		   (:instance uniq-inst-at-stgs*
			      (stgs '((LSU WBUF0 LCH)
				      (COMPLETE WBUF0)
				      (COMMIT WBUF0))))
		   (:instance uniq-inst-at-stgs*
			      (stgs '((COMPLETE WBUF0)
				      (COMMIT WBUF0))))
		   (:instance LSU-WBUF0-COMPLETE-IF-COMPLETE-INST-IN
			      (i (inst-at-stg '(LSU wbuf0 lch) MT)))
		   (:instance LSU-WBUF0-COMPLETE-IF-COMPLETE-INST-IN
			      (i (inst-at-stg '(complete wbuf0) MT)))
		   (:instance LSU-WBUF0-COMPLETE-IF-COMPLETE-INST-IN
			      (i (inst-at-stg '(commit wbuf0) MT))))
		  :in-theory (disable UNIQ-INST-AT-LSU-WBUF0-IF-VALID
				      LSU-WBUF0-COMPLETE-IF-COMPLETE-INST-IN)
		  )))

(defthm uniq-inst-at-stg-LSU-wbuf1
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (not (b1p (wbuf-complete? (LSU-wbuf1 (MA-LSU MA)))))
		  (b1p (wbuf-valid? (LSU-wbuf1 (MA-LSU MA)))))
	     (uniq-inst-at-stg '(LSU wbuf1) MT))
  :hints (("goal" :use
		  ((:instance UNIQ-INST-AT-LSU-WBUF1-IF-VALID)
		   (:instance uniq-inst-at-stgs*
			      (stgs '((LSU WBUF1)
				      (LSU WBUF1 LCH)
				      (COMPLETE WBUF1)
				      (COMMIT WBUF1))))
		   (:instance uniq-inst-at-stgs*
			      (stgs '((LSU WBUF1 LCH)
				      (COMPLETE WBUF1)
				      (COMMIT WBUF1))))
		   (:instance uniq-inst-at-stgs*
			      (stgs '((COMPLETE WBUF1)
				      (COMMIT WBUF1))))
		   (:instance LSU-WBUF1-COMPLETE-IF-COMPLETE-INST-IN
			      (i (inst-at-stg '(LSU wbuf1 lch) MT)))
		   (:instance LSU-WBUF1-COMPLETE-IF-COMPLETE-INST-IN
			      (i (inst-at-stg '(complete wbuf1) MT)))
		   (:instance LSU-WBUF1-COMPLETE-IF-COMPLETE-INST-IN
			      (i (inst-at-stg '(commit wbuf1) MT))))
		  :in-theory (disable UNIQ-INST-AT-LSU-WBUF1-IF-VALID
				      LSU-WBUF1-COMPLETE-IF-COMPLETE-INST-IN)
		  )))

(defthm uniq-inst-at-stg-commit-wbuf0
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (b1p (wbuf-commit? (LSU-wbuf0 (MA-LSU MA))))
		  (b1p (wbuf-valid? (LSU-wbuf0 (MA-LSU MA)))))
	     (uniq-inst-at-stg '(commit wbuf0) MT))
  :hints (("goal" :use
		  ((:instance UNIQ-INST-AT-LSU-WBUF0-IF-VALID)
		   (:instance uniq-inst-at-stgs*
			      (stgs '((LSU WBUF0)
				      (LSU WBUF0 LCH)
				      (COMPLETE WBUF0)
				      (COMMIT WBUF0))))
		   (:instance uniq-inst-at-stgs*
			      (stgs '((LSU WBUF0 LCH)
				      (COMPLETE WBUF0)
				      (COMMIT WBUF0))))
		   (:instance uniq-inst-at-stgs*
			      (stgs '((COMPLETE WBUF0)
				      (COMMIT WBUF0)))))
		  :in-theory (disable
			      UNIQ-INST-AT-LSU-WBUF0-IF-VALID))))

(defthm uniq-inst-at-stg-commit-wbuf1
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (b1p (wbuf-commit? (LSU-wbuf1 (MA-LSU MA))))
		  (b1p (wbuf-valid? (LSU-wbuf1 (MA-LSU MA)))))
	     (uniq-inst-at-stg '(commit wbuf1) MT))
  :hints (("goal" :use
		  ((:instance UNIQ-INST-AT-LSU-WBUF1-IF-VALID)
		   (:instance uniq-inst-at-stgs*
			      (stgs '((LSU WBUF1)
				      (LSU WBUF1 LCH)
				      (COMPLETE WBUF1)
				      (COMMIT WBUF1))))
		   (:instance uniq-inst-at-stgs*
			      (stgs '((LSU WBUF1 LCH)
				      (COMPLETE WBUF1)
				      (COMMIT WBUF1))))
		   (:instance uniq-inst-at-stgs*
			      (stgs '((COMPLETE WBUF1)
				      (COMMIT WBUF1)))))
		  :in-theory (disable
			      UNIQ-INST-AT-LSU-WBUF1-IF-VALID))))

(defthm not-INST-excpt-if-commit-stg
    (implies (and (inv MT MA)
		  (INST-in i MT)
		  (or (equal (INST-stg i) '(commit wbuf0))
		      (equal (INST-stg i) '(commit wbuf1)))
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-p i))
	     (equal (INST-excpt? I) 0))
  :hints (("goal" :in-theory (e/d (inst-inv-def equal-b1p-converter)
				  (INST-inv-if-INST-in))
		  :use (:instance INST-inv-if-INST-in))))

(local
(defthm not-no-inst-at-stgs-in-trace-if-member-equal
    (implies (and (member-equal i trace)
		  (member-equal (INST-stg i) stgs))
	     (not (no-inst-at-stgs-in-trace stgs trace)))))

(local
(defthm not-no-inst-at-stg-in-trace-if-member-equal
    (implies (member-equal j trace)
	     (not (no-inst-at-stg-in-trace (INST-stg j) trace)))))

(local
(defthm no-inst-at-stg-in-trace-if-no-inst-at-stgs-in-trace
    (implies (and (not (no-inst-at-stg-in-trace stg trace))
		  (member-equal stg stgs))
	     (not (no-inst-at-stgs-in-trace stgs trace)))))

(encapsulate nil
(local
(defthm uniq-inst-at-LSU-lch-if-INST-in-help
    (implies (and (inv MT MA)
		  (subtrace-p trace MT) (INST-listp trace) 
		  (uniq-inst-at-stgs-in-trace '((LSU LCH)
						(LSU WBUF0 LCH)
						(LSU WBUF1 LCH))
					      trace)
		  (equal (INST-stg i) '(LSU lch))
		  (member-equal i trace) (INST-p i)
		  (MAETT-p MT) (MA-state-p MA))
	     (uniq-inst-at-stg-in-trace '(LSU lch) trace))))

(local
(defthm uniq-inst-at-LSU-lch-if-INST-in
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i)
		  (MAETT-p MT) (MA-state-p MA)
		  (equal (INST-stg i) '(LSU lch)))
	     (uniq-inst-at-stg '(LSU lch) MT))
  :hints (("goal" :use ((:instance UNIQ-INST-AT-LSU-LCH-IF-VALID)
			(:instance LSU-LCH-VALID-IF-INST-IN))
		  :in-theory (e/d (uniq-inst-at-stg uniq-inst-at-stgs
					    equal-b1p-converter INST-in)
				  (UNIQ-INST-AT-LSU-LCH-IF-VALID))))))
	
(local
(defthm uniq-inst-at-LSU-wbuf0-lch-if-INST-in-help
    (implies (and (inv MT MA)
		  (subtrace-p trace MT) (INST-listp trace) 
		  (uniq-inst-at-stgs-in-trace '((LSU LCH)
						(LSU WBUF0 LCH)
						(LSU WBUF1 LCH))
					      trace)
		  (equal (INST-stg i) '(LSU wbuf0 lch))
		  (member-equal i trace) (INST-p i)
		  (MAETT-p MT) (MA-state-p MA))
	     (uniq-inst-at-stg-in-trace '(LSU wbuf0 lch) trace))))

(local
(defthm uniq-inst-at-LSU-wbuf0-lch-if-INST-in
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i)
		  (MAETT-p MT) (MA-state-p MA)
		  (equal (INST-stg i) '(LSU wbuf0 lch)))
	     (uniq-inst-at-stg '(LSU wbuf0 lch) MT))
  :hints (("goal" :use ((:instance UNIQ-INST-AT-LSU-LCH-IF-VALID)
			(:instance LSU-LCH-VALID-IF-INST-IN))
		  :in-theory (e/d (uniq-inst-at-stg uniq-inst-at-stgs
					    equal-b1p-converter INST-in)
				  (UNIQ-INST-AT-LSU-LCH-IF-VALID))))))

(local
(defthm uniq-inst-at-LSU-wbuf1-lch-if-INST-in-help
    (implies (and (inv MT MA)
		  (subtrace-p trace MT) (INST-listp trace) 
		  (uniq-inst-at-stgs-in-trace '((LSU LCH)
						(LSU WBUF0 LCH)
						(LSU WBUF1 LCH))
					      trace)
		  (equal (INST-stg i) '(LSU wbuf1 lch))
		  (member-equal i trace) (INST-p i)
		  (MAETT-p MT) (MA-state-p MA))
	     (uniq-inst-at-stg-in-trace '(LSU wbuf1 lch) trace))))

(local
(defthm uniq-inst-at-LSU-wbuf1-lch-if-INST-in
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i)
		  (MAETT-p MT) (MA-state-p MA)
		  (equal (INST-stg i) '(LSU wbuf1 lch)))
	     (uniq-inst-at-stg '(LSU wbuf1 lch) MT))
  :hints (("goal" :use ((:instance UNIQ-INST-AT-LSU-LCH-IF-VALID)
			(:instance LSU-LCH-VALID-IF-INST-IN))
		  :in-theory (e/d (uniq-inst-at-stg uniq-inst-at-stgs
					    equal-b1p-converter INST-in)
				  (UNIQ-INST-AT-LSU-LCH-IF-VALID))))))

; If i is at stage IFU, DQ or EXECUTE, then
; i is the uniq instruction at the stage (INST-stg i).
; This may not be true for other stages, because there can be multiple retired
; instructions in a MAETT. 
(defthm uniq-inst-at-INST-stg-if-INST-in
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i)
		  (MAETT-p MT) (MA-state-p MA)
		  (or (IFU-stg-p (INST-stg i))
		      (DQ-stg-p (INST-stg i))
		      (execute-stg-p (INST-stg i))))
	     (uniq-inst-at-stg (INST-stg i) MT))
  :hints (("goal" :in-theory (enable IFU-stg-p DQ-stg-p execute-stg-p
				     IU-stg-p MU-stg-p BU-stg-p
				     LSU-stg-p))))
)

(encapsulate nil
(local
(defthm uniq-stage-inst-induct
    (implies (and (equal (INST-stg i) (INST-stg j))
		  (member-equal i trace)
		  (member-equal j trace)
		  (not (equal i j)))
	     (not (uniq-inst-at-stg-in-trace (INST-stg i) trace)))))

(local
(defthm uniq-stage-inst-help
    (implies (and (inv MT MA)
		  (uniq-inst-at-stg (INST-stg i) MT)
		  (INST-in i MT) (INST-p i)
		  (INST-in j MT) (INST-p j) 
		  (MAETT-p MT) (MA-state-p MA)
		  (equal (INST-stg i) (INST-stg j)))
	     (equal i j))
  :hints (("goal" :in-theory (enable INST-in uniq-inst-at-stg)))
  :rule-classes nil))

		      
; A corollary of uniq-inst-at-INST-stg-if-INST-in.
(defthm uniq-stage-inst
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i)
		  (INST-in j MT) (INST-p j) 
		  (MAETT-p MT) (MA-state-p MA)
		  (equal (INST-stg i) (INST-stg j))
		  (or (IFU-stg-p (INST-stg i))
		      (DQ-stg-p (INST-stg i))
		      (execute-stg-p (INST-stg i))))
	     (equal i j))
  :hints (("goal" :use (:instance uniq-stage-inst-help)))
  :rule-classes nil)
)

(in-theory (disable uniq-inst-at-INST-stg-if-INST-in))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;; ROB Related Lemmas Index
; Lemmas about Uniq-INST and robe-valid bits.
; Stages of inst-of-tag
; INST-inv of inst-of-tag
; ROB-head(MA-rob)=MT-rob-head(MT) and similar lemmas
; Lemmas about robe-complete? fields
; Lemmas about consistent-robe-p
; Lemmas about robe identity
; Lemmas related to rob-empty? rob-full?
; Lemmas about other fields.
; Lemmas to relate inst-of-tag and INST-at-stg
; definition and lemmas about tag-in-order

;  Related lemmas:
;   not-commit-jmp-if-rob-head-complete-wbuf
;   not-leave-excpt-if-rob-head-complete-wbuf
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(defthm rob-index-p-minis-8
    (implies (and (integerp idx) (< 0 idx) (<= idx *rob-size*))
	     (rob-index-p (- *rob-size* idx)))
  :hints (("goal" :in-theory (enable rob-index-p unsigned-byte-p))))

(defthm rob-index-p-minis-x-y
    (implies (and (integerp x) (integerp y)  (<= 0 y) (<= y x)
		  (< x *rob-size*))
	     (rob-index-p (- x y)))
  :hints (("goal" :in-theory (enable rob-index-p unsigned-byte-p))))

(defthm len-ROB-entries
    (implies (ROB-p ROB)
	     (equal (len (ROB-entries ROB)) *rob-size*))
  :hints (("goal" :in-theory (enable ROB-p ROB-ENTRIES-P))))

(defthm INST-tag-ge-0
    (implies (INST-p i) (<= 0 (INST-tag i)))
  :rule-classes :linear)

(defthm INST-tag-lt-8
    (implies (INST-p i) (< (INST-tag i) 8))
  :rule-classes :linear)

;;;;;;Begin of lemmas about Uniq-INST predicates and valid bits;;;;;;
;; inst-of-tag is an INST-p if there is an instruction with the tag.
(encapsulate nil
(local
(defthm INST-p-inst-of-tag-in-trace
    (implies (and (uniq-inst-of-tag-in-trace stg trace)
		  (INST-listp trace))
	     (INST-p (inst-of-tag-in-trace stg trace)))))

(defthm INST-p-inst-of-tag
    (implies (and (uniq-inst-of-tag rix MT)
		  (MAETT-p MT))
	     (INST-p (inst-of-tag rix MT)))
  :hints (("Goal" :in-theory (enable uniq-inst-of-tag inst-of-tag))))
)

(local
(defthm no-inst-of-tag-in-trace-INST-tag-if-member
    (implies (and (member-equal i trace)
		  (dispatched-p i)
		  (not (committed-p i)))
	     (not (no-inst-of-tag-in-trace (INST-tag i) trace)))
  :hints (("goal" :in-theory (enable dispatched-p committed-p)))))

(local
(defthm member-equal-inst-of-tag-in-trace
    (implies (uniq-inst-of-tag-in-trace rix trace)
	     (member-equal (inst-of-tag-in-trace rix trace) trace))))

;;; inst-of-tag belongs to a MAETT.
(defthm INST-in-inst-of-tag
    (implies (uniq-inst-of-tag rix MT)
	     (INST-in (inst-of-tag rix MT) MT))
  :Hints (("Goal" :in-theory (enable inst-of-tag uniq-inst-of-tag
				     INST-in))))

(encapsulate nil
(local
(defthm uniq-inst-of-tag-no-inst-of-tag-exclusive-help
    (implies (uniq-inst-of-tag-in-trace rix trace)
	     (not (no-inst-of-tag-in-trace rix trace)))))

(defthm uniq-inst-of-tag-no-inst-of-tag-exclusive
    (implies (uniq-inst-of-tag rix MT)
	     (not (no-inst-of-tag rix MT)))
  :hints (("goal" :in-theory (enable no-inst-of-tag uniq-inst-of-tag)))
  :rule-classes
  ((:rewrite)
   (:rewrite :corollary
	     (implies (no-inst-of-tag rix MT)
		      (not (uniq-inst-of-tag rix MT))))))
)

(encapsulate nil
(local
(defthm uniq-inst-of-tag-in-trace-if-robe-valid-help-help-help
    (implies (and (no-tag-conflict-at rix MT MA)
		  (MAETT-p MT)
		  (MA-state-p MA)
		  (b1p (robe-valid? (nth-robe rix (MA-rob MA)))))
	     (uniq-inst-of-tag rix MT))
  :hints (("Goal" :in-theory (enable no-tag-conflict-at)))))

(local
(defthm uniq-inst-of-tag-in-trace-if-robe-valid-help-help
    (implies (and (no-tag-conflict-under upper MT MA)
		  (MAETT-p MT)
		  (MA-state-p MA)
		  (integerp rix)
		  (<= 0 rix)
		  (integerp upper)
		  (< rix upper)
		  (b1p (robe-valid? (nth-robe rix (MA-rob MA)))))
	     (uniq-inst-of-tag rix MT))))

(local
(defthm uniq-inst-of-tag-in-trace-if-robe-valid-help
    (implies (and (no-tag-conflict MT MA)
		  (MAETT-p MT)
		  (MA-state-p MA)
		  (rob-index-p rix)
		  (b1p (robe-valid? (nth-robe rix (MA-rob MA)))))
	     (uniq-inst-of-tag rix MT))
  :hints (("Goal" :in-theory (enable rob-index-p unsigned-byte-p
				     no-tag-conflict)))))

; relation between robe-valid? and uniq-inst-of-tag.
(defthm uniq-inst-of-tag-if-robe-valid
    (implies (and (inv MT MA)
		  (MAETT-p MT)
		  (MA-state-p MA)
		  (rob-index-p rix)
		  (b1p (robe-valid? (nth-robe rix (MA-rob MA)))))
	     (uniq-inst-of-tag rix MT))
  :rule-classes
  ((:rewrite)
   (:rewrite :corollary
	     (implies (and (inv MT MA)
			   (MAETT-p MT)
			   (MA-state-p MA)
			   (rob-index-p rix)
			   (b1p (robe-valid? (nth-robe rix (MA-rob MA)))))
		      (uniq-inst-of-tag-in-trace rix (MT-trace MT)))
	     :hints (("goal" :in-theory (enable uniq-inst-of-tag))))))

) ; encapsulate

(encapsulate nil
(local
(defthm no-inst-of-tag-in-trace-if-not-robe-valid-help-help-help
    (implies (and (no-tag-conflict-at rix MT MA)
		  (MAETT-p MT)
		  (MA-state-p MA)
		  (not (b1p (robe-valid? (nth-robe rix (MA-rob MA))))))
	     (no-inst-of-tag rix MT))
  :hints (("Goal" :in-theory (enable no-tag-conflict-at)))))

(local
(defthm no-inst-of-tag-in-trace-if-not-robe-valid-help-help
    (implies (and (no-tag-conflict-under upper MT MA)
		  (MAETT-p MT)
		  (MA-state-p MA)
		  (integerp rix)
		  (<= 0 rix)
		  (integerp upper)
		  (< rix upper)
		  (not (b1p (robe-valid? (nth-robe rix (MA-rob MA))))))
	     (no-inst-of-tag rix MT))))

(local
(defthm no-inst-of-tag-in-trace-if-not-robe-valid-help
    (implies (and (no-tag-conflict MT MA)
		  (MAETT-p MT)
		  (MA-state-p MA)
		  (rob-index-p rix)
		  (not (b1p (robe-valid? (nth-robe rix (MA-rob MA))))))
	     (no-inst-of-tag rix MT))
  :hints (("Goal" :in-theory (enable rob-index-p unsigned-byte-p
				     no-tag-conflict)))))

(defthm no-inst-of-tag-if-not-robe-valid
    (implies (and (inv MT MA)
		  (MAETT-p MT)
		  (MA-state-p MA)
		  (rob-index-p rix)
		  (not (b1p (robe-valid? (nth-robe rix (MA-rob MA))))))
	     (no-inst-of-tag rix MT)))
)

(encapsulate nil
(local
(defthm robe-valid-nth-robe-INST-tag-help
    (implies (and (INST-inv i MA)		  
		  (MA-state-p MA)
		  (INST-p i)
		  (dispatched-p i)
		  (not (committed-p i)))
	     (b1p (robe-valid? (nth-robe (INST-tag i) (MA-rob MA)))))
  :hints (("Goal" :in-theory (enable inst-inv-def
				     lift-b-ops)))))

(defthm robe-valid-nth-robe-INST-tag
    (implies (and (inv MT MA)
		  (INST-in i MT)
		  (MAETT-p MT)
		  (MA-state-p MA)
		  (INST-p i)
		  (dispatched-p i)
		  (not (committed-p i)))
	     (b1p (robe-valid? (nth-robe (INST-tag i) (MA-rob MA)))))
  :rule-classes 
  ((:rewrite :corollary
    (implies (and (inv MT MA)
		  (INST-in i MT)
		  (MAETT-p MT)
		  (MA-state-p MA)
		  (INST-p i)
		  (dispatched-p i)
		  (not (committed-p i)))
	     (equal (robe-valid? (nth-robe (INST-tag i) (MA-rob MA))) 1))
    :hints (("goal" :in-theory (enable equal-b1p-converter lift-b-ops))))))
)

(encapsulate nil
(local
(defthm uniq-inst-of-tag-tag-if-INST-in-help
    (implies (and (no-tag-conflict-at (INST-tag i) MT MA)
		  (INST-inv i MA)
		  (MAETT-p MT)
		  (INST-p i)
		  (MA-state-p MA)
		  (dispatched-p i)
		  (not (committed-p i)))
	     (uniq-inst-of-tag (INST-tag i) MT))
  :hints (("goal" :In-theory (enable no-tag-conflict-at
				     inst-inv-def)))
  :rule-classes nil))
	  
(defthm uniq-inst-of-tag-INST-tag-if-INST-in
    (implies (and (inv MT MA)
		  (MAETT-p MT)
		  (MA-state-p MA)
		  (INST-p i)
		  (INST-in i MT)
		  (dispatched-p i)
		  (not (committed-p i)))
	     (uniq-inst-of-tag (INST-tag i) MT))
  :hints (("goal" :use (:instance uniq-inst-of-tag-tag-if-INST-in-help))))
)

;; Following two lemmas show that INST-tag and inst-of-tag
;; are inverse functions of each other in a sense.

(encapsulate nil
(local
(defthm INST-tag-inst-of-tag-in-trace
    (implies (and (INST-listp trace)
		  (rob-index-p rix)
		  (uniq-inst-of-tag-in-trace rix trace))
	     (equal (INST-tag (inst-of-tag-in-trace rix trace)) rix))))

(defthm INST-tag-inst-of-tag
    (implies (and (MAETT-p MT)
		  (rob-index-p rix)
		  (uniq-inst-of-tag rix MT))
	     (equal (INST-tag (inst-of-tag rix MT)) rix))
  :hints (("Goal" :in-theory (enable inst-of-tag uniq-inst-of-tag))))
)

(encapsulate nil
(local
(defthm inst-of-tag-in-trace-INST-tag
    (implies (and (INST-listp trace)
		  (INST-p i)
		  (member-equal i trace)
		  (uniq-inst-of-tag-in-trace (INST-tag i) trace)
		  (dispatched-p i)
		  (not (committed-p i)))
	     (equal (inst-of-tag-in-trace (INST-tag i) trace) i))
  :hints (("goal" :in-theory (enable dispatched-p committed-p)))))

(local
(defthm inst-of-tag-INST-tag-help
    (implies (and (inv MT MA)
		  (MAETT-p MT)
		  (INST-p i)
		  (INST-in i MT)
		  (uniq-inst-of-tag (INST-tag i) MT)
		  (dispatched-p i)
		  (not (committed-p i)))
	     (equal (inst-of-tag (INST-tag i) MT) i))
  :hints (("Goal" :in-theory (enable inst-of-tag INST-in uniq-inst-of-tag)))))

(defthm inst-of-tag-INST-tag
    (implies (and (inv MT MA)
		  (MAETT-p MT)
		  (INST-p i)
		  (MA-state-p MA)
		  (INST-in i MT)
		  (dispatched-p i)
		  (not (committed-p i)))
	     (equal (inst-of-tag (INST-tag i) MT) i)))
)

(encapsulate nil
(local  
 (defthm not-no-inst-of-tag-INST-stg-if-member-equal
     (implies (and (member-equal i trace)
		   (dispatched-p i ) (not (committed-p i)))
	      (not (no-inst-of-tag-in-trace (INST-tag i) trace)))
   :hints (("goal" :in-theory (enable dispatched-p committed-p)))))

(defthm not-no-inst-of-tag-if-inst-in
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-p i) (INST-in i MT)
		  (dispatched-p i) (not (committed-p i)))
	     (not (no-inst-of-tag (INST-tag i) MT)))
  :hints (("goal" :in-theory (enable inst-in no-inst-of-tag))))
)

;;;;;;End of lemmas about Uniq-INST predicates and valid bits;;;;;;

;;;;; Begin of lemmas about stages of inst-of-tag ;;;;;
(encapsulate nil
(local
(defthm execute-or-complete-stg-p-inst-of-tag-in-trace
  (implies (and (not (execute-stg-p
		      (INST-stg (inst-of-tag-in-trace rix trc))))
		(not (complete-stg-p
		      (INST-stg (inst-of-tag-in-trace rix trc)))))
	   (not (uniq-inst-of-tag-in-trace rix trc)))
  :hints (("goal" :in-theory (enable committed-p dispatched-p)))))

(defthm execute-or-complete-stg-p-inst-of-tag
    (implies (uniq-inst-of-tag rix MT)
	     (and (dispatched-p (inst-of-tag rix MT))
		  (not (committed-p (inst-of-tag rix MT)))))
  :rule-classes
  ((:rewrite :corollary
	     (implies (not (dispatched-p (inst-of-tag rix MT)))
		      (not (uniq-inst-of-tag rix MT))))
   (:rewrite :corollary
	     (implies (committed-p (inst-of-tag rix MT))
		      (not (uniq-inst-of-tag rix MT))))
   (:rewrite :corollary
     (implies (and (not (execute-stg-p (INST-stg (inst-of-tag rix MT))))
		   (not (complete-stg-p (INST-stg (inst-of-tag rix MT)))))
	      (not (uniq-inst-of-tag rix MT)))
     :hints (("goal" :in-theory (e/d (committed-p dispatched-p)
				     (INST-OF-TAG-IS-DISPATCHED
				      INST-OF-TAG-IS-NOT-COMMITTED))))))
  :hints (("Goal" :in-theory (enable inst-of-tag uniq-inst-of-tag
				     dispatched-p committed-p))))
) ; encapsulate
;;;;; End of lemmas about stages of inst-of-tag ;;;;;

;;;;; INST-inv about inst-of-tag
(defthm INST-inv-inst-of-tag
    (implies (and (inv MT MA)
		  (uniq-inst-of-tag rix MT))
	     (INST-inv (inst-of-tag rix MT) MA)))

;;;;; rob-head-MA-rob-=-MT-rob-head and similar lemmas.
;; Rob-head field of MA and ROB-head field of MAETT are equal.
(defthm rob-head-MA-rob-=-MT-rob-head
    (implies (and (inv MT MA)
		  (MA-state-p MA)
		  (MAETT-p MT))
	     (equal (rob-head (MA-rob MA)) (MT-rob-head MT)))
  :hints (("goal" :in-theory (enable weak-inv inv
				     misc-inv))))

;; Rob-tail field of MA and ROB-tail field of MAETT are equal.
(defthm rob-tail-MA-rob-=-MT-rob-tail
    (implies (and (inv MT MA)
		  (MA-state-p MA)
		  (MAETT-p MT))
	     (equal (rob-tail (MA-rob MA)) (MT-rob-tail MT)))
  :hints (("goal" :in-theory (enable weak-inv inv
				     misc-inv))))

(defthm MA-rob-flg-MT-rob-flg
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA))
	     (equal (rob-flg (MA-rob MA)) (MT-rob-flg MT)))
  :hints (("Goal" :in-theory (enable inv misc-inv))))

(defthm MT-ROB-tail-le-MT-rob-head
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA) 
		  (b1p (ROB-flg (MA-ROB MA))))
	     (<= (MT-ROB-tail MT) (MT-ROB-head MT)))
  :hints (("Goal" :in-theory (e/d (consistent-ROB-flg-p
				   consistent-MA-p consistent-rob-p
				   lift-b-ops)
				  (consistent-rob-flg-p-forward))
		  :cases ((consistent-MA-p MA))))
  :rule-classes :linear)

(defthm MT-ROB-tail-ge-MT-rob-head
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA) 
		  (not (b1p (ROB-flg (MA-ROB MA)))))
	     (>= (MT-ROB-tail MT) (MT-ROB-head MT)))
  :hints (("Goal" :in-theory (e/d (consistent-ROB-flg-p
				   consistent-MA-p consistent-rob-p
				   lift-b-ops)
				  (consistent-rob-flg-p-forward))
		  :cases ((consistent-MA-p MA))))
  :rule-classes :linear)

(defthm MT-ROB-head-ge-0
    (implies (MAETT-p MT) (>= (MT-rob-head MT) 0))
  :rule-classes :linear)

(defthm MT-ROB-tail-ge-0
    (implies (MAETT-p MT) (>= (MT-rob-tail MT) 0))
  :rule-classes :linear)

(defthm MT-ROB-head-lt-8
    (implies (MAETT-p MT) (< (MT-rob-head MT) 8))
  :rule-classes :linear)

(defthm MT-ROB-tail-lt-8
    (implies (MAETT-p MT) (< (MT-rob-tail MT) 8))
  :rule-classes :linear)

(defthm INST-in-order-inst-of-tag-not-dispatched
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-in i MT)
		  (uniq-inst-of-tag rix MT)
		  (not (dispatched-p i)))
	     (INST-in-order-p (inst-of-tag rix MT) i MT)))

(encapsulate nil
; If there is a dispatched but not yet committed instruction, the ROB
; is not empty.  Thus there is an instruction at MT-head
(local
(defthm not-uniq-inst-of-tag-in-trace-if-no-dispatched-inst-p
    (implies (no-dispatched-inst-p trace)
	     (not (uniq-inst-of-tag-in-trace rix trace)))))

(local
(defthm uncommitted-inst-p-is-after-MT-ROB-head-help
    (implies (and (INST-listp trace)
		  (distinct-member-p trace)
		  (in-order-trace-p trace)
		  (in-order-rob-trace-p trace rob-head)
		  (uniq-inst-of-tag-in-trace rob-head trace)
		  (INST-p i) (member-equal i trace)
		  (not (committed-p i))
		  (not (equal (inst-of-tag-in-trace rob-head trace)
			      i)))
	     (member-in-order (inst-of-tag-in-trace rob-head trace) i trace))
  :hints (("goal" :in-theory (enable committed-p dispatched-p
				     member-in-order*)))))

(defthm uncommitted-inst-p-is-after-MT-ROB-head
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (uniq-inst-of-tag (MT-rob-head MT) MT)
		  (INST-p i) (INST-in i MT)
		  (not (committed-p i))
		  (not (equal (inst-of-tag (MT-rob-head MT) MT) i)))
	     (INST-in-order-p (inst-of-tag (MT-rob-head MT) MT) i MT))
  :hints (("goal" :in-theory (enable inv in-order-dispatch-commit-p
				     weak-inv
				     MT-distinct-INST-p
				     in-order-rob-p
				     INST-in-order-p inst-of-tag
				     uniq-inst-of-tag INST-in))))
)

(defthm INST-tag-step-INST-at-DQ
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (uniq-inst-at-stg '(DQ 0) MT)
		  (b1p (dispatch-inst? MA)))
	     (equal (INST-tag (step-INST (INST-at-stg '(DQ 0) MT)
					 MT MA sigs))
		    (MT-rob-tail MT)))
  :hints (("Goal" :in-theory (enable step-inst-DQ-inst
				     step-inst-low-level-functions))))
;;;;;;;;;Lemmas about robe-complete? fields;;;;;;;;;;;;;;;;;;
(encapsulate nil
(local
(defthm robe-execute-nth-robe-INST-tag-help
    (implies (and (INST-inv i MA)
		  (MAETT-p MT)
		  (MA-state-p MA)
		  (INST-p i)
		  (execute-stg-p (INST-stg i)))
	     (equal (robe-complete? (nth-robe (INST-tag i) (MA-rob MA)))
		    0))
  :hints (("Goal" :in-theory (enable inst-inv-def
				     equal-b1p-converter
				     lift-b-ops)))))

(defthm robe-execute-nth-robe-INST-tag
    (implies (and (inv MT MA)
		  (MAETT-p MT)
		  (MA-state-p MA)
		  (INST-p i)
		  (INST-in i MT)
		  (execute-stg-p (INST-stg i)))
	     (equal (robe-complete? (nth-robe (INST-tag i) (MA-rob MA))) 0)))
)

(encapsulate nil
(local
(defthm robe-execute-nth-robe-rix-help
    (implies (and (inv MT MA)
		  (MAETT-p MT)
		  (MA-state-p MA)
		  (rob-index-p rix)
		  (uniq-inst-of-tag rix MT)
		  (execute-stg-p (INST-stg (inst-of-tag rix MT))))
	     (equal (robe-complete? (nth-robe (INST-tag (inst-of-tag rix MT))
					      (MA-rob MA)))
		    0))
  :hints (("goal" :in-theory (disable  INST-TAG-INST-OF-TAG)))
  :rule-classes nil)
)

(defthm robe-execute-nth-robe-rix
    (implies (and (inv MT MA)
		  (MAETT-p MT)
		  (MA-state-p MA)
		  (rob-index-p rix)
		  (uniq-inst-of-tag rix MT)
		  (execute-stg-p (INST-stg (inst-of-tag rix MT))))
	     (equal (robe-complete? (nth-robe rix (MA-rob MA))) 0))
  :hints (("Goal" :use (:instance robe-execute-nth-robe-rix-help))))
)

(encapsulate nil
(local
(defthm robe-complete-nth-robe-INST-tag-help
    (implies (and (INST-inv i MA)
		  (MAETT-p MT)
		  (MA-state-p MA)
		  (INST-p i)
		  (complete-stg-p (INST-stg i)))
	     (equal (robe-complete? (nth-robe (INST-tag i) (MA-rob MA))) 1))
  :hints (("Goal" :in-theory (enable inst-inv-def
				     equal-b1p-converter
				     lift-b-ops)))))

(defthm robe-complete-nth-robe-INST-tag
    (implies (and (inv MT MA)
		  (MAETT-p MT)
		  (MA-state-p MA)
		  (INST-p i)
		  (INST-in i MT)
		  (complete-stg-p (INST-stg i)))
	     (equal (robe-complete? (nth-robe (INST-tag i) (MA-rob MA))) 1)))
) ;encapsulate

(encapsulate nil
(local
(defthm robe-complete-nth-robe-rix-help
    (implies (and (inv MT MA)
		  (MAETT-p MT)
		  (MA-state-p MA)
		  (rob-index-p rix)
		  (uniq-inst-of-tag rix MT)
		  (complete-stg-p (INST-stg (inst-of-tag rix MT))))
	     (equal (robe-complete? (nth-robe (INST-tag (inst-of-tag rix MT))
					      (MA-rob MA)))
		    1))
  :hints (("goal" :in-theory (disable  INST-TAG-INST-OF-TAG)))
  :rule-classes nil)
)

(defthm robe-complete-nth-robe-rix
    (implies (and (inv MT MA)
		  (MAETT-p MT)
		  (MA-state-p MA)
		  (rob-index-p rix)
		  (uniq-inst-of-tag rix MT)
		  (complete-stg-p (INST-stg (inst-of-tag rix MT))))
	     (equal (robe-complete? (nth-robe rix (MA-rob MA))) 1))
  :hints (("Goal" :use (:instance robe-complete-nth-robe-rix-help))))
)

(defthm complete-stg-if-robe-complete
    (implies (and (inv MT MA)
		  (MAETT-p MT)
		  (MA-state-p MA)
		  (rob-index-p rix)
		  (uniq-inst-of-tag rix MT)
		  (b1p (robe-complete? (nth-robe rix (MA-rob MA)))))
	     (complete-stg-p (INST-stg (inst-of-tag rix MT))))
  :hints (("goal" :use (:instance INST-is-at-one-of-the-stages
				  (i (inst-of-tag rix MT))))))

(defthm execute-stg-if-not-robe-complete
    (implies (and (inv MT MA)
		  (MAETT-p MT)
		  (MA-state-p MA)
		  (rob-index-p rix)
		  (uniq-inst-of-tag rix MT)
		  (not (b1p (robe-complete? (nth-robe rix (MA-rob MA))))))
	     (execute-stg-p (INST-stg (inst-of-tag rix MT))))
  :hints (("goal" :use (:instance INST-is-at-one-of-the-stages
				  (i (inst-of-tag rix MT))))))

(in-theory (disable complete-stg-if-robe-complete
		    execute-stg-if-not-robe-complete))

(defthm robe-complete-if-complete-stg-inst-of-tag
    (implies (and (inv MT MA)
		  (MAETT-p MT)
		  (MA-state-p MA)
		  (rob-index-p rix)
		  (uniq-inst-of-tag rix MT))
	     (equal (b1p (robe-complete? (nth-robe rix (MA-rob MA))))
		    (complete-stg-p (INST-stg (inst-of-tag rix MT)))))
  :hints (("goal" :use (:instance INST-is-at-one-of-the-stages
				  (i (inst-of-tag rix MT))))))

(in-theory (disable robe-complete-if-complete-stg-inst-of-tag))

;;;;; End of lemmas about robe-complete? field

;;;;; Lemmas about consistent-robe-p
(encapsulate nil
(local
(defthm rob-index-+-1
    (implies (rob-index-p idx)
	     (equal (rob-index (+ 1 idx))
		    (b-if (logbit *ROB-INDEX-SIZE* (+ 1 idx))
			  0 (+ 1 idx))))
  :hints (("goal" :in-theory (enable lift-b-ops rob-index-p rob-index
				     unsigned-byte-p)
		  :cases ((B1P (LOGBIT 3 (+ 1 IDX)))))
	  ("subgoal 1" :use (:instance logbit-0-if-val-lt-expt-2-width
				       (val (+ 1 idx)) (width 3))))))

(local
(defthm logbit3-0-if-rob-index-not-7
    (implies (rob-index-p rix)
	     (iff (b1p (logbit 3 (+ 1 rix))) (equal rix 7)))
  :Hints (("goal" :use (:instance logbit-0-if-val-lt-expt-2-width
				  (val (+ 1 rix)) (width 3))
		  :in-theory (enable rob-p rob-index-p unsigned-byte-p)))))

(local
 (defthm consistent-robe-p-nth-robe-help
     (implies (and (ROBE-listp entries)
		   (equal (len entries) (- *ROB-SIZE* idx))
		   (rob-index-p idx)
		   (rob-index-p rix)
		   (<= idx rix)
		   (consistent-rob-entries-p entries idx ROB))
	      (consistent-robe-p (nth (- rix idx) entries) rix rob))
   :hints (("goal" :in-theory (enable rob-index-p unsigned-byte-p)))
   :rule-classes nil))

; Any rob-entry satisfies consistent-robe-p.
; The proof requires logbit-0-if-val-lt-expt-2-width
(defthm consistent-robe-p-nth-robe
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (rob-index-p rix))
	     (consistent-robe-p (nth-robe rix (MA-ROB MA))
				rix (MA-rob MA)))
  :hints (("goal" :in-theory (enable inv consistent-rob-p
				     nth-robe
				     rob-index-p unsigned-byte-p
				     consistent-MA-p)
		  :use (:instance consistent-robe-p-nth-robe-help
				  (idx 0)
				  (rob (MA-rob MA))
				  (entries (ROB-entries (MA-rob MA)))))))
)
;;;;; End of Lemmas about consistent-robe-p
;;;;; Lemmas about tag identity
(encapsulate nil
(local
(defthm not-member-equal-if-no-inst-of-tag-in-trace
    (implies (and (no-inst-of-tag-in-trace (INST-tag j) trace)
		  (dispatched-p j) (not (committed-p j)))
	     (not (member-equal j trace)))
  :hints (("goal" :in-theory (enable committed-p dispatched-p)))))

(local
(defthm tag-identity-help3
    (implies (and (uniq-inst-of-tag-in-trace rix trace)
		  (INST-p i) (member-equal i trace)
		  (dispatched-p i) (not (committed-p i))
		  (INST-p j) (member-equal j trace)
		  (dispatched-p j) (not (committed-p j))
		  (equal (INST-tag i) rix)
		  (equal (INST-tag j) rix))
	     (equal i j))
  :hints (("goal" :in-theory (enable dispatched-p committed-p)
		  :induct t))
  :rule-classes nil))

(local
(defthm tag-identity-help-help
    (implies (and (uniq-inst-of-tag (INST-tag i) MT)
		  (INST-p i) (INST-in i MT)
		  (dispatched-p i) (not (committed-p i))
		  (INST-p j) (INST-in j MT)
		  (dispatched-p j) (not (committed-p j)))
	     (equal (equal (INST-tag i) (INST-tag j))
		    (equal i j)))
  :hints (("goal" :use (:instance tag-identity-help3
				  (rix (INST-tag i)) (trace (MT-trace MT)))
		  :in-theory (enable uniq-inst-of-tag
				     INST-in)))))

(local
(defthm tag-identity-help
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (no-tag-conflict-at (INST-tag i) MT MA)
		  (INST-p i) (INST-in i MT)
		  (dispatched-p i) (not (committed-p i))
		  (INST-p j) (INST-in j MT)
		  (dispatched-p j) (not (committed-p j)))
	     (equal (equal (INST-tag i) (INST-tag j))
		    (equal i j)))
  :hints (("goal" :in-theory (e/d (no-tag-conflict-at)
				  (NO-TAG-CONFLICT-AT-ALL-RIX
				   UNIQ-INST-OF-TAG-INST-TAG-IF-INST-IN
				   UNIQ-INST-OF-TAG-IF-ROBE-VALID))))))

(defthm tag-identity
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-p i) (INST-in i MT)
		  (dispatched-p i) (not (committed-p i))
		  (INST-p j) (INST-in j MT)
		  (dispatched-p j) (not (committed-p j)))
	     (equal (equal (INST-tag i) (INST-tag j))
		    (equal i j)))
  :hints (("goal" :restrict ((tag-identity-help ((MA MA) (MT MT)))))))
)

;;;;; Begin of Lemmas related to rob-empty?
(encapsulate nil
(local
(defthm zbp-robe-valid-if-rob-empty-help-help
    (implies (AND (ROB-P ROB)
		  (B1P (ROB-EMPTY? ROB))
		  (B1P (ROBE-VALID? robe)))
	     (not (CONSISTENT-ROBE-P robe rix ROB)))
  :hints (("goal" :in-theory (enable consistent-robe-p rob-empty?
				     lift-b-ops bv-eqv-iff-equal)))))

(local
(defthm zbp-robe-valid-if-rob-empty-help
    (IMPLIES (AND (B1P (ROBE-VALID? (NTH RIX entries)))
		  (ROB-P ROB)
		  (B1P (ROB-EMPTY? ROB))
		  (robe-listp entries)
		  (< rix (len entries)))
	     (not (CONSISTENT-ROB-ENTRIES-P entries rix2 ROB)))))

(defthm not-robe-valid-if-rob-empty-and-consistent-rob
    (implies (and (ROB-p rob)
		  (rob-index-p rix)
		  (b1p (rob-empty? rob))
		  (consistent-rob-p rob))
	     (equal (robe-valid? (nth-robe rix rob)) 0))
  :hints (("goal" :in-theory (enable nth-robe rob-entries-p rob-p
				     equal-b1p-converter
				     lift-b-ops
				     consistent-rob-p))))
)

(defthm not-robe-valid-nth-robe-if-rob-empty
    (implies (and (inv MT MA)
		  (MA-state-p MA)
		  (rob-index-p rix)
		  (b1p (rob-empty? (MA-rob MA))))
	     (equal (robe-valid? (nth-robe rix (MA-rob MA))) 0))
  :hints (("goal" :in-theory (enable consistent-rob-p-forward))))

(defthm robe-not-head-if-INST-at-execute-stg-while-commit
    (implies (and (inv MT MA)
		  (INST-p i)
		  (MAETT-p MT)
		  (MA-state-p MA)
		  (INST-in i MT)
		  (b1p (commit-inst? MA))
		  (execute-stg-p (INST-stg i)))
	     (not (equal (INST-tag i) (MT-rob-head MT))))
  :hints  (("goal" :in-theory (e/d (commit-inst? lift-b-ops)
				   ()))))

(defthm not-rob-empty-if-INST-is-executed
    (implies (and (inv MT MA) 
		  (dispatched-p i)
		  (not (committed-p i))
		  (INST-in i MT)
		  (MAETT-p MT)
		  (MA-state-p MA)
		  (INST-p i))
	     (equal (rob-empty? (MA-rob MA)) 0))
  :hints (("Goal" :use (:instance not-robe-valid-nth-robe-if-rob-empty
				  (rix (INST-tag i)))
		  :in-theory (e/d (equal-b1p-converter lift-b-ops)
				  (not-robe-valid-nth-robe-if-rob-empty
				   NOT-ROBE-VALID-IF-ROB-EMPTY-AND-CONSISTENT-ROB))))
  :rule-classes
  ((:rewrite)
   (:rewrite :corollary
	     (implies (and (inv MT MA) 
			   (execute-stg-p (INST-stg i))
			   (INST-in i MT)
			   (MAETT-p MT)
			   (MA-state-p MA)
			   (INST-p i))
		      (equal (rob-empty? (MA-rob MA)) 0)))
   (:rewrite :corollary
	     (implies (and (inv MT MA) 
			   (complete-stg-p (INST-stg i))
			   (INST-in i MT)
			   (MAETT-p MT)
			   (MA-state-p MA)
			   (INST-p i))
		      (equal (rob-empty? (MA-rob MA)) 0)))))

(encapsulate nil 
(local
(defthm robe-empty-if-MT-rob-head-tail-matches-help
    (implies (and (consistent-rob-entries-p
		   (nthcdr (- idx n) (ROB-entries ROB)) (rob-index (- idx n))
		   ROB)
		  (integerp idx) (integerp n)
		  (<= 0 n) (<= n idx) (< idx *rob-size*)
		  (ROB-p rob)
		  (equal (rob-tail ROB) (rob-head ROB))
		  (not (b1p (rob-flg ROB))))
	     (equal (robe-empty? idx ROB) 1))
  :Hints (("Goal" :in-theory (enable consistent-rob-entries-p
				     ROBE-EMPTY? nth-robe lift-b-ops
				     equal-b1p-converter
				     consistent-robe-p)
		  :expand (CONSISTENT-ROB-ENTRIES-P
			   (NTHCDR (+ IDX (- N)) (ROB-ENTRIES ROB))
			   (ROB-INDEX (+ IDX (- N)))
			   ROB)
		  :induct (natural-induction n)))
  :rule-classes nil))

(defthm robe-empty-if-MT-rob-head-tail-matches
    (implies (and (inv MT MA)
		  (equal (MT-rob-tail MT) (MT-rob-head MT))
		  (rob-index-p idx)
		  (not (b1p (MT-rob-flg MT)))
		  (MAETT-p MT) (MA-state-p MA))
	     (equal (robe-empty? idx (MA-ROB MA)) 1))
  :Hints (("Goal" :in-theory (e/d (rob-index-p CONSISTENT-MA-P
					       UNSIGNED-BYTE-P
					       consistent-rob-p)
				  (CONSISTENT-MA-P-forward))
		  :use ((:instance robe-empty-if-MT-rob-head-tail-matches-help
				   (n idx)
				   (ROB (MA-rob MA)))
			(:instance consistent-MA-p-forward
				   (MA MA))))))
)

(defthm robe-empty-under-if-head-tail-matches
    (implies (and (inv MT MA)
		  (equal (MT-rob-tail MT) (MT-rob-head MT))
		  (not (b1p (MT-rob-flg MT)))
		  (integerp idx) (<= 0 idx) (<= idx *rob-size*)
		  (MAETT-p MT) (MA-state-p MA))
	     (equal (robe-empty-under? idx (MA-ROB MA)) 1))
  :hints (("goal" :in-theory (enable lift-b-ops ROBE-EMPTY-UNDER?
				     rob-index-p unsigned-byte-p
				     equal-b1p-converter)
		  :induct (natural-induction idx))))

(encapsulate nil
(local
(defthm ROB-valid-MT-rob-head-if-not-ROB-empty-help
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (ROB-entry-p robe)
		  (consistent-robe-p robe (MT-ROB-head MT) (MA-ROB MA))
		  (consistent-rob-flg-p (MA-ROB MA))
		  (not (b1p (ROB-empty? (MA-rob MA)))))
	     (equal (ROBE-valid? robe) 1))
  :hints (("goal" :in-theory (enable consistent-robe-p
				     consistent-rob-flg-p
				     ROB-empty? lift-b-ops
				     equal-b1p-converter)))))

; ROB-empty? is not on, MT-ROB-head contains a valid instruction.
(defthm ROB-valid-MT-rob-head-if-not-ROB-empty
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (not (b1p (ROB-empty? (MA-rob MA)))))
	     (equal (ROBE-valid? (nth-robe (MT-ROB-head MT) (MA-ROB MA))) 1))
  :hints (("goal" :in-theory (enable consistent-ROB-p-forward
				     consistent-ROB-flg-p-forward))))
)

(defthm not-commit-inst-if-rob-empty
    (implies (and  (inv MT MA)
		   (b1p (rob-empty? (MA-ROB MA)))
		   (MAETT-p MT) (MA-state-p MA)) 
	     (equal (commit-inst? MA) 0))
  :hints (("Goal" :in-theory (enable commit-inst?))))

; If ROB is not empty, ROB contains an instruction at index MT-ROB-head.
(defthm uniq-inst-of-tag-MT-rob-head-if-not-empty
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (not (b1p (ROB-empty? (MA-rob MA)))))
	     (uniq-inst-of-tag (MT-rob-head MT) MT)))

(defthm MT-rob-head-MT-rob-tail-if-rob-empty
    (implies (and (inv MT MA)
		  (b1p (rob-empty? (MA-rob MA)))
		  (MAETT-p MT) (MA-state-p MA)) 
	     (equal (MT-rob-tail MT) (MT-ROB-head MT)))
  :hints (("Goal" :in-theory (enable rob-empty? lift-b-ops))))

; When ROB is not full, the entry pointed by ROB-tail is free.
(defthm robe-valid-MT-ROB-tail-if-not-rob-full
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA) 
		  (not (b1p (rob-full? (MA-ROB MA)))))
	     (equal (robe-valid? (nth-robe (MT-ROB-tail MT) (MA-rob MA)))
		    0))
  :hints (("goal" :in-theory (e/d (rob-full? lift-b-ops
					     consistent-robe-p)
				  (CONSISTENT-ROBE-P-NTH-ROBE))
		  :use (:instance CONSISTENT-ROBE-P-NTH-ROBE
				  (rix (MT-ROB-tail MT))))))

(defthm not-INST-at-rob-tail-if-execute-or-complete
    (implies  (and (inv MT MA)
		   (INST-in i MT) (INST-p i) 
		   (MAETT-p MT) (MA-state-p MA)
		   (or (execute-stg-p (INST-stg i))
		       (complete-stg-p (INST-stg i)))
		   (not (b1p (ROB-full? (MA-ROB MA)))))
	      (equal (equal (INST-tag i) (MT-rob-tail MT)) nil))
  :hints (("Goal" :in-theory (disable robe-valid-MT-ROB-tail-if-not-rob-full)
		  :use (:instance robe-valid-MT-ROB-tail-if-not-rob-full))))

;;; End of Lemmas related to rob-empty?

;;;;; Lemmas about other fields in robe;;;;;;;
(defthm not-INST-bu-if-decode-error
    (implies (and (b1p (INST-decode-error? i))
		  (inst-p i))
	     (equal (INST-bu? i) 0))
  :hints (("goal" :in-theory (enable INST-decode-error? INST-bu?
				     decode-illegal-inst?
				     equal-b1p-converter
				     INST-opcode
				     lift-b-ops logbit* decode rdb
				     INST-cntlv))))

(defthm INST-BU-if-INST-decode-error-detected
    (implies (and (INST-p i)
		  (INST-decode-error-detected-p i))
	     (equal (INST-BU? i) 0))
  :hints (("Goal" :in-theory (enable INST-BU? INST-decode-error-detected-p
				     INST-cntlv equal-b1p-converter
				     lift-b-ops decode logbit*
				     rdb))))

(defthm INST-BU-if-INST-data-accs-error-detected
    (implies (and (INST-p i)
		  (INST-data-accs-error-detected-p i))
	     (equal (INST-BU? i) 0))
  :hints (("Goal" :in-theory (enable INST-BU? INST-data-accs-error-detected-p
				     INST-load-accs-error-detected-p
				     INST-store-accs-error-detected-p
				     INST-cntlv equal-b1p-converter
				     lift-b-ops decode logbit*
				     rdb))))

(encapsulate nil
(local
(defthm robe-branch-INST-branch-help
    (implies (and (MA-state-p MA)
		  (MAETT-p MT)
		  (rob-index-p rix)
		  (INST-inv (inst-of-tag rix MT) MA)
		  (uniq-inst-of-tag rix MT)
		  (not (INST-fetch-error-detected-p (inst-of-tag rix MT)))
		  (not (b1p (INST-modified? (inst-of-tag rix MT))))
		  (not (b1p (inst-specultv? (inst-of-tag rix MT)))))
	     (equal (robe-branch? (nth-robe rix (MA-rob MA)))
		    (INST-BU? (inst-of-tag rix MT))))
  :Hints (("goal" :in-theory (enable inst-inv-def)
		  :use (:instance INST-is-at-one-of-the-stages
				  (i (inst-of-tag rix MT)))))))

(local
(defthm robe-branch-INST-branch-help2
    (implies (and (MA-state-p MA)
		  (MAETT-p MT)
		  (rob-index-p rix)
		  (INST-inv (inst-of-tag rix MT) MA)
		  (uniq-inst-of-tag rix MT)
		  (INST-fetch-error-detected-p (inst-of-tag rix MT))
		  (not (b1p (INST-modified? (inst-of-tag rix MT))))
		  (not (b1p (inst-specultv? (inst-of-tag rix MT)))))
	     (equal (robe-branch? (nth-robe rix (MA-rob MA)))
		    0))
  :Hints (("goal" :in-theory (enable inst-inv-def)
		  :use (:instance INST-is-at-one-of-the-stages
				  (i (inst-of-tag rix MT)))))))

(defthm robe-branch-INST-branch-1
    (implies (and (inv MT MA)
		  (MA-state-p MA)
		  (MAETT-p MT)
		  (rob-index-p rix)
		  (uniq-inst-of-tag rix MT)
		  (not (b1p (INST-modified? (inst-of-tag rix MT))))
		  (not (b1p (inst-specultv? (inst-of-tag rix MT)))))
	     (equal (robe-branch? (nth-robe rix (MA-rob MA)))
		    (if (INST-excpt-detected-p (inst-of-tag rix MT))
			0 (INST-BU? (inst-of-tag rix MT)) )))
  :hints (("Goal" :in-theory (enable exception-relations
				     INST-EXCPT-DETECTED-P))))

(defthm robe-branch-INST-branch-2
    (implies (and (inv MT MA)
		  (MA-state-p MA)
		  (MAETT-p MT)
		  (INST-p i)
		  (INST-in i MT)
		  (not (b1p (INST-modified? i)))
		  (not (b1p (inst-specultv? i)))
		  (dispatched-p i)
		  (not (committed-p i)))
	     (equal (robe-branch? (nth-robe (INST-tag i) (MA-rob MA)))
		    (if (INST-excpt-detected-p i)
			0 (INST-BU? i)))))
)

(encapsulate nil
(local
(defthm robe-val-INST-dest-val-1-help
    (implies (and (MAETT-p MT) (MA-state-p MA)
		  (complete-stg-p (INST-stg (inst-of-tag rix MT)))
		  (rob-index-p rix)
		  (INST-inv (inst-of-tag rix MT) MA)
		  (uniq-inst-of-tag rix MT)
		  (INST-writeback-p (inst-of-tag rix MT))
		  (not (b1p (INST-modified? (inst-of-tag rix MT))))
		  (not (b1p (inst-specultv? (inst-of-tag rix MT))))
		  (not (INST-excpt-detected-p (inst-of-tag rix MT))))
	     (equal (robe-val (nth-robe rix (MA-rob MA)))
		    (INST-dest-val (inst-of-tag rix MT))))
  :hints (("goal" :in-theory (enable INST-inv
				     INST-excpt-detected-p
				     INST-inv-def)))))

(defthm robe-val-INST-dest-val-1
    (implies (and (inv MT MA)
		  (complete-stg-p (INST-stg (inst-of-tag rix MT)))
		  (INST-writeback-p (inst-of-tag rix MT))
		  (MAETT-p MT) (MA-state-p MA)
		  (rob-index-p rix)
		  (uniq-inst-of-tag rix MT)
		  (not (b1p (INST-modified? (inst-of-tag rix MT))))
		  (not (b1p (inst-specultv? (inst-of-tag rix MT))))
		  (not (INST-excpt-detected-p (inst-of-tag rix MT))))
	     (equal (robe-val (nth-robe rix (MA-rob MA)))
		    (INST-dest-val (inst-of-tag rix MT)))))

(defthm robe-val-INST-dest-val-2
    (implies (and (inv MT MA)
		  (complete-stg-p (INST-stg i))
		  (INST-writeback-p i)
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-p i) (INST-in i MT)
		  (not (b1p (INST-modified? i)))
		  (not (b1p (inst-specultv? i)))
		  (not (INST-excpt-detected-p i)))
	     (equal (robe-val (nth-robe (INST-tag i) (MA-rob MA)))
		    (INST-dest-val i))))
)

(defthm robe-dest-INST-dest-reg-if-complete
    (implies (and (inv MT MA)
		  (complete-stg-p (INST-stg i))
		  (INST-writeback-p i)
		  (not (b1p (INST-modified? i)))
		  (not (b1p (inst-specultv? i)))
		  (not (INST-excpt-detected-P I))
		  (inst-p i) (INST-in i MT)
		  (MAETT-p MT) (MA-state-p MA))
	     (equal (robe-dest (nth-robe (INST-tag i) (MA-ROB MA)))
		    (INST-dest-reg i)))
  :Hints (("goal" :in-theory (e/d (INST-inv
				   complete-inst-inv
				   INST-EXCPT-DETECTED-P
				   complete-inst-robe-inv)
				  (INST-inv-if-inst-in))
		  :use ((:instance INST-inv-if-inst-in)))))

(defthm robe-dest-INST-dest-reg-if-complete-2
    (implies (and (inv MT MA)
		  (complete-stg-p (INST-stg (inst-of-tag rix MT)))
		  (INST-writeback-p (inst-of-tag rix MT))
		  (not (b1p (INST-modified? (inst-of-tag rix MT))))
		  (not (b1p (inst-specultv? (inst-of-tag rix MT))))
		  (not (INST-excpt-detected-P (inst-of-tag rix MT)))
		  (uniq-inst-of-tag rix MT)
		  (rob-index-p rix)
		  (MAETT-p MT) (MA-state-p MA))
	     (equal (robe-dest (nth-robe rix (MA-ROB MA)))
		    (INST-dest-reg (inst-of-tag rix MT))))
  :Hints (("goal" :in-theory (e/d () (robe-dest-INST-dest-reg-if-complete))
		  :use (:instance robe-dest-INST-dest-reg-if-complete
				  (i (inst-of-tag rix MT))))))

(defthm robe-val-INST-br-target-1
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (rob-index-p rix)
		  (uniq-inst-of-tag rix MT)
		  (b1p (INST-bu? (inst-of-tag rix MT)))
		  (not (b1p (inst-specultv? (inst-of-tag rix MT))))
		  (not (b1p (INST-modified? (inst-of-tag rix MT))))
		  (not (INST-fetch-error-detected-p (inst-of-tag rix MT))))
	     (equal (ROBE-val (nth-robe rix (MA-ROB MA)))
		    (INST-br-target (inst-of-tag rix MT))))
  :hints (("goal" :in-theory (e/d (INST-inv
				   INST-excpt-detected-p
				   INST-inv-def)
				  (INST-INV-INST-OF-TAG
				   INST-INV-IF-INST-IN))
		  :use (:instance INST-INV-INST-OF-TAG))))

(defthm robe-val-INST-br-target-2
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-in i MT) (INST-p i)
		  (dispatched-p i)
		  (not (committed-p i))
		  (b1p (INST-bu? i))
		  (not (b1p (inst-specultv? i)))
		  (not (b1p (INST-modified? i)))
		  (not (INST-fetch-error-detected-p i)))
	     (equal (ROBE-val (nth-robe (INST-tag i) (MA-ROB MA)))
		    (INST-br-target i)))
  :hints (("goal" :use (:instance robe-val-INST-br-target-1
				  (rix (INST-tag i))))))

(defthm INST-sync-if-INST-data-accs-error-detected
    (implies (and (INST-p i)
		  (INST-data-accs-error-detected-p i))
	     (equal (INST-sync? i) 0))
  :hints (("Goal" :in-theory (enable INST-sync? INST-data-accs-error-detected-p
				     INST-load-accs-error-detected-p
				     INST-store-accs-error-detected-p
				     INST-cntlv equal-b1p-converter
				     lift-b-ops decode logbit*
				     rdb))))

(encapsulate nil
(local
(defthm robe-sync-INST-sync-1-help
    (implies (and (MAETT-p MT)
		  (INST-inv (inst-of-tag rix MT) MA)
		  (MA-state-p MA)
		  (rob-index-p rix)
		  (uniq-inst-of-tag rix MT)
		  (not (INST-fetch-error-detected-p (inst-of-tag rix MT)))
		  (not (b1p (INST-modified? (inst-of-tag rix MT))))
		  (not (b1p (inst-specultv? (inst-of-tag rix MT)))))
	     (equal (robe-sync? (nth-robe rix (MA-rob MA)))
		    (INST-sync? (inst-of-tag rix MT))))
  :hints (("Goal" :In-theory (enable inst-inv-def)))))

(defthm robe-sync-INST-sync-1
    (implies (and (inv MT MA)
		  (MA-state-p MA)
		  (MAETT-p MT)
		  (rob-index-p rix)
		  (uniq-inst-of-tag rix MT)
		  (not (INST-fetch-error-detected-p (inst-of-tag rix MT)))
		  (not (b1p (INST-modified? (inst-of-tag rix MT))))
		  (not (b1p (inst-specultv? (inst-of-tag rix MT)))))
	     (equal (robe-sync? (nth-robe rix (MA-rob MA)))
		    (INST-sync? (inst-of-tag rix MT))))
  :hints (("Goal" :in-theory (enable exception-relations))))

(defthm robe-sync-INST-sync-2
    (implies (and (inv MT MA)
		  (MA-state-p MA)
		  (MAETT-p MT)
		  (INST-p i)
		  (INST-in i MT)
		  (not (b1p (INST-modified? i)))
		  (not (b1p (inst-specultv? i)))
		  (not (INST-fetch-error-detected-p i))
		  (dispatched-p i)
		  (not (committed-p i)))
	     (equal (robe-sync? (nth-robe (INST-tag i) (MA-rob MA)))
		    (INST-sync? i)))
  :hints (("Goal" :in-theory (enable exception-relations))))
)

(defthm robe-excpt-INST-excpt-flags-1
    (implies (and (inv MT MA)
		  (b1p (robe-complete? (nth-robe rix (MA-rob MA))))
		  (not (b1p (inst-specultv? (inst-of-tag rix MT))))
		  (not (b1p (INST-modified? (inst-of-tag rix MT))))
		  (MA-state-p MA)
		  (MAETT-p MT)
		  (rob-index-p rix)
		  (uniq-inst-of-tag rix MT))
	     (equal (robe-excpt (nth-robe rix (MA-rob MA)))
		    (INST-excpt-flags (inst-of-tag rix MT))))
  :hints (("goal" :use (:instance INST-inv-inst-of-tag)
		  :in-theory (e/d (inst-inv-def)
				  (INST-inv-inst-of-tag
				   INST-INV-IF-INST-IN)))))

(defthm robe-excpt-INST-excpt-flags-2
    (implies (and (inv MT MA)
		  (complete-stg-p (INST-stg i))
		  (not (b1p (inst-specultv? i)))
		  (not (b1p (INST-modified? i)))
		  (MA-state-p MA)
		  (INST-p i)
		  (MAETT-p MT)
		  (INST-in i MT))
	     (equal (robe-excpt (nth-robe (INST-tag i) (MA-rob MA)))
		    (INST-excpt-flags i))))

(defthm robe-wb-INST-wb-1
    (implies (and (inv MT MA)
		  (MA-state-p MA)
		  (MAETT-p MT)
		  (rob-index-p rix)
		  (uniq-inst-of-tag rix MT)
		  (not (INST-fetch-error-detected-p (inst-of-tag rix MT)))
		  (not (b1p (INST-modified? (inst-of-tag rix MT))))
		  (not (b1p (inst-specultv? (inst-of-tag rix MT)))))
	     (equal (robe-wb? (nth-robe rix (MA-rob MA)))
		    (INST-wb? (inst-of-tag rix MT))))
  :hints (("goal" :use (:instance INST-inv-inst-of-tag)
		  :in-theory (e/d (inst-inv-def)
				  (INST-inv-inst-of-tag
				   INST-INV-IF-INST-IN)))))

(defthm robe-wb-INST-wb-2
    (implies (and (inv MT MA)
		  (MA-state-p MA)
		  (INST-p i)
		  (MAETT-p MT)
		  (INST-in i MT)
		  (not (INST-fetch-error-detected-p i))
		  (not (b1p (INST-modified? i)))
		  (not (b1p (inst-specultv? i)))
		  (dispatched-p i)
		  (not (committed-p i)))
	     (equal (robe-wb? (nth-robe (INST-tag i) (MA-rob MA)))
		    (INST-wb? i))))

(defthm robe-wb-sreg-INST-wb-sreg-1
    (implies (and (inv MT MA)
		  (MA-state-p MA)
		  (MAETT-p MT)
		  (rob-index-p rix)
		  (uniq-inst-of-tag rix MT)
		  (not (INST-fetch-error-detected-p (inst-of-tag rix MT)))
		  (not (b1p (INST-modified? (inst-of-tag rix MT))))
		  (not (b1p (inst-specultv? (inst-of-tag rix MT)))))
	     (equal (robe-wb-sreg? (nth-robe rix (MA-rob MA)))
		    (INST-wb-sreg? (inst-of-tag rix MT))))
  :hints (("goal" :use (:instance INST-inv-inst-of-tag)
		  :in-theory (e/d (inst-inv-def)
				  (INST-inv-inst-of-tag
				   INST-INV-IF-INST-IN)))))

(defthm robe-wb-sreg-INST-cntlv-wb-sreg-2
    (implies (and (inv MT MA)
		  (MA-state-p MA)
		  (MAETT-p MT)
		  (INST-p i)
		  (INST-in i MT)
		  (not (INST-fetch-error-detected-p i))
		  (not (b1p (INST-modified? i)))
		  (not (b1p (inst-specultv? i)))
		  (dispatched-p i)
		  (not (committed-p i)))
	     (equal (robe-wb-sreg? (nth-robe (INST-tag i) (MA-rob MA)))
		    (INST-wb-sreg? i))))

(defthm INST-wb-if-INST-data-accs-error-detected
    (implies (and (INST-p i)
		  (INST-data-accs-error-detected-p i))
	     (equal (INST-rfeh? i) 0))
  :hints (("Goal" :in-theory (enable INST-rfeh? INST-data-accs-error-detected-p
				     INST-load-accs-error-detected-p
				     INST-store-accs-error-detected-p
				     INST-cntlv equal-b1p-converter
				     lift-b-ops decode logbit*
				     rdb))))


(defthm robe-rfeh-INST-rfeh-1
    (implies (and (inv MT MA)
		  (MA-state-p MA)
		  (MAETT-p MT)
		  (rob-index-p rix)
		  (uniq-inst-of-tag rix MT)
		  (not (INST-fetch-error-detected-p (inst-of-tag rix MT)))
		  (not (b1p (INST-modified? (inst-of-tag rix MT))))
		  (not (b1p (inst-specultv? (inst-of-tag rix MT)))))
	     (equal (robe-rfeh? (nth-robe rix (MA-rob MA)))
		    (INST-rfeh? (inst-of-tag rix MT))))
  :hints (("goal" :use ((:instance INST-inv-inst-of-tag)
			(:instance INST-is-at-one-of-the-stages
				   (i (inst-of-tag rix MT))))
		  :in-theory (e/d (INST-inv-opener
				   exception-relations
				   INST-excpt-detected-p)
				  (INST-inv-inst-of-tag
				   INST-INV-IF-INST-IN)))))

(defthm robe-rfeh-INST-rfeh-2
    (implies (and (inv MT MA)
		  (MA-state-p MA)
		  (MAETT-p MT)
		  (INST-p i)
		  (INST-in i MT)
		  (not (b1p (INST-modified? i)))
		  (not (b1p (inst-specultv? i)))
		  (not (INST-fetch-error-detected-p i))
		  (dispatched-p i)
		  (not (committed-p i)))
	     (equal (robe-rfeh? (nth-robe (INST-tag i) (MA-rob MA)))
		    (INST-rfeh? i))))

(defthm robe-br-predict-INST-br-predict-1
    (implies (and (inv MT MA)
		  (MA-state-p MA)
		  (MAETT-p MT)
		  (rob-index-p rix)
		  (uniq-inst-of-tag rix MT)
		  (not (INST-fetch-error-detected-p (inst-of-tag rix MT)))
		  (not (b1p (INST-modified? (inst-of-tag rix MT))))
		  (not (b1p (inst-specultv? (inst-of-tag rix MT)))))
	     (equal (robe-br-predict? (nth-robe rix (MA-rob MA)))
		    (INST-br-predict? (inst-of-tag rix MT))))
  :hints (("goal" :use (:instance INST-inv-inst-of-tag)
		  :in-theory (e/d (inst-inv-def)
				  (INST-inv-inst-of-tag
				   INST-INV-IF-INST-IN)))))

(defthm robe-br-predict-INST-br-predict-2
    (implies (and (inv MT MA)
		  (MA-state-p MA)
		  (MAETT-p MT)
		  (INST-p i)
		  (INST-in i MT)
		  (not (INST-fetch-error-detected-p i))
		  (not (b1p (INST-modified? i)))
		  (not (b1p (inst-specultv? i)))
		  (dispatched-p i)
		  (not (committed-p i)))
	     (equal (robe-br-predict? (nth-robe (INST-tag i) (MA-rob MA)))
		    (INST-br-predict? i))))

; The value in the INST-br-actual field
(defthm robe-br-predict-INST-br-actual-1
    (implies (and (inv MT MA)
		  (MA-state-p MA)
		  (MAETT-p MT)
		  (rob-index-p rix)
		  (uniq-inst-of-tag rix MT)
		  (b1p (inst-BU? (inst-of-tag rix MT)))
		  (complete-stg-p (INST-stg (inst-of-tag rix MT)))
		  (not (INST-fetch-error-detected-p (inst-of-tag rix MT)))
		  (not (b1p (INST-modified? (inst-of-tag rix MT))))
		  (not (b1p (inst-specultv? (inst-of-tag rix MT)))))
	     (equal (robe-br-actual? (nth-robe rix (MA-rob MA)))
		    (INST-branch-taken? (inst-of-tag rix MT))))
  :hints (("goal" :use (:instance INST-inv-inst-of-tag)
		  :in-theory (e/d (inst-inv-def)
				  (INST-inv-inst-of-tag
				   INST-INV-IF-INST-IN)))))

(defthm robe-br-predict-INST-br-actual-2
    (implies (and (inv MT MA)
		  (MA-state-p MA)
		  (MAETT-p MT)
		  (INST-p i)
		  (INST-in i MT)
		  (b1p (inst-BU? i))
		  (complete-stg-p (INST-stg i))
		  (not (INST-fetch-error-detected-p i))
		  (not (b1p (INST-modified? i)))
		  (not (b1p (inst-specultv? i)))
		  (or (execute-stg-p (INST-stg i))
		      (complete-stg-p (INST-stg i))))
	     (equal (robe-br-actual? (nth-robe (INST-tag i) (MA-rob MA)))
		    (INST-branch-taken? i))))

(defthm INST-branch-INST-sync-exclusive
    (implies (and (inv MT MA)
		  (MA-state-p MA)
		  (MAETT-p MT)
		  (rob-index-p rix)
		  (b1p (robe-valid? (nth-robe rix (MA-rob MA)))))
	     (not (and (b1p (INST-BU? (inst-of-tag rix MT)))
		       (b1p (INST-sync? (inst-of-tag rix MT))))))
  :hints (("Goal" :in-theory (enable INST-BU? INST-cntlv INST-sync?)))
  :rule-classes 
  ((:rewrite :corollary
    (implies (and (inv MT MA)
		  (MA-state-p MA)
		  (MAETT-p MT)
		  (rob-index-p rix)
		  (b1p (robe-valid? (nth-robe rix (MA-rob MA))))
		  (b1p (INST-BU? (inst-of-tag rix MT))))
	     (equal (INST-sync? (inst-of-tag rix MT)) 0))
    :hints (("goal" :in-theory (enable equal-b1p-converter lift-b-ops))))))

(defthm INST-sync-INST-BU-exclusive-2
    (implies (and (INST-p i) (b1p (INST-BU? i)))
	     (equal (INST-sync? i) 0))
  :hints (("goal" :in-theory (enable INST-sync? INST-BU? INST-cntlv))))

(encapsulate nil
(local
(defthm robe-branch-robe-sync-exclusive-help
    (implies (and (consistent-robe-p (nth-robe rix (MA-rob MA))
				     rix (MA-ROB MA))
		  (b1p (robe-valid? (nth-robe rix (MA-ROB MA))))
		  (b1p (robe-branch? (nth-robe rix (MA-ROB MA))))
		  (MA-state-p MA)
		  (rob-index-p rix))
	     (equal (robe-sync? (nth-robe rix (MA-ROB MA))) 0))
  :hints (("goal" :in-theory (enable consistent-robe-p
				     lift-b-ops equal-b1p-converter)))))

; Robe-branch? and robe-sync? field of an ROB entry are not 1 simultaneously. 
(defthm robe-branch-robe-sync-exclusive
    (implies (and (inv MT MA)
		  (b1p (robe-valid? (nth-robe rix (MA-ROB MA))))
		  (b1p (robe-branch? (nth-robe rix (MA-ROB MA))))
		  (rob-index-p rix)
		  (MAETT-p MT) (MA-state-p MA))
	     (equal (robe-sync? (nth-robe rix (MA-ROB MA))) 0))
  :hints (("goal" :use (:instance robe-branch-robe-sync-exclusive-help))))
)

(encapsulate nil
(local
(defthm robe-wb-robe-sync-exclusive-help
    (implies (and (consistent-robe-p (nth-robe rix (MA-rob MA))
				     rix (MA-ROB MA))
		  (b1p (robe-valid? (nth-robe rix (MA-ROB MA))))
		  (b1p (robe-wb? (nth-robe rix (MA-ROB MA))))
		  (MA-state-p MA)
		  (rob-index-p rix))
	     (equal (robe-sync? (nth-robe rix (MA-ROB MA))) 0))
  :hints (("goal" :in-theory (enable consistent-robe-p
				     lift-b-ops equal-b1p-converter)))))

; Robe-wb? and robe-sync? field of an ROB entry are not 1 simultaneously. 
(defthm robe-wb-robe-sync-exclusive
    (implies (and (inv MT MA)
		  (b1p (robe-valid? (nth-robe rix (MA-ROB MA))))
		  (b1p (robe-wb? (nth-robe rix (MA-ROB MA))))
		  (rob-index-p rix)
		  (MAETT-p MT) (MA-state-p MA))
	     (equal (robe-sync? (nth-robe rix (MA-ROB MA))) 0))
  :hints (("goal" :use (:instance robe-wb-robe-sync-exclusive-help)
		  :in-theory (e/d (equal-b1p-converter lift-b-ops)
				  (robe-wb-robe-sync-exclusive-help)))))
)

; Robe-pc field of an ROB entry to which instruction i is assigned contains
; the pc value for i.
(defthm robe-pc-INST-tag
    (implies (and (inv MT MA)
		  (dispatched-p i)
		  (not (committed-p i))
		  (not (b1p (INST-modified? i)))
		  (not (b1p (inst-specultv? i)))
		  (inst-p i) (INST-in i MT)
		  (MAETT-p MT) (MA-state-p MA))
	     (equal (robe-pc (nth-robe (INST-tag i) (MA-ROB MA)))
		    (INST-pc i)))
  :Hints (("goal" :in-theory (e/d (INST-inv inst-inv-def
				   committed-p dispatched-p
						   INST-pc)
				  (INST-inv-if-inst-in))
		  :use ((:instance INST-inv-if-inst-in)
			(:instance INST-is-at-one-of-the-stages)))))

(defthm robe-pc-INST-tag-2
    (implies (and (inv MT MA)
		  (uniq-inst-of-tag rix MT)
		  (rob-index-p rix)
		  (not (b1p (INST-modified? (inst-of-tag rix MT))))
		  (not (b1p (inst-specultv? (inst-of-tag rix MT))))
		  (MAETT-p MT) (MA-state-p MA))
	     (equal (robe-pc (nth-robe rix (MA-ROB MA)))
		    (INST-pc (inst-of-tag rix MT))))
  :Hints (("goal" :use (:instance robe-pc-INST-tag
				  (i (inst-of-tag rix MT))))))

; Field robe-dest of an ROB entry contains the index to the destination
; register of the corresponding instruction.
(defthm robe-dest-INST-dest-reg
    (implies (and (inv MT MA)
		  (INST-writeback-p i)
		  (dispatched-p i)
		  (not (committed-p i))
		  (not (b1p (INST-modified? i)))
		  (not (b1p (inst-specultv? i)))
		  (not (INST-fetch-error-detected-P I))
		  (inst-p i) (INST-in i MT)
		  (MAETT-p MT) (MA-state-p MA))
	     (equal (robe-dest (nth-robe (INST-tag i) (MA-ROB MA)))
		    (INST-dest-reg i)))
  :Hints (("goal" :in-theory (e/d (INST-inv
				   complete-inst-inv
				   complete-inst-robe-inv
				   execute-inst-inv
				   execute-inst-robe-inv
				   committed-p dispatched-p)
				  (INST-inv-if-inst-in))
		  :use ((:instance INST-inv-if-inst-in)
			(:instance INST-is-at-one-of-the-stages)))))

(defthm robe-dest-INST-dest-reg-2
    (implies (and (inv MT MA)
		  (INST-writeback-p (inst-of-tag rix MT))
		  (not (b1p (INST-modified? (inst-of-tag rix MT))))
		  (not (b1p (inst-specultv? (inst-of-tag rix MT))))
		  (not (INST-fetch-error-detected-P (inst-of-tag rix MT)))
		  (uniq-inst-of-tag rix MT)
		  (rob-index-p rix)
		  (MAETT-p MT) (MA-state-p MA))
	     (equal (robe-dest (nth-robe rix (MA-ROB MA)))
		    (INST-dest-reg (inst-of-tag rix MT))))
  :hints (("goal" :in-theory (disable robe-dest-INST-dest-reg)
		  :use (:instance robe-dest-INST-dest-reg
				  (i (inst-of-tag rix MT))))))

(defthm robe-branch-nth-robe-if-inst-fetch-error
    (implies (and (inv MT MA)
		  (dispatched-p i)
		  (not (committed-p i))
		  (not (b1p (INST-modified? i)))
		  (not (b1p (inst-specultv? i)))
		  (INST-FETCH-ERROR-DETECTED-P I)
		  (inst-p i) (INST-in i MT)
		  (MAETT-p MT) (MA-state-p MA))
	     (equal (robe-branch? (nth-robe (INST-tag i) (MA-ROB MA))) 0))
  :Hints (("goal" :in-theory (e/d (INST-inv
				   complete-inst-inv
				   complete-inst-robe-inv
				   execute-inst-inv
				   execute-inst-robe-inv
				   committed-p dispatched-p
				   INST-dest-reg)
				  (INST-inv-if-inst-in))
		  :use ((:instance INST-inv-if-inst-in)
			(:instance INST-is-at-one-of-the-stages)))))

(defthm robe-sync-nth-robe-if-inst-fetch-error
    (implies (and (inv MT MA)
		  (dispatched-p i)
		  (not (committed-p i))
		  (not (b1p (INST-modified? i)))
		  (not (b1p (inst-specultv? i)))
		  (INST-FETCH-ERROR-DETECTED-P I)
		  (inst-p i) (INST-in i MT)
		  (MAETT-p MT) (MA-state-p MA))
	     (equal (robe-sync? (nth-robe (INST-tag i) (MA-ROB MA))) 0))
  :Hints (("goal" :in-theory (e/d (INST-inv
				   complete-inst-inv
				   complete-inst-robe-inv
				   execute-inst-inv
				   execute-inst-robe-inv
				   committed-p dispatched-p
				   INST-dest-reg)
				  (INST-inv-if-inst-in))
		  :use ((:instance INST-inv-if-inst-in)
			(:instance INST-is-at-one-of-the-stages)))))

(defthm robe-rfeh-nth-robe-if-inst-fetch-error
    (implies (and (inv MT MA)
		  (dispatched-p i)
		  (not (committed-p i))
		  (not (b1p (INST-modified? i)))
		  (not (b1p (inst-specultv? i)))
		  (INST-FETCH-ERROR-DETECTED-P I)
		  (inst-p i) (INST-in i MT)
		  (MAETT-p MT) (MA-state-p MA))
	     (equal (robe-rfeh? (nth-robe (INST-tag i) (MA-ROB MA))) 0))
  :Hints (("goal" :in-theory (e/d (INST-inv
				   complete-inst-inv
				   complete-inst-robe-inv
				   execute-inst-inv
				   execute-inst-robe-inv
				   committed-p dispatched-p
				   INST-dest-reg)
				  (INST-inv-if-inst-in))
		  :use ((:instance INST-inv-if-inst-in)
			(:instance INST-is-at-one-of-the-stages)))))

(defthm robe-rfeh-nth-robe-if-inst-fetch-error-2
    (implies (and (inv MT MA)
		  (uniq-inst-of-tag rix MT)
		  (INST-FETCH-ERROR-DETECTED-P (inst-of-tag rix MT))
		  (not (b1p (INST-modified? (inst-of-tag rix MT))))
		  (not (b1p (inst-specultv? (inst-of-tag rix MT))))
		  (rob-index-p rix)
		  (MAETT-p MT) (MA-state-p MA))
	     (equal (robe-rfeh? (nth-robe rix (MA-ROB MA))) 0))
  :Hints (("goal" :use (:instance robe-rfeh-nth-robe-if-inst-fetch-error
				  (i (inst-of-tag rix MT))))))

(defthm robe-excpt-nth-robe-if-fetch-or-decode-error
    (implies (and (inv MT MA)
		  (dispatched-p i)
		  (not (committed-p i))
		  (not (b1p (INST-modified? i)))
		  (not (b1p (inst-specultv? i)))
		  (or (b1p (inst-fetch-error? i))
		      (b1p (inst-decode-error? i)))
		  (inst-p i) (INST-in i MT)
		  (MAETT-p MT) (MA-state-p MA))
	     (equal (robe-excpt (nth-robe (INST-tag i) (MA-ROB MA)))
		    (INST-excpt-flags i)))
  :Hints (("goal" :in-theory (e/d (INST-inv
				   complete-inst-inv
				   complete-inst-robe-inv
				   execute-inst-inv
				   execute-inst-robe-inv
				   committed-p dispatched-p
				   INST-dest-reg)
				  (INST-inv-if-inst-in))
		  :use ((:instance INST-inv-if-inst-in)
			(:instance INST-is-at-one-of-the-stages)))))

;;; Lemmas to relate inst-of-tag and INST-at-stg
(defthm uniq-inst-of-tag-if-IU-RS0-valid
    (implies (and (inv MT MA)
		  (b1p (RS-valid? (IU-RS0 (MA-IU MA))))
		  (MA-state-p MA) (MAETT-p MT))
	     (uniq-inst-of-tag (RS-tag (IU-RS0 (MA-IU MA))) MT))
  :hints (("goal" :in-theory (enable IU-RS-field-INST-at-lemmas))))

(defthm inst-of-tag-IU-RS0-tag-INST-at-stg-IU-RS0
    (implies (and (inv MT MA)
		  (b1p (RS-valid? (IU-RS0 (MA-IU MA))))
		  (MA-state-p MA) (MAETT-p MT))
	     (equal (inst-of-tag (RS-tag (IU-RS0 (MA-IU MA))) MT)
		    (INST-at-stg '(IU RS0) MT)))
  :hints (("goal" :in-theory (enable IU-RS-field-INST-at-lemmas))))

(defthm uniq-inst-of-tag-if-IU-RS1-valid
    (implies (and (inv MT MA)
		  (b1p (RS-valid? (IU-RS1 (MA-IU MA))))
		  (MA-state-p MA) (MAETT-p MT))
	     (uniq-inst-of-tag (RS-tag (IU-RS1 (MA-IU MA))) MT))
  :hints (("goal" :in-theory (enable IU-RS-field-INST-at-lemmas))))
				     

(defthm inst-of-tag-IU-RS-tag-INST-at-stg-IU-RS1
    (implies (and (inv MT MA)
		  (b1p (RS-valid? (IU-RS1 (MA-IU MA))))
		  (MA-state-p MA) (MAETT-p MT))
	     (equal (inst-of-tag (RS-tag (IU-RS1 (MA-IU MA))) MT)
		    (INST-at-stg '(IU RS1) MT)))
  :hints (("goal" :in-theory (enable IU-RS-field-INST-at-lemmas))))

(defthm uniq-inst-of-tag-if-BU-RS0-valid
    (implies (and (inv MT MA)
		  (b1p (BU-RS-valid? (BU-RS0 (MA-BU MA))))
		  (MA-state-p MA) (MAETT-p MT))
	     (uniq-inst-of-tag (BU-RS-tag (BU-RS0 (MA-BU MA))) MT))
  :hints (("goal" :in-theory (enable BU-RS-field-inst-at-lemmas))))

(defthm uniq-inst-of-tag-if-BU-RS1-valid
    (implies (and (inv MT MA)
		  (b1p (BU-RS-valid? (BU-RS1 (MA-BU MA))))
		  (MA-state-p MA) (MAETT-p MT))
	     (uniq-inst-of-tag (BU-RS-tag (BU-RS1 (MA-BU MA))) MT))
  :hints (("goal" :in-theory (enable BU-RS-field-inst-at-lemmas))))

;;; definition and lemmas about tag-in-order
(defun tag-in-order (rix1 rix2 MT)
  (if (b1p (MT-rob-flg MT))
      (or (and (<= (MT-rob-head MT) rix1)
	       (< rix2 (MT-rob-tail MT)))
	  (and (<= (MT-rob-head MT) rix1) (< rix1 rix2))
	  (and (< rix1 rix2) (< rix2 (MT-rob-tail MT))))
      (< rix1 rix2)))
(in-theory (disable tag-in-order))

;;;;;  End of Lemmas about ROB and INST ;;;;;

;;;;;  Instruction Specific properties about INST fields
; Relations between INST-wrong-branch? and INST-BU?
(defthm not-INST-wrong-branch-if-not-INST-BU
    (implies (and (INST-p I) (not (b1p (INST-BU? i))))
	     (not (b1p (INST-wrong-branch? i))))
  :hints (("goal" :in-theory (enable INST-wrong-branch?
				     bv-eqv-iff-equal
				     INST-opcode
				     INST-cntlv decode
				     rdb logbit*
				     INST-BU? lift-b-ops))))

(defthm INST-sync-if-INST-rfeh
    (implies (and (INST-p i) (b1p (INST-rfeh? i)))
	     (equal (INST-sync? i) 1))
  :hints (("goal" :in-theory (enable INST-sync? INST-rfeh? decode
				     INST-cntlv logbit* rdb))))

(defthm INST-sync-opcode-5-8
    (implies (INST-p i)
	     (iff (b1p (INST-sync? i))
		  (or (equal (INST-opcode i) 5)
		      (equal (INST-opcode i) 8))))
  :hints (("goal" :in-theory (enable INST-sync? RDB logbit* decode INST-opcode
				     INST-cntlv lift-b-ops)))
  :rule-classes nil)

;; INST-sync? field for a load store instruction.
(defthm not-INST-sync-if-INST-LSU?
    (implies (and (INST-p i) (b1p (INST-LSU? i)))
	     (equal (INST-sync? i) 0))
  :hints (("Goal" :in-theory (enable INST-LSU? INST-cntlv decode
				     lift-b-ops equal-b1p-converter
				     INST-sync?
				     logbit* rdb))))

;; INST-rfeh field for a load store instruction.
(defthm not-INST-rfeh-if-INST-LSU?
    (implies (and (INST-p i) (b1p (INST-LSU? i)))
	     (equal (INST-rfeh? i) 0))
  :hints (("Goal" :in-theory (enable INST-LSU? INST-cntlv decode
				     lift-b-ops equal-b1p-converter
				     INST-rfeh? logbit* rdb))))

;; INST-wb field for a store instruction
(defthm not-INST-wb-if-INST-store?
    (implies (and (INST-p i) (b1p (INST-store? i)))
	     (equal (INST-wb? i) 0))
  :hints (("Goal" :in-theory (enable INST-store? INST-cntlv decode
				     lift-b-ops equal-b1p-converter
				     INST-LSU? INST-ld-st?
				     INST-wb? logbit* rdb))))

;; INST-wb-sreg field for a load store instruction
(defthm not-INST-wb-sreg-if-INST-LSU?
    (implies (and (INST-p i) (b1p (INST-LSU? i)))
	     (equal (INST-wb-sreg? i) 0))
  :hints (("Goal" :in-theory (enable INST-LSU? INST-cntlv decode
				     lift-b-ops equal-b1p-converter
				     INST-wb-sreg? logbit* rdb))))

(deflabel begin-opcode-inst-type)
(defthm INST-IU-opcode-0
    (implies (and (INST-p i) (equal (INST-opcode i) 0))
	     (equal (INST-IU? i) 1))
  :hints (("goal" :in-theory (enable INST-IU? INST-cntlv decode
				     logbit* rdb))))

(defthm INST-MU-opcode-1
    (implies (and (INST-p i) (equal (INST-opcode i) 1))
	     (equal (INST-MU? i) 1))
  :hints (("goal" :in-theory (enable INST-MU? INST-cntlv decode
				     logbit* rdb))))

(defthm INST-BU-opcode-2
    (implies (and (INST-p i) (equal (INST-opcode i) 2))
	     (equal (INST-BU? i) 1))
  :hints (("goal" :in-theory (enable INST-BU? INST-cntlv decode
				     logbit* rdb))))

(defthm INST-load-opcode-3
    (implies (and (INST-p i) (equal (INST-opcode i) 3))
	     (equal (INST-load? i) 1))
  :hints (("goal" :in-theory (enable INST-load? INST-cntlv decode
				     INST-LSU? INST-LD-ST?
				     logbit* rdb))))
(defthm INST-store-opcode-4
    (implies (and (INST-p i) (equal (INST-opcode i) 4))
	     (equal (INST-store? i) 1))
  :hints (("goal" :in-theory (enable INST-store? INST-cntlv decode
				     INST-LSU? INST-LD-ST?
				     logbit* rdb))))

(defthm INST-load-opcode-6
    (implies (and (INST-p i) (equal (INST-opcode i) 6))
	     (equal (INST-load? i) 1))
  :hints (("goal" :in-theory (enable INST-load? INST-cntlv decode
				     INST-LSU? INST-LD-ST?
				     logbit* rdb))))

(defthm INST-store-opcode-7
    (implies (and (INST-p i) (equal (INST-opcode i) 7))
	     (equal (INST-store? i) 1))
  :hints (("goal" :in-theory (enable INST-store? INST-cntlv decode
				     INST-LSU? INST-LD-ST?
				     logbit* rdb))))
    
(deflabel end-opcode-inst-type)
(deftheory opcode-inst-type
    (set-difference-theories
     (universal-theory 'end-opcode-inst-type)
     (universal-theory 'begin-opcode-inst-type)))

(in-theory (disable opcode-inst-type))     

(defthm opcodes-at-IU-stg-p
    (implies (and (inv MT MA)
		  (IU-stg-p (INST-stg i))
		  (INST-in i MT) (INST-p i)
		  (MAETT-p MT) (MA-state-p MA)
		  (not (b1p (inst-specultv? i)))
		  (not (b1p (INST-modified? i))))
	     (or (equal (INST-opcode i) 0)
		 (equal (INST-opcode i) 9)
		 (equal (INST-opcode i) 10)))
  :hints (("goal" :in-theory (e/d (equal-b1p-converter
				   decode rdb logbit* lift-b-ops
				   INST-IU? inst-cntlv)
				  (INST-IU-IF-IU-STG-P ))
		  :use (:instance INST-IU-IF-IU-STG-P)))
  :rule-classes nil)

(defthm opcode-2-at-BU-stg-p
    (implies (and (inv MT MA)
		  (BU-stg-p (INST-stg i))
		  (INST-in i MT) (INST-p i)
		  (MAETT-p MT) (MA-state-p MA)
		  (not (b1p (inst-specultv? i)))
		  (not (b1p (INST-modified? i))))
	     (equal (INST-opcode i) 2))
  :hints (("goal" :in-theory (e/d (equal-b1p-converter
				   decode rdb logbit* lift-b-ops
				   INST-BU? inst-cntlv)
				  (INST-BU-IF-BU-STG-P ))
		  :use (:instance INST-BU-IF-BU-STG-P)))
  :rule-classes nil)

(defthm opcode-1-at-MU-stg-p
    (implies (and (inv MT MA)
		  (MU-stg-p (INST-stg i))
		  (INST-in i MT) (INST-p i)
		  (MAETT-p MT) (MA-state-p MA)
		  (not (b1p (inst-specultv? i)))
		  (not (b1p (INST-modified? i))))
	     (equal (INST-opcode i) 1))
  :hints (("goal" :in-theory (e/d (equal-b1p-converter
				   decode rdb logbit* lift-b-ops
				   INST-MU? inst-cntlv)
				  (INST-MU-IF-MU-STG-P ))
		  :use (:instance INST-MU-IF-MU-STG-P)))
  :rule-classes nil)

(defthm opcodes-at-LSU-stg-p
    (implies (and (inv MT MA)
		  (LSU-stg-p (INST-stg i))
		  (INST-in i MT) (INST-p i)
		  (MAETT-p MT) (MA-state-p MA)
		  (not (b1p (inst-specultv? i)))
		  (not (b1p (INST-modified? i))))
	     (or (equal (INST-opcode i) 3)
		 (equal (INST-opcode i) 4)
		 (equal (INST-opcode i) 6)
		 (equal (INST-opcode i) 7)))
  :hints (("goal" :in-theory (e/d (equal-b1p-converter
				   decode rdb logbit* lift-b-ops
				   INST-LSU? inst-cntlv)
				  (INST-LSU-IF-LSU-STG-P ))
		  :use (:instance INST-LSU-IF-LSU-STG-P)))
  :rule-classes nil)

(defthm INST-type-exclusive
    (and (implies (and (INST-p i) (b1p (INST-LSU? i)))
		  (equal (INST-no-unit? i) 0))
	 (implies (and (INST-p i) (b1p (INST-BU? i)))
		  (equal (INST-no-unit? i) 0))
	 (implies (and (INST-p i) (b1p (INST-MU? i)))
		  (equal (INST-no-unit? i) 0))
	 (implies (and (INST-p i) (b1p (INST-IU? i)))
		  (equal (INST-no-unit? i) 0))
	 (implies (and (INST-p i) (b1p (INST-LSU? i)))
		  (equal (INST-IU? i) 0))
	 (implies (and (INST-p i) (b1p (INST-BU? i)))
		  (equal (INST-IU? i) 0))
	 (implies (and (INST-p i) (b1p (INST-MU? i)))
		  (equal (INST-IU? i) 0))
	 (implies (and (INST-p i) (b1p (INST-LSU? i)))
		  (equal (INST-MU? i) 0))
	 (implies (and (INST-p i) (b1p (INST-BU? i)))
		  (equal (INST-MU? i) 0))
	 (implies (and (INST-p i) (b1p (INST-LSU? i)))
		  (equal (INST-BU? i) 0)))
  :hints (("goal" :in-theory (enable INST-LSU? INST-no-unit?
				     INST-MU? INST-IU? INST-BU?
				     INST-cntlv
				     equal-b1p-converter lift-b-ops))))

(defthm INST-type-exclusive-2
    (and (implies (and (INST-p i) (b1p (INST-LSU? i)))
		  (not (b1p (INST-no-unit? i))))
	 (implies (and (INST-p i) (b1p (INST-BU? i)))
		  (not (b1p (INST-no-unit? i))))
	 (implies (and (INST-p i) (b1p (INST-MU? i)))
		  (not (b1p (INST-no-unit? i))))
	 (implies (and (INST-p i) (b1p (INST-IU? i)))
		  (not (b1p (INST-no-unit? i))))
	 (implies (and (INST-p i) (b1p (INST-no-unit? i)))
		  (not (b1p (INST-IU? i))))
	 (implies (and (INST-p i) (b1p (INST-LSU? i)))
		  (not (b1p (INST-IU? i))))
	 (implies (and (INST-p i) (b1p (INST-BU? i)))
		  (not (b1p (INST-IU? i))))
	 (implies (and (INST-p i) (b1p (INST-MU? i)))
		  (not (b1p (INST-IU? i))))
	 (implies (and (INST-p i) (b1p (INST-no-unit? i)))
		  (not (b1p (INST-MU? i))))
	 (implies (and (INST-p i) (b1p (INST-IU? i)))
		  (not (b1p (INST-MU? i))))
	 (implies (and (INST-p i) (b1p (INST-LSU? i)))
		  (not (b1p (INST-MU? i))))
	 (implies (and (INST-p i) (b1p (INST-BU? i)))
		  (not (b1p (INST-MU? i))))
	 (implies (and (INST-p i) (b1p (INST-no-unit? i)))
		  (not (b1p (INST-BU? i))))
	 (implies (and (INST-p i) (b1p (INST-IU? i)))
		  (not (b1p (INST-BU? i))))
	 (implies (and (INST-p i) (b1p (INST-MU? i)))
		  (not (b1p (INST-BU? i))))
	 (implies (and (INST-p i) (b1p (INST-LSU? i)))
		  (not (b1p (INST-BU? i))))
	 (implies (and (INST-p i) (b1p (INST-no-unit? i)))
		  (not (b1p (INST-LSU? i))))
	 (implies (and (INST-p i) (b1p (INST-IU? i)))
		  (not (b1p (INST-LSU? i))))
	 (implies (and (INST-p i) (b1p (INST-MU? i)))
		  (not (b1p (INST-LSU? i))))
	 (implies (and (INST-p i) (b1p (INST-BU? i)))
		  (not (b1p (INST-LSU? i))))))

(in-theory (disable INST-type-exclusive))

(defthm INST-store-INST-sync-exclusive
    (implies (and (INST-p i) (b1p (INST-sync? i)))
	     (equal (INST-store? i) 0))
  :hints (("goal" :in-theory (enable INST-sync? INST-store?
				     INST-LSU? lift-b-ops equal-b1p-converter
				     INST-cntlv decode logbit* rdb))))

(defthm INST-store-INST-rfeh-exclusive
    (implies (and (INST-p i) (b1p (INST-rfeh? i)))
	     (equal (INST-store? i) 0))
  :hints (("goal" :in-theory (enable INST-rfeh? INST-store?
				     INST-LSU? lift-b-ops equal-b1p-converter
				     INST-cntlv decode logbit* rdb))))

(defthm INST-load-INST-store-exclusive
    (and (implies (b1p (INST-store? i)) (not (b1p (INST-load? i))))
	 (implies (b1p (INST-load? i)) (not (b1p (INST-store? i)))))
  :hints (("goal" :in-theory (enable INST-load? INST-store? lift-b-ops))))

(encapsulate nil 
(local 
(defthm not-INST-sync-if-at-complete-wbuf-help
    (implies (and (INST-p i)
		  (MA-state-p MA)
		  (INST-inv i MA)
		  (not (b1p (INST-modified? i)))
		  (not (b1p (inst-specultv? i)))
		  (wbuf-stg-p (INST-stg i)))
	     (equal (INST-sync? i) 0))
  :hints (("goal" :in-theory (enable inst-inv-def wbuf-stg-p)))))

; INST-sync? for the instruction at write buffer.
(defthm not-INST-sync-if-at-complete-wbuf
    (implies (and (inv MT MA)
		  (INST-in i MT)
		  (MAETT-p MT)
		  (INST-p i)
		  (not (b1p (INST-modified? i)))
		  (not (b1p (inst-specultv? i)))
		  (MA-state-p MA)
		  (wbuf-stg-p (INST-stg i)))
	     (equal (INST-sync? i) 0)))
) ;encapsulate

(encapsulate nil
(local 
(defthm not-INST-rfeh-if-at-complete-wbuf-help
    (implies (and (INST-p i)
		  (MA-state-p MA)
		  (INST-inv i MA)
		  (not (b1p (INST-modified? i)))
		  (not (b1p (inst-specultv? i)))
		  (wbuf-stg-p (INST-stg i)))
	     (equal (INST-rfeh? i) 0))
  :hints (("Goal" :in-theory (enable wbuf-stg-p inst-inv-def)))))

;  INST-rfeh field for an instruction in the write buffer.
(defthm not-INST-rfeh-if-at-complete-wbuf
    (implies (and (inv MT MA)
		  (INST-p i)
		  (MAETT-p MT)
		  (MA-state-p MA)
		  (not (b1p (INST-modified? i)))
		  (not (b1p (inst-specultv? i)))
		  (INST-in i MT)
		  (wbuf-stg-p (INST-stg i)))
	     (equal (INST-rfeh? i) 0)))
)  ;encapsulate

(encapsulate nil
(local
(defthm not-INST-wb-if-at-complete-wbuf-help
    (implies (and (INST-p i)
		  (MA-state-p MA)
		  (INST-inv i MA)
		  (not (b1p (INST-modified? i)))
		  (not (b1p (inst-specultv? i)))
		  (wbuf-stg-p (INST-stg i)))
	     (equal (INST-wb? i) 0))
  :hints (("goal" :in-theory (enable wbuf-stg-p inst-inv-def)))))

; INST-wb field for an instruction in the write buffer.
(defthm not-INST-wb-if-at-complete-wbuf
    (implies (and (inv MT MA)
		  (INST-in i MT)
		  (MAETT-p MT)
		  (MA-state-p MA)
		  (not (b1p (INST-modified? i)))
		  (not (b1p (inst-specultv? i)))
		  (INST-p i)
		  (wbuf-stg-p (INST-stg i)))
	     (equal (INST-wb? i) 0)))
)

(encapsulate nil
(local
(defthm not-INST-wb-sreg-if-at-complete-wbuf-help
    (implies (and (INST-p i)
		  (MA-state-p MA)
		  (INST-inv i MA)
		  (not (b1p (INST-modified? i)))
		  (not (b1p (inst-specultv? i)))
		  (wbuf-stg-p (INST-stg i)))
	     (equal (INST-wb-sreg? i) 0))
  :hints (("Goal" :in-theory (enable inst-inv-def wbuf-stg-p)))))

; INST-wb-sreg for an instruction in a write buffer.
(defthm not-INST-wb-sreg-if-at-complete-wbuf
    (implies (and (inv MT MA)
		  (INST-in i MT)
		  (INST-p i)
		  (MAETT-p MT)
		  (MA-state-p MA)
		  (not (b1p (INST-modified? i)))
		  (not (b1p (inst-specultv? i)))
		  (wbuf-stg-p (INST-stg i)))
	     (equal (INST-wb-sreg? i) 0)))
)

(encapsulate nil
(local
(defthm not-INST-branch-if-at-complete-wbuf-help
    (implies (and (INST-p i)
		  (MA-state-p MA)
		  (INST-inv i MA)
		  (not (b1p (INST-modified? i)))
		  (not (b1p (inst-specultv? i)))
		  (wbuf-stg-p (INST-stg i)))
	     (equal (INST-BU? i) 0))
  :hints (("Goal" :in-theory (enable wbuf-stg-p inst-inv-def
				     equal-b1p-converter)))))

;  INST-branch field for an instruction in a write buffer.
(defthm not-INST-branch-if-at-complete-wbuf
    (implies (and (inv MT MA)
		  (INST-in i MT)
		  (MA-state-p MA)
		  (MAETT-p MT)
		  (not (b1p (INST-modified? i)))
		  (not (b1p (inst-specultv? i)))
		  (INST-p i)
		  (wbuf-stg-p (INST-stg i)))
	     (equal (INST-BU? i) 0)))
)

(defthm INST-writeback-p-INST-BU-exclusive
    (implies (and (INST-p i) (b1p (INST-BU? I)))
	     (not (INST-writeback-p i)))
  :hints (("goal" :in-theory (enable INST-writeback-p INST-BU?
				     inst-cntlv INST-opcode))))

;;;;; Relations about INST predicates such as INST-cause-jmp, INST-exintr-now
;;;;; INST-start-specultv?
(defthm not-INST-cause-jmp-if-not-flush-all
    (implies (not (b1p (flush-all? MA sigs)))
	     (equal (INST-cause-jmp? i MT MA sigs) 0))
  :hints (("goal" :in-theory (enable INST-cause-jmp? flush-all?
				     equal-b1p-converter
				     lift-b-ops))))

(defthm not-INST-exintr-now-if-not-flush-all
    (implies (not (b1p (flush-all? MA sigs)))
	     (equal (INST-exintr-now? i MA sigs) 0))
  :hints (("goal" :in-theory (enable INST-exintr-now? flush-all?
				     equal-b1p-converter ex-intr?
				     lift-b-ops))))

(defthm not-INST-exintr-now-if-not-fetch-inst
    (implies (b1p (fetch-inst? MA sigs))
	     (equal (INST-exintr-now? i MA sigs) 0))
  :hints (("goal" :in-theory (enable lift-b-ops fetch-inst?))))

(defthm not-INST-cause-jmp-if-not-fetch-inst
    (implies (b1p (fetch-inst? MA sigs))
	     (equal (INST-cause-jmp? i MT MA sigs) 0))
  :hints (("goal" :in-theory (enable lift-b-ops fetch-inst?))))

(defthm not-execute-stg-p-if-ex-intr
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-p i)
		  (INST-in i MT)
		  (b1p (ex-intr? MA sigs)))
	     (not (execute-stg-p (INST-stg i))))
  :hints (("Goal" :in-theory (enable ex-intr? lift-b-ops))))

(defthm not-complete-stg-p-if-ex-intr
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-p i)
		  (INST-in i MT)
		  (b1p (ex-intr? MA sigs)))
	     (not (complete-stg-p (INST-stg i))))
    :hints (("Goal" :in-theory (enable ex-intr? lift-b-ops))))

(defthm inst-exintr-now-if-ex-intr
    (implies (and (b1p (ex-intr? MA sigs))
		  (or (IFU-stg-p (INST-stg I))
		      (DQ-stg-p (INST-stg I))))
	     (equal (INST-exintr-now? i MA sigs) 1))
  :hints (("Goal" :in-theory (enable inst-exintr-now? equal-b1p-converter
				     ex-intr?
				     lift-b-ops)))
  :rule-classes
  ((:rewrite)
   (:rewrite :corollary
	     (implies (and (b1p (ex-intr? MA sigs))
			   (not (dispatched-p i))
			   (INST-p i))
		      (equal (INST-exintr-now? i MA sigs) 1))
	     :hints (("goal" :in-theory (enable dispatched-p))))))

(defthm INST-exintr-now-if-ex-intr-if-not-commit
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i)
		  (not (committed-p i))
		  (b1p (ex-intr? MA sigs))
		  (MAETT-p MT) (MA-state-p MA))
	     (equal (INST-exintr-now? i MA sigs) 1))
  :hints (("goal" :use (:instance inst-is-at-one-of-the-stages)
		  :in-theory (disable inst-is-at-one-of-the-stages))))

(defthm not-INST-exintr-now-if-commit-inst?
    (implies (and (inv MT MA)
		  (MA-state-p MA)
		  (MAETT-p MT)
		  (b1p (commit-inst? MA)))
	     (equal (INST-exintr-now? i MA sigs) 0))
  :hints (("Goal" :in-theory (enable commit-inst? INST-exintr-now?
				     lift-b-ops equal-b1p-converter))))

; INST-exintr-now? is true for an instruction only if 
; an external interrupt signal is set or the external interrupt flag
; has been set.
(defthm INST-exintr-now-when-no-exintr-flag
    (implies (and (MA-state-p MA)
		  (MA-input-p sigs)
		  (not (b1p (MA-input-exintr sigs)))
		  (not (b1p (exintr-flag? MA))))
	     (not (b1p (INST-exintr-now? i MA sigs))))
  :hints (("Goal" :in-theory (enable INST-exintr-now? lift-b-ops
				     exintr-flag?))))

; The external interrupt is not asserted if there is an instruction in
; the execution or complete stage.
(defthm not-ex-intr-if-INST-at-execute-or-complete-stg
    (implies (and (inv MT MA)
		  (INST-in i MT)
		  (MAETT-p MT)
		  (MA-state-p MA)
		  (INST-p i)
		  (dispatched-p i)
		  (not (committed-p i)))
	     (equal (ex-intr? MA sigs) 0))
  :hints (("goal" :in-theory (e/d (ex-intr? lift-b-ops equal-b1p-converter)
				  (not-ex-intr-if-rob-not-empty))
		  :use (:instance not-ex-intr-if-rob-not-empty))))

(in-theory (disable not-ex-intr-if-INST-at-execute-or-complete-stg))

;; INST-excpt-flags is the current exception flags stored in the ROB.
;; This is equivalent to INST-excpt-detected-p
(defthm excpt-raised-INST-excpt
    (implies (INST-p i)
	     (equal (excpt-raised? (INST-excpt-flags i))
		    (if (INST-excpt-detected-p i) 1 0)))
  :hints (("Goal" :in-theory (enable INST-excpt-flags INST-excpt-detected-p))))
			
; Only instructions at IFU or DQ stage can be externally interrupted.
(defthm not-INST-exintr-now-if-not-IFU-or-dq
    (implies (dispatched-p i)
	     (equal (INST-exintr-now? i MA sigs) 0))
  :hints (("Goal" :in-theory (enable INST-exintr-now?))))

; INST-exintr-now? predicate is not true if the external interrupt 
; is not detected by ex-intr?.
(defthm not-INST-exintr-now-if-not-ex-intr
    (implies (and (inv MT MA)
		  (not (b1p (ex-intr? MA sigs))))
	     (equal (INST-exintr-now? i MA sigs) 0))
  :hints (("Goal" :in-theory (enable INST-exintr-now? lift-b-ops
				     equal-b1p-converter
				     ex-intr?))))

; INST-start-specultv cannot be true for committed instructions.
; INST-start-specultv is true if it is followed by instructions that
; will eventually thrown away.
(defthm not-INST-start-specultv-if-committed
    (implies (committed-p i)
	     (equal (INST-start-specultv? i) 0))
  :hints (("Goal" :in-theory (enable INST-start-specultv? committed-p))))

(defthm INST-start-specultv-if-INST-excpt
    (implies (and (not (committed-p i))
		  (b1p (INST-excpt? i)))
	     (equal (INST-start-specultv? i) 1))
  :hints (("goal" :in-theory (enable INST-start-specultv? committed-p
				     lift-b-ops equal-b1p-converter))))

(defthm INST-start-specultv-if-INST-context-sync
    (implies (and (not (committed-p i))
		  (b1p (INST-context-sync? i)))
	     (equal (INST-start-specultv? i) 1))
  :hints (("goal" :in-theory (enable INST-start-specultv? committed-p
				     lift-b-ops equal-b1p-converter))))

(defthm INST-start-specultv-if-INST-wrong-branch?
    (implies (and (not (committed-p i))
		  (b1p (INST-wrong-branch? i)))
	     (equal (INST-start-specultv? i) 1))
  :hints (("goal" :in-theory (enable INST-start-specultv? committed-p
				     lift-b-ops equal-b1p-converter))))

(defthm not-INST-cause-jmp-if-robe-not-head
    (implies (and (INST-p i)
		  (MAETT-p MT)
		  (not (equal (INST-tag i) (MT-rob-head MT))))
	     (equal (INST-cause-jmp? i MT MA sigs) 0))
  :hints (("Goal" :in-theory (enable INST-cause-jmp? lift-b-ops
				     equal-b1p-converter))))

;; INST-cause-jmp can be true only if the instruction is at complete stage.
(defthm not-INST-cause-jmp-if-not-complete
    (implies (not (complete-stg-p (INST-stg i)))
	     (equal (INST-cause-jmp? i MT MA sigs) 0))
  :hints (("Goal" :in-theory (enable INST-cause-jmp?))))

;; INST-cause-jmp? is not true if commit-inst? is not asserted.
(defthm not-INST-cause-jmp-if-not-commit-inst
    (implies (and (inv MT MA)
		  (MAETT-p MT)
		  (MA-state-p MA)
		  (INST-p i)
		  (INST-in i MT)
		  (not (b1p (INST-modified? i)))
		  (not (b1p (inst-specultv? i)))
		  (not (b1p (commit-inst? MA))))
	     (equal (INST-cause-jmp? i MT MA sigs) 0))
  :hints (("Goal" :in-theory (e/d (INST-cause-jmp? lift-b-ops
				     equal-b1p-converter
				     exception-relations
				     commit-jmp? commit-inst?
				     leave-excpt? enter-excpt?)
				  ())
		  :cases ((INST-excpt-detected-p i)))))

; INST-cause-jmp? and ex-intr? are exclusive.
(defthm not-INST-cause-jmp-if-ex-intr
    (implies (and (inv MT MA)
		  (INST-in i MT)
		  (MAETT-p MT)
		  (MA-state-p MA)
		  (INST-p i)
		  (b1p (ex-intr? MA sigs)))
	     (equal (INST-cause-jmp? i MT MA sigs) 0))
  :hints (("Goal" :use
		  (:instance not-ex-intr-if-INST-at-execute-or-complete-stg)
		  :in-theory (enable INST-cause-jmp? lift-b-ops
				     equal-b1p-converter))))

(defthm not-commit-jmp-if-rob-head-complete-wbuf
    (implies (and (inv MT MA)
		  (INST-in i MT)
		  (MAETT-p MT)
		  (MA-state-p MA)
		  (INST-p i)
		  (not (b1p (inst-specultv? i)))
		  (not (b1p (INST-modified? i)))		  
		  (equal (INST-tag i) (MT-rob-head MT))
		  (or (equal (INST-stg i) '(complete wbuf0))
		      (equal (INST-stg i) '(complete wbuf1))))
	     (not (b1p (commit-jmp? MA))))
  :hints (("Goal" :in-theory (enable commit-jmp? lift-b-ops wbuf-stg-p)))
  :rule-classes
  ((:rewrite :corollary
	     (implies (and (inv MT MA)
			   (INST-in i MT)
			   (MAETT-p MT)
			   (MA-state-p MA)
			   (INST-p i)
			   (b1p (commit-jmp? MA))
			   (not (b1p (inst-specultv? i)))
			   (not (b1p (INST-modified? i)))		  
			   (or (equal (INST-stg i) '(complete wbuf0))
			       (equal (INST-stg i) '(complete wbuf1))))
		      (equal (equal (INST-tag i) (MT-rob-head MT)) nil)))))

(defthm not-leave-excpt-if-rob-head-complete-wbuf
    (implies (and (inv MT MA)
		  (INST-in i MT)
		  (MAETT-p MT)
		  (MA-state-p MA)
		  (INST-p i)
		  (equal (INST-tag i) (MT-rob-head MT))
		  (not (b1p (inst-specultv? i)))
		  (not (b1p (INST-modified? i)))		  
		  (or (equal (INST-stg i) '(complete wbuf0))
		      (equal (INST-stg i) '(complete wbuf1))))
	     (not (b1p (leave-excpt? MA))))
  :hints (("Goal" :in-theory (enable leave-excpt? lift-b-ops wbuf-stg-p)))
  :rule-classes
  ((:rewrite :corollary
	     (implies (and (inv MT MA)
			   (INST-in i MT)
			   (MAETT-p MT)
			   (MA-state-p MA)
			   (INST-p i)
			   (not (b1p (inst-specultv? i)))
			   (not (b1p (INST-modified? i)))		  
			   (b1p (leave-excpt? MA))
			   (or (equal (INST-stg i) '(complete wbuf0))
			       (equal (INST-stg i) '(complete wbuf1))))
		      (equal (equal (INST-tag i) (MT-rob-head MT)) nil)))))

; If flush-all? is not on, an instruction remains in a MAETT after
; MAETT-update.
(encapsulate nil
(local
(defthm INST-in-step-INST-if-not-flush-all-help
    (implies (and (not (b1p (flush-all? MA sigs)))
		  (member-equal i trace))
	     (member-equal (step-INST i MT MA sigs)
			   (step-trace trace MT MA sigs
				       ISA smc spc)))
  :hints (("goal" :in-theory (enable flush-all? INST-exintr-now? ex-intr?
				     INST-cause-jmp?
				     lift-b-ops)))))

(defthm INST-in-step-INST-if-not-flush-all
    (implies (and (not (b1p (flush-all? MA sigs)))
		  (INST-in i MT))
	     (INST-in (step-INST i MT MA sigs) (MT-step MT MA sigs)))
  :hints (("goal" :in-theory (enable INST-in MT-step))))
)

;;;;;;;;;;;;;Other lemmas about MT and MA;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm LSU-pending-writes-if-wbuf-INST-in
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i)
		  (or (equal (INST-stg i) '(commit wbuf0))
		      (equal (INST-stg i) '(commit wbuf1)))
		  (MAETT-p MT) (MA-state-p MA))
	     (equal (LSU-pending-writes? (MA-LSU MA)) 1))
  :hints (("goal" :in-theory (enable LSU-pending-writes?
				     equal-b1p-converter wbuf-stg-p
				     lift-b-ops))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Property about reachable microarchitectural states
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(defthm not-ex-intr-if-commit-inst?
    (implies (and (inv MT MA)
		  (MA-state-p MA)
		  (MAETT-p MT)
		  (b1p (commit-inst? MA)))
	     (equal (ex-intr? MA sigs) 0))
  :hints (("Goal" :in-theory (enable commit-inst? ex-intr? lift-b-ops
				     equal-b1p-converter))))

(defthm commit-inst-if-commit-jmp
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (b1p (commit-jmp? MA)))
	     (equal (commit-inst? MA) 1))
  :hints (("goal" :in-theory (enable commit-jmp? commit-inst? lift-b-ops
				     equal-b1p-converter))))
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;  step-INST and stage again
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(defthm not-commit-stg-step-INST-if-robe-not-head
    (implies (and (INST-p i)
		  (MA-state-p MA)
		  (MAETT-p MT)
		  (inv MT MA)
		  (not (equal (INST-tag i) (MT-rob-head MT)))
		  (not (commit-stg-p (INST-stg i)))
		  (not (retire-stg-p (INST-stg i))))
	     (not (commit-stg-p (INST-stg (step-INST i MT MA sigs)))))
  :hints (("goal" :in-theory (enable MT-def lift-b-ops))))

(defthm not-retire-stg-step-INST-if-robe-not-head
    (implies (and (INST-p i)
		  (MAETT-p MT)
		  (MA-state-p MA)
		  (inv MT MA)
		  (not (equal (INST-tag i) (MT-rob-head MT)))
		  (not (commit-stg-p (INST-stg i)))
		  (not (retire-stg-p (INST-stg i))))
	     (not (retire-stg-p (INST-stg (step-INST i MT MA sigs)))))
  :hints (("goal" :in-theory (enable MT-def lift-b-ops))))

;;
(defthm not-commit-stg-p-step-INST-if-not-commit-inst?
    (implies (and (not (b1p (commit-inst? MA)))
		  (not (commit-stg-p (INST-stg i))))
	     (not (commit-stg-p (INST-stg (step-INST i MT MA sigs)))))
  :hints (("goal" :in-theory (enable MT-def lift-b-ops))))

(defthm not-retire-stg-p-step-INST-if-not-commit-inst?
    (implies (and (not (b1p (commit-inst? MA)))
		  (not (commit-stg-p (INST-stg i)))
		  (not (retire-stg-p (INST-stg i))))
	     (not (retire-stg-p (INST-stg (step-INST i MT MA sigs)))))
  :hints (("goal" :in-theory (enable MT-def lift-b-ops))))

(defthm retire-INST-stg-step-INST-if-complete-robe-is-head
    (implies (and (INST-p i)
		  (MAETT-p MT)
		  (MA-state-p MA)
		  (inv MT MA)
		  (equal (INST-tag i) (MT-rob-head MT))
		  (complete-stg-p (INST-stg i))
		  (b1p (commit-inst? MA))
		  (not (commit-stg-p (INST-stg (step-INST i MT MA sigs)))))
	     (retire-stg-p (INST-stg (step-INST i MT MA sigs))))
  :hints (("goal" :in-theory (enable MT-def lift-b-ops))))

;; If j is at the complete stage and it does not commit in this cycle,
;; it stays in the complete stage in the next cycle.
(defthm complete-stg-p-step-INST-if-not-INST-commit
    (implies (and (complete-stg-p (INST-stg j))
		  (not (b1p (INST-commit? j MA))))
	     (complete-stg-p (INST-stg (step-INST j MT MA sigs))))
  :hints (("Goal" :in-theory (enable step-INST step-INST-complete
				     lift-b-ops))))

(defthm commit-if-inst-commit
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i)
		  (b1p (INST-commit? i MA))
		  (not (commit-stg-p (INST-stg (step-INST i MT MA sigs))))
		  (MAETT-p MT) (MA-state-p MA))
	     (retire-stg-p (INST-stg (step-INST i MT MA sigs))))
  :hints (("goal" :in-theory (enable INST-commit? lift-b-ops)))
  :rule-classes
  ((:rewrite)
   (:rewrite :corollary
	     (implies (and (inv MT MA)
			   (INST-in i MT) (INST-p i)
			   (b1p (INST-commit? i MA))
			   (MAETT-p MT) (MA-state-p MA))
		      (committed-p (step-INST i MT MA sigs)))
	     :hints (("goal" :in-theory (enable committed-p))))))

(defthm not-commit-if-not-INST-commit
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i) 
		  (MAETT-p MT) (MA-state-p MA) (MA-input-p sigs)
		  (not (committed-p i))
		  (not (b1p (INST-commit? i MA))))
	     (not (committed-p (step-INST i MT MA sigs))))
  :hints (("Goal" :in-theory (enable step-inst-complete-inst lift-b-ops
				     step-inst-low-level-functions 
				     committed-p*))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; no-commit-inst-p no-dispatched-inst-p
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(defthm no-commit-inst-p-if-no-dispatched-inst-p
    (implies (and (INST-listp trace) (no-dispatched-inst-p trace))
	     (no-commit-inst-p trace))
  :hints (("goal" :in-theory (enable dispatched-p))))

(defthm no-trace-CMI-p-if-no-commit-inst-p
    (implies (and (INST-listp trace) (no-commit-inst-p trace))
	     (not (trace-CMI-p trace))))

(encapsulate nil
(local
  (defthm no-dispatched-inst-p-cdr-help
      (implies (and (in-order-trace-p trace)
		    (INST-listp trace)
		    (INST-listp sub)
		    (tail-p sub trace)
		    (not (dispatched-p (car sub))))
	       (no-dispatched-inst-p (cdr sub)))
    :hints (("goal" :in-theory (enable dispatched-p)))))

(defthm no-dispatched-inst-p-cdr
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-listp trace)
		  (subtrace-p trace MT)
		  (not (dispatched-p (car trace))))
	     (no-dispatched-inst-p (cdr trace)))
  :hints (("Goal" :in-theory (enable inv weak-inv
				     in-order-dispatch-commit-p
				     subtrace-p))))
)

(encapsulate nil
(local
 (defthm no-commit-inst-p-cdr-help
     (implies (and (in-order-trace-p trace)
		   (INST-listp trace)
		   (INST-listp sub)
		   (tail-p sub trace)
		   (not (committed-p (car sub))))
	      (no-commit-inst-p (cdr sub)))
   :hints (("Goal" :in-theory (enable committed-p)))))

	     
(defthm no-commit-inst-p-cdr
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-listp trace)
		  (subtrace-p trace MT)
		  (not (committed-p (car trace))))
	     (no-commit-inst-p (cdr trace)))
  :hints (("goal" :in-theory (enable inv weak-inv
				     in-order-dispatch-commit-p
				     subtrace-p))))
)

		  
(defun trace-1st-non-commit-inst (trace)
  (if (endp trace) nil
      (if (not (committed-p (car trace)))
	  (car trace)
	  (trace-1st-non-commit-inst (cdr trace)))))

(defun MT-1st-non-commit-INST (MT)
  (trace-1st-non-commit-inst (MT-trace MT)))

(defun trace-all-committed-p (trace)
  (if (endp trace) T
      (if (committed-p (car trace))
	  (trace-all-committed-p (cdr trace))
	  nil)))
			 
      
(defun MT-all-committed-p (MT)  (trace-all-committed-p (MT-trace MT)))
(in-theory (disable MT-all-committed-p MT-1st-non-commit-inst))

(encapsulate nil
(local
(defthm not-MT-all-committed-p-if-non-commit-INST-in-help
    (implies (and (member-equal i trace) 
		  (not (committed-p i)))
	     (not (trace-all-committed-p trace)))))

(defthm not-MT-all-committed-p-if-non-commit-INST-in
    (implies (and (INST-in i MT) (INST-p i)
		  (not (committed-p i)))
	     (not (MT-all-committed-p MT)))
  :hints (("goal" :in-theory (enable INST-in MT-all-committed-p))))
)

(encapsulate nil
(local
(defthm INST-p-MT-1st-non-commit-inst-help
    (implies (and (INST-listp trace)
		  (not (trace-all-committed-p trace)))
	     (INST-p (trace-1st-non-commit-inst trace)))))

(defthm INST-p-MT-1st-non-commit-inst
    (implies (and (MAETT-p MT)
		  (not (MT-all-committed-p MT)))
	     (INST-p (MT-1st-non-commit-inst MT)))
  :hints (("goal" :in-theory
		  (enable MT-all-committed-p MT-1st-non-commit-inst))))
)

(encapsulate nil
(local
(defthm INST-in-MT-1st-non-commit-inst-help
    (implies (not (trace-all-committed-p trace))
	     (member-equal (trace-1st-non-commit-inst trace) trace))))

(defthm INST-in-MT-1st-non-commit-inst
    (implies (and (inv MT MA)
		  (not (MT-all-committed-p MT)))
	     (INST-in (MT-1st-non-commit-inst MT) MT))
  :hints (("goal" :in-theory (enable MT-all-committed-p MT-1st-non-commit-inst
				     INST-in))))
)

(encapsulate nil
(local
(defthm committed-p-MT-1st-non-commit-inst-help
    (implies (not (trace-all-committed-p trace))
	     (not (committed-p (trace-1st-non-commit-inst trace))))))

(defthm committed-p-MT-1st-non-commit-inst
    (implies (not (MT-all-committed-p MT))
	     (not (committed-p (MT-1st-non-commit-inst MT))))
  :hints (("goal" :in-theory
		  (enable MT-1st-non-commit-inst MT-all-committed-p))))
)

(encapsulate nil
(local
 (defthm inst-specultv-MT-1st-non-commit-inst-help
     (implies (and (INST-listp trace)
		   (trace-correct-speculation-p trace)
		   (not (trace-all-committed-p trace)))
	      (equal (inst-specultv? (trace-1st-non-commit-inst trace)) 0))
   :hints (("goal" :in-theory (enable equal-b1p-converter)))))

(defthm inst-specultv-MT-1st-non-commit-inst
    (implies (and (inv MT MA)
		  (not (MT-all-committed-p MT))
		  (MAETT-p MT) (MA-state-p MA))
	     (equal (inst-specultv? (MT-1st-non-commit-inst MT)) 0))
  :hints (("goal" :in-theory (enable inv correct-speculation-p
				     MT-all-committed-p
				     MT-1st-non-commit-inst))))
)

(encapsulate nil
(local
(defthm INST-tag-MT-1st-non-commit-inst-help
    (implies (and (in-order-rob-trace-p trace rix)
		  (INST-listp trace)
		  (dispatched-p (trace-1st-non-commit-inst trace))
		  (not (trace-all-committed-p trace)))
	     (equal (INST-tag (trace-1st-non-commit-inst trace))
		    rix))
  :hints (("goal" :in-theory (enable committed-p)))))

(defthm INST-tag-MT-1st-non-commit-inst
    (implies (and (inv MT MA)
		  (not (MT-all-committed-p MT))
		  (dispatched-p (MT-1st-non-commit-inst MT))
		  (MAETT-p MT) (MA-state-p MA))
	     (equal (INST-tag (MT-1st-non-commit-inst MT))
		    (MT-ROB-head MT)))
  :hints (("goal" :in-theory (enable MT-1st-non-commit-inst MT-all-committed-p
				     inv IN-order-ROB-p))))
)

(encapsulate nil
(local
(defthm dispatched-p-MT-1st-non-commit-inst-help
    (implies (and (inv MT MA)
		  (subtrace-p trace MT)
		  (member-equal i trace) (INST-p i)
		  (INST-listp trace)
		  (not (committed-p i))
		  (dispatched-p i)
		  (MAETT-p MT) (MA-state-p MA))
	     (dispatched-p (trace-1st-non-commit-inst trace)))
  :hints (("goal" :in-theory (disable INST-IN-ORDER-DISPATCHED-UNDISPATCHED)) 
	  (when-found (dispatched-p (car trace))
		      (:use (:instance INST-IN-ORDER-DISPATCHED-UNDISPATCHED
				       (j (car trace))))))))

(defthm dispatched-p-MT-1st-non-commit-inst
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i)
		  (not (committed-p i))
		  (dispatched-p i)
		  (MAETT-p MT) (MA-state-p MA))
	     (dispatched-p (MT-1st-non-commit-inst MT)))
  :hints (("goal" :in-theory (enable MT-1st-non-commit-inst
				     INST-in))))
)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; A theory about the instruction at ROB head
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(encapsulate nil
(local
(defthm uniq-inst-of-tag-if-commit-inst-help
    (implies (and (inv MT MA)
		  (no-tag-conflict-at (MT-ROB-head MT) MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (b1p (commit-inst? MA)))
	     (uniq-inst-of-tag (MT-ROB-head MT) MT))
  :hints (("goal" :in-theory (enable no-tag-conflict-at
				     commit-inst? lift-b-ops)))
  :rule-classes nil))

;  If an instruction commits this cycle, there is a unique instruction
; stored at the head of ROB.
(defthm uniq-inst-of-tag-if-commit-inst
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (b1p (commit-inst? MA)))
	     (uniq-inst-of-tag (MT-ROB-head MT) MT))
  :hints (("goal" :use (:instance uniq-inst-of-tag-if-commit-inst-help))))
)

(defthm uniq-inst-of-tag-if-context-sync
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (or (b1p (commit-jmp? MA))
		      (b1p (leave-excpt? MA))
		      (b1p (enter-excpt? MA))))
	     (uniq-inst-of-tag (MT-rob-head MT) MT))
  :hints (("goal" :in-theory (enable commit-jmp? lift-b-ops
				     enter-excpt? leave-excpt?))))

(defthm complete-inst-of-tag-if-context-sync
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (or (b1p (commit-jmp? MA))
		      (b1p (leave-excpt? MA))
		      (b1p (enter-excpt? MA))))
	     (complete-stg-p (INST-stg (inst-of-tag (MT-rob-head MT) MT))))
  :hints (("goal" :in-theory (e/d (commit-jmp? lift-b-ops
					       leave-excpt? enter-excpt?
					       committed-p dispatched-p)
				  (inst-of-tag-is-dispatched
				   inst-of-tag-is-not-committed))
		  :use ((:instance inst-of-tag-is-not-committed
				   (rix (MT-rob-head MT)))
			(:instance inst-of-tag-is-dispatched
				   (rix (MT-rob-head MT)))))))

; Matt K. mod: Modernize theory-invariant call below.
#|
(theory-invariant
 (not (and (or (member-equal '(:rewrite uniq-inst-of-tag-if-context-sync)
			     theory)
	       (member-equal '(:rewrite complete-inst-of-tag-if-context-sync)
			     theory))
	   (or (member-equal '(:definition enter-excpt?) theory)
	       (member-equal '(:definition commit-jmp?) theory)
	       (member-equal '(:definition leave-excpt?) theory)))))

; Matt K. mod: The following modernization of the event above can be accepted,
; but it causes a theory-invariant violation in event
; not-INST-commit-if-not-enter-excpt below.
(theory-invariant
 (not (and (or (active-runep '(:rewrite uniq-inst-of-tag-if-context-sync))
	       (active-runep '(:rewrite complete-inst-of-tag-if-context-sync)))
	   (or (active-runep '(:definition enter-excpt?))
	       (active-runep '(:definition commit-jmp?))
	       (active-runep '(:definition leave-excpt?))))))
|#

; The instruction at the head of ROB will not be in execute-stg if
; commit-inst? is on.
(defthm not-execute-stg-p-inst-at-rob-head-if-commit-inst
    (implies (and (inv MT MA)
		  (MA-state-p MA) (MAETT-p MT)
		  (b1p (commit-inst? MA)))
     (not (execute-stg-p (INST-stg (inst-of-tag (MT-ROB-head MT) MT)))))
  :hints (("goal" :in-theory (enable commit-inst? lift-b-ops))))

(defthm complete-inst-of-tag-if-commit-inst
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (b1p (commit-inst? MA)))
	     (complete-stg-p (INST-stg (inst-of-tag (MT-rob-head MT) MT))))
  :hints (("goal" :in-theory (e/d (commit-inst? lift-b-ops
						committed-p dispatched-p)
				  (inst-of-tag-is-dispatched
				   inst-of-tag-is-not-committed))
		  :use ((:instance inst-of-tag-is-not-committed
				   (rix (MT-rob-head MT)))
			(:instance inst-of-tag-is-dispatched
				   (rix (MT-rob-head MT)))))))

; Matt K. mod: Modernize theory-invariant call below.
#|
(theory-invariant
 (not (and (member-equal '(:definition commit-inst?) theory)
	   (or (member-equal '(:rewrite uniq-inst-of-tag-if-commit-inst)
			     theory)
	       (member-equal '(:rewrite COMPLETE-INST-OF-TAG-IF-COMMIT-INST)
			     theory)
	       (member-equal '(:rewrite
			  NOT-EXECUTE-STG-P-INST-AT-ROB-HEAD-IF-COMMIT-INST)
			  theory)))))

; Matt K. mod: The following modernization of the event above can be accepted,
; but it causes a theory-invariant violation in event
; not-INST-commit-if-not-enter-excpt below.
(theory-invariant
 (not (and (active-runep '(:definition commit-inst?))
	   (or (active-runep '(:rewrite uniq-inst-of-tag-if-commit-inst))
	       (active-runep '(:rewrite COMPLETE-INST-OF-TAG-IF-COMMIT-INST))
	       (active-runep '(:rewrite
                               NOT-EXECUTE-STG-P-INST-AT-ROB-HEAD-IF-COMMIT-INST))))))
|#

(deftheory incompatible-with-excpt-in-MAETT-lemmas
    '(uniq-inst-of-tag-if-commit-inst
      uniq-inst-of-tag-if-context-sync
      complete-inst-of-tag-if-context-sync
      COMPLETE-INST-OF-TAG-IF-COMMIT-INST
      NOT-EXECUTE-STG-P-INST-AT-ROB-HEAD-IF-COMMIT-INST))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;  Theory about MT-non-commit-trace and MT-non-retire-trace.
;;  MT-non-commit-trace and MT-non-retire-trace return the subtrace
;;  of a MAETT which contains non-committed or non-retired instructions. 

;; Definitions of MT-non-commit-trace and MT-non-retire-trace.
(defun non-commit-trace (trace)
  (declare (xargs :guard (INST-listp trace)))
  (if (endp trace) nil
      (if (or (commit-stg-p (INST-stg (car trace)))
	      (retire-stg-p (INST-stg (car trace))))
	  (non-commit-trace (cdr trace))
	  trace)))
      
; MT-non-commit-trace returns the largest subtrace of an MAETT
; which begins with an non-committed instruction.  Since instructions
; commit in program order, a subtrace returned by MT-non-commit-trace
; contains only non-committed instructions.
(defun MT-non-commit-trace (MT)
  (declare (xargs :guard (MAETT-p MT)))
  (non-commit-trace (MT-trace MT)))
(in-theory (disable MT-non-commit-trace))

(defun non-retire-trace (trace)
  (declare (xargs :guard (INST-listp trace)))
  (if (endp trace) nil
      (if (retire-stg-p (INST-stg (car trace)))
	  (non-retire-trace (cdr trace))
	  trace)))
      
; MT-non-retire-trace returns the largest subtrace of an MAETT which
; begins with an non-retired instructions.  A subtrace returned by
; MT-non-retire-trace may contains non-retired instructions.
(defun MT-non-retire-trace (MT)
  (declare (xargs :guard (MAETT-p MT)))
  (non-retire-trace (MT-trace MT)))
(in-theory (disable MT-non-retire-trace))

;; Basic lemmas about MT-non-commit-trace and MT-non-retire-trace.
(defthm INST-listp-non-commit-trace
    (implies (INST-listp trace)
	     (INST-listp (non-commit-trace trace))))

(defthm INST-listp-MT-non-commit-trace
    (implies (MAETT-p MT)
	     (INST-listp (MT-non-commit-trace MT)))
  :hints (("Goal" :in-theory (enable MT-non-commit-trace))))

(encapsulate nil
(local
 (defthm subtrace-p-MT-non-commit-trace-help
     (implies (INST-listp trace) (tail-p (non-commit-trace trace) trace))))

(defthm subtrace-p-MT-non-commit-trace
    (implies (MAETT-p MT) (subtrace-p (MT-non-commit-trace MT) MT))
  :hints (("Goal" :in-theory (enable subtrace-p MT-non-commit-trace))))
) ;encapsulate

(encapsulate nil
(local
(defthm not-retire-stg-p-car-MT-non-commit-trace-help
    (implies (and (consp (non-commit-trace trace)) (INST-listp trace))
	     (not (retire-stg-p (INST-stg (car (non-commit-trace trace))))))))

; The first entry of an subtrace returned by MT-non-commit-trace
; represents an non-committed instruction.  Thus the represented
; instruction is not in retire-stg-p.
(defthm not-retire-stg-p-car-MT-non-commit-trace
    (implies (and (MAETT-p MT) (consp (MT-non-commit-trace MT)))
	     (not (retire-stg-p (INST-stg (car (MT-non-commit-trace MT))))))
  :hints (("Goal" :in-theory (enable MT-non-commit-trace))))
)

(encapsulate nil
(local
(defthm not-retire-stg-p-car-MT-non-retire-trace-help
    (implies (and (consp (non-retire-trace trace)) (INST-listp trace))
	     (not (retire-stg-p (INST-stg (car (non-retire-trace trace))))))))

; The first entry of an subtrace returned by MT-non-retire-trace
; represents a non-retired instruction.
(defthm not-retire-stg-p-car-MT-non-retire-trace
    (implies (and (MAETT-p MT) (consp (MT-non-retire-trace MT)))
	     (not (retire-stg-p (INST-stg (car (MT-non-retire-trace MT))))))
  :hints (("Goal" :in-theory (enable MT-non-retire-trace))))
)

(encapsulate nil
(local
(defthm not-commit-stg-p-car-MT-non-commit-trace-help
    (implies (and (consp (non-commit-trace trace)) (INST-listp trace))
	     (not (commit-stg-p (INST-stg (car (non-commit-trace trace))))))))

; The first instruction of an subtrace returned by MT-non-commit-trace
; is not committed.
(defthm not-commit-stg-p-car-MT-non-commit-trace
    (implies (and (MAETT-p MT) (consp (MT-non-commit-trace MT)))
	     (not (commit-stg-p (INST-stg (car (MT-non-commit-trace MT))))))
  :hints (("Goal" :in-theory (enable MT-non-commit-trace))))
)

; MT-no-commit-trace does not contain any committed instruction entries. 
; A similar lemma about MT-no-retire-trace is not true since
; instruction retirement is not in-order.
(encapsulate nil
(local
(defthm no-commit-inst-p-MT-non-commit-trace
    (implies (and (in-order-trace-p trace)
		  (INST-listp trace))
	     (no-commit-inst-p (non-commit-trace trace))))
)
 
(defthm no-commit-trace-p-MT-non-commit-trace
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA))
	     (no-commit-inst-p (MT-non-commit-trace MT)))
  :hints (("Goal" :in-theory (enable weak-inv inv
				     MT-non-commit-trace
				     IN-ORDER-DISPATCH-COMMIT-P))))
)		  

(encapsulate nil
(local
 (defthm member-equal-non-commit-inst-MT-non-commit-trace-help
     (implies (and (in-order-trace-p trace)
		   (INST-p i) 
		   (member-equal i trace)
		   (not (retire-stg-p (inst-stg i)))
		   (not (commit-stg-p (inst-stg i))))
	      (member-equal i (non-commit-trace trace)))))

; A non-committed instruction is a member of MT-non-commit-trace.
(defthm member-equal-non-commit-inst-MT-non-commit-trace
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-p i) (INST-in i MT)
		  (not (retire-stg-p (inst-stg i)))
		  (not (commit-stg-p (inst-stg i))))
	     (member-equal i (MT-non-commit-trace MT)))
  :hints (("goal" :in-theory (enable MT-non-commit-trace INST-in))))
) ;encapsulate 

(encapsulate nil
(local
 (defthm member-equal-non-retire-inst-MT-non-retire-trace-help
     (implies (and (in-order-trace-p trace)
		   (INST-p i) 
		   (member-equal i trace)
		   (not (retire-stg-p (inst-stg i))))
	      (member-equal i (non-retire-trace trace)))))

; A non-retired instruction is a member of MT-non-commit-trace.
(defthm member-equal-non-retire-inst-MT-non-retire-trace
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-p i) (INST-in i MT)
		  (not (retire-stg-p (inst-stg i))))
	     (member-equal i (MT-non-retire-trace MT)))
  :hints (("goal" :in-theory (enable MT-non-retire-trace INST-in))))
)

; trace-correct-speculation-p is true for MT-non-commit-trace.
(encapsulate nil
(local
 (defthm trace-correct-speculation-p-MT-non-commit-trace-help
     (implies (trace-correct-speculation-p trace)
	      (trace-correct-speculation-p (non-commit-trace trace)))))

(defthm trace-correct-speculation-p-MT-non-commit-trace
    (implies (and (inv MT MA) (MAETT-p MT) (MA-state-p MA))
	     (trace-correct-speculation-p (MT-non-commit-trace MT)))
  :hints (("Goal" :in-theory (enable MT-non-commit-trace
				     inv
				     correct-speculation-p))))
)

; (MT-non-commit-trace MT) is a subtrace of MT.
(encapsulate nil
(local
(defthm tail-p-MT-non-commit-trace-help
    (implies (INST-listp trace) (tail-p (non-commit-trace trace) trace))))
	     
(defthm tail-p-MT-non-commit-trace
    (implies (MAETT-p MT) (tail-p (MT-non-commit-trace MT) (MT-trace MT)))
  :hints (("goal" :in-theory (enable MT-non-commit-trace))))
)

; (MT-non-retire-trace MT) is a subtrace of MT.
(encapsulate nil
(local
(defthm tail-p-MT-non-retire-trace-help
    (implies (INST-listp trace) (tail-p (non-retire-trace trace) trace))))
	     
(defthm tail-p-MT-non-retire-trace
    (implies (MAETT-p MT) (tail-p (MT-non-retire-trace MT) (MT-trace MT)))
  :hints (("goal" :in-theory (enable MT-non-retire-trace))))
)

(encapsulate nil
(local
 (defthm super-trace-of-MT-non-commit-trace-w-car-commit-help
     (implies (and (tail-p trace trace2)
		   (not (retire-stg-p (INST-stg (car trace))))
		   (not (commit-stg-p (INST-stg (car trace))))
		   (tail-p (non-commit-trace trace2) trace))
	      (equal (equal (non-commit-trace trace2) trace) t))
   :hints ((when-found-multiple 
	    ((TAIL-P TRACE (CDR TRACE2)) (TAIL-P TRACE2 TRACE))
	    (:use (:instance tail-p-transitivity
			     (lst1 trace2) (lst2 trace)
			     (lst3 (cdr trace2))))))))
     
; A subtrace trace is a terminating sublist of MT-non-commit-trace,
; if the first instruction in trace is committed.
(defthm super-trace-of-MT-non-commit-trace-w-car-commit
    (implies (and (inv MT MA)
		  (MAETT-p MT)
		  (MA-state-p MA)
		  (subtrace-p trace MT)
		  (not (retire-stg-p (INST-stg (car trace))))
		  (not (commit-stg-p (INST-stg (car trace))))
		  (tail-p (MT-non-commit-trace MT) trace))
	     (equal (MT-non-commit-trace MT) trace))
  :hints (("Goal" :in-theory (enable MT-non-commit-trace
				     subtrace-p)))
  :rule-classes
  ((:rewrite :corollary
	     (implies (and (inv MT MA)
			   (MAETT-p MT)
			   (MA-state-p MA)
			   (subtrace-p trace MT)
			   (not (retire-stg-p (INST-stg (car trace))))
			   (not (commit-stg-p (INST-stg (car trace))))
			   (tail-p (MT-non-commit-trace MT) trace))
		      (equal (equal (MT-non-commit-trace MT) trace)
			     T)))))

) ;encapsulate

(encapsulate nil
(local
 (defthm super-trace-of-MT-non-retire-trace-w-car-retire-help
     (implies (and (tail-p trace trace2)
		   (not (retire-stg-p (INST-stg (car trace))))
		   (tail-p (non-retire-trace trace2) trace))
	      (equal (equal (non-retire-trace trace2) trace) t))
   :hints ((when-found-multiple 
	    ((TAIL-P TRACE (CDR TRACE2)) (TAIL-P TRACE2 TRACE))
	    (:use (:instance tail-p-transitivity
			     (lst1 trace2) (lst2 trace)
			     (lst3 (cdr trace2))))))))
     
; A subtrace trace is a terminating sublist of MT-non-commit-trace,
; if the first instruction in trace is retired.
(defthm super-trace-of-MT-non-retire-trace-w-car-retire
    (implies (and (inv MT MA)
		  (MAETT-p MT)
		  (MA-state-p MA)
		  (subtrace-p trace MT)
		  (not (retire-stg-p (INST-stg (car trace))))
		  (tail-p (MT-non-retire-trace MT) trace))
	     (equal (MT-non-retire-trace MT) trace))
  :hints (("Goal" :in-theory (enable MT-non-retire-trace
				     subtrace-p)))
  :rule-classes
  ((:rewrite :corollary
	     (implies (and (inv MT MA)
			   (MAETT-p MT)
			   (MA-state-p MA)
			   (subtrace-p trace MT)
			   (not (retire-stg-p (INST-stg (car trace))))
			   (tail-p (MT-non-retire-trace MT) trace))
		      (equal (equal (MT-non-retire-trace MT) trace)
			     T)))))
)

(local
 (defthm no-uniq-inst-of-tag-in-trace-if-no-dispatched-inst-p
     (implies (no-dispatched-inst-p trace)
	      (not (uniq-inst-of-tag-in-trace idx trace)))))

(encapsulate nil

(local
(defthm not-uniq-inst-of-tag-in-trace-if-car-dispatched-help
    (implies (and (in-order-trace-p trace)
		  (INST-listp sub) 
		  (tail-p sub trace)
		  (not (dispatched-p (car sub))))
	     (not (uniq-inst-of-tag-in-trace idx (cdr sub))))
  :hints (("goal" :in-theory (disable INST-is-at-one-of-the-stages))
	  (when-found (IFU-STG-P (INST-STG (CAR SUB)))
	  (:use (:instance INST-is-at-one-of-the-stages (i (car sub))))))))

; If (car trace) is not a dispatched instruction, following instructions
; in (cdr trace) are not dispatched either.  Therefore, no instruction
; in (cdr trace) is stored in the ROB.
(defthm not-uniq-inst-of-tag-in-trace-if-car-dispatched
    (implies (and (inv MT MA)
		  (not (dispatched-p (car trace)))
		  (MAETT-p MT) (MA-state-p MA)
		  (subtrace-p trace MT)
		  (INST-listp trace))
	     (not (uniq-inst-of-tag-in-trace idx (cdr trace))))
  :hints (("goal" :in-theory (enable inv
				     subtrace-p
				     in-order-dispatch-commit-p))))
)
     
;;; Definition of local predicate MT-all-commit-before. The predicate
;;; returns non-nil value if all the instructions before instruction i are
;;; committed.
(defun trace-all-commit-before (i trace)
  (if (endp trace)
      T
      (if (equal i (car trace))
	  T
	  (and (or (commit-stg-p (INST-stg (car trace)))
		   (retire-stg-p (INST-stg (car trace))))
	       (trace-all-commit-before i (cdr trace))))))

(defun MT-all-commit-before (i MT)
  (trace-all-commit-before i (MT-trace MT)))

(in-theory (disable MT-all-commit-before))

(defun trace-all-commit-before-trace (sub trace)
  (if (endp trace)
      t
      (if (equal sub trace)
	  T
	  (and (or (commit-stg-p (INST-stg (car trace)))
		   (retire-stg-p (INST-stg (car trace))))
	       (trace-all-commit-before-trace sub (cdr trace))))))

(defun MT-all-commit-before-trace (trace MT)
  (trace-all-commit-before-trace trace (MT-trace MT)))

(in-theory (disable MT-all-commit-before-trace))

(encapsulate nil
(local
(defthm car-trace-INST-at-rob-head-help
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (in-order-rob-trace-p trace idx)
		  (not (committed-p (car sub)))
		  (subtrace-p trace MT)
		  (tail-p sub trace)
		  (INST-listp sub) 
		  (uniq-inst-of-tag-in-trace idx trace)
		  (trace-all-commit-before-trace sub trace))
	     (equal (inst-of-tag-in-trace idx trace)
		    (car sub)))
  :hints (("goal" :in-theory (e/d (committed-p dispatched-p)
				  (INST-is-at-one-of-the-stages)))
	  ("subgoal *1/2" :use (:instance INST-is-at-one-of-the-stages
					  (i (car trace)))))))

; The instruction at the head of the ROB is the first uncommitted instruction
; in program order.
(defthm car-trace-INST-at-rob-head
    (implies (and (inv MT MA)
		  (MA-state-p MA) (MAETT-p MT)
		  (subtrace-p trace MT)
		  (INST-listp trace)
		  (not (committed-p (car trace)))
		  (uniq-inst-of-tag (MT-rob-head MT) MT)
		  (MT-all-commit-before-trace trace MT))
	     (equal  (inst-of-tag (MT-rob-head MT) MT)
		     (car trace)))
  :hints (("goal" :in-theory (enable subtrace-p MT-all-commit-before-trace
				     inv in-order-ROB-p
				     uniq-inst-of-tag
				     inst-of-tag)
		  :use (:instance car-trace-INST-at-rob-head-help
				  (sub trace) (trace (MT-trace MT))
				  (idx (MT-rob-head MT)))))
  :rule-classes
  ((:rewrite)
   (:rewrite :corollary
	     (implies (and (inv MT MA)
			   (MA-state-p MA) (MAETT-p MT)
			   (subtrace-p trace MT)
			   (INST-listp trace)
			   (not (committed-p (car trace)))
			   (uniq-inst-of-tag (MT-rob-head MT) MT)
			   (MT-all-commit-before-trace trace MT))
		      (equal  (car trace)
			      (inst-of-tag (MT-rob-head MT) MT))))))
)

(in-theory (disable (:rewrite car-trace-INST-at-rob-head . 1)
		    (:rewrite car-trace-INST-at-rob-head . 2)))

(encapsulate nil
(local
(defthm robe-at-head-if-MT-all-commit-before-help
    (implies (and (IN-order-rob-trace-p trace rix)
		  (member-equal i trace)
		  (trace-all-commit-before i trace)
		  (not (committed-p i))
		  (dispatched-p I)
		  (INST-p i) (INST-listp trace))
	     (equal (INST-tag i) rix))
  :hints (("goal" :in-theory (enable committed-p dispatched-p)))))

(defthm robe-at-head-if-MT-all-commit-before
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i)
		  (MT-all-commit-before i MT)
		  (not (committed-p i))
		  (dispatched-p i)
		  (MAETT-p MT) (MA-state-p MA))
	     (equal (equal (MT-rob-head MT) (INST-tag i)) t))
  :hints (("goal" :in-theory (enable INST-in inv MT-all-commit-before
				     IN-ORDER-ROB-P))))
)

(encapsulate nil
(local
(defthm not-MT-all-commit-before-trace-nil-if-commit-inst-help-help
    (implies (uniq-inst-of-tag-in-trace rix trace)
	     (not (trace-all-commit-before-trace nil trace)))))

(local
(defthm not-MT-all-commit-before-trace-nil-if-commit-inst-help
    (implies (uniq-inst-of-tag (MT-ROB-head MT) MT)
	     (not (MT-all-commit-before-trace nil MT)))
  :hints (("goal" :in-theory (enable uniq-inst-of-tag
				     MT-all-commit-before-trace)))))

; There exist uncommitted instructions in MT if commit-inst? is 1.
; Consider the relation with committed-p-car-if-MT-all-commit-before-trace.
(defthm not-MT-all-commit-before-trace-nil-if-commit-inst
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (b1p (commit-inst? MA)))
	     (not (MT-all-commit-before-trace nil MT)))
  :hints (("goal" :in-theory
		  (enable incompatible-with-excpt-in-MAETT-lemmas))))
)

(encapsulate  nil
(local
(defthm not-MT-all-commit-before-trace-cdr-help
    (implies (and (tail-p sub trace)
		  (not (trace-all-commit-before-trace sub trace)))
	     (not (trace-all-commit-before-trace (cdr sub) trace)))))

(defthm not-MT-all-commit-before-trace-cdr
    (implies (and (subtrace-p trace MT)
		  (not (MT-all-commit-before-trace trace MT)))
	     (not (MT-all-commit-before-trace (cdr trace) MT)))
  :hints (("Goal" :in-theory (enable subtrace-p MT-all-commit-before-trace))))
)

(defthm MT-all-commit-before-trace-MT-trace
    (MT-all-commit-before-trace (MT-trace MT) MT)
  :hints (("goal" :in-theory (enable MT-all-commit-before-trace))))

(encapsulate nil
(local
 (defthm MT-all-commit-before-cdr-trace-help
     (implies (and (consp sub)
		   (trace-all-commit-before-trace sub trace)
		   (committed-p (car sub)))
	      (trace-all-commit-before-trace (cdr sub) trace))))

(defthm MT-all-commit-before-cdr-trace
    (implies (and (consp trace)
		  (MT-all-commit-before-trace trace MT)
		  (committed-p (car trace)))
	     (MT-all-commit-before-trace (cdr trace) MT))
  :hints (("goal" :in-theory (enable MT-all-commit-before-trace))))
)

(encapsulate nil
(local
 (defthm local-help
     (implies (and (inv MT MA)
		   (subtrace-p trace MT)
		   (consp trace)
		   (consp sub)
		   (committed-p (car sub))
		   (not (committed-p (car trace)))
		   (MAETT-p MT) (MA-state-p MA))
	      (not (tail-p sub (cdr trace))))
   :hints (("goal" :cases ((member-equal (car sub) (cdr trace))))
	   ("subgoal 2" :in-theory
			(disable
			 NOT-MEMBER-EQUAL-CDR-IF-CAR-IS-NOT-COMMIT)))))

(local
(defthm MT-all-commit-before-trace-if-car-is-commit-help
    (implies (and (inv MT MA)
		  (consp sub) (committed-p (car sub))
		  (subtrace-p trace MT)
		  (tail-p sub trace)
		  (MAETT-p MT) (MA-state-p MA))
	     (trace-all-commit-before-trace sub trace))))

(defthm MT-all-commit-before-trace-if-car-is-commit
    (implies (and (inv MT MA)
		  (consp trace) (committed-p (car trace))
		  (subtrace-p trace MT)
		  (MAETT-p MT) (MA-state-p MA))
	     (MT-all-commit-before-trace trace MT))
  :hints (("goal" :in-theory (enable MT-all-commit-before-trace subtrace-p))))
)

(encapsulate nil
(local
(defthm no-commit-inst-precedes-if-all-commit-before-help
    (implies (and (inv MT MA)
		  (subtrace-p trace MT)
		  (trace-all-commit-before i trace)
		  (not (committed-p j)))
	     (not (member-in-order j i trace)))
  :hints (("goal" :in-theory (enable member-in-order*
				     committed-p)))))

(defthm no-commit-inst-precedes-if-all-commit-before
    (implies (and (inv MT MA)
		  (MT-all-commit-before i MT)
		  (not (committed-p j)))
	     (not (inst-in-order-p j i MT)))
  :Hints (("Goal" :in-theory (enable MT-all-commit-before inst-in-order-p
				     subtrace-p))))
)

(encapsulate nil
(local
(defthm MT-all-commit-before-trace-MT-non-commit-trace-help
    (trace-all-commit-before-trace (non-commit-trace trace) trace)))

(defthm MT-all-commit-before-trace-MT-non-commit-trace
    (MT-all-commit-before-trace (MT-non-commit-trace MT) MT)
  :hints (("goal" :in-theory (enable MT-all-commit-before-trace
				     MT-non-commit-trace))))
)

(encapsulate nil
(local
 (defthm not-MT-all-commit-before-if-inst-specultv-help
     (implies (and (trace-correct-speculation-p trace)
		   (member-equal i trace) (INST-p i)
		   (INST-listp trace)
		   (b1p (inst-specultv? i)))
	      (not (trace-all-commit-before i trace)))))

(defthm not-MT-all-commit-before-if-inst-specultv
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i)
		  (b1p (inst-specultv? i))
		  (MAETT-p MT) (MA-state-p MA))
	     (not (MT-all-commit-before i MT)))
  :hints (("goal" :In-theory (enable MT-all-commit-before INST-in
				     inv correct-speculation-p))))
)

(encapsulate nil
(local
(defthm MT-all-commit-before-car-help
    (implies (and (consp sub)
		  (trace-all-commit-before-trace sub trace))
	     (trace-all-commit-before (car sub) trace))))

(defthm MT-all-commit-before-car
    (implies (and (consp trace)
		  (MT-all-commit-before-trace trace MT))
	     (MT-all-commit-before (car trace) MT))
  :hints (("goal" :in-theory (enable MT-all-commit-before-trace
				     MT-all-commit-before))))
)

(encapsulate nil
(local
(defthm not-MT-all-commit-before-car-help
    (implies (and (distinct-member-p trace)
		  (tail-p sub trace)
		  (consp sub)
		  (not (trace-all-commit-before-trace sub trace)))
	     (not (trace-all-commit-before (car sub) trace)))))

(defthm not-MT-all-commit-before-car
    (implies (and (inv MT MA)
		  (subtrace-p trace MT)
		  (consp trace)
		  (not (MT-all-commit-before-trace trace MT)))
	     (not (MT-all-commit-before (car trace) MT)))
  :hints (("goal" :in-theory (enable MT-all-commit-before-trace
				     subtrace-p inv weak-inv
				     MT-distinct-inst-p
				     MT-all-commit-before))))
)

(encapsulate nil
(local
(defthm not-uniq-inst-of-tag-in-trace-if-no-dispatched-inst-p
    (implies (no-dispatched-inst-p trace)
	     (not (uniq-inst-of-tag-in-trace rix trace)))))

(local
(defthm MT-all-commit-before-INST-at-rob-head-help
    (implies (and (INST-listp trace)
		  (in-order-trace-p trace)		  
		  (in-order-rob-trace-p trace rix)
		  (uniq-inst-of-tag-in-trace rix trace))
	     (trace-all-commit-before (inst-of-tag-in-trace rix trace)
				      trace))
  :hints (("goal" :in-theory (enable dispatched-p)))))

; All instructions before the instruction at the head of the ROB are
; committed.
(defthm MT-all-commit-before-INST-at-rob-head
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (uniq-inst-of-tag (MT-ROB-head MT) MT))
	     (MT-all-commit-before (inst-of-tag (MT-ROB-head MT) MT) MT))
  :hints (("goal" :in-theory (enable MT-all-commit-before
				     inst-of-tag
				     uniq-inst-of-tag
				     inv
				     in-order-dispatch-commit-p
				     in-order-ROB-p))))
)

(defthm MT-all-commit-before-INST-at-rob-head-2
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i)
		  (equal (INST-tag i) (MT-rob-head MT))
		  (dispatched-p i) (not (committed-p i))
		  (MAETT-p MT) (MA-state-p MA))
	     (MT-all-commit-before i MT))
  :hints (("Goal" :use (:instance MT-all-commit-before-INST-at-rob-head)
		  :in-theory (disable MT-all-commit-before-INST-at-rob-head))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;End of the theory about MT-non-commit-trace and MT-non-retire-trace.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Theories about commit again.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; If i is not completed, it does not commit this cycle.
(defthm complete-stg-p-if-INST-commit
    (implies (not (complete-stg-p (INST-stg i)))
	     (not (b1p (INST-commit? i MA))))
  :hints (("goal" :in-theory (enable INST-commit? lift-b-ops)))
  :rule-classes
  ((:rewrite :corollary (implies (not (complete-stg-p (INST-stg i)))
				 (equal (INST-commit? i MA) 0))
	     :hints (("goal" :in-theory (enable INST-commit? lift-b-ops))))))

;  Proof of not-INST-commit-if-earlier-inst-not-committed
;  Suppose we have two dispatched but not committed instruction i and j,
;  I and j are in ISA execution order.  J does not commit this cycle,
;  because instructions commit in-order, and I should commit first.
(encapsulate nil
; I and J are instructions in ROB. If I and J are in the ISA execution order,
; J cannot be at the head of ROB.
; Proof: If I is (MT-rob-head MT), trivial.  If they are different,
; (INST-in-order-p (MT-rob-head MT) i MT), and we get the lemma from
; transitivity of INST-in-order-p 
(local
(defthm J-is-ROB-head-if-I-is-not-commit
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-in-order-p i j MT)
		  (INST-p i) 
		  (INST-in i MT)
		  (not (committed-p i))
		  (INST-in j MT) (INST-p j)
		  (dispatched-p j))
	     (INST-in-order-p (inst-of-tag (MT-rob-head MT) MT) j MT))
  :hints (("goal" :cases ((equal (inst-of-tag (MT-rob-head MT) MT) i))
		  :restrict ((NOT-ROB-EMPTY-IF-INST-IS-EXECUTED
			      ((i i)))))
	  ("subgoal 2" :cases ((dispatched-p i))))))

(local
 (defthm no-inst-of-tag-in-trace-if-member-equal
     (implies (and (no-inst-of-tag-in-trace (INST-tag j) trace)
		   (dispatched-p j)
		   (not (committed-p j)))
	      (not (member-equal j trace)))
   :hints (("goal" :in-theory (enable dispatched-p committed-p)))))

(local
 (defthm not-INST-in-order-p-if-INST-tag-equal-induct
     (implies (and (uniq-inst-of-tag-in-trace (INST-tag i) trace)
		   (not (committed-p i))
		   (dispatched-p i)
		   (not (committed-p j))
		   (dispatched-p j)
		   (equal (INST-tag j) (INST-tag i)))
	      (not (member-in-order i j trace)))
   :hints (("goal" :in-theory (enable member-in-order* dispatched-p
				      committed-p)))))

(local
(defthm not-INST-in-order-p-if-INST-tag-equal
    (implies (and (uniq-inst-of-tag (INST-tag i) MT)
		  (not (committed-p i))
		  (dispatched-p i)
		  (not (committed-p j))
		  (dispatched-p j)
		  (equal (INST-tag j) (INST-tag i)))
	     (not (INST-in-order-p i j MT)))
  :hints (("Goal" :in-theory (enable INST-in-order-p uniq-inst-of-tag)))))

(local
(defthm not-equal-to-MT-rob-head-if-preceded-by-inst-of-tag-head
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-p j) (INST-in j MT)
		  (uniq-inst-of-tag (MT-rob-head MT) MT)
		  (INST-in-order-p (inst-of-tag (MT-rob-head MT) MT) j MT)
		  (not (committed-p j))
		  (dispatched-p j))
	     (not (equal (INST-tag j) (MT-rob-head MT))))))

(defthm not-at-ROB-head-if-earlier-inst-not-commit
    (implies (and (inv MT MA)
		  (INST-in-order-p i j MT)
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-p i) (INST-p j)
		  (INST-in i MT) (INST-in j MT)
		  (not (committed-p i))
		  (dispatched-p j))
	     (not (equal (INST-tag j) (MT-rob-head MT))))
  :Hints (("goal" :restrict ((NOT-ROB-EMPTY-IF-INST-IS-EXECUTED ((i i))))
		  :cases ((not (dispatched-p i)) (committed-p j)))))

; Instruction j does not commit in this cycle, if a preceding instruction
; i is not yet committed. 
(defthm not-INST-commit-if-earlier-inst-not-committed
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-in-order-p i j MT)
		  (INST-p i) (INST-in i MT)
		  (INST-p j) (INST-in j MT)
		  (not (committed-p i)))
	     (equal (INST-commit? j MA) 0))
  :hints (("goal" :in-theory (enable INST-commit? lift-b-ops
				     equal-b1p-converter
				     bv-eqv-iff-equal))))
)
(in-theory (disable not-INST-commit-if-earlier-inst-not-committed))

; If instruction j follows i in program order, and j commits, i
; is already committed because of in-order commit.
(defthm committed-p-if-INST-commit-following
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i)  (INST-in j MT) (INST-p j)
		  (not (committed-p i))
		  (b1p (INST-commit? j MA))
		  (MAETT-p MT) (MA-state-p MA))
	     (not (INST-in-order-p i j MT)))
  :hints (("goal" :in-theory (e/d (committed-p INST-commit? lift-b-ops)
				  (complete-stg-p-if-INST-commit
				   INST-is-at-one-of-the-stages))
		  :use ((:instance complete-stg-p-if-INST-commit (i j))
			(:instance INST-is-at-one-of-the-stages)))))

(in-theory (disable committed-p-if-INST-commit-following))	      

; Suppose instruction i causes an exception. When i commits, 
; enter-excpt? must be asserted. 
(defthm not-INST-commit-if-not-enter-excpt
    (implies (and (inv MT MA)
		  (b1p (INST-excpt? i))
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-p i) (INST-in i MT)
		  (not (b1p (inst-specultv? i)))
		  (not (b1p (INST-modified? i)))
		  (not (b1p (enter-excpt? MA))))
	     (equal (INST-commit? i MA) 0))
  :hints (("goal" :in-theory (enable INST-commit? enter-excpt? lift-b-ops
				     bv-eqv-iff-equal
				     inst-excpt-detected-p
				     commit-inst?
				     equal-b1p-converter))))

(defthm not-INST-commit-if-not-INST-excpt
    (implies (and (inv MT MA)
		  (complete-stg-p (INST-stg i))
		  (not (b1p (INST-excpt? i)))
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-p i) (INST-in i MT)
		  (not (b1p (inst-specultv? i)))
		  (not (b1p (INST-modified? i)))
		  (b1p (enter-excpt? MA)))
	     (equal (INST-commit? i MA) 0))
  :hints (("goal" :in-theory (enable INST-commit? enter-excpt? lift-b-ops
				     bv-eqv-iff-equal
				     inst-excpt-detected-p
				     commit-inst?
				     equal-b1p-converter))))

(defthm not-INST-commit-if-not-commit-jmp
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i)
		  (MAETT-p MT) (MA-state-p MA)
		  (complete-stg-p (INST-stg i))
		  (b1p (INST-wrong-branch? i))
		  (not (b1p (commit-jmp? MA)))
		  (not (b1p (inst-specultv? i)))
		  (not (b1p (INST-modified? i))))
	     (equal (INST-commit? i MA) 0))
  :hints (("goal" :in-theory (e/d (lift-b-ops commit-jmp? commit-inst?
					      equal-b1p-converter
					      INST-excpt?
					      INST-commit? INST-wrong-branch?)
				  (incompatible-with-excpt-in-MAETT-lemmas)))))
 
(defthm not-INST-commit-if-not-leave-or-enter-excpt
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i)
		  (MAETT-p MT) (MA-state-p MA)
		  (complete-stg-p (INST-stg i))
		  (b1p (INST-context-sync? i))
		  (not (b1p (commit-jmp? MA)))
		  (not (b1p (inst-specultv? i)))
		  (not (b1p (INST-modified? i))))
	     (equal (INST-commit? i MA) 0))
  :hints (("goal" :in-theory (e/d (lift-b-ops  commit-inst?
					       INST-excpt?
					       equal-b1p-converter
					       INST-context-sync? 
					       commit-jmp? INST-commit?)
				  (incompatible-with-excpt-in-MAETT-lemmas)))))

(defthm not-INST-commit-if-not-flush-all
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i)
		  (MAETT-p MT) (MA-state-p MA)
		  (not (b1p (inst-specultv? i)))
		  (not (b1p (INST-modified? i)))
		  (complete-stg-p (INST-stg i))
		  (b1p (INST-start-specultv? i))
		  (not (b1p (flush-all? MA sigs))))
	     (equal (INST-commit? i MA) 0))
  :hints (("goal" :in-theory (enable INST-start-specultv? lift-b-ops
				     flush-all?))))

; If i is a speculative executed instruction, it is not at the head of ROB.
(defthm ROBE-not-head-if-inst-specultv
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i)
		  (complete-stg-p (INST-stg i))
		  (b1p (inst-specultv? i))
		  (MAETT-p MT) (MA-state-p MA))
	     (not (equal (INST-tag i) (MT-ROB-head MT))))
  :hints (("goal" :in-theory (disable tag-identity)
		  :use (:instance tag-identity
				  (j (MT-1st-non-commit-inst MT))))))

(encapsulate nil
(local
(defthm inst-specultv-INST-at-ROB-head-if-commit-inst-help-help
    (implies (and (trace-correct-speculation-p trace)
		  (trace-no-specultv-commit-p trace)
		  (member-equal i trace)
		  (trace-all-commit-before i trace))
	     (not (b1p (inst-specultv? i))))))

(local
(defthm inst-specultv-INST-at-ROB-head-if-commit-inst-help
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-in i MT) (INST-p i)
		  (MT-all-commit-before i MT))
	     (not (b1p (inst-specultv? i))))
  :hints (("goal" :in-theory (enable MT-all-commit-before
				     inv correct-speculation-p
				     INST-in
				     no-specultv-commit-p)))))

; The instruction at ROB head is not speculative
(defthm inst-specultv-INST-at-ROB-head-if-uniq-INST-at-ROB-head
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (uniq-inst-of-tag (MT-rob-head MT) MT))
	     (equal (inst-specultv? (inst-of-tag (MT-ROB-head MT) MT))
		    0))
  :hints (("goal" :in-theory (enable equal-b1p-converter lift-b-ops))))

)

; If commit-INST? is true, the instruction at the head of ROB commits.
(defthm INST-commit-INST-at-MT-rob-head
    (implies (and (inv MT MA)
		  (b1p (commit-INST? MA))
		  (MAETT-p MT) (MA-state-p MA))
	     (equal (INST-commit? (inst-of-tag (MT-ROB-head MT) MT) MA) 1))
  :hints (("goal" :in-theory (e/d (INST-commit? lift-b-ops
						committed-p dispatched-p
						commit-inst? 
						equal-b1p-converter)
				  (INST-OF-TAG-IS-dispatched
				   EXECUTE-OR-COMPLETE-STG-P-INST-OF-TAG
				   INST-OF-TAG-IS-not-committed))
		  :use ((:instance INST-OF-TAG-IS-dispatched
				   (rix (MT-rob-head MT)))
			(:instance INST-OF-TAG-IS-not-committed
				   (rix (MT-rob-head MT)))))))

; If i is a speculatively executed instruction, i does not commit.
(defthm not-INST-commit-if-inst-specultv
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i)
		  (b1p (inst-specultv? i))
		  (MAETT-p MT) (MA-state-p MA))
	     (equal (INST-commit? i MA) 0))
  :hints (("goal" :in-theory (enable equal-b1p-converter lift-b-ops
				     INST-commit?))))

; INST-commit? is always off if commit-inst? is off.		   
(defthm not-commit-inst-if-not-commit-inst
    (implies (not (b1p (commit-inst? MA)))
	     (equal (INST-commit? i MA) 0))
  :hints (("Goal" :in-theory (enable lift-b-ops INST-commit?
				     equal-b1p-converter))))

; If i commits, it is not externally interrupted.
(defthm not-INST-exintr-now-if-inst-commit
    (implies (b1p (INST-commit? i MA))
	     (equal (INST-exintr-now? i MT sigs) 0))
  :hints (("goal" :in-theory (enable INST-commit? INST-exintr-now?
				     lift-b-ops))))

(defthm INST-cause-jmp-if-leave-excpt
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (b1p (leave-excpt? MA)))
	     (equal (INST-cause-jmp? (inst-of-tag (MT-ROB-head MT) MT)
				     MT MA sigs)
		    1))
  :hints (("goal" :in-theory (enable INST-cause-jmp? leave-excpt?
				     lift-b-ops equal-b1p-converter))))

(defthm not-INST-cause-jmp-if-not-INST-commit
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (not (b1p (INST-commit? i MA))))
	     (equal (INST-cause-jmp? i MT MA sigs) 0))
  :hints (("goal" :in-theory (enable INST-cause-jmp? INST-commit? lift-b-ops
				     equal-b1p-converter))))

(defthm not-all-commit-before-if-execute-stg-p
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i)
		  (execute-stg-p (INST-stg i))
		  (or (b1p (commit-jmp? MA)) (b1p (enter-excpt? MA))
		      (b1p (leave-excpt? MA)))
		  (MAETT-p MT) (MA-state-p MA))
	     (not (MT-all-commit-before i MT)))
  :hints (("goal" :use (:instance robe-at-head-if-MT-all-commit-before)
		  :in-theory (e/d (commit-jmp? enter-excpt?
					       leave-excpt? lift-b-ops)
				  (robe-at-head-if-MT-all-commit-before)))))

(defthm INST-cause-jmp-if-complete-stg-p
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i)
		  (complete-stg-p (INST-stg i))
		  (MT-all-commit-before i MT)
		  (or (b1p (commit-jmp? MA))
		      (b1p (enter-excpt? MA))
		      (b1p (leave-excpt? MA)))
		  (MAETT-p MT) (MA-state-p MA))
	     (equal (INST-cause-jmp? i MT MA sigs) 1))
  :hints (("goal" :use (:instance robe-at-head-if-MT-all-commit-before)
		  :in-theory (e/d (INST-cause-jmp? lift-b-ops
						   equal-b1p-converter)
				  (robe-at-head-if-MT-all-commit-before)))))

(encapsulate nil
(local
 (defthm not-subtrace-after-p-if-out-of-order-dispatch
     (implies (and (inv MT MA)
		   (INST-in i MT)
		   (consp trace)
		   (dispatched-p (car trace))
		   (not (dispatched-p i))
		   (MAETT-p MT) (MA-state-p MA))
	      (not (subtrace-after-p i trace MT)))
   :hints (("goal" :use (:instance inst-in-order-dispatched-undispatched
				   (i (car trace)) (j i))
		   :in-theory (disable
			       INST-IN-ORDER-DISPATCHED-UNDISPATCHED)))))

(local
(defthm no-inst-at-MT-rob-head-if-MT-all-commit-before-help-help
    (implies (and (inv MT MA)
		  (not (dispatched-p i))
		  (INST-in i MT)
		  (subtrace-after-p i trace MT)
		  (MAETT-p MT) (MA-state-p MA))
	     (no-inst-of-tag-in-trace rix trace))))

(local
(defthm no-inst-at-MT-rob-head-if-MT-all-commit-before-help
    (implies (and (inv MT MA)
		  (subtrace-p trace MT)
		  (member-equal i trace) (INST-p i)
		  (trace-all-commit-before i trace)
		  (not (dispatched-p i))
		  (MAETT-p MT) (MA-state-p MA))
	     (no-inst-of-tag-in-trace rix trace))))

(defthm no-inst-at-MT-rob-head-if-MT-all-commit-before
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i)
		  (MT-all-commit-before i MT)
		  (not (dispatched-p i))
		  (MAETT-p MT) (MA-state-p MA))
	     (no-inst-of-tag rix MT))
  :hints (("goal" :in-theory (enable no-inst-of-tag INST-in
				     MT-all-commit-before))))
)

(defthm not-MT-all-commit-before-undispatched
    (implies (and (inv MT MA)
		  (or (DQ-stg-p (INST-stg i))
		      (IFU-stg-p (INST-stg i)))
		  (not (b1p (rob-empty? (MA-rob MA))))
		  (INST-in i MT) (INST-p i) 
		  (MAETT-p MT) (MA-state-p MA))
	     (not (MT-all-commit-before i MT)))
  :hints (("Goal" :use (:instance
			no-inst-at-MT-rob-head-if-MT-all-commit-before
			(rix (MT-ROB-head MT)))
		  :in-theory
		  (disable NO-INST-AT-MT-ROB-HEAD-IF-MT-ALL-COMMIT-BEFORE))))

(defthm INST-cause-jmp-if-commit-jmp
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i)
		  (MT-all-commit-before i MT)
		  (not (committed-p i))
		  (or (b1p (commit-jmp? MA))
		      (b1p (enter-excpt? MA))
		      (b1p (leave-excpt? MA)))
		  (MAETT-p MT) (MA-state-p MA))
	     (equal (INST-cause-jmp? i MT MA sigs) 1))
  :hints (("goal" :use (:instance inst-is-at-one-of-the-stages)
		  :in-theory
		  (e/d (commit-jmp? leave-excpt? enter-excpt? lift-b-ops)
		       (incompatible-with-excpt-in-MAETT-lemmas
			INST-is-at-one-of-the-stages
			no-inst-at-MT-rob-head-if-MT-all-commit-before)))
	  (when-found (IFU-stg-p (INST-stg i))
		      (:use (:instance
			     no-inst-at-MT-rob-head-if-MT-all-commit-before
			     (rix (MT-rob-head MT)))))))

(defthm INST-cause-jmp-or-INST-exintr-now-if-first-uncommit
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i)
		  (MT-all-commit-before i MT)
		  (not (committed-p i))
		  (b1p (flush-all? MA sigs))
		  (not (b1p (INST-exintr-now? i MA sigs)))
		  (MAETT-p MT) (MA-state-p MA))
	     (equal (INST-cause-jmp? i MT MA sigs) 1))
  :Hints (("goal" :in-theory (enable flush-all? lift-b-ops))))

(defthm committed-p-step-inst-if-INST-cause-jmp
    (implies (and (inv MT MA)
		  (INST-p i) (MAETT-p MT) (MA-state-p MA)
		  (b1p (INST-cause-jmp? i MT MA sigs))
		  (not (commit-stg-p (INST-stg (step-INST i MT MA sigs)))))
	     (retire-stg-p (INST-stg (step-INST i MT MA sigs))))
  :hints (("goal" :in-theory (enable INST-cause-jmp? lift-b-ops
				     INST-commit?
				     step-INST step-INST-complete))))

(in-theory (disable no-inst-at-MT-rob-head-if-MT-all-commit-before))

(defthm inst-cause-jmp-if-flush-all
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i) 
		  (complete-stg-p (INST-stg i))
		  (MT-all-commit-before i MT)
		  (b1p (flush-all? MA sigs))
		  (MAETT-p MT) (MA-state-p MA))
	     (equal (INST-cause-jmp? i MT MA sigs) 1))
  :hints (("Goal" :in-theory (enable INST-exintr-now? lift-b-ops))))

(defthm inst-exintr-now-if-flush-all
    (implies (and (inv MT MA)
		  (or (DQ-stg-p (INST-stg i))
		      (IFU-stg-p (INST-stg i)))
		  (MT-all-commit-before i MT)
		  (b1p (flush-all? MA sigs))
		  (INST-in i MT) (INST-p i) 
		  (MAETT-p MT) (MA-state-p MA))
	     (equal (INST-exintr-now? i MA sigs) 1))
  :hints (("Goal" :in-theory (e/d (flush-all? lift-b-ops)
				  (not-MT-all-commit-before-undispatched
				   NOT-COMMIT-INST-IF-ROB-EMPTY))
		  :use ((:instance not-MT-all-commit-before-undispatched)
			(:instance NOT-COMMIT-INST-IF-ROB-EMPTY)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Lemmas about INST-start-speculative and MT-specultv
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(defthm inst-start-specultv-step-INST-if-DQ-or-execute
    (implies (and (INST-p i) (MA-state-p MA) (MAETT-p MT) (MA-input-p sigs)
		  (or (DQ-stg-p (INST-stg i))
		      (execute-stg-p (INST-stg i))))
	     (equal (inst-start-specultv? (step-INST i MT MA sigs))
		    (inst-start-specultv? i)))
  :hints (("Goal" :in-theory (enable inst-start-specultv?))))

(defthm INST-start-specultv-step-INST-if-IFU
    (implies (and (INST-p i) (MA-state-p MA) (MAETT-p MT)
		  (MA-input-p sigs) (IFU-stg-p (INST-stg i))
		  (or (not (b1p (IFU-branch-predict? (MA-IFU MA) MA sigs)))
		      (b1p (DQ-full? (MA-DQ MA)))))
	     (equal (INST-start-specultv? (step-INST i MT MA sigs))
		    (INST-start-specultv? i)))
  :Hints (("goal" :in-theory (enable INST-start-specultv?
				     committed-p
				     lift-b-ops))))

(defthm INST-start-specultv-step-INST-if-complete
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i) (MA-state-p MA) (MAETT-p MT)
		  (MA-input-p sigs)
		  (complete-stg-p (INST-stg i))
		  (not (b1p (inst-specultv? i)))
		  (not (b1p (INST-modified? i)))
		  (not (b1p (flush-all? MA sigs))))
	     (equal (INST-start-specultv? (step-INST i MT MA sigs))
		    (INST-start-specultv? i)))
  :hints (("goal" :in-theory (enable equal-b1p-converter
				     INST-start-specultv? lift-b-ops))))

(defthm INST-start-specultv-step-INST
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i) (MA-state-p MA) (MAETT-p MT)
		  (MA-input-p sigs)
		  (not (b1p (inst-specultv? i)))
		  (not (b1p (INST-modified? i)))
		  (or (not (b1p (IFU-branch-predict? (MA-IFU MA) MA sigs)))
		      (b1p (DQ-full? (MA-DQ MA))))
		  (not (b1p (flush-all? MA sigs))))
	     (equal (INST-start-specultv? (step-INST i MT MA sigs))
		    (INST-start-specultv? i)))
  :hints (("goal" :use (:instance INST-is-at-one-of-the-stages)
		  :in-theory (disable INST-is-at-one-of-the-stages))))

(defthm INST-start-specultv-step-INST-2
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i)
		  (not (b1p (flush-all? MA sigs)))
		  (b1p (fetch-inst? MA sigs))
		  (not (b1p (inst-specultv? i)))
		  (not (b1p (INST-modified? i)))
		  (MA-input-p sigs)
		  (MA-state-p MA) (MAETT-p MT))
	     (equal (INST-start-specultv? (step-INST i MT MA sigs))
		    (INST-start-specultv? i)))
  :hints (("goal" :in-theory (enable fetch-inst? lift-b-ops))))

(defthm inst-start-specultv-step-INST-if-not-retire-after-step
    (implies (and (INST-p i)
		  (MAETT-p MT) (MA-state-p MA) (MA-input-p sigs)
		  (complete-stg-p (INST-stg i))
		  (not (commit-stg-p (INST-stg (step-INST i MT MA sigs))))
		  (not (retire-stg-p (INST-stg (step-INST i MT MA sigs)))))
	     (equal (inst-start-specultv? (step-INST i MT MA sigs))
		    (inst-start-specultv? i)))
  :hints (("Goal" :in-theory (enable inst-start-specultv? lift-b-ops))))

(encapsulate nil
(local
(defthm MT-inst-specultv-if-INST-start-specultv-help
    (implies (and (member-equal i trace)
		  (b1p (INST-start-specultv? i)))
	     (equal (trace-specultv? trace) 1))
  :hints (("goal" :in-theory (enable lift-b-ops equal-b1p-converter)))))

(defthm MT-inst-specultv-if-INST-start-specultv
    (implies (and (INST-in i MT) (b1p (INST-start-specultv? i)))
	     (equal (MT-specultv? MT) 1))
  :hints (("goal" :in-theory (enable MT-specultv? INST-in))))

)

(encapsulate nil
(local
(defthm MT-specultv-MT-step-if-INST-specultv-help
    (implies (and (b1p (inst-specultv? i))
		  (member-equal i trace)
		  (not (b1p (flush-all? MA sigs))))
	     (equal (trace-specultv? (step-trace trace MT MA sigs
						 ISA spc smc))
		    1))
  :hints (("goal" :in-theory (enable flush-all? lift-b-ops
				     equal-b1p-converter
				     INST-cause-jmp? INST-exintr-now?
				     ex-intr?)))))

(defthm MT-specultv-MT-step-if-INST-specultv
    (implies (and (b1p (inst-specultv? i))
		  (INST-in i MT)
		  (not (b1p (flush-all? MA sigs))))
	     (equal (MT-specultv? (MT-step MT MA sigs)) 1))
  :hints (("Goal" :in-theory (enable MT-specultv? MT-step
				     INST-in))))
)

(defthm not-commit-stg-step-inst-if-inst-specultv
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i) 
		  (b1p (inst-specultv? i))
		  (not (committed-p i))
		  (MA-state-p MA) (MAETT-p MT) (MA-input-p sigs))
	     (not (commit-stg-p (INST-stg (step-inst i MT MA sigs)))))
  :hints (("Goal" :use (:instance inst-is-at-one-of-the-stages)
		  :in-theory (disable INST-is-at-one-of-the-stages))))

(defthm not-retire-stg-step-inst-if-inst-specultv
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i) 
		  (MAETT-p MT) (MA-state-p MA)
		  (b1p (inst-specultv? i)))
	     (not (retire-stg-p (INST-stg (step-INST i MT MA sigs)))))
  :hints (("Goal" :use ((:instance stages-reachable-to-retire-stg))
		  :in-theory (enable NOT-INST-SPECULTV-INST-IN-IF-COMMITTED))))

(defthm not-committed-p-step-inst-if-inst-specultv
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i)
		  (not (committed-p i))
		  (b1p (inst-specultv? i))
		  (MA-state-p MA) (MAETT-p MT) (MA-input-p sigs))
	     (not (committed-p (step-inst i MT MA sigs))))
  :hints (("Goal" :in-theory (enable committed-p))))

(encapsulate nil
; If a complete instruction i causes an exception, i does not advance to
; commit stage.
(local
(defthm not-commit-stg-p-step-INST-if-inst-excpt
    (implies (and (inv MT MA)
		  (complete-stg-p (INST-stg i))
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-p i) (INST-in i MT)
		  (not (b1p (inst-specultv? i)))
		  (not (b1p (INST-modified? i)))
		  (b1p (INST-excpt? I)))
	     (not (commit-stg-p (INST-stg (step-INST i MT MA sigs)))))
  :hints (("goal" :in-theory (enable step-inst-opener step-inst-complete
				     lift-b-ops)))))

(local
(defthm not-commit-stg-p-step-INST-if-stg-is-complete
    (implies (and (INST-p I)
		  (equal (INST-stg i) '(complete)))
	     (not (commit-stg-p (INST-stg (step-INST i MT MA sigs)))))
  :Hints (("Goal" :in-theory (enable MT-def)))))

(local
(defthm not-commit-stg-p-step-INST-if-inst-wrong-branch
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-p i) (INST-in i MT)
		  (not (b1p (inst-specultv? i)))
		  (not (b1p (INST-modified? i)))
		  (complete-stg-p (INST-stg i))
		  (b1p (INST-wrong-branch? I)))
	     (not (commit-stg-p (INST-stg (step-INST i MT MA sigs)))))
  :hints (("Goal" :cases ((b1p (INST-BU? i)))
		  :in-theory (enable complete-stg-p)))))

(local
(defthm not-commit-stg-p-step-INST-if-inst-context-sync
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-p I) (INST-in I MT)
		  (not (b1p (inst-specultv? i)))
		  (not (b1p (INST-modified? i)))
		  (complete-stg-p (INST-stg i))
		  (b1p (INST-context-sync? I)))
	     (not (commit-stg-p (INST-stg (step-INST i MT MA sigs)))))
  :hints (("goal" :in-theory (enable complete-stg-p INST-context-sync?
				     lift-b-ops)))))

; A completed instruction which starts speculative execution does not
; advance to the commit stage.  A store instruction which is committed
; but whose memory write is not completed can be in the commit stage.
(defthm not-commit-stg-p-step-INST-if-inst-start-specultv
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (MA-input-p sigs)
		  (INST-p I) (INST-in i MT)
		  (not (b1p (inst-specultv? i)))
		  (not (b1p (INST-modified? i)))
		  (complete-stg-p (INST-stg i))
		  (b1p (inst-start-specultv? i))		  )
	     (not (commit-stg-p (INST-stg (step-INST i MT MA sigs)))))
  :hints (("Goal" :in-theory (enable inst-start-specultv? lift-b-ops))))
)

(encapsulate nil
; Instruction i does not cause a jump in this cycle, and i is an
; exception causing instruction (not an ordinary memory write operation),
; then i does not advance to retire stage from the complete stage.
; (because jumping to the exception vector is detected by INST-cause-jmp?.)
(local
(defthm not-retire-without-INST-cause-jmp-if-INST-excpt
    (implies (and (inv MT MA)
		  (MA-state-p MA) (MAETT-p MT)
		  (INST-p i)
		  (INST-in i MT)
		  (not (b1p (inst-specultv? i)))
		  (not (b1p (INST-modified? i)))
		  (complete-stg-p (INST-stg i))
		  (b1p (INST-excpt? i))
		  (not (b1p (INST-cause-jmp? i MT MA sigs))))
	     (not (retire-stg-p (INST-stg (step-INST i MT MA sigs)))))
  :hints (("goal" :in-theory (enable step-INST-opener
				     step-INST-complete
				     inst-commit?
				     enter-excpt?
				     commit-inst?
				     complete-stg-p
				     INST-cause-jmp?
				     lift-b-ops)))))

; Similar lemma for the case where instruction i is a mispredicted branch.
(local
(defthm not-retire-without-INST-cause-jmp-if-INST-wrong-branch
    (implies (and (inv MT MA)
		  (MA-state-p MA) (MAETT-p MT)
		  (INST-p i)
		  (INST-in i MT)
		  (complete-stg-p (INST-stg i))
		  (not (b1p (inst-specultv? i)))
		  (not (b1p (INST-modified? i)))
		  (b1p (INST-wrong-branch? i))
		  (not (b1p (INST-cause-jmp? i MT MA sigs))))
	     (not (retire-stg-p (INST-stg (step-INST i MT MA sigs)))))
  :hints (("goal" :in-theory (enable step-INST-opener
				     step-INST-complete
				     inst-commit?
				     enter-excpt?
				     inst-wrong-branch?
				     commit-jmp?
				     commit-inst?
				     complete-stg-p
				     exception-relations
				     INST-cause-jmp?
				     lift-b-ops)))))

; Lemma for the case where instruction i is an context synchronization
; instruction.
(local
(defthm not-retire-without-INST-cause-jmp-if-INST-context-sync
    (implies (and (inv MT MA)
		  (MA-state-p MA) (MAETT-p MT)
		  (INST-p i)
		  (INST-in i MT)
		  (complete-stg-p (INST-stg i))
		  (b1p (INST-context-sync? i))
		  (not (b1p (inst-specultv? i)))
		  (not (b1p (INST-modified? i)))
		  (not (b1p (INST-cause-jmp? i MT MA sigs))))
	     (not (retire-stg-p (INST-stg (step-INST i MT MA sigs)))))
  :hints (("goal" :in-theory
		  (enable step-INST-opener
			  step-INST-complete
			  inst-commit?
			  inst-context-sync?
			  INST-excpt?
			  commit-jmp?
			  commit-inst?
			  complete-stg-p
			  exception-relations
			  INST-fetch-error-detected-p-iff-INST-fetch-error?
			  INST-decode-error-detected-p-iff-INST-decode-error?
			  INST-cause-jmp?
			  lift-b-ops)))))

(defthm not-retire-stg-p-step-INST-if-not-INST-cause-jmp?
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-p I) (INST-in i MT) 
		  (complete-stg-p (INST-stg i))
		  (b1p (inst-start-specultv? i))
		  (not (b1p (inst-specultv? i)))
		  (not (b1p (INST-modified? i)))
		  (not (b1p (INST-cause-jmp? i MT MA sigs))))
	     (not (retire-stg-p (INST-stg (step-INST i MT MA sigs)))))
  :hints (("Goal" :in-theory (enable inst-start-specultv? lift-b-ops))))
)

(defthm not-committed-p-step-INST-if-not-INST-cause-jmp?
    (implies (and (inv MT MA)
		  (MAETT-p MT) (MA-state-p MA) (MA-input-p sigs)
		  (INST-p I) (INST-in i MT) 
		  (complete-stg-p (INST-stg i))
		  (b1p (inst-start-specultv? i))
		  (not (b1p (inst-specultv? i)))
		  (not (b1p (INST-modified? i)))
		  (not (b1p (INST-cause-jmp? i MT MA sigs))))
	     (not (committed-p (step-INST i MT MA sigs))))
  :hints (("goal" :in-theory (enable committed-p))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Lemmas about MT-self-modify
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(encapsulate nil
(local
(defthm MT-self-modify-if-INST-in-modified-help
    (implies (and (b1p (INST-modified? i))
		  (member-equal i trace))
	     (equal (trace-self-modify? trace) 1))
  :hints (("goal" :in-theory (enable lift-b-ops equal-b1p-converter)))))

(defthm MT-self-modify-if-INST-in-modified
    (implies (and (b1p (INST-modified? i))
		  (INST-in i MT))
	     (equal (MT-self-modify? MT) 1))
  :Hints (("goal" :in-theory (enable MT-self-modify? INST-in))))
)
(defthm  INST-modified-car-if-not-MT-self-modify
    (implies (and (inv MT MA)
		  (not (b1p (MT-self-modify? MT)))
		  (subtrace-p trace MT)
		  (INST-listp trace) (consp trace)
		  (MAETT-p MT) (MA-state-p MA))
	     (equal (INST-modified? (car trace)) 0))
  :hints (("goal" :in-theory (enable equal-b1p-converter))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;  Lemmas about MT-CMI-p
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(encapsulate nil
(local
(defthm MT-CMI-p-if-INST-modified-help
    (implies (and (inv MT MA)
		  (subtrace-p trace MT)
		  (b1p (INST-modified? i))
		  (committed-p i)
		  (member-equal i trace)
		  (INST-p i) (INST-listp trace) (MAETT-p MT) (MA-state-p MA)) 
	     (trace-CMI-p trace))))

(defthm MT-CMI-p-if-INST-modified
    (implies (and (inv MT MA)
		  (b1p (INST-modified? i))
		  (committed-p i)
		  (INST-in i MT) (MAETT-p MT) (MA-state-p MA))
	     (MT-CMI-p MT))
  :hints (("goal" :in-theory (enable INST-in MT-CMI-p))))
)

(encapsulate nil
(local
 (defthm MT-CMI-p-MT-step-help
     (implies (and (MA-state-p MA)
		   (MA-input-p sigs)
		   (MAETT-p MT)
		   (INST-listp trace)
		   (subtrace-p trace MT)
		   (trace-CMI-p trace))
	      (trace-CMI-p (step-trace trace MT MA sigs
				       pre spc smc)))
   :hints (("Goal" :in-theory (enable INST-EXINTR-NOW? INST-cause-jmp?
				      lift-b-ops))))
 )

(defthm MT-CMI-p-MT-step
    (implies (and (MT-CMI-p MT)
		  (MAETT-p MT)
		  (MA-state-p MA)
		  (MA-input-p sigs))
	     (MT-CMI-p (MT-step MT MA sigs)))
  :hints (("Goal" :in-theory (enable MT-CMI-p MT-step))))
)

(defthm commit-self-modified-p-MT-stepn
    (implies (and (MT-CMI-p MT)
		  (MAETT-p MT)
		  (MA-state-p MA)
		  (MA-input-listp sigs-lst)
		  (<= n (len sigs-lst)))
	     (MT-CMI-p (MT-stepn MT MA sigs-lst n))))

(defthm INST-exintr-now-INST-commit-exclusive
    (implies (and (inv MT MA)
		  (b1p (INST-commit? i MA))
		  (INST-in i MT) (INST-p i)
		  (INST-in j MT) (INST-p j)
		  (MAETT-p MT) (MA-state-p MA))
	     (equal (INST-exintr-now? j MA sigs) 0))
  :hints (("goal" :in-theory (enable INST-exintr-now? INST-commit?
				     lift-b-ops equal-b1p-converter)
		  :restrict ((NOT-ROB-EMPTY-IF-INST-IS-EXECUTED
			      ((i i)))))))
(in-theory (disable INST-exintr-now-INST-commit-exclusive))

(encapsulate nil

(local
(defthm not-INST-cause-jmp-if-another-INST-commit
    (implies (and (inv MT MA)
		  (b1p (INST-commit? i MA))
		  (INST-in i MT) (INST-p i) (INST-in j MT) (INST-p j)
		  (not (equal i j))
		  (MAETT-p MT) (MA-state-p MA))
	     (equal (INST-cause-jmp? j MT MA sigs) 0))
  :hints (("goal" :in-theory (enable INST-cause-jmp? INST-commit?
				     lift-b-ops equal-b1p-converter)))))

(local
 (defthm MT-CMI-p-if-modified-INST-commit-help
     (implies (and (inv MT MA)
		   (b1p (INST-commit? j MA))
		   (INST-in-order-p i j MT)
		   (not (commit-stg-p (INST-stg (step-INST i MT MA sigs))))
		   (INST-in i MT) (INST-p i) (INST-in j MT) (INST-p j)
		   (MAETT-p MT) (MA-state-p MA))
	      (retire-stg-p (INST-stg (step-INST i MT MA sigs))))
   :hints (("goal" :cases ((committed-p i))
		   :in-theory (enable committed-p inst-commit?
				      lift-b-ops)))))

(local
(defthm MT-CMI-p-if-modified-INST-commit-induct
    (implies (and (inv MT MA)
		  (subtrace-p trace MT)
		  (member-equal i trace) (INST-p i)
		  (INST-listp trace)
		  (b1p (INST-modified? i))
		  (b1p (INST-commit? i MA))
		  (MAETT-p MT) (MA-state-p MA))
	     (trace-CMI-p (step-trace trace MT MA sigs
				      isa spc smc)))
  :hints (("goal" :in-theory
		  (enable NOT-INST-COMMIT-IF-EARLIER-INST-NOT-COMMITTED
			  INST-exintr-now-INST-commit-exclusive
			  committed-p)
		  :restrict ((NOT-INST-COMMIT-IF-EARLIER-INST-NOT-COMMITTED
			      ((i (car trace)))))))))

(defthm MT-CMI-p-if-modified-INST-commit
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i)
		  (b1p (INST-modified? i))
		  (b1p (INST-commit? i MA))
		  (MAETT-p MT) (MA-state-p MA))
	     (MT-CMI-p (MT-step MT MA sigs)))
  :hints (("goal" :in-theory (enable MT-CMI-p
				     INST-in
				     MT-step))))
)

(defthm not-retire-stg-step-inst-if-INST-modified
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i) 
		  (MAETT-p MT) (MA-state-p MA)
		  (MA-input-p sigs)
		  (not (MT-CMI-p (MT-step MT MA sigs)))
		  (b1p (INST-modified? i)))
	     (not (retire-stg-p (INST-stg (step-INST i MT MA sigs)))))
  :hints (("Goal" :use ((:instance stages-reachable-to-retire-stg))
		  :in-theory (enable inst-stg-step-inst lift-b-ops))))
;;;;;
;;;;Misc lemmas about inst-exintr-now?
(defthm IFU-or-DQ-stg-if-inst-exintr-now
    (implies (and (not (IFU-stg-p (INST-stg i)))
		  (not (DQ-stg-p (INST-stg i))))
	     (not (b1p (inst-exintr-now? i MA sigs))))
  :hints (("Goal" :in-theory (enable inst-exintr-now? lift-b-ops))))

(defthm inst-cause-jmp-inst-exintr-now-exclusive
    (implies (and (INST-p i) (b1p (inst-cause-jmp? i MT MA sigs)))
	     (not (b1p (inst-exintr-now? i MA sigs))))
  :hints (("goal" :use (:instance INST-is-at-one-of-the-stages)
		  :in-theory (disable INST-is-at-one-of-the-stages))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; MT-specultv-at-dispatch?
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(encapsulate nil
(local
(defthm local-help1
    (implies (and (inv MT MA)
		  (subtrace-p trace MT) (INST-listp trace) 
		  (not (dispatched-p i))
		  (member-equal i trace) (INST-p i)
		  (not (b1p (inst-specultv? i)))
		  (MAETT-p MT) (MA-state-p MA))
	     (not (b1p (trace-specultv-at-dispatch? trace))))
  :hints (("goal" :in-theory (enable INST-START-SPECULTV-CAR)))))

; If a non-dispatched instruction is not speculatively executed,
; currently no dispatched instructions are speculatively executed. 
(defthm MT-specultv-at-dispatch-off-if-non-specultv-inst-in
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i)
		  (not (dispatched-p i))
		  (not (b1p (inst-specultv? i)))
		  (MAETT-p MT) (MA-state-p MA))
	     (equal (MT-specultv-at-dispatch? MT) 0))
  :hints (("Goal" :in-theory (enable MT-specultv-at-dispatch?
				     equal-b1p-converter INST-in))))
)
(in-theory (disable MT-specultv-at-dispatch-off-if-non-specultv-inst-in))

(encapsulate nil
(local
(defthm local-help
    (implies (and (inv MT MA)
		  (subtrace-p trace MT) (INST-listp trace) 
		  (member-equal i trace) (INST-p i) 
		  (not (dispatched-p i))
		  (not (b1p (INST-modified? i)))
		  (MAETT-p MT) (MA-state-p MA)) 
	     (equal (trace-modified-at-dispatch? trace) 0))))

(defthm INST-modified-at-dispatch-off-if-undispatched-inst-in
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i) 
		  (not (dispatched-p i))
		  (not (b1p (INST-modified? i)))
		  (MAETT-p MT) (MA-state-p MA)) 
	     (equal (MT-modified-at-dispatch? MT) 0))
  :hints (("Goal" :in-theory (enable MT-modified-at-dispatch? INST-in))))
)
(in-theory (disable INST-modified-at-dispatch-off-if-undispatched-inst-in))

; If an instruction i is dispatched, but not yet committed, it is not
; speculatively executed, and if flush-all?  is not true, then the
; value of INST-start-specultv?  won't change.  If the instruction is
; at the execute stage, this is true from the definition of
; INST-start-specultv?.  If it is at complete-stg-p, the instruction
; will not retire because flush-all? is 0.
(defthm INST-start-specultv-if-not-flush-all
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i) 
		  (dispatched-p i)
		  (not (committed-p i))
		  (not (b1p (flush-all? MA sigs)))
		  (not (b1p (inst-specultv? i)))
		  (not (MT-CMI-p (MT-step MT MA sigs)))
		  (MAETT-p MT) (MA-state-p MA) (MA-input-p sigs))
	     (equal (INST-start-specultv? (step-INST i MT MA sigs))
		    (INST-start-specultv? i)))
  :hints (("Goal" :in-theory (e/d (dispatched-p committed-p
				     equal-b1p-converter)
				  (inst-is-at-one-of-the-stages))
		  :cases ((b1p (INST-modified? i))))
	  ("subgoal 1" :cases ((committed-p (step-INST i MT MA sigs))))
	  ("subgoal 1.1" :in-theory (e/d (dispatched-p committed-p
					    step-inst-low-level-functions
					    step-inst-complete-inst
					    lift-b-ops
					    equal-b1p-converter
				     step-inst-complete-inst)
				  (inst-is-at-one-of-the-stages)))))

(encapsulate nil
(local
(defthm MT-specultv-at-dispatch-MT-step-help-help 
    (implies (and (inv MT MA)
		  (INST-in i MT) (INST-p i) 
		  (not (committed-p i))
		  (b1p (INST-start-specultv? i))
		  (not (b1p (flush-all? MA sigs)))
		  (not (MT-CMI-p (MT-step MT MA sigs)))
		  (MAETT-p MT) (MA-state-p MA) (MA-input-p sigs))
	     (not (committed-p (step-INST i MT MA sigs))))
  :hints (("Goal" :cases ((b1p (inst-specultv? i))
			  (b1p (INST-modified? i)))
		  :in-theory (e/d ( step-inst-complete-inst
				     step-inst-low-level-functions
				     lift-b-ops
				     committed-p*)
				  (INST-IS-AT-ONE-OF-THE-STAGES))))))

(local
(defthm MT-specultv-at-dispatch-MT-step-help
    (implies (and (inv MT MA)
		  (subtrace-p trace MT) (INST-listp trace)
		  (not (MT-CMI-p (MT-step MT MA sigs)))
		  (b1p (trace-specultv-at-dispatch? trace))
		  (not (b1p (flush-all? MA sigs)))
		  (MAETT-p MT) (MA-state-p MA) (MA-input-p sigs))
	     (equal (trace-specultv-at-dispatch?
		     (step-trace trace MT MA sigs ISA spc smc))
		    1))
  :hints (("Goal" :in-theory (e/d (lift-b-ops)
				  (INST-IS-AT-ONE-OF-THE-STAGES))))))

; If we are dispatching instructions speculatively in the current cycle, 
; and if flush-all? is not true, we are still dispatching speculatively
; in the next cycle.
(defthm MT-specultv-at-dispatch-MT-step
    (implies (and (inv MT MA)
		  (b1p (MT-specultv-at-dispatch? MT))
		  (not (MT-CMI-p (MT-step MT MA sigs)))
		  (not (b1p (flush-all? MA sigs)))
		  (MAETT-p MT) (MA-state-p MA) (MA-input-p sigs))
	     (equal (MT-specultv-at-dispatch? (MT-step MT MA sigs)) 1))
  :hints (("Goal" :in-theory (enable MT-specultv-at-dispatch?))))
)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; MT-no-jmp-exintr-before
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; We define a predicate to check whether instructions are abandoned by
; branching, exceptions, and other context synchronizing events.
; (MT-no-jmp-exintr-before i MT MA sigs) returns nil if a committing
; instruction which appears earlier than instruction i in MT is either
; a mispredicted branch, an external or internal exception, or other
; instructions that makes machine synchronize.  For instance, return
; from exception handling.
; (MT-no-jmp-exintr-before-trace sub MT MA sigs) checks if there appears
; such an instruction before a terminating list, sub, of MAETT, MT.
; Lemma MT-no-jmp-exintr-before-INST-and-trace shows the relation of
; these two predicates.

(defun trace-no-jmp-exintr-before (i trace MT MA sigs)
  (declare (xargs :guard (and (INST-p i) (INST-listp trace)
			      (MAETT-p MT) (MA-state-p MA)
			      (MA-input-p sigs))))
  (if (endp trace)
      t
      (if (equal i (car trace))
	  t
	  (if (or (b1p (INST-cause-jmp? (car trace) MT MA sigs))
		  (b1p (INST-exintr-now? (car trace) MA sigs)))
	      nil
	      (trace-no-jmp-exintr-before i (cdr trace) MT MA sigs)))))

(defun MT-no-jmp-exintr-before (i MT MA sigs)
  (declare (xargs :guard (and (INST-p i) (MAETT-p MT) (MA-state-p MA)
			      (MA-input-p sigs))))
  (trace-no-jmp-exintr-before i (MT-trace MT) MT MA sigs))

(in-theory (disable MT-no-jmp-exintr-before))

(encapsulate nil
(local
(defthm MT-no-jmp-exintr-before-cadr-help
    (implies (and (consp trace)
		  (consp (cdr trace))
		  (distinct-member-p trace2)
		  (not (b1p (INST-cause-jmp? (car trace) MT MA sigs)))
		  (not (b1p (INST-exintr-now? (car trace) MA sigs)))
		  (tail-p trace trace2)
		  (trace-no-jmp-exintr-before (car trace) trace2
						    MT MA sigs))
	     (trace-no-jmp-exintr-before (cadr trace) trace2 MT MA sigs))
  :hints (("goal" :in-theory (enable MT-no-jmp-exintr-before)))))

(defthm MT-no-jmp-exintr-before-cadr
    (implies (and (weak-inv MT)
		  (consp trace) 
		  (consp (cdr trace))
		  (not (b1p (INST-cause-jmp? (car trace) MT MA sigs)))
		  (not (b1p (INST-exintr-now? (car trace) MA sigs)))
		  (subtrace-p trace MT)
		  (MT-no-jmp-exintr-before (car trace) MT MA sigs))
	     (MT-no-jmp-exintr-before (cadr trace) MT MA sigs))
  :hints (("goal" :in-theory (enable MT-no-jmp-exintr-before subtrace-p
				     weak-inv MT-distinct-INST-p
				     ))))
)

(defthm MT-no-jmp-exintr-before-car-MT-trace
    (MT-no-jmp-exintr-before (car (MT-trace MT)) MT MA sigs)
  :hints (("goal" :in-theory (enable MT-no-jmp-exintr-before))))

(defun trace-no-jmp-exintr-before-trace (sub trace MT MA sigs)
  (declare (xargs :guard (and (INST-listp sub) (INST-listp trace) (MAETT-p MT)
			      (MA-state-p MA) (MA-input-p sigs))))
  (if (endp trace)
      t
      (if (equal sub trace)
	  t
	  (if (or (b1p (INST-cause-jmp? (car trace) MT MA sigs))
		  (b1p (INST-exintr-now? (car trace) MA sigs)))
	      nil
	      (trace-no-jmp-exintr-before-trace sub (cdr trace) MT MA sigs)))))

(defun MT-no-jmp-exintr-before-trace (trace MT MA sigs)
  (declare (xargs :guard (and (INST-listp trace) (MAETT-p MT)
			      (MA-state-p MA) (MA-input-p sigs))))
  (trace-no-jmp-exintr-before-trace trace (MT-trace MT) MT MA sigs))

(in-theory (disable MT-no-jmp-exintr-before-trace))

(encapsulate nil
(local
(defthm MT-no-jmp-exintr-before-cdr-help
    (implies (and (consp trace) 
		  (distinct-member-p trace2)
		  (not (b1p (INST-cause-jmp? (car trace) MT MA sigs)))
		  (not (b1p (INST-exintr-now? (car trace) MA sigs)))
		  (tail-p trace trace2)
		  (trace-no-jmp-exintr-before-trace trace trace2 MT MA sigs))
	     (trace-no-jmp-exintr-before-trace (cdr trace) trace2 MT MA sigs))
  :hints (("goal" :in-theory (enable MT-no-jmp-exintr-before-trace)))))

(defthm MT-no-jmp-exintr-before-cdr
    (implies (and (weak-inv MT)
		  (consp trace) 
		  (not (b1p (INST-cause-jmp? (car trace) MT MA sigs)))
		  (not (b1p (INST-exintr-now? (car trace) MA sigs)))
		  (subtrace-p trace MT)
		  (MT-no-jmp-exintr-before-trace trace MT MA sigs))
	     (MT-no-jmp-exintr-before-trace (cdr trace) MT MA sigs))
  :hints (("goal" :in-theory (enable MT-no-jmp-exintr-before-trace subtrace-p
				     weak-inv MT-distinct-INST-p))))
)

(defthm MT-no-jmp-exintr-before-trace-MT-trace
    (MT-no-jmp-exintr-before-trace (MT-trace MT) MT MA sigs)
  :hints (("goal" :in-theory (enable MT-no-jmp-exintr-before-trace))))

(defthm MT-no-jmp-exintr-before-INST-and-trace-help
    (implies (and (distinct-member-p trace)
		  (tail-p sub trace)
		  (consp sub))
	     (iff (trace-no-jmp-exintr-before (car sub) trace MT MA sigs)
		  (trace-no-jmp-exintr-before-trace sub trace MT MA sigs))))

(defthm MT-no-jmp-exintr-before-INST-and-trace
    (implies (and (weak-inv MT)
		  (subtrace-p trace MT)
		  (consp trace))
	     (iff (MT-no-jmp-exintr-before (car trace) MT MA sigs)
		  (MT-no-jmp-exintr-before-trace trace MT MA sigs)))
  :hints (("goal" :in-theory (enable MT-no-jmp-exintr-before
				     MT-no-jmp-exintr-before-trace
				     weak-inv
				     subtrace-p
				     MT-distinct-INST-p))))


(deftheory INST-exunit-relations
    '(INST-sync-INST-BU-exclusive-2      NOT-INST-RFEH-IF-INST-LSU?
      NOT-INST-WB-SREG-IF-INST-LSU?      NOT-INST-SYNC-IF-INST-LSU?
      INST-writeback-p-INST-BU-exclusive))

(in-theory (disable INST-exunit-relations))
