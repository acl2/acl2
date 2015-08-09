(in-package "ACL2")

;(include-book "utils")
(include-book "basic-def")
(include-book "model")
(include-book "table-def")

(deflabel begin-basic-lemmas)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;  Proof of misc lemmas
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Lemmas about bv-eqv
(defthm bv-eqv-opcode-p
    (implies (and (opcd-p x) (opcd-p y))
	     (equal (b1p (bv-eqv *opcode-size* x y)) (equal x y)))
  :hints (("goal" :in-theory (enable opcd-p))))

(defthm bv-eqv-rname-p
    (implies (and (rname-p x) (rname-p y))
	     (equal (b1p (bv-eqv *opcode-size* x y)) (equal x y)))
  :hints (("goal" :in-theory (enable rname-p))))


; Lemmas about the projection from an MA state to an ISA state.
(defthm ISA-pc-proj
    (equal (ISA-pc (proj MA)) (MA-pc MA))
  :hints (("Goal" :in-theory (enable proj))))

(defthm ISA-regs-proj
    (equal (ISA-regs (proj MA)) (MA-regs MA))
  :hints (("Goal" :in-theory (enable proj))))

(defthm ISA-mem-proj
    (equal (ISA-mem (proj MA)) (MA-mem MA))
  :hints (("Goal" :in-theory (enable proj))))

; (tail-p sublist list) is true if sublist is a terminating sub-list
; of list.  For instance, (tail-p '(1 2 3 4) '(3 4)) is T, while
; (tail-p '(1 2 3 4) '(2 3)) is nil.
(defun tail-p (sublist list)
  (declare (xargs :guard (and (true-listp sublist) (true-listp list))))
  (if (equal sublist list)
      T
    (if (endp list)
	nil
      (tail-p sublist (cdr list)))))

; Basic lemmas bout tail-p.
(defthm tail-p-cdr-1
    (implies (and (consp sub) (tail-p sub lst))
	     (tail-p (cdr sub) lst)))

(defthm tail-p-cdr-2
    (implies (consp lst) (not (tail-p lst (cdr lst))))
  :hints (("Goal" :induct (len lst))))

; (INST-in i MT) is T, if MT contains i as an instruction entry.
(defun INST-in (i MT)
  (member-equal i (MT-trace MT)))

; (subtrace-p trace MT) is T if trace is a terminating sub-list of
; the list of instruction entries in MT.   Since MT stores
; instruction entries in ISA execution order, trace is a list of
; entries representing most recently fetched instructions.
(defun subtrace-p (trace MT)
  (declare (xargs :guard (and (INST-listp trace) (MAETT-p MT))))
  (tail-p trace (MT-trace MT)))

(in-theory (disable INST-in subtrace-p))

(defthm subtrace-p-MT-trace
    (subtrace-p (MT-trace MT) MT)
  :hints (("Goal" :in-theory (enable subtrace-p))))

(defthm subtrace-p-cdr
    (implies (and (subtrace-p trace MT) (consp trace))
	     (subtrace-p (cdr trace) MT))
  :hints (("goal" :in-theory (enable subtrace-p))))

(encapsulate nil
(local
(defthm inst-in-car-subtrace-induction
    (implies (and (consp sub) (tail-p sub trace))
	     (member-equal (car sub) trace))))

(defthm inst-in-car-subtrace
    (implies (and  (consp trace) (subtrace-p trace MT))
	     (INST-in (car trace) MT))
  :hints (("Goal" :in-theory (enable INST-in subtrace-p))))
)

; ISA-at-tail is used in the definition of ISA-before
(defun ISA-at-tail (sub trace pre)
  (declare (xargs :guard (and (INST-listp sub) (INST-listp trace)
			      (ISA-state-p pre))))
  (if (equal sub trace)
      pre
      (if (endp trace) pre
	  (ISA-at-tail sub (cdr trace) (INST-post-ISA (car trace))))))

(defthm ISA-state-p-ISA-at-tail
    (implies (and (ISA-state-p pre)
		  (INST-listp trace))
	     (ISA-state-p (ISA-at-tail sub trace pre))))

; (ISA-before sub MT) returns the ISA state before the execution of
; the first instruction in sub.  For instance, MT represents
; instructions I_1, I_2, I_3 and I_4.  If sub = (I_3 I_4), then
; (ISA-before sub MT) returns ISA state before executing I_3.  If sub is nil,
; (ISA-before sub MT) returns the ISA state after executing all instructions
; represented in MT.
(defun ISA-before (sub MT)
  (declare (xargs :guard (and (INST-listp sub) (MAETT-p MT))))
  (ISA-at-tail sub (MT-trace MT) (MT-init-ISA MT)))

(in-theory (disable ISA-before))

(defthm ISA-state-p-ISA-before
    (implies (MAETT-p MT)
	     (ISA-state-p (ISA-before sub MT)))
  :hints (("goal" :in-theory (enable ISA-before))))

(defthm ISA-before-MT-trace
    (equal (ISA-before (MT-trace MT) MT)
	   (MT-init-ISA MT))
  :hints (("Goal" :in-theory (enable ISA-before))))

(encapsulate nil
(defthm ISA-before-cdr-induction
    (implies (and (tail-p sub trace)
		  (consp sub))
	     (equal (ISA-at-tail (cdr sub) trace ISA)
		    (INST-post-ISA (car sub)))))

(defthm ISA-before-cdr
    (implies (and (subtrace-p sub MT)
		  (consp sub))
	     (equal (ISA-before (cdr sub) MT)
		    (INST-post-ISA (car sub))))
  :hints (("Goal" :in-theory (enable ISA-before subtrace-p))))
)

(encapsulate nil
(local
(defthm INST-p-INST-at-induction
    (implies (and (INST-listp trace) (trace-INST-at stg trace))
	     (INST-p (trace-INST-at stg trace)))))

; INST-p-INST-at asserts that (INST-at stg MT) is of type INST-p if
; there exists an instruction at stage stg.  (INST-at stg MT) is
; nil if MT does not contains an entry representing an instruction at
; stage stg.
(defthm INST-p-INST-at
    (implies (and (MAETT-p MT) (INST-at stg MT))
	     (INST-p (INST-at stg MT)))
  :hints (("Goal" :in-theory (enable INST-p INST-at))))
)

(encapsulate nil
(local
(defthm INST-in-INST-at-induction
    (implies (trace-INST-at stg trace)
	     (member-equal (trace-INST-at stg trace) trace))))

; (INST-at stg MT) is an instruction entry in MT, unless it is nil.
(defthm INST-in-INST-at
    (implies (INST-at stg MT)
	     (INST-in (INST-at stg MT) MT))
  :hints (("Goal" :in-theory (enable INST-at INST-in))))
)


(encapsulate nil
(local
(defthm INST-stg-INST-at-induction
    (implies (trace-INST-at stg trace)
	     (equal (INST-stg (trace-INST-at stg trace)) stg))))

; Stage of (INST-at stg MT).
(defthm INST-stg-INST-at
    (implies (INST-at stg MT) (equal (INST-stg (INST-at stg MT)) stg))
  :hints (("Goal" :in-theory (enable INST-at))))
)

; Memory is not updated by our machine.
(defthm ISA-mem-ISA-step
    (equal (ISA-mem (ISA-step ISA)) (ISA-mem ISA))
  :hints (("Goal" :in-theory (enable ISA-step ISA-add ISA-sub ISA-default))))

(defthm ISA-mem-ISA-stepn
    (equal (ISA-mem (ISA-stepn ISA n)) (ISA-mem ISA)))

; Various small lemmas about attributes of instructions.  I don't
; comment each of them.  Most of them are trivial from the definition
; of the instruction attributes and the definition of step-INST.
(defthm INST-word-new-INST
    (equal (INST-word (new-INST ISA))
	   (read-mem (ISA-pc ISA) (ISA-mem ISA)))
  :hints (("Goal" :in-theory (enable new-INST INST-word))))

(defthm INST-stg-new-INST
    (equal (INST-stg (new-INST ISA)) 'latch1)
  :hints (("Goal" :in-theory (enable new-INST))))

(defthm INST-pre-ISA-new-INST
    (equal (INST-pre-ISA (new-INST ISA)) ISA)
  :hints (("Goal" :in-theory (enable new-INST))))

(defthm INST-post-ISA-new-INST
    (equal (INST-post-ISA (new-INST ISA)) (ISA-step ISA))
  :hints (("Goal" :in-theory (enable new-INST))))

(defthm INST-word-step-INST
    (implies (INST-p i)
	     (equal (INST-word (step-INST i MA)) (INST-word i)))
  :hints (("Goal" :in-theory (enable step-INST step-latch1-INST
				     INST-word step-latch2-INST))))

(defthm INST-op-step-INST
    (implies (INST-p i)
	     (equal (INST-op (step-INST i MA)) (INST-op i)))
  :hints (("Goal" :in-theory (enable INST-op))))

(defthm INST-rc-step-INST
    (implies (INST-p i)
	     (equal (INST-rc (step-INST i MA)) (INST-rc i)))
  :hints (("Goal" :in-theory (enable INST-rc))))

(defthm INST-ra-step-INST
    (implies (INST-p i)
	     (equal (INST-ra (step-INST i MA)) (INST-ra i)))
  :hints (("Goal" :in-theory (enable INST-ra))))

(defthm INST-rb-step-INST
    (implies (INST-p i)
	     (equal (INST-rb (step-INST i MA)) (INST-rb i)))
  :hints (("Goal" :in-theory (enable INST-rb))))


(defthm INST-pre-ISA-step-INST
    (implies (INST-p i)
	     (equal (INST-pre-ISA (step-INST i MA)) (INST-pre-ISA i)))
  :hints (("Goal" :in-theory (enable step-INST step-latch1-INST
				     step-latch2-INST))))

(defthm INST-post-ISA-step-INST
    (implies (INST-p i)
	     (equal (INST-post-ISA (step-INST i MA)) (INST-post-ISA i)))
  :hints (("Goal" :in-theory (enable step-INST step-latch1-INST
				     step-latch2-INST))))
(defthm INST-pre-ISA-car-MT-trace
    (implies (and (invariant MT MA)
		  (consp (MT-trace MT)))
	     (equal (INST-pre-ISA (car (MT-trace MT))) (MT-init-ISA MT)))
  :hints (("Goal" :in-theory (enable invariant ISA-chain-p))))


(defthm MT-init-ISA-init-MT
    (equal (MT-init-ISA (init-MT MA)) (proj MA))
  :hints (("Goal" :in-theory (enable init-MT))))

(defthm MT-init-ISA-MT-step
    (equal (MT-init-ISA (MT-step MT MA sig))
	   (MT-init-ISA MT))
  :hints (("goal" :in-theory (enable MT-step))))

(defthm MT-init-ISA-MT-stepn
    (equal (MT-init-ISA (MT-stepn MT MA sig n))
	   (MT-init-ISA MT)))


; In order to understand following several lemmas, you need to understand
; how INST-pre-ISA and INST-post-ISA make a chain of ISA states.
; Intuitively, (INST-pre-ISA i) is the ISA state before executing the
; instruction represented by i, and (INST-post-ISA i) is the ISA state
; after the execution.  Suppose we execute instruction I_0, I_1 and I_2
; in that order successively.  Equation
; (INST-post-ISA I_0) = (INST-pre-ISA I_1)
; holds because the resulting state of an instruction is a starting state
; for the immediately following instruction.   This relation can be
; described better with a picture shown below:
;   (INST-pre-ISA i_0)
;         |  execution of i_0
;         v
;   (INST-post-ISA i_0) = (INST-pre-ISA i_1)
;         |  execution of i_1
;         v
;   (INST-post-ISA i_1) = (INST-pre-ISA i_2)
;         ...
; The transition relation can be written as
;  (INST-post-ISA I_0) = (ISA-step (INST-pre-ISA I_0)).
(encapsulate nil
(local
(defthm INST-post-ISA-INST-in-induction
    (implies (and (member-equal i trace)
		  (ISA-chain-trace-p trace ISA)
		  (INST-p i))
	     (equal (INST-post-ISA i)
		    (ISA-step (INST-pre-ISA i))))))

(defthm INST-post-ISA-INST-in
    (implies (and (invariant MT MA)
		  (MAETT-p MT)
		  (INST-in i MT) (INST-p i))
	     (equal (INST-post-ISA i)
		    (ISA-step (INST-pre-ISA i))))
  :hints (("Goal" :in-theory (enable INST-in invariant ISA-chain-p))))
)


(encapsulate nil
(local
(defthm INST-post-ISA-car-subtrace-help
    (implies (and (ISA-chain-trace-p trace ISA)
		  (tail-p sub trace)
		  (consp sub)
		  (INST-listp trace))
	     (equal (INST-post-ISA (car sub))
		    (ISA-step (INST-pre-ISA (car sub)))))))

(defthm INST-post-ISA-car-subtrace
    (implies (and (invariant MT MA)
		  (subtrace-p trace MT)
		  (MAETT-p MT)
		  (consp trace)
		  (INST-listp trace))
	     (equal (INST-post-ISA (car trace))
		    (ISA-step (INST-pre-ISA (car trace)))))
  :hints (("goal" :in-theory (enable invariant subtrace-p
				     ISA-chain-p))))
)

(encapsulate nil
(local
(defthm INST-pre-ISA-cadr-subtrace-induction
    (implies (and (ISA-chain-trace-p trace ISA)
		  (tail-p sub trace)
		  (INST-listp trace)
		  (consp sub)
		  (consp (cdr sub)))
	     (equal (INST-pre-ISA (cadr sub))
		    (ISA-step (INST-pre-ISA (car sub)))))))

(defthm INST-pre-ISA-cadr-subtrace
    (implies (and (invariant MT MA)
		  (subtrace-p trace MT)
		  (MAETT-p MT)
		  (INST-listp trace)
		  (consp trace)
		  (consp (cdr trace)))
	     (equal (INST-pre-ISA (cadr trace))
		    (ISA-step (INST-pre-ISA (car trace)))))
  :hints (("goal" :in-theory (enable invariant ISA-chain-p subtrace-p))))
)

(encapsulate nil
(local
(defthm ISA-before-INST-pre-ISA-car-induction
    (implies (and (invariant MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-listp trace)
		  (subtrace-p trace MT)
		  (tail-p sub trace)
		  (consp sub))
     (equal (ISA-at-tail sub trace (INST-pre-ISA (car trace)))
	    (INST-pre-ISA (car sub))))
  :hints (("Subgoal *1/3" :cases ((consp (cdr trace)))))
  :rule-classes nil))

; The relation between ISA-before and INST-pre-ISA is described by this
; lemma.
(defthm ISA-before-INST-pre-ISA-car
    (implies (and (invariant MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (subtrace-p trace MT)
		  (consp trace))
	     (equal (ISA-before trace MT)
		    (INST-pre-ISA (car trace))))
  :hints (("Goal" :in-theory (enable ISA-before subtrace-p)
		  :use (:instance ISA-before-INST-pre-ISA-car-induction
				  (sub trace)
				  (trace (MT-trace MT))))
	  ("Goal'" :cases ((consp (MT-trace MT))))))
)
(in-theory (disable ISA-before-INST-pre-ISA-car))

(encapsulate nil
(local
(defthm ISA-pc-ISA-before-nil-help
    (implies (and (equal (trace-pc trace ISA) (MA-pc MA))
		  (MAETT-p MT) (MA-state-p MA))
	     (equal (ISA-pc (ISA-at-tail nil trace ISA)) (MA-pc MA)))))

; The program counter in an MA state points to the instruction which
; will be fetched in the next machine cycle.  Since the MAETT records
; all fetched instructions, the program counter of post-ISA of the
; last instruction in the MAETT is equal to the  program counter in
; the MA state.
(defthm ISA-pc-ISA-before-nil
    (implies (and (invariant MT MA)
		  (MAETT-p MT) (MA-state-p MA))
	     (equal (ISA-pc (ISA-before nil MT)) (MA-pc MA)))
  :hints (("Goal" :in-theory (enable ISA-before invariant pc-match-p
				     MT-pc))))
)


(encapsulate nil
(local
(defthm ISA-mem-ISA-before-nil-induction
    (implies (and (MAETT-p MT) (MA-state-p MA)
		  (ISA-chain-trace-p trace ISA))
	     (equal (ISA-mem (ISA-at-tail nil trace ISA))
		    (ISA-mem ISA)))))

(local
(defthm ISA-mem-ISA-before-nil-help
    (implies (and (MAETT-p MT) (MA-state-p MA)
		  (invariant MT MA))
	     (equal (ISA-mem (ISA-before nil MT))
		    (ISA-mem (MT-init-ISA MT))))
  :hints (("Goal" :in-theory (enable ISA-before invariant ISA-chain-p)))))

; Memory is not updated, therefore the memory state at any ISA state
; is equal to any MA state.
(defthm ISA-mem-ISA-before-nil
    (implies (and (invariant MT MA)
		  (MAETT-p MT) (MA-state-p MA))
	     (equal (ISA-mem (ISA-before nil MT)) (MA-mem MA)))
  :hints (("Goal" :in-theory (enable invariant mem-match-p))))
)

; There are only two states in this pipeline latch1 and latch2.  We also
; count retire as another stage.  The stage of an instruction entry
; should be one of them.
(defthm stages-of-INST
    (implies (INST-p i)
	     (or (equal (INST-stg i) 'latch1) (equal (INST-stg i) 'latch2)
		 (equal (INST-stg i) 'retire)))
  :hints (("goal" :in-theory (enable INST-p stage-p)))
  :rule-classes nil)

; Following several lemmas are about how the stages of an instruction
; changes.
(defthm INST-stg-step-latch1-INST
    (implies (equal (INST-stg i) 'latch1)
	     (equal (INST-stg (step-INST i MA))
		    (if (b1p (stall-cond? MA)) 'latch1 'latch2)))
  :hints (("Goal" :in-theory (enable step-INST step-latch1-INST))))


(defthm retire-step-INST-if-latch2
    (implies (equal (INST-stg i) 'latch2)
	     (equal (INST-stg (step-INST i MA)) 'retire))
  :hints (("Goal" :in-theory (enable step-INST step-latch1-INST
				     step-latch2-INST))))

(defthm retire-step-INST-if-retire
    (implies (equal (INST-stg i) 'retire)
	     (equal (INST-stg (step-INST i MA)) 'retire))
  :hints (("Goal" :in-theory (enable step-INST step-latch1-INST
				     step-latch2-INST))))

(defthm not-retire-step-INST-if-not-retire-latch2
    (implies (and (INST-p i)
		  (not (equal (INST-stg i) 'retire))
		  (not (equal (INST-stg i) 'latch2)))
	     (not (equal (INST-stg (step-INST i MT)) 'retire)))
  :hints (("Goal" :in-theory (enable INST-p stage-p step-INST
				     step-latch1-INST))))

(encapsulate nil
(local
(defthm no-inst-after-INST-latch1-induction
    (implies (and (trace-in-order-p trace)
		  (tail-p sub trace)
		  (INST-listp trace)
		  (consp sub)
		  (equal (INST-stg (car sub)) 'latch1))
	     (endp (cdr sub)))
  :rule-classes nil))

; Instruction at latch1 is the most recently fetched instruction.  A
; MAETT records instructions in program order, so the instruction at latch1
; is always represented by the last entry of a MAETT.
(defthm no-inst-after-INST-latch1
    (implies (and (invariant MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (subtrace-p trace MT)
		  (INST-listp trace)
		  (consp trace)
		  (equal (INST-stg (car trace)) 'latch1))
	     (endp (cdr trace)))
  :hints (("Goal" :in-theory (enable subtrace-p invariant MT-in-order-p)
		  :use (:instance no-inst-after-INST-latch1-induction
				  (sub trace) (trace (MT-trace MT)))))
  :rule-classes nil)
)

; A corollary of no-inst-after-INST-latch1.
(defthm INST-latch1-last-inst-in-MT
    (implies (and (invariant MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (subtrace-p trace MT)
		  (INST-listp trace)
		  (consp trace)
		  (equal (INST-stg (car trace)) 'latch1))
	     (not (member-equal i (cdr trace))))
  :hints (("Goal" :use (:instance no-inst-after-INST-latch1))))

; The instruction at stage latch2 is older than the instruction at latch1.
(defthm no-inst-at-latch2-after-latch1
    (implies (and (invariant MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (subtrace-p trace MT)
		  (INST-listp trace)
		  (consp trace)
		  (equal (INST-stg (car trace)) 'latch1))
	     (not (trace-INST-at 'latch2 (cdr trace))))
  :hints (("Goal" :use (:instance no-inst-after-INST-latch1))))


(encapsulate nil
(local
(defthm no-inst-at-latch2-after-latch2-help
    (implies (and (trace-in-order-p trace)
		  (tail-p sub trace)
		  (INST-listp trace)
		  (consp sub)
		  (equal (INST-stg (car sub)) 'latch2))
	     (not (trace-INST-at 'latch2 (cdr sub))))))

; There are no two instructions at latch2.
(defthm no-inst-at-latch2-after-latch2
    (implies (and (invariant MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (subtrace-p trace MT)
		  (INST-listp trace)
		  (consp trace)
		  (equal (INST-stg (car trace)) 'latch2))
	     (not (trace-INST-at 'latch2 (cdr trace))))
  :hints (("Goal" :in-theory (enable subtrace-p invariant MT-in-order-p))))
)

(encapsulate nil
(local
(defthm no-inst-at-retire-after-latch2-help
    (implies (and (trace-in-order-p trace)
		  (tail-p sub trace)
		  (INST-listp trace)
		  (consp sub)
		  (equal (INST-stg (car sub)) 'latch2))
	     (not (trace-INST-at 'retire (cdr sub))))))

; No retired instruction is younger than instruction at latch2.
; Instructions are retired in program order.
(defthm no-inst-at-retire-after-latch2
    (implies (and (invariant MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (subtrace-p trace MT)
		  (INST-listp trace)
		  (consp trace)
		  (equal (INST-stg (car trace)) 'latch2))
	     (not (trace-INST-at 'retire (cdr trace))))
  :hints (("Goal" :in-theory (enable subtrace-p invariant MT-in-order-p))))
)

; An instruction at latch2 is immediately followed by an instruction
; at latch1.
(defthm INST-latch1-follows-INST-latch2
    (implies (and (invariant MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (subtrace-p trace MT)
		  (INST-listp trace)
		  (consp trace) (consp (cdr trace))
		  (equal (INST-stg (car trace)) 'latch2))
	     (equal (INST-stg (cadr trace)) 'latch1))
  :hints (("Goal" :use ((:instance stages-of-inst (i (cadr trace)))
			(:instance no-inst-at-latch2-after-latch2)
			(:instance no-inst-at-retire-after-latch2))
		  :in-theory (disable no-inst-at-latch2-after-latch2
				      no-inst-at-retire-after-latch2))))


; Predicate inst-invariant is an invariant condition that every
; instruction in a MAETT should satisfy.  Following two lemmas shows
; that in two different formulation.
(encapsulate nil
(local
(defthm inst-invariant-INST-at-help
    (implies (and (trace-INST-invariant trace MA)
		  (trace-INST-at stg trace))
	     (inst-invariant (trace-INST-at stg trace) MA))))

(defthm inst-invariant-INST-at
    (implies (and (invariant MT MA)
		  (INST-at stg MT))
	     (inst-invariant (INST-at stg MT) MA))
  :hints (("Goal" :in-theory (enable INST-at invariant MT-inst-invariant))))
)

(encapsulate nil
(local
 (defthm INST-invariant-INST-in-induction
     (implies (and (trace-inst-invariant trace MA)
		   (member-equal i trace))
	      (inst-invariant i MA))))


(defthm INST-invariant-INST-in
    (implies (and (invariant MT MA)
		  (INST-in i MT))
	     (inst-invariant i MA))
  :hints (("Goal" :in-theory (enable invariant INST-in MT-inst-invariant
				     trace-INST-invariant)))
  :rule-classes nil)
)

; There must be an instruction at latch1 if flag latch1-valid? in an
; MA state is on.  This lemma shows that a MAETT contains an entry
; representing the instruction at latch1 if latch1-valid? is on in
; the corresponding MA state.
(defthm INST-at-latch1-if-latch1-valid
    (implies (and (invariant MT MA)
		  (b1p (latch1-valid? (MA-latch1 MA))))
	     (INST-at 'latch1 MT))
  :hints (("Goal" :in-theory (enable invariant MT-contains-all-insts))))

; If latch1-valid? is off, no instruction is at latch1.
(defthm not-INST-at-latch1-if-not-latch1-valid
    (implies (and (invariant MT MA)
		  (not (b1p (latch1-valid? (MA-latch1 MA)))))
	     (not (INST-at 'latch1 MT)))
  :hints (("Goal" :use (:instance INST-invariant-INST-at (stg 'latch1))
		  :in-theory (e/d (INST-invariant INST-latch1-inv)
				  (INST-invariant-INST-at)))))

; If instruction i is at latch1, latch1-valid? should be on.
(defthm latch1-valid-if-INST-in
    (implies (and (invariant MT MA)
		  (INST-in i MT) (INST-p i)
		  (equal (INST-stg i) 'latch1))
	     (b1p (latch1-valid? (MA-latch1 MA))))
  :hints (("Goal" :use (:instance INST-invariant-INST-in)
		  :in-theory (e/d (INST-invariant INST-latch1-inv)
				  ()))))

; Same for latch2.
(defthm INST-at-latch2-if-latch2-valid
    (implies (and (invariant MT MA)
		  (b1p (latch2-valid? (MA-latch2 MA))))
	     (INST-at 'latch2 MT))
  :hints (("Goal" :in-theory (enable invariant MT-contains-all-insts))))

(defthm not-INST-at-latch2-if-not-latch2-valid
    (implies (and (invariant MT MA)
		  (not (b1p (latch2-valid? (MA-latch2 MA)))))
	     (not (INST-at 'latch2 MT)))
  :hints (("Goal" :use (:instance INST-invariant-INST-at (stg 'latch2))
		  :in-theory (e/d (INST-invariant INST-latch2-inv)
				  (INST-invariant-INST-at)))))

(defthm latch2-valid-if-INST-in
    (implies (and (invariant MT MA)
		  (INST-in i MT) (INST-p i)
		  (equal (INST-stg i) 'latch2))
	     (b1p (latch2-valid? (MA-latch2 MA))))
  :hints (("Goal" :use (:instance INST-invariant-INST-in)
		  :in-theory (e/d (INST-invariant INST-latch2-inv)
				  ()))))

; Correct intermediate values of instruction execution can be specified
; using the instruction entry in a MAETT.  For
; instance, if instruction I is in latch1, then the latch1-op should
; hold the operand of instruction I, which can be specified as
; (INST-op i). This is shown by Lemma latch1-op-INST-op-if-INST-in.
; In the rest of this file, we give a list of similar lemmas.

;
; Note: First, we give all lemmas in the same style as
; latch1-op-INST-op-if-INST-in.  Then we re-state all the lemmas in a
; different style, starting from latch1-op-INST-op.  In the latter
; style, we use function INST-at to specify the instruction at a
; specific latch.
(defthm latch1-op-INST-op-if-INST-in
    (implies (and (invariant MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-in i MT) (INST-p i)
		  (equal (INST-stg i) 'latch1))
	     (equal (latch1-op (MA-latch1 MA)) (INST-op i)))
  :hints (("goal" :in-theory (e/d (INST-INVARIANT INST-LATCH1-INV)
				  (inst-invariant-INST-at))
		  :use (:instance inst-invariant-INST-in))))

(defthm latch1-rc-INST-rc-if-INST-in
    (implies (and (invariant MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-in i MT) (INST-p i)
		  (equal (INST-stg i) 'latch1))
	     (equal (latch1-rc (MA-latch1 MA)) (INST-rc i)))
  :hints (("goal" :in-theory (e/d (INST-INVARIANT INST-LATCH1-INV)
				  (inst-invariant-INST-at))
		  :use (:instance inst-invariant-INST-in))))

(defthm latch1-ra-INST-ra-if-INST-in
    (implies (and (invariant MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-in i MT) (INST-p i)
		  (equal (INST-stg i) 'latch1))
	     (equal (latch1-ra (MA-latch1 MA)) (INST-ra i)))
  :hints (("goal" :in-theory (e/d (INST-INVARIANT INST-LATCH1-INV)
				  (inst-invariant-INST-at))
		  :use (:instance inst-invariant-INST-in))))

(defthm latch1-rb-INST-rb-if-INST-in
    (implies (and (invariant MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-in i MT) (INST-p i)
		  (equal (INST-stg i) 'latch1))
	     (equal (latch1-rb (MA-latch1 MA)) (INST-rb i)))
  :hints (("goal" :in-theory (e/d (INST-INVARIANT INST-LATCH1-INV)
				  (inst-invariant-INST-at))
		  :use (:instance inst-invariant-INST-in))))

(defthm latch2-op-INST-op-if-INST-in
    (implies (and (invariant MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-in i MT) (INST-p i)
		  (equal (INST-stg i) 'latch2))
	     (equal (latch2-op (MA-latch2 MA)) (INST-op i)))
  :hints (("goal" :in-theory (e/d (INST-INVARIANT INST-LATCH2-INV)
				  (inst-invariant-INST-at))
		  :use (:instance inst-invariant-INST-in))))

(defthm latch2-rc-INST-rc-if-INST-in
    (implies (and (invariant MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-in i MT) (INST-p i)
		  (equal (INST-stg i) 'latch2))
	     (equal (latch2-rc (MA-latch2 MA)) (INST-rc i)))
  :hints (("goal" :in-theory (e/d (INST-INVARIANT INST-LATCH2-INV)
				  (inst-invariant-INST-at))
		  :use (:instance inst-invariant-INST-in))))

(defthm latch2-val1-INST-val1-if-INST-in
    (implies (and (invariant MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-in i MT) (INST-p i)
		  (equal (INST-stg i) 'latch2))
	     (equal (latch2-ra-val (MA-latch2 MA)) (INST-ra-val i)))
  :hints (("goal" :in-theory (e/d (INST-INVARIANT INST-LATCH2-INV)
				  (inst-invariant-INST-at))
		  :use (:instance inst-invariant-INST-in))))

(defthm latch2-rb-val-INST-rb-val-if-INST-in
    (implies (and (invariant MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-in i MT) (INST-p i)
		  (equal (INST-stg i) 'latch2))
	     (equal (latch2-rb-val (MA-latch2 MA)) (INST-rb-val i)))
  :hints (("goal" :in-theory (e/d (INST-INVARIANT INST-LATCH2-INV)
				  (inst-invariant-INST-at))
		  :use (:instance inst-invariant-INST-in))))


(defthm latch1-op-INST-op
    (implies (and (invariant MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-at 'latch1 MT))
	     (equal (latch1-op (MA-latch1 MA))
		    (INST-op (INST-at 'latch1 MT))))
  :hints (("goal" :in-theory (e/d (INST-INVARIANT INST-LATCH1-INV)
				  (inst-invariant-INST-at))
		  :use (:instance inst-invariant-INST-at (stg 'latch1)))))

(defthm latch1-rc-INST-rc
    (implies (and (invariant MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-at 'latch1 MT))
	     (equal (latch1-rc (MA-latch1 MA))
		    (INST-rc (INST-at 'latch1 MT))))
  :hints (("goal" :in-theory (e/d (INST-INVARIANT INST-LATCH1-INV)
				  (inst-invariant-INST-at))
		  :use (:instance inst-invariant-INST-at (stg 'latch1)))))

(defthm latch1-ra-INST-ra
    (implies (and (invariant MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-at 'latch1 MT))
	     (equal (latch1-ra (MA-latch1 MA))
		    (INST-ra (INST-at 'latch1 MT))))
  :hints (("goal" :in-theory (e/d (INST-INVARIANT INST-LATCH1-INV)
				  (inst-invariant-INST-at))
		  :use (:instance inst-invariant-INST-at (stg 'latch1)))))

(defthm latch1-rb-INST-rb
    (implies (and (invariant MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-at 'latch1 MT))
	     (equal (latch1-rb (MA-latch1 MA))
		    (INST-rb (INST-at 'latch1 MT))))
  :hints (("goal" :in-theory (e/d (INST-INVARIANT INST-LATCH1-INV)
				  (inst-invariant-INST-at))
		  :use (:instance inst-invariant-INST-at (stg 'latch1)))))

(defthm latch2-op-INST-op
    (implies (and (invariant MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-at 'latch2 MT))
	     (equal (latch2-op (MA-latch2 MA))
		    (INST-op (INST-at 'latch2 MT))))
  :hints (("goal" :in-theory (e/d (INST-INVARIANT INST-LATCH2-INV)
				  (inst-invariant-INST-at))
		  :use (:instance inst-invariant-INST-at (stg 'latch2)))))

(defthm latch2-rc-INST-rc
    (implies (and (invariant MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-at 'latch2 MT))
	     (equal (latch2-rc (MA-latch2 MA))
		    (INST-rc (INST-at 'latch2 MT))))
  :hints (("goal" :in-theory (e/d (INST-INVARIANT INST-LATCH2-INV)
				  (inst-invariant-INST-at))
		  :use (:instance inst-invariant-INST-at (stg 'latch2)))))

(defthm latch2-ra-val-INST-ra-val
    (implies (and (invariant MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-at 'latch2 MT))
	     (equal (latch2-ra-val (MA-latch2 MA))
		    (INST-ra-val (INST-at 'latch2 MT))))
  :hints (("goal" :in-theory (e/d (INST-INVARIANT INST-LATCH2-INV)
				  (inst-invariant-INST-at))
		  :use (:instance inst-invariant-INST-at (stg 'latch2)))))

(defthm latch2-rb-val-INST-rb-val
    (implies (and (invariant MT MA)
		  (MAETT-p MT) (MA-state-p MA)
		  (INST-at 'latch2 MT))
	     (equal (latch2-rb-val (MA-latch2 MA))
		    (INST-rb-val (INST-at 'latch2 MT))))
  :hints (("goal" :in-theory (e/d (INST-INVARIANT INST-LATCH2-INV)
				  (inst-invariant-INST-at))
		  :use (:instance inst-invariant-INST-at (stg 'latch2)))))


