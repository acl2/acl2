; This file contains the proof of skipping simulation theorem for
; vectorizing compiler transformation
(in-package "ACL2S")
(include-book "op-semantics")

(defun scalarize (inst)
  "scalerize a vector instruction"
;  :input-contract (mix-instp inst)
;  :output-contract (imemp (scalarize inst))
  (cond ((vecinstp inst)
         (let ((op (mget :op inst))
               (ra1 (car (mget :ra inst)))
               (ra2 (cdr (mget :ra inst)))
               (rb1 (car (mget :rb inst)))
               (rb2 (cdr (mget :rb inst)))
               (rc1 (car (mget :rc inst)))
               (rc2 (cdr (mget :rc inst))))
          (case op
            (vadd (list (inst 'add rc1 ra1 rb1)
                        (inst 'add rc2 ra2 rb2)))
            (vsub (list (inst 'sub rc1 ra1 rb1)
                        (inst 'sub rc2 ra2 rb2)))
            (vmul (list (inst 'mul rc1 ra1 rb1)
                        (inst 'mul rc2 ra2 rb2))))))
        ((instp inst) (list inst))
        (t nil)))


(defun scalarize-mem (pc V)
  "scalerize the memory [0,pc]"
;  :input-contract (and (natp pc) (vecimemp V))
;  :output-contract (imemp (scalarize-mem pc V))
  (if (or (not (integerp pc))
          (< pc 0))
      nil
    (let ((inst (nth pc V)))
     (cond
      ((zp pc) ;=0
       (scalarize inst))
      (t
       (append  (scalarize-mem (1- pc) V) (scalarize inst)))))))

(defun count-num-scaler-inst (inst)
  "return number of scaler instruction between 0 and pc both including"
;  :input-contract (mix-instp inst)
;  :output-contract (natp (count-num-scaler-inst inst))
  (cond ((vecinstp inst)
         2)
        ((instp inst)
         1)
        (t 0)))

; 
(defun get-num-inst (pc V)
  "count total number of scalar instruction in [0,pc]"
;  :input-contract (and (natp pc) (vecimemp V))
;  :output-contract (natp (get-num-inst pc V)
  (let ((inst (nth pc V)))
   (cond ((or (not (integerp pc))
              (< pc 0))
          0)
         ((zp pc)
          (count-num-scaler-inst inst))
         (t (+ (count-num-scaler-inst inst) (get-num-inst (1- pc) V))))))

(defun ref-map (s)
  "refinement map"
;  :input-contract (vecisa-statep s)
;  :output-contract (isa-statep (ref-map s))
  (let* ((regs (mget :regs s))
         (V (vecisa-state-vecinmem s))
         (isapc (get-num-inst (1- (mget :prc s)) V)))
    (isa-state isapc regs (scalarize-mem (len V) V))))

(defun spec-run-upto-2 (s n)
  "spec step for n steps"
;  :input-contract (and (spec-statep s) (natp n))
;  :output-contract (spec-statep (spec-run-upto-3 s n))
  (cond ((equal n 1)
         (isa-step s))
        ((equal n 2)
         (isa-step (isa-step s)))
        (t s)))

(defun spec-run-upto-2-rel (s u)
  "u is reachable from s in atmost 2 steps"
;  :input-contract (and (spec-statep s) (spec-statep u))
;  :output-contract (booleanp (spec-run-upto-3-rel s u))
  (or (equal (spec-run-upto-2 s 1) u)
      (equal (spec-run-upto-2 s 2) u)))

; y is reachable from x in one or more steps
(defun-sk spec-step+ (s u)
  (exists n
    (and (posp n)
         (equal (isa-run s n)
                u))))

 (defun spec-run-expanded (s n)
   "define a new run relation to reason about the upto-2-step-relation"
   (cond ((zp n) s)
        ((equal n 1) (isa-step s))
        ((equal n 2) (isa-step (isa-step s)))
        (t (spec-run-expanded (isa-step s) (1- n)))))
 
(defthmd run-expanded-equivalent-isa-run-n
  (equal (spec-run-expanded s n)
         (isa-run s n))
  :hints (("goal" :induct (isa-run s n)
           :in-theory (e/d () (isa-step)))))

(defun-sk spec-run-expanded-exist (s u)
  (exists n 
    (and (posp n)
         (equal (spec-run-expanded s n) u))))


(defthmd run-expanded-exist-equivalent
  (implies (spec-run-expanded-exist s u)
         (spec-step+ s u))
  :hints (("goal" :use
           ((:instance  run-expanded-equivalent-isa-run-n
                        (n (spec-run-expanded-exist-witness
                            s u)))
            (:instance spec-run-expanded-exist-suff)
            (:instance spec-step+-suff (n (spec-run-expanded-exist-witness s u))))
           :in-theory (e/d () (spec-step+)))))

(defthm finite-step-implies-exists
  (implies (spec-run-upto-2-rel s u)
           (spec-run-expanded-exist s u))
  :hints (("goal" :use ((:instance spec-run-expanded-exist-suff (n 1))
                        (:instance spec-run-expanded-exist-suff (n 2))
                        (:instance spec-run-expanded-exist-suff (n 3)))
           :in-theory (e/d () (isa-step)))))

(defthm finite-step-implies-spec-step-+
  (implies (spec-run-upto-2-rel s u)
           (spec-step+ s u))
  :hints (("goal" :use ((:instance finite-step-implies-exists)
                        (:instance run-expanded-exist-equivalent)))))


(defthm inst-or-vecinst-vecimem
  (implies (and (vecimemp vecimem)
                (natp k)
                (nth k vecimem)
                (not (instp (nth k vecimem))))
           (vecinstp (nth k vecimem)))
  :rule-classes :forward-chaining)

(defthm opcode-case-analysis
  (implies (and (instp i)
                (not (equal (mget :op i) 'add))
                (not (equal (mget :op i) 'sub)))
           (equal (mget :op i) 'mul))
  :hints (("goal" :in-theory (enable op-codep instp))))

(defthm nth-=>len 
  (implies (and (natp j) (>= j (len l)))
           (null (nth j l))))

(defthm nth-append-l+1
  (equal (nth (len l) (append l (cons x l2)))
         x))


(encapsulate 
 ()
 (local 
  (defun f-ind (k l)
    (if (endp l)
        nil
      (+ k (f-ind (1- k) (cdr l)))))
  )

 (defthm nth-app-lemma-2
   (implies (and (natp k) (> k (len l1))
                 (true-listp l1) (true-listp l))
            (equal (nth k (append l1 l))
                   (nth (- k (len l1)) l)))
   :hints (("goal" :induct (f-ind k l1)))
   :rule-classes (:linear :rewrite))
 )

(encapsulate 
 ()
 (local
  (defun f-ind-1 (k) 
    (if (zp k)
        1
      (1+ (f-ind-1 (1- k)))))

  )
 (defthm nth-lemma-1
   (implies (and (vecimemp l) 
                 (nth k l))
            (nth (1- k) l))
   :rule-classes (:forward-chaining :rewrite))
 )


(defthm count-num-scaler-inst->0
  (implies (and (vecimemp vecimem)
                (or (instp i)
                    (vecinstp i)))
           (> (count-num-scaler-inst i) 0))
  :rule-classes :linear)


(defthm vecopcode-case-analysis
  (implies (and (vecinstp i)
                (not (equal (mget :op i) 'vadd))
                (not (equal (mget :op i) 'vsub)))
           (equal (mget :op i) 'vmul))
  :hints (("goal" :in-theory (enable vecinstp vec-op-codep))))

; relate the length after flatten and gen-num-inst  
(defthm flatten-len-get-num-inst
  (implies (and (vecimemp vecimem)
                (integerp k))
           (equal (get-num-inst k vecimem)
                  (len (scalarize-mem k vecimem)))))

; lemma for len of scalarize-mem when one more instruction is added
(defthm len-k-1-flatten-k-vecimem
  (implies (and (vecimemp vecimem)
                (integerp k)
                (not (equal (len (scalarize-mem k vecimem))
                            (len (scalarize-mem (1- k) vecimem))))
                (not (equal (len (scalarize-mem k vecimem))
                            (+ 2 (len (scalarize-mem (1- k) vecimem))))))
           (equal (len (scalarize-mem k vecimem))
                  (1+ (len (scalarize-mem (1- k) vecimem)))))
  :hints (("goal" :use (:instance vecopcode-case-analysis)))
  :rule-classes (:linear :rewrite))

(defthm len-flatten-case-lemma-inst-+1
  (implies (and (natp k) 
                (vecimemp vecimem)
                (instp (nth k vecimem))
                (not (vecinstp (nth k vecimem)))
                )
           (equal (len (scalarize-mem k vecimem))
                  (+ 1 (len (scalarize-mem (1- k) vecimem)))))
  :hints (("goal" :in-theory (disable instp vecimemp))))

(defthm len-flatten-case-lemma-vecinst-+2
  (implies (and (natp k) 
                (vecimemp vecimem)
                (vecinstp (nth k vecimem))
                )
           (equal (len (scalarize-mem k vecimem))
                  (+ 2 (len (scalarize-mem (1- k) vecimem)))))
  :hints (("goal" :in-theory (disable instp vecimemp))))


(encapsulate 
 ()
;lemma to move from k to any j >= k in LHS (flatten-1 k vecimem) 
; in particular k = (len vecimem)
 (local
  ; alternate definition of scalarize starting from the first instruction
  (defun S (L)
    (if (endp L)
        nil
      (append (scalarize (car L)) (S (cdr L)))))
  )

 (local
  (defun seg (k L)
    (if (endp L)
        nil
      (if (zp k)
          (list (car L))
        (cons (car L)
              (seg (1- k) (cdr L))))))
  )

 (local
  ; relate two definitions of scalerize
  (defthm S-rel-Scalarize-mem
    (implies (and (vecimemp V)
                  (natp k))
             (equal (scalarize-mem k V)
                    (S (seg k V))))
    :hints (("goal" :in-theory (disable scalarize))))
  )

 (local
  (defthm full-segment
    (implies (true-listp L)
             (equal (seg (len L) L) L)))
  )

 (local
  (defun segmentp (X Y)
    (if (endp X)
        T
      (if (endp Y)
          nil
        (and (equal (car X) (car Y))
             (segmentp (cdr X) (cdr Y))))))
  )

 (local
  (defthm subset-index-rel
    (implies (and (true-listp l)
                  (natp j)
                  (< j (len l1))
                  (segmentp l1 l))
             (equal (nth j l)
                    (nth j l1))))
  )

 (local
  (defthm segments-indexes-rel
    (implies (and (true-listp l)
                  (< j (len L)))
             (segmentp (seg j l) l)))
  )

 (local
  (defthm S-sewgf
    (implies (vecimemp V)
             (segmentp (S (seg k V)) (S V))))
  )

 (local
  (defthm nth-inst-in-alternate-defs-same
    (implies (and (natp k)
                  (vecimemp V)
                  (natp j)
                  (< j (len (scalarize-mem k V))))
             (equal (nth j (S V))
                    (nth j (scalarize-mem k V)))))
  )
 
 (defthm scalarize-invariant-upto-j
   (implies (and (natp k)
                 (vecimemp l)
                 (< k (len l))
                 (natp j)
                 (< j (len (scalarize-mem k l))))
            (equal (nth j (scalarize-mem (len l) l))
                   (nth j (scalarize-mem k l)))))
 )


(defthmd get-num-inst-decreases
  (implies (and (vecimemp vecimem)
                (natp k)
                (nth k vecimem))
           (< (get-num-inst (1- k) vecimem)
              (get-num-inst k vecimem)))
  :rule-classes :linear)

(defthmd get-num-inst-scalarize-mem-reduction
  (implies (and (natp k)
                (vecimemp vecimem)
                (nth k vecimem)
                (< k (len vecimem))
                )
           (equal (nth (get-num-inst (1- k) vecimem)
                       (scalarize-mem (len vecimem) vecimem))
                  (nth (get-num-inst (1- k) vecimem)
                       (scalarize-mem k vecimem))))
  :hints (("goal" :use ((:instance scalarize-invariant-upto-j (j (get-num-inst (1- k) vecimem)) (l vecimem))
                        (:instance flatten-len-get-num-inst)
                        (:instance get-num-inst-decreases))
           :in-theory (disable get-num-inst scalarize-mem
                               (:rewrite scalarize-invariant-upto-j)
                               (:rewrite flatten-len-get-num-inst)))))

(defthmd get-num-inst-decreases-1
  (implies (and (vecimemp vecimem)
                (natp k)
                (vecinstp (nth k vecimem)))
           (< (1+ (get-num-inst (1- k) vecimem))
              (get-num-inst k vecimem)))
  :rule-classes :linear)

(defthmd get-num-inst-scalarize-mem-reduction-+1
  (implies (and (natp k)
                (vecimemp vecimem)
                (nth k vecimem)
                (vecinstp (nth k vecimem))
                (< k (len vecimem))
                )
           (equal (nth (1+ (get-num-inst (1- k) vecimem))
                       (scalarize-mem (len vecimem) vecimem))
                  (nth (1+ (get-num-inst (1- k) vecimem))
                       (scalarize-mem k vecimem))))
  :hints (("goal" :use ((:instance scalarize-invariant-upto-j (j (1+ (get-num-inst (1- k) vecimem))) (l vecimem))
                        (:instance flatten-len-get-num-inst)
                        (:instance get-num-inst-decreases-1))
           :in-theory (disable get-num-inst count-num-scaler-inst
                               scalarize-mem
                               (:rewrite scalarize-invariant-upto-j)
                               (:rewrite flatten-len-get-num-inst)))))

;; vecimem is mapped to (flatten vecimem) by the refinement map. I
;; need a relation that relates the instruction executed in the vector
;; machine at vecpc and the one pointed by the get-num-inst in the
;; flattened vecimem. Infact, I need to prove that the instruction is
;; same in case the next instruction to be executed in vector machine
;; is a scaler instruction and similarly if the next is a vector
;; instruction then its decomposition is two consecutive scalar
;; instruction. These obligations are captured in lemma 5,6,7
(encapsulate
 ()
 (local 
  (defthm lemma-5-main
  (implies (and (natp k)
                (vecimemp vecimem)
                (instp (nth k vecimem))
                (not (vecinstp (nth k vecimem))))
           (equal (nth (1- (len (scalarize-mem k vecimem))) (scalarize-mem k vecimem))
                  (nth k vecimem))))
)
 (local
  (defthmd lemma-5-aux-consp
    (implies (and (natp k)
                  (vecimemp vecimem)
                  (instp (nth k vecimem))
                  (not (vecinstp (nth k vecimem))))
             (equal (nth (get-num-inst (1- k) vecimem) ;; number of scaler instruction from [0,k)
                         (scalarize-mem k vecimem))
                    (nth k vecimem)))
    :hints (("goal" :in-theory (disable instp vecinstp vecinst scalarize get-num-inst scalarize-mem vecimemp nth inst)
             :use ((:instance inst-or-vecinst-vecimem)
                   (:instance lemma-5-main)
                   (:instance len-k-1-flatten-k-vecimem)
                   (:instance flatten-len-get-num-inst)
                   (:instance len-flatten-case-lemma-inst-+1)))))
  )

 
 (local
  (defthmd lemma-5-aux-k
    (implies (and (natp k)
                  (vecimemp vecimem)
                  (instp (nth k vecimem))
                  (not (vecinstp (nth k vecimem))))
             (equal (nth (get-num-inst (1- k) vecimem)
                         (scalarize-mem k vecimem))
                    (nth k vecimem)))
    :hints (("goal" :in-theory (disable instp inst get-num-inst scalarize-mem vecimemp)
             :use ((:instance lemma-5-aux-consp))
             :cases ((null vecimem) (consp vecimem)))))
  )

 (local
  (defthmd lemma-5-1
    (implies (and (vecisa-statep s)
                  (vecimemp (vecisa-state-vecinmem s))
                  (instp (nth (mget :prc s) (vecisa-state-vecinmem s)))
                  (not (vecinstp (nth (mget :prc s) (vecisa-state-vecinmem s))))
                  (< (mget :prc s) (len (vecisa-state-vecinmem s))))
             (equal (nth (get-num-inst (1- (mget :prc s)) (vecisa-state-vecinmem s))
                         (scalarize-mem (len (vecisa-state-vecinmem s))
                                        (vecisa-state-vecinmem s)))
                    (nth (mget :prc s) (vecisa-state-vecinmem s))))
    :hints (("goal"  :in-theory (disable scalarize-mem get-num-inst scalarize inst vecopcode-case-analysis lemma-5-aux-k)
             :use ((:instance get-num-inst-scalarize-mem-reduction (k (mget :prc s)) (vecimem (vecisa-state-vecinmem s)))
                   (:instance lemma-5-aux-k (k (mget :prc s))
                              (vecimem (vecisa-state-vecinmem s)))))))

  )
 (local
  (defthmd lemma-5-2
    (implies (and (vecisa-statep s)
                  (instp (nth (mget :prc s) (vecisa-state-vecinmem s)))
                  (not (vecinstp (nth (mget :prc s) (vecisa-state-vecinmem s))))
                  (>= (mget :prc s) (len (vecisa-state-vecinmem s))))
             (equal (nth (get-num-inst (1- (mget :prc s)) (vecisa-state-vecinmem s))
                         (scalarize-mem (len (vecisa-state-vecinmem s))
                                        (vecisa-state-vecinmem s)))
                    (nth (mget :prc s) (vecisa-state-vecinmem s))))
    :hints (("goal" :in-theory (disable scalarize-mem get-num-inst scalarize inst vecopcode-case-analysis lemma-5-aux-k)
             :use ((:instance nth-=>len (j (mget :prc s)) (l (vecisa-state-vecinmem s)))))))
  )

 (defthmd lemma-5
   (implies (and (vecisa-statep s)
                 (instp (nth (mget :prc s) (vecisa-state-vecinmem s)))
                 (not (vecinstp (nth (mget :prc s) (vecisa-state-vecinmem s)))))
            (equal (nth (get-num-inst (1- (mget :prc s)) (vecisa-state-vecinmem s))
                        (scalarize-mem (len (vecisa-state-vecinmem s))
                                       (vecisa-state-vecinmem s)))
                   (nth (mget :prc s) (vecisa-state-vecinmem s))))
   :hints (("goal" :cases ((>= (mget :prc s) (len (vecisa-state-vecinmem s))) (< (mget :prc s) (len (vecisa-state-vecinmem s))))
            :in-theory (disable vecinstp instp vecisa-statep scalarize-mem flatten-len-get-num-inst))
           ("Subgoal 2" :use (:instance lemma-5-2))
           ("Subgoal 1" :use ((:instance lemma-5-1)))))
 )

(encapsulate
 ()
 ; last but one instruction (= 2- len) in the (scalarize-mem k vecimem) is the same as the
 ; first instruction on scalerizing the k the instruction in vecimem
 (local
  (defthm lemma-main-6
    (implies (and (natp k)
                  (vecimemp vecimem)
                  (vecinstp (nth k vecimem)))
             (equal (nth (- (len (scalarize-mem k vecimem)) 2) (scalarize-mem k vecimem))
                    (car (scalarize (nth k vecimem))))))
  )

 (local
  (defthmd lemma-6-aux
    (implies (and (natp k)
                  (vecimemp vecimem)
                  (vecinstp (nth k vecimem)))
             (equal (nth (get-num-inst (1- k) vecimem) ;; number of scaler instruction from [0,k)
                         (scalarize-mem k vecimem))
                    (car (scalarize (nth k vecimem)))))
    :hints (("goal" :in-theory (disable instp vecinstp vecinst scalarize get-num-inst scalarize-mem vecimemp nth inst)
             :use ((:instance lemma-main-6)))))
  )

 (local
  (defthmd lemma-6-aux-k
    (implies (and (natp k)
                  (vecimemp vecimem)
                  (vecinstp (nth k vecimem)))
             (equal (nth (get-num-inst (1- k) vecimem) ;; number of scaler instruction from [0,k)
                         (scalarize-mem k vecimem))
                    (car (scalarize (nth k vecimem)))))
    :hints (("goal" :in-theory (disable instp inst get-num-inst scalarize-mem vecimemp)
             :use ((:instance lemma-6-aux))
             :cases ((null vecimem) (consp vecimem)))))
  )

 (local
  (defthmd lemma-6-1
    (implies (and (vecisa-statep s)
                  (vecimemp (vecisa-state-vecinmem s))
                  (vecinstp (nth (mget :prc s) (vecisa-state-vecinmem s)))
                  (< (mget :prc s) (len (vecisa-state-vecinmem s))))
             (equal (nth (get-num-inst (1- (mget :prc s)) (vecisa-state-vecinmem s))
                         (scalarize-mem (len (vecisa-state-vecinmem s))
                                        (vecisa-state-vecinmem s)))
                    (car (scalarize (nth (mget :prc s) (vecisa-state-vecinmem s))))))
    :hints (("goal"  :in-theory (disable scalarize-mem get-num-inst scalarize inst vecopcode-case-analysis)
             :use ((:instance get-num-inst-scalarize-mem-reduction (k (mget :prc s)) (vecimem (vecisa-state-vecinmem s)))
                   (:instance lemma-6-aux-k (k (mget :prc s))
                              (vecimem (vecisa-state-vecinmem s)))))))
  )

 (local
  (defthmd lemma-6-2
    (implies (and (vecisa-statep s)
                  (vecinstp (nth (mget :prc s) (vecisa-state-vecinmem s)))
                  (>= (mget :prc s) (len (vecisa-state-vecinmem s))))
             (equal (nth (get-num-inst (1- (mget :prc s)) (vecisa-state-vecinmem s))
                         (scalarize-mem (len (vecisa-state-vecinmem s))
                                        (vecisa-state-vecinmem s)))
                    (car (scalarize (nth (mget :prc s) (vecisa-state-vecinmem s))))))
    :hints (("goal" :in-theory (disable scalarize-mem get-num-inst scalarize inst vecopcode-case-analysis)
             :use ((:instance nth-=>len (j (mget :prc s)) (l (vecisa-state-vecinmem s)))))))
  )

 (defthmd lemma-6
    (implies (and (vecisa-statep s)
                  (vecinstp (nth (mget :prc s) (vecisa-state-vecinmem s))))
             (equal (nth (get-num-inst (1- (mget :prc s)) (vecisa-state-vecinmem s))
                         (scalarize-mem (len (vecisa-state-vecinmem s))
                                        (vecisa-state-vecinmem s)))
                    (car (scalarize (nth (mget :prc s) (vecisa-state-vecinmem s))))))
    :hints (("goal" :cases ((>= (mget :prc s) (len (vecisa-state-vecinmem s))) (< (mget :prc s) (len (vecisa-state-vecinmem s))))
             :in-theory (disable vecinstp instp vecisa-statep scalarize-mem flatten-len-get-num-inst))
            ("Subgoal 2" :use (:instance lemma-6-2))
            ("Subgoal 1" :use ((:instance lemma-6-1)))))
 )

(encapsulate
 ()
 ; last instruction (= 1- len) in the (scalarize-mem k vecimem) is the same as the
 ; first instruction on scalerizing the k the instruction in vecimem
 (local
  (defthm lemma-7-main
    (implies (and (natp k)
                  (vecimemp vecimem)
                  (vecinstp (nth k vecimem)))
             (equal (nth (1- (len (scalarize-mem k vecimem))) (scalarize-mem k vecimem))
                    (cadr (scalarize (nth k vecimem))))))
  )

 (local
  (defthmd lemma-7-aux-consp
    (implies (and (natp k)
                  (vecimemp vecimem)
                  (vecinstp (nth k vecimem)))
             (equal (nth (1+ (get-num-inst (1- k) vecimem)) ;; number of scaler instruction from [0,k)
                         (scalarize-mem k vecimem))
                    (cadr (scalarize (nth k vecimem)))))
    :hints (("goal" :in-theory (disable instp vecinstp vecinst scalarize get-num-inst scalarize-mem vecimemp nth inst)
             :use ((:instance lemma-7-main)))))
  )
 (local
  (defthmd lemma-7-aux-k
    (implies (and (natp k)
                  (vecimemp vecimem)
                  (vecinstp (nth k vecimem)))
             (equal (nth (1+ (get-num-inst (1- k) vecimem)) ;; number of scaler instruction from [0,k)
                         (scalarize-mem k vecimem))
                    (cadr (scalarize (nth k vecimem)))))
    :hints (("goal" :in-theory (disable instp inst get-num-inst scalarize-mem vecimemp)
             :use ((:instance lemma-7-aux-consp))
             :cases ((null vecimem) (consp vecimem)))))
  )

 (local
  (deftheory my-th
   '((:rewrite get-num-inst-scalarize-mem-reduction-+1)
     (:rewrite lemma-7-aux-k))))
 
 (local
   (defthmd lemma-7-1
     (implies (and (vecisa-statep s)
                   (natp (mget :prc s))
                   (vecimemp (vecisa-state-vecinmem s))
                   (vecimemp (vecisa-state-vecinmem s))
                   (nth (mget :prc s) (vecisa-state-vecinmem s))
                   (vecinstp (nth (mget :prc s) (vecisa-state-vecinmem s)))
                   (< (mget :prc s) (len (vecisa-state-vecinmem s))))
              (equal (nth (1+ (get-num-inst (1- (mget :prc s)) (vecisa-state-vecinmem s)))
                          (scalarize-mem (len (vecisa-state-vecinmem s))
                                         (vecisa-state-vecinmem s)))
                     (cadr (scalarize (nth (mget :prc s) (vecisa-state-vecinmem s))))))
     :hints (("goal" :in-theory (union-theories (theory 'my-th) nil)))))
    
 (local
  (defthmd lemma-7-2
    (implies (and (vecisa-statep s)
                  (vecinstp (nth (mget :prc s) (vecisa-state-vecinmem s)))
                  (>= (mget :prc s) (len (vecisa-state-vecinmem s))))
             (equal (nth (1+ (get-num-inst (1- (mget :prc s)) (vecisa-state-vecinmem s)))
                         (scalarize-mem (len (vecisa-state-vecinmem s))
                                        (vecisa-state-vecinmem s)))
                    (cadr (scalarize (nth (mget :prc s) (vecisa-state-vecinmem s))))))
    :hints (("goal" :in-theory (disable scalarize-mem get-num-inst scalarize inst vecopcode-case-analysis)
             :use ((:instance nth-=>len (j (mget :prc s)) (l (vecisa-state-vecinmem s)))))))
  )
 
 (defthmd lemma-7
   (implies (and (vecisa-statep s)
                 (vecinstp (nth (mget :prc s) (vecisa-state-vecinmem s))))
            (equal (nth (1+ (get-num-inst (1- (mget :prc s)) (vecisa-state-vecinmem s)))
                        (scalarize-mem (len (vecisa-state-vecinmem s))
                                       (vecisa-state-vecinmem s)))
                   (cadr (scalarize (nth (mget :prc s) (vecisa-state-vecinmem s))))))
   :hints (("goal" :cases ((>= (mget :prc s) (len (vecisa-state-vecinmem s))) (< (mget :prc s) (len (vecisa-state-vecinmem s))))
            :in-theory (disable vecinstp instp vecisa-statep scalarize-mem flatten-len-get-num-inst))
           ("Subgoal 2" :use (:instance lemma-7-2))
           ("Subgoal 1" :use ((:instance lemma-7-1)))))
 )

(defun case-inst-1 (s)
  (equal (mget :op (nth (mget :prc s) (vecisa-state-vecinmem s)))
         'add))

(defun case-inst-2 (s)
  (equal (mget :op (nth (mget :prc s) (vecisa-state-vecinmem s)))
         'sub))

(defun case-inst-3 (s)
  (equal (mget :op (nth (mget :prc s) (vecisa-state-vecinmem s)))
         'mul))

(defthm case-inst-exhaustive
  (implies (and (vecisa-statep s)
                (instp (nth (mget :prc s) (vecisa-state-vecinmem s)))
                (not (case-inst-1 s))
                (not (case-inst-2 s)))
           (case-inst-3 s))
  :hints (("goal" :in-theory (enable instp))))

(in-theory (disable flatten-len-get-num-inst))

(defthm simulation-inst
  (implies (and (vecisa-statep s)
                (instp (nth (mget :prc s) (vecisa-state-vecinmem s)))
                (equal (vecisa-step s) u)
                (equal w (ref-map s))
                )
           (equal (isa-step w)
                  (ref-map u)))
  :hints (("goal" :use ((:instance lemma-5)
                        (:instance case-inst-exhaustive))
           :cases ((case-inst-1 s) (case-inst-2 s) (case-inst-3 s)))))

(defun case-vinst-1 (s)
  (equal (mget :op (nth (mget :prc s) (vecisa-state-vecinmem s)))
         'vadd))

(defun case-vinst-2 (s)
  (equal (mget :op (nth (mget :prc s) (vecisa-state-vecinmem s)))
         'vsub))

(defun case-vinst-3 (s)
  (equal (mget :op (nth (mget :prc s) (vecisa-state-vecinmem s)))
         'vmul))

(defthm case-vecinst-exhaustive
  (implies (and (vecisa-statep s)
                (vecinstp (nth (mget :prc s) (vecisa-state-vecinmem s)))
                (not (case-vinst-1 s))
                (not (case-vinst-2 s)))
           (case-vinst-3 s))
  :hints (("goal" :in-theory (enable vecinstp))))

(in-theory (disable vecopcode-case-analysis add-rc sub-rc mul-rc))

(defthm simulation-vecinst
  (implies (and (vecisa-statep s)
                (vecinstp (nth (mget :prc s) (vecisa-state-vecinmem s)))
                (equal (vecisa-step s) u)
                (equal w (ref-map s)))
           (equal (isa-step (isa-step w))
                  (ref-map u)))
  :hints (("goal"   :use ((:instance case-vecinst-exhaustive)
                          (:instance lemma-6)
                          (:instance lemma-7))
           :cases ((case-vinst-1 s) (case-vinst-2 s) (case-vinst-3 s)))))

(defun case-1-inst (k v)
  (and (vecinstp (nth k v))
       (not (instp (nth k v)))))

(defun case-2-inst (k v)
  (and (not (vecinstp (nth k v)))
       (instp (nth k v))))


(defthmd case-exhaustive
  (implies (and (vecimemp v)
                (natp k)
                (nth k v)
                (not (case-1-inst k v)))
           (case-2-inst k v)))

(in-theory (disable simulation-vecinst simulation-inst vecisa-step
                    vecisa-statep isa-step ref-map ))
                
(defthm impl-simulates-vecinst-run-lemma
  (implies (and (vecisa-statep s)
                (nth (mget :prc s) (vecisa-state-vecinmem s))
                (equal (vecisa-step s) u)
                (equal w (ref-map s)))
           (spec-run-upto-2-rel w (ref-map u)))
  :hints (("goal" :cases ((case-1-inst (mget :prc s) (vecisa-state-vecinmem s))
                          (case-2-inst (mget :prc s) (vecisa-state-vecinmem s)))
           :use ((:instance case-exhaustive (k (mget :prc s)) (v (vecisa-state-vecinmem s))))
           )
          ("subgoal 3" :in-theory (disable case-1-inst case-2-inst))
          ("subgoal 1" :use (:instance simulation-inst))
          ("subgoal 2" :use (:instance simulation-vecinst))))


(defthm impl-simulates-spec
  (implies (and (vecisa-statep s)
                (vecisa-statep u)
                (isa-statep w)
                (isa-statep (ref-map u))
                (equal w (ref-map s))
                (nth (mget :prc s) (vecisa-state-vecinmem s))
                (equal (vecisa-step s) u))
           (spec-step+ (ref-map s) (ref-map u)))
  :hints (("goal" :use ((:instance finite-step-implies-exists 
                                   (s (ref-map s)) (u (ref-map u)))
                        (:instance impl-simulates-vecinst-run-lemma)))))
