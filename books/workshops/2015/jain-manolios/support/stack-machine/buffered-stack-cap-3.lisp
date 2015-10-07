; This book contains the model and proof of skipping refinement for
; stack machine with buffer capacity = 3

(in-package "ACL2S")

;; STK 
(defdata el all)

(defdata stack (listof el))

(defdata inst (oneof (list 'push el)
                     (list 'pop)
                     (list 'top)
                     (list 'nop)))

(defdata inst-mem (listof inst))

;; State of STK machine
(defdata sstate (record (imem . inst-mem)
                        (pc . nat)
                        (stk . stack)))


(defun mpush (el stk)
;  :input-contract (stackp stk) (elp el)
;  :output-contract (stackp (mpush stk el))
  (cons el stk))

(defthm mpush-contract
  (implies (stackp stk)
           (stackp (mpush el stk)))
  :rule-classes :tau-system)

(defun mpop (stk)
  "pop an element from the stk"
;  :input-contract (stackp stk)
;  :output-contract (stackp (mpop stk))
  (cdr stk))

(defthm mpop-contract
  (implies (stackp stk)
           (stackp (mpop stk)))
  :rule-classes :tau-system)


(defun mtop (stk)
  "top leaves the stack unchanged."
;  :input-contract (stackp stk)
;  :output-contract  (stackp (mtop stk))
  stk)


(defthm mtop-contract
  (implies (stackp stk)
           (stackp (mtop stk)))
  :rule-classes :tau-system)


(defun mnop (stk)
  "no-op instruction"
;  :input-contract (stackp stk)
;  :output-contract  (stackp (mnop stk))
  stk)

(defthm mnop-contract
  (implies (stackp stk)
           (stackp (mnop stk)))
  :rule-classes :tau-system)

(defun stk-step-inst (inst stk)
  "returns next state of stk "
; :input-contract (and (instp inst) (stackp stk))
; :output-contract (stackp (stk-step-inst inst stk))
  (let ((op (car inst)))
    (cond ((equal op 'push)
           (mpush (cadr inst) stk ))
          ((equal op 'pop)
           (mpop stk))
          ((equal op 'top)
           (mtop stk))
          (t stk))))

(defthm stk-step-inst-contract
  (implies (and (instp inst)
                (stackp stk))
           (stackp (stk-step-inst inst stk)))
    :rule-classes :tau-system)


(defthm push-pop-unchanged
  (equal (mpop (mpush el stk))
         stk))

(defthm mnop-unchanged
  (equal (mnop s)
         s))

(defthm mtop-unchanged
  (equal (mtop s)
         s))
  
(in-theory (disable mpush mpop mtop mnop stk-step-inst))

(defun spec-step (s)
"single step STK machine"
;  :input-contract (spec-statep s)
;  :output-contract (spec-statep (spec-step s))
(let* ((pc (sstate-pc s))
       (imem (sstate-imem s))
       (inst (nth pc imem))
       (stk (sstate-stk s)))
  (if (instp inst)
      (sstate imem (1+ pc) (stk-step-inst inst stk))
    (sstate imem (1+ pc) stk))))


;; BSTK Machine (implementation)

(defun ibuf-capacity ()
  "capacity of ibuf"
  (declare (xargs :guard t))
  3)

(defun inst-buffp (l)
  (and (inst-memp l)
       (<= (len l) (ibuf-capacity))))

(program)
(defun nth-inst-buff-enum (n)
  (let ((imem (nth-inst-mem n)))
    (if (<= (len imem) (ibuf-capacity))
        imem
      (let ((i1 (car imem))
            (i2 (cadr imem))
            (i3 (caddr imem)))
        (list i1 i2 i3)))))
(logic)
(verify-guards inst-buffp)
(register-custom-type inst-buff t nth-inst-buff-enum inst-buffp)
 
;; State of BSTK machine
(defdata istate
  (record (imem . inst-mem)
          (pc . nat)
          (stk . stack)
          (ibuf . inst-buff)))

(defun enque (el l)
  "first in first out"
; :input-contract (true-listp l)
; :output-contract (true-listp (enque el l))
  (if (endp l)
      (list el)
    (cons (car l) (enque el (cdr l)))))

(defun impl-internal-ibuf-step (inst ibuf)
  "enque the inst in ibuf"
; :input-contract (and (instp inst) (inst-memp ibuf))
; :output-contract (inst-memp (impl-internal-ibuf-step inst ibuf))
  (enque inst ibuf))

(defun impl-observable-stk-step (stk ibuf)
  "state of the stk when BSTK takes an observable step (i.e. does not
  stutter) by executing all instructions enqueued in ibuf"
;  :input-contract (and (stackp stk) (inst-memp ibuf))
;  :output-contract (stackp (impl-observable-stk-step stk ibuf))
  (cond ((endp ibuf)
         stk)
        ((endp (cdr ibuf))
         (stk-step-inst (car ibuf) stk))
        ((endp (cddr ibuf))
         (let* ((stk (stk-step-inst (car ibuf) stk))
                (stk (stk-step-inst (cadr ibuf) stk)))
           stk))
        ((endp (cdddr ibuf))
         (let* ((stk (stk-step-inst (car ibuf) stk))
                (stk (stk-step-inst (cadr ibuf) stk))
                (stk (stk-step-inst (caddr ibuf) stk)))
           stk))))


(defun impl-observable-ibuf-step (inst)
  "next state of ibuf when BSTK does not stutter"
;  :input-contract (instp inst)
;  :output-contract (instsp (impl-observable-ibuf-step inst))
  (if (equal (car inst) 'top)
      nil
    (list inst)))

(defun stutterp (inst ibuf)
  "BSTK stutters if ibuf is not full or the current instruction is not 'top"
;  :input-contract (and (instp inst) (inst-mem cbuf))
;  :output-contract (booleanp (stutterp inst cbuf))
  (and (< (len ibuf) (ibuf-capacity))
       (not (equal (car inst) 'top))))


(defun impl-step (s)
  "sigle step of BSTK"
;  :input-contract (impl-statep s)
;  :output-contract (impl-statep (impl-step s))
  (let* ((stk (istate-stk s))
         (ibuf (istate-ibuf s))
         (imem (istate-imem s))
         (pc (istate-pc s))
         (inst (nth pc imem)))
    (if (instp inst)
        (let ((nxt-pc (1+ pc))
              (nxt-stk (if (stutterp inst ibuf)
                           stk
                         (impl-observable-stk-step stk ibuf)))
              (nxt-ibuf (if (stutterp inst ibuf)
                            (impl-internal-ibuf-step inst ibuf)
                          (impl-observable-ibuf-step inst))))
          (istate imem nxt-pc nxt-stk nxt-ibuf))
      (let ((nxt-pc (1+ pc))
            (nxt-stk (impl-observable-stk-step stk ibuf))
            (nxt-ibuf nil))
        (istate imem nxt-pc nxt-stk nxt-ibuf)))))

(defthm mset-ibuf-nil
  (equal (mset :ibuf
               nil (mset :imem (mget :imem s) nil))
         (mset :imem (mget :imem s) nil))
  :hints (("goal" :use (:instance acl2::mset-diff-mset (b :ibuf) (a :imem) (x (mget :imem s)) (y nil)
                                  (r nil))
           :in-theory (disable acl2::mset-diff-mset))))

(defun commited-state (s)
  (let* ((stk (istate-stk s))
         (imem (istate-imem s))
         (ibuf (istate-ibuf s))
         (pc (istate-pc s))
         (cpc (nfix (- pc (len ibuf)))))
    (istate imem cpc stk nil)))

  
(defun good-statep (s)
  "if it is reachable from a commited-state in |ibuf| steps"
  (let ((pc (istate-pc s))
        (ibuf (istate-ibuf s)))
    (and (istatep s)
         (>= pc (len ibuf))
         (let* ((cms (commited-state s))
                (s-cms (cond ((endp ibuf)
                              cms)
                             ((endp (cdr ibuf))
                              (impl-step cms))
                             ((endp (cddr ibuf))
                              (impl-step (impl-step cms)))
                             ((endp (cdddr ibuf))
                              (impl-step (impl-step (impl-step cms))))
                             (t cms))))
           (equal s-cms s)))))
  
(defthm good-statep-implies-istatep
  (implies (good-statep s)
           (istatep s)))

(defthm commited-state-good-state
  (implies (good-statep s)
           (good-statep (commited-state s)))
  :hints (("goal" :in-theory (e/d (istate istatep)(impl-step)))))

(defthm good-state-inductive
  (implies (good-statep s)
           (good-statep (impl-step s)))
  :hints (("goal" :in-theory (e/d (istatep)(instp)))))
          

(defun ref-map (s)
  "refinement map returns the observable state of istate. This version
assumes the capacity of ibuf = 2"
  ;(declare (xargs :guard (good-statep s)))
  (let* ((stk (istate-stk s))
         (imem (istate-imem s))
         (pc (istate-pc s))
         (ibuf (istate-ibuf s))
         (ibuflen (cond ((endp ibuf)
                         0)
                        ((endp (cdr ibuf))
                         1)
                        ((endp (cddr ibuf))
                         2)
                        ((endp (cdddr ibuf))
                         3)
                        (t 0)))
         (rpc (nfix (- pc ibuflen))))
    (sstate imem rpc stk)))

(defun rank (s)
  "rank of an istate s is capacity of ibuf - #inst in ibuf"
  (nfix (- (ibuf-capacity) (len (istate-ibuf s)))))


(defun spec-step-skip-rel (w v)
  "is v reachable from w in <= 4 (= (ibuf-capacity) + 1) steps. Plus 1
is to account for the case when the current inst is a TOP
instruction."
  (or (equal v (spec-step (spec-step w)))
      (equal v (spec-step (spec-step (spec-step w))))
      (equal v (spec-step (spec-step (spec-step (spec-step w)))))))


;; Final theorem BSTK refines STK
#|
; The following form should work.  However, since it
; takes 3 hours (in 2015), we comment it and let the
; interested user submit it themselves.

(defthm bstk-skip-refines-stk
  (implies (and (good-statep s)
                (equal w (ref-map s)) ; s and r.s are related
                (equal u (impl-step s)) ; s --> u
                (not (equal (ref-map u); (wfsk2a) r.u is related to v
                                       ; (where w --> v)
                            (spec-step w)))
                (not (and (equal w (ref-map u)); (wfsk2b) r.s and r.u
                                               ; are related and rank
                                               ; decreases
                          (< (rank u) (rank s)))))
           (spec-step-skip-rel w (ref-map u)))
  :hints (("goal" :in-theory (e/d (stk-step-inst) (instp )))))

|#
