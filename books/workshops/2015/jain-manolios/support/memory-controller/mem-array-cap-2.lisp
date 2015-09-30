; This book contains the model and proof of skipping refinement for
; memory controller with buffer capacity = 2
(in-package "ACL2S")

; element in the stack
(defdata el nat)
(defdata add nat)
; memory cell
(defdata mem (listof nat))

; command
(defdata req (oneof (list 'read nat)
                    (list 'write nat el)
                    (list 'refresh)))

; list of commands
(defdata reqs (listof req))

(defdata sstate (record (mem-reqs . reqs)
                        (dmem . mem)
                        (pt . nat)))

(defun mread (add mem)
  "memory read"
  (declare (ignore add))
  mem)

(defun mwrite (add el mem)
  "memory write"
  (update-nth add el mem))

(defun mrefresh-aux (add mem)
" read each memory location in [1,add] and write it back !!"
(if (or (zp add) (>= add (len mem)))
      mem
    (mrefresh-aux (1- add) (mwrite add (nth add mem) mem))))

 
(defun mrefresh (mem)
  "read location [1, len-1] in the memory and write it back again."
  (mrefresh-aux (1- (len mem)) mem))

(defthm update-nth-nth-same 
  (implies (and (natp add) (< add (len mem)))
           (equal (mwrite add (nth add mem) mem)
                  mem)))

(defthm mrefresh-aux-mem-unchanged
  (implies (and (natp add) 
		(< add (len mem)))
           (equal (mrefresh-aux add mem)
                  mem))
  :hints (("goal" :in-theory (e/d () (mwrite)))))

(defthm mrefresh-mem-unchanged
  (equal (mrefresh mem)
         mem))

(in-theory (disable mrefresh))

(defun mem-step (req mem)
  "returns next state of mem"
  (let ((op (car req))
        (add (cadr req)))
   (cond ((equal op 'read)
          (mread add mem))
         ((equal op 'write)
          (mwrite add (caddr req) mem))
         ((equal op 'refresh)
          (mrefresh mem))
         (t mem))))

(defun spec-step (s)
  "single step of MEM machine"
  (let* ((pt (sstate-pt s))
         (reqs (sstate-mem-reqs s))
         (req (nth pt reqs))
         (mem (sstate-dmem s)))
    (if (reqp req)
        (sstate reqs (mem-step req mem) (1+ pt))
      (sstate reqs mem (1+ pt)))))

;; Optimized MEMC implimentation

(defun rbuf-capacity ()
  "capacity of rbuf"
  2)

(defun req-buffp (l)
  (and (reqsp l)
       (<= (len l) (rbuf-capacity))))

(program)
(defun nth-req-buff-enum (n)
  (let ((mem-reqs (nth-reqs n)))
    (if (<= (len mem-reqs) (rbuf-capacity))
        mem-reqs
      (let ((i1 (car mem-reqs))
            (i2 (cadr mem-reqs))
            (i3 (caddr mem-reqs)))
        (list i1 i2 i3)))))
(logic)
(verify-guards rbuf-capacity)
(verify-guards req-buffp)
(register-custom-type req-buff t nth-req-buff-enum req-buffp)

(defdata istate (record (dmem . mem)
                        (rbuf . req-buff)
                        (pt . nat)
                        (mem-reqs . reqs)))

(defun stutterp (req rbuf)
" machine stutters if rbuf is not full (number of entries < buffer capacity)
 and if the req is not 'read or 'refresh'"
  (and (< (len rbuf) (RBUF-CAPACITY) )
       (not (equal (car req) 'read))
       ;; (not (equal (car req) 'refresh))
       ))

(defun enque (l c)
  " enque c at the end of list l"
  (if (endp l)
      (list c)
    (cons (car l) (enque (cdr l) c))))

(defun impl-internal-step (req rbuf)
  "enque req in rbuf"
  (enque rbuf req))

(defun impl-observable-mem-step (mem rbuf)
  (cond ((endp rbuf);(equal rbuflen 0)
          mem)
         ((endp (cdr rbuf));(equal (len rbuf) 1)
          (mem-step (car rbuf) mem))
         ((endp (cddr rbuf));(equal (len rbuf) 2)
          (let* ((req1 (car rbuf))
                 (req2 (cadr rbuf))
                 (op1 (car req1))
                 (op2 (car req2))
                 (add1 (cadr req1))
                 (add2 (cadr req2))
                 (nxt-mem (if (and (equal op1 'write)
                                   (equal op2 'write)
                                   (equal add1 add2))
                              (mem-step req2 mem)
                            (mem-step req2 (mem-step req1 mem)))))
            nxt-mem))
         ((endp (cdddr rbuf));(equal (len rbuf) 3)
          (let* ((req1 (car rbuf))
                 (op1 (car req1))
                 (add1 (cadr req1))
                 (req2 (cadr rbuf))
                 (op2 (car req2))
                 (add2 (cadr req2))
                 (req3 (caddr rbuf))
                 (op3 (car req3))
                 (add3 (cadr req3))
                 (nxt-mem (cond ((and (equal op1 'write)
                                      (equal op2 'write)
                                      (equal op3 'write)
                                      (equal add1 add2)
                                      (equal add2 add3))
                                 ;; all three reqs are write to the same address
                                 (mem-step req3 mem))
                                ((and (equal op1 'write)
                                      (equal op2 'write)
                                      (equal add1 add2))
                                 ;; first two reqs are write to the same address
                                 (mem-step req3 (mem-step req2 mem)))
                                ((and (equal op2 'write)
                                      (equal op3 'write)
                                      (equal add2 add3))
                                 (mem-step req3 (mem-step req1 mem)))
                                 ;; else
                                (t (mem-step req3 (mem-step req2 (mem-step req1 mem)))))))
            nxt-mem))))

(defun impl-observable-rbuf-step (req)
  (if (equal (car req) 'read)
      nil
    (list req)))

; single step of buffered stack machine
(defun impl-step (s)
  (let* ((mem (mget :dmem s))
         (rbuf (mget :rbuf s))
         (reqs (istate-mem-reqs s))
         (pt (mget :pt s))
         (req (nth pt reqs)))
    (if (reqp req)
        (let ((nxt-mem (if (stutterp req rbuf)
                           mem
                         (impl-observable-mem-step mem rbuf)))
              (nxt-rbuf (if (stutterp req rbuf)
                            (impl-internal-step req rbuf)
                          (impl-observable-rbuf-step req)))
              (nxt-pt (1+ pt)))
          (istate nxt-mem nxt-rbuf nxt-pt reqs))
      (let ((nxt-pt (1+ pt))
            (nxt-rbuf nil) 
            (nxt-mem (impl-observable-mem-step mem rbuf)))
        (istate nxt-mem nxt-rbuf nxt-pt reqs)))))

(defun rank (s)
  (nfix (- (rbuf-capacity) (len (istate-rbuf s)))))


(defun commited-state (s)
  (let ((pt (istate-pt s))
        (rbuf (istate-rbuf s))
        (mem-reqs (istate-mem-reqs s))
        (dmem (istate-dmem s)))
    (let ((rbuflen (cond ((endp rbuf)
                          0)
                         ((endp (cdr rbuf))
                          1)
                         ((endp (cddr rbuf))
                          2))))
      (istate dmem nil (nfix (- pt rbuflen)) mem-reqs))))

(defun good-statep (s)
  (let ((pt (istate-pt s))
        (rbuf (istate-rbuf s)))
    (and (istatep s)
         (>= pt (len rbuf))
         (let* ((cms (commited-state s))
                (s-cms (cond ((endp rbuf);(equal rbuflen 0)
                              cms)
                             ((endp (cdr rbuf));(equal rbuflen 1)
                              (impl-step cms))
                             ((endp (cddr rbuf));(equal rbuflen 2)
                              (impl-step (impl-step cms)))
                             (t nil))))
               (equal s-cms s)))))

(defun ref-map (s)
  (let* ((mem-reqs (istate-mem-reqs s))
        (dmem (istate-dmem s))
        (pt (istate-pt s))
        (rbuf (istate-rbuf s)))
    (let ((rbuflen (cond ((endp rbuf)
                          0)
                         ((endp (cdr rbuf))
                          1)
                         ((endp (cddr rbuf))
                          2))))
      (sstate mem-reqs dmem (nfix (- pt rbuflen))))))


(defun spec-step-skip-rel (w v)
  "is v reachable from w in <= 5 (= (rbuf-capacity) + 1) steps. Plus 1
is to account for the case when the current inst is a TOP
instruction."
  (or (equal v (spec-step (spec-step w)))
      (equal v (spec-step (spec-step (spec-step w))))))

(defthm mset-rbuf-nil
  (equal (mset :rbuf
               nil (mset :mem-reqs (mget :mem-reqs s) nil))
         (mset :mem-reqs (mget :mem-reqs s) nil))
  :hints (("goal" :use (:instance acl2::mset-diff-mset (b :rbuf) (a :mem-reqs) (x (mget :mem-reqs s)) (y nil)
                                  (r nil))
           :in-theory (disable acl2::mset-diff-mset))))


(defthm optmemc-skip-refines-memc
  (implies (and (good-statep s)
                (equal w (ref-map s)); s and r.s are related
                (equal u (impl-step s)); s --> u
                (not (equal (ref-map u); not (wfsk2a) r.u is related
                                       ; to v (where w --> v)
                            (spec-step w)))
                (not (and (equal w (ref-map u)); not (wfsk2b) r.s and
                                               ; r.u are related and
                                               ; rank decreases
                          (< (rank u) (rank s)))))
           (spec-step-skip-rel w (ref-map u)))
  :hints (("goal" :in-theory (disable reqp))))
