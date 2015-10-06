; Copyright (C) 2015, Regents of the University of Texas
; Written by Ben Selfridge
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

;; SB
;;
;; SB is simple parallel architecture model with store buffers. The model is
;; meant to be a simple, generic architecture model, with concurrency and
;; memory semantics that closely adhere to the x86-TSO memory model, the de
;; facto specification for concurrent x86 memory operations.
;;
;; The model consists primarily of 1) a list of processors and 2) a shared
;; memory. It also has a global lock for executing locked instructions that
;; perform several memory operations in sequence that must remain atomic.
;;
;; Each processor consists of a program (list of instructions), a program
;; counter, a store buffer for pending writes to the system's shared memory,
;; and an alist mapping register ``names'' (symbols) to values
;; (integers). The store buffer is a list of pending writes, treated
;; as a FIFO queue; primitive write operations either enqueue a write onto this
;; buffer, or dequeue the oldest write from the ``back'' of the buffer and
;; commit the write to shared memory. Each processor can see its own writes
;; transparently as if they were already in memory (this is modeled by the
;; function lookup-addr, which represents a particular processor's current view
;; of the memory), and no processor can see the contents of another processor's
;; store buffer.
;;
;; Each processor also has two additional fields: phase and
;; tmp-data. Individual instructions may involve multiple primitive
;; ``operations''; for instance, reading a value from memory into a register
;; involves at least two (potentially three) operations: 1) look up the most
;; recent write to the given address in the store buffer; 2) if there are no
;; writes to that location in the buffer, look it up in memory and 3) store the
;; value in the indicated register. These three operations are grouped together
;; in the mrmov instruction, and are separated into three distinct ``phases.''
;; The pc tells us which instruction we are executing, and the ``phase'' field
;; of a proc tells us which phase of that instruction we are in. The tmp-data
;; field is used to store temporary data between the execution of distinct
;; phases of a single instruction; for example, after a value is read from
;; memory in an mrmov, it is stored in tmp-data so that when the final phase of
;; the instruction executes, the value can be retrieved and loaded in a
;; register. 
;;
;; The shared memory is an alist mapping symbols to values (integers).

(in-package "SB")
(set-ignore-ok t)

(in-theory (disable assoc put-assoc nth update-nth))

(defrule assoc-of-put-assoc
  (equal (assoc k1 (put-assoc k2 v a))
         (if (equal k1 k2)
             (cons k1 v)
           (assoc k1 a)))
  :enable (assoc put-assoc))

(defrule not-assoc-nil
  (not (assoc a nil))
  :enable assoc)

(defrule acl2-numberp-of-integerp
  (implies (integerp x)
           (acl2-numberp x)))

;; TODO -- at some point I think I want to define a special function memoryi or
;; something to look up the value at an address, with a default value of 0 if
;; the address is not present.

;; MEMORY
;; In our memory, addresses will be symbols.
(defalist memory
  :key-type symbolp
  :val-type integerp
  :true-listp t

  ///
  (defrule put-assoc-memory
    (implies (and (memory-p mem)
                  (symbolp dest)
                  (integerp val))
             (memory-p (put-assoc dest val mem)))
    :enable put-assoc)
  (defrule assoc-memory
    (implies (and (memory-p mem)
                  (assoc loc mem))
             (and (consp (assoc loc mem))
                  (symbolp (car (assoc loc mem)))
                  (integerp (cdr (assoc loc mem)))))
    :enable assoc)
  (defrule memory-eqlable-alistp
    (implies (memory-p mem)
             (eqlable-alistp mem))))

;; REGISTERS
(defalist registers
  :key-type symbolp
  :val-type integerp
  :true-listp t
  
  ///
  (defrule put-assoc-registers
    (implies (and (registers-p registers)
                  (symbolp reg)
                  (integerp val))
             (registers-p (put-assoc reg val registers)))
    :enable put-assoc)
  (defrule assoc-registers
    (implies (and (registers-p registers)
                  (assoc reg registers))
             (and (consp (assoc reg registers))
                  (symbolp (car (assoc reg registers)))
                  (integerp (cdr (assoc reg registers)))))
    :enable assoc))

;; STORE BUFFER ELEMENT
; A store buffer element is a pair (value destination)
(defprod sb-element
  ((addr symbolp)
   (val integerp)))

;; STORE BUFFER
; A store buffer is a true-listp of sb-elements
(deflist sb
  :elt-type sb-element
  :true-listp t)

;; We do not need the next four functions, but we keep them around
;; anyway. 
(define sb-enq
  ((x sb-element-p)
   (sb sb-p))
  :returns (sb-plus-x (and (sb-p sb-plus-x)
                           (consp sb-plus-x))
                      :hyp :fguard)
  (cons x sb))

(define sb-next
  ((sb (and (sb-p sb)
            (consp sb))))
  :returns (x sb-element-p
              :hyp :fguard)
  (car (last sb)))

(define sb-deq
  ((sb (and (sb-p sb)
            (consp sb))))
  :returns (sb-minus-x sb-p
                       :hyp :fguard)
  (if (endp (cdr sb))
      nil
    (cons (car sb) (sb-deq (cdr sb))))
  
  ///
  (defrule acl2-count-sb-deq
    (implies (and (< 0 (acl2-count sb)))
             (< (acl2-count (sb-deq sb))
                (acl2-count sb)))
    :rule-classes :linear))

(define sb-latest
  ((addr symbolp)
   (sb sb-p))
  :returns (most-recent
            (implies (not (sb-element-p most-recent))
                     (equal most-recent nil))
            :hyp :fguard)
  (b*
   (((when (endp sb)) nil)
    ((sb-element sb-elt) (car sb)))
   (if (eq sb-elt.addr addr)
       sb-elt
     (sb-latest addr (cdr sb))))

  ///
  (defrule sb-latest-implies-not-empty
    (implies (and (sb-p sb)
                  (symbolp addr)
                  (sb-latest addr sb))
             (consp sb)))
  ;; case split!!!
  (defrule sb-latest-sb-enq
    (equal (sb-latest addr (sb-enq sb-elt sb))
           (if (equal (sb-element->addr sb-elt) addr)
               sb-elt
             (sb-latest addr sb)))
    :enable sb-enq)
  (defrule sb-latest-sb-deq
    (implies (and (sb-p sb)
                  (sb-latest addr sb)
                  (sb-latest addr (sb-deq sb)))
             (equal (sb-latest addr (sb-deq sb))
                    (sb-latest addr sb)))
    :enable sb-deq)
  (defrule sb-latest-sb-deq-2
    (implies (and (sb-p sb)
                  (sb-latest addr sb)
                  (not (sb-latest addr (sb-deq sb)))
                  (symbolp addr))
             (equal (sb-element->addr (sb-next sb)) addr))
    :enable (sb-deq sb-next))
  (defrule sb-latest-sb-deq-3
    (implies (and (sb-p sb)
                  (sb-latest addr sb)
                  (not (sb-latest addr (sb-deq sb)))
                  (symbolp addr))
             (equal (sb-latest addr sb)
                    (sb-next sb)))
    :enable (sb-next sb-deq))
  (defrule sb-latest-sb-deq-4
    (implies (and (sb-p sb)
                  (not (sb-latest addr sb))
                  (symbolp addr))
             (not (sb-latest addr (sb-deq sb))))
    :enable sb-deq)
  (defrule sb-latest-sb-next-not-nil
    (implies (and (sb-p sb)
                  (consp sb))
             (sb-latest (sb-element->addr (sb-next sb)) sb))
    :enable (sb-next sb-deq)))

;; INSTRUCTIONS
(deftagsum instruction
  (:mrmov ((addr symbolp) (reg symbolp)) :base-name mrmov)
  (:rmmov ((reg symbolp) (addr symbolp)) :base-name rmmov)
  (:irmov ((val integerp) (reg symbolp)) :base-name irmov)
  (:immov ((val integerp) (addr symbolp)) :base-name immov)
  (:ifz ((reg symbolp) (line natp)) :base-name ifz)
  (:lock () :base-name lock)
  (:unlock () :base-name unlock)
  (:fence () :base-name fence)
  (:no-op () :base-name no-op))

(deflist program
  :elt-type instruction
  :true-listp t)

(defrule nth-program
  (implies (and (natp pc)
                (< pc (len program))
                (program-p program))
           (instruction-p (nth pc program)))
  :enable nth)

;; PROCESSOR
(defprod proc
  ((program program-p)
   (pc natp)
   (sb sb-p)
   (registers registers-p)
   (phase natp)
   (tmp-data integerp))
  :require t)

;; PROCESSOR LIST
(deflist proc-list
  :elt-type proc
  :true-listp t

  ///
  (defrule index-proc-list
    (implies (and (proc-list-p proc-list)
                  (natp i)
                  (< i (len proc-list)))
             (proc-p (nth i proc-list)))
    :enable nth)
  (defrule update-proc-list
    (implies (and (proc-list-p proc-list)
                  (natp i)
                  (< i (len proc-list))
                  (proc-p new-proc))
             (proc-list-p (update-nth i new-proc proc-list)))
    :enable update-nth))

;; LOCK - either natp, or nil.
(define lockp (x)
  :returns (lock? booleanp)
  (or (equal x nil)
      (natp x))

  ///
  (defrule lockp-is-integerp
    (implies (and (lockp x) x)
             (integerp x)))
  (defrule lockp-is-acl2-numberp
    (implies (and (lockp x) x)
             (acl2-numberp x)))
  (defrule lockp-if-nil
    (implies (not x)
             (lockp x)))
  (defrule lock-if-natp
    (implies (natp x)
             (lockp x))))

(define lockp-fix (x)
  :returns (x-lockp lockp)
  (if (lockp x) x nil))

(deffixtype lock
  :pred lockp
  :fix lockp-fix
  :equiv equal)

(defrule lockp-fix-lockp
  (implies (lockp x)
           (equal (lockp-fix x) x))
  :enable (lockp lockp-fix))

(defprod machine
  ((procs proc-list)
   (mem memory-p)
   (lock lockp)))

;;;;;;;;;;;;;;;;;;;;;;;;;;
;; MISC STATE FUNCTIONS ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;

(define num-procs ((m machine-p))
  :returns (num-procs natp)
  (len (machine->procs m))

  ///
  (defrule nth-proc
    (implies (and (machine-p m)
                  (natp proc-num)
                  (< proc-num (num-procs m)))
             (proc-p (nth proc-num (machine->procs m)))))
  (defrule proc-num-<-num-procs-len
    (implies (< proc-num (num-procs m))
             (< proc-num (len (machine->procs m)))))
  (defrule proc-num-<-len-num-procs
    (implies (< proc-num (len (machine->procs m)))
             (< proc-num (num-procs m))))
  (defrule num-procs-machine-update-nth
    (implies (and (machine-p m)
                  (natp proc-num)
                  (< proc-num (num-procs m)))
             (equal (num-procs
                     (machine (update-nth proc-num new-proc (machine->procs m))
                              mem
                              lock))
                    (num-procs m))))
  (defrule num-procs-machine-machine->procs
    (equal (num-procs (machine (machine->procs m) mem lock))
           (num-procs m))))

;; Note -- we could define this to include the scenario where the lock
;; is a number that is invalid (i.e. larger than the actual number of
;; processors). I'm not sure if this is needed now so I'm just
;; defining this function in the obvious way.
(define not-blocked
  ((m machine-p)
   (proc-num (and (natp proc-num)
                  (< proc-num (num-procs m)))))
  :returns (not-blocked? booleanp)
  (b* (((machine m) m))
      (or (equal m.lock nil)
          (= m.lock proc-num))))

(defrule len-consp
  (implies (and (true-listp x)
                x)
           (consp x)))

(define no-pending-sb
  ((sb sb-p)
   (addr symbolp))
  (b* (((when (endp sb)) t)
       ((sb-element sb-elt) (car sb)))
      (if (equal sb-elt.addr addr)
          nil
        (no-pending-sb (cdr sb) addr)))

  ///
  (defrule no-pending-sb-sb-next
    (implies (and (sb-p sb)
                  (consp sb))
             (not (no-pending-sb sb (sb-element->addr (sb-next sb)))))
    :enable sb-next)
  ;; When deq-ing the store buffer causing the SB to no longer contain a
  ;; pending write to a particular location, sb-next and sb-latest are equal.
  (defrule no-pending-sb-sb-next-deq
    (implies (and (sb-p sb)
                  (consp sb)
                  (not (no-pending-sb sb addr))
                  (no-pending-sb (sb-deq sb) addr))
             (equal (sb-latest addr sb)
                    (sb-next sb)))
    :enable (sb-next sb-latest sb-deq))
  (defrule not-no-pending-latest
    (implies (and (sb-p sb)
                  (consp sb)
                  (not (no-pending-sb (sb-deq sb) addr)))
             (equal (sb-latest addr (sb-deq sb))
                    (sb-latest addr sb)))
    :enable (sb-deq sb-latest))
  (defrule no-pending-sb-deq
    (implies (and (sb-p sb)
                  (no-pending-sb sb addr))
             (no-pending-sb (sb-deq sb) addr))
    :enable sb-deq)
  (defrule no-pending-sb-sb-latest
    (implies (and (sb-p sb)
                  (no-pending-sb sb addr)
                  (symbolp addr))
             (not (sb-latest addr sb)))
    :enable sb-latest)
  (defrule no-pending-sb-sb-latest-2
    (implies (and (sb-p sb)
                  (symbolp addr)
                  (not (sb-latest addr sb)))
             (no-pending-sb sb addr))
    :enable sb-latest)
  (defrule sb-next-no-pending-sb
    (implies (and (sb-p sb)
                  (consp sb)
                  (symbolp addr)
                  (no-pending-sb sb addr))
             (not (equal (sb-element->addr (sb-next sb))
                         addr))))
  (defrule no-pending-sb-not-consp
    (implies (and (not (consp sb)))
             (no-pending-sb sb addr))))

(define no-pending
  ((m machine-p)
   (proc-num (and (natp proc-num)
                  (< proc-num (num-procs m))))
   (addr symbolp))
  :returns (no-pending? booleanp)
  (b* (((machine m) m)
       ((proc proc) (nth proc-num m.procs)))
      (no-pending-sb proc.sb addr))

  ///
  ;; no-pending always returns nil if given the address of its next pending
  ;; write. 
  (defrule no-pending-sb-next
    (implies (and (machine-p m)
                  (natp i)
                  (< i (num-procs m))
                  (consp (proc->sb (nth i (machine->procs m)))))
             (not (no-pending 
                     m i
                     (sb-element->addr
                      (sb-next (proc->sb (nth i (machine->procs m)))))))))
  (defrule consp-when-not-no-pending
    (implies (and (machine-p m)
                  (natp i)
                  (< i (num-procs m))
                  (not (no-pending m i addr)))
             (consp (proc->sb (nth i (machine->procs m)))))
    :enable no-pending-sb)
  (defrule no-pending-when-not-consp
    (implies (and (machine-p m)
                  (natp i)
                  (< i (num-procs m))
                  (not (consp (proc->sb (nth i (machine->procs m))))))
             (no-pending m i addr))
    :enable no-pending-sb)
  (defrule sb-latest-no-pending
    (implies (and (machine-p m)
                  (natp i)
                  (< i (num-procs m))
                  (no-pending m i addr)
                  (symbolp addr))
             (not (sb-latest addr (proc->sb (nth i (machine->procs m)))))))
  (defrule sb-latest-no-pending-2
    (implies (and (machine-p m)
                  (natp i)
                  (< i (num-procs m))
                  (symbolp addr)
                  (not (sb-latest addr (proc->sb (nth i (machine->procs m))))))
             (no-pending m i addr)))
  (defrule sb-next-no-pending
    (implies (and (machine-p m)
                  (natp i)
                  (< i (num-procs m))
                  (consp (proc->sb (nth i (machine->procs m))))
                  (symbolp addr)
                  (no-pending m i addr))
             (not (equal (sb-element->addr
                          (sb-next (proc->sb (nth i (machine->procs m)))))
                         addr)))
    :enable no-pending-sb))

;;;;;;;;;;;;;;;;;;;;;
;; ACCESS TO STATE ;;
;;;;;;;;;;;;;;;;;;;;;

;; Functions that access properties of the state without needing any kind of
;; precondition to be satisfied first. These functions are for stating and
;; proving theorems about a program, NOT for implementation of the model.

;; The functions defined here are lookup-addr-mem and
;; lookup-addr. lookup-addr-mem simply looks up a given address in the shared 
;; memory, ignoring the contents of all the store buffers. lookup-addr presents
;; the particular view of the memory enjoyed by an individual processor; by
;; using this function in our invariants we can sometimes avoid saying anything
;; about the store buffers.

(define lookup-addr-mem
  ((m (and (machine-p m)))
   (addr (symbolp addr)))
  :returns (val integerp :hyp :fguard)
  (b* (((machine m) m)
       (lookup-addr-mem (assoc addr m.mem))
       (val (if lookup-addr-mem (cdr lookup-addr-mem) 0)))
      val))

(define lookup-addr
  ((m (and (machine-p m)))
   (i (and (natp i)
           (< i (num-procs m))))
   (addr (symbolp addr)))
  :returns (val integerp :hyp :fguard)
  (b* (((machine m) m)
       ((proc proc) (nth i m.procs))
       (lookup-addr-sb (sb-latest addr proc.sb))
       (lookup-addr-mem (lookup-addr-mem m addr)))
      (if lookup-addr-sb
          (sb-element->val lookup-addr-sb)
        lookup-addr-mem)))

(defrule lookup-addr-no-pending
  (implies (and (machine-p m)
                (symbolp addr)
                (natp i)
                (< i (num-procs m))
                (no-pending m i addr))
           (equal (lookup-addr m i addr)
                  (lookup-addr-mem m addr)))
  :enable (lookup-addr lookup-addr-mem))

;;;;;;;;;;;;;;;;;;;;;;;
;; STATE TRANSITIONS ;;
;;;;;;;;;;;;;;;;;;;;;;;

;; Here we define the nine different ``transitions'' from the x86-TSO memory
;; model. Most of these transitions have certain preconditions that are modeled
;; here by guards. The step function must first check that the guards are
;; satisfied before allowing the processor to execute the memory operation.

; preconditions: not-blocked and not-pending. We omit the requirement
; that the address is *in* the memory because in our model, we
; consider all addresses to exist within the memory and contain some
; value (0 is the default, if the address is not present in the memory
; alist). 
(define read-mem
  ((m (and (machine-p m)))
   (proc-num (and (natp proc-num)
                  (< proc-num (num-procs m))
                  (not-blocked m proc-num))) ; PRECONDITION
   (addr (and (symbolp addr)
              (no-pending m proc-num addr)))) ; PRECONDITION
  :returns (val integerp :hyp :fguard)
  (b* (((machine m) m)
       (read-mem (assoc addr m.mem))
       (val (if read-mem (cdr read-mem) 0)))
      val)

  ///

  (defrule read-mem-lookup-addr-mem
    (implies (and (machine-p m) (natp i) (< i (num-procs m)))
             (equal (read-mem m i addr)
                    (lookup-addr-mem m addr)))
    :enable lookup-addr-mem))


; preconditions: not-blocked. The preconditions about existence of a
; write in the store buffer, and it being the ``latest'' write, are
; theorems that need to be proved about sb-latest, and thus are not
; really preconditions for this function.
(define read-sb
  ((m (and (machine-p m)))
   (proc-num (and (natp proc-num)
                  (< proc-num (num-procs m))
                  (not-blocked m proc-num))) ; PRECONDITION
   (addr symbolp))
  :returns (val (implies (not (integerp val))
                         (equal val nil))
                :hyp :fguard)
  (b* (((machine m) m)
       ((proc proc) (nth proc-num m.procs))
       (read-sb (sb-latest addr proc.sb)))
      (if read-sb (sb-element->val read-sb) nil))
  
  ///

  (defrule read-sb-no-pending
    (implies (and (machine-p m)
                  (natp i)
                  (< i (num-procs m))
                  (symbolp addr)
                  (no-pending m i addr))
             (not (read-sb m i addr))))

  (defrule read-sb-no-pending-2
    (implies (and (machine-p m)
                  (natp i)
                  (< i (num-procs m))
                  (symbolp addr)
                  (not (read-sb m i addr)))
             (no-pending m i addr)))

  (defrule lookup-addr-read-sb
    (implies (and (machine-p m)
                  (natp i)
                  (< i (num-procs m))
                  (symbolp addr))
             (equal (lookup-addr m i addr)
                    (if (no-pending m i addr)
                        (read-mem m i addr)
                      (read-sb m i addr))))
    :enable (lookup-addr lookup-addr-mem)))

; preconditions: none. We omit the requirement that the register has
; some value because all registers are assumed to exist (i.e. all
; symbols correspond to some register) and the value is 0 by default
; (just like memory).
(define read-reg
  ((m (and (machine-p m)))
   (proc-num (and (natp proc-num)
                  (< proc-num (num-procs m))))
   (reg symbolp))
  :returns (val integerp :hyp :fguard)
  (b* (((machine m) m)
       ((proc proc) (nth proc-num m.procs))
       ;; get val from register (default value is 0)
       (val (if (assoc reg proc.registers)
                (cdr (assoc reg proc.registers))
              0)))
      val))

; preconditions: none. We can always write to our own store buffer,
; regardless of whether the system is locked or not.
(define write-sb
  ((m (and (machine-p m)))
   (proc-num (and (natp proc-num)
                  (< proc-num (num-procs m))))
   (val integerp)
   (addr symbolp))
  :returns (m-prime machine-p :hyp :fguard)
  (b* (((machine m) m)
       ((proc proc) (nth proc-num m.procs))
       (new-sb (sb-enq (sb-element addr val) proc.sb))
       (new-proc (proc proc.program
                       proc.pc
                       new-sb
                       proc.registers
                       proc.phase
                       proc.tmp-data))
       (new-procs (update-nth proc-num new-proc m.procs)))
      (machine new-procs m.mem m.lock))

  ///
  (defrule write-sb-num-procs
    (implies (and (natp proc-num)
                  (< proc-num (num-procs m)))
             (equal (num-procs (write-sb m proc-num val addr))
                    (num-procs m)))
    :enable num-procs)
  (defrule write-sb-program
    (implies (and (natp proc-num)
                  (< proc-num (num-procs m))
                  (natp i))
             (equal (proc->program
                     (nth i (machine->procs
                             (write-sb m proc-num val addr))))
                    (proc->program (nth i (machine->procs m))))))
  (defrule write-sb-latest
    (implies (and (machine-p m)
                  (natp i)
                  (< i (num-procs m))
                  (natp j)
                  (< j (num-procs m))
                  (symbolp addr0)
                  (symbolp addr1))
             (equal (sb-latest addr0
                               (proc->sb
                                (nth i (machine->procs
                                        (write-sb m j val addr1)))))
                    (if (and (equal addr0 addr1)
                             (equal i j))
                        (sb-element addr1 val)
                      (sb-latest addr0
                                 (proc->sb
                                  (nth i (machine->procs m))))))))
  (defrule pc-write-sb
    (implies (and (machine-p m)
                  (natp i)
                  (< i (num-procs m))
                  (natp j)
                  (< j (num-procs m)))
             (equal (proc->pc (nth i (machine->procs (write-sb m j val addr))))
                    (proc->pc (nth i (machine->procs m))))))
  (defrule phase-write-sb
    (implies (and (machine-p m)
                  (natp i)
                  (< i (num-procs m))
                  (natp j)
                  (< j (num-procs m)))
             (equal (proc->phase
                     (nth i (machine->procs (write-sb m j val addr))))
                    (proc->phase (nth i (machine->procs m))))))
  (defrule tmp-data-write-sb
    (implies (and (machine-p m)
                  (natp i)
                  (< i (num-procs m))
                  (natp j)
                  (< j (num-procs m)))
             (equal (proc->tmp-data
                     (nth i (machine->procs (write-sb m j val addr))))
                    (proc->tmp-data (nth i (machine->procs m))))))
  (defrule read-reg-write-sb
    (implies (and (machine-p m)
                  (natp i)
                  (< i (num-procs m))
                  (natp j)
                  (< j (num-procs m)))
             (equal (read-reg (write-sb m j val addr1) i reg)
                    (read-reg m i reg)))
    :enable read-reg)
  (defrule read-mem-write-sb
    (implies (and (machine-p m)
                  (natp i)
                  (< i (num-procs m))
                  (natp j)
                  (< j (num-procs m)))
             (equal (read-mem (write-sb m j val addr1) i addr2)
                    (read-mem m i addr2)))
    :enable read-mem)
  (defrule read-sb-write-sb
    (implies (and (machine-p m)
                  (natp i)
                  (< i (num-procs m))
                  (natp j)
                  (< j (num-procs m))
                  (symbolp addr1)
                  (symbolp addr2)
                  (integerp val))
             (equal (read-sb (write-sb m j val addr1) i addr2)
                    (if (and (equal i j)
                             (equal addr1 addr2))
                        val
                      (read-sb m i addr2))))
    :enable read-sb)
  (defrule no-pending-write-sb
    (implies (and (machine-p m)
                  (natp i)
                  (< i (num-procs m))
                  (natp j)
                  (< j (num-procs m))
                  (symbolp addr1)
                  (symbolp addr2))
             (equal (no-pending (write-sb m j val addr1) i addr2)
                    (if (and (= i j) (equal addr1 addr2))
                        nil
                      (no-pending m i addr2))))
    :enable (no-pending
             no-pending-sb
             sb-enq))
  (defrule not-blocked-write-sb
    (implies (and (machine-p m)
                  (natp i)
                  (< i (num-procs m))
                  (natp j)
                  (< j (num-procs m)))
             (equal (not-blocked (write-sb m j val addr) i)
                    (not-blocked m i)))
    :enable not-blocked)
  (defrule lookup-addr-mem-write-sb
    (implies (and (machine-p m)
                  (natp i)
                  (< i (num-procs m))
                  (symbolp addr1)
                  (symbolp addr2))
             (equal (lookup-addr-mem (write-sb m j val addr1) addr2)
                    (lookup-addr-mem m addr2)))
    :enable lookup-addr-mem)
  (defrule lookup-addr-write-sb
    (implies (and (machine-p m)
                  (natp i)
                  (< i (num-procs m))
                  (natp j)
                  (< j (num-procs m))
                  (symbolp addr1)
                  (symbolp addr2)
                  (integerp val))
             (equal (lookup-addr (write-sb m j val addr1) i addr2)
                    (if (and (equal i j)
                             (equal addr1 addr2))
                        val
                      (lookup-addr m i addr2))))
    :enable lookup-addr
    :disable write-sb))                          

; preconditions: not-blocked. We omit the requirement that the write
; is the oldest in the buffer because that's inherent to the sb-next
; function. Also, we allow a processor to ``flush'' even if its buffer
; is empty; it's just a no-op. 
(define flush-sb
  ((m (and (machine-p m)))
   (proc-num (and (natp proc-num)
                  (< proc-num (num-procs m))
                  (not-blocked m proc-num))))
  :returns (m-prime machine-p :hyp :fguard)
  (b* (((machine m) m)
       ((proc proc) (nth proc-num m.procs))
       ((when (endp proc.sb)) m)
       ((sb-element pending-write) (sb-next proc.sb))
       (new-sb (sb-deq proc.sb))
       (new-proc (proc proc.program
                       proc.pc
                       new-sb
                       proc.registers
                       proc.phase
                       proc.tmp-data))
       (new-procs (update-nth proc-num new-proc m.procs))
       (new-mem (put-assoc pending-write.addr
                           pending-write.val
                           m.mem)))
      (machine new-procs new-mem m.lock))

  ///
  (defrule flush-sb-num-procs
    (implies (and (natp proc-num)
                  (< proc-num (num-procs m)))
             (equal (num-procs (flush-sb m proc-num))
                    (num-procs m)))
    :enable num-procs)
  (defrule flush-sb-program
    (implies (and (natp proc-num)
                  (< proc-num (num-procs m))
                  (natp i))
             (equal (proc->program (nth i (machine->procs
                                           (flush-sb m proc-num))))
                    (proc->program (nth i (machine->procs m))))))
  (defrule read-reg-flush-sb
    (implies (and (machine-p m)
                  (natp i)
                  (< i (num-procs m))
                  (natp j)
                  (< j (num-procs m)))
             (equal (read-reg (flush-sb m i) j reg)
                    (read-reg m j reg)))
    :enable read-reg)
  (defrule pc-flush-sb
    (implies (and (machine-p m)
                  (natp i)
                  (< i (num-procs m))
                  (natp j)
                  (< j (num-procs m)))
             (equal (proc->pc (nth i (machine->procs (flush-sb m j))))
                    (proc->pc (nth i (machine->procs m))))))
  (defrule phase-flush-sb
    (implies (and (machine-p m)
                  (natp i)
                  (< i (num-procs m))
                  (natp j)
                  (< j (num-procs m)))
             (equal (proc->phase (nth i (machine->procs (flush-sb m j))))
                    (proc->phase (nth i (machine->procs m))))))
  (defrule tmp-data-flush-sb
    (implies (and (machine-p m)
                  (natp i)
                  (< i (num-procs m))
                  (natp j)
                  (< j (num-procs m)))
             (equal (proc->tmp-data (nth i (machine->procs (flush-sb m j))))
                    (proc->tmp-data (nth i (machine->procs m))))))

  ;; The following two rules address what happens to the memory when we flush
  ;; a single write from a store buffer.
  (defrule lookup-addr-mem-flush-sb-no-pending
    (implies (and (machine-p m)
                  (natp i)
                  (< i (num-procs m))
                  (no-pending m i addr))
             (equal (lookup-addr-mem (flush-sb m i) addr)
                    (lookup-addr-mem m addr)))
    :enable lookup-addr-mem)
  (defrule lookup-addr-mem-flush-sb-pending
    (implies (and (machine-p m)
                  (natp i)
                  (< i (num-procs m))
                  (consp (proc->sb (nth i (machine->procs m))))
                  (no-pending (flush-sb m i) i addr))
             (equal (lookup-addr-mem (flush-sb m i) addr)
                    (if (equal addr 
                               (sb-element->addr
                                (sb-next (proc->sb (nth i (machine->procs m))))))
                        (sb-element->val
                         (sb-next (proc->sb (nth i (machine->procs m)))))
                      (lookup-addr-mem m addr))))
    :enable (lookup-addr-mem no-pending))
  ;; if we flush our store buffer, the memory looks the same to us
  (defrule lookup-addr-flush-sb-same
    (implies (and (machine-p m)
                  (natp i)
                  (< i (num-procs m))
                  (symbolp addr))
             (equal (lookup-addr (flush-sb m i) i addr)
                    (lookup-addr m i addr)))
    :enable (lookup-addr lookup-addr-mem))
  (defrule lookup-addr-flush-sb-no-pending
    (implies (and (machine-p m)
                  (natp i)
                  (< i (num-procs m))
                  (natp j)
                  (< j (num-procs m))
                  (symbolp addr)
                  (no-pending m j addr))
             (equal (lookup-addr (flush-sb m j) i addr)
                    (lookup-addr m i addr)))
    :enable (lookup-addr lookup-addr-mem))
  (defrule sb-latest-flush-sb
    (implies (and (machine-p m)
                  (natp i)
                  (< i (num-procs m))
                  (not (no-pending (flush-sb m i) i addr)))
             (equal (sb-latest addr
                               (proc->sb
                                (nth i (machine->procs (flush-sb m i)))))
                    (sb-latest addr
                               (proc->sb (nth i (machine->procs m))))))
    :enable (no-pending))
  (defrule sb-latest-sb-next-flush
    (implies (and (machine-p m)
                  (natp i)
                  (< i (num-procs m))
                  (not (no-pending m i addr))
                  (no-pending (flush-sb m i) i addr))
             (equal (sb-latest addr (proc->sb (nth i (machine->procs m))))
                    (sb-next (proc->sb (nth i (machine->procs m))))))
    :enable no-pending)
  (defrule no-pending-flush-sb-1
    (implies (and (machine-p m)
                  (natp i)
                  (< i (num-procs m))
                  (no-pending m i addr))
             (no-pending (flush-sb m i) i addr))
    :enable no-pending)
  (defrule no-pending-flush-sb-2
    (implies (and (machine-p m)
                  (natp i)
                  (< i (num-procs m))
                  (natp j)
                  (< j (num-procs m))
                  (not (= i j)))
             (equal (no-pending (flush-sb m j) i addr)
                    (no-pending m i addr)))
    :enable no-pending)
  (defrule read-mem-flush-sb-no-pending
    (implies (and (machine-p m)
                  (natp i)
                  (< i (num-procs m))
                  (natp j)
                  (< j (num-procs m))
                  (no-pending m j addr))
             (equal (read-mem (flush-sb m j) i addr)
                    (read-mem m i addr)))
    :enable read-mem)
  (defrule not-blocked-flush-sb
    (implies (and (machine-p m)
                  (natp i)
                  (< i (num-procs m))
                  (natp j)
                  (< j (num-procs m)))
             (equal (not-blocked (flush-sb m j) i)
                    (not-blocked m i)))
    :enable not-blocked))

; preconditions: none. We can always put a value in our own register.
(define write-reg
  ((m (and (machine-p m)))
   (proc-num (and (natp proc-num)
                  (< proc-num (num-procs m))))
   (val integerp)
   (reg symbolp))
  :returns (m-prime machine-p :hyp :fguard)
  (b* (((machine m) m)
       ((proc proc) (nth proc-num m.procs))
       (new-registers
        (put-assoc reg val proc.registers))
       (new-proc (proc proc.program
                       proc.pc
                       proc.sb
                       new-registers
                       proc.phase
                       proc.tmp-data))
       (new-procs (update-nth proc-num new-proc m.procs)))
      (machine new-procs m.mem m.lock))

  ///
  (defrule write-reg-num-procs
    (implies (and (natp proc-num)
                  (< proc-num (num-procs m)))
             (equal (num-procs (write-reg m proc-num val reg))
                    (num-procs m)))
    :enable num-procs)
  (defrule write-reg-program
    (implies (and (natp proc-num)
                  (< proc-num (num-procs m))
                  (natp i))
             (equal (proc->program (nth i (machine->procs
                                           (write-reg m proc-num val reg))))
                    (proc->program (nth i (machine->procs m))))))
  (defrule write-reg-latest
    (implies (and (machine-p m)
                  (natp i)
                  (< i (num-procs m))
                  (natp j)
                  (< j (num-procs m))
                  (symbolp addr))
             (equal (sb-latest addr
                               (proc->sb
                                (nth i (machine->procs
                                        (write-reg m j val reg)))))
                    (sb-latest addr
                               (proc->sb
                                (nth i (machine->procs m)))))))
  (defrule pc-write-reg
    (implies (and (machine-p m)
                  (natp i)
                  (< i (num-procs m))
                  (natp j)
                  (< j (num-procs m)))
             (equal (proc->pc (nth i (machine->procs (write-reg m j val reg))))
                    (proc->pc (nth i (machine->procs m))))))
  (defrule phase-write-reg
    (implies (and (machine-p m)
                  (natp i)
                  (< i (num-procs m))
                  (natp j)
                  (< j (num-procs m)))
             (equal (proc->phase (nth i (machine->procs (write-reg m j val reg))))
                    (proc->phase (nth i (machine->procs m))))))
  (defrule tmp-data-write-reg
    (implies (and (machine-p m)
                  (natp i)
                  (< i (num-procs m))
                  (natp j)
                  (< j (num-procs m)))
             (equal (proc->tmp-data (nth i (machine->procs (write-reg m j val reg))))
                    (proc->tmp-data (nth i (machine->procs m))))))
  (defrule read-reg-write-reg
    (implies (and (machine-p m)
                  (natp i)
                  (< i (num-procs m))
                  (natp j)
                  (< j (num-procs m))
                  (symbolp reg1)
                  (symbolp reg2)
                  (integerp val))
             (equal (read-reg (write-reg m i val reg1) j reg2)
                    (if (and (equal i j)
                             (equal reg1 reg2))
                        val
                      (read-reg m j reg2))))
    :enable read-reg)
  (defrule write-reg-sb
    (implies (and (machine-p m)
                  (natp i)
                  (< i (num-procs m))
                  (natp j)
                  (< j (num-procs m)))
             (equal (proc->sb (nth i (machine->procs (write-reg m j val reg))))
                    (proc->sb (nth i (machine->procs m))))))
  (defrule lookup-addr-mem-write-reg
    (implies (and (machine-p m)
                  (natp i)
                  (< i (num-procs m)))
             (equal (lookup-addr-mem (write-reg m i val reg) addr)
                    (lookup-addr-mem m addr)))
    :enable lookup-addr-mem)
  (defrule lookup-addr-write-reg
    (implies (and (machine-p m)
                  (natp i)
                  (< i (num-procs m))
                  (natp j)
                  (< j (num-procs m)))
             (equal (lookup-addr (write-reg m j val reg) i addr)
                    (lookup-addr m i addr)))
    :enable lookup-addr
    :disable write-reg)
  (defrule no-pending-write-reg
    (implies (and (machine-p m)
                  (natp i)
                  (< i (num-procs m))
                  (natp j)
                  (< j (num-procs m)))
             (equal (no-pending (write-reg m j val reg) i addr)
                    (no-pending m i addr)))
    :enable no-pending)
  (defrule not-blocked-write-reg
    (implies (and (machine-p m)
                  (natp i)
                  (< i (num-procs m))
                  (natp j)
                  (< j (num-procs m)))
             (equal (not-blocked (write-reg m j val reg)
                                 i)
                    (not-blocked m i)))
    :enable not-blocked)
  (defrule read-sb-write-reg
    (implies (and (machine-p m)
                  (natp i)
                  (< i (num-procs m))
                  (natp j)
                  (< j (num-procs m)))
             (equal (read-sb (write-reg m j val reg) i addr)
                    (read-sb m i addr)))
    :enable read-sb))

; preconditions: not-blocked and empty store buffer.
(define acquire-lock
  ((m (and (machine-p m)))
   (proc-num (and (natp proc-num)
                  (< proc-num (num-procs m))
                  (not-blocked m proc-num)
                  (endp (proc->sb (nth proc-num (machine->procs m)))))))
  :returns (m-prime machine-p :hyp :fguard)
  (b* (((machine m) m))
      (machine m.procs
               m.mem
               proc-num))

  ///
  (defrule acquire-lock-num-procs
    (implies (and (natp proc-num)
                  (< proc-num (num-procs m)))
             (equal (num-procs (acquire-lock m proc-num))
                    (num-procs m)))
    :enable num-procs)
  (defrule acquire-lock-program
    (implies (and (natp proc-num)
                  (< proc-num (num-procs m))
                  (natp i))
             (equal (proc->program (nth i (machine->procs
                                           (acquire-lock m proc-num))))
                    (proc->program (nth i (machine->procs m))))))
  (defrule pc-acquire-lock
    (implies (and (machine-p m)
                  (natp i)
                  (< i (num-procs m))
                  (natp j)
                  (< j (num-procs m)))
             (equal (proc->pc (nth i (machine->procs (acquire-lock m j))))
                    (proc->pc (nth i (machine->procs m))))))
  (defrule phase-acquire-lock
    (implies (and (machine-p m)
                  (natp i)
                  (< i (num-procs m))
                  (natp j)
                  (< j (num-procs m)))
             (equal (proc->phase (nth i (machine->procs (acquire-lock m j))))
                    (proc->phase (nth i (machine->procs m))))))
  (defrule tmp-data-acquire-lock
    (implies (and (machine-p m)
                  (natp i)
                  (< i (num-procs m))
                  (natp j)
                  (< j (num-procs m)))
             (equal (proc->tmp-data
                     (nth i (machine->procs (acquire-lock m j))))
                    (proc->tmp-data (nth i (machine->procs m))))))
  (defrule sb-acquire-lock
    (implies (and (machine-p m)
                  (natp i)
                  (< i (num-procs m))
                  (natp j)
                  (< j (num-procs m)))
             (equal (proc->sb (nth i (machine->procs (acquire-lock m j))))
                    (proc->sb (nth i (machine->procs m))))))
  (defrule lookup-addr-mem-acquire-lock
    (implies (and (machine-p m)
                  (natp i)
                  (< i (num-procs m)))
             (equal (lookup-addr-mem (acquire-lock m i) addr)
                    (lookup-addr-mem m addr)))
    :enable lookup-addr-mem)
  (defrule lookup-addr-acquire-lock
    (implies (and (machine-p m)
                  (natp i)
                  (< i (num-procs m))
                  (natp j)
                  (< j (num-procs m)))
             (equal (lookup-addr (acquire-lock m j) i addr)
                    (lookup-addr m i addr)))
    :enable lookup-addr
    :disable acquire-lock)
  (defrule read-reg-acquire-lock
    (implies (and (machine-p m)
                  (natp i)
                  (< i (num-procs m))
                  (natp j)
                  (< j (num-procs m)))
             (equal (read-reg (acquire-lock m j) i reg)
                    (read-reg m i reg)))
    :enable read-reg)
  (defrule read-sb-acquire-lock
    (implies (and (machine-p m)
                  (natp i)
                  (< i (num-procs m))
                  (natp j)
                  (< j (num-procs m)))
             (equal (read-sb (acquire-lock m j) i reg)
                    (read-sb m i reg)))
    :enable read-sb)
  (defrule no-pending-acquire-lock
    (implies (and (machine-p m)
                  (natp i)
                  (< i (num-procs m))
                  (natp j)
                  (< j (num-procs m)))
             (equal (no-pending (acquire-lock m j) i addr)
                    (no-pending m i addr)))
    :enable no-pending))

; preconditions: processor has the lock and the SB is empty
(define release-lock
  ((m (and (machine-p m)))
   (proc-num (and (natp proc-num)
                  (< proc-num (num-procs m))
                  (equal (machine->lock m) proc-num) ; PRECONDITION
                  (endp
                   (proc->sb (nth proc-num (machine->procs m)))))))
  :returns (m-prime machine-p :hyp :fguard)
  (b* (((machine m) m))
      (machine m.procs
               m.mem
               nil))

  ///
  (defrule release-lock-num-procs
    (implies (and (natp proc-num)
                  (< proc-num (num-procs m)))
             (equal (num-procs (release-lock m proc-num))
                    (num-procs m)))
    :enable num-procs)
  (defrule release-lock-program
    (implies (and (natp proc-num)
                  (< proc-num (num-procs m))
                  (natp i))
             (equal (proc->program (nth i (machine->procs
                                           (release-lock m proc-num))))
                    (proc->program (nth i (machine->procs m))))))
  (defrule pc-release-lock
    (implies (and (machine-p m)
                  (natp i)
                  (< i (num-procs m))
                  (natp j)
                  (< j (num-procs m)))
             (equal (proc->pc (nth i (machine->procs (release-lock m j))))
                    (proc->pc (nth i (machine->procs m))))))
  (defrule phase-release-lock
    (implies (and (machine-p m)
                  (natp i)
                  (< i (num-procs m))
                  (natp j)
                  (< j (num-procs m)))
             (equal (proc->phase (nth i (machine->procs (release-lock m j))))
                    (proc->phase (nth i (machine->procs m))))))
  (defrule tmp-data-release-lock
    (implies (and (machine-p m)
                  (natp i)
                  (< i (num-procs m))
                  (natp j)
                  (< j (num-procs m)))
             (equal (proc->tmp-data
                     (nth i (machine->procs (release-lock m j))))
                    (proc->tmp-data (nth i (machine->procs m))))))
  (defrule sb-release-lock
    (implies (and (machine-p m)
                  (natp i)
                  (< i (num-procs m))
                  (natp j)
                  (< j (num-procs m)))
             (equal (proc->sb (nth i (machine->procs (release-lock m j))))
                    (proc->sb (nth i (machine->procs m))))))
  (defrule lookup-addr-mem-release-lock
    (implies (and (machine-p m)
                  (natp i)
                  (< i (num-procs m)))
             (equal (lookup-addr-mem (release-lock m i) addr)
                    (lookup-addr-mem m addr)))
    :enable lookup-addr-mem)
  (defrule lookup-addr-release-lock
    (implies (and (machine-p m)
                  (natp i)
                  (< i (num-procs m))
                  (natp j)
                  (< j (num-procs m)))
             (equal (lookup-addr (release-lock m j) i addr)
                    (lookup-addr m i addr)))
    :enable lookup-addr
    :disable release-lock)
  (defrule read-reg-release-lock
    (implies (and (machine-p m)
                  (natp i)
                  (< i (num-procs m))
                  (natp j)
                  (< j (num-procs m)))
             (equal (read-reg (release-lock m j) i reg)
                    (read-reg m i reg)))
    :enable read-reg)
  (defrule read-sb-release-lock
    (implies (and (machine-p m)
                  (natp i)
                  (< i (num-procs m))
                  (natp j)
                  (< j (num-procs m)))
             (equal (read-sb (release-lock m j) i reg)
                    (read-sb m i reg)))
    :enable read-sb)
  (defrule no-pending-release-lock
    (implies (and (machine-p m)
                  (natp i)
                  (< i (num-procs m))
                  (natp j)
                  (< j (num-procs m)))
             (equal (no-pending (release-lock m j) i addr)
                    (no-pending m i addr)))
    :enable no-pending))

(define phase-machine
  ((m (and (machine-p m)))
   (proc-num (and (natp proc-num)
                  (< proc-num (num-procs m))))
   (next-phase natp)
   (next-pc natp)
   (next-tmp-data integerp))
  :returns (m-prime machine-p :hyp :fguard)
  (b* (((machine m) m)
       ((proc proc) (nth proc-num m.procs))
       (new-proc (proc proc.program
                       next-pc
                       proc.sb
                       proc.registers
                       next-phase
                       next-tmp-data))
       (new-procs (update-nth proc-num new-proc m.procs)))
      (machine new-procs m.mem m.lock))

  ///
  (defrule phase-machine-num-procs
    (implies (and (natp proc-num)
                  (< proc-num (num-procs m)))
             (equal (num-procs (phase-machine m
                                              proc-num
                                              next-phase
                                              next-pc
                                              next-tmp-data))
                    (num-procs m)))
    :enable num-procs)
  (defrule phase-machine-program
    (implies (and (natp proc-num)
                  (< proc-num (num-procs m))
                  (natp i))
             (equal (proc->program
                     (nth i (machine->procs
                             (phase-machine m
                                            proc-num
                                            next-phase
                                            next-pc
                                            next-tmp-data))))
                    (proc->program (nth i (machine->procs m))))))
  (defrule phase-machine-latest
    (implies (and (machine-p m)
                  (natp i)
                  (< i (num-procs m))
                  (natp j)
                  (< j (num-procs m))
                  (symbolp addr))
             (equal (sb-latest addr
                               (proc->sb
                                (nth i (machine->procs
                                        (phase-machine
                                         m
                                         j
                                         next-phase
                                         next-pc
                                         next-tmp-data)))))
                    (sb-latest addr
                               (proc->sb
                                (nth i (machine->procs m)))))))
  (defrule pc-phase-machine
    (implies (and (machine-p m)
                  (natp i)
                  (< i (num-procs m))
                  (natp j)
                  (< j (num-procs m))
                  (natp next-pc))
             (equal (proc->pc
                     (nth i (machine->procs
                             (phase-machine m j
                                            next-phase
                                            next-pc
                                            next-tmp-data))))
                    (if (= i j)
                        next-pc
                      (proc->pc (nth i (machine->procs m)))))))
  (defrule phase-phase-machine
    (implies (and (machine-p m)
                  (natp i)
                  (< i (num-procs m))
                  (natp j)
                  (< j (num-procs m))
                  (natp next-phase))
             (equal (proc->phase
                     (nth i (machine->procs
                             (phase-machine m j
                                            next-phase
                                            next-pc
                                            next-tmp-data))))
                    (if (= i j)
                        next-phase
                      (proc->phase (nth i (machine->procs m)))))))
  (defrule read-reg-phase-machine
    (implies (and (machine-p m)
                  (natp i)
                  (< i (num-procs m))
                  (natp j)
                  (< j (num-procs m)))
             (equal (read-reg (phase-machine m i
                                             next-phase
                                             next-pc
                                             next-tmp-data)
                              j
                              reg)
                    (read-reg m j reg)))
    :enable read-reg)
  (defrule read-mem-phase-machine
    (implies (and (machine-p m)
                  (natp i)
                  (< i (num-procs m))
                  (natp j)
                  (< j (num-procs m)))
             (equal (read-mem (phase-machine m i
                                             next-phase
                                             next-pc
                                             next-tmp-data)
                              j
                              addr)
                    (read-mem m j addr)))
    :enable read-mem)
  (defrule read-sb-phase-machine
    (implies (and (machine-p m)
                  (natp i)
                  (< i (num-procs m))
                  (natp j)
                  (< j (num-procs m)))
             (equal (read-sb (phase-machine m i
                                            next-phase
                                            next-pc
                                            next-tmp-data)
                             j
                             addr)
                    (read-sb m j addr)))
    :enable read-sb)
  (defrule no-pending-phase-machine
    (implies (and (machine-p m)
                  (natp i)
                  (< i (num-procs m))
                  (natp j)
                  (< j (num-procs m)))
             (equal (no-pending (phase-machine m j
                                               next-phase
                                               next-pc
                                               next-tmp-data)
                                i addr)
                    (no-pending m i addr)))
    :enable no-pending)
  (defrule tmp-data-phase-machine
    (implies (and (machine-p m)
                  (natp i)
                  (< i (num-procs m))
                  (natp j)
                  (< j (num-procs m))
                  (integerp next-tmp-data))
             (equal (proc->tmp-data
                     (nth i (machine->procs (phase-machine m j
                                                           next-phase
                                                           next-pc
                                                           next-tmp-data))))
                    (if (= i j)
                        next-tmp-data
                      (proc->tmp-data
                       (nth i (machine->procs m)))))))
  (defrule lookup-addr-mem-phase-machine
    (implies (and (machine-p m)
                  (natp i)
                  (< i (num-procs m)))
             (equal (lookup-addr-mem (phase-machine m i
                                                    next-phase
                                                    next-pc
                                                    next-tmp-data)
                                     addr)
                    (lookup-addr-mem m addr)))
    :enable lookup-addr-mem)
  (defrule sb-latest-phase-machine
    (implies (and (machine-p m)
                  (natp i)
                  (< i (num-procs m))
                  (natp j)
                  (< j (num-procs m)))
             (equal (sb-latest
                     addr
                     (proc->sb (nth i (machine->procs
                                       (phase-machine m j
                                                      next-phase
                                                      next-pc
                                                      next-tmp-data)))))
                    (sb-latest
                     addr
                     (proc->sb (nth i (machine->procs m)))))))
  (defrule lookup-addr-phase-machine
    (implies (and (machine-p m)
                  (natp i)
                  (< i (num-procs m))
                  (natp j)
                  (< j (num-procs m)))
             (equal (lookup-addr (phase-machine m j
                                                next-phase
                                                next-pc
                                                next-tmp-data)
                                 i addr)
                    (lookup-addr m i addr)))
    :enable lookup-addr
    :disable phase-machine)
  (defrule not-blocked-phase-machine
    (implies (and (machine-p m)
                  (natp i)
                  (< i (num-procs m))
                  (natp j)
                  (< j (num-procs m)))
             (equal (not-blocked (phase-machine m j
                                                next-phase
                                                next-pc
                                                next-tmp-data)
                                 i)
                    (not-blocked m i)))
    :enable not-blocked))

(define step
  ((m (and (machine-p m)))
   (proc-num (and (natp proc-num)
                  (< proc-num (num-procs m)))))
  :returns (m-prime machine-p :hyp :fguard)
  (b* (((machine m) m)
       ((proc proc) (nth proc-num m.procs))
       ;; blocked check
       ((unless (not-blocked m proc-num)) m)
       ;; halted check
       ((unless (< proc.pc (len proc.program))) m)
       (inst (nth proc.pc proc.program)))
      (instruction-case
       inst
       (:mrmov 
        ;; Three phases (phase 1 is skipped if write in sb)
        ;; Phase 0: get value from store buffer
        ;; Phase 1: if sb had nothing, get value from memory
        ;; Phase 2: store the value in register
        (case proc.phase
          (0
           (b* ((read-sb (read-sb m proc-num inst.addr)))
               (if read-sb
                   (phase-machine m
                                  proc-num
                                  ;; skip phase 1 since we got a val
                                  2
                                  proc.pc
                                  read-sb)
                 (phase-machine m
                                proc-num
                                ;; go to phase 1 since sb didn't have
                                ;; addr 
                                1
                                proc.pc
                                0))))
          (1
           (b* (((unless (no-pending m proc-num inst.addr)) m)
                (read-mem (read-mem m proc-num inst.addr)))
               ;; read-mem will be 0 if addr is uninitialized
               (phase-machine m
                              proc-num
                              2
                              proc.pc
                              read-mem)))
          (2 
           (phase-machine (write-reg m proc-num proc.tmp-data inst.reg)
                          proc-num
                          0 ;; next-phase
                          (1+ proc.pc) ;; next-pc
                          0))
          (otherwise ;; no-op
           m)))
       (:rmmov 
        ;; Two phases
        ;; Phase 0: get value from register
        ;; Phase 1: store the value in the store buffer
        (case proc.phase
          (1 
           ;; get value from tmp-data, write it to memory
           (phase-machine (write-sb m proc-num proc.tmp-data inst.addr)
                          proc-num
                          0
                          (1+ proc.pc)
                          0))
          (0
           (phase-machine m
                          proc-num
                          1
                          proc.pc
                          (read-reg m proc-num inst.reg)))
          (otherwise m)))
       (:irmov 
        ;; One phase
        ;; Phase 0: Store immediate in register
        (case proc.phase
          (0
           (phase-machine (write-reg m proc-num inst.val inst.reg)
                          proc-num
                          0
                          (1+ proc.pc)
                          0))
          (otherwise m)))
       (:immov 
        ;; One phase
        ;; Phase 0: Store immediate in memory
        (case proc.phase
          (0
           (phase-machine (write-sb m proc-num inst.val inst.addr)
                          proc-num
                          0
                          (1+ proc.pc)
                          0))
          (otherwise m)))
       (:ifz
        ;; Two phases
        ;; Phase 0: read from register
        ;; Phase 1: Conditionally set the pc based on the value read
        (case proc.phase
          (1
           (phase-machine m
                          proc-num
                          0
                          (if (= proc.tmp-data 0)
                              inst.line
                            (1+ proc.pc))
                          0))
          (0
           (phase-machine m
                          proc-num
                          1
                          proc.pc
                          (read-reg m proc-num inst.reg)))
          (otherwise m)))
       (:lock
        (case proc.phase
          (0
           (b* (((unless (endp proc.sb)) m))
               (acquire-lock m proc-num)))
          (otherwise m)))
       (:unlock
        (case proc.phase
          (0
           (b* (((unless (endp proc.sb)) m)
                ((unless (equal m.lock proc-num)) m))
               (release-lock m proc-num)))
          (otherwise m)))
       (:fence
        (case proc.phase
          (0
           (b* (((unless (endp proc.sb)) m))
               (phase-machine m
                              proc-num
                              0
                              (1+ proc.pc)
                              0)))
          (otherwise m)))
       (:no-op m)))

  ///
  (defrule step-num-procs
    (implies (and (natp proc-num)
                  (< proc-num (num-procs m)))
             (equal (num-procs (step m proc-num))
                    (num-procs m))))
  (defrule step-program
    (implies (and (natp proc-num)
                  (< proc-num (num-procs m))
                  (natp i))
             (equal (proc->program (nth i (machine->procs
                                           (step m proc-num))))
                    (proc->program (nth i (machine->procs m)))))))

;; ORACLE
(deftagsum o
  (:step ((proc-num natp)))
  (:flush ((proc-num natp))))

(deflist oracle
  :elt-type o
  :true-listp t)

(define run
  ((m (and (machine-p m)))
   (oracle oracle-p))
  :returns (final-m machine-p :hyp :fguard)
  (if (endp oracle) m
    (b*
     ((next (car oracle)))
     (run 
      (o-case next
              ;; We will only use this function if (oracle-p oracle)
              ;; is t. However, this does not guarantee that every
              ;; element in the oracle only steps or flushes a
              ;; processor that actually exists. So, we do a check
              ;; here to make sure that the next oracle instruction in
              ;; fact involves a processor that exists. 
              (:step
               (if (< next.proc-num (num-procs m))
                   (step m next.proc-num)
                 m))
              (:flush
               (if (and (< next.proc-num (num-procs m))
                        (not-blocked m next.proc-num))
                   (flush-sb m next.proc-num)
                 m)))
      (cdr oracle)))))

(define short-to-oracle
  (short)
  :returns (o oracle-p)
  (cond ((atom short) nil)
        ((natp (car short)) (cons (o-step (car short))
                                  (short-to-oracle (cdr short))))
        ((and (consp (car short))
              (consp (cdar short))
              (equal (caar short) 'f)
              (natp (cadar short)))
         (cons (o-flush (cadar short))
               (short-to-oracle (cdr short))))
        (t (short-to-oracle (cdr short)))))

(deflist program-list
  :elt-type program
  :true-listp t)

(define program-to-proc
  ((program program-p))
  :returns (proc proc-p :hyp :fguard)
  (proc program 0 nil nil 0 0))

(define program-list-to-proc-list
  ((program-list program-list-p))
  :returns (proc-list proc-list-p :hyp :fguard)
  (cond ((endp program-list) nil)
        (t (cons (program-to-proc (car program-list))
                 (program-list-to-proc-list (cdr program-list))))))

(define program-list-to-machine
  ((program-list program-list-p))
  :returns (m machine-p :hyp :fguard)
  (machine (program-list-to-proc-list program-list)
           nil
           nil))

(define run-short
  ((program-list program-list-p)
   short)
  (run (program-list-to-machine program-list)
       (short-to-oracle short)))

;; MISCELLANEOUS ;;

;; This rule often helps with complicated invariants. We leave it disabled.
(defruled open-<-with-explicit-natp
  (implies (and (syntaxp (quotep n))
                (posp n)
                (natp i)
                (equal m (1- n)) ; avoid rewriting (1- n) twice
                )
           (iff (< i n)
                (or (equal i m)
                    (< i m)))))


;; SC
;; (i-am-here)

;; (define all-sb-empty-procs
;;   ((procs proc-list-p))
;;   :returns (all-sb-empty? booleanp)
;;   (if (endp procs)
;;       t
;;     (b* (((proc proc) (car procs)))
;;         (and (endp proc.sb)
;;              (all-sb-empty-procs (cdr procs))))))

;; (define all-sb-empty
;;   ((m machine-p))
;;   :returns (all-sb-empty? booleanp)
;;   (b* (((machine m) m))
;;       (all-sb-empty-procs m.procs)))

;; (define step-sc
;;   ((m (and (machine-p m)
;;            (all-sb-empty m)))
;;    (proc-num (and (natp proc-num)
;;                   (< proc-num (num-procs m)))))
;;   :returns (m-prime machine-p :hyp :fguard)
;;   (b* (((machine m) m)
;;        ((proc proc) (nth proc-num m.procs))
;;        ;; blocked check
;;        ((unless (not-blocked m proc-num)) m)
;;        ;; halted check
;;        ((unless (< proc.pc (len proc.program))) m)
;;        (inst (nth proc.pc proc.program)))
;;       (instruction-case
;;        inst
;;        (:mrmov 
;;         ;; Three phases (phase 1 is skipped if write in sb)
;;         ;; Phase 0: get value from store buffer
;;         ;; Phase 1: if sb had nothing, get value from memory
;;         ;; Phase 2: store the value in register
;;         (case proc.phase
;;           (0
;;            (b* ((read-sb (read-sb m proc-num inst.addr)))
;;                (if read-sb
;;                    (phase-machine m
;;                                   proc-num
;;                                   ;; skip phase 1 since we got a val
;;                                   2
;;                                   proc.pc
;;                                   read-sb)
;;                  (phase-machine m
;;                                 proc-num
;;                                 ;; go to phase 1 since sb didn't have
;;                                 ;; addr 
;;                                 1
;;                                 proc.pc
;;                                 0))))
;;           (1
;;            (b* (((unless (no-pending m proc-num inst.addr)) m)
;;                 (read-mem (read-mem m proc-num inst.addr)))
;;                ;; read-mem will be 0 if addr is uninitialized
;;                (phase-machine m
;;                               proc-num
;;                               2
;;                               proc.pc
;;                               read-mem)))
;;           (2 
;;            (phase-machine (write-reg m proc-num proc.tmp-data inst.reg)
;;                           proc-num
;;                           0 ;; next-phase
;;                           (1+ proc.pc) ;; next-pc
;;                           0))
;;           (otherwise ;; no-op
;;            m)))
;;        (:rmmov 
;;         ;; Two phases
;;         ;; Phase 0: get value from register
;;         ;; Phase 1: store the value in the store buffer
;;         (case proc.phase
;;           (1 
;;            ;; get value from tmp-data, write it to memory
;;            (phase-machine (write-sb m proc-num proc.tmp-data inst.addr)
;;                           proc-num
;;                           0
;;                           (1+ proc.pc)
;;                           0))
;;           (0
;;            (phase-machine m
;;                           proc-num
;;                           1
;;                           proc.pc
;;                           (read-reg m proc-num inst.reg)))
;;           (otherwise m)))
;;        (:irmov 
;;         ;; One phase
;;         ;; Phase 0: Store immediate in register
;;         (case proc.phase
;;           (0
;;            (phase-machine (write-reg m proc-num inst.val inst.reg)
;;                           proc-num
;;                           0
;;                           (1+ proc.pc)
;;                           0))
;;           (otherwise m)))
;;        (:immov 
;;         ;; One phase
;;         ;; Phase 0: Store immediate in memory
;;         (case proc.phase
;;           (0
;;            (phase-machine (write-sb m proc-num inst.val inst.addr)
;;                           proc-num
;;                           0
;;                           (1+ proc.pc)
;;                           0))
;;           (otherwise m)))
;;        (:ifz
;;         ;; Two phases
;;         ;; Phase 0: read from register
;;         ;; Phase 1: Conditionally set the pc based on the value read
;;         (case proc.phase
;;           (1
;;            (phase-machine m
;;                           proc-num
;;                           0
;;                           (if (= proc.tmp-data 0)
;;                               inst.line
;;                             (1+ proc.pc))
;;                           0))
;;           (0
;;            (phase-machine m
;;                           proc-num
;;                           1
;;                           proc.pc
;;                           (read-reg m proc-num inst.reg)))
;;           (otherwise m)))
;;        (:lock
;;         (case proc.phase
;;           (0
;;            (b* (((unless (endp proc.sb)) m))
;;                (acquire-lock m proc-num)))
;;           (otherwise m)))
;;        (:unlock
;;         (case proc.phase
;;           (0
;;            (b* (((unless (endp proc.sb)) m)
;;                 ((unless (equal m.lock proc-num)) m))
;;                (release-lock m proc-num)))
;;           (otherwise m)))
;;        (:fence
;;         (case proc.phase
;;           (0
;;            (b* (((unless (endp proc.sb)) m))
;;                (phase-machine m
;;                               proc-num
;;                               0
;;                               (1+ proc.pc)
;;                               0)))
;;           (otherwise m)))
;;        (:no-op m)))
