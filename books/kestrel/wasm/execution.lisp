; An interpreter / operational semantics for Web Assembly
;
; Copyright (C) 2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "WASM")

;; STATUS: INCOMPLETE (need to add many more instructions, but working for one example)

(include-book "portcullis") ; for the package

(include-book "std/util/defaggregate" :dir :system)
(include-book "kestrel/utilities/forms" :dir :system)
(include-book "kestrel/bv/bvplus" :dir :system)

(local
  (defthm consp-when-true-listp
    (implies (true-listp x)
             (iff (consp x)
                  x))))

(local (in-theory (disable natp)))

(defund u32p (x)
  (declare (xargs :guard t))
  (unsigned-byte-p 32 x))

(defthm u32p-forward-to-natp
  (implies (u32p x)
           (natp x))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable u32p))))

(defun storep (x) (declare (xargs :guard t) (ignore x)) t)
(in-theory (disable (:t storep)))

(defund i32-valp (val)
  (declare (xargs :guard t))
  (and (consp val)
       (true-listp val)
       (eq :i32.const (ffn-symb val))
       (= 1 (len (acl2::fargs val)))
       (u32p (acl2::farg1 val))))

(defund valp (val)
  (declare (xargs :guard t))
  (or (i32-valp val)
      )
  ;; (and (consp val)
  ;;      (true-listp val)
  ;;      (= 1 (len (acl2::fargs val)))
  ;;      (case (acl2::ffn-symb val)
  ;;        (:i32.const (u32p (acl2::farg1 val)))
  ;;        ;; todo: more!
  ;;        (otherwise nil)))
  )

(defun val-listp (vals)
  (declare (xargs :guard t))
  (if (not (consp vals))
      (null vals)
    (and (valp (first vals))
         (val-listp (rest vals)))))

(defund localsp (locals)
  (declare (xargs :guard t))
  (val-listp locals))

(defthm localsp-forward-to-true-listp
  (implies (localsp locals)
           (true-listp locals))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable localsp))))

(defund nth-local (n locals)
  (declare (xargs :guard (and (natp n)
                              (< n (len locals))
                              (localsp locals))))
  (nth n locals))

(defthm valp-of-nth-local
  (implies (and (natp n)
                (< n (len locals))
                (localsp locals))
           (valp (nth-local n locals)))
  :hints (("Goal" :in-theory (enable val-listp nth-local localsp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The first item is the topmost in the stack
(defund operand-stackp (stack)
  (declare (xargs :guard t))
  (if (not (consp stack))
      (null stack)
    (and (valp (first stack))
         (operand-stackp (rest stack)))))

(defun empty-operand-stack ()
  (declare (xargs :guard t))
  nil)

(defund push-operand (val stack)
  (declare (xargs :guard (and (valp val)
                              (operand-stackp stack))))
  (cons val stack))

(defthm operand-stackp-of-push-operand-stack
  (implies (and (valp val)
                (operand-stackp ostack))
           (operand-stackp (push-operand val ostack)))
  :hints (("Goal" :in-theory (enable push-operand operand-stackp))))

(defund operand-stack-height (stack)
  (declare (xargs :guard (operand-stackp stack)))
  (len stack))

(defund top-operand (stack)
  (declare (xargs :guard (and (operand-stackp stack)
                              (<= 1 (operand-stack-height stack)))
                  :guard-hints (("Goal" :in-theory (enable operand-stackp)))))
  (car stack))

(defthm valp-of-top-operand
  (implies (and (operand-stackp stack)
                (<= 1 (operand-stack-height stack)))
           (valp (top-operand stack)))
  :hints (("Goal" :in-theory (enable operand-stackp operand-stack-height top-operand))))

(defund pop-operand (stack)
  (declare (xargs :guard (and (operand-stackp stack)
                              (<= 1 (operand-stack-height stack)))
                  :guard-hints (("Goal" :in-theory (enable operand-stackp)))))
  (cdr stack))

(defthm pop-operand-of-push-operand
  (equal (pop-operand (push-operand val stack))
         stack)
  :hints (("Goal" :in-theory (enable push-operand
                                     pop-operand))))

(defthm top-operand-of-push-operand
  (equal (top-operand (push-operand val stack))
         val)
  :hints (("Goal" :in-theory (enable push-operand
                                     top-operand))))

(defthm operand-stackp-of-pop-operand-stack
  (implies (operand-stackp operand-stack)
           (operand-stackp (pop-operand operand-stack)))
  :hints (("Goal" :in-theory (enable pop-operand operand-stackp))))

(defthm operand-stack-height-of-pop-operand-stack
  (implies (<= 1 (operand-stack-height stack))
           (equal (operand-stack-height (pop-operand stack))
                  (+ -1 (operand-stack-height stack))))
  :hints (("Goal" :in-theory (enable pop-operand operand-stack-height))))

(defthm operand-stack-height-of-push-operand
  (equal (operand-stack-height (push-operand val stack))
         (+ 1 (operand-stack-height stack)))
  :hints (("Goal" :in-theory (enable push-operand operand-stack-height))))

;; returns a list, with the deepest operand first
(defund top-n-operands (n stack acc)
  (declare (xargs :guard (and (natp n)
                              (operand-stackp stack)
                              (<= n (operand-stack-height stack)))
                  :guard-hints (("Goal" :in-theory (enable operand-stack-height pop-operand operand-stackp)))))
  (if (zp n)
      acc
    (top-n-operands (+ -1 n)
                    (pop-operand stack)
                    (cons (top-operand stack) acc))))

(defthm val-listp-of-top-n-operands
  (implies (and (natp n)
                (operand-stackp stack)
                (<= n (operand-stack-height stack))
                (val-listp acc))
           (val-listp (top-n-operands n stack acc)))
  :hints (("Goal" :in-theory (enable top-n-operands val-listp))))

;; earlier vals end up deeper in the stack
(defund push-vals (vals stack)
  (declare (xargs :guard (and (val-listp vals)
                              (operand-stackp stack))))
  (if (endp vals)
      stack
    (push-vals (rest vals) (push-operand (first vals) stack))))

(defthm operand-stackp-of-push-vals
  (implies (and (val-listp vals)
                (operand-stackp stack))
           (operand-stackp (push-vals vals stack)))
  :hints (("Goal" :in-theory (enable push-vals))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; (defun weak-instrp (instr)
;;   (declare (xargs :guard t))
;;   (and (true-listp instr)
;;        (consp instr)
;;        (let ((opcode (ffn-symb instr))
;;              (fargs (fargs instr)))
;;          (symbolp opcode))))

(defun local.get-argsp (args)
  (declare (xargs :guard (and (true-listp args))))
  (and (= 1 (len args)) (u32p (first args))))

(defun i32.add-argsp (args)
  (declare (xargs :guard (and (true-listp args))))
  (null args))

(defund instrp (instr)
  (declare (xargs :guard t))
  (and (true-listp instr)
       (consp instr)
       (let ((name (ffn-symb instr))
             (args (fargs instr)))
         (and (symbolp name)
              (case name
                (:local.get (local.get-argsp args))
                (:i32.add (null args))
                ;; todo more!
                (otherwise nil))))))

(defun instr-listp (instrs)
  (declare (xargs :guard t))
  (if (not (consp instrs))
      (null instrs)
    (and (instrp (first instrs))
         (instr-listp (rest instrs)))))

(defthm instr-listp-forward-to-true-listp
  (implies (instr-listp instrs)
           (true-listp instrs))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable instr-listp))))


(local
  (defthm true-listp-when-instr-listp
    (implies (instr-listp instrs)
             (true-listp instrs))
    :hints (("Goal" :in-theory (enable instr-listp)))))

(defthm instrp-of-first
  (implies (instr-listp instrs)
           (equal (instrp (first instrs))
                  (consp instrs)))
  :hints (("Goal" :in-theory (enable instr-listp))))

(defthm instr-listp-of-rest
  (implies (instr-listp instrs)
           (instr-listp (rest instrs)))
  :hints (("Goal" :in-theory (enable instr-listp))))

(defaggregate frame
  ((return-arity natp)
   (locals val-listp)
   ;; todo: module
   (operand-stack operand-stackp)
   (instrs (and (instr-listp instrs)
                ;(consp instrs)
                )))
  :pred framep
  )

(defthm true-listp-of-frame->instrs
  (implies (framep frame)
           (true-listp (frame->instrs frame)))
  :hints (("Goal" :in-theory (enable framep frame->instrs))))

;; The first item is the topmost in the stack
(defund call-stackp (stack)
  (declare (xargs :guard t))
  (if (not (consp stack))
      (null stack)
    (and (framep (first stack))
         (call-stackp (rest stack)))))

(defun empty-call-stack ()
  (declare (xargs :guard t))
  nil)

;; the top frame on the stack
(defund top-frame (stack)
  (declare (xargs :guard (and (call-stackp stack)
                              (consp stack))))
  (first stack))

(defthm framep-of-top-frame
  (implies (and (call-stackp stack)
                (consp stack))
           (framep (top-frame stack)))
  :hints (("Goal" :in-theory (enable top-frame call-stackp))))

(defund pop-call-stack (call-stack)
  (declare (xargs :guard (and (call-stackp call-stack)
                              (consp call-stack))))
  (cdr call-stack))

(defthm call-stackp-of-pop-call-stack
  (implies (call-stackp call-stack)
           (call-stackp (pop-call-stack call-stack)))
  :hints (("Goal" :in-theory (enable pop-call-stack call-stackp))))

(defund push-call-stack (frame call-stack)
  (declare (xargs :guard (and (framep frame)
                              (call-stackp call-stack))))
  (cons frame call-stack))

(defthm pop-call-stack-of-push-call-stack
  (equal (pop-call-stack (push-call-stack frame call-stack))
         call-stack)
  :hints (("Goal" :in-theory (enable push-call-stack
                                     pop-call-stack))))

(defthm call-stackp-of-push-call-stack
  (implies (and (framep frame)
                (call-stackp call-stack))
           (call-stackp (push-call-stack frame call-stack)))
  :hints (("Goal" :in-theory (enable push-call-stack call-stackp))))

(defthm top-frame-of-push-call-stack
  (equal (top-frame (push-call-stack frame call-stack))
         frame)
  :hints (("Goal" :in-theory (enable push-call-stack top-frame))))

;; todo: or make it a stobj?
(defaggregate state
  ((store storep)
   (call-stack (and (call-stackp call-stack)
                    (consp call-stack) ; must be at least one frame
                    ))
   )
  :pred statep)



;use this below
(defund current-frame (state)
  (declare (xargs :guard (statep state)))
  (let ((call-stack (state->call-stack state)))
    (top-frame call-stack)))

(defthm framep-of-current-frame
  (implies (statep state)
           (framep (current-frame state)))
  :hints (("Goal" :in-theory (enable current-frame))))

(defund current-instrs (state)
  (declare (xargs :guard (statep state)))
  (let* ((call-stack (state->call-stack state))
         (frame (top-frame call-stack)))
    (frame->instrs frame)))

(defthm instr-listp-of-current-instrs
  (implies (statep state)
           (instr-listp (current-instrs state)))
  :hints (("Goal" :in-theory (enable current-instrs))))

(defun current-operand-stack (state)
  (declare (xargs :guard (statep state)))
  (let* ((call-stack (state->call-stack state))
         (frame (top-frame call-stack)))
    (frame->operand-stack frame)))

(defun current-locals (state)
  (declare (xargs :guard (statep state)))
  (let* ((call-stack (state->call-stack state))
         (frame (top-frame call-stack)))
    (frame->locals frame)))

(defun update-current-instrs (instrs state)
  (declare (xargs :guard (and (instr-listp instrs)
                              (statep state))))
  (let* ((call-stack (state->call-stack state))
         (frame (top-frame call-stack))
         (new-frame (change-frame frame :instrs instrs))
         (new-call-stack (push-call-stack new-frame (pop-call-stack call-stack)))
         (new-state (change-state state :call-stack new-call-stack))
         )
    new-state))

(defun update-current-operand-stack (operand-stack state)
  (declare (xargs :guard (and (operand-stackp operand-stack)
                              (statep state))))
  (let* ((call-stack (state->call-stack state))
         (frame (top-frame call-stack))
         (new-frame (change-frame frame :operand-stack operand-stack))
         (new-call-stack (push-call-stack new-frame (pop-call-stack call-stack)))
         (new-state (change-state state :call-stack new-call-stack))
         )
    new-state))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Returns a new state or :trap
(defun execute-local.get (args state)
  (declare (xargs :guard (and (true-listp args)
                              (local.get-argsp args)
                              (statep state))))
  (b* ((x (first args))
       (locals (current-locals state))
       (ostack (current-operand-stack state))
       ((when (not (< x (len locals)))) ; impossible if the code is validated?
        :trap)
       (val (nth-local x locals))
       (ostack (push-operand val ostack))
       (state (update-current-operand-stack ostack state))
       (state (update-current-instrs (rest (current-instrs state)) state)))
    state))

(defund make-i32-val (x)
  (declare (xargs :guard (u32p x)))
  `(:i32.const ,x))

(defthm i32-valp-of-make-i32-val
  (equal (i32-valp (make-i32-val x))
         (u32p x))
  :hints (("Goal" :in-theory (enable i32-valp make-i32-val))))

;or call this addi32?
(defund i32.add-vals (val1 val2)
  (declare (xargs :guard (and (i32-valp val1)
                              (i32-valp val2))
                  :guard-hints (("Goal" :in-theory (enable i32-valp u32p)))
                  ))
  (make-i32-val (bvplus 32 (farg1 val1) (farg1 val2))))

(defthm i32-valp-of-i32.add-vals
  (implies (and (i32-valp val1)
                (i32-valp val2))
           (i32-valp (i32.add-vals val1 val2)))
  :hints (("Goal" :in-theory (enable i32.add-vals i32-valp u32p))))

;; Returns a new state or :trap
(defun execute-i32.add (state)
  (declare (xargs :guard (statep state)
                  :guard-hints (("Goal" :in-theory (enable valp i32-valp u32p)))))
  (b* ((ostack (current-operand-stack state))
       ((when (not (<= 2 (operand-stack-height ostack))))
        :trap ;excluded by validation?
        )
       (arg2 (top-operand ostack)) ; todo: check this
       (arg1 (top-operand (pop-operand ostack)))
       ((when (not (and (i32-valp arg1)
                        (i32-valp arg2))))
        :trap ;excluded by validation?
        )
       (result (i32.add-vals arg1 arg2))
       (ostack (push-operand result (pop-operand (pop-operand ostack))))
       (state (update-current-operand-stack ostack state))
       (state (update-current-instrs (rest (current-instrs state)) state)))
    state))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Returns a new state or :trap.
(defund execute-instr (instr state)
  (declare (xargs :guard (and (instrp instr)
                              (statep state))
                  :guard-hints (("Goal" :in-theory (enable instrp)))))
  (let ((name (ffn-symb instr))
        (args (fargs instr)))
    (case name
      (:local.get (execute-local.get args state))
      (:i32.add (execute-i32.add state))
      (otherwise (prog2$ (cw "Unhandled instr: ~x0.~%" instr)
                         :trap)))))

(defthm statep-of-execute-instr
  (implies (and (not (equal :trap (execute-instr instr state)))
                (instrp instr)
                (statep state))
           (statep (execute-instr instr state)))
  :hints (("Goal" :in-theory (enable execute-instr instrp))))

;; returns a new state or :trap or (:done ..)
;; todo: handle blocks and loops
(defun step (state)
  (declare (xargs :guard (and (statep state)
                              (consp (current-instrs state)))
                  :guard-hints (("Goal" :in-theory (enable current-instrs)))))
  (let* ((instrs (current-instrs state))
         (instr (first instrs))
         (state-or-trap (execute-instr instr state)))
    (if (eq :trap state-or-trap)
        :trap
      state-or-trap)))

;; 4.4.10
(defund return-from-function (state)
  (declare (xargs :guard (and (statep state)
                              (not (consp (current-instrs state)))
                              ;(consp (pop-call-stack (state->call-stack state))) ; must be at least 2 frames ; todo
                              )))
  (b* ((f (current-frame state))
       (n (frame->return-arity f))
       (ostack (frame->operand-stack f))
       ((when (not (equal n (operand-stack-height ostack)))) ; todo: "exactly n" -- the language is unclear?
        :trap ; should never happen, due to validation
        )
       (valn (top-n-operands n ostack nil)) ; deepest first
       (call-stack (pop-call-stack (state->call-stack state)))
       ((when (not (consp call-stack))) ; returning from the only remaining frame
        `(:done ,state))
       (state (change-state state :call-stack call-stack))
       (state (update-current-operand-stack (push-vals valn (current-operand-stack state)) state))
       ;; remove the call instr now, after the call returns (leaving it there
       ;; during the call may help with debugging):
       (state (update-current-instrs (rest (current-instrs state)) state)))
    state))

(defun run (n state)
  (declare (xargs :guard (and (natp n)
                              (statep state)
                              ;(consp (pop-call-stack (state->call-stack state)))
                              )))
  (if (zp n)
      state
    (if (not (consp (current-instrs state)))
        (return-from-function state) ; todo: should this consume a step?
      (let ((new-state-or-trap (step state)))
        (if (eq :trap new-state-or-trap)
            :trap
          (run (+ -1 n) new-state-or-trap))))))

;; a test:
;; (run 4
;;      (make-state :store :fake
;;                  :call-stack (list (make-frame :return-arity 1
;;                                                :locals (list (make-i32-val 7) (make-i32-val 8)) ; the params
;;                                                :operand-stack nil
;;                                                :instrs '((:local.get 1)
;;                                                          (:local.get 0)
;;                                                          (:i32.add))))))
