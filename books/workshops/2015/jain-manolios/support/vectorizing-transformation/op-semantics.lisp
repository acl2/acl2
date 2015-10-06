; This file contains semantics for scalar and vector machines.

(in-package "ACL2S")
(include-book "data-struct")

(defun get-val (r regs)
  (cdr (assoc r regs)))

(defun add-rc (ra rb rc regs)
  (put-assoc-eq rc (+ (get-val ra regs)
              (get-val rb regs))
        regs))

(defun ISA-add (rc ra rb ISA)
  (isa-state (1+ (mget :prc ISA))
             (add-rc ra rb rc (mget :regs ISA))
             (isa-state-inmem  ISA)))

(defun sub-rc (ra rb rc regs)
  (put-assoc-eq rc (- (get-val ra regs)
                      (get-val rb regs))
                regs))

(defun ISA-sub (rc ra rb ISA)
  (isa-state (1+ (mget :prc ISA))
       (sub-rc ra rb rc (mget :regs ISA))
       (isa-state-inmem  ISA)
       ))

(defun mul-rc (ra rb rc regs)
  (put-assoc-eq rc (* (get-val ra regs)
              (get-val rb regs))
        regs))

(defun ISA-mul (rc ra rb ISA)
  (isa-state (1+ (mget :prc ISA))
       (mul-rc ra rb rc (mget :regs ISA))
       (isa-state-inmem  ISA)
       ))

(defun ISA-default (ISA)
  ISA)

(defun ISA-step (ISA)
  (let ((inst (nth  (mget :prc ISA) (isa-state-inmem  ISA))))
   (let ((op (mget  :op inst))
         (rc (mget  :rc     inst))
         (ra (mget  :ra     inst))
         (rb (mget  :rb     inst)))
    (case op
      (add       (ISA-add rc ra rb ISA))  ; REGS[rc] := REGS[ra] + REGS[rb]
      (sub       (ISA-sub rc ra rb ISA))
      (mul       (ISA-mul rc ra rb ISA))
      (otherwise (ISA-default ISA))))))

(defun ISA-run (ISA n)
  (if (zp n)
      ISA
      (ISA-run (ISA-step ISA) (- n 1))))

(defun step-vec-reg (inst regs)
  (let ((opv (mget  :op inst))
        (rc1 (car (mget :rc inst)))
        (ra1 (car (mget :ra inst)))
        (rb1 (car (mget :rb inst)))
        (rc2 (cdr (mget :rc inst)))
        (ra2 (cdr (mget :ra inst)))
        (rb2 (cdr (mget :rb inst))))
    (case opv
      (vadd (add-rc ra2 rb2 rc2 
                    (add-rc ra1 rb1 rc1 regs)))
      (vsub (sub-rc ra2 rb2 rc2 
                    (sub-rc ra1 rb1 rc1 regs)))
      (vmul (mul-rc ra2 rb2 rc2 
                    (mul-rc ra1 rb1 rc1 regs)))
      (otherwise regs))))

;; this function is exactly same as isa-step but can potentially be
;; different in a different implementation. For example, this could be
;; binary implementation of the operations.
(defun step-scalar-reg (inst regs)
  (let* ((op (mget  :op inst))
         (rc (mget  :rc inst))
         (ra (mget  :ra inst))
         (rb (mget  :rb inst)))
    (case op
      (add (add-rc ra rb rc regs))  ; REGS[rc] := REGS[ra] + REGS[rb]
      (sub (sub-rc ra rb rc regs))
      (mul (mul-rc ra rb rc regs))
      (otherwise regs))))

(defun step-reg (inst regs)
  (cond ((vecinstp inst)
         (step-vec-reg inst regs))
        (t ;(instp inst)
         (step-scalar-reg inst regs))))

(defun vecisa-step (s)
  (let* ((inst (nth (mget :prc s) (vecisa-state-vecinmem s))))
    (vecisa-state (1+ (mget :prc s))
                  (step-reg inst (mget :regs s))
                  (vecisa-state-vecinmem s))))
