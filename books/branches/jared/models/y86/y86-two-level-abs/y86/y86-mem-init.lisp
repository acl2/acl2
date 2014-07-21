;  y86-mem-init.lisp                          Warren A. Hunt, Jr.

(in-package "ACL2")

(include-book "y86")
(local (include-book "centaur/gl/gl" :dir :system))

; Functions to gather items from the registers and memory.
; Functions to initialize the memory.

(defund rmbytes (n addr x86-32)
  (declare (xargs :guard (and (natp n)
                              (n32p addr)
                              (x86-32p x86-32))
                  :stobjs (x86-32)))
  (if (mbe :logic (zp n) :exec (= n 0))
      nil
    (cons (list addr (rm08 addr x86-32))
          (rmbytes (1- n) (n32+ addr 1) x86-32))))


(defund m86-clear-mem-dword-addr (x86-32 dword-addr)
  ;; Clear from dword-addr down to memory address zero
  (declare (xargs :guard (and (n30p dword-addr)
                              (x86-32p x86-32))
                  :stobjs (x86-32)))
  (if (mbe :logic (zp dword-addr) :exec (= dword-addr 0))
      x86-32
    (let ((x86-32 (!memi dword-addr 0 x86-32)))
      (m86-clear-mem-dword-addr x86-32 (1- dword-addr)))))

(encapsulate
 ()

 (local
  (def-gl-thm ash-addr--2-is-less-with-exploded-n32p
    :hyp (and (integerp addr)
              (<= 0 addr)
              (< addr 4294967296))
    :concl (n30p (ash addr -2))
    :g-bindings
    `((addr (:g-number ,(gl-int  0  1  33))))))

 (defund m86-clear-mem (x86-32 addr)
   ;; Clear from addr down to memory address zero
   (declare (xargs :guard  (and (n32p addr)
                                (x86-32p x86-32))
                   :stobjs (x86-32)))
   (b* ((dword-addr (ash addr -2))
        ;; Clear "most" of the memory.
        (x86-32 (m86-clear-mem-dword-addr x86-32 dword-addr))

        ((if (zp addr)) x86-32)
        (x86-32 (wm08 addr 0 x86-32))
        (addr (1- addr))

        ((if (zp addr)) x86-32)
        (x86-32 (wm08 addr 0 x86-32))
        (addr (1- addr))

        ((if (zp addr)) x86-32)
        (x86-32 (wm08 addr 0 x86-32)))
       x86-32)))

(defun m86-regp (updates)
  (declare (xargs :guard t))
  (if (atom updates)
      t
    (b* ((update (car updates))
         (rest   (cdr updates)))
        (and (consp update)
             (b* ((field (car update))
                  (value (cdr update)))
                 (and (keywordp field)
                      (assoc field *x86-32-reg-numbers*)
                      (n32p value)
                      (m86-regp rest)))))))

(defund m86-reg-updates (x86-32 updates)
  (declare (xargs :guard (and (m86-regp updates)
                              (x86-32p x86-32))
                  :stobjs (x86-32)))
  (if (atom updates)
      x86-32
    (b* ((update (car updates))
         (rest   (cdr updates))
         (field  (car update))
         (value  (cdr update))
         (x86-32 (!rgfi (x86-rton field) value x86-32)))
        (m86-reg-updates x86-32 rest))))

(defun m86-memp (updates)
  (declare (xargs :guard t))
  (if (atom updates)
      t
    (b* ((update (car updates))
         (rest   (cdr updates)))
        (and (consp update)
             (b* ((addr  (car update))
                  (value (cdr update)))
                 (and (n32p addr)
                      (n08p value)
                      (m86-memp rest)))))))

(defund m86-mem-updates (x86-32 updates)
  (declare (xargs :guard (and (m86-memp updates)
                              (x86-32p x86-32))
                  :stobjs (x86-32)))
  (if (atom updates)
      x86-32
    (b* ((update (car updates))
         (rest   (cdr updates))
         (addr   (car update))
         (value  (cdr update))
         (x86-32 (wm08 addr value x86-32)))
        (m86-mem-updates x86-32 rest))))


(defund m32-get-regs-and-flags (x86-32)
  (declare (xargs :guard (x86-32p x86-32)
                  :stobjs (x86-32)))
  (let ((eflags (flg x86-32)))
    (list
     (list :eip (eip x86-32))
     (list :eax (rgfi *mr-eax* x86-32)
           :ebx (rgfi *mr-ebx* x86-32)
           :ecx (rgfi *mr-ecx* x86-32)
           :edx (rgfi *mr-edx* x86-32))
     (list :edi (rgfi *mr-edi* x86-32)
           :esi (rgfi *mr-esi* x86-32)
           :ebp (rgfi *mr-ebp* x86-32)
           :esp (rgfi *mr-esp* x86-32))
     (list :eflags eflags
           :f-zf (y86-zf eflags)
           :f-sf (y86-sf eflags)
           :f-of (y86-of eflags))
     (list :mr-status (ms x86-32)))))


(defund m86-clear-regs (x86-32)
  ;; Clear all registers
  (declare (xargs :stobjs (x86-32) :guard (x86-32p x86-32)))
  (b* ((x86-32 (!rgfi *mr-eax* 0 x86-32))
       (x86-32 (!rgfi *mr-ecx* 0 x86-32))
       (x86-32 (!rgfi *mr-edx* 0 x86-32))
       (x86-32 (!rgfi *mr-ebx* 0 x86-32))

       (x86-32 (!rgfi *mr-esi* 0 x86-32))
       (x86-32 (!rgfi *mr-edi* 0 x86-32))
       (x86-32 (!rgfi *mr-esp* 0 x86-32))
       (x86-32 (!rgfi *mr-ebp* 0 x86-32))

       (x86-32 (!eip 0 x86-32))
       (x86-32 (y86-ALU-results-store-flgs 0 0 0 x86-32)))
      x86-32))


(defund init-y86-state (mr-status pc regs flags mem x86-32)
  (declare (xargs :guard (and (n32p pc)
                              (m86-regp regs)
                              (m86-memp mem)
                              (alistp flags)
                              (x86-32p x86-32))
                  :stobjs (x86-32))
           (ignorable mr-status pc regs flags mem))
  (let* ((x86-32 (m86-mem-updates x86-32 mem))
         (x86-32 (m86-reg-updates x86-32 regs))
         (x86-32 (!eip pc x86-32))
         (x86-32 (!ms mr-status x86-32))
         (zf (n01 (nfix (cdr (assoc :zf flags)))))
         (sf (n01 (nfix (cdr (assoc :sf flags)))))
         (of (n01 (nfix (cdr (assoc :of flags)))))
         (x86-32 (y86-ALU-results-store-flgs zf sf of x86-32))
         )
    x86-32))
