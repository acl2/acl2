;;;; x86-64-vm.lisp -- VOP definitions SBCL

(cl:in-package :sb-vm)

(define-vop (%check-bound)
  (:translate nibbles::%check-bound)
  (:policy :fast-safe)
  (:args (array :scs (descriptor-reg))
         (bound :scs (any-reg))
         (index :scs (any-reg)))
  (:arg-types simple-array-unsigned-byte-8 positive-fixnum tagged-num
              (:constant (member 2 4 8 16)))
  (:info offset)
  (:temporary (:sc any-reg) temp)
  (:results (result :scs (any-reg)))
  (:result-types positive-fixnum)
  (:vop-var vop)
  (:generator 5
    (let ((error (generate-error-code vop 'invalid-array-index-error
                                      array bound index)))
      ;; We want to check the conditions:
      ;;
      ;; 0 <= INDEX
      ;; INDEX < BOUND
      ;; 0 <= INDEX + OFFSET
      ;; (INDEX + OFFSET) < BOUND
      ;;
      ;; We can do this naively with two unsigned checks:
      ;;
      ;; INDEX <_u BOUND
      ;; INDEX + OFFSET <_u BOUND
      ;;
      ;; If INDEX + OFFSET <_u BOUND, though, INDEX must be less than
      ;; BOUND.  We *do* need to check for 0 <= INDEX, but that has
      ;; already been assured by higher-level machinery.
      (inst lea temp (ea (fixnumize offset) nil index))
      (inst cmp temp bound)
      (inst jmp :a error)
      (move result index))))

#.(flet ((frob (bitsize setterp signedp big-endian-p)
           (let* ((name (funcall (if setterp
                                     #'nibbles::byte-set-fun-name
                                     #'nibbles::byte-ref-fun-name)
                                 bitsize signedp big-endian-p))
                  (internal-name (nibbles::internalify name))
                  (operand-size (ecase bitsize
                                  (16 :word)
                                  (32 :dword)
                                  (64 :qword)))
                  (ref-mov-insn (ecase bitsize
                                  (16
                                   (if big-endian-p
                                       'movzx
                                       (if signedp 'movsx 'movzx)))
                                  (32
                                   (if big-endian-p
                                       'mov
                                       (if signedp 'movsxd 'movzxd)))
                                   (64 'mov)))
                  (result-sc (if signedp 'signed-reg 'unsigned-reg))
                  (result-type (if signedp 'signed-num 'unsigned-num)))
             (flet ((movx (insn dest source source-size)
                      (cond ((eq insn 'mov)
                             `(inst ,insn ,dest ,source))
                            ;; (movzx (:dword :qword) dest source) is
                            ;; no longer allowed on SBCL > 2.1.4.134
                            ;; but older versions already supported
                            ;; this new spelling.
                            ((and (member insn '(movzx movzxd))
                                  (eq source-size :dword))
                             `(inst mov :dword ,dest ,source))
                            (t
                             `(inst ,(case insn (movsxd 'movsx) (movzxd 'movzx) (t insn))
                                    '(,source-size :qword) ,dest ,source))))
                    (swap-tn-inst-form (tn-name)
                      (if (= bitsize 16)
                          `(inst rol ,operand-size ,tn-name 8)
                          ;; The '(bswap :dword r)' notation is only
                          ;; supported on SBCL > 1.5.9.
                          (if (ignore-errors (sb-ext:assert-version->= 1 5 9 17) t)
                              `(inst bswap ,operand-size ,tn-name)
                              `(inst bswap (sb-vm::reg-in-size ,tn-name ,operand-size))))))
               `(define-vop (,name)
                  (:translate ,internal-name)
                  (:policy :fast-safe)
                  (:args (vector :scs (descriptor-reg))
                         (index :scs (immediate unsigned-reg))
                         ,@(when setterp
                             `((value* :scs (,result-sc) :target result))))
                  (:arg-types simple-array-unsigned-byte-8
                              positive-fixnum
                              ,@(when setterp
                                  `(,result-type)))
                  ,@(when (and setterp big-endian-p)
                      `((:temporary (:sc unsigned-reg
                                     :from (:load 0)
                                     :to (:result 0)) temp)))
                  (:results (result :scs (,result-sc)))
                  (:result-types ,result-type)
                  (:generator 3
                    (let* ((base-disp (- (* vector-data-offset n-word-bytes)
                                         other-pointer-lowtag))
                           (memref (sc-case index
                                     (immediate
                                      (ea (+ (tn-value index) base-disp) vector))
                                     (t
                                      (ea base-disp vector index)))))
                      ,@(when (and setterp big-endian-p)
                          `((inst mov temp value*)
                            ,(swap-tn-inst-form 'temp)))
                      ,(if setterp
                           `(inst mov ,operand-size memref ,(if big-endian-p
                                                                'temp
                                                                'value*))
                           (movx ref-mov-insn 'result 'memref operand-size))
                      ,@(if setterp
                            '((move result value*))
                            (when big-endian-p
                              `(,(swap-tn-inst-form 'result)
                                ,(when (and (/= bitsize 64) signedp)
                                   (movx 'movsx 'result 'result operand-size))))))))))))
    (loop for i from 0 upto #b10111
          for bitsize = (ecase (ldb (byte 2 3) i)
                          (0 16)
                          (1 32)
                          (2 64))
          for setterp = (logbitp 2 i)
          for signedp = (logbitp 1 i)
          for big-endian-p = (logbitp 0 i)
          collect (frob bitsize setterp signedp big-endian-p) into forms
          finally (return `(progn ,@forms))))
