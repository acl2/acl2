; Generating assumptions for 32-bit RISC-V code proofs
;
; Copyright (C) 2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "R")

;; This is for 32-bit only

(include-book "kestrel/memory/memory32" :dir :system)
(include-book "kestrel/memory/memory-regions" :dir :system)
(include-book "../../x86/parsers/elf-tools")
(include-book "read-and-write")

;; Creates assumptions about STATE-VAR and BASE-VAR.
;; Returns (mv erp assumptions).
(defund assumptions-for-memory-regions32 (regions
                                          base-var
                                          state-var
                                          stack-pointer-expression ; over state-var
                                          stack-slots-needed existing-stack-slots position-independentp acc)
  (declare (xargs :guard (and (memory-regionsp regions)
                              (symbolp base-var) ; only used if position-independentp
                              (symbolp state-var)
                              (pseudo-termp stack-pointer-expression)
                              (natp stack-slots-needed)
                              (natp existing-stack-slots)
                              (booleanp position-independentp)
                              (true-listp acc))
                  :guard-hints (("Goal" :in-theory (e/d (memory-regionsp
                                                         memory-regionp)
                                                        (acl2::acl2-numberp-of-car-when-acl2-number-listp ; todo, for speed
                                                         rationalp-implies-acl2-numberp))))))
  (if (endp regions)
      (mv nil (reverse acc))
    (b* ((region (first regions))
         (length (first region))
         (addr (second region))
         (bytes (third region))
         ((mv erp assumptions-for-region)
          ;(if position-independentp
          ;;todo:
          ;;               ;; Relative addresses make everything relative to the base-var:
          ;;               (b* ((last-addr (+ 1 (+ -1 addr length))) ; adding 1 for the one-past-RET issue
          ;;                    ;; Ensures that the canonical assumptions are satisfiable:
          ;;                    ((when (<= (expt 2 47) last-addr)) ; could relax to 2^48, since base-addr can be "negative"?
          ;;                     (mv :bad-address nil))
          ;;                    (first-addr-term (symbolic-bvplus-constant 64 addr base-var))
          ;;                    ;; (last-addr-term (symbolic-bvplus-constant 48 (+ 1 ; todo: why is this needed?  I have code that ends in RET and checks whether the address after the RET is canonical.  however, making this change elsewhere broke other proofs.
          ;;                    ;;                                                 (+ -1 addr length))
          ;;                    ;;                                           base-var)
          ;;                    ;;                 ;;   (symbolic-add-constant (+ 1 ; todo: why is this needed?  I have code that ends in RET and checks whether the address after the RET is canonical.  however, making this change elsewhere broke other proofs.
          ;;                    ;;                 ;;                             (+ -1 addr length))
          ;;                    ;;                 ;;                          base-var)
          ;;                    ;;                 )
          ;; ; todo: use bvplus?
          ;;                    )
          ;;                 (mv nil ; no error
          ;;                     (append
          ;;                       ;; Assert that the addresses are canonical:
          ;;                       `((canonical-regionp ,(+ 1 length)  ; todo: why the +1? (see above about RET)
          ;;                                            ,(if (= addr 0) base-var `(bvplus 64 ,addr ,base-var)) ; todo: call symbolic-bvplus-constant
          ;;                                            ))
          ;;                       ;; Assert that the chunk is loaded into memory:
          ;;                       ;; TODO: "program-at" is not a great name since the bytes may not represent a program:
          ;;                       `((equal (read-bytes ,first-addr-term ',(len bytes) ,state-var) ',bytes))
          ;;                       ;; Assert that the chunk is disjoint from the existing part of the stack that will be written:
          ;;                       ;; TODO: Do this only for writable chunks?
          ;;                       (if (posp existing-stack-slots)
          ;;                           ;; todo: make a better version of separate that doesn't require the Ns to be positive (and that doesn't have the useless rwx params):
          ;;                           `((disjoint-regions48p ',(len bytes) ,first-addr-term
          ;;                                                  ',(* 8 existing-stack-slots) ,stack-pointer-expression))
          ;;                         nil)
          ;;                       ;; Assert that the chunk is disjoint from the new part of the stack that will be written:
          ;;                       ;; TODO: Do this only for writable chunks?
          ;;                       (if (posp stack-slots-needed)
          ;;                           ;; todo: make a better version of separate that doesn't require the Ns to be positive (and that doesn't have the useless rwx params):
          ;;                           `((disjoint-regions48p ',(len bytes) ,first-addr-term
          ;;                                                  ',(* 8 stack-slots-needed) (bvplus 48 ',(bvchop 48 (* -8 stack-slots-needed)) ,stack-pointer-expression)))
          ;;                         nil))))
          ;; Absolute addresses are just numbers:
          (let* ((first-addr addr)
                 (last-addr (+ -1 addr length)) ; don't need to add 1 here for that RET issue, because the number should be clearly canonical
                 )
            (if (not (unsigned-byte-p 32 last-addr))
                (mv :bad-address nil)
              (mv nil ; no error
                  `(;; Assert that the chunk is loaded into memory:
                    (equal (read-bytes ',first-addr ',(len bytes) ,state-var) ',bytes)
                    ;; Assert that the chunk is disjoint from the existing part of the stack that will be written:
                    ;; TODO: Do this only for writable chunks?
                    ,@(if (posp existing-stack-slots)
                          `((disjoint-regions32p ',(len bytes) ',first-addr
                                                 ',(* 4 existing-stack-slots) ,stack-pointer-expression))
                        nil)
                    ;; Assert that the chunk is disjoint from the new part of the stack that will be written:
                    ;; TODO: Do this only for writable chunks?
                    ,@(if (posp stack-slots-needed)
                          `((disjoint-regions32p ',(len bytes) ',first-addr
                                                 ',(* 4 stack-slots-needed) (bvplus 32 ',(bvchop 32 (* -4 stack-slots-needed)) ,stack-pointer-expression)))
                        nil))))))
         ((when erp) (mv erp nil)))
      (assumptions-for-memory-regions32 (rest regions)
                                        base-var state-var stack-pointer-expression stack-slots-needed existing-stack-slots position-independentp
                                        ;; todo: think about the order:
                                        (append assumptions-for-region acc)))))

;; Returns (mv erp assumptions).
(defun assumptions-elf32 (parsed-elf)
  (declare (xargs :guard (acl2::parsed-elfp parsed-elf)))
  (b* (((mv erp regions) (acl2::elf64-regions-to-load parsed-elf))
       (state-var 'stat)
       ((when erp) (mv erp nil))
       ((mv erp memory-region-assumptions)
        (assumptions-for-memory-regions32 regions 'base-address ; not used yet
                                          state-var
                                          `(reg '2 ,state-var) ; over the state-var
                                          10 ; todo: stack-slots-needed
                                          0 ; todo: existing-stack-slots
                                          nil ; todo: position-independentp
                                          nil))
       ((when erp) (mv erp nil))
       (standard-assumptions '((not (error32p stat))
                               ;; (state32p stat)
                               )) ; todo: what else?
       )
    (mv nil ; no error
        (append standard-assumptions
                memory-region-assumptions))))

;; does not return an error
(defund assumptions-elf32! (parsed-elf)
  (mv-let (erp assumptions)
    (assumptions-elf32 parsed-elf)
    (if erp
        (er hard? 'assumptions-elf32! "Error generating assumptions: ~x0." erp)
      assumptions)))
