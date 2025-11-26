; Assumptions for 64-bit x86 proofs
;
; Copyright (C) 2016-2019 Kestrel Technology, LLC
; Copyright (C) 2020-2024 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "X")

(include-book "assumptions")
(include-book "readers-and-writers64")
(include-book "read-and-write")
(include-book "read-bytes-and-write-bytes")
(include-book "kestrel/memory/memory48" :dir :system)
(include-book "parsers/parsed-executable-tools")
(local (include-book "kestrel/arithmetic-light/plus" :dir :system))

(defund bytes-loaded-at-address-64 (bytes addr bvp x86)
  (declare (xargs :guard (and (acl2::all-unsigned-byte-p 8 bytes)
                              (true-listp bytes)
                              (consp bytes)
                              (booleanp bvp))
                  :stobjs x86))
  (and ;; We'll base all addresses on the address of the text section
   ;; (we can calculate the relative offset of other things by
   ;; taking their default load addresses (numbers from the
   ;; executable) and subtracting the default load address of the
   ;; text section (also a number stored in the executable).
   ;; The addresses where the program is located are canonical:
   ;; TODO: Or should these be guards (then we could just use program-at)?
   ;; todo: factor out these checks:
   (canonical-address-p addr)
   (canonical-address-p (+ addr
                           ;; (len bytes) ; todo: I've seen a program that ends in RET cause the model to check whether the next address is canonical.  However, changing this broke some proofs.
                           (- (len bytes) 1)
                           ))
   ;; We assume the program (and eventually all data from the
   ;; executable) is loaded into memory.
   ;; (TODO: What about more than 1 section?):
   ;; TODO: "program-at" is not a great name since the bytes may not represent a program:
   (if bvp
       ;; essentially the same as the below PROGRAM-AT claim:
       ;; todo: huge arrays cause STP crashes (exclude these claims from SMT queries)?
       (equal (read-bytes (len bytes) addr x86) bytes)
     (program-at addr bytes x86))))

;; todo: add 64 to the name
(defund addresses-of-subsequent-stack-slots-aux (num-stack-slots address)
  (declare (xargs :guard (and (natp num-stack-slots)
                              (integerp address) ; strengthen?  what if this goes negative?
                              )))
  (if (zp num-stack-slots)
      nil
    (cons address
          (addresses-of-subsequent-stack-slots-aux (+ -1 num-stack-slots) (+ -8 address)))))

(defthmd addresses-of-subsequent-stack-slots-aux-opener
  (implies (and (syntaxp (quotep num-stack-slots))
                (< num-stack-slots 1000) ;prevent huge expansions
                (not (zp num-stack-slots)))
           (equal (addresses-of-subsequent-stack-slots-aux num-stack-slots address)
                  (cons address
                        (addresses-of-subsequent-stack-slots-aux (+ -1 num-stack-slots) (+ -8 address)))))
  :hints (("Goal" :in-theory (enable addresses-of-subsequent-stack-slots-aux))))

(defthm canonical-address-listp-of-addresses-of-subsequent-stack-slots-aux
  (implies (and (posp num-stack-slots)
                (integerp address))
           (equal (x86isa::canonical-address-listp (addresses-of-subsequent-stack-slots-aux num-stack-slots address))
                  (and (x86isa::canonical-address-p address)
                       (x86isa::canonical-address-p (+ (* -8 (- num-stack-slots 1)) address)))))
  :hints (("Subgoal *1/2" :cases ((equal 1 num-stack-slots)))
          ("Goal" :expand (addresses-of-subsequent-stack-slots-aux 1 address)
           :in-theory (enable addresses-of-subsequent-stack-slots-aux
                              x86isa::canonical-address-p signed-byte-p integer-range-p))))


;; recall that the stack grows downward
;; These are just the starting addresses of the slots (1 address per 8-byte slot)
(defun addresses-of-subsequent-stack-slots (num-stack-slots rsp)
  (declare (xargs :guard (and (natp num-stack-slots)
                              (integerp rsp) ; strengthen?  what if this subsequent stack slots go negative?
                              )))
  (let ((first-slot-address (+ -8 rsp)))
    (addresses-of-subsequent-stack-slots-aux num-stack-slots first-slot-address)))

;; (defun all-addreses-of-stack-slots (num-slots rsp)
;;   (x86isa::create-canonical-address-list (* 8 num-slots) (+ (* -8 num-slots) rsp)))

;; Returns a list of terms
(defund make-standard-state-assumptions-64-fn (state-var)
  (declare (xargs :guard (symbolp state-var)))
  `((standard-state-assumption ,state-var)
     (equal (64-bit-modep ,state-var) t)
     ;; Alignment checking is turned off:
     (not (alignment-checking-enabled-p ,state-var))

     ;; The RSP is 8-byte aligned (TODO: check with Shilpi):
     ;; This may not be respected by malware.
     ;; TODO: Try without this
     (equal 0 (bvchop 3 (rgfi *rsp* ,state-var)))

     ;; The return address must be canonical because we will transfer
     ;; control to that address when doing the return:
     (canonical-address-p (logext 64 (read 8 (rgfi *rsp* ,state-var) ,state-var)))

     ;; The stack slot contaning the return address must be canonical
     ;; because the stack pointer returns here when we pop the saved
     ;; RBP:
     (canonical-address-p (rgfi *rsp* ,state-var))

     ;; The stack slot 'below' the return address must be canonical
     ;; because the stack pointer returns here when we do the return:
     (canonical-address-p (+ 8 (rgfi *rsp* ,state-var)))))

(defmacro make-standard-state-assumptions-64 (state-var)
  `(and ,@(make-standard-state-assumptions-64-fn state-var)))

;; NOTE: Some of these conjuncts (e.g., stack pointer alignment) are
;; conventions that may not be respected by malware!
(defun standard-state-assumption-64 (x86)
  (declare (xargs :stobjs x86))
  (make-standard-state-assumptions-64 x86))

;; todo: move (calls x86isa::cpuid-flag, which is non-executable):
(in-theory (disable (:e feature-flag)))

;TODO: Show that there is a state that satisfies these assumptions
;TODO: Use this more
;TODO: Test this on a program which uses more than 1 stack slot
