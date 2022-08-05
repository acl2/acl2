; Assumptions for 64-bit x86 proofs
;
; Copyright (C) 2016-2019 Kestrel Technology, LLC
; Copyright (C) 2020-2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "X")

(include-book "assumptions")
(include-book "read-and-write")
(include-book "../parsers/parsed-executable-tools")
(local (include-book "kestrel/arithmetic-light/plus" :dir :system))

(defun bytes-loaded-at-address-64 (bytes addr x86)
  (declare (xargs :guard (and (acl2::all-unsigned-byte-p 8 bytes)
                              (true-listp bytes)
                              (consp bytes))
                  :stobjs x86))
  (and ;; We'll base all addresses on the address of the text section
   ;; (we can calculate the relative offset of other things by
   ;; taking their default load addresses (numbers from the
   ;; executable) and subtracting the default load address of the
   ;; text section (also a number stored in the executable).
   ;; The addresses where the program is located are canonical:
   ;; TODO: Or should these be guards (then we could just use program-at)?
   (canonical-address-p addr)
   (canonical-address-p (+ addr
                           (- (len bytes) 1)))
   ;; We assume the program (and eventually all data from the
   ;; executable) is loaded into memory.
   ;; (TODO: What about more than 1 section?):
   ;; TODO: "program-at" is not a great name since the bytes may not represent a program:
   (program-at addr
               bytes
               x86)))

(defund addresses-of-subsequent-stack-slots-aux (num-stack-slots address)
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
  (let ((first-slot-address (+ -8 rsp)))
    (addresses-of-subsequent-stack-slots-aux num-stack-slots first-slot-address)))

;; (defun all-addreses-of-stack-slots (num-slots rsp)
;;   (x86isa::create-canonical-address-list (* 8 num-slots) (+ (* -8 num-slots) rsp)))

;; This is separate so we can easily create a list of terms to pass to symsim.
;; NOTE: Some of these (e.g., stack pointer alignment) are conventions that may not be respected by malware!
;; Creates a list of terms.
(defun standard-state-assumption-terms-64 (x86)
  `((standard-state-assumption ,x86)
    (equal (64-bit-modep ,x86) t)
    ;; Alignment checking is turned off.
    (not (alignment-checking-enabled-p ,x86))

    ;; The RSP is 8-byte aligned (TODO: check with Shilpi):
    ;; This may not be respected by malware.
    ;; TODO: Try without this
    (equal 0 (bvchop 3 (rgfi *rsp* ,x86)))

    ;; The return address must be canonical because we will transfer
    ;; control to that address when doing the return:
    (canonical-address-p (read 8 (rgfi *rsp* x86) x86))

    ;; The stack slot contaning the return address must be canonical
    ;; because the stack pointer returns here when we pop the saved
    ;; RBP:
    (canonical-address-p (rgfi *rsp* x86))

    ;; The stack slot 'below' the return address must be canonical
    ;; because the stack pointer returns here when we do the return:
    (canonical-address-p (+ 8 (rgfi *rsp* x86)))))

(defmacro standard-state-assumption-64 (x86)
  `(and ,@(standard-state-assumption-terms-64 x86)))


;TODO: Show that there is a state that satisfies these assumptions
;TODO: Use this more
;TODO: Test this on a program which uses more than 1 stack slot

;; Check that the x86 state has TEXT-SECTION-BYTES loaded starting at
;; TEXT-OFFSET and has the program counter set to TEXT-OFFSET plus
;; OFFSET-TO-SUBROUTINE.  Also assume things are disjoint.  TODO: Give this a
;; better name, this is logical, not meta.
(defun standard-assumptions-core-64 (text-section-bytes
                                     text-offset
                                     offset-to-subroutine ;from the start of the text section
                                     stack-slots-needed
                                     x86)
  (declare (xargs :stobjs x86
                  :verify-guards nil ;todo
                  ))
  (and (standard-state-assumption-64 x86)
       (bytes-loaded-at-address-64 text-section-bytes text-offset x86)
       ;; The program counter is at the start of the routine to lift:
       (equal (rip x86) (+ text-offset offset-to-subroutine))

       ;; Stack addresses are canonical (could use something like all-addreses-of-stack-slots here, but these addresses are by definition canonical):
       (x86isa::canonical-address-listp (addresses-of-subsequent-stack-slots stack-slots-needed (rgfi *rsp* x86)))
       ;; old: (canonical-address-p (+ -8 (rgfi *rsp* x86))) ;; The stack slot where the RBP will be saved

       ;; The program is disjoint from the part of the stack that is written:
       (separate :r (len text-section-bytes) text-offset
                 ;; Only a single stack slot is written
                 ;;old: (create-canonical-address-list 8 (+ -8 (rgfi *rsp* x86)))
                 :r (* 8 stack-slots-needed) (+ (* -8 stack-slots-needed) (rgfi *rsp* x86)))))

(defun standard-assumptions-mach-o-64 (subroutine-name
                                       parsed-mach-o
                                       stack-slots-needed
                                       text-offset
                                       x86)
  (declare (xargs :stobjs x86
                  :verify-guards nil ;todo
                  ))
  (let ((text-section-bytes (acl2::get-mach-o-code parsed-mach-o)) ;all the code, not just the given subroutine
        (text-section-address (acl2::get-mach-o-code-address parsed-mach-o))
        (subroutine-address (acl2::subroutine-address-mach-o subroutine-name parsed-mach-o)))
    (standard-assumptions-core-64 text-section-bytes
                                  text-offset
                                  (- subroutine-address text-section-address)
                                  stack-slots-needed
                                  x86)))

;; TODO: The error below may not be thrown since this gets inserted as an assumption and simplified rather than being executed.
(defun standard-assumptions-pe-64 (subroutine-name
                                   parsed-executable
                                   stack-slots-needed
                                   text-offset
                                   x86)
  (declare (xargs :stobjs x86
                  :verify-guards nil ;todo
                  ))
  (standard-assumptions-core-64 (acl2::lookup-eq :raw-data (acl2::get-pe-text-section parsed-executable)) ; text-section-bytes, all the code, not just the given subroutine
                                text-offset
                                (acl2::subroutine-address-within-text-section-pe-64 subroutine-name parsed-executable)
                                stack-slots-needed
                                x86))
