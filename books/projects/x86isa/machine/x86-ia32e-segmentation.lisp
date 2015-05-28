;; AUTHOR:
;; Shilpi Goel <shigoel@cs.utexas.edu>

(in-package "X86ISA")
(include-book "x86-ia32e-paging" :ttags (:undef-flg))

;; ======================================================================

(local (include-book "centaur/bitops/ihs-extensions" :dir :system))

;; ======================================================================

(defsection ia32e-segmentation
  :parents (machine)
  :short "Specification of Segmentation in the 64-bit Mode"
  )

(local (xdoc::set-default-parents ia32e-segmentation))

;; ======================================================================

;; Segmentation:

;; LLDT: http://www.ece.unm.edu/~jimp/310/slides/micro_arch2.html
;;       http://www.fermimn.gov.it/linux/quarta/x86/lldt.htm
;;       http://stackoverflow.com/questions/6886112/using-lldt-and-configuring-the-gdt-for-it
;;       http://www.osdever.net/bkerndev/Docs/gdt.htm
;;       http://duartes.org/gustavo/blog/post/memory-translation-and-segmentation/

;; QUESTION:

;; FS and GS segments are given special treatment in that their base
;; addresses are allowed to be non-zero in 64-bit mode.  The hidden
;; portions of the FS and GS registers are mapped to the
;; model-specific registers IA32_FS_BASE and IA32_GS_BASE,
;; respectively---specifically, these registers contain the segment
;; base address.  My question is:

;; 1. When the FS or GS selector is updated to point to a data-segment
;; descriptor in GDT or LDT, is the base address from the descriptor
;; used to update these model-specific registers?

;; 2. Or is the base address in the descriptor ignored completely and
;; we have to update the model-specific registers separately to
;; provide a base address for FS or GS?

;; ======================================================================

;; [TO-DO@Shilpi]: I've written the following predicates by referring
;; to the AMD manuals.  Turns out that segmentation differs
;; significantly in Intel and AMD machines.  Intel defines more fields
;; in the descriptors to be available in 64-bit mode than AMD.  Also,
;; Intel defines a descriptor --- the Task gate --- that is not
;; available in AMD machines at all.  I need to read chapters 5, 6,
;; and 7 from Intel Vol. 3 to figure out how segmentation is done on
;; Intel machines.

;; Predicates to determine valid user descriptors (in IA32e mode):

;; Code Segment Descriptor:

(define ia32e-valid-code-segment-descriptor-p
  ((descriptor :type (unsigned-byte 64)))
  :parents (ia32e-segmentation)
  :short "Recognizer for a valid code segment descriptor \(which is a
  64-bit field\)"

  (b* ((type (code-segment-descriptor-layout-slice :type descriptor))
       (msb-of-type (part-select type :low 3 :width 1))

       ((when (not (equal msb-of-type 1)))
        (mv nil (cons :Invalid-Segment-Type descriptor)))

       ;; User segment?
       ((when (not (equal (code-segment-descriptor-layout-slice :s descriptor) 1)))
        (mv nil (cons :Invalid-Segment-Type descriptor)))

       ;; Segment Present?
       ((when (not (equal (code-segment-descriptor-layout-slice :p descriptor) 1)))
        (mv nil (cons :Segment-Not-Present descriptor)))

       ;; IA32e Mode is on?
       ((when (not (equal (code-segment-descriptor-layout-slice :l descriptor) 1)))
        (mv nil (cons :IA32e-Mode-Off descriptor)))

       ;; Default operand size of 32 bit and default address size of
       ;; 64 bits when no error below.
       ((when (not (equal (code-segment-descriptor-layout-slice :d descriptor) 0)))
        (mv nil (cons :IA32e-Default-Operand-Size-Incorrect descriptor))))
      (mv t 0)))

;; Data Segment Descriptor:

(define ia32e-valid-data-segment-descriptor-p
  ((descriptor :type (unsigned-byte 64)))
  :parents (ia32e-segmentation)
  :short "Recognizer for a valid data segment descriptor \(which is a
  64-bit field\)"

  (b* ((type (data-segment-descriptor-layout-slice :type descriptor))
       (msb-of-type (part-select type :low 3 :width 1))

       ((when (not (equal msb-of-type 0)))
        (mv nil (cons :Invalid-Type descriptor)))

       ;; User segment?
       ((when (not (equal (data-segment-descriptor-layout-slice :s descriptor) 1)))
        (mv nil (cons :Invalid-Segment-Type descriptor)))

       ;; Segment is present.
       ((when (not (equal (data-segment-descriptor-layout-slice :p descriptor) 1)))
        (mv nil (cons :Segment-Not-Present descriptor))))
      (mv t 0)))

;; Predicates to determine valid system descriptors (in IA32e mode):

;; 64-bit LDT Descriptor:

(define ia32e-valid-ldt-segment-descriptor-p
  ((descriptor :type (unsigned-byte 128)))
  :parents (ia32e-segmentation)
  :short "Recognizer for a valid LDT segment descriptor \(which is a
  128-bit field\)"


  (b* ((type (system-segment-descriptor-layout-slice :type descriptor))
       ;; Valid type: 64-bit LDT?
       ((when (not (equal type #x2)))
        (mv nil (cons :Invalid-Type descriptor)))

       ;; System Segment?
       ((when (not (equal (system-segment-descriptor-layout-slice :s descriptor) 0)))
        (mv nil (cons :Invalid-Segment-Type descriptor)))

       ;; Segment Present?
       ((when (not (equal (system-segment-descriptor-layout-slice :p descriptor) 1)))
        (mv nil (cons :Segment-Not-Present descriptor)))

       ;; All zeroes?
       ((when (not (equal (system-segment-descriptor-layout-slice :all-zeroes? descriptor) 0)))
        (mv nil (cons :All-Zeroes-Absent descriptor))))

      (mv t 0)))

;; Available 64-bit TSS, and Busy 64-bit TSS Descriptor (in IA32e mode):

(define ia32e-valid-available-tss-segment-descriptor-p
  ((descriptor :type (unsigned-byte 128)))
  :parents (ia32e-segmentation)
  :short "Recognizer for a valid Available TSS segment descriptor
  \(which is a 128-bit field\)"

  (b* ((type (system-segment-descriptor-layout-slice :type descriptor))
       ((when (not (equal type #x9)))
        (mv nil (cons :Invalid-Type descriptor)))

       ;; System Segment?
       ((when (not (equal (system-segment-descriptor-layout-slice :s descriptor) 0)))
        (mv nil (cons :Invalid-Segment-Type descriptor)))

       ((when (not (equal (system-segment-descriptor-layout-slice :p descriptor) 1)))
        (mv nil (cons :Segment-Not-Present descriptor)))

       ((when (not (equal (system-segment-descriptor-layout-slice :all-zeroes? descriptor) 0)))
        (mv nil (cons :All-Zeroes-Absent descriptor))))
      (mv t 0)))

(define ia32e-valid-busy-tss-segment-descriptor-p
  ((descriptor :type (unsigned-byte 128)))
  :parents (ia32e-segmentation)
  :short "Recognizer for a valid Busy TSS segment descriptor \(which
  is a 128-bit field\)"

  (b* ((type (system-segment-descriptor-layout-slice :type descriptor))
       ((when (not (equal type #xB)))
        (mv nil (cons :Invalid-Type descriptor)))

       ;; System Segment?
       ((when (not (equal (system-segment-descriptor-layout-slice :s descriptor) 0)))
        (mv nil (cons :Invalid-Segment-Type descriptor)))

       ((when (not (equal (system-segment-descriptor-layout-slice :p descriptor) 1)))
        (mv nil (cons :Segment-Not-Present descriptor)))

       ((when (not (equal (system-segment-descriptor-layout-slice :all-zeroes? descriptor) 0)))
        (mv nil (cons :All-Zeroes-Absent descriptor))))
      (mv t 0)))

;; 64-bit mode Call Gate:

(define ia32e-valid-call-gate-segment-descriptor-p
  ((descriptor :type (unsigned-byte 128)))
  :parents (ia32e-segmentation)
  :short "Recognizer for a valid Call Gate segment descriptor \(which
  is a 128-bit field\)"

  (b* ((type (call-gate-descriptor-layout-slice :type descriptor))
       ((when (not (equal type #xC)))
        (mv nil (cons :Invalid-Type descriptor)))
       ((when (not (equal (call-gate-descriptor-layout-slice :s descriptor) 0)))
        (mv nil (cons :Invalid-Segment-Type descriptor)))
       ((when (not (equal (call-gate-descriptor-layout-slice :p descriptor) 1)))
        (mv nil (cons :Segment-Not-Present descriptor)))
       ((when (not (equal (call-gate-descriptor-layout-slice :all-zeroes? descriptor) 0)))
        (mv nil (cons :All-Zeroes-Absent descriptor))))
      (mv t 0)))

;; 64-bit Interrupt and Trap Gate Descriptor:

(define ia32e-valid-interrupt-gates-segment-descriptor-p
  ((descriptor :type (unsigned-byte 128)))
  :parents (ia32e-segmentation)
  :short "Recognizer for a valid Interrupt Gate segment descriptor
  \(which is a 128-bit field\)"

  (b* ((type (interrupt/trap-gate-descriptor-layout-slice :type descriptor))
       ((when (not (equal type #xE)))
        (mv nil (cons :Invalid-Type descriptor)))
       ((when (not (equal (interrupt/trap-gate-descriptor-layout-slice :s descriptor) 0)))
        (mv nil (cons :Invalid-Segment-Type descriptor)))
       ((when (not (equal (interrupt/trap-gate-descriptor-layout-slice :p descriptor) 1)))
        (mv nil (cons :Segment-Not-Present descriptor))))
      (mv t 0)))

(define ia32e-valid-trap-gates-segment-descriptor-p
  ((descriptor :type (unsigned-byte 128)))
  :parents (ia32e-segmentation)
  :short "Recognizer for a valid Trap Gate segment descriptor \(which
  is a 128-bit field\)"

  (b* ((type (interrupt/trap-gate-descriptor-layout-slice :type descriptor))
       ((when (not (equal type #xF)))
        (mv nil (cons :Invalid-Type descriptor)))
       ((when (not (equal (interrupt/trap-gate-descriptor-layout-slice :s descriptor) 0)))
        (mv nil (cons :Invalid-Segment-Type descriptor)))
       ((when (not (equal (interrupt/trap-gate-descriptor-layout-slice :p descriptor) 1)))
        (mv nil (cons :Segment-Not-Present descriptor))))
      (mv t 0)))

;; ======================================================================

;; Given a descriptor, we consolidate the various flags contributing
;; to the attribute field in the hidden portions of the segment
;; registers.

(local (include-book "centaur/gl/gl" :dir :system))

;; Code Segment:

(local
 (def-gl-thm make-code-segment-attr-guard-helper
   :hyp (unsigned-byte-p 64 descriptor)
   :concl (equal
           (logior
            (loghead 4 (logtail 40 descriptor))
            (ash (bool->bit (logbitp 44 descriptor))
                 4)
            (logand
             65504
             (logior
              (ash (loghead 2 (logtail 45 descriptor))
                   5)
              (logand
               65424
               (logior
                (ash (bool->bit (logbitp 47 descriptor))
                     7)
                (logand
                 65392
                 (logior
                  (ash (bool->bit (logbitp 52 descriptor))
                       8)
                  (logand 65264
                          (logior (ash (bool->bit (logbitp 53 descriptor))
                                       9)
                                  (logand 65008
                                          (ash (bool->bit (logbitp 55 descriptor))
                                               11)))))))))))
           (logior
            (loghead 4 (logtail 40 descriptor))
            (logand
             65520
             (logior
              (ash (bool->bit (logbitp 44 descriptor))
                   4)
              (logand
               65519
               (logior
                (ash (loghead 2 (logtail 45 descriptor))
                     5)
                (logand
                 65439
                 (logior
                  (ash (bool->bit (logbitp 47 descriptor))
                       7)
                  (logand
                   65407
                   (logior
                    (ash (bool->bit (logbitp 52 descriptor))
                         8)
                    (logand 65279
                            (logior (ash (bool->bit (logbitp 53 descriptor))
                                         9)
                                    (logand 65023
                                            (ash (bool->bit (logbitp 55 descriptor))
                                                 11))))))))))))))
   :g-bindings (gl::auto-bindings
                (:nat descriptor 64))))

(define make-code-segment-attr-field
  ((descriptor  :type (unsigned-byte 64)))
  :parents (ia32e-segmentation)
  :short "Constructor for the Code Segment attribute field"

  :guard-hints (("Goal" :in-theory (e/d ()
                                        (unsigned-byte-p))))

  (b* ((type
        (code-segment-descriptor-layout-slice :type descriptor))
       (s
        (code-segment-descriptor-layout-slice :s descriptor))
       (dpl
        (code-segment-descriptor-layout-slice :dpl descriptor))
       (p
        (code-segment-descriptor-layout-slice :p descriptor))
       (avl
        (code-segment-descriptor-layout-slice :avl descriptor))
       (l
        (code-segment-descriptor-layout-slice :l descriptor))
       (g
        (code-segment-descriptor-layout-slice :g descriptor)))

      (!code-segment-descriptor-attributes-layout-slice
       :type type
       (!code-segment-descriptor-attributes-layout-slice
        :s s
        (!code-segment-descriptor-attributes-layout-slice
         :dpl dpl
         (!code-segment-descriptor-attributes-layout-slice
          :p p
          (!code-segment-descriptor-attributes-layout-slice
           :avl avl
           (!code-segment-descriptor-attributes-layout-slice
            :l l
            (!code-segment-descriptor-attributes-layout-slice
             :g g
             0))))))))

  ///

  (defthm-usb n16p-make-code-segment-attr
    :hyp (unsigned-byte-p 64 descriptor)
    :bound 16
    :concl (make-code-segment-attr-field descriptor)
    :gen-type t
    :gen-linear t))

;; Data Segment:

(local
 (def-gl-thm make-data-segment-attr-guard-helper
   :hyp (unsigned-byte-p 64 descriptor)
   :concl (equal
           (logior
            (loghead 4 (logtail 40 descriptor))
            (ash (bool->bit (logbitp 44 descriptor))
                 4)
            (logand
             65504
             (logior
              (ash (loghead 2 (logtail 45 descriptor))
                   5)
              (logand
               65424
               (logior
                (ash (bool->bit (logbitp 47 descriptor))
                     7)
                (logand
                 65392
                 (logior
                  (ash (bool->bit (logbitp 52 descriptor))
                       8)
                  (logand 65264
                          (logior (ash (bool->bit (logbitp 54 descriptor))
                                       9)
                                  (logand 65008
                                          (ash (bool->bit (logbitp 55 descriptor))
                                               10)))))))))))
           (logior
            (loghead 4 (logtail 40 descriptor))
            (logand
             65520
             (logior
              (ash (bool->bit (logbitp 44 descriptor))
                   4)
              (logand
               65519
               (logior
                (ash (loghead 2 (logtail 45 descriptor))
                     5)
                (logand
                 65439
                 (logior
                  (ash (bool->bit (logbitp 47 descriptor))
                       7)
                  (logand
                   65407
                   (logior
                    (ash (bool->bit (logbitp 52 descriptor))
                         8)
                    (logand 65279
                            (logior (ash (bool->bit (logbitp 54 descriptor))
                                         9)
                                    (logand 65023
                                            (ash (bool->bit (logbitp 55 descriptor))
                                                 10))))))))))))))
   :g-bindings (gl::auto-bindings
                (:nat descriptor 64))))

(define make-data-segment-attr-field
  ((descriptor  :type (unsigned-byte 64)))
  :parents (ia32e-segmentation)
  :short "Constructor for the Data Segment attribute field"

  :guard-hints (("Goal" :in-theory (e/d ()
                                        (unsigned-byte-p))))

  (b* ((type
        (data-segment-descriptor-layout-slice :type descriptor))
       (s
        (data-segment-descriptor-layout-slice :s descriptor))
       (dpl
        (data-segment-descriptor-layout-slice :dpl descriptor))
       (p
        (data-segment-descriptor-layout-slice :p descriptor))
       (avl
        (data-segment-descriptor-layout-slice :avl descriptor))
       (d/b
        (data-segment-descriptor-layout-slice :d/b descriptor))
       (g
        (data-segment-descriptor-layout-slice :g descriptor)))

      (!data-segment-descriptor-attributes-layout-slice
       :type type
       (!data-segment-descriptor-attributes-layout-slice
        :s s
        (!data-segment-descriptor-attributes-layout-slice
         :dpl dpl
         (!data-segment-descriptor-attributes-layout-slice
          :p p
          (!data-segment-descriptor-attributes-layout-slice
           :avl avl
           (!data-segment-descriptor-attributes-layout-slice
            :d/b d/b
            (!data-segment-descriptor-attributes-layout-slice
             :g g
             0))))))))

  ///

  (defthm-usb n16p-make-data-segment-attr
    :hyp (unsigned-byte-p 64 descriptor)
    :bound 16
    :concl (make-data-segment-attr-field descriptor)
    :gen-type t
    :gen-linear t))

;; System Segment:

(local
 (def-gl-thm make-system-segment-attr-guard-helper
   :hyp (and (unsigned-byte-p 1 g)
             (unsigned-byte-p 1 avl)
             (unsigned-byte-p 1 p)
             (unsigned-byte-p 2 dpl)
             (unsigned-byte-p 1 s)
             (unsigned-byte-p 4 type))
   :concl (equal
           (logior
            type (ash s #x4)
            (logand
             #xffe0
             (logior
              (ash dpl #x5)
              (logand #xff90
                      (logior (ash p #x7)
                              (logand #xff70
                                      (logior (ash avl #x8)
                                              (logand #xfef0 (ash g #x9)))))))))
           (logior
            type
            (logand
             #xfff0
             (logior
              (ash s #x4)
              (logand
               #xffef
               (logior
                (ash dpl #x5)
                (logand #xff9f
                        (logior (ash p #x7)
                                (logand #xff7f
                                        (logior (ash avl #x8)
                                                (logand #xfeff (ash g #x9))))))))))))
   :g-bindings (gl::auto-bindings
                (:nat g    1)
                (:nat avl  1)
                (:nat p    1)
                (:nat dpl  2)
                (:nat s    1)
                (:nat type 4))))


(define make-system-segment-attr-field
  ((descriptor  :type (unsigned-byte 128)))

  :parents (ia32e-segmentation)
  :short "Constructor for the System Segment attribute field"
  :guard-hints (("Goal" :in-theory (e/d ()
                                        (unsigned-byte-p))))

  (b* ((type
        (system-segment-descriptor-layout-slice :type descriptor))
       (s
        (system-segment-descriptor-layout-slice :s descriptor))
       (dpl
        (system-segment-descriptor-layout-slice :dpl descriptor))
       (p
        (system-segment-descriptor-layout-slice :p descriptor))
       (avl
        (system-segment-descriptor-layout-slice :avl descriptor))
       (g
        (system-segment-descriptor-layout-slice :g descriptor)))

      (!system-segment-descriptor-attributes-layout-slice
       :type type
       (!system-segment-descriptor-attributes-layout-slice
        :s s
        (!system-segment-descriptor-attributes-layout-slice
         :dpl dpl
         (!system-segment-descriptor-attributes-layout-slice
          :p p
          (!system-segment-descriptor-attributes-layout-slice
           :avl avl
           (!system-segment-descriptor-attributes-layout-slice
            :g g
            0)))))))

  ///

  (defthm-usb n16p-make-system-segment-attr
    :hyp (unsigned-byte-p 128 descriptor)
    :bound 16
    :concl (make-system-segment-attr-field descriptor)
    :gen-type t
    :gen-linear t))

;; ======================================================================
