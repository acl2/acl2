;; AUTHOR
;; Shilpi Goel <shigoel@cs.utexas.edu>

(in-package "X86ISA")

;; ======================================================================

;; Undef Flg:

(defun undef-flg$notinline (x86)
  (declare (xargs :mode :program :stobjs x86))
  (when (or (equal (f-get-global 'in-prove-flg ACL2::*the-live-state*)
                   t)
            (equal (f-get-global
                    'in-verify-flg ACL2::*the-live-state*)
                   t))
    (return-from X86ISA::undef-flg$notinline
      (X86ISA::undef-flg-logic x86)))
  ;; TO-DO@Shilpi: For now, I'm just returning 0 as the "undefined"
  ;; value.
  (mv 0 x86))

;; Safe-!undef:

(defun safe-!undef$notinline (v x86)
  (declare (xargs :mode :program :stobjs x86))
  (when (or (equal (f-get-global 'in-prove-flg ACL2::*the-live-state*)
                   t)
            (equal (f-get-global 'in-verify-flg
                                 ACL2::*the-live-state*)
                   t))
    (return-from X86ISA::safe-!undef$notinline
      (X86ISA::!undef v x86)))
  (er hard! 'safe-!undef
      "Ill-advised attempt to call safe-!undef during top-level ~
       evaluation."))

;; ======================================================================
