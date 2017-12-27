;; AUTHOR:
;; Shilpi Goel <shigoel@cs.utexas.edu>

(in-package "X86ISA")

(include-book "syscalls"
              :ttags (:include-raw :undef-flg :syscall-exec))

;; ======================================================================

(defsection other-non-deterministic-computations
  :parents (machine)
  :short "Definitions of other non-deterministic computations"

  :long "<p>All the *-logic functions \(like @(see HW_RND_GEN-logic)
for the @('RDRAND') instruction\) should be untouchable --- we want to
disallow the use of these functions during evaluation as well as proof
since they aren't the top-level interface functions \(like @(see
HW_RND_GEN)\).</p>"

  )

(local (xdoc::set-default-parents other-non-deterministic-computations))

;; ======================================================================
;; INSTRUCTION: RDRAND
;; ======================================================================

(define HW_RND_GEN-logic
  ((size :type (integer 2 8))
   x86)
  :guard (or (equal size 2)
             (equal size 4)
             (equal size 8))
  ;; Old implementation used the env field.
  ;; (pop-x86-oracle x86)
  (b* (((mv cf x86)
        (undef-flg x86))
       ((mv rand x86)
        (undef-read x86))
       (rand (loghead (ash size 3) rand)))
    (mv cf rand x86)))

(define HW_RND_GEN
  ((size :type (integer 2 8))
   x86)
  :inline nil
  :guard (or (equal size 2)
             (equal size 4)
             (equal size 8))
  (HW_RND_GEN-logic size x86))

;; ======================================================================

(push-untouchable (
                   HW_RND_GEN-logic
                   )
                  t)

;; Exec definitions:

(defsection other-non-deterministic-computations-exec
  :parents (other-non-deterministic-computations)
  :short "Definitions of non-deterministic computations to be used for
  execution"
  :long "<p>We smash the definition of @(see HW_RND_GEN) to provide
  random numbers during execution by using Lisp's @('random')
  function.</p>"

; Instruction to cert.pl for dependency tracking.
; (depends-on "other-non-det-raw.lsp")

  (defttag :other-non-det)
  (include-raw "other-non-det-raw.lsp"))

;; ======================================================================
