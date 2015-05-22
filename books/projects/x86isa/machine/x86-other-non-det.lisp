;; AUTHOR:
;; Shilpi Goel <shigoel@cs.utexas.edu>

(in-package "X86ISA")

(include-book "x86-syscalls"
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
  (declare (ignorable size))
  (pop-x86-oracle x86))

(define HW_RND_GEN
  ((size :type (integer 2 8))
   x86)
  :inline nil
  :guard (or (equal size 2)
	     (equal size 4)
	     (equal size 8))
  (declare (ignorable size))
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
  :long "<p><b>IMPORTANT:</b> The following raw Lisp definitions will
not be available unless the x86 books have been build with the
environment variable @('X86ISA_EXEC') set to @('t'). See @(see
Build-Instructions) for details.</p>

<ul>
<li>@(see HW_RND_GEN)</li>
</ul>
"

  (build-with-full-exec-support

   x86isa_rdrand_exec_support

   (progn

     (defttag :other-non-det)

     (defconst *os-specific-other-non-det-lib*
       ;; Hopefully, one day I'll have FreeBSD listed here as well.
       (os
	"shared/librdrand.so"    ;; Linux
	"shared/librdrand.dylib" ;; Darwin
	))

     (defconst *shared-other-non-det-dir-path*
       (string-append *current-dir* *os-specific-other-non-det-lib*))

; Instruction to cert.pl for dependency tracking.
; (depends-on "x86-other-non-det-raw.lsp")

     (include-raw "x86-other-non-det-raw.lsp"))

   (value-triple
    (cw "~%~%X86ISA_EXEC Warning: x86-other-non-det-raw.lsp is not included.~%~%~%"))))

;; ======================================================================
