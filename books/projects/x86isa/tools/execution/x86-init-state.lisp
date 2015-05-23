;; AUTHOR:
;; Shilpi Goel <shigoel@cs.utexas.edu>

(in-package "X86ISA")

(include-book "../../machine/x86"
              :ttags (:include-raw :syscall-exec :other-non-det :undef-flg))

;; ======================================================================

(defsection initialize-x86-state
  :parents (program-execution)
  :short "Initializing the x86 state"

  :long "<p>The events in this section are meant to be used to
initialize the x86 state when doing execution or maybe bit-blasting
using GL, not for doing proofs using re-writing.  For events that help
in code proofs, see the books in directory proofs/basics.</p>"
  )

;; ======================================================================

(define n64p-byte-alistp (alst)
  :enabled t
  :parents (initialize-x86-state)
  :short "Recognizer for a list of pairs of up to 64-bit wide linear address and byte"

  (if (atom alst)
      (equal alst nil)
    (if (atom (car alst))
        nil
      (let ((addr (caar alst))
            (byte (cdar alst))
            (rest (cdr  alst)))
        (and (n64p addr)
             (n08p byte)
             (n64p-byte-alistp rest)))))
  ///

  (defthm n64p-byte-alistp-fwd-chain-to-alistp
    (implies (n64p-byte-alistp alst)
             (alistp alst))
    :rule-classes :forward-chaining))

(define load-program-into-memory
  ((n64-bytes-lst "Required to be a @(see n64p-byte-alistp)")
   x86)

  :guard (n64p-byte-alistp n64-bytes-lst)

  :parents (initialize-x86-state)

  :short "Loading a program into the model's memory"

  :long "<p>@('load-program-into-memory') expects a program
  represented in the form of a @('n64p-byte-alistp'), and loads that
  program, byte-by-byte, into the model's memory. Obviously, this
  function is not efficient, but the speed with which we load a
  program into the memory has not yet proved to be a deal-breaker in
  our experiments so far.</p>

<p><b>Note on dealing with linear addresses emitted by GCC/LLVM:</b></p>

<p>GCC and LLVM might not always output addresses satisfying our
definition of @(see canonical-address-p) \(i.e., essentially
@('i48p')\).  These tools will output 64-bit addresses.  Therefore,
this function needs to be able to take a 64-bit address, check if it
is canonical in the \"real\" world, and if so, convert it into a
canonical address in our world.</p>

<code>
if (canonical-address-p (n64-to-i64 address))
    address = (n64-to-i64 address)
else
    error!
</code>"


  (cond ((endp n64-bytes-lst) (mv nil x86))
        (t
         (b* ((n64-addr (caar n64-bytes-lst))
              (byte (cdar n64-bytes-lst))
              ((mv flg addr)
               (let ((i48-addr (n64-to-i64 n64-addr)))
                 (if (canonical-address-p i48-addr)
                     (mv nil i48-addr)
                   (mv t n64-addr))))
              ((when flg)
               (mv (cons 'load-program-into-memory 'non-canonical-address) x86))
              ((mv flg x86) (wm08 addr byte x86))
              ((when flg)
               (mv (cons 'load-program-into-memory 'wm08-error) x86)))
             (load-program-into-memory (cdr n64-bytes-lst) x86))))

  ///

  (defthm x86p-mv-nth-1-load-program-into-memory
    (implies (x86p x86)
             (x86p (mv-nth 1 (load-program-into-memory n64-program-lst x86))))))

;; ======================================================================

(define rgfi-alistp (alst)
  :parents (initialize-x86-state)
  :short "Recognizer for pairs of general-purpose register indices and
  values"
  :long "<p>Note that the register values are required to be @('i64p') </p>"

  :enabled t
  (if (atom alst)
      (equal alst nil)
    (if (atom (car alst))
        nil
      (let ((index (caar alst))
            (value (cdar alst))
            (rest  (cdr  alst)))
        (and (natp index)
             (< index *64-bit-general-purpose-registers-len*)
             (signed-byte-p 64 value)
             (rgfi-alistp rest))))))

(define !rgfi-from-alist (rgf-alist x86)
  :guard (rgfi-alistp rgf-alist)
  :parents (initialize-x86-state)
  :short "Update general-purpose registers as dictated by
  @('rgf-alist'), which is required to be a @('rgfi-alistp')."

  (cond ((endp rgf-alist) x86)
        (t (let ((x86 (!rgfi (caar rgf-alist) (cdar rgf-alist) x86)))
             (!rgfi-from-alist (cdr rgf-alist) x86))))

  ///

  (defthm x86p-!rgfi-from-alist
    (implies (and (rgfi-alistp rgf-alist)
                  (x86p x86))
             (x86p (!rgfi-from-alist rgf-alist x86)))))

(define ctri-alistp (alst)
  :parents (initialize-x86-state)
  :short "Recognizer for pairs of control register indices and values"
  :long "<p>Note that the register values are required to be @('n64p') </p>"

  :enabled t
  (if (atom alst)
      (equal alst nil)
    (if (atom (car alst))
        nil
      (let ((index (caar alst))
            (value (cdar alst))
            (rest  (cdr  alst)))
        (and (natp index)
             (< index *control-register-names-len*)
             (unsigned-byte-p 64 value)
             (ctri-alistp rest))))))

(define !ctri-from-alist (ctr-alist x86)
  :parents (initialize-x86-state)
  :short "Update control registers as dictated by @('ctr-alist'),
  which is required to be a @('ctri-alistp')."

  :guard (ctri-alistp ctr-alist)
  (cond ((endp ctr-alist) x86)
        (t (let ((x86 (!ctri (caar ctr-alist) (cdar ctr-alist) x86)))
             (!ctri-from-alist (cdr ctr-alist) x86))))
  ///

  (defthm x86p-!ctri-from-alist
    (implies (and (ctri-alistp ctr-alist)
                  (x86p x86))
             (x86p (!ctri-from-alist ctr-alist x86)))))

(define msri-alistp (alst)
  :parents (initialize-x86-state)
  :short "Recognizer for pairs of model-specific register indices and
  values"
  :long "<p>Note that the register values are required to be @('n64p') </p>"
  :enabled t

  (if (atom alst)
      (equal alst nil)
    (if (atom (car alst))
        nil
      (let ((index (caar alst))
            (value (cdar alst))
            (rest  (cdr  alst)))
        (and (natp index)
             (< index *model-specific-register-names-len*)
             (unsigned-byte-p 64 value)
             (msri-alistp rest))))))

(define !msri-from-alist (msr-alist x86)

  :parents (initialize-x86-state)
  :short "Update model-specific registers as dictated by
  @('msr-alist'), which is required to be a @('msri-alistp')."

  :guard (msri-alistp msr-alist)

  (cond ((endp msr-alist) x86)
        (t (let ((x86 (!msri (caar msr-alist) (cdar msr-alist) x86)))
             (!msri-from-alist (cdr msr-alist) x86))))

  ///

  (defthm x86p-!msri-from-alist
    (implies (and (msri-alistp alist)
                  (x86p x86))
             (x86p (!msri-from-alist alist x86)))))

;; ======================================================================

(define init-x86-state
  (status start-addr halt-addr gprs ctrs msrs flags mem x86)

  :parents (initialize-x86-state)
  :short "A convenient function to populate the x86 state's
  instruction pointer, registers, and memory"
  :guard (and (canonical-address-p start-addr)
              (canonical-address-p halt-addr)
              (rgfi-alistp gprs)
              (ctri-alistp ctrs)
              (msri-alistp msrs)
              (n64p flags)
              (n64p-byte-alistp mem))

  :prepwork ((local (include-book "arithmetic-5/top" :dir :system)))
  :returns (mv flg
               (x86 x86p :hyp :guard))

  (b* ((x86 (!ms status x86))
       (x86 (!fault status x86))
       (x86 (!rip start-addr x86))
       ((mv flg0 x86)
        (load-program-into-memory mem x86))
       ((when flg0)
        (mv (cons 'load-program-into-memory flg0) x86))
       ((mv flg1 x86)
        (wm08 halt-addr #xF4 x86)) ;; "Fake" halt address
       ((when flg1)
        (mv (cons 'halt-addr flg0) x86))
       (x86 (!rgfi-from-alist gprs x86)) ;; General-Purpose Registers
       (x86 (!msri-from-alist msrs x86)) ;; Model-Specific Registers
       (x86 (!ctri-from-alist ctrs x86)) ;; Control Registers
       (x86 (!rflags                     ;; Initial Flags
             (n32 flags) x86)))
      (mv nil x86)))

;; ======================================================================
