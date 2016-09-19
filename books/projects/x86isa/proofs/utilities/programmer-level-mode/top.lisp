;; AUTHOR:
;; Shilpi Goel <shigoel@cs.utexas.edu>

(in-package "X86ISA")

;; This is the top-level book to include when reasoning about code in
;; the programmer-level mode.

(include-book "environment-utils" :ttags :all)
(include-book "programmer-level-memory-utils" :ttags :all)

(defsection programmer-level-mode-proof-utilities
  :parents (proof-utilities x86-programs-proof-debugging)

  :short "General-purpose code-proof libraries to include in the programmer-level mode"

  :long "<p>When reasoning about an application program in the
  programmer-level mode of operation of the x86 ISA model, include the
  book @('x86isa/proofs/utilities/programmer-level-mode/top') to make
  use of some standard rules you would need to control the symbolic
  simulation of the program.</p>

  <p>If unwinding the @('(x86-run ... x86)') expression during your
  proof attempt does not result in a 'clean' expression (i.e., one
  entirely in terms of updates made to the initial state as opposed to
  in terms of @(see x86-fetch-decode-execute) or @(see x86-run)), then
  there is a good chance that you're missing some preconditions.  You
  can @(see acl2::monitor) the following rules to get some clues:</p>

  <ul>

    <li>@(see x86-run-opener-not-ms-not-zp-n): Useful when you see
    un-expanded calls of @(see x86-run).</li>

    <li>@(see x86-fetch-decode-execute-opener): Useful when you see
    un-expanded calls of @(see x86-fetch-decode-execute).</li>

    <li>@(see get-prefixes-opener-lemma-no-prefix-byte): Useful when
    monitoring @('x86-fetch-decode-execute-opener') tells you that a
    hypothesis involving @(see get-prefixes) was not rewritten to
    @('t').  Note that if the instruction under consideration has
    prefix bytes, you should monitor one of these rules instead: @(see
    get-prefixes-opener-lemma-group-1-prefix), @(see
    get-prefixes-opener-lemma-group-2-prefix), @(see
    get-prefixes-opener-lemma-group-3-prefix), or @(see
    get-prefixes-opener-lemma-group-4-prefix).</li>

    <li>@(see rb-in-terms-of-nth-and-pos): Useful when you believe
    that ACL2 is not able to fetch/read an instruction
    successfully.</li>

    <li>@(see program-at-wb-disjoint): Useful if you believe that ACL2
    can't resolve that the program remained unchanged (@(see
    program-at)) after a write operation @(see wb) occurred.  An
    instance of where monitoring this rule might be helpful is when
    the @('program-at') hypothesis of @('rb-in-terms-of-nth-and-pos')
    is not being relieved.</li>

    <li>@(see member-p-canonical-address-listp): Useful if you believe
    that the canonical nature of a linear address should be inferable
    from the canonical nature of a list of addresses, of which that
    address is a member.  An instance of where monitoring this rule
    might be helpful is when the @('member-p') hypothesis of
    @('rb-in-terms-of-nth-and-pos') is not being relieved.</li>

  </ul>

")
