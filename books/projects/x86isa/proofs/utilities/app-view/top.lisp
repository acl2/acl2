;; AUTHOR:
;; Shilpi Goel <shigoel@cs.utexas.edu>

(in-package "X86ISA")

;; This is the top-level book to include when reasoning about code in
;; the application-level view.

(include-book "environment-utils" :ttags :all)
(include-book "user-level-memory-utils" :ttags :all)

(defsection app-view-proof-utilities
  :parents (proof-utilities debugging-code-proofs)

  :short "General-purpose code-proof libraries to include in the
  application-level view"

  :long "<p>When reasoning about an application program in the
  application-level view of the x86 ISA model, include the book
  @('x86isa/proofs/utilities/app-view/top') to make use of some
  standard rules you would need to control the symbolic simulation of
  the program.</p>

  <p>If unwinding the @('(x86-run ... x86)') expression during your
  proof attempt does not result in a 'clean' expression (i.e., one
  entirely in terms of updates made to the initial state as opposed to
  in terms of @(see x86-fetch-decode-execute) or @(see x86-run)), then
  there is a good chance that you're missing some preconditions, or
  that the existing rules are not good enough.  In any case, it can
  help to @(see acl2::monitor) the existing rules to figure out what's
  wrong.  Feel free to send on suggestions for new rules or improving
  existing ones!</p>

  <p>You can monitor the following rules, depending on the kind of
  subgoals you see, to get some clues.  You can find definitions of
  these rules in @(see
  unwind-x86-interpreter-in-app-view).</p>

  <ul>

    <li>When the subgoal has calls of @('x86-run'): <br/>
        Monitor @('x86-run-opener-not-ms-not-zp-n').
   </li>

    <li>When the subgoal has calls of @(see x86-fetch-decode-execute): <br/>
        Monitor @('x86-fetch-decode-execute-opener').
   </li>

   <li>When monitoring @('x86-fetch-decode-execute-opener') tells you
    that a hypothesis involving @(see get-prefixes) was not rewritten
    to @('t'): <br/>
    Monitor
    @('get-prefixes-opener-lemma-no-prefix-byte'). <br/>
    Note that if the instruction under consideration has prefix
    bytes, you should monitor one of these rules instead: <br/>
    @('get-prefixes-opener-lemma-group-1-prefix') <br/>
    @('get-prefixes-opener-lemma-group-2-prefix') <br/>
    @('get-prefixes-opener-lemma-group-3-prefix') <br/>
    @('get-prefixes-opener-lemma-group-4-prefix').
  </li>


    <li>When monitoring other rules above indicates that an
    instruction is not being fetched successfully using @(see rb):
    <br/>
    Monitor @('one-read-with-rb-from-program-at').
    </li>

   <li>When monitoring other rules above indicates that ACL2 can't
    resolve that the program remained unchanged (@(see
    program-at)) after a write operation @(see wb) occurred: <br/>
    Monitor @('program-at-wb-disjoint'). <br/>
    <br/>
    An instance of where monitoring this rule might be helpful is when
    the @('program-at') hypothesis of @('rb-in-terms-of-nth-and-pos')
    is not being relieved.
   </li>

   <li>When reasoning about disjointness/overlap of memory regions: <br/>
   @('rb-wb-disjoint') <br/>
   @('rb-wb-subset') <br/>
   @('rb-wb-equal') <br/>
   @('separate-smaller-regions') <br/>
   @('separate-contiguous-regions')
   </li>

  </ul>

")

(defsection unwind-x86-interpreter-in-app-view
  :parents (app-view-proof-utilities)

  ;; A benefit of defining this topic (apart from letting the user
  ;; view the definitions of the rules) is that if the rule names
  ;; mentioned in the parent topic are changed, the manual build
  ;; process will complain about broken links, and we'll know to
  ;; modify these two doc topics.

  :short "Definitions of rules to monitor in the application-level
  view"

  :long "

 <h3>Rules about @('x86-run') and @('x86-fetch-decode-execute')</h3>

 @(def x86-run-opener-not-ms-not-zp-n)

 @(def x86-fetch-decode-execute-opener)

 <h3>Rules about @('get-prefixes')</h3>

 @(def get-prefixes-opener-lemma-no-prefix-byte)

 @(def get-prefixes-opener-lemma-group-1-prefix)

 @(def get-prefixes-opener-lemma-group-2-prefix)

 @(def get-prefixes-opener-lemma-group-3-prefix)

 @(def get-prefixes-opener-lemma-group-4-prefix)

 <h3>Rules related to instruction fetches and program location</h3>

 @(def one-read-with-rb-from-program-at)

 @(def program-at-wb-disjoint)

 <h3>Rules related to disjointness/overlap of memory regions</h3>

 @(def rb-wb-disjoint)
 @(def rb-wb-subset)
 @(def rb-wb-equal)
 @(def separate-smaller-regions)
 @(def separate-contiguous-regions)
 "
  )
