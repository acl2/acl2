; X86ISA Library

; Note: The license below is based on the template at:
; http://opensource.org/licenses/BSD-3-Clause

; Copyright (C) 2015, Regents of the University of Texas
; All rights reserved.

; Redistribution and use in source and binary forms, with or without
; modification, are permitted provided that the following conditions are
; met:

; o Redistributions of source code must retain the above copyright
;   notice, this list of conditions and the following disclaimer.

; o Redistributions in binary form must reproduce the above copyright
;   notice, this list of conditions and the following disclaimer in the
;   documentation and/or other materials provided with the distribution.

; o Neither the name of the copyright holders nor the names of its
;   contributors may be used to endorse or promote products derived
;   from this software without specific prior written permission.

; THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
; "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
; LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
; A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
; HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
; SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
; LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
; DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
; THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
; (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
; OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.

; Original Author(s):
; Shilpi Goel         <shigoel@cs.utexas.edu>

(in-package "X86ISA")
(include-book "marking-view-utils")

(local (include-book "gl-lemmas"))
(local (include-book "centaur/bitops/ihs-extensions" :dir :system))
(local (include-book "centaur/bitops/signed-byte-p" :dir :system))
(local (include-book "arithmetic/top-with-meta" :dir :system))

(local (in-theory (e/d* () (signed-byte-p unsigned-byte-p))))

;; ======================================================================

(defsection system-level-marking-view-proof-utilities
  :parents (proof-utilities debugging-code-proofs)

  :short "General-purpose code-proof libraries to include in the
  system-level marking view (with A/D flag updates on)"

  :long "<p>When reasoning about an supervisor-mode program in the
  system-level <i>marking</i> view of the x86 ISA model, include the
  book @('x86isa/proofs/utilities/sys-view/marking-view-top') to make
  use of some standard rules you would need to control the symbolic
  simulation of the program.</p>

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
  these rules in @(see unwind-x86-interpreter-in-marking-view).</p>

  <ul>

    <li>When the subgoal has calls of @('x86-run'): <br/>
        Monitor @('x86-run-opener-not-ms-not-zp-n').
   </li>

    <li>When the subgoal has calls of @(see x86-fetch-decode-execute): <br/>
        Monitor @('x86-fetch-decode-execute-opener-in-marking-view').
   </li>

   <li>When monitoring
    @('x86-fetch-decode-execute-opener-in-marking-view') tells you
    that a hypothesis involving @(see get-prefixes-alt) was not
    rewritten to @('t'): <br/>
    Monitor
    @('get-prefixes-alt-opener-lemma-no-prefix-byte'). <br/>
    Note that if the instruction under consideration has prefix
    bytes, you should monitor one of these rules instead: <br/>
    @('get-prefixes-alt-opener-lemma-group-1-prefix-in-marking-view') <br/>
    @('get-prefixes-alt-opener-lemma-group-2-prefix-in-marking-view') <br/>
    @('get-prefixes-alt-opener-lemma-group-3-prefix-in-marking-view') <br/>
    @('get-prefixes-alt-opener-lemma-group-4-prefix-in-marking-view').<br/>
    <br/>
    Other useful rules involving @('get-prefixes-alt') are:
   @('get-prefixes-alt-and-wb-in-system-level-marking-view-disjoint-from-paging-structures') <br/>
   and <br/>
   @('mv-nth-3-get-prefixes-alt-no-prefix-byte').
  </li>

    <li>When monitoring other rules above indicates that an
    instruction is not being fetched successfully using @(see rb-alt):
    <br/>
    Monitor @('one-read-with-rb-alt-from-program-at-alt-in-marking-view).
    </li>

    <li>When monitoring other rules above indicates that ACL2 can't
    resolve that the program remained unchanged (@(see
    program-at-alt)) after a write operation @(see wb) occurred: <br/>
    Monitor @('program-at-alt-wb-disjoint-in-sys-view'). <br/>
    <br/>
    An instance of where monitoring this rule might be helpful is when
    the @('program-at') hypothesis of
    @('one-read-with-rb-alt-from-program-at-alt-in-marking-view) is not
    being relieved.
   </li>

   <li>When inferring the canonical nature of a linear address:<br/>
    Monitor @('member-p-canonical-address-listp'). <br/>

    <br/> This is useful if you believe that the canonical nature of a
    linear address should be inferable from the canonical nature of a
    list of addresses, of which that address is a member.  An instance
    of where monitoring this rule might be helpful is when the
    @('member-p') hypothesis of
    @('one-read-with-rb-alt-from-program-at-alt-in-marking-view') is
    not being relieved. </li>

   <li>When reasoning about disjointness/overlap of memory regions:<br/>
   Monitor one of these rules: <br/>
   @('rb-alt-wb-equal-in-sys-view') <br/>
   @('rb-alt-wb-disjoint-in-sys-view') <br/>
   @('rb-alt-and-wb-to-paging-structures-disjoint') <br/>
   @('rb-wb-disjoint-in-sys-view') <br/>
   @('rb-wb-equal-in-sys-view') <br/>
   @('all-xlation-governing-entries-paddrs-and-mv-nth-1-wb-disjoint') <br/>
   @('la-to-pas-values-and-mv-nth-1-wb-disjoint-from-xlation-gov-addrs').<br/>
   <br/>
   Note that @(see rb) is rewritten to @(see rb-alt) when the read is
   being done from a program address.
  </li>

 </ul>

 <p>When symbolically simulating supervisor-mode programs, you might
 also want to do the following, which replaces ACL2's default ancestor
 check with something simpler:</p>

 <code>
 (local (include-book \"tools/trivial-ancestors-check\" :dir :system))
 (local (acl2::use-trivial-ancestors-check))
 </code>

")

(defsection unwind-x86-interpreter-in-marking-view
  :parents (system-level-marking-view-proof-utilities)

  ;; A benefit of defining this topic (apart from letting the user
  ;; view the definitions of the rules) is that if the rule names
  ;; mentioned in the parent topic are changed, the manual build
  ;; process will complain about broken links, and we'll know to
  ;; modify these two doc topics.

  :short "Definitions of rules to monitor in the system-level marking view"

  :long "

 <h3>Rules about @('x86-run') and @('x86-fetch-decode-execute')</h3>

 @(def x86-run-opener-not-ms-not-zp-n)

 @(def x86-fetch-decode-execute-opener-in-marking-view)

 <h3>Rules about @('get-prefixes-alt')</h3>

 @(def get-prefixes-alt-opener-lemma-no-prefix-byte)

 @(def get-prefixes-alt-opener-lemma-group-1-prefix-in-marking-view)

 @(def get-prefixes-alt-opener-lemma-group-2-prefix-in-marking-view)

 @(def get-prefixes-alt-opener-lemma-group-3-prefix-in-marking-view)

 @(def get-prefixes-alt-opener-lemma-group-4-prefix-in-marking-view)

 @(def get-prefixes-alt-and-wb-in-system-level-marking-view-disjoint-from-paging-structures)

 @(def mv-nth-3-get-prefixes-alt-no-prefix-byte)

 <h3>Rules related to instruction fetches and program location</h3>

 @(def one-read-with-rb-alt-from-program-at-alt-in-marking-view)

 @(def program-at-alt-wb-disjoint-in-sys-view)

 <h3>Rules related to canonical linear addresses</h3>

 @(def member-p-canonical-address-listp)

 <h3>Rules related to disjointness/overlap of memory regions</h3>

 @(def rb-alt-wb-equal-in-sys-view)
 @(def rb-alt-wb-disjoint-in-sys-view)
 @(def rb-alt-and-wb-to-paging-structures-disjoint)
 @(def rb-wb-disjoint-in-sys-view)
 @(def rb-wb-equal-in-sys-view)
 @(def all-xlation-governing-entries-paddrs-and-mv-nth-1-wb-disjoint)
 @(def la-to-pas-values-and-mv-nth-1-wb-disjoint-from-xlation-gov-addrs).
 "
  )

(local (xdoc::set-default-parents system-level-marking-view-proof-utilities))

;; ======================================================================

;; (acl2::why x86-run-opener-not-ms-not-zp-n)
;; (acl2::why x86-fetch-decode-execute-opener-in-marking-view)
;; (acl2::why get-prefixes-alt-opener-lemma-no-prefix-byte)
;; (acl2::why get-prefixes-alt-and-wb-in-system-level-marking-view-disjoint-from-paging-structures)
;; (acl2::why la-to-pas-values-and-mv-nth-1-wb-disjoint-from-xlation-gov-addrs)
;; (acl2::why rb-alt-wb-disjoint-in-sys-view)
;; (acl2::why rb-alt-wb-equal-in-sys-view)
;; (acl2::why mv-nth-1-rb-after-mv-nth-2-rb-alt)
;; (acl2::why all-xlation-governing-entries-paddrs-and-mv-nth-1-wb-disjoint)
;; (acl2::why la-to-pas-values-and-mv-nth-1-wb-disjoint-from-xlation-gov-addrs)
;; (acl2::why mv-nth-1-rb-after-mv-nth-3-get-prefixes-alt-no-prefix-byte)
;; (acl2::why mv-nth-3-get-prefixes-alt-no-prefix-byte)
;; (acl2::why mv-nth-2-rb-in-system-level-marking-view)
;; (acl2::why combine-mv-nth-2-las-to-pas-same-r-x)
;; (acl2::why mv-nth-1-rb-after-mv-nth-2-las-to-pas)
;; (acl2::why mv-nth-1-rb-after-mv-nth-2-rb)
;; (acl2::why get-prefixes-alt-and-wb-to-paging-structures)
;; (acl2::why rb-wb-disjoint-in-sys-view)
;; (acl2::why x86-fetch-decode-execute-opener-in-marking-view)
;; (acl2::why mv-nth-3-get-prefixes-alt-no-prefix-byte)
;; (acl2::why rb-alt-and-wb-to-paging-structures-disjoint)

;; ======================================================================

;; Lemmas about direct-map-p:

(defun-nx direct-map-p (count addr r-x x86)
  (equal
   (mv-nth 1 (las-to-pas count addr r-x x86))
   (addr-range count addr)))

(defthm xlate-equiv-memory-and-direct-map-p
  (implies (xlate-equiv-memory x86-1 x86-2)
           (equal (direct-map-p count addr r-x x86-1)
                  (direct-map-p count addr r-x x86-2)))
  :rule-classes :congruence)

(defthm direct-map-p-and-wb-disjoint-from-xlation-governing-addrs
  (implies
   (and (disjoint-p
         (mv-nth 1 (las-to-pas n-w write-addr :w (double-rewrite x86)))
         (all-xlation-governing-entries-paddrs
          count addr (double-rewrite x86)))
        (64-bit-modep (double-rewrite x86)))
   (equal (direct-map-p count addr r-x (mv-nth 1 (wb n-w write-addr w val x86)))
          (direct-map-p count addr r-x (double-rewrite x86))))
  :hints (("Goal" :in-theory (e/d* () (force (force))))))

(in-theory (e/d* () (direct-map-p)))

;; ======================================================================

(define program-at-alt ((prog-addr canonical-address-p)
                        (bytes     byte-listp)
                        x86)

  :parents (system-level-marking-view-proof-utilities)
  :non-executable t
  :prepwork
  (
   ;; Note that unlike rb-alt and get-prefixes-alt, we need to use
   ;; disjoint-p$ for program-at-alt instead of disjoint-p.
   (local (in-theory (e/d (disjoint-p$) ()))))

  (if (and (marking-view x86)
           (64-bit-modep x86)
           (not (app-view x86))
           (canonical-address-p prog-addr)
           (canonical-address-p (+ -1 (len bytes) prog-addr))
           ;; (not (mv-nth 0 (las-to-pas (len bytes) prog-addr :x x86)))
           (disjoint-p$ (mv-nth 1 (las-to-pas (len bytes) prog-addr :x x86))
                        (open-qword-paddr-list
                         (gather-all-paging-structure-qword-addresses x86))))

      (program-at prog-addr bytes x86)

    nil)

  ///

  (local (in-theory (e/d* () (program-at-alt))))

  (defthmd program-at-alt-implies-program-addresses-properties
    (implies (program-at-alt prog-addr bytes (double-rewrite x86))
             (and (marking-view x86)
                  (not (app-view x86))
                  (canonical-address-p prog-addr)
                  (canonical-address-p (+ -1 (len bytes) prog-addr))
                  (disjoint-p$
                   (mv-nth 1 (las-to-pas (len bytes) prog-addr :x x86))
                   (open-qword-paddr-list
                    (gather-all-paging-structure-qword-addresses x86)))
                  (program-at prog-addr bytes x86)))
    :hints (("Goal" :in-theory (e/d* (program-at-alt)
                                     ()))))

  (defthm rewrite-program-at-to-program-at-alt
    (implies (forced-and
              (disjoint-p$
               (mv-nth 1 (las-to-pas (len bytes) prog-addr :x (double-rewrite x86)))
               (open-qword-paddr-list
                (gather-all-paging-structure-qword-addresses (double-rewrite x86))))
              ;; (not (mv-nth 0 (las-to-pas (len bytes) prog-addr :x (double-rewrite x86))))
              (canonical-address-p prog-addr)
              (canonical-address-p (+ -1 (len bytes) prog-addr))
              (marking-view x86)
              (not (app-view x86))
              (64-bit-modep (double-rewrite x86)))
             (equal (program-at prog-addr bytes x86)
                    (program-at-alt prog-addr bytes (double-rewrite x86))))
    :hints (("Goal" :in-theory (e/d* (program-at-alt) ()))))

  (defthm program-at-alt-and-xlate-equiv-memory-cong
    (implies (xlate-equiv-memory x86-1 x86-2)
             (equal (program-at-alt prog-addr bytes x86-1)
                    (program-at-alt prog-addr bytes x86-2)))
    :hints (("Goal"
             :do-not-induct t
             :use ((:instance mv-nth-1-rb-and-xlate-equiv-memory-disjoint-from-paging-structures
                              (n (len bytes))
                              (lin-addr prog-addr)
                              (r-w-x :x)))
             :in-theory (e/d* (program-at-alt
                               program-at)
                              (rewrite-program-at-to-program-at-alt
                               mv-nth-1-rb-and-xlate-equiv-memory-disjoint-from-paging-structures
                               force (force)))))
    :rule-classes :congruence)

  (defthm program-at-alt-wb-disjoint-in-sys-view
    (implies
     (and
      (disjoint-p$
       (mv-nth 1 (las-to-pas n-w write-addr :w (double-rewrite x86)))
       (mv-nth 1 (las-to-pas (len bytes) prog-addr :x (double-rewrite x86))))
      (disjoint-p$
       (mv-nth 1 (las-to-pas n-w write-addr :w (double-rewrite x86)))
       (open-qword-paddr-list
        (gather-all-paging-structure-qword-addresses (double-rewrite x86))))
      (canonical-address-p (+ -1 n-w write-addr))
      (canonical-address-p write-addr))
     (equal (program-at-alt prog-addr bytes (mv-nth 1 (wb n-w write-addr w value x86)))
            (program-at-alt prog-addr bytes (double-rewrite x86))))
    :hints
    (("Goal"
      :do-not-induct t
      :use ((:instance program-at-wb-disjoint-in-sys-view))
      :in-theory
      (e/d
       (program-at-alt
        disjoint-p-commutative)
       (rewrite-program-at-to-program-at-alt
        program-at-wb-disjoint-in-sys-view
        rb-wb-disjoint-in-sys-view
        disjointness-of-all-xlation-governing-entries-paddrs-from-all-xlation-governing-entries-paddrs-subset-p
        mv-nth-1-las-to-pas-subset-p-disjoint-from-other-p-addrs
        rb wb)))))

  (make-event
   (generate-read-fn-over-xw-thms
    (remove-elements-from-list
     '(:mem :rflags :ctr :seg-visible
            :seg-hidden-base :seg-hidden-limit :seg-hidden-attr
            :msr :fault :app-view :marking-view)
     *x86-field-names-as-keywords*)
    'program-at-alt
    (acl2::formals 'program-at (w state))
    ;; :hyps '(not (app-view x86))
    :prepwork '((local (in-theory (e/d (program-at-alt)
                                       (rewrite-program-at-to-program-at-alt)))))
    :double-rewrite? t))

  (defthm program-at-alt-xw-rflags
    (implies (and (equal (rflagsBits->ac value)
                         (rflagsBits->ac (xr :rflags 0 (double-rewrite x86))))
                  (not (app-view x86))
                  (x86p x86))
             (equal (program-at-alt l-addrs bytes (xw :rflags 0 value x86))
                    (program-at-alt l-addrs bytes (double-rewrite x86))))
    :hints (("Goal" :in-theory (e/d* (program-at-alt)
                                     (rewrite-program-at-to-program-at-alt)))))

  (defthm program-at-alt-after-mv-nth-2-rb
    (implies
     (not (mv-nth 0 (las-to-pas n lin-addr r-x (double-rewrite x86))))
     (equal (program-at-alt prog-addr bytes
                            (mv-nth 2 (rb n lin-addr r-x x86)))
            (program-at-alt prog-addr bytes (double-rewrite x86))))
    :hints (("Goal"
             :do-not-induct t
             :in-theory (e/d* (program-at-alt
                               program-at)
                              (rewrite-program-at-to-program-at-alt
                               force (force)))))))

;; ======================================================================

(define rb-alt ((n    natp                "Number of bytes to be read")
                (addr integerp            "First linear address")
                (r-x :type (member :r :x) "Type of memory access")
                (x86))

  :parents (system-level-marking-view-proof-utilities)

  :long "<p>rb-alt is defined basically to read the program bytes from
 the memory. I don't intend to use it to read paging data
 structures.</p>"

  :non-executable t
  (if (and (marking-view x86)
           (64-bit-modep x86)
           (not (app-view x86))
           (canonical-address-p addr)
           (canonical-address-p (+ -1 n addr))
           (not (mv-nth 0 (las-to-pas n addr r-x x86)))
           (disjoint-p (mv-nth 1 (las-to-pas n addr r-x x86))
                       (open-qword-paddr-list
                        (gather-all-paging-structure-qword-addresses x86))))

      (rb n addr r-x x86)

    (mv nil 0 x86))

  ///

  (defthm integerp-of-mv-nth-1-rb-alt
    (integerp (mv-nth 1 (rb-alt n addr r-x x86)))
    :hints (("Goal" :in-theory (e/d* () (force (force)))))
    :rule-classes :type-prescription)

  (defthm natp-of-mv-nth-1-rb-alt
    (implies (x86p x86)
             (natp (mv-nth 1 (rb-alt n addr r-x x86))))
    :hints (("Goal" :in-theory (e/d* () (force (force)))))
    :rule-classes :type-prescription)

  (defthm x86p-of-mv-nth-2-rb-alt
    (implies (x86p x86)
             (x86p (mv-nth 2 (rb-alt n addr r-x x86)))))

  (defthm rb-alt-no-reads-when-zp-n
    (equal (mv-nth 1 (rb-alt 0 addr r-x x86)) 0)
    :hints (("Goal" :in-theory (e/d* () (force (force))))))

  (make-event
   (generate-xr-over-write-thms
    (remove-elements-from-list
     '(:mem :fault)
     *x86-field-names-as-keywords*)
    'rb-alt
    (acl2::formals 'rb-alt (w state))
    :output-index 2
    :prepwork '((local (in-theory (e/d () (force (force))))))))

  (defthm xr-fault-rb-alt-state-in-sys-view
    (equal (xr :fault index (mv-nth 2 (rb-alt n lin-addr r-x x86)))
           (xr :fault index x86))
    :hints (("Goal" :in-theory (e/d* (rb-alt
                                      las-to-pas)
                                     (force (force))))))

  (defthm mv-nth-0-rb-alt-is-nil
    (equal (mv-nth 0 (rb-alt n addr r-x x86)) nil)
    :hints (("Goal"
             :use ((:instance mv-nth-0-rb-and-mv-nth-0-las-to-pas-in-sys-view))
             :in-theory (e/d* ()
                              (mv-nth-0-rb-and-mv-nth-0-las-to-pas-in-sys-view
                               force (force))))))

  (make-event
   (generate-read-fn-over-xw-thms
    (remove-elements-from-list
     '(:mem :rflags :ctr :seg-visible
            :seg-hidden-base :seg-hidden-limit :seg-hidden-attr
            :msr :fault :app-view :marking-view)
     *x86-field-names-as-keywords*)
    'rb-alt
    (acl2::formals 'rb-alt (w state))
    :output-index 0
    :double-rewrite? t))

  (make-event
   (generate-read-fn-over-xw-thms
    (remove-elements-from-list
     '(:mem :rflags :ctr :seg-visible
            :seg-hidden-base :seg-hidden-limit :seg-hidden-attr
            :msr :fault :app-view :marking-view)
     *x86-field-names-as-keywords*)
    'rb-alt
    (acl2::formals 'rb-alt (w state))
    :output-index 1
    :double-rewrite? t))

  (defthm rb-alt-xw-rflags-not-ac-values-in-sys-view
    (implies (equal (rflagsBits->ac (double-rewrite value))
                    (rflagsBits->ac (rflags x86)))
             (and (equal (mv-nth 0 (rb-alt n addr r-x (xw :rflags 0 value x86)))
                         (mv-nth 0 (rb-alt n addr r-x x86)))
                  (equal (mv-nth 1 (rb-alt n addr r-x (xw :rflags 0 value x86)))
                         (mv-nth 1 (rb-alt n addr r-x x86)))))
    :hints (("Goal" :in-theory (e/d* () (force (force))))))

  (make-event
   (generate-write-fn-over-xw-thms
    (remove-elements-from-list
     '(:mem :rflags :ctr :seg-visible
            :seg-hidden-base :seg-hidden-limit :seg-hidden-attr
            :msr :fault :app-view :marking-view)
     *x86-field-names-as-keywords*)
    'rb-alt
    (acl2::formals 'rb-alt (w state))
    :output-index 2
    :prepwork '((local (in-theory (e/d* () (force (force))))))))

  (defthm rb-alt-xw-rflags-not-ac-state-in-sys-view
    (implies (equal (rflagsBits->ac (double-rewrite value))
                    (rflagsBits->ac (rflags x86)))
             (equal (mv-nth 2 (rb-alt n addr r-x (xw :rflags 0 value x86)))
                    (xw :rflags 0 value (mv-nth 2 (rb-alt n addr r-x x86)))))
    :hints (("Goal" :in-theory (e/d* () (force (force))))))

  (defthm rb-alt-values-and-xw-rflags-in-sys-view
    (implies (and (equal (rflagsBits->ac (double-rewrite value))
                         (rflagsBits->ac (rflags x86)))
                  (x86p x86))
             (and (equal (mv-nth 0 (rb-alt n addrs r-x (xw :rflags 0 value x86)))
                         (mv-nth 0 (rb-alt n addrs r-x (double-rewrite x86))))
                  (equal (mv-nth 1 (rb-alt n addrs r-x (xw :rflags 0 value x86)))
                         (mv-nth 1 (rb-alt n addrs r-x (double-rewrite x86))))))
    :hints (("Goal" :do-not-induct t
             :in-theory (e/d* () (force (force))))))

  (defthm rb-alt-and-xw-rflags-state-in-sys-view
    (implies (and (equal (rflagsBits->ac (double-rewrite value))
                         (rflagsBits->ac (rflags x86)))
                  (x86p x86))
             (equal (mv-nth 2 (rb-alt n lin-addr r-x (xw :rflags 0 value x86)))
                    (xw :rflags 0 value (mv-nth 2 (rb-alt n lin-addr r-x x86)))))
    :hints (("Goal"
             :do-not-induct t
             :in-theory (e/d* () (force (force))))))

  (defthm xr-rflags-and-mv-nth-2-rb-alt
    (equal (xr :rflags 0 (mv-nth 2 (rb-alt n lin-addr r-x x86)))
           (xr :rflags 0 x86)))

  (defthm alignment-checking-enabled-p-and-mv-nth-2-rb-alt
    (equal (alignment-checking-enabled-p (mv-nth 2 (rb-alt n lin-addr r-x x86)))
           (alignment-checking-enabled-p x86))
    :hints (("Goal" :in-theory (e/d* (alignment-checking-enabled-p) ()))))

  (defthm mv-nth-2-rb-alt-in-system-level-marking-view
    (implies
     (and (not (mv-nth 0 (las-to-pas n lin-addr r-x (double-rewrite x86))))
          (disjoint-p (mv-nth 1 (las-to-pas n lin-addr r-x (double-rewrite x86)))
                      (open-qword-paddr-list
                       (gather-all-paging-structure-qword-addresses (double-rewrite x86))))
          (canonical-address-p lin-addr)
          (canonical-address-p (+ -1 n lin-addr))
          (64-bit-modep (double-rewrite x86))
          (not (app-view x86)))
     (equal (mv-nth 2 (rb-alt n lin-addr r-x x86))
            (mv-nth 2 (las-to-pas n lin-addr r-x (double-rewrite x86)))))
    :hints (("Goal" :do-not-induct t
             :in-theory (e/d* () (force (force))))))

  (local (in-theory (e/d* () (rb-alt))))

  ;; Note that in the lemmas below, we use program-at-alt instead of
  ;; program-at.

  ;; Rewrite rb to rb-alt:

  (defthm rewrite-rb-to-rb-alt
    ;; Note that the hyps here aren't forced --- this is because we
    ;; don't always want rb to rewrite to rb-alt. E.g., when we're
    ;; reading from the paging data structures, we want to reason
    ;; about rb.
    (implies (and
              (disjoint-p
               (mv-nth 1 (las-to-pas n addr r-x (double-rewrite x86)))
               (open-qword-paddr-list
                (gather-all-paging-structure-qword-addresses (double-rewrite x86))))
              (not (mv-nth 0 (las-to-pas n addr r-x (double-rewrite x86))))
              (canonical-address-p addr)
              (canonical-address-p (+ -1 n addr))
              (marking-view x86)
              (not (app-view x86))
              (64-bit-modep (double-rewrite x86)))
             (equal (rb n addr r-x x86)
                    (rb-alt n addr r-x (double-rewrite x86))))
    :hints (("Goal" :in-theory (e/d* (rb-alt) ()))))

  ;; rb-alt and xlate-equiv-memory:

  (defthm mv-nth-0-rb-alt-and-xlate-equiv-memory-cong
    (implies (xlate-equiv-memory x86-1 x86-2)
             (equal (mv-nth 0 (rb-alt n addr r-x x86-1))
                    (mv-nth 0 (rb-alt n addr r-x x86-2))))
    :hints (("Goal" :in-theory (e/d* (rb-alt) (rewrite-rb-to-rb-alt force (force)))))
    :rule-classes :congruence)

  (defthm mv-nth-1-rb-alt-and-xlate-equiv-memory-cong
    (implies (xlate-equiv-memory x86-1 x86-2)
             (equal (mv-nth 1 (rb-alt n lin-addr r-w-x x86-1))
                    (mv-nth 1 (rb-alt n lin-addr r-w-x x86-2))))
    :hints (("Goal"
             :do-not-induct t
             :use ((:instance mv-nth-1-rb-and-xlate-equiv-memory-disjoint-from-paging-structures))
             :in-theory (e/d* (rb-alt)
                              (mv-nth-1-rb-and-xlate-equiv-memory-disjoint-from-paging-structures
                               rewrite-rb-to-rb-alt
                               force (force)))))
    :rule-classes :congruence)

  (defthm mv-nth-2-rb-alt-and-xlate-equiv-memory
    (and (xlate-equiv-memory (mv-nth 2 (rb-alt n addr r-x x86)) (double-rewrite x86))
         (xlate-equiv-memory x86 (mv-nth 2 (rb-alt n addr r-x x86))))
    :hints (("Goal" :in-theory (e/d* (rb-alt) (rewrite-rb-to-rb-alt force (force))))))

  (defthm xlate-equiv-memory-and-two-mv-nth-2-rb-alt-cong
    (implies (xlate-equiv-memory x86-1 x86-2)
             (xlate-equiv-memory (mv-nth 2 (rb-alt n addr r-x x86-1))
                                 (mv-nth 2 (rb-alt n addr r-x x86-2))))
    :hints (("Goal" :in-theory (e/d* (rb-alt) (rewrite-rb-to-rb-alt))
             :use ((:instance xlate-equiv-memory-and-two-mv-nth-2-rb))))
    :rule-classes :congruence)

  (local
   (defthmd establishing-some-canonical-address-properties
     (implies (and ;; <n,lin-addr> is a subset of <(len bytes),prog-addr>.
               (<= prog-addr lin-addr)
               (< (+ n lin-addr) (+ prog-len prog-addr))
               (canonical-address-p prog-addr)
               (canonical-address-p (+ -1 prog-len prog-addr))
               (posp n) (integerp lin-addr))
              (and (canonical-address-p (+ -1 n lin-addr))
                   (canonical-address-p lin-addr)
                   (canonical-address-p (+ -1 n prog-addr))))
     :hints (("Goal" :in-theory (e/d* (canonical-address-p
                                       signed-byte-p)
                                      ())))))

  (defthm many-reads-with-rb-alt-from-program-at-alt-in-marking-view
    (implies (and
              (bind-free
               (find-program-at-info 'prog-addr 'bytes mfc state)
               (prog-addr bytes))
              (program-at-alt prog-addr bytes (double-rewrite x86))
              ;; <n,lin-addr> is a subset of <(len bytes),prog-addr>.
              (<= prog-addr lin-addr)
              (< (+ n lin-addr) (+ (len bytes) prog-addr))
              (integerp lin-addr) (posp n)
              (byte-listp bytes)
              (64-bit-modep (double-rewrite x86))
              (x86p x86))
             (equal (mv-nth 1 (rb-alt n lin-addr :x x86))
                    ;; During symbolic simulation of a program, we'd
                    ;; know the concrete value of "bytes".  Moreover,
                    ;; note that using combine-bytes instead of
                    ;; combine-n-bytes would have been expensive because
                    ;; the former would combine all program bytes
                    ;; whereas the latter only combines n of them.
                    (combine-n-bytes (- lin-addr prog-addr) n bytes)))
    :hints (("Goal"
             :do-not-induct t
             :in-theory (e/d (disjoint-p$)
                             (acl2::mv-nth-cons-meta
                              many-reads-with-rb-from-program-at-in-marking-view
                              rewrite-program-at-to-program-at-alt
                              rewrite-rb-to-rb-alt
                              mv-nth-1-las-to-pas-subset-p
                              combine-n-bytes))
             :use ((:instance establishing-some-canonical-address-properties
                              (prog-len (len bytes)))
                   (:instance mv-nth-1-las-to-pas-subset-p
                              (n-2 n) (addr-2 lin-addr)
                              (n-1 (len bytes)) (addr-1 prog-addr)
                              (r-w-x :x))
                   (:instance many-reads-with-rb-from-program-at-in-marking-view)
                   (:instance rewrite-rb-to-rb-alt (addr lin-addr) (r-x :x))
                   (:instance program-at-alt-implies-program-addresses-properties)
                   (:instance program-at-implies-canonical-addresses)))))

  (local
   (defthmd establishing-some-more-canonical-address-properties
     (implies (and ;; <1,lin-addr> is a subset of <(len bytes),prog-addr>.
               (<= prog-addr lin-addr)
               (< lin-addr (+ prog-len prog-addr))
               (canonical-address-p prog-addr)
               (canonical-address-p (+ -1 prog-len prog-addr))
               (integerp lin-addr))
              (canonical-address-p lin-addr))
     :hints (("Goal" :in-theory (e/d* (canonical-address-p
                                       signed-byte-p)
                                      ())))))

  (local
   (defthmd mv-nth-0-las-to-pas-subset-p-for-1-byte
     (implies
      (and (64-bit-modep x86)
           (<= addr-1 addr-2)
           (< addr-2 (+ n-1 addr-1))
           (not (mv-nth 0 (las-to-pas n-1 addr-1 r-w-x x86)))
           (posp n-1)
           (canonical-address-p addr-2))
      (not (mv-nth 0 (las-to-pas 1   addr-2 r-w-x x86))))
     :hints
     (("Goal" :in-theory (e/d* (las-to-pas
                                subset-p
                                canonical-address-p
                                signed-byte-p)
                               ())))))

  (local
   (defthmd mv-nth-1-las-to-pas-subset-p-for-1-byte
     (implies
      (and (64-bit-modep x86)
           (<= addr-1 addr-2)
           (< addr-2 (+ n-1 addr-1))
           (not (mv-nth 0 (las-to-pas n-1 addr-1 r-w-x x86)))
           (posp n-1))
      (subset-p (mv-nth 1 (las-to-pas 1   addr-2 r-w-x x86))
                (mv-nth 1 (las-to-pas n-1 addr-1 r-w-x x86))))
     :hints
     (("Goal"
       :in-theory (e/d* (las-to-pas subset-p)
                        (mv-nth-1-las-to-pas-subset-p))))))

  (defthm one-read-with-rb-alt-from-program-at-alt-in-marking-view
    ;; Even though we have
    ;; many-reads-with-rb-alt-from-program-at-alt-in-marking-view, I like having
    ;; this lemma around because it has a weaker hyp of
    ;; (< lin-addr (+ (len bytes) prog-addr))
    ;; instead of
    ;; (< (+ 1 lin-addr) (+ (len bytes) prog-addr)).
    (implies (and
              (bind-free
               (find-program-at-info 'prog-addr 'bytes mfc state)
               (prog-addr bytes))
              (program-at-alt prog-addr bytes (double-rewrite x86))
              ;; <1,lin-addr> is a subset of <(len bytes),prog-addr>.
              (<= prog-addr lin-addr)
              (< lin-addr (+ (len bytes) prog-addr))
              (integerp lin-addr) (byte-listp bytes)
              (64-bit-modep (double-rewrite x86))
              (x86p x86))
             (equal (mv-nth 1 (rb-alt 1 lin-addr :x x86))
                    (nth (- lin-addr prog-addr) bytes)))
    :hints (("Goal"
             :do-not-induct t
             :in-theory (e/d (disjoint-p$)
                             (acl2::mv-nth-cons-meta
                              many-reads-with-rb-from-program-at-in-marking-view
                              one-read-with-rb-from-program-at-in-marking-view
                              many-reads-with-rb-alt-from-program-at-alt-in-marking-view
                              rewrite-program-at-to-program-at-alt
                              rewrite-rb-to-rb-alt
                              mv-nth-1-las-to-pas-subset-p
                              combine-n-bytes
                              program-at-implies-error-free-address-translation))
             :use ((:instance program-at-implies-error-free-address-translation)
                   (:instance rewrite-rb-to-rb-alt (n 1) (addr lin-addr) (r-x :x))
                   (:instance program-at-alt-implies-program-addresses-properties)
                   (:instance establishing-some-more-canonical-address-properties
                              (prog-len (len bytes)))
                   (:instance one-read-with-rb-from-program-at-in-marking-view)
                   (:instance mv-nth-1-las-to-pas-subset-p-for-1-byte
                              (addr-2 lin-addr)
                              (n-1 (len bytes)) (addr-1 prog-addr)
                              (r-w-x :x))
                   (:instance mv-nth-0-las-to-pas-subset-p-for-1-byte
                              (addr-2 lin-addr)
                              (n-1 (len bytes)) (addr-1 prog-addr)
                              (r-w-x :x))))))

  (defthmd rb-alt-wb-equal-in-sys-view
    (implies (and (equal
                   ;; The physical addresses pertaining to the read
                   ;; operation are equal to those pertaining to the
                   ;; write operation.
                   (mv-nth 1 (las-to-pas n lin-addr r-w-x (double-rewrite x86)))
                   (mv-nth 1 (las-to-pas n-w write-addr :w (double-rewrite x86))))
                  ;; The following should be directly present as a
                  ;; hypothesis of the effects theorem for programs.
                  ;; That's why it's in terms of disjoint-p$ instead
                  ;; of disjoint-p.
                  (disjoint-p$
                   ;; The physical addresses pertaining to the write are
                   ;; disjoint from the xlation-governing-entries-paddrs
                   ;; pertaining to the read.
                   (mv-nth 1 (las-to-pas n-w write-addr :w (double-rewrite x86)))
                   (open-qword-paddr-list (gather-all-paging-structure-qword-addresses
                                           (double-rewrite x86))))
                  (no-duplicates-p
                   (mv-nth 1 (las-to-pas n-w write-addr :w (double-rewrite x86))))
                  (not (mv-nth 0 (las-to-pas n lin-addr r-w-x (double-rewrite x86))))
                  (not (mv-nth 0 (las-to-pas n-w write-addr :w (double-rewrite x86))))
                  (canonical-address-p (+ -1 n lin-addr))
                  (canonical-address-p lin-addr)
                  (unsigned-byte-p (ash n-w 3) value)
                  (natp n-w)
                  (64-bit-modep (double-rewrite x86))
                  (not (app-view x86))
                  (marking-view x86)
                  (x86p x86))
             (and
              (equal (mv-nth 0 (rb-alt n lin-addr r-w-x
                                       (mv-nth 1 (wb n-w write-addr w value x86))))
                     nil)
              (equal (mv-nth 1 (rb-alt n lin-addr r-w-x
                                       (mv-nth 1 (wb n-w write-addr w value x86))))
                     value)))
    :hints (("Goal"
             :do-not-induct t
             :in-theory (e/d* (las-to-pas
                               disjoint-p$)
                              (rewrite-rb-to-rb-alt
                               disjointness-of-all-xlation-governing-entries-paddrs-from-all-xlation-governing-entries-paddrs-subset-p
                               mv-nth-1-las-to-pas-subset-p-disjoint-from-other-p-addrs
                               force (force)))
             :use ((:instance rewrite-rb-to-rb-alt
                              (addr lin-addr) (r-x r-w-x)
                              (x86 (mv-nth 1 (wb n-w write-addr w value x86))))
                   (:instance rb-wb-equal-in-sys-view)))))

  (defthm rb-alt-wb-disjoint-in-sys-view
    (implies (and
              (disjoint-p
               ;; The physical addresses pertaining to the write
               ;; operation are disjoint from those pertaining to the
               ;; read operation.
               (mv-nth 1 (las-to-pas n-w write-addr :w (double-rewrite x86)))
               (mv-nth 1 (las-to-pas n lin-addr r-w-x (double-rewrite x86))))
              ;; We use disjoint-p for reads and disjoint-p$ for
              ;; writes, because l-addrs can be a subset of program
              ;; addresses and hence, unlike (strip-cars addr-lst),
              ;; the following hyp won't be directly present as a hyp
              ;; of a program's effects theorem.  It'll instead be in
              ;; terms of the superset of l-addrs.
              (disjoint-p
               ;; The physical addresses pertaining to the read are
               ;; disjoint from the physical addresses of the paging
               ;; structures.
               (mv-nth 1 (las-to-pas n lin-addr r-w-x (double-rewrite x86)))
               (open-qword-paddr-list (gather-all-paging-structure-qword-addresses
                                       (double-rewrite x86))))
              (disjoint-p$
               ;; The physical addresses pertaining to the write are
               ;; disjoint from the physical addresses of the paging
               ;; structures.
               (mv-nth 1 (las-to-pas n-w write-addr :w (double-rewrite x86)))
               (open-qword-paddr-list
                (gather-all-paging-structure-qword-addresses (double-rewrite x86))))
              (not (mv-nth 0 (las-to-pas n lin-addr r-w-x (double-rewrite x86))))
              (canonical-address-p (+ -1 n lin-addr))
              (canonical-address-p lin-addr)
              (canonical-address-p (+ -1 n-w write-addr))
              (canonical-address-p write-addr)
              (marking-view x86)
              (64-bit-modep (double-rewrite x86))
              (not (app-view x86)))
             (and
              (equal (mv-nth 0 (rb-alt n lin-addr r-w-x
                                       (mv-nth 1 (wb n-w write-addr w value x86))))
                     (mv-nth 0 (rb-alt n lin-addr r-w-x (double-rewrite x86))))
              (equal (mv-nth 1 (rb-alt n lin-addr r-w-x
                                       (mv-nth 1 (wb n-w write-addr w value x86))))
                     (mv-nth 1 (rb-alt n lin-addr r-w-x (double-rewrite x86))))))
    :hints (("Goal" :do-not-induct t
             :use ((:instance rewrite-rb-to-rb-alt
                              (addr lin-addr) (r-x r-w-x)
                              (x86 (mv-nth 1 (wb n-w write-addr w value x86))))
                   (:instance rewrite-rb-to-rb-alt
                              (addr lin-addr) (r-x r-w-x))
                   (:instance rb-wb-disjoint-in-sys-view))
             :in-theory (e/d* (disjoint-p$)
                              (rewrite-rb-to-rb-alt
                               rb-wb-disjoint-in-sys-view
                               disjointness-of-all-xlation-governing-entries-paddrs-from-all-xlation-governing-entries-paddrs-subset-p
                               mv-nth-1-las-to-pas-subset-p-disjoint-from-other-p-addrs)))))

  (defthm no-errors-when-translating-program-bytes-in-marking-view-using-program-at-alt
    (implies
     (and (bind-free (find-program-at-info 'prog-addr 'bytes mfc state)
                     (prog-addr bytes))
          (program-at-alt prog-addr bytes x86)
          (<= prog-addr addr)
          (<= (+ n addr) (+ (len bytes) prog-addr))
          (canonical-address-p addr)
          (64-bit-modep (double-rewrite x86)))
     (equal (mv-nth 0 (las-to-pas n addr :x x86)) nil))
    :hints
    (("Goal" :do-not-induct t
      :use ((:instance program-at-implies-error-free-address-translation)
            (:instance mv-nth-0-las-to-pas-subset-p
                       (n-1 (len bytes))
                       (addr-1 prog-addr)
                       (n-2 n)
                       (addr-2 addr)
                       (r-w-x :x))
            (:instance program-at-alt-implies-program-addresses-properties))
      :in-theory
      (e/d* (signed-byte-p)
            (rewrite-program-at-to-program-at-alt
             program-at-implies-error-free-address-translation)))))

  (defthm disjointness-of-program-bytes-from-paging-structures
    (implies (and
              (bind-free
               (find-program-at-info 'prog-addr 'bytes mfc state)
               (prog-addr bytes))
              (program-at-alt prog-addr bytes (double-rewrite x86))
              ;; <n,lin-addr> is a non-strict subset of <(len bytes),prog-addr>.
              (<= prog-addr lin-addr)
              (<= (+ n lin-addr) (+ (len bytes) prog-addr))
              (posp n) (integerp lin-addr)
              (64-bit-modep (double-rewrite x86)))
             (disjoint-p (mv-nth 1 (las-to-pas n lin-addr :x x86))
                         (open-qword-paddr-list
                          (gather-all-paging-structure-qword-addresses x86))))
    :hints (("Goal"
             :do-not-induct t
             :cases ((= (+ n lin-addr) (+ (len bytes) prog-addr)))
             :use ((:instance program-at-alt-implies-program-addresses-properties)
                   (:instance program-at-implies-error-free-address-translation)
                   (:instance disjoint-p-subset-p
                              (x (mv-nth 1 (las-to-pas (len bytes) prog-addr :x x86)))
                              (y
                               (open-qword-paddr-list
                                (gather-all-paging-structure-qword-addresses x86)))
                              (a (mv-nth 1 (las-to-pas n lin-addr :x x86)))
                              (b (open-qword-paddr-list
                                  (gather-all-paging-structure-qword-addresses x86)))))
             :in-theory (e/d* (disjoint-p$)
                              (disjoint-p-subset-p
                               program-at-implies-error-free-address-translation
                               force (force))))))

  (local
   (defthm subset-p-and-open-qword-paddr-list
     (implies (subset-p x y)
              (subset-p (open-qword-paddr-list x) (open-qword-paddr-list y)))
     :hints (("Goal" :in-theory (e/d* (subset-p open-qword-paddr-list) ())))))

  (defthmd disjointness-of-las-to-pas-from-write-to-physical-memory-subset-of-paging-structures
    (implies (and
              (equal p-addrs (addr-range 8 index))
              (disjoint-p
               (mv-nth 1 (las-to-pas n lin-addr r-x x86))
               (open-qword-paddr-list (gather-all-paging-structure-qword-addresses x86)))
              (equal (page-size (double-rewrite value)) 1)
              (physical-address-p index)
              (equal (loghead 3 index) 0)
              (unsigned-byte-p 64 value)
              (not (app-view x86)))
             (disjoint-p
              (mv-nth 1 (las-to-pas n lin-addr r-x x86))
              (open-qword-paddr-list
               (gather-all-paging-structure-qword-addresses
                (write-to-physical-memory p-addrs value x86)))))
    :hints (("Goal"
             :use ((:instance gather-all-paging-structure-qword-addresses-and-write-to-physical-memory-subset-p)
                   (:instance disjoint-p-subset-p
                              (x (mv-nth 1 (las-to-pas n lin-addr r-x x86)))
                              (y (open-qword-paddr-list
                                  (gather-all-paging-structure-qword-addresses x86)))
                              (a (mv-nth 1 (las-to-pas n lin-addr r-x x86)))
                              (b (open-qword-paddr-list
                                  (gather-all-paging-structure-qword-addresses
                                   (write-to-physical-memory p-addrs value x86))))))
             :in-theory (e/d* (subset-p
                               subset-p-reflexive)
                              (disjoint-p-subset-p
                               gather-all-paging-structure-qword-addresses-and-write-to-physical-memory-subset-p)))))

  (defthmd disjointness-of-las-to-pas-from-wb-to-subset-of-paging-structures-general
    (implies ;; No bind-free here.
     (and
      ;; The equality of
      ;; gather-all-paging-structure-qword-addresses and
      ;; las-to-pas with x86-1 and x86-2 are better than the
      ;; xlate-equiv-memory hyp because x86-2 may contain wb
      ;; terms, which don't preserve xlate-equiv-memory relation
      ;; on the x86 states.
      ;; (xlate-equiv-memory (double-rewrite x86-1) (double-rewrite x86-2))
      (equal
       (gather-all-paging-structure-qword-addresses (double-rewrite x86-2))
       (gather-all-paging-structure-qword-addresses (double-rewrite x86-1)))
      (equal (mv-nth 1 (las-to-pas n-1 lin-addr-1 r-w-x (double-rewrite x86-1)))
             (mv-nth 1 (las-to-pas n-1 lin-addr-1 r-w-x (double-rewrite x86-2))))
      (equal (page-size (double-rewrite value)) 1)
      (direct-map-p 8 entry-addr :w (double-rewrite x86-2))
      (disjoint-p$
       (mv-nth 1 (las-to-pas n-1 lin-addr-1 r-w-x (double-rewrite x86-1)))
       (open-qword-paddr-list
        (gather-all-paging-structure-qword-addresses (double-rewrite x86-1))))
      ;; <n-2,lin-addr-2> is a subset of <n-1,lin-addr-1>.
      (<= lin-addr-1 lin-addr-2)
      (< (+ n-2 lin-addr-2) (+ n-1 lin-addr-1))
      (not (mv-nth 0 (las-to-pas n-1 lin-addr-1 r-w-x (double-rewrite x86-1))))
      (physical-address-p entry-addr)
      (equal (loghead 3 entry-addr) 0)
      (unsigned-byte-p 64 value)
      (64-bit-modep x86-1)
      (64-bit-modep (double-rewrite x86-2))
      (not (app-view x86-2))
      (posp n-1) (posp n-2) (integerp lin-addr-2))
     (disjoint-p
      (mv-nth 1 (las-to-pas n-2 lin-addr-2 r-w-x x86-1))
      (open-qword-paddr-list
       (gather-all-paging-structure-qword-addresses
        (mv-nth 1 (wb 8 entry-addr w value x86-2))))))
    :hints (("Goal"
             :do-not-induct t
             :use ((:instance disjointness-of-las-to-pas-from-write-to-physical-memory-subset-of-paging-structures
                              (n n-1) (lin-addr lin-addr-1)
                              (p-addrs (addr-range 8 entry-addr))
                              (r-x r-w-x)
                              (index entry-addr)
                              (value value)
                              (x86 (mv-nth 2 (las-to-pas 8 entry-addr :w x86-2))))
                   (:instance disjoint-p-subset-p
                              (x (mv-nth 1 (las-to-pas n-1 lin-addr-1 r-w-x x86-1)))
                              (y (open-qword-paddr-list
                                  (gather-all-paging-structure-qword-addresses x86-1)))
                              (a (mv-nth 1 (las-to-pas n-2 lin-addr-2 r-w-x x86-1)))
                              (b (open-qword-paddr-list
                                  (gather-all-paging-structure-qword-addresses x86-1))))
                   (:instance disjoint-p-subset-p
                              (x (mv-nth 1 (las-to-pas n-1 lin-addr-1 r-w-x x86-1)))
                              (y (open-qword-paddr-list
                                  (gather-all-paging-structure-qword-addresses
                                   (write-to-physical-memory
                                    (addr-range 8 entry-addr)
                                    value
                                    (mv-nth 2 (las-to-pas 8 entry-addr :w x86-2))))))
                              (a (mv-nth 1 (las-to-pas n-2 lin-addr-2 r-w-x x86-1)))
                              (b (open-qword-paddr-list
                                  (gather-all-paging-structure-qword-addresses
                                   (write-to-physical-memory
                                    (addr-range 8 entry-addr)
                                    value
                                    (mv-nth 2 (las-to-pas 8 entry-addr :w x86-2))))))))
             :in-theory (e/d* (disjoint-p$
                               subset-p
                               subset-p-reflexive
                               wb
                               direct-map-p)
                              (disjointness-of-las-to-pas-from-write-to-physical-memory-subset-of-paging-structures)))))

  (defun find-program-at-alt-len-bytes-info (addr-var bytes-var mfc state)
    (declare (xargs :stobjs (state) :mode :program)
             (ignorable state))
    (b* ((call (acl2::find-call-lst 'program-at-alt (acl2::mfc-clause mfc)))
         (call (or call (acl2::find-call-lst 'program-at (acl2::mfc-clause mfc))))
         ((when (not call))
          ;; program-at-alt or program-at terms not encountered.
          nil))
      `((,addr-var . ,(nth 1 call))
        ;; (,bytes-var . (len ,(nth 2 call)))
        ;; No need to worry about the executable-counterpart of len being
        ;; enabled with the following binding...
        (,bytes-var . (quote ,(len (unquote (nth 2 call))))))))

  (defthm disjointness-of-las-to-pas-from-wb-to-subset-of-paging-structures
    ;; Note that r-x = :x here -- this rule applies during
    ;; instruction fetches.
    (implies (and
              (bind-free
               (find-program-at-alt-len-bytes-info 'lin-addr-1 'n-1 mfc state)
               (lin-addr-1 n-1))

              ;; The equality of
              ;; gather-all-paging-structure-qword-addresses and
              ;; las-to-pas with x86-1 and x86-2 are better than the
              ;; xlate-equiv-memory hyp because x86-2 may contain wb
              ;; terms, which don't preserve xlate-equiv-memory relation
              ;; on the x86 states.
              ;; (xlate-equiv-memory (double-rewrite x86-1) (double-rewrite x86-2))
              (equal
               (gather-all-paging-structure-qword-addresses (double-rewrite x86-2))
               (gather-all-paging-structure-qword-addresses (double-rewrite x86-1)))
              (equal (mv-nth 1 (las-to-pas n-1 lin-addr-1 :x (double-rewrite x86-1)))
                     (mv-nth 1 (las-to-pas n-1 lin-addr-1 :x (double-rewrite x86-2))))
              (equal (page-size (double-rewrite value)) 1)
              (direct-map-p 8 entry-addr :w (double-rewrite x86-2))
              (disjoint-p$
               (mv-nth 1 (las-to-pas n-1 lin-addr-1 :x (double-rewrite x86-1)))
               (open-qword-paddr-list
                (gather-all-paging-structure-qword-addresses (double-rewrite x86-1))))
              ;; <n-2,lin-addr-2> is a subset of <n-1,lin-addr-1>.
              (<= lin-addr-1 lin-addr-2)
              (< (+ n-2 lin-addr-2) (+ n-1 lin-addr-1))
              (not (mv-nth 0 (las-to-pas n-1 lin-addr-1 :x (double-rewrite x86-1))))
              (physical-address-p entry-addr)
              (equal (loghead 3 entry-addr) 0)
              (unsigned-byte-p 64 value)
              (64-bit-modep x86-1)
              (64-bit-modep (double-rewrite x86-2))
              (not (app-view x86-2))
              (posp n-1) (posp n-2) (integerp lin-addr-2))
             (disjoint-p
              (mv-nth 1 (las-to-pas n-2 lin-addr-2 :x x86-1))
              (open-qword-paddr-list
               (gather-all-paging-structure-qword-addresses
                (mv-nth 1 (wb 8 entry-addr w value x86-2))))))
    :hints (("Goal"
             :do-not-induct t
             :use ((:instance disjointness-of-las-to-pas-from-wb-to-subset-of-paging-structures-general
                              (r-w-x :x))))))

  (defthmd disjointness-of-las-to-pas-from-wb-to-a-paging-entry
    (implies ;; No bind-free here, and no linear address subsets.
     (and
      ;; the equality of
      ;; gather-all-paging-structure-qword-addresses and
      ;; las-to-pas with x86-1 and x86-2 are better than the
      ;; xlate-equiv-memory hyp because x86-2 may contain wb
      ;; terms, which don't preserve xlate-equiv-memory relation
      ;; on the x86 states.
      ;; (xlate-equiv-memory (double-rewrite x86-1) (double-rewrite x86-2))

      (equal
       (gather-all-paging-structure-qword-addresses (double-rewrite x86-2))
       (gather-all-paging-structure-qword-addresses (double-rewrite x86-1)))
      (equal (mv-nth 1 (las-to-pas n lin-addr r-w-x (double-rewrite x86-1)))
             (mv-nth 1 (las-to-pas n lin-addr r-w-x (double-rewrite x86-2))))
      (equal (page-size (double-rewrite value)) 1)
      (direct-map-p 8 entry-addr :w (double-rewrite x86-2))
      (disjoint-p
       (mv-nth 1 (las-to-pas n lin-addr r-w-x (double-rewrite x86-1)))
       (open-qword-paddr-list
        (gather-all-paging-structure-qword-addresses (double-rewrite x86-1))))
      (physical-address-p entry-addr)
      (equal (loghead 3 entry-addr) 0)
      (unsigned-byte-p 64 value)
      (64-bit-modep x86-1)
      (64-bit-modep (double-rewrite x86-2))
      (not (app-view x86-2)))
     (disjoint-p
      (mv-nth 1 (las-to-pas n lin-addr r-w-x x86-1))
      (open-qword-paddr-list
       (gather-all-paging-structure-qword-addresses
        (mv-nth 1 (wb 8 entry-addr w value x86-2))))))
    :hints (("Goal"
             :do-not-induct t
             :use ((:instance disjointness-of-las-to-pas-from-write-to-physical-memory-subset-of-paging-structures
                              (n n) (lin-addr lin-addr)
                              (p-addrs (addr-range 8 entry-addr))
                              (r-x r-w-x)
                              (index entry-addr)
                              (value value)
                              (x86 (mv-nth 2 (las-to-pas 8 entry-addr :w x86-2))))
                   (:instance disjoint-p-subset-p
                              (x (mv-nth 1 (las-to-pas n lin-addr r-w-x x86-1)))
                              (y (open-qword-paddr-list
                                  (gather-all-paging-structure-qword-addresses x86-1)))
                              (a (mv-nth 1 (las-to-pas n lin-addr r-w-x x86-1)))
                              (b (open-qword-paddr-list
                                  (gather-all-paging-structure-qword-addresses x86-1))))
                   (:instance disjoint-p-subset-p
                              (x (mv-nth 1 (las-to-pas n lin-addr r-w-x x86-1)))
                              (y (open-qword-paddr-list
                                  (gather-all-paging-structure-qword-addresses
                                   (write-to-physical-memory
                                    (addr-range 8 entry-addr)
                                    value
                                    (mv-nth 2 (las-to-pas 8 entry-addr :w x86-2))))))
                              (a (mv-nth 1 (las-to-pas n lin-addr r-w-x x86-1)))
                              (b (open-qword-paddr-list
                                  (gather-all-paging-structure-qword-addresses
                                   (write-to-physical-memory
                                    (addr-range 8 entry-addr)
                                    value
                                    (mv-nth 2 (las-to-pas 8 entry-addr :w x86-2))))))))
             :in-theory (e/d* (disjoint-p$
                               subset-p
                               subset-p-reflexive
                               wb
                               direct-map-p)
                              (disjointness-of-las-to-pas-from-write-to-physical-memory-subset-of-paging-structures)))))

  ;; [Shilpi] la-to-pas-values-and-mv-nth-1-wb-disjoint-from-xlation-gov-addrs
  ;; is a better rule, so commenting out las-to-pas-values-and-wb-disjoint.
  ;; (defthm las-to-pas-values-and-wb-disjoint
  ;;   (implies
  ;;    (and
  ;;     (64-bit-modep (double-rewrite x86))
  ;;     (disjoint-p
  ;;      (mv-nth 1 (las-to-pas n-2 write-addr :w (double-rewrite x86)))
  ;;      (all-xlation-governing-entries-paddrs n-1 lin-addr (double-rewrite x86)))
  ;;     (not (app-view x86))
  ;;     (x86p x86))
  ;;    (and
  ;;     (equal
  ;;      (mv-nth 0 (las-to-pas n-1 lin-addr r-w-x (mv-nth 1 (wb n-2 write-addr w value x86))))
  ;;      (mv-nth 0 (las-to-pas n-1 lin-addr r-w-x (double-rewrite x86))))
  ;;     (equal
  ;;      (mv-nth 1 (las-to-pas n-1 lin-addr r-w-x (mv-nth 1 (wb n-2 write-addr w value x86))))
  ;;      (mv-nth 1 (las-to-pas n-1 lin-addr r-w-x (double-rewrite x86))))))
  ;;   :hints (("Goal"
  ;;            :do-not-induct t
  ;;            :in-theory (e/d* (wb) ()))))

  (defthm rb-alt-and-wb-to-paging-structures-disjoint
    (implies
     (and
      (direct-map-p 8 entry-addr :w (double-rewrite x86))
      (equal (page-size (double-rewrite value)) 1)
      (disjoint-p
       (mv-nth 1 (las-to-pas n lin-addr r-w-x (double-rewrite x86)))
       (open-qword-paddr-list
        (gather-all-paging-structure-qword-addresses (double-rewrite x86))))
      (disjoint-p
       (mv-nth 1 (las-to-pas 8 entry-addr :w (double-rewrite x86)))
       (all-xlation-governing-entries-paddrs n lin-addr (double-rewrite x86)))
      (disjoint-p
       (mv-nth 1 (las-to-pas 8 entry-addr :w (double-rewrite x86)))
       (mv-nth 1 (las-to-pas n lin-addr r-w-x (double-rewrite x86))))
      (physical-address-p entry-addr)
      (equal (loghead 3 entry-addr) 0)
      (unsigned-byte-p 64 value)
      (canonical-address-p entry-addr))
     (and
      (equal (mv-nth 0 (rb-alt n lin-addr r-w-x
                               (mv-nth 1 (wb 8 entry-addr w value x86))))
             (mv-nth 0 (rb-alt n lin-addr r-w-x (double-rewrite x86))))
      (equal (mv-nth 1 (rb-alt n lin-addr r-w-x
                               (mv-nth 1 (wb 8 entry-addr w value x86))))
             (mv-nth 1 (rb-alt n lin-addr r-w-x (double-rewrite x86))))))
    :hints (("Goal"
             :do-not-induct t
             :in-theory (e/d* (disjoint-p$
                               rb-alt
                               disjointness-of-las-to-pas-from-wb-to-a-paging-entry)
                              (rewrite-rb-to-rb-alt))))))

;; ======================================================================

(define get-prefixes-alt
  ((start-rip :type (signed-byte   #.*max-linear-address-size*))
   (prefixes  :type (unsigned-byte 52))
   (rex-byte  :type (unsigned-byte 8))
   (cnt       :type (integer 0 15))
   x86)
  :non-executable t
  :guard (and (canonical-address-p (+ -1 cnt start-rip))
              (not (app-view x86))
              (marking-view x86))

  :parents (system-level-marking-view-proof-utilities)

  :short "Rewriting @('get-prefixes') to @('get-prefixes-alt')"

  :long "<p>The following is not a theorem, which is why we can not
  define congruence rules about @('get-prefixes') and
  @('xlate-equiv-memory') directly.</p>

 <code>
 (implies
  (xlate-equiv-memory x86-1 x86-2)
  (equal (mv-nth 0 (get-prefixes
                    *64-bit-mode* start-rip prefixes rex-byte cnt x86-1))
         (mv-nth 0 (get-prefixes
                    *64-bit-mode* start-rip prefixes rex-byte cnt x86-2))))
 </code>

 <p>The above would be a theorem if the following pre-conditions held
 about both @('x86-1') and @('x86-2'):</p>

 <code>
 (and (marking-view x86)
      (not (app-view x86))
      (canonical-address-p start-rip)
      (disjoint-p
       (mv-nth 1 (las-to-pas cnt start-rip :x x86))
       (open-qword-paddr-list
        (gather-all-paging-structure-qword-addresses x86)))
      (not (mv-nth 0 (las-to-pas cnt start-rip :x x86))))
 </code>

 <p>Since 'conditional' congruence rules can't be defined, we define
 an alternative version of @('get-prefixes'), called
 @('get-prefixes-alt'), which is equal to @('get-prefixes') if these
 pre-conditions hold, and if not, it returns benign values.  We prove
 a rewrite rule that rewrites @('get-prefixes') to
 @('get-prefixes-alt') when applicable, and then we can prove
 congruence rules about @('get-prefixes-alt') and
 @('xlate-equiv-memory').  Note that this approach will be most
 successful if we expect these pre-conditions to hold all the
 time.</p>

 <p>A drawback of this approach to have 'conditional' congruence-based
 rules is that all the theorems I have about @('get-prefixes') now
 have to be re-proved in terms of @('get-prefixes-alt').</p>"

  (if (and (marking-view x86)
           (64-bit-modep x86)
           (not (app-view x86))
           (canonical-address-p start-rip)
           ;; In the following two conditions below, if we're being
           ;; really precise, cnt should really be
           ;; (1+ (prefixes->num prefixes)).
           (disjoint-p
            (mv-nth 1 (las-to-pas cnt start-rip :x x86))
            (open-qword-paddr-list
             (gather-all-paging-structure-qword-addresses x86)))
           (not (mv-nth 0 (las-to-pas cnt start-rip :x x86))))

      (get-prefixes #.*64-bit-mode* start-rip prefixes rex-byte cnt x86)

    (mv nil prefixes rex-byte x86))

  ///

  (defthm natp-get-prefixes-alt.new-prefixes
    (implies
     (forced-and
      (natp prefixes)
      (canonical-address-p start-rip)
      (x86p x86))
     (natp (mv-nth 1 (get-prefixes-alt start-rip prefixes rex-byte cnt x86))))
    :rule-classes :type-prescription)

  (defthm natp-get-prefixes-alt.new-rex-byte
    (implies
     (forced-and
      (natp rex-byte)
      (natp prefixes)
      (x86p x86))
     (natp (mv-nth 2 (get-prefixes-alt start-rip prefixes rex-byte cnt x86))))
    :rule-classes :type-prescription)

  (defthm-unsigned-byte-p prefixes-width-p-of-get-prefixes.new-prefixes-alt
    :hyp (and (unsigned-byte-p #.*prefixes-width* prefixes)
              (x86p x86))
    :bound #.*prefixes-width*
    :concl (mv-nth 1 (get-prefixes-alt start-rip prefixes rex-byte cnt x86))
    :hints (("Goal"
             :use ((:instance prefixes-width-p-of-get-prefixes.new-prefixes
                              (proc-mode #.*64-bit-mode*)))
             :in-theory (e/d () (prefixes-width-p-of-get-prefixes.new-prefixes))))
    :gen-linear t)

  (defthm-unsigned-byte-p byte-p-of-get-prefixes.new-rex-byte-alt
    :hyp (and (unsigned-byte-p 8 rex-byte)
              (natp prefixes)
              (x86p x86))
    :bound 8
    :concl (mv-nth 2 (get-prefixes-alt start-rip prefixes rex-byte cnt x86))
    :hints (("Goal"
             :use ((:instance byte-p-of-get-prefixes.new-rex-byte
                              (proc-mode #.*64-bit-mode*)))
             :in-theory (e/d () (byte-p-of-get-prefixes.new-rex-byte))))
    :gen-linear t)

  (defthm x86p-get-prefixes-alt
    (implies (force (x86p x86))
             (x86p (mv-nth 3 (get-prefixes-alt
                              start-rip prefixes rex-byte cnt x86)))))

  (make-event
   (generate-xr-over-write-thms
    (remove-elements-from-list
     '(:mem :fault)
     *x86-field-names-as-keywords*)
    'get-prefixes-alt
    (acl2::formals 'get-prefixes-alt (w state))
    :output-index 3))

  (defthm xr-fault-and-get-prefixes-alt
    (equal (xr :fault index
               (mv-nth 3 (get-prefixes-alt start-rip prefixes rex-byte cnt x86)))
           (xr :fault index x86))
    :hints (("Goal" :in-theory (e/d* (get-prefixes-alt)
                                     (not force (force))))))

  (make-event
   (generate-read-fn-over-xw-thms
    (remove-elements-from-list
     '(:mem :rflags :ctr :seg-visible
            :seg-hidden-base :seg-hidden-limit :seg-hidden-attr
            :msr :fault :app-view :marking-view)
     *x86-field-names-as-keywords*)
    'get-prefixes-alt
    (acl2::formals 'get-prefixes-alt (w state))
    :output-index 0
    ;; :hyps '(not (app-view x86))
    :double-rewrite? t))

  (make-event
   (generate-read-fn-over-xw-thms
    (remove-elements-from-list
     '(:mem :rflags :ctr :seg-visible
            :seg-hidden-base :seg-hidden-limit :seg-hidden-attr
            :msr :fault :app-view :marking-view)
     *x86-field-names-as-keywords*)
    'get-prefixes-alt
    (acl2::formals 'get-prefixes-alt (w state))
    :output-index 1
    ;; :hyps '(not (app-view x86))
    :double-rewrite? t))

  (make-event
   (generate-read-fn-over-xw-thms
    (remove-elements-from-list
     '(:mem :rflags :ctr :seg-visible
            :seg-hidden-base :seg-hidden-limit :seg-hidden-attr
            :msr :fault :app-view :marking-view)
     *x86-field-names-as-keywords*)
    'get-prefixes-alt
    (acl2::formals 'get-prefixes-alt (w state))
    :output-index 2
    ;; :hyps '(not (app-view x86))
    :double-rewrite? t))

  (make-event
   (generate-write-fn-over-xw-thms
    (remove-elements-from-list
     '(:mem :rflags :ctr :seg-visible
            :seg-hidden-base :seg-hidden-limit :seg-hidden-attr
            :msr :fault :app-view :marking-view)
     *x86-field-names-as-keywords*)
    'get-prefixes-alt
    (acl2::formals 'get-prefixes-alt (w state))
    :output-index 3
    ;; :hyps '(not (app-view x86))
    ))

  (defthm get-prefixes-alt-values-and-xw-rflags-in-sys-view
    (implies
     (and (equal (rflagsBits->ac (double-rewrite value))
                 (rflagsBits->ac (rflags x86)))
          (x86p x86))
     (and
      (equal (mv-nth
              0
              (get-prefixes-alt start-rip prefixes rex-byte cnt
                                (xw :rflags 0 value x86)))
             (mv-nth
              0
              (get-prefixes-alt start-rip prefixes rex-byte
                                cnt (double-rewrite x86))))
      (equal (mv-nth
              1
              (get-prefixes-alt start-rip prefixes rex-byte cnt
                                (xw :rflags 0 value x86)))
             (mv-nth
              1
              (get-prefixes-alt start-rip prefixes rex-byte cnt
                                (double-rewrite x86))))
      (equal (mv-nth
              2
              (get-prefixes-alt start-rip prefixes rex-byte cnt
                                (xw :rflags 0 value x86)))
             (mv-nth
              2
              (get-prefixes-alt start-rip prefixes rex-byte
                                cnt (double-rewrite x86))))))
    :hints (("Goal" :do-not-induct t
             :in-theory (e/d* () (force (force))))))

  (defthm get-prefixes-alt-and-xw-rflags-state-in-sys-view
    (implies (and (equal (rflagsBits->ac (double-rewrite value))
                         (rflagsBits->ac (rflags x86)))
                  (not (app-view x86))
                  (x86p x86))
             (equal
              (mv-nth
               3
               (get-prefixes-alt start-rip prefixes rex-byte cnt
                                 (xw :rflags 0 value x86)))
              (xw :rflags 0 value
                  (mv-nth
                   3
                   (get-prefixes-alt
                    start-rip prefixes rex-byte cnt x86)))))
    :hints (("Goal" :do-not-induct t :in-theory (e/d* () (force (force))))))

  (defthm xr-rflags-and-mv-nth-3-get-prefixes-alt
    (equal (xr :rflags 0
               (mv-nth 3
                       (get-prefixes-alt start-rip prefixes rex-byte cnt x86)))
           (xr :rflags 0 x86)))

  (defthm alignment-checking-enabled-p-and-mv-nth-3-get-prefixes-alt
    (equal (alignment-checking-enabled-p
            (mv-nth 3 (get-prefixes-alt start-rip prefixes rex-byte cnt x86)))
           (alignment-checking-enabled-p x86))
    :hints (("Goal" :in-theory (e/d* (alignment-checking-enabled-p) ()))))

  (local (in-theory (e/d* () (get-prefixes-alt))))

  (defthm rewrite-get-prefixes-to-get-prefixes-alt
    (implies (forced-and
              (disjoint-p
               (mv-nth 1 (las-to-pas cnt start-rip :x (double-rewrite x86)))
               (open-qword-paddr-list
                (gather-all-paging-structure-qword-addresses (double-rewrite x86))))
              (not (mv-nth 0 (las-to-pas cnt start-rip :x (double-rewrite x86))))
              (marking-view x86)
              (64-bit-modep (double-rewrite x86))
              (not (app-view x86))
              (canonical-address-p start-rip))
             (equal (get-prefixes
                     #.*64-bit-mode* start-rip prefixes rex-byte cnt x86)
                    (get-prefixes-alt start-rip prefixes rex-byte cnt
                                      (double-rewrite x86))))
    :hints (("Goal" :in-theory (e/d* (get-prefixes-alt) ()))))

  ;; Opener lemmas:

  (defthm get-prefixes-alt-opener-lemma-zero-cnt
    (implies (and (marking-view x86)
                  (64-bit-modep (double-rewrite x86))
                  (not (app-view x86))
                  (canonical-address-p start-rip))
             (equal (get-prefixes-alt start-rip prefixes rex-byte 0 x86)
                    (mv t prefixes rex-byte x86)))
    :hints
    (("Goal"
      :use ((:instance get-prefixes-opener-lemma-zero-cnt
                       (proc-mode #.*64-bit-mode*)
                       (cnt 0)))
      :in-theory (e/d ()
                      (get-prefixes-opener-lemma-zero-cnt force (force))))))

  (defthm get-prefixes-alt-opener-lemma-no-prefix-byte
    (implies
     (and (b* (((mv flg prefix-byte &)
                (rb-alt 1 start-rip :x (double-rewrite x86)))
               (prefix-byte-group-code
                (get-one-byte-prefix-array-code prefix-byte)))
            (and (not flg)
                 (zp prefix-byte-group-code)
                 (not (equal (ash prefix-byte -4) 4))))
          (not (zp cnt))
          (marking-view x86)
          (64-bit-modep (double-rewrite x86))
          (not (app-view x86))
          (canonical-address-p start-rip)
          ;; We read only one byte inside get-prefixes-alt --
          ;; there's really no need for us to know that the
          ;; translation of (create-canonical-address-list cnt
          ;; start-rip) is non-erroneous or that that range is
          ;; disjoint from the paging structures.  But,
          ;; unfortunately, because of the definition of
          ;; get-prefixes-alt, we need to know the following two
          ;; things in terms of a general cnt instead of cnt == 1.
          (not (mv-nth 0 (las-to-pas cnt start-rip :x (double-rewrite x86))))
          (disjoint-p
           (mv-nth 1 (las-to-pas cnt start-rip :x (double-rewrite x86)))
           (open-qword-paddr-list
            (gather-all-paging-structure-qword-addresses
             (double-rewrite x86)))))
     (b* (((mv new-flg new-prefixes new-rex-byte &)
           (get-prefixes-alt start-rip prefixes rex-byte cnt x86)))

       (and
        (equal new-flg nil)
        (equal new-prefixes
               (let ((prefixes
                      (!prefixes->nxt
                       (mv-nth 1 (rb-alt 1 start-rip :x (double-rewrite x86)))
                       prefixes)))
                 (!prefixes->num (- 15 cnt) prefixes)))
        (equal new-rex-byte rex-byte))))
    :hints (("Goal"
             :use ((:instance get-prefixes-opener-lemma-no-prefix-byte
                              (proc-mode #.*64-bit-mode*))
                   (:instance rewrite-rb-to-rb-alt
                              (r-x :x) (addr start-rip) (n 1)))
             :in-theory (e/d* (mv-nth-0-las-to-pas-subset-p disjoint-p$)
                              (rewrite-rb-to-rb-alt
                               get-prefixes-opener-lemma-no-prefix-byte)))))

  (defthm get-prefixes-alt-opener-lemma-no-legacy-prefix-but-rex-prefix
    (implies
     (and (b* (((mv flg prefix-byte &)
                (rb-alt 1 start-rip :x (double-rewrite x86)))
               (prefix-byte-group-code
                (get-one-byte-prefix-array-code prefix-byte)))
            (and (not flg)
                 (zp prefix-byte-group-code)
                 (equal (ash prefix-byte -4) 4)))
          (not (zp cnt))
          (marking-view x86)
          (64-bit-modep (double-rewrite x86))
          (not (app-view x86))
          (canonical-address-p start-rip)
          (not (mv-nth 0 (las-to-pas cnt start-rip :x (double-rewrite x86))))
          (disjoint-p
           (mv-nth 1 (las-to-pas cnt start-rip :x (double-rewrite x86)))
           (open-qword-paddr-list
            (gather-all-paging-structure-qword-addresses
             (double-rewrite x86)))))
     (equal
      (get-prefixes-alt start-rip prefixes rex-byte cnt x86)
      (b* (((mv & byte byte-x86)
            (rb-alt 1 start-rip :x x86))
           (next-rip (the (signed-byte
                           #.*max-linear-address-size+1*)
                       (1+ start-rip))))
        (if (not (canonical-address-p next-rip))
            (mv (list :non-canonical-instruction-pointer next-rip)
                prefixes rex-byte byte-x86)
          (get-prefixes-alt
           next-rip prefixes
           byte ;; REX prefix, overwriting a previously encountered REX,
           ;; if any
           (1- cnt)
           byte-x86)))))
    :hints (("Goal"
             :use
             ((:instance get-prefixes-opener-lemma-no-legacy-prefix-but-rex-prefix
                         (proc-mode #.*64-bit-mode*))
              (:instance rewrite-rb-to-rb-alt
                         (r-x :x) (addr start-rip) (n 1)))
             :in-theory
             (e/d* (mv-nth-0-las-to-pas-subset-p disjoint-p$)
                   (rewrite-rb-to-rb-alt
                    get-prefixes-opener-lemma-no-legacy-prefix-but-rex-prefix)))))

  (defthm get-prefixes-alt-opener-lemma-group-1-prefix-in-marking-view
    (b* (((mv flg prefix-byte new-x86)
          (rb-alt 1 start-rip :x (double-rewrite x86)))
         (prefix-byte-group-code
          (get-one-byte-prefix-array-code prefix-byte)))
      (implies
       (and
        (not flg)
        (equal prefix-byte-group-code 1)
        (canonical-address-p (1+ start-rip))
        (not (zp cnt))
        (marking-view x86)
        (64-bit-modep (double-rewrite x86))
        (not (app-view x86))
        (canonical-address-p start-rip)
        (disjoint-p
         (mv-nth 1 (las-to-pas cnt start-rip :x (double-rewrite x86)))
         (open-qword-paddr-list
          (gather-all-paging-structure-qword-addresses (double-rewrite x86))))
        (not (mv-nth 0 (las-to-pas cnt start-rip :x (double-rewrite x86)))))
       (equal (get-prefixes-alt start-rip prefixes rex-byte cnt x86)
              (get-prefixes-alt (+ 1 start-rip)
                                (if (equal prefix-byte #.*lock*)
                                    (!prefixes->lck prefix-byte prefixes)
                                  (!prefixes->rep prefix-byte prefixes))
                                0
                                (+ -1 cnt)
                                new-x86))))
    :hints (("Goal"
             :use ((:instance get-prefixes-opener-lemma-group-1-prefix-in-marking-view)
                   (:instance rewrite-rb-to-rb-alt
                              (r-x :x) (addr start-rip) (n 1))
                   (:instance rewrite-get-prefixes-to-get-prefixes-alt)
                   (:instance rewrite-get-prefixes-to-get-prefixes-alt
                              (start-rip (1+ start-rip))
                              (prefixes
                               (if (equal
                                    (mv-nth 1 (rb-alt 1 start-rip :x x86))
                                    *lock*)
                                   (!prefixes->lck
                                    (mv-nth 1 (rb-alt 1 start-rip :x x86))
                                    prefixes)
                                 (!prefixes->rep
                                  (mv-nth 1 (rb-alt 1 start-rip :x x86))
                                  prefixes)))
                              (rex-byte 0)
                              (cnt (1- cnt))
                              (x86 (mv-nth 2 (rb-alt 1 start-rip :x x86))))
                   (:instance mv-nth-1-las-to-pas-subset-p-disjoint-from-other-p-addrs
                              (prog-len cnt) (prog-addr start-rip) (r-w-x :x)
                              (n (1- cnt)) (addr (1+ start-rip))
                              (other-p-addrs
                               (open-qword-paddr-list
                                (gather-all-paging-structure-qword-addresses x86)))))
             :in-theory (e/d* (mv-nth-0-las-to-pas-subset-p disjoint-p$)
                              (rewrite-rb-to-rb-alt
                               rewrite-get-prefixes-to-get-prefixes-alt
                               get-prefixes-opener-lemma-group-1-prefix-in-marking-view
                               mv-nth-1-las-to-pas-subset-p-disjoint-from-other-p-addrs
                               open-qword-paddr-list
                               get-prefixes-alt-opener-lemma-no-legacy-prefix-but-rex-prefix
                               force (force))))))

  (defthm get-prefixes-alt-opener-lemma-group-2-prefix-in-marking-view
    (b* (((mv flg prefix-byte new-x86)
          (rb-alt 1 start-rip :x (double-rewrite x86)))
         (prefix-byte-group-code
          (get-one-byte-prefix-array-code prefix-byte)))
      (implies
       (and
        (canonical-address-p (1+ start-rip))
        (not (zp cnt))
        (not flg)
        (equal prefix-byte-group-code 2)
        (marking-view x86)
        (64-bit-modep (double-rewrite x86))
        (not (app-view x86))
        (canonical-address-p start-rip)
        (disjoint-p
         (mv-nth 1 (las-to-pas cnt start-rip :x (double-rewrite x86)))
         (open-qword-paddr-list
          (gather-all-paging-structure-qword-addresses (double-rewrite x86))))
        (not (mv-nth 0 (las-to-pas cnt start-rip :x (double-rewrite x86)))))
       (equal (get-prefixes-alt start-rip prefixes rex-byte cnt x86)
              (if (or (equal prefix-byte #.*fs-override*)
                      (equal prefix-byte #.*gs-override*))
                  (get-prefixes-alt
                   (1+ start-rip)
                   (!prefixes->seg prefix-byte prefixes)
                   0
                   (1- cnt)
                   new-x86)
                (get-prefixes-alt
                 (1+ start-rip) prefixes 0 (1- cnt)
                 new-x86)))))
    :hints (("Goal"
             :use ((:instance get-prefixes-opener-lemma-group-2-prefix-in-marking-view)
                   (:instance rewrite-rb-to-rb-alt
                              (r-x :x) (addr start-rip) (n 1))
                   (:instance rewrite-get-prefixes-to-get-prefixes-alt)
                   (:instance rewrite-get-prefixes-to-get-prefixes-alt
                              (start-rip (1+ start-rip))
                              (prefixes
                               (if (or (equal
                                        (mv-nth 1 (rb-alt 1 start-rip :x x86))
                                        *fs-override*)
                                       (equal
                                        (mv-nth 1 (rb-alt 1 start-rip :x x86))
                                        *gs-override*))
                                   (!prefixes->seg
                                    (mv-nth 1 (rb-alt 1 start-rip :x x86))
                                    prefixes)
                                 prefixes))
                              (rex-byte 0)
                              (cnt (1- cnt))
                              (x86 (mv-nth 2 (rb-alt 1 start-rip :x x86))))
                   (:instance mv-nth-1-las-to-pas-subset-p-disjoint-from-other-p-addrs
                              (prog-len cnt) (prog-addr start-rip) (r-w-x :x)
                              (n (1- cnt)) (addr (1+ start-rip))
                              (other-p-addrs
                               (open-qword-paddr-list
                                (gather-all-paging-structure-qword-addresses x86)))))
             :in-theory (e/d* (mv-nth-0-las-to-pas-subset-p disjoint-p$)
                              (rewrite-rb-to-rb-alt
                               rewrite-get-prefixes-to-get-prefixes-alt
                               get-prefixes-opener-lemma-group-2-prefix-in-marking-view
                               mv-nth-1-las-to-pas-subset-p-disjoint-from-other-p-addrs
                               open-qword-paddr-list
                               force (force))))))

  (defthm get-prefixes-alt-opener-lemma-group-3-prefix-in-marking-view
    (b* (((mv flg prefix-byte new-x86)
          (rb-alt 1 start-rip :x (double-rewrite x86)))
         (prefix-byte-group-code
          (get-one-byte-prefix-array-code prefix-byte)))
      (implies
       (and
        (canonical-address-p (1+ start-rip))
        (not (zp cnt))
        (not flg)
        (equal prefix-byte-group-code 3)
        (marking-view x86)
        (64-bit-modep (double-rewrite x86))
        (not (app-view x86))
        (canonical-address-p start-rip)
        (disjoint-p
         (mv-nth 1 (las-to-pas cnt start-rip :x (double-rewrite x86)))
         (open-qword-paddr-list
          (gather-all-paging-structure-qword-addresses (double-rewrite x86))))
        (not (mv-nth 0 (las-to-pas cnt start-rip :x (double-rewrite x86)))))
       (equal (get-prefixes-alt start-rip prefixes rex-byte cnt x86)
              (get-prefixes-alt (+ 1 start-rip)
                                (!prefixes->opr
                                 prefix-byte
                                 prefixes)
                                0
                                (+ -1 cnt)
                                new-x86))))
    :hints (("Goal"
             :use ((:instance get-prefixes-opener-lemma-group-3-prefix-in-marking-view)
                   (:instance rewrite-rb-to-rb-alt
                              (r-x :x) (addr start-rip) (n 1))
                   (:instance rewrite-get-prefixes-to-get-prefixes-alt)
                   (:instance rewrite-get-prefixes-to-get-prefixes-alt
                              (start-rip (1+ start-rip))
                              (prefixes (!prefixes->opr
                                         (mv-nth 1 (rb-alt 1 start-rip :x x86))
                                         prefixes))
                              (rex-byte 0)
                              (cnt (1- cnt))
                              (x86 (mv-nth 2 (rb-alt 1 start-rip :x x86))))
                   (:instance mv-nth-1-las-to-pas-subset-p-disjoint-from-other-p-addrs
                              (prog-len cnt) (prog-addr start-rip) (r-w-x :x)
                              (n (1- cnt)) (addr (1+ start-rip))
                              (other-p-addrs
                               (open-qword-paddr-list
                                (gather-all-paging-structure-qword-addresses x86)))))
             :in-theory (e/d* (mv-nth-0-las-to-pas-subset-p disjoint-p$)
                              (rewrite-rb-to-rb-alt
                               rewrite-get-prefixes-to-get-prefixes-alt
                               get-prefixes-opener-lemma-group-3-prefix-in-marking-view
                               mv-nth-1-las-to-pas-subset-p-disjoint-from-other-p-addrs
                               open-qword-paddr-list
                               force (force))))))

  (defthm get-prefixes-alt-opener-lemma-group-4-prefix-in-marking-view
    (b* (((mv flg prefix-byte new-x86)
          (rb-alt 1 start-rip :x (double-rewrite x86)))
         (prefix-byte-group-code
          (get-one-byte-prefix-array-code prefix-byte)))
      (implies
       (and
        (canonical-address-p (1+ start-rip))
        (not (zp cnt))
        (not flg)
        (equal prefix-byte-group-code 4)
        (marking-view x86)
        (64-bit-modep (double-rewrite x86))
        (not (app-view x86))
        (canonical-address-p start-rip)
        (disjoint-p
         (mv-nth 1 (las-to-pas cnt start-rip :x (double-rewrite x86)))
         (open-qword-paddr-list
          (gather-all-paging-structure-qword-addresses (double-rewrite x86))))
        (not (mv-nth 0 (las-to-pas cnt start-rip :x (double-rewrite x86)))))
       (equal (get-prefixes-alt start-rip prefixes rex-byte cnt x86)
              (get-prefixes-alt (+ 1 start-rip)
                                (!prefixes->adr prefix-byte prefixes)
                                0
                                (+ -1 cnt)
                                new-x86))))
    :hints (("Goal"
             :use ((:instance get-prefixes-opener-lemma-group-4-prefix-in-marking-view)
                   (:instance rewrite-rb-to-rb-alt
                              (r-x :x) (addr start-rip) (n 1))
                   (:instance rewrite-get-prefixes-to-get-prefixes-alt)
                   (:instance rewrite-get-prefixes-to-get-prefixes-alt
                              (start-rip (1+ start-rip))
                              (prefixes
                               (!prefixes->adr
                                (mv-nth 1 (rb-alt 1 start-rip :x x86))
                                prefixes))
                              (rex-byte 0)
                              (cnt (1- cnt))
                              (x86 (mv-nth 2 (rb-alt 1 start-rip :x x86))))
                   (:instance mv-nth-1-las-to-pas-subset-p-disjoint-from-other-p-addrs
                              (prog-len cnt) (prog-addr start-rip) (r-w-x :x)
                              (n (1- cnt)) (addr (1+ start-rip))
                              (other-p-addrs
                               (open-qword-paddr-list
                                (gather-all-paging-structure-qword-addresses x86)))))
             :in-theory (e/d* (mv-nth-0-las-to-pas-subset-p disjoint-p$)
                              (rewrite-rb-to-rb-alt
                               rewrite-get-prefixes-to-get-prefixes-alt
                               get-prefixes-opener-lemma-group-4-prefix-in-marking-view
                               mv-nth-1-las-to-pas-subset-p-disjoint-from-other-p-addrs
                               open-qword-paddr-list
                               force (force))))))

  (defthm get-prefixes-alt-xw-rflags-not-ac-values-in-sys-view
    (implies
     (equal (rflagsbits->ac (double-rewrite value))
            (rflagsbits->ac (rflags x86)))
     (and (equal (mv-nth 0 (get-prefixes-alt start-rip prefixes rex-byte cnt
                                             (xw :rflags 0 value x86)))
                 (mv-nth 0 (get-prefixes-alt start-rip prefixes rex-byte cnt x86)))
          (equal (mv-nth 1 (get-prefixes-alt start-rip prefixes rex-byte cnt
                                             (xw :rflags 0 value x86)))
                 (mv-nth 1 (get-prefixes-alt start-rip prefixes rex-byte cnt x86)))
          (equal (mv-nth 2 (get-prefixes-alt start-rip prefixes rex-byte cnt
                                             (xw :rflags 0 value x86)))
                 (mv-nth 2 (get-prefixes-alt start-rip prefixes rex-byte cnt x86)))))
    :hints (("Goal" :in-theory (e/d (get-prefixes-alt)
                                    (rewrite-get-prefixes-to-get-prefixes-alt)))))

  (defthm xlate-equiv-memory-and-two-mv-nth-0-get-prefixes-alt-cong
    (implies
     (xlate-equiv-memory x86-1 x86-2)
     (equal (mv-nth 0 (get-prefixes-alt start-rip prefixes rex-byte cnt x86-1))
            (mv-nth 0 (get-prefixes-alt start-rip prefixes rex-byte cnt x86-2))))
    :hints (("Goal"
             :use ((:instance xlate-equiv-memory-and-two-get-prefixes-values))
             :in-theory (e/d* (get-prefixes-alt las-to-pas)
                              (rewrite-get-prefixes-to-get-prefixes-alt
                               xlate-equiv-memory-and-two-get-prefixes-values))))
    :rule-classes :congruence)

  (defthm xlate-equiv-memory-and-two-mv-nth-1-get-prefixes-alt-cong
    (implies
     (xlate-equiv-memory x86-1 x86-2)
     (equal (mv-nth 1 (get-prefixes-alt start-rip prefixes rex-byte cnt x86-1))
            (mv-nth 1 (get-prefixes-alt start-rip prefixes rex-byte cnt x86-2))))
    :hints (("Goal"
             :use ((:instance xlate-equiv-memory-and-two-get-prefixes-values))
             :in-theory (e/d* (get-prefixes-alt las-to-pas)
                              (rewrite-get-prefixes-to-get-prefixes-alt
                               xlate-equiv-memory-and-two-get-prefixes-values))))
    :rule-classes :congruence)

  (defthm xlate-equiv-memory-and-two-mv-nth-2-get-prefixes-alt-cong
    (implies
     (xlate-equiv-memory x86-1 x86-2)
     (equal (mv-nth 2 (get-prefixes-alt start-rip prefixes rex-byte cnt x86-1))
            (mv-nth 2 (get-prefixes-alt start-rip prefixes rex-byte cnt x86-2))))
    :hints (("Goal"
             :use ((:instance xlate-equiv-memory-and-two-get-prefixes-values))
             :in-theory (e/d* (get-prefixes-alt las-to-pas)
                              (rewrite-get-prefixes-to-get-prefixes-alt
                               xlate-equiv-memory-and-two-get-prefixes-values))))
    :rule-classes :congruence)

  (defthm xlate-equiv-memory-and-two-mv-nth-3-get-prefixes-alt-cong
    (implies (xlate-equiv-memory x86-1 x86-2)
             (xlate-equiv-memory
              (mv-nth 3 (get-prefixes-alt start-rip prefixes rex-byte cnt x86-1))
              (mv-nth 3 (get-prefixes-alt start-rip prefixes rex-byte cnt x86-2))))
    :hints (("Goal"
             :use ((:instance xlate-equiv-memory-and-two-mv-nth-3-get-prefixes))
             :in-theory (e/d* (get-prefixes-alt)
                              (xlate-equiv-memory-and-mv-nth-3-get-prefixes
                               rewrite-get-prefixes-to-get-prefixes-alt))))
    :rule-classes :congruence)

  (defthm xlate-equiv-memory-and-mv-nth-3-get-prefixes-alt
    ;; Why do I need both the versions?
    (and
     ;; Matt thinks that this one here acts as a rewrite rule which
     ;; hangs on iff and whose RHS is T.
     (xlate-equiv-memory
      x86 (mv-nth 3 (get-prefixes-alt start-rip prefixes rex-byte cnt x86)))
     ;; Matt thinks that this one acts as a driver rule whose RHS is
     ;; (double-rewrite x86).
     (xlate-equiv-memory
      (mv-nth 3 (get-prefixes-alt start-rip prefixes rex-byte cnt x86))
      (double-rewrite x86)))
    :hints (("Goal"
             :in-theory (e/d* (get-prefixes-alt)
                              (rewrite-get-prefixes-to-get-prefixes-alt
                               force (force))))))

  (defthm mv-nth-3-get-prefixes-alt-no-prefix-byte
    ;; Rewrite (mv-nth 3 (get-prefixes-alt ...)) to (mv-nth 2
    ;; (las-to-pas ...)) when no prefix bytes are present and no
    ;; errors are encountered.
    (b* (((mv flg prefix-byte &)
          ;; (rml08 start-rip :x x86)
          (rb-alt 1 start-rip :x (double-rewrite x86)))
         (prefix-byte-group-code
          (get-one-byte-prefix-array-code prefix-byte)))
      (implies
       (and (not flg)
            (zp prefix-byte-group-code)
            (not (equal (ash prefix-byte -4) 4))
            (not (zp cnt))
            (not (mv-nth 0 (las-to-pas cnt start-rip :x (double-rewrite x86))))
            (disjoint-p
             (mv-nth 1 (las-to-pas cnt start-rip :x (double-rewrite x86)))
             (open-qword-paddr-list
              (gather-all-paging-structure-qword-addresses (double-rewrite x86))))
            (64-bit-modep (double-rewrite x86)))
       (equal (mv-nth 3 (get-prefixes-alt start-rip prefixes rex-byte cnt x86))
              (mv-nth 2 (las-to-pas 1 start-rip :x x86)))))
    :hints
    (("Goal"
      :do-not-induct t
      :use ((:instance rewrite-rb-to-rb-alt
                       (r-x :x) (addr start-rip) (n 1)))
      :in-theory (e/d* (get-prefixes-alt
                        get-prefixes
                        las-to-pas
                        mv-nth-0-las-to-pas-subset-p
                        disjoint-p)
                       (rewrite-rb-to-rb-alt
                        rewrite-get-prefixes-to-get-prefixes-alt)))))

  ;; Interaction between get-prefixes-alt and wb:
  ;; Proof of
  ;; get-prefixes-alt-and-wb-in-system-level-marking-view-disjoint-from-paging-structures
  ;; and get-prefixes-alt-and-wb-to-paging-structures follows.

  (encapsulate
    ()

    (local (in-theory (e/d (mv-nth-0-las-to-pas-subset-p)
                           (xlate-equiv-memory-and-mv-nth-1-rml08))))

    (defthm mv-nth-0-rb-and-xw-mem-in-sys-view
      (implies (and (disjoint-p
                     (list index)
                     (all-xlation-governing-entries-paddrs
                      n lin-addr (double-rewrite x86)))
                    (canonical-address-p lin-addr)
                    (canonical-address-p (+ -1 n lin-addr))
                    (physical-address-p index)
                    (unsigned-byte-p 8 value)
                    (64-bit-modep (double-rewrite x86))
                    (x86p x86))
               (equal (mv-nth 0 (rb n lin-addr r-x (xw :mem index value x86)))
                      (mv-nth 0 (rb n lin-addr r-x (double-rewrite x86)))))
      :hints (("Goal" :in-theory (e/d* (rb disjoint-p las-to-pas)
                                       (force (force))))))

    (defthm read-from-physical-memory-xw-mem
      (implies (disjoint-p (list index) p-addrs)
               (equal (read-from-physical-memory
                       p-addrs (xw :mem index value x86))
                      (read-from-physical-memory p-addrs x86)))
      :hints (("Goal" :in-theory (e/d* (read-from-physical-memory
                                        disjoint-p)
                                       ()))))

    (defthm mv-nth-1-rb-and-xw-mem-in-sys-view
      (implies
       (and
        (disjoint-p
         (list index)
         (all-xlation-governing-entries-paddrs n lin-addr (double-rewrite x86)))
        (disjoint-p
         (list index)
         (mv-nth 1 (las-to-pas n lin-addr r-x (double-rewrite x86))))
        (disjoint-p
         (mv-nth 1 (las-to-pas n lin-addr r-x (double-rewrite x86)))
         (all-xlation-governing-entries-paddrs n lin-addr (double-rewrite x86)))
        (canonical-address-p lin-addr)
        (canonical-address-p (+ -1 n lin-addr))
        (physical-address-p index)
        (unsigned-byte-p 8 value)
        (64-bit-modep (double-rewrite x86))
        (not (app-view x86))
        (x86p x86))
       (equal (mv-nth 1 (rb n lin-addr r-x (xw :mem index value x86)))
              (mv-nth 1 (rb n lin-addr r-x x86))))
      :hints (("Goal" :in-theory (e/d* (rb
                                        disjoint-p
                                        las-to-pas)
                                       (xlate-equiv-memory-and-xr-mem-from-rest-of-memory
                                        force (force))))))

    (define find-l-addrs-from-disjoint-p-of-las-to-pas-1-aux ((vars true-listp)
                                                              calls)
      :guard (equal (len vars) 2)
      (if (atom calls)
          nil
        (b* ((one-call (car calls))
             ((unless (and (true-listp one-call) (equal 3 (len one-call))))
              ;; (cw "~%One-call: ~p0~%" one-call)
              nil)
             (mv-nth-term-1 (nth 1 one-call))
             ((unless (and (true-listp mv-nth-term-1) (equal 3 (len mv-nth-term-1))))
              nil)
             (term-1 (nth 2 mv-nth-term-1))
             ((unless (and (true-listp term-1) (equal 5 (len term-1))))
              nil)
             ((list n-var addr-var) vars))
          (cons (list (cons n-var    (nth 1 term-1))
                      (cons addr-var (nth 2 term-1)))
                (find-l-addrs-from-disjoint-p-of-las-to-pas-1-aux vars (cdr calls))))))

    (defun find-l-addrs-from-disjoint-p-of-las-to-pas-and-all-xlation
      (vars r-w-x mfc state)
      (declare (xargs :stobjs (state) :mode :program)
               (ignorable state))
      ;; Narrows the matches by looking at only those calls of las-to-pas
      ;; which have "r-w-x" in the permission field.
      (b* ((calls (acl2::find-matches-list
                   `(disjoint-p
                     (mv-nth 1 (las-to-pas n addr ,r-w-x x86))
                     (all-xlation-governing-entries-paddrs n addr x86))
                   (acl2::mfc-clause mfc) nil))
           ((when (not calls))
            ;; Term not encountered.
            nil))
        (find-l-addrs-from-disjoint-p-of-las-to-pas-1-aux
         vars calls)))


    (local
     (defthmd disjoint-p-all-xlation-governing-entries-paddrs-and-las-to-pas-subset-p
       ;; Very similar to
       ;; MV-NTH-1-LAS-TO-PAS-SUBSET-P-DISJOINT-FROM-OTHER-P-ADDRS,
       ;; DISJOINTNESS-OF-ALL-XLATION-GOVERNING-ENTRIES-PADDRS-FROM-ALL-XLATION-GOVERNING-ENTRIES-PADDRS-SUBSET-P.

       ;; This rule is tailored to rewrite terms of the form

       ;; (disjoint-p
       ;;  (mv-nth 1 (las-to-pas l-addrs-subset r-x cpl x86))
       ;;  (all-xlation-governing-entries-paddrs l-addrs-subset x86))

       ;; where l-addrs-subset is a subset of l-addrs, and l-addrs is of
       ;; the form (create-canonical-address-list ...).

       (implies
        (and
         (bind-free (find-l-addrs-from-disjoint-p-of-las-to-pas-and-all-xlation
                     '(n-1 addr-1) r-x mfc state)
                    (n-1 addr-1))
         (disjoint-p
          (mv-nth 1 (las-to-pas n-1 addr-1 r-x (double-rewrite x86)))
          (all-xlation-governing-entries-paddrs n-1 addr-1 (double-rewrite x86)))
         ;; <n-2,addr-2> is a subset of <n-1,addr-1>.
         (<= addr-1 addr-2)
         (< (+ n-2 addr-2) (+ n-1 addr-1))
         (posp n-1) (posp n-2) (integerp addr-2) (integerp addr-1)
         (not (mv-nth 0 (las-to-pas n-1 addr-1 r-x (double-rewrite x86))))
         (64-bit-modep x86))
        (disjoint-p (mv-nth 1 (las-to-pas n-2 addr-2 r-x x86))
                    (all-xlation-governing-entries-paddrs n-2 addr-2 x86)))
       :hints
       (("Goal"
         :in-theory (e/d* (disjoint-p-commutative) ())
         :use ((:instance disjointness-of-all-xlation-governing-entries-paddrs-from-all-xlation-governing-entries-paddrs-subset-p
                          (n-1 n-2) (addr-1 addr-2)
                          (n-2 n-1) (addr-2 addr-1)
                          (other-p-addrs (mv-nth 1 (las-to-pas n-1 addr-1 r-x x86)))
                          (other-p-addrs-subset
                           (mv-nth 1 (las-to-pas n-2 addr-2 r-x x86)))))))))

    (encapsulate
      ()

      (local
       ;; (show-accumulated-persistence :useless :list)
       (in-theory
        (e/d* ()
              (disjointness-of-all-xlation-governing-entries-paddrs-from-all-xlation-governing-entries-paddrs-subset-p
               disjoint-p-append-2
               get-prefixes-alt-opener-lemma-zero-cnt

               open-qword-paddr-list-and-member-p
               unsigned-byte-p
               xlate-equiv-memory-and-xr-mem-from-rest-of-memory
               mv-nth-0-ia32e-la-to-pa-member-of-mv-nth-1-las-to-pas-if-lin-addr-member-p
               mv-nth-1-ia32e-la-to-pa-member-of-mv-nth-1-las-to-pas-if-lin-addr-member-p
               infer-disjointness-with-all-xlation-governing-entries-paddrs-from-gather-all-paging-structure-qword-addresses-1
               infer-disjointness-with-all-xlation-governing-entries-paddrs-from-gather-all-paging-structure-qword-addresses-2
               r-x-is-irrelevant-for-mv-nth-1-ia32e-la-to-pa-when-no-errors
               mv-nth-1-rb-and-xlate-equiv-memory-disjoint-from-paging-structures
               xlate-equiv-memory-with-mv-nth-2-las-to-pas

               all-xlation-governing-entries-paddrs-and-xw-mem-not-member

               xr-app-view-mv-nth-2-las-to-pas
               all-xlation-governing-entries-paddrs-and-xw-not-mem
               xr-seg-visible-mv-nth-2-las-to-pas
               xr-marking-view-mv-nth-2-las-to-pas
               disjoint-p
               member-p
               rewrite-get-prefixes-to-get-prefixes-alt
               create-canonical-address-list
               xlate-equiv-memory-and-two-get-prefixes-values
               xlate-equiv-memory-and-xr-mem-from-rest-of-memory
               rb-xw-values-in-app-view
               bitops::commutativity-2-of-logand
               mv-nth-1-las-to-pas-subset-p-disjoint-from-other-p-addrs
               get-prefixes-does-not-modify-x86-state-in-system-level-non-marking-view
               get-prefixes-does-not-modify-x86-state-in-app-view
               (:rewrite disjoint-p-all-xlation-governing-entries-paddrs-subset-p)
               (:definition disjoint-p$)
               (:rewrite mv-nth-0-las-to-pas-and-xw-mem-not-member)
               (:rewrite
                all-xlation-governing-entries-paddrs-subset-p-all-xlation-governing-entries-paddrs)
               (:rewrite subset-p-and-append-both)
               (:definition binary-append)
               (:rewrite subset-p-of-append-1)
               (:rewrite no-errors-when-translating-program-bytes-in-marking-view)
               (:type-prescription acl2::expt-type-prescription-integerp)
               (:rewrite not-member-p-when-disjoint-p)
               (:rewrite subset-p-cons-member-p-lemma)
               (:type-prescription disjoint-p$)
               (:rewrite mv-nth-2-ia32e-la-to-pa-system-level-non-marking-view)
               (:rewrite r/x-is-irrelevant-for-mv-nth-2-ia32e-la-to-pa-when-no-errors)
               (:rewrite r-w-x-is-irrelevant-for-mv-nth-1-las-to-pas-when-no-errors)
               (:rewrite xr-ia32e-la-to-pa)
               (:rewrite r-w-x-is-irrelevant-for-mv-nth-2-las-to-pas-when-no-errors)
               (:rewrite xr-and-ia32e-la-to-pa-in-non-marking-view)
               (:rewrite mv-nth-1-las-to-pas-subset-p)
               (:rewrite xr-mv-nth-2-ia32e-la-to-pa-when-error)
               (:rewrite one-read-with-rb-from-program-at-in-marking-view)
               (:rewrite many-reads-with-rb-from-program-at-in-marking-view)
               (:rewrite acl2::append-atom-under-list-equiv)
               (:type-prescription true-listp-of-las-to-pas.p-addrs)
               (:rewrite
                xlation-governing-entries-paddrs-subset-p-all-xlation-governing-entries-paddrs)
               (:linear size-of-rb-in-app-view)
               (:rewrite cdr-mv-nth-1-las-to-pas-no-error)
               (:type-prescription rm-low-64-logand-logior-helper-1)
               (:rewrite rb-returns-x86-in-non-marking-view-if-no-error)
               (:rewrite ia32e-la-to-pa-xw-state)
               (:rewrite rb-xw-state-in-app-view)
               (:rewrite subset-p-cons)
               (:rewrite
                infer-disjointness-with-all-xlation-governing-entries-paddrs-from-gather-all-paging-structure-qword-addresses-with-both-disjoint-p-and-disjoint-p$-and-subset-p)
               (:rewrite ia32e-la-to-pa-xw-values)
               acl2::zp-open
               not
               (:rewrite unsigned-byte-p-of-combine-bytes)
               (:rewrite acl2::ash-0)
               (:rewrite acl2::zip-open)
               (:linear ash-monotone-2)
               (:rewrite subset-p-cdr-y)
               (:rewrite default-<-2)
               (:rewrite negative-logand-to-positive-logand-with-integerp-x)
               (:meta acl2::cancel_plus-lessp-correct)
               (:rewrite member-p-canonical-address-listp)
               (:rewrite bitops::logtail-of-logior)
               (:definition member-equal)
               (:type-prescription bitops::logior-natp-type)
               (:rewrite loghead-of-non-integerp)
               (:rewrite unsigned-byte-p-of-logior)
               (:rewrite default-+-2)
               (:rewrite default-<-1)
               (:rewrite default-+-1)
               (:rewrite acl2::ifix-when-not-integerp)
               (:rewrite bitops::logtail-of-ash)
               (:linear member-p-pos-value)
               (:linear member-p-pos-1-value)
               (:definition byte-listp)
               (:rewrite default-cdr)
               (:rewrite bitops::loghead-of-logior)
               (:rewrite member-p-cdr)
               (:rewrite unsigned-byte-p-of-logtail)
               (:rewrite consp-mv-nth-1-las-to-pas)
               (:rewrite car-mv-nth-1-las-to-pas)
               (:rewrite default-car)
               (:rewrite unsigned-byte-p-of-logand-2)
               (:definition len)
               (:rewrite bitops::logtail-of-logand)
               (:type-prescription acl2::|x < y  =>  0 < -x+y|)
               (:rewrite get-prefixes-opener-lemma-no-prefix-byte)
               (:rewrite acl2::logtail-identity)
               (:rewrite acl2::zp-when-gt-0)
               (:rewrite bitops::logand-with-bitmask)
               (:linear mv-nth-1-idiv-spec)
               (:linear mv-nth-1-div-spec)
               (:type-prescription bitops::logand-natp-type-2)
               (:rewrite bitops::logsquash-cancel)
               (:meta acl2::cancel_times-equal-correct)
               (:meta acl2::cancel_plus-equal-correct)
               (:rewrite member-p-of-subset-is-member-p-of-superset)
               (:type-prescription bitops::logtail-natp)
               (:linear ia32e-la-to-pa-<-*mem-size-in-bytes-15*-when-low-12-bits-=-4081)
               (:linear ia32e-la-to-pa-<-*mem-size-in-bytes-1*-when-low-12-bits-=-4090)
               (:linear ia32e-la-to-pa-<-*mem-size-in-bytes-1*-when-low-12-bits-=-4089)
               (:definition n08p$inline)
               (:rewrite unsigned-byte-p-of-logand-1)
               (:rewrite rb-returns-no-error-app-view)
               (:rewrite bitops::loghead-of-logand)
               (:type-prescription consp-mv-nth-1-las-to-pas)
               (:type-prescription bitops::logand-natp-type-1)
               (:rewrite canonical-address-p-limits-thm-2)
               (:rewrite canonical-address-p-limits-thm-0)
               (:linear ia32e-la-to-pa-<-*mem-size-in-bytes-15*-when-low-12-bits-<-4081)
               (:linear ia32e-la-to-pa-<-*mem-size-in-bytes-1*-when-low-12-bits-<-4093)
               (:linear ia32e-la-to-pa-<-*mem-size-in-bytes-1*-when-low-12-bits-<-4089)
               (:linear
                ia32e-la-to-pa-<-*mem-size-in-bytes-1*-when-low-12-bits-!=-all-ones)
               (:rewrite bitops::logior-equal-0)
               (:rewrite ia32e-la-to-pa-in-app-view)
               (:rewrite subset-p-of-nil)
               (:linear acl2::expt->-1)
               (:type-prescription acl2::logtail-type)
               (:rewrite canonical-address-p-limits-thm-1)
               (:type-prescription zip)
               (:rewrite bitops::loghead-of-logsquash-commute)
               (:rewrite bitops::associativity-of-logand)
               (:type-prescription xw)
               (:rewrite canonical-address-p-limits-thm-3)
               (:rewrite unsigned-byte-p-of-logsquash)
               (:linear n52p-mv-nth-1-ia32e-la-to-pa)
               (:rewrite member-p-of-nil)
               (:linear bitops::logior-<-0-linear-2)
               (:rewrite bitops::logsquash-of-0-i)
               (:linear bitops::logior-<-0-linear-1)
               (:rewrite mv-nth-1-ia32e-la-to-pa-when-error)
               (:rewrite weed-out-irrelevant-logand-when-first-operand-constant)
               (:rewrite logand-redundant)
               (:type-prescription logtail-*2^x-byte-pseudo-page*-of-physical-address)
               (:rewrite subset-p-cdr-x)
               (:type-prescription n52p-mv-nth-1-ia32e-la-to-pa)
               (:linear <=-logior)
               (:linear prefixes-width-p-of-get-prefixes.new-prefixes)
               (:rewrite get-prefixes-opener-lemma-group-4-prefix)
               (:rewrite get-prefixes-opener-lemma-group-3-prefix)
               (:rewrite get-prefixes-opener-lemma-group-2-prefix)
               (:rewrite get-prefixes-opener-lemma-group-1-prefix)
               (:rewrite unsigned-byte-p-of-ash)
               (:linear bitops::logior->=-0-linear)
               (:definition n52p$inline)
               (:definition n55p$inline)
               (:rewrite bitops::logtail-of-logtail)
               (:rewrite mv-nth-2-las-to-pas-system-level-non-marking-view)
               (:rewrite mv-nth-1-las-to-pas-when-error)
               (:rewrite loghead-unequal)
               (:rewrite bitops::logand-fold-consts)
               (:rewrite rb-returns-x86-app-view)
               (:rewrite mv-nth-2-rb-in-system-level-non-marking-view)
               (:rewrite unsigned-byte-p-of-loghead)
               (:rewrite bitops::signed-byte-p-of-logtail)
               (:rewrite acl2::distributivity-of-minus-over-+)
               (:rewrite member-p-and-mult-8-qword-paddr-listp)
               (:rewrite acl2::natp-posp)
               (:rewrite bitops::logior-fold-consts)
               (:rewrite bitops::basic-unsigned-byte-p-of-+)
               (:rewrite rm-low-64-logand-logior-helper-1)
               (:rewrite acl2::posp-rw)
               (:type-prescription member-p-physical-address-p-physical-address-listp)
               (:type-prescription member-p-physical-address-p)
               (:definition n64p$inline)
               (:rewrite bitops::signed-byte-p-when-unsigned-byte-p-smaller)
               (:rewrite bitops::signed-byte-p-when-signed-byte-p-smaller)
               (:rewrite bitops::signed-byte-p-monotonicity)
               (:rewrite default-unary-minus)
               (:rewrite loghead-ash-0)
               (:rewrite acl2::expt-with-violated-guards)
               (:type-prescription bitops::lognot-negp)
               (:type-prescription all-xlation-governing-entries-paddrs)
               (:rewrite acl2::unsigned-byte-p-loghead)
               (:rewrite bitops::loghead-of-ash-same)
               (:type-prescription n52p$inline)
               (:type-prescription n55p$inline)
               (:type-prescription ash)
               (:rewrite bitops::loghead-of-0-i)
               (:rewrite acl2::equal-constant-+)
               (:linear acl2::expt-is-increasing-for-base>1)
               (:linear bitops::upper-bound-of-logior-for-naturals)
               (:rewrite bitops::logsquash-of-logsquash-2)
               (:rewrite bitops::logsquash-of-logsquash-1)
               (:linear n08p-mv-nth-1-rml08)
               (:type-prescription n64p$inline)
               (:rewrite bitops::logand-of-logand-self-1)
               (:type-prescription bitops::lognot-natp)
               (:type-prescription lognot)
               (:type-prescription acl2::expt-type-prescription-rationalp)
               (:linear bitops::expt-2-lower-bound-by-logbitp)
               (:rewrite acl2::natp-when-gte-0)
               (:rewrite acl2::natp-when-integerp)
               (:rewrite acl2::natp-rw)
               (:type-prescription bitops::part-install-width-low$inline)
               (:type-prescription bitops::natp-part-install-width-low)
               (:rewrite rewrite-rb-to-rb-alt)
               (:rewrite
                no-errors-when-translating-program-bytes-in-marking-view-using-program-at-alt)
               (:definition open-qword-paddr-list)
               (:definition addr-range)
               (:definition integer-listp)
               (:rewrite gather-all-paging-structure-qword-addresses-xw-fld=mem-disjoint)
               (:rewrite 64-bit-modep-of-rb)
               (:type-prescription gather-all-paging-structure-qword-addresses)
               (:type-prescription integer-listp)
               (:type-prescription open-qword-paddr-list)
               (:rewrite neg-addr-range=nil)
               (:rewrite
                infer-disjointness-with-all-xlation-governing-entries-paddrs-from-gather-all-paging-structure-qword-addresses-with-disjoint-p$)
               (:definition rme08$inline)
               (:rewrite car-cons)
               (:rewrite cdr-cons)
               (:rewrite disjointness-of-program-bytes-from-paging-structures)
               (:rewrite mv-nth-1-las-to-pas-and-xw-mem-not-member)
               (:rewrite subset-p-cons-2)
               (:rewrite canonical-address-p-limits-thm-4)
               (:definition ea-to-la$inline)
               (:type-prescription acl2::expt-type-prescription-nonzero)
               (:type-prescription acl2::expt-type-prescription-positive)
               (:rewrite
                gather-all-paging-structure-qword-addresses-mv-nth-2-ia32e-la-to-pa)
               (tau-system)))))

      (defthm get-prefixes-xw-mem-in-sys-view
        (implies
         (and
          (disjoint-p
           (mv-nth 1 (las-to-pas cnt start-rip :x (double-rewrite x86)))
           (all-xlation-governing-entries-paddrs
            cnt start-rip (double-rewrite x86)))
          (disjoint-p
           (list index)
           (mv-nth 1 (las-to-pas cnt start-rip :x (double-rewrite x86))))
          (disjoint-p
           (list index)
           (all-xlation-governing-entries-paddrs
            cnt start-rip (double-rewrite x86)))
          (not (mv-nth 0 (las-to-pas cnt start-rip :x (double-rewrite x86))))
          (posp cnt)
          (canonical-address-p start-rip)
          (canonical-address-p (+ -1 cnt start-rip))
          (physical-address-p index)
          (unsigned-byte-p 8 value)
          (64-bit-modep (double-rewrite x86))
          (not (app-view x86))
          (marking-view x86)
          (x86p x86))
         (and
          (equal
           (mv-nth
            0 (get-prefixes #.*64-bit-mode* start-rip prefixes rex-byte cnt
                            (xw :mem index value x86)))
           (mv-nth
            0 (get-prefixes #.*64-bit-mode* start-rip prefixes rex-byte cnt
                            (double-rewrite x86))))
          (equal
           (mv-nth
            1 (get-prefixes #.*64-bit-mode* start-rip prefixes rex-byte cnt
                            (xw :mem index value x86)))
           (mv-nth
            1 (get-prefixes #.*64-bit-mode* start-rip prefixes rex-byte cnt
                            (double-rewrite x86))))
          (equal
           (mv-nth
            2 (get-prefixes #.*64-bit-mode* start-rip prefixes rex-byte cnt
                            (xw :mem index value x86)))
           (mv-nth
            2 (get-prefixes #.*64-bit-mode* start-rip prefixes rex-byte cnt
                            (double-rewrite x86))))
          (equal
           (mv-nth
            3 (get-prefixes #.*64-bit-mode* start-rip prefixes rex-byte cnt
                            (xw :mem index value x86)))
           (xw :mem index value
               (mv-nth 3
                       (get-prefixes
                        #.*64-bit-mode* start-rip prefixes rex-byte cnt
                        (double-rewrite x86)))))))
        :hints
        (("Goal"
          :induct (list
                   (all-xlation-governing-entries-paddrs cnt start-rip x86)
                   (las-to-pas cnt start-rip :x x86)
                   (get-prefixes-two-x86-induct-hint
                    start-rip prefixes rex-byte cnt x86
                    (xw :mem index value x86)))
          :in-theory (e/d* (get-prefixes disjoint-p$ subset-p) ()))

         (if (equal (car id) '(0 1))

             '(:expand
               ((all-xlation-governing-entries-paddrs cnt start-rip x86)
                (all-xlation-governing-entries-paddrs 1 start-rip x86)
                (all-xlation-governing-entries-paddrs 1 start-rip (xw :mem index value x86))
                (las-to-pas cnt start-rip :x x86)
                (las-to-pas 1 start-rip :x (xw :mem index value x86))
                (las-to-pas 1 start-rip :x x86)
                (get-prefixes
                 #.*64-bit-mode* start-rip prefixes rex-byte cnt
                 (xw :mem index value x86))
                (get-prefixes
                 #.*64-bit-mode* start-rip prefixes rex-byte cnt x86))
               :in-theory
               (e/d* (get-prefixes disjoint-p$ subset-p disjoint-p-cons-1)
                     ()))
           nil))))

    (defthm get-prefixes-and-write-to-physical-memory
      (implies
       (and
        (disjoint-p
         (mv-nth 1 (las-to-pas cnt start-rip :x (double-rewrite x86)))
         (all-xlation-governing-entries-paddrs
          cnt start-rip (double-rewrite x86)))
        (disjoint-p
         p-addrs
         (mv-nth 1 (las-to-pas cnt start-rip :x (double-rewrite x86))))
        (disjoint-p
         p-addrs
         (all-xlation-governing-entries-paddrs
          cnt start-rip (double-rewrite x86)))
        (not (mv-nth 0 (las-to-pas cnt start-rip :x (double-rewrite x86))))
        (posp cnt)
        (canonical-address-p start-rip)
        (canonical-address-p (+ -1 cnt start-rip))
        (physical-address-listp p-addrs)
        (64-bit-modep (double-rewrite x86))
        (not (app-view x86))
        (marking-view x86)
        (x86p x86))
       (and
        (equal
         (mv-nth 0 (get-prefixes
                    #.*64-bit-mode* start-rip prefixes rex-byte cnt
                    (write-to-physical-memory p-addrs value x86)))
         (mv-nth 0 (get-prefixes
                    #.*64-bit-mode* start-rip prefixes rex-byte cnt
                    (double-rewrite x86))))
        (equal
         (mv-nth 1 (get-prefixes
                    #.*64-bit-mode* start-rip prefixes rex-byte cnt
                    (write-to-physical-memory p-addrs value x86)))
         (mv-nth 1 (get-prefixes
                    #.*64-bit-mode* start-rip prefixes rex-byte cnt
                    (double-rewrite x86))))
        (equal
         (mv-nth 2 (get-prefixes
                    #.*64-bit-mode* start-rip prefixes rex-byte cnt
                    (write-to-physical-memory p-addrs value x86)))
         (mv-nth 2 (get-prefixes
                    #.*64-bit-mode* start-rip prefixes rex-byte cnt
                    (double-rewrite x86))))
        (equal
         (mv-nth 3 (get-prefixes
                    #.*64-bit-mode* start-rip prefixes rex-byte cnt
                    (write-to-physical-memory p-addrs value x86)))
         (write-to-physical-memory p-addrs value
                                   (mv-nth
                                    3
                                    (get-prefixes
                                     #.*64-bit-mode*
                                     start-rip prefixes rex-byte cnt x86))))))
      :hints
      (("Goal"
        :induct (write-to-physical-memory p-addrs value x86)
        :in-theory
        (e/d* (gather-all-paging-structure-qword-addresses-xw-fld=mem-disjoint
               disjoint-p
               byte-listp
               n08p)
              (rewrite-get-prefixes-to-get-prefixes-alt
               las-to-pas-values-and-write-to-physical-memory-disjoint
               xlate-equiv-memory-and-two-get-prefixes-values)))))

    (defthm get-prefixes-alt-and-write-to-physical-memory-disjoint-from-paging-structures
      (implies
       (and
        (disjoint-p
         p-addrs
         (mv-nth 1 (las-to-pas cnt start-rip :x (double-rewrite x86))))
        (disjoint-p$
         p-addrs
         (open-qword-paddr-list
          (gather-all-paging-structure-qword-addresses (double-rewrite x86))))
        (posp cnt)
        (canonical-address-p (+ -1 cnt start-rip))
        (physical-address-listp p-addrs)
        (x86p x86))
       (and
        (equal
         (mv-nth
          0 (get-prefixes-alt start-rip prefixes rex-byte cnt
                              (write-to-physical-memory p-addrs value x86)))
         (mv-nth
          0 (get-prefixes-alt start-rip prefixes rex-byte cnt
                              (double-rewrite x86))))
        (equal
         (mv-nth
          1 (get-prefixes-alt start-rip prefixes rex-byte cnt
                              (write-to-physical-memory p-addrs value x86)))
         (mv-nth
          1 (get-prefixes-alt start-rip prefixes rex-byte cnt
                              (double-rewrite x86))))

        (equal
         (mv-nth 2 (get-prefixes-alt start-rip prefixes rex-byte cnt
                                     (write-to-physical-memory p-addrs value x86)))
         (mv-nth 2 (get-prefixes-alt start-rip prefixes rex-byte cnt
                                     (double-rewrite x86))))
        (equal
         (mv-nth 3 (get-prefixes-alt start-rip prefixes rex-byte cnt
                                     (write-to-physical-memory p-addrs value x86)))
         (write-to-physical-memory
          p-addrs value
          (mv-nth 3 (get-prefixes-alt
                     start-rip prefixes rex-byte cnt x86))))))
      :hints
      (("Goal"
        :do-not-induct t
        :use ((:instance get-prefixes-and-write-to-physical-memory)
              (:instance all-xlation-governing-entries-paddrs-subset-of-paging-structures
                         (n cnt) (addr start-rip)))
        :in-theory
        (e/d*
         (get-prefixes-alt
          subset-p
          disjoint-p$
          disjoint-p-commutative
          disjoint-p-subset-p)
         (disjointness-of-all-xlation-governing-entries-paddrs-from-all-xlation-governing-entries-paddrs-subset-p
          disjoint-p-all-xlation-governing-entries-paddrs-subset-p
          mv-nth-1-las-to-pas-subset-p-disjoint-from-other-p-addrs
          rewrite-get-prefixes-to-get-prefixes-alt
          get-prefixes-and-write-to-physical-memory
          xlate-equiv-memory-and-two-get-prefixes-values
          mv-nth-1-rb-and-xlate-equiv-memory-disjoint-from-paging-structures
          all-xlation-governing-entries-paddrs-subset-of-paging-structures
          open-qword-paddr-list
          force (force))))))

    (defthm get-prefixes-alt-and-wb-in-system-level-marking-view-disjoint-from-paging-structures
      (implies
       (and
        (disjoint-p$
         (mv-nth 1 (las-to-pas n-w write-addr :w (double-rewrite x86)))
         (open-qword-paddr-list
          (gather-all-paging-structure-qword-addresses (double-rewrite x86))))
        (disjoint-p
         (mv-nth 1 (las-to-pas n-w write-addr :w (double-rewrite x86)))
         (mv-nth 1 (las-to-pas cnt start-rip :x (double-rewrite x86))))
        (posp cnt)
        (canonical-address-p (+ -1 cnt start-rip))
        (64-bit-modep (double-rewrite x86))
        (not (app-view x86))
        (x86p x86))
       (and
        (equal
         (mv-nth
          0 (get-prefixes-alt start-rip prefixes rex-byte cnt
                              (mv-nth 1 (wb n-w write-addr w value x86))))
         (mv-nth
          0 (get-prefixes-alt start-rip prefixes rex-byte cnt (double-rewrite x86))))
        (equal
         (mv-nth
          1 (get-prefixes-alt start-rip prefixes rex-byte cnt
                              (mv-nth 1 (wb n-w write-addr w value x86))))
         (mv-nth
          1 (get-prefixes-alt start-rip prefixes rex-byte cnt
                              (double-rewrite x86))))
        (equal
         (mv-nth
          2 (get-prefixes-alt start-rip prefixes rex-byte cnt
                              (mv-nth 1 (wb n-w write-addr w value x86))))
         (mv-nth
          2 (get-prefixes-alt start-rip prefixes rex-byte cnt (double-rewrite x86))))))
      :hints (("Goal"
               :do-not-induct t
               :in-theory
               (e/d* (las-to-pas
                      disjoint-p$
                      wb
                      disjoint-p-commutative
                      infer-disjointness-with-all-xlation-governing-entries-paddrs-from-gather-all-paging-structure-qword-addresses-1
                      infer-disjointness-with-all-xlation-governing-entries-paddrs-from-gather-all-paging-structure-qword-addresses-2
                      xlate-equiv-memory-with-mv-nth-2-las-to-pas)
                     (rewrite-get-prefixes-to-get-prefixes-alt
                      xlate-equiv-memory-and-two-get-prefixes-values
                      xlate-equiv-memory-and-xr-mem-from-rest-of-memory)))))

    (defthm get-prefixes-alt-and-write-to-physical-memory-paging-structures
      (implies
       (and
        (equal p-addrs (addr-range 8 index))
        (disjoint-p
         (mv-nth 1 (las-to-pas cnt start-rip :x (double-rewrite x86)))
         (open-qword-paddr-list
          (gather-all-paging-structure-qword-addresses (double-rewrite x86))))
        (disjoint-p
         p-addrs
         (mv-nth 1 (las-to-pas cnt start-rip :x (double-rewrite x86))))
        (disjoint-p$
         p-addrs
         (all-xlation-governing-entries-paddrs
          cnt start-rip (double-rewrite x86)))
        (equal (page-size (double-rewrite value)) 1)
        (posp cnt)
        (canonical-address-p (+ -1 cnt start-rip))
        (physical-address-listp p-addrs)
        (unsigned-byte-p 64 value)
        (physical-address-p index)
        (equal (loghead 3 index) 0)
        (x86p x86))
       (and
        (equal
         (mv-nth
          0 (get-prefixes-alt start-rip prefixes rex-byte cnt
                              (write-to-physical-memory p-addrs value x86)))
         (mv-nth 0 (get-prefixes-alt start-rip prefixes rex-byte cnt
                                     (double-rewrite x86))))
        (equal
         (mv-nth
          1 (get-prefixes-alt start-rip prefixes rex-byte cnt
                              (write-to-physical-memory p-addrs value x86)))
         (mv-nth 1 (get-prefixes-alt start-rip prefixes rex-byte cnt (double-rewrite x86))))

        (equal
         (mv-nth 2 (get-prefixes-alt start-rip prefixes rex-byte cnt
                                     (write-to-physical-memory p-addrs value x86)))
         (mv-nth 2 (get-prefixes-alt start-rip prefixes rex-byte cnt (double-rewrite x86))))))
      :hints
      (("Goal"
        :do-not-induct t
        :use
        ((:instance get-prefixes-and-write-to-physical-memory)
         (:instance all-xlation-governing-entries-paddrs-subset-of-paging-structures
                    (n cnt) (addr start-rip))
         (:instance disjointness-of-las-to-pas-from-write-to-physical-memory-subset-of-paging-structures
                    (index index)
                    (p-addrs (addr-range 8 index))
                    (n cnt) (lin-addr start-rip)
                    (r-x :x)))
        :in-theory
        (e/d*
         (get-prefixes-alt
          subset-p
          disjoint-p$
          disjoint-p-subset-p)
         (disjointness-of-las-to-pas-from-write-to-physical-memory-subset-of-paging-structures
          rewrite-get-prefixes-to-get-prefixes-alt
          get-prefixes-and-write-to-physical-memory
          xlate-equiv-memory-and-two-get-prefixes-values
          mv-nth-1-rb-and-xlate-equiv-memory-disjoint-from-paging-structures
          all-xlation-governing-entries-paddrs-subset-of-paging-structures
          mv-nth-1-las-to-pas-subset-p-disjoint-from-other-p-addrs
          mv-nth-0-las-to-pas-subset-p
          cdr-mv-nth-1-las-to-pas-no-error
          mv-nth-0-ia32e-la-to-pa-member-of-mv-nth-1-las-to-pas-if-lin-addr-member-p
          force (force))))))

    (defthm get-prefixes-alt-and-wb-to-paging-structures
      (implies
       (and
        (equal (page-size (double-rewrite value)) 1)
        (direct-map-p 8 lin-addr :w (double-rewrite x86))
        (disjoint-p
         (mv-nth 1 (las-to-pas cnt start-rip :x (double-rewrite x86)))
         (open-qword-paddr-list
          (gather-all-paging-structure-qword-addresses (double-rewrite x86))))
        (disjoint-p
         (mv-nth 1 (las-to-pas 8 lin-addr :w (double-rewrite x86)))
         (all-xlation-governing-entries-paddrs
          cnt start-rip (double-rewrite x86)))
        (disjoint-p
         (mv-nth 1 (las-to-pas 8 lin-addr :w (double-rewrite x86)))
         (mv-nth 1 (las-to-pas cnt start-rip :x (double-rewrite x86))))
        (posp cnt)
        (canonical-address-p (+ -1 cnt start-rip))
        (physical-address-p lin-addr)
        (equal (loghead 3 lin-addr) 0)
        (canonical-address-p lin-addr)
        (unsigned-byte-p 64 value)
        (64-bit-modep (double-rewrite x86))
        (not (app-view x86))
        (x86p x86))
       (and
        (equal
         (mv-nth
          0 (get-prefixes-alt start-rip prefixes rex-byte cnt
                              (mv-nth 1 (wb 8 lin-addr w value x86))))
         (mv-nth 0 (get-prefixes-alt start-rip prefixes rex-byte cnt
                                     (double-rewrite x86))))
        (equal
         (mv-nth
          1 (get-prefixes-alt start-rip prefixes rex-byte cnt
                              (mv-nth 1 (wb 8 lin-addr w value x86))))
         (mv-nth 1 (get-prefixes-alt start-rip prefixes rex-byte cnt
                                     (double-rewrite x86))))
        (equal
         (mv-nth 2 (get-prefixes-alt start-rip prefixes rex-byte cnt
                                     (mv-nth 1 (wb 8 lin-addr w value x86))))
         (mv-nth 2 (get-prefixes-alt start-rip prefixes rex-byte cnt
                                     (double-rewrite x86))))))
      :hints (("Goal"
               :do-not-induct t
               :use
               ((:instance
                 get-prefixes-alt-and-write-to-physical-memory-paging-structures
                 (index lin-addr)
                 (p-addrs (mv-nth 1 (las-to-pas 8 lin-addr :w x86)))
                 (value value)
                 (x86 (mv-nth 2 (las-to-pas 8 lin-addr :w x86)))))
               :in-theory
               (e/d* (direct-map-p
                      get-prefixes-alt-and-write-to-physical-memory-paging-structures
                      acl2::loghead-identity
                      acl2::fold-consts-in-+
                      disjoint-p$
                      wb
                      xlate-equiv-memory-with-mv-nth-2-las-to-pas
                      acl2::mv-nth-cons-meta)
                     (las-to-pas
                      rewrite-get-prefixes-to-get-prefixes-alt
                      subset-p
                      mv-nth-0-las-to-pas-subset-p
                      mv-nth-0-ia32e-la-to-pa-member-of-mv-nth-1-las-to-pas-if-lin-addr-member-p
                      xlate-equiv-memory-and-two-get-prefixes-values
                      xlate-equiv-memory-and-xr-mem-from-rest-of-memory
                      mv-nth-1-las-to-pas-subset-p-disjoint-from-other-p-addrs
                      write-to-physical-memory-and-mv-nth-2-las-to-pas-commute
                      infer-disjointness-with-all-xlation-governing-entries-paddrs-from-gather-all-paging-structure-qword-addresses-1
                      infer-disjointness-with-all-xlation-governing-entries-paddrs-from-gather-all-paging-structure-qword-addresses-2)))))))

;; ======================================================================

;; Step function opener lemma:

(defthm x86-fetch-decode-execute-opener-in-marking-view
  ;; Note that we use get-prefixes-alt here instead of get-prefixes.
  ;; TODO: Extend to VEX and EVEX prefixes when necessary.
  (implies
   (and
    ;; Start: binding hypotheses.
    (equal start-rip (rip x86))
    ;; get-prefixes-alt:
    (equal four-vals-of-get-prefixes (get-prefixes-alt start-rip 0 0 15 x86))
    (equal flg-get-prefixes (mv-nth 0 four-vals-of-get-prefixes))
    (equal prefixes (mv-nth 1 four-vals-of-get-prefixes))
    (equal rex-byte (mv-nth 2 four-vals-of-get-prefixes))
    (equal x86-1 (mv-nth 3 four-vals-of-get-prefixes))

    (equal opcode/vex/evex-byte (prefixes->nxt prefixes))
    (equal prefix-length (prefixes->num prefixes))
    (equal temp-rip0 (+ prefix-length start-rip 1))

    ;; *** No VEX prefixes ***
    (not (equal opcode/vex/evex-byte #.*vex3-byte0*))
    (not (equal opcode/vex/evex-byte #.*vex2-byte0*))
    ;; *** No EVEX prefixes ***
    (not (equal opcode/vex/evex-byte #.*evex-byte0*))

    (equal modr/m?
           (one-byte-opcode-ModR/M-p #.*64-bit-mode* opcode/vex/evex-byte))

    ;; modr/m byte:
    (equal three-vals-of-modr/m
           (if modr/m? (rml08 temp-rip0 :x x86-1) (mv nil 0 x86-1)))
    (equal flg-modr/m (mv-nth 0 three-vals-of-modr/m))
    (equal modr/m (mv-nth 1 three-vals-of-modr/m))
    (equal x86-2 (mv-nth 2 three-vals-of-modr/m))

    (equal temp-rip1 (if modr/m? (1+ temp-rip0) temp-rip0))
    (equal sib? (and modr/m? (x86-decode-sib-p modr/m nil)))

    ;; sib byte:
    (equal three-vals-of-sib
           (if sib? (rml08 temp-rip1 :x x86-2) (mv nil 0 x86-2)))
    (equal flg-sib (mv-nth 0 three-vals-of-sib))
    (equal sib (mv-nth 1 three-vals-of-sib))
    (equal x86-3 (mv-nth 2 three-vals-of-sib))

    (equal temp-rip2 (if sib? (1+ temp-rip1) temp-rip1))
    ;; End: binding hypotheses.

    (marking-view x86)
    (64-bit-modep (double-rewrite x86))
    (not (app-view x86))
    (not (ms x86))
    (not (fault x86))
    (x86p x86)
    (not (double-rewrite flg-get-prefixes))
    (canonical-address-p temp-rip0)
    (if modr/m?
        (and (not (double-rewrite flg-modr/m))
             (canonical-address-p temp-rip1))
      t)
    (if sib?
        (and (not (double-rewrite flg-sib))
             (canonical-address-p temp-rip2))
      t)
    ;; For get-prefixes-alt (we wouldn't need these hyps if we
    ;; used get-prefixes):
    (disjoint-p
     (mv-nth 1 (las-to-pas 15 (xr :rip 0 x86) :x (double-rewrite x86)))
     (open-qword-paddr-list
      (gather-all-paging-structure-qword-addresses (double-rewrite x86))))
    (not (mv-nth 0 (las-to-pas 15 (xr :rip 0 x86) :x (double-rewrite x86))))

    ;; Print the rip and the first opcode byte of the instruction
    ;; under consideration after all the non-trivial hyps (above) of
    ;; this rule have been relieved:
    (syntaxp (and (not (cw "~% [ x86instr @ rip: ~p0 ~%" start-rip))
                  (not (cw "              op0: ~s0 ] ~%"
                           (str::hexify (unquote opcode/vex/evex-byte)))))))
   (equal (x86-fetch-decode-execute x86)
          (one-byte-opcode-execute
           #.*64-bit-mode* start-rip temp-rip2 prefixes rex-byte
           opcode/vex/evex-byte modr/m sib x86-3)))
  :hints
  (("Goal"
    :do-not '(preprocess)
    :in-theory
    (e/d (x86-fetch-decode-execute
          get-prefixes-alt
          x86-operation-mode)
         (rewrite-get-prefixes-to-get-prefixes-alt
          one-byte-opcode-execute
          xlate-equiv-memory-and-mv-nth-0-rml08-cong
          xlate-equiv-memory-and-two-mv-nth-2-rml08-cong
          xlate-equiv-memory-and-mv-nth-2-rml08
          signed-byte-p
          not
          member-equal
          mv-nth-1-las-to-pas-subset-p-disjoint-from-other-p-addrs
          remove-duplicates-equal
          combine-bytes
          byte-listp
          acl2::ash-0
          open-qword-paddr-list
          unsigned-byte-p-of-combine-bytes
          get-prefixes-opener-lemma-no-prefix-byte
          get-prefixes-opener-lemma-group-1-prefix-in-marking-view
          get-prefixes-opener-lemma-group-2-prefix-in-marking-view
          get-prefixes-opener-lemma-group-3-prefix-in-marking-view
          get-prefixes-opener-lemma-group-4-prefix-in-marking-view
          mv-nth-0-rb-and-mv-nth-0-las-to-pas-in-sys-view
          mv-nth-2-rb-in-system-level-marking-view
          (force) force)))))

;; ======================================================================
