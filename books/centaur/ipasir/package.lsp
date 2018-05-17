; IPASIR - Link from ACL2 to IPASIR incremental sat solvers
; Copyright (C) 2017 Centaur Technology
;
; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/
;
; License: (An MIT/X11-style license)
;
;   Permission is hereby granted, free of charge, to any person obtaining a
;   copy of this software and associated documentation files (the "Software"),
;   to deal in the Software without restriction, including without limitation
;   the rights to use, copy, modify, merge, publish, distribute, sublicense,
;   and/or sell copies of the Software, and to permit persons to whom the
;   Software is furnished to do so, subject to the following conditions:
;
;   The above copyright notice and this permission notice shall be included in
;   all copies or substantial portions of the Software.
;
;   THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
;   IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
;   FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
;   AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
;   LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
;   FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
;   DEALINGS IN THE SOFTWARE.
;
; Original authors: Sol Swords <sswords@centtech.com>

(in-package "ACL2")

(include-book "std/portcullis" :dir :system)
(include-book "oslib/portcullis" :dir :system)
(include-book "centaur/satlink/portcullis" :dir :system)

(defpkg "IPASIR"
  (append '(b*
            bitp
            lnfix
            lbfix
            bfix
            b-not
            b-and
            b-ior
            b-xor
            b-eqv
            b-ite
            bool->bit
            bit->bool
            defxdoc
            defsection
            defstobj-clone
            list-fix
            list-equiv
            set-equiv
            nat-equiv
            bit-equiv
            bits-equiv
            rev
            duplicity
            alist-keys
            alist-vals
            hons-remove-duplicates
            set-reasoning
            enable*
            disable*
            e/d*
            bitarr get-bit set-bit bits-length resize-bits bits-equiv
            natarr get-nat set-nat nats-length resize-nats nats-equiv
            tshell-call tshell-start tshell-stop tshell-ensure
            satlink boolean-reasoning gl tshell)
          std::*std-exports*
          satlink::*satlink-exports*
          (remove-eq 'clause acl2::*standard-acl2-imports*)))

(defconst *ipasir-exports*
  #!ipasir
  '(ipasir
    ipasirp
    create-ipasir
    ipasir-init
    ipasir-reinit
    ipasir-release
    ipasir-input
    ipasir-add-lit
    ipasir-finalize-clause
    ipasir-assume
    ipasir-val
    ipasir-failed
    ipasir-solve
    ipasir-set-limit
    ipasir-callback-count
    with-local-ipasir
    ipasir$a
    ipasir$a->formula
    ipasir$a->assumption
    ipasir$a->new-clause
    ipasir$a->status
    ipasir$a->solution
    ipasir$a->solved-assumption
    ipasir$a->callback-count
    ipasir$a->history
    ipasir-cancel-new-clause
    ipasir-cancel-assumption
    ipasir-add-empty
    ipasir-add-unary
    ipasir-add-binary
    ipasir-add-ternary
    ipasir-add-4ary
    ipasir-add-list
    ipasir-add-clauses
    ipasir-set-buf
    ipasir-set-and
    ipasir-set-or
    ipasir-set-mux
    ipasir-set-xor
    ipasir-set-iff
    ipasir-check-equivalence))

