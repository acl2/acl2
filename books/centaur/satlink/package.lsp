; SATLINK - Link from ACL2 to SAT Solvers
; Copyright (C) 2013 Centaur Technology
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
; Original authors: Jared Davis <jared@centtech.com>
;                   Sol Swords <sswords@centtech.com>

(in-package "ACL2")

(include-book "std/portcullis" :dir :system)
(include-book "oslib/portcullis" :dir :system)

(defpkg "SATLINK"
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
          acl2::*standard-acl2-imports*))

(defpkg "DIMACS"
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
            bool->bit
            bit->bool
            defxdoc
            defsection
            satlink::satlink-to-dimacs-lit
            satlink::dimacs-to-satlink-lit)
          std::*std-exports*
          acl2::*standard-acl2-imports*))

(defconst satlink::*satlink-exports*
  #!satlink
  '(litp make-lit lit->var lit->neg ;; var->index make-var
         lit-to-dimacs
         eval-var eval-lit eval-clause eval-cube
         eval-formula lit-listp lit-list-fix lit-list-listp lit-list-list-fix env$
         var-equiv var-fix ;; to-lit lit-val
         lit-fix lit-equiv lit lit-negate
         lit-negate-cond lit->index
         max-index-clause max-index-formula clause-indices formula-indices
         satlink-to-dimacs-lit
         dimacs-to-satlink-lit
         lit->var^ lit->neg^ make-lit^ lit-negate^ lit-negate-cond^
         lit-abs lit-abs^))
