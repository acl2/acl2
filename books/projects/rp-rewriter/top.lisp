; RP-REWRITER

; Note: The license below is based on the template at:
; http://opensource.org/licenses/BSD-3-Clause

; Copyright (C) 2019, Regents of the University of Texas
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
; Mertcan Temel         <mert@utexas.edu>

(in-package "RP")

(include-book "proofs/guards")

(include-book "cl-correct")
(include-book "add-meta-rule-formula-checks")
(include-book "misc")

(include-book "user-lemmas")
(include-book "proofs/useful-lemmas")

(include-book "meta/top")

(include-book "xdoc/top" :dir :system)

(xdoc::defxdoc rp-rewriter
  :parents (acl2::projects acl2::clause-processor-tools)
  :short "A customized rewriter for large terms that uses existing ACL2 rewrite
  rules to prove theorems."
  :long
  "<p>RP-rewriter (rp for 'retain property') is a verified clause processor
  that can be used to replace ACL2's rewriter for some theorems, and for some
  cases, can provide time efficieny and conveinence when building lemmas. It
  uses a subset of the heuristics of the ACL2's rewriter but adds two
  distintive features: 1. By introducing an invariant, it can retain properties
  about terms. 2. In the case of alists in the theorems to be rewritten, it can
  create a corresponding fast-alist in the background.</p> <p> It supports a
  big set of rewrite rules existing in ACL2's world that may have syntaxp.
  However, it ignores definition rules for recursive functions, treating the
  rest of the definitions as well as type-prescription rules as rewrite
  rules. It also provides a mechanism to run meta functions. The rest of the
  rule classes are not supported and are discarded by the rewriter. We also do
  not support rules with @(see bind-free), @(see acl2::loop-stopper), @(see
  acl2::free-variables), @(see force), @(see case-split) etc. Note that there
  is also no @(see acl2::type-alist) or any form of type reasoning.  </p> <p>
  The rewriter enables users to attach certain properties to terms as rewriting
  takes places. These properties can be used to quickly relieve
  hypothesis. This is especially handy if backchaining is too slow.</p> <p> If
  a rewrite rule has @(see hons-acons) on its right hand side, rp-rewriter has
  a built-in meta function ath uses this as a trigger function to create a
  fast-alist in the background. When another term seems to be trying to read a
  value from that alist with a known instance of a function such as
  assoc-equal, the built in meta functions reads the value from the
  corresponding fast-alist instead of tracing it in the logical term. This may
  give great timing benefits when dealing with terms with large alists. </p>")

#|
(xdoc::defsection RP-Rewriter-Simple-Tutorial
  :parents (RP-Rewriter)
  :short "An example showing how the rewriter works without any of its special features"
  :long "Some stuff")

(xdoc::defsection RP-Rewriter-Side-Conditions-Tutorial
  :parents (RP-Rewriter)
  :short "Attaching the properties/side-conditions to terms for fast hypothesis
  relief."
  :long "Not Ready Yet")

(xdoc::defsection RP-Rewriter-Fast-Alist-Tutorial
  :parents (RP-Rewriter)
  :short "Creating fast-alists in the background for theorems with alist terms."
  :long "Not Ready Yet")

(xdoc::defsection RP-Rewriter-Adding-Meta-Rules
  :parents (RP-Rewriter)
  :short "Extra steps needed to add meta functions are described on an example."
  :long "Not Ready Yet")||#
