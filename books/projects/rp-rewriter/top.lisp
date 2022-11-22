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
(include-book "meta-rule-macros")
(include-book "misc")

(include-book "user-lemmas")

(include-book "meta/top")

(include-book "xdoc/top" :dir :system)

               
(xdoc::defxdoc rp-rewriter
  :parents (acl2::projects acl2::clause-processor-tools)
  :short "A verified clause-processor and customized rewriter for large terms
  that uses existing ACL2 rewrite rules to prove theorems."
  :long
  "<p>RP-Rewriter (rp for 'retain property') is a verified clause processor
  that can be used to replace ACL2's rewriter for some theorems, and for some
  cases, can provide time efficiency and convenience when building lemmas. It
  uses a subset of the heuristics of the ACL2's rewriter but has some
  distinctive features:</p>

<ol>
 <li> By introducing an invariant, it can retain
  properties about terms, which we call side-conditions. These properties can
 help relieve hypotheses or be used in meta functions even after large terms
 went through drastic changes through rewriting that may have made it difficult
 to confirm those properties through regular hyp relief system.
 </li>
<li> In the case of
  alists in the theorems to be rewritten, it can create a corresponding
  fast-alist in the background for later fast search and access. It does that
 by triggering a special mechanism when it encounters @(see hons-acons) and
 @(see hons-get) in terms. </li>
<li> Meta rules can return a @(see dont-rw) structure to prevent repeated rewriting of large
   returned terms, which can provide large performance (time and memory)
  benefits. </li>
<li> It supports inside-out as well as outside-in rewriting in the same
  rewriting pass. </li>
</ol>


 <p> The rewriter supports a big set of rewrite rules existing in
  ACL2's world. For every other rule-classes, it treats
  them as rewrite-rules if possible.  It also provides a mechanism to run meta
  functions. We do not support rules with @(see bind-free), @(see
  acl2::loop-stopper), @(see acl2::free-variables), @(see
  case-split) etc. Note that there is also no @(see acl2::type-alist) or any
  form of type reasoning.  </p>


<p> This rewriter is mainly used by an efficient integer @(see
multiplier-verification) library. </p>

<p> Two papers are published that mainly discuss RP-Rewriter: </p>

<ul>
<li> (<a
href=\"https://doi.org/10.48550/arXiv.2009.13765\">
RP-Rewriter: An Optimized Rewriter for Large Terms in ACL2</a>)
</li>

<li>
(<a
href=\"https://doi.org/10.48550/arXiv.2205.11703\">
Verified Implementation of an Efficient Term-Rewriting Algorithm for Multiplier Verification on ACL2
</a>)
</li>

</ul>
")


(xdoc::defxdoc
 rp-utilities
 :parents (rp-rewriter)
 :short "Some useful tools for rp-rewriter")

(xdoc::defxdoc
 rp-rewriter/applications
 :parents (rp-rewriter)
 :short "Applications of RP-Rewriter")

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


(xdoc::defxdoc
 rp-rewriter-demo
 :parents (rp-rewriter)
 :short "A demo and a case where side-conditions of RP-Rewriter are used."
 :long "
<p> Below is a list of events where we use the side-conditions feature of
 RP-Rewriter to verify a conjecture. </p> 
<p> This documentation is still under construction, please see
 books/projects/rp-rewriter/demo.lsp for the demo events.
</p>")

               
