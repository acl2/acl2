; GL - A Symbolic Simulation Framework for ACL2

; Note: The license below is based on the template at:
; http://opensource.org/licenses/BSD-3-Clause

; Copyright (C) 2015, Regents of the University of Texas
; Copyright (C) 2018, Kestrel Technology, LLC
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
; Warren A. Hunt, Jr. <hunt@cs.utexas.edu>
; Matt Kaufmann       <kaufmann@cs.utexas.edu>
; Contributing Author(s):
; Alessandro Coglio   <coglio@kestrel.edu>

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "GL")

(include-book "def-gl-rule")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc defthm-using-gl
  :parents (def-gl-thm)
  :short "Prove a theorem using GL, including GL only locally."
  :long
  "<p>
   This macro generates
   (1) a local theorem proved via GL and
   (2) a non-local theorem proved trivially from the previous one.
   GL must be included at least locally
   in order for the first theorem to work,
   but GL may be included just locally,
   and the second theorem will work.
   This helps reduce dependencies among books.
   </p>
   @(def defthm-using-gl)")

(defmacro defthm-using-gl (name &key hyp concl g-bindings rule-classes)
  (if (and hyp concl g-bindings)
      (let ((gl-name (acl2::add-suffix name "-GL")))
        `(progn
           (gl::def-gl-ruledl
            ,gl-name
            :hyp ,hyp
            :concl ,concl
            :g-bindings ,g-bindings)
           (defthm ,name
             (implies ,hyp ,concl)
             :hints (("Goal" :in-theory (theory 'minimal-theory)
                      :use ((:instance ,gl-name))))
             :rule-classes ,(or rule-classes :rewrite))))
    nil))
