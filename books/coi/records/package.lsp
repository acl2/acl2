; Computational Object Inference
; Copyright (C) 2005-2014 Kookamara LLC
;
; Contact:
;
;   Kookamara LLC
;   11410 Windermere Meadows
;   Austin, TX 78759, USA
;   http://www.kookamara.com/
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

#!ACL2 (in-package "ACL2")

(include-book "../lists/portcullis")
(include-book "../alists/portcullis")
(include-book "../symbol-fns/portcullis")
(include-book "../bags/portcullis")
(include-book "../adviser/portcullis")
(include-book "std/portcullis" :dir :system)
(include-book "data-structures/memories/portcullis" :dir :system)

(defconst *record-exports*
  `(
    g
    s
    wfkey
    wfkeys
    wfr
    defrecord

    g-of-s-redux
    s-diff-s

    ))

(defpkg "REC" ;(remove-duplicates-eql ;no longer necessary due to change in ACL2
               `(,@ACL2::*acl2-exports*
                 ,@ACL2::*common-lisp-symbols-from-main-lisp-package*
                 ,@ACL2::*record-exports*
                 ACL2::acl2->rcd ACL2::rcd->acl2
                 ACL2::s-aux ACL2::g-aux
                 ACL2::ifrp ACL2::rcdp
                 ACL2::<<
                 )
;               )
               )


;; (defpkg "GR" nil)

;; (defpkg "PATH" (remove-duplicates-eql
;; 		`(SYN::defignore
;; 		  SYN::defignored
;; 		  SYN::defirrelevant
;; 		  ,@ACL2::*record-exports*
;; 		  ,@LIST::*exports*
;; 		  ,@ACL2::*acl2-exports*
;; 		  ,@ACL2::*common-lisp-symbols-from-main-lisp-package*
;;                   )))
