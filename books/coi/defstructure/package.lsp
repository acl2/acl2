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

(in-package "ACL2")

; The following comment line tells the build system that if *acl2-exports*
; changes, then every book that uses this file should be recertified:
; (depends-on "build/acl2-exports.certdep" :dir :system)

(include-book "../symbol-fns/portcullis")
(include-book "../records/portcullis")
(include-book "../paths/portcullis")

;; Define the STRUCTURES package (and the U package).  The STRUCTURES and U packages are stolen from the books/
;; directory and put here so that we can modify them and refer to them more easily.  (We like to ld the books which
;; contain defpkgs, but we have no way to easily ld a book from the books/ directory without using an absolute
;; pathname.)   
;;-- Now we do, with :dir support on LDs in ACL2 version 2.9.3.  So I'm trying to make use of that   -ews

(include-book "data-structures/portcullis" :dir :system)

;; (defpkg "U" (union-eq *acl2-exports*
;;                       *common-lisp-symbols-from-main-lisp-package*))

;This differs somewhat from the version in books/data-structures/define-structures-package.lisp.  -ews

(defpkg "STRUCTURES"
  (union-eq
   symbol-fns::*symbol-fns-exports*
   (union-eq
    '(DEFSTRUCTURE DEFSTRUCTURE+) ;The main macros exported by defstructure.lisp
    (union-eq
     *acl2-exports*
     (union-eq
      *common-lisp-symbols-from-main-lisp-package*
      '(

	acl2::wfr

	cpath::sp
	cpath::gp
	cpath::gp-list
	cpath::psort

	ACCESS ARGLISTP *BUILT-IN-EXECUTABLE-COUNTERPARTS*
        CHANGE CONSTANT DEFREC ER *EXPANDABLE-BOOT-STRAP-NON-REC-FNS*
        HARD LEGAL-VARIABLE-OR-CONSTANT-NAMEP MAKE MSG
        REASON-FOR-NON-KEYWORD-VALUE-LISTP STATE-GLOBAL-LET*
	
	u::defloop u::force-term-list
	u::get-option-argument u::get-option-as-flag
	u::get-option-check-syntax u::get-option-entry
	u::get-option-entries u::get-option-member
	u::get-option-subset u::pack-intern
	u::unique-symbols))))))





