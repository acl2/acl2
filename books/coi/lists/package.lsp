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

#!ACL2
(in-package "ACL2")

; The following comment line tells the build system that if *acl2-exports*
; changes, then every book that uses this file should be recertified:
; (depends-on "build/acl2-exports.certdep" :dir :system)

(include-book "../adviser/portcullis")
(include-book "../util/portcullis")

(defpkg "LIST"
  (set-difference-eq
;;   (remove-duplicates-eql ;no longer necessary due to change in ACL2
    `(,@*acl2-exports*
      ,@*common-lisp-symbols-from-main-lisp-package*

      a b c d e f g h i j k l m n o p q r s u v w x y z

      ;; Leave this here, becuase we want our version of firstn to be
      ;; the same one as used in some of the books, e.g.,
      ;; data-structures.
      firstn

      ;; bzo - this was originally in the ACL2 package and some code
      ;; may still rely on that.  But, we should remove this eventually.
      repeat

      ;; bzo - remove me eventually if Matt adds me to *acl2-exports*
      update-nth-array

      )
    ;)
    '(fix)))



;; This list should be considered a rough draft.  We might want to include
;; other things, particularly:
;;
;;   - names of theorems that often should be enabled or disabled?
;;   - names of new functions as we add them?
;;   - names of variables used throughout our theorems?

#!LIST
(defconst *exports*
  '(finalcdr memberp firstn repeat
    cdddddr cddddddr caddddddr cadddddr caddddr
    ))


