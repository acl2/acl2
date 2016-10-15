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

(include-book "std/portcullis" :dir :system)
(include-book "../adviser/portcullis")

(defpkg "MAP" (set-difference-eq
;               (remove-duplicates-eql ;no longer necessary
                `(,@ACL2::*acl2-exports*
                  ,@ACL2::*common-lisp-symbols-from-main-lisp-package*
		  a b c d e f g h i j k l m n o p q r s u v w x y z
		  ADVISER::defadvice)
                ;)
               '(get set default optimize fix)))

#!MAP
;; We intend to export only the following symbols.  Most of these are just
;; macro aliases for our functions.  See the file aliases.lisp for more
;; information about this.

(defconst *exports*
  '(;; symbols for our exportable function names and aliases
    mapp emptymap mapfix mapoptimize mapdomain mapget mapset
    maperase mapin submap mapequiv maphead maptail mapempty
    mapempty-exec mapdefault

    ;; symbols for "common" theorems to enable/disable, use,
    ;; or functionally instantiate
    submap-by-membership
    equal-of-gets-when-submap
    typed-mapp
    typed-mapp-hyps
    typed-mapp-map
    predicate-when-in-typed-mapp
    typed-mapp-by-membership
    typed-mapp-of-set
    typed-mapp-of-erase
    equiv-implies-equal-typed-mapp-1
    ))
