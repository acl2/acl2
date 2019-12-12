; Record Like Stobjs
; Copyright (C) 2011-2012 Centaur Technology
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
; Original author: Jared Davis <jared@centtech.com>

(in-package "ACL2")

; The following comment line tells the build system that if *acl2-exports*
; changes, then every book that uses this file should be recertified:
; (depends-on "build/acl2-exports.certdep" :dir :system)

(defpkg "RSTOBJ2"
  (union-eq *acl2-exports*
            *common-lisp-symbols-from-main-lisp-package*
            ;; things missing from acl2 exports
            '(unsigned-byte-p signed-byte-p extend-pathname defstobj-template
                              translate-declaration-to-guard keyword-value-listp
                              partition-rest-and-keyword-args assoc-keyword
                              remove-keyword alist-to-keyword-alist *defstobj-keywords*
                              update-nth-array)
            ;; single-letter variables for better theorem compatibility with
            ;; acl2 package, and for g/s.
            '(a b c d e f g h i j k l m n o p q r s u v w x y z)
            ;; things we're importing from acl2 libraries
            '(<< equal-by-nths equal-by-nths-lhs equal-by-nths-rhs equal-by-nths-hyp
                 defsection definline b*)
            ;; extra imports for better documentation links
            '(stobj macro-libraries legacy-defrstobj)
            ;; things from from type-spec-fns
            '(atom-fix bitp bit-fix bit-listp character-fix cons-fix nat-listp
                       string-fix symbol-fix signed-byte-fix signed-byte-listp
                       unsigned-byte-fix unsigned-byte-listp)))
