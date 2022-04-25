; VL Verilog Toolkit
; Copyright (C) 2008-2013 Centaur Technology
; Copyright (C) 2022 Intel Corporation
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

(in-package "VL")

;; NOTE: This book should generally only be included locally; it nonlocally
;; changes the default hints used in define/defines returnspecs and
;; deffixequiv/deffixequiv-mutual events.

(include-book "std/util/defines" :dir :system)
(include-book "centaur/fty/fixequiv" :dir :system)
(include-book "clause-processors/just-expand" :dir :system)
(include-book "centaur/meta/resolve-flag-cp" :dir :system)

(defun big-mutrec-default-hint
    #!acl2 (fnname id wait-til-stablep world)
    (declare (xargs :mode :program))
    ;; copied mostly from just-expand.lisp, just-expand-mrec-default-hint,
    ;; added resolve-flags-cp and do-not-induct before expanding
    #!acl2
    (and (eql 0 (acl2::access acl2::clause-id id :forcing-round))
         (equal '(1) (acl2::access acl2::clause-id id :pool-lst))
         (let* ((fns (acl2::recursivep fnname t world))
                (flags (strip-cdrs (acl2::flag-alist fnname world)))
                (expand-hints (just-expand-cp-parse-hints
                               (just-expand-mrec-expanders fns world)
                               world)))
           `(:computed-hint-replacement
             ('(:clause-processor (mark-expands-cp clause '(t t ,expand-hints)))
              ;; (cmr::call-urewrite-clause-proc)
              ;; '(:clause-processor cmr::dumb-flatten-clause-proc)
              ;; '(:clause-processor (cmr::let-abstract-lits-clause-proc clause 'xxx))
              (and (or (not ',wait-til-stablep) stable-under-simplificationp)
                   (expand-marked)))
             :in-theory (disable . ,fns)
             :do-not-induct t
             :clause-processor (cmr::resolve-flags-cp
                                clause
                                ',(cons 'vl::flag flags))))))

(std::set-returnspec-default-hints
 ((acl2::just-induct/expand-default-hint 'std::fnname id nil world)))
(std::set-returnspec-mrec-default-hints
 ((big-mutrec-default-hint 'std::fnname id nil world)))

(fty::set-deffixequiv-default-hints
 ((acl2::just-induct/expand-default-hint 'fty::fnname id nil world)))
(fty::set-deffixequiv-mutual-default-hints
 ((big-mutrec-default-hint 'fty::fnname id nil world)))
