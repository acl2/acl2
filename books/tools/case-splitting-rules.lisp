; case-splitting-rules -- figure out which rules caused case splits
; Copyright (C) 2012 Centaur Technology
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
; Original authors: Sol Swords and Jared Davis
;                   {sswords,jared}@centtech.com

(in-package "ACL2")
(include-book "std/util/bstar" :dir :system)

; This is something you can use to figure out which rewrite rules led to case
; splits in a proof.  The interface is terrible:
;
; First, do:
;     (set-raw-proof-format t)
;
; Then, try your proof and find the goal that is case splitting on you.  The
; proof log will then have a big list of rules:
;
;    ((:rewrite ...) (:definition ...))
;
; Copy this s-expression, and then submit the form:
;
;    (case-splitting-rules ((:rewrite ...) (:definition ...)))
;
; This will print out just the rewrite rules with IF on their right-hand side.
;
; Known Limits:
;  - Does not show you non-rewrite rules (e.g., :definition rules)
;  - Does not show you rules with (case-split ...) in their hyps

(defun not-pr-body (wrld-segment numes wrld state)
  (declare (xargs :stobjs state :mode :program))
  (info-for-rules (actual-props wrld-segment nil nil)
                  numes
                  (ens state)
                  wrld))

(defun not-pr-fn (name state)
  (declare (xargs :stobjs state :mode :program))
  (cond ((and (symbolp name)
              (not (keywordp name)))
         (let* ((wrld (w state))
                (name (deref-macro-name name (macro-aliases wrld)))
                (numes (strip-cars (getprop name 'runic-mapping-pairs nil
                                            'current-acl2-world wrld)))
                (wrld-segment (world-to-next-event
                               (cdr (decode-logical-name name wrld)))))
           (not-pr-body wrld-segment numes wrld state)))
        (t (er hard? 'not-pr
               "The argument to NOT-PR must be a non-keyword symbol."))))

(defun not-pr-fn-list (names state)
  (declare (xargs :stobjs state :mode :program))
  (if (atom names)
      nil
    (append (not-pr-fn (car names) state)
            (not-pr-fn-list (cdr names) state))))

(defun easy-translate
  (term  ; the term you want to translate (i.e., macro-expand)
   ctx   ; a "context" for error messages
   state)
  "Returns (MV ER VAL STATE)"
  (declare (xargs :mode :program :stobjs state))
  (translate term ;; term to translate
             t ;; we're translating for logical use
             t ;; logic mode
             t ;; known stobjs, t means "all stobjs in world"
             ctx
             (w state)
             state))

(mutual-recursion
 (defun has-callp (fn x)
   (cond ((atom x)
          nil)
         ((quotep x)
          nil)
         ((equal (car x) fn)
          t)
         ((atom (car x))
          (has-callp-list fn (cdr x)))
         (t ;; ((lambda formals body) args)
          (or (has-callp fn (third (first x)))
              (has-callp-list fn (cdr x))))))
 (defun has-callp-list (fn x)
   (if (atom x)
       nil
     (or (has-callp fn (car x))
         (has-callp-list fn (cdr x))))))

(defun collect-case-splits (info-list state)
  (declare (xargs :mode :program :stobjs state))
  (b* (((when (atom info-list))
        (mv nil state))
       (rhs-values (cdr (assoc :rhs (car info-list))))
       ((unless rhs-values)
        (collect-case-splits (cdr info-list) state))
       ((mv er val state)
        (easy-translate (car rhs-values) 'collect-case-splits state))
       ((when er)
        (er hard? 'collect-case-splits "something bad happened: ~@0" er)
        (mv nil state))
       ((mv rest state) (collect-case-splits (cdr info-list) state))
       ((when (has-callp 'if val))
        (mv (cons (car info-list) rest) state)))
    (mv rest state)))

(defun collect-rewrites (info-list)
  (if (atom info-list)
      nil
    (if (eq (caadr (assoc :rune (car info-list))) :rewrite)
        (cons (car info-list) (collect-rewrites (cdr info-list)))
      (collect-rewrites (cdr info-list)))))

(defmacro case-splitting-rules (x)
  `(b* ((info (not-pr-fn-list (acl2::strip-cadrs ',x) state))
        (rewrites (collect-rewrites info))
        ((mv splits state)
         (collect-case-splits rewrites state)))
     (print-info-for-rules splits (standard-co state) state)))
