; Centaur SV Hardware Verification Tutorial
; Copyright (C) 2012-2015 Centaur Technology
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
; Original authors: Jared Davis <jared@centtech.com>
;                   Sol Swords <sswords@centtech.com>

(in-package "SV")

(include-book "xdoc/top" :dir :system)

(defxdoc sv-tutorial
  :parents (sv)
  :short "Basic tutorial: how to use the svex package to do datapath verification."
  :long " <p>The subtopics are listed in the intended order of the
tutorial, which first covers verification of a simple 16-bit combinational ALU
module, then a counter module to illustrate how to deal with state over time,
and finally a multiplier implementation to show how to structurally decompose
your proofs.</p>

<p>Note: A much higher level of detail is present in the comments of this book
than in the xdoc tutorial.  The xdoc tutorial is intended to give a high-level
idea of how to do it; to actually replicate it, you will likely want to look at
the sources.</p>

<p>To begin the ALU example, start at @(see translating-verilog-to-svex).</p>")



;; NOTE: This macro just runs an event and also saves the form into the given
;; name as a state global, so we can copy the form into xdoc.  For purposes of
;; reading this tutorial, pretend each def-saved-event is just the form inside it.
(defmacro def-saved-event (name form)
  `(make-event
    (let* ((form ',form))
      (value `(progn (table saved-forms-table ',',name ',form)
                     ,form)))))

;; NOTE: This macro saves and runs the form, but doesn't produce any event.
(defmacro def-saved-nonevent (name form &key (return '?res) writep)
  `(make-event
    (b* ((form ',form)
         (?res :ok)
         ,@(and writep '((state (f-put-global 'acl2::writes-okp t state))))
         (,return ,form))
      (value `(table saved-forms-table ',',name ',form)))))

;; NOTE: This macro just keeps track of the ordering of subtopics.  Otherwise
;; it's just defxdoc.
(defmacro deftutorial (name &rest args)
  (let ((parent (car (cadr (assoc-keyword :parents args)))))
    `(progn
       (local
        ;; Accumulate topic names in reverse order.
        (table tutorial-ordering-table
               ',parent
               (let* ((table (table-alist 'tutorial-ordering-table world))
                      (topics (cdr (assoc ',parent table))))
                 (cons ',name topics))))
       (defxdoc ,name . ,args))))

(defmacro $ (name)
  `(cdr (assoc ',name (table-alist 'saved-forms-table (w state)))))

(defun recreate-saved-forms-table (pairs)
  (if (atom pairs)
      nil
    (cons `(table saved-forms-table ',(caar pairs) ',(cdar pairs))
          (recreate-saved-forms-table (cdr pairs)))))
