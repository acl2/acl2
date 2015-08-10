; Def-saved-obligs --
; Copyright (C) 2013 Centaur Technology
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
; Original author: Sol Swords <sswords@centtech.com>

(in-package "ACL2")

(include-book "std/util/support" :dir :system)

(defxdoc def-saved-obligs
  :parents (macro-libraries)
  :short "Save the proof obligations for a given event as separate defthms."
  :long "<p>Say you'd like to admit a function and verify its guards, but you
want its termination and guard proof obligations to be saved as defthms so that
you can use them later.  Here is how to do this with def-saved-obligs:</p>

@({
 (def-saved-obligs foo-obligs
   :proofs ((foo-measure-thm :hints (...))
            (foo-guard-thm   :hints (...)))
   (defun foo (x y)
     (declare (xargs :guard ...))
     ...))
 })

<h5>Notes</h5>

<p>Major caveat: This works by trying to admit the proof obligations as defthms
before admitting the actual events.  In some cases this isn't possible: e.g.,
for termination conditions of some reflexive functions and guard verifications
involving some requirement about the result of a recursive call.  For guards,
it should work to defer the guard verification to a separate def-saved-obligs
event from the one with the defun.  For reflexive functions, you're out of luck
with this macro, for the present.</p>

<p>The :proofs entries should occur in the order that the corresponding proof
obligations are tackled by ACL2.</p>

<p>The theorems produced will all have :rule-classes nil.</p>

<p>The ambient theory may affect the proof obligations that are saved.  It
might make sense to do @('(local (in-theory nil))') when you use this.</p>

<h5>Implementation</h5>

<p>This macro expands to a make-event form.  In the make-event expansion phase,
the events are run with some default hints installed that record each proof
obligation and avoid having to actually complete the proof. on every proof
obligation, push the corresponding clause onto a state global, and then
unsoundly complete the proof by instantiating a bogus theorem NIL submitted
using skip-proofs.  (Since the use of skip-proofs is only in the make-event
expansion phase, its effects are erased and it is allowed by certify-book even
without :skip-proofs-okp.)</p> ")



(defconst *def-saved-obligs-keywords*
  '(:proofs))

(defun saved-obligs-to-defthms (prooflst clauses wrld)
  (declare (xargs :mode :program)
           (ignorable wrld))
  (if (atom prooflst)
      nil
    (cons `(defthm ,(caar prooflst)
             ,(disjoin (car clauses))
             :hints ,(cadr (assoc-keyword :hints (cdar prooflst)))
             :rule-classes nil)
          (saved-obligs-to-defthms (cdr prooflst) (cdr clauses) wrld))))

(defun saved-obligs-hints-to-computed (hints)
  (if (atom hints)
      nil
    (cons (if (and (consp (car hints))
                   (stringp (caar hints)))
              `(and (equal id (parse-clause-id ,(caar hints)))
                    ',(cdar hints))
            (car hints))
          (saved-obligs-hints-to-computed (cdr hints)))))


(defun saved-obligs-prooflst-collect-hints (prooflst)
  (if (atom prooflst)
      nil
    (cons `(:by ,(caar prooflst))
          (saved-obligs-prooflst-collect-hints (cdr prooflst)))))


(defun saved-obligs-hint (id state)
  (declare (xargs :mode :program :stobjs state))
  (b* (((unless (and (eql (access clause-id id :forcing-round) 0)
                     (eq (access clause-id id :pool-lst) nil)))
        (value nil))
       (hintlst (@ saved-obligs-hintlst))
       (state (f-put-global 'saved-obligs-hintlst (cdr hintlst) state)))
    (value (car hintlst))))


(defun def-saved-obligs-fn (name args state)
  (declare (xargs :mode :program :stobjs state))
  (b* ((state (f-put-global 'saved-obligs-clauses nil state))
       (prev-skip-proofsp (ld-skip-proofsp state))
       ((er &) (set-ld-skip-proofsp nil state))
       ((mv kwd-alist events)
        (std::extract-keywords 'def-saved-obligs *def-saved-obligs-keywords* args nil))
       (proof-list (cdr (assoc :proofs kwd-alist)))
       (default-hints-table (table-alist 'default-hints-table (w state)))
       (collect-events
        `(with-output :off :all :on (error)
           (progn
             (skip-proofs (defthm saved-obligs-cheat nil :rule-classes nil))
             (table default-hints-table nil nil :clear)
             (set-default-hints
              '((pprogn (f-put-global 'saved-obligs-clauses
                                      (cons clause (@ saved-obligs-clauses))
                                      state)
                        (value '(:by saved-obligs-cheat)))))
             (deflabel saved-obligs-redundancy-detection)
             (in-theory nil)
             . ,events)))
       ((er &) (trans-eval collect-events 'def-saved-obligs state t))
       ((er &) (set-ld-skip-proofsp prev-skip-proofsp state))
       ;; Check that some events were actually recorded after the deflabel.
       (last-event-tuple (cddr (car (scan-to-event (w state)))))
       ((when (and (eq (access-event-tuple-type last-event-tuple) 'deflabel)
                   (eq (access-event-tuple-namex last-event-tuple)
                       'saved-obligs-redundancy-detection)))
        (cw "DEF-SAVED-OBLIGS: We think all events were redundant.~%")
        (value `(value-triple ',name)))
       (clauses (reverse (@ saved-obligs-clauses)))
       ((unless (eql (len clauses) (len proof-list)))
        (er soft 'def-saved-obligs
            "We collected ~x0 proof obligations, but have ~x1 entries under :proofs."
            (len clauses) (len proof-list)))
       (thms (saved-obligs-to-defthms proof-list clauses (w state)))
       (hintlst (saved-obligs-prooflst-collect-hints proof-list))
       (- (cw "hintlst: ~x0~%" hintlst))
       (state (f-put-global 'saved-obligs-hintlst hintlst state)))
    (value
     `(progn ,@thms
             (local (table default-hints-table
                           nil
                           '((t . ((saved-obligs-hint id state))))
                           :clear))
             (encapsulate nil
               (local (in-theory nil))
               ,@events)
             (local (table default-hints-table
                           nil
                           ',default-hints-table
                           :clear))
             (value-triple ',name)))))





(defmacro def-saved-obligs (name &rest args)
  `(make-event
    (def-saved-obligs-fn ',name ',args state)))


(local (in-theory (disable len nat-listp)))

(local
 (def-saved-obligs foo-stuff
   :proofs ((foo-measure :hints(("Goal" :in-theory (enable len))))
            (foo-guard :hints ((and stable-under-simplificationp
                                    '(:in-theory (enable nat-listp))))))
   (defun foo (x)
     (declare (xargs :measure (len x)
                     :guard (nat-listp x)))
     (if (atom x)
         12
       (+ 2 (car x)
          (foo (cdr x)))))))
