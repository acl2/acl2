; RP-REWRITER

; Noe: The license below is based on the template at:
; http://opensource.org/licenses/BSD-3-Clause

; Copyright (C) 2019 Regents of the University of Texas
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
; Mertcan Temel         <mert@utexas.edu>

(in-package "RP")

(include-book "aux-functions")

(include-book "macros")

;;(fetch-new-theory
 (include-book "projects/apply/top" :dir :system)
 ;; use-apply-top-lemmas
 ;; :disabled t)
 

(progn
  (defun rule-result-comperator (x y)
    (declare (xargs :mode :logic))
    (> (cdr x)
       (cdr y)))

  (defwarrant rule-result-comperator))

(defmacro set-rw-step-limit (new-rw-limit)
  `(make-event
    (b* ((rp-state (rp::update-rw-step-limit ,new-rw-limit rp-state)))
      (mv nil `(value-triple `(rw-step-limit ,',,new-rw-limit)) state rp-state))))


(xdoc::defxdoc
 set-rw-step-limit
 :parents (rp-utilities)
 :short "Number of steps RP-Rewriter can take when rewriting a conjecture."
 :long "<p> Similar to the built-in rewriter (see @(see REWRITE-STACK-LIMIT)),
 RP-Rewriter has a rewrite step limit. This can be changed with
 <code> @('(set-rw-step-limit <number>)') </code>
which submits an event.
</p>")


(xdoc::defxdoc
 show-rules
 :parents (rp-rewriter/debugging rp-utilities)
 :short "Sets whether or not RP-Rewriter should print used rules when rewriting
 a conjecture."
 :long
 "<p>(show-rules  @('<nil-OR-t-OR-:cnt>'))   submits  an  event   that  changes
 RP-Rewriter's behaviour on  saving and printing used rules. When  set to t, it
 prints rule in a fashion similar to the built-in rewriter but only differently
 for meta-rules.  When set  to :cnt,  it also  attaches a  number to  each rune
 showing how many  times they are used,  and how many times they  failed due to
 unrelieved hypotheses.  These entries are  saved in rules-used field  of stobj
 rp::rp-state. </p>" )


(encapsulate
  nil

  (defmacro show-rules (flg)
    `(make-event
      (b* ((rp-state ,(if flg
                          `(update-show-used-rules-flg t rp-state)
                        `(update-show-used-rules-flg nil rp-state)))
           (rp-state ,(if (equal flg ':cnt)
                          `(update-count-used-rules-flg t rp-state)
                        `(update-count-used-rules-flg nil rp-state))))
        (mv nil `(value-triple `(show-rules ,',',flg)) state rp-state))))

  #|(defmacro show-used-rules (flg)
  `(update-show-used-rules-flg ,flg rp-state))||#

  #|(defmacro show-used-rules-cnt (flg)
  `(update-count-used-rules-flg ,flg rp-state))||#

  (defmacro set-not-simplified-action (flg)
    `(make-event
      (b* ((rp-state (update-not-simplified-action ',flg rp-state)))
        (mv nil `(value-triple `(not-simplifed-action ,',',flg)) state
            rp-state))))

  (defund rp-stat-add-to-rules-used (rule failed ex-counterpart-flg rp-state)
    (declare (xargs :guard (or ex-counterpart-flg
                               (weak-custom-rewrite-rule-p rule))
                    :guard-hints (("Goal"
                                   :in-theory (e/d () (rp-statep
                                                       COUNT-USED-RULES-FLG
                                                       SHOW-USED-RULES-FLG
                                                       weak-custom-rewrite-rule-p))))
                    :stobjs (rp-state)))
    (if (show-used-rules-flg rp-state)
        (cond ((count-used-rules-flg rp-state)
               (b* ((rune (if ex-counterpart-flg
                              `(:executable-counterpart ,rule)
                            (rp-rune rule)))
                    (rune
                     (cond (failed
                            (cons rune failed))
                           (t rune)))
                    (rp-state
                     (if (not (rules-used-boundp rune rp-state))
                         (rules-used-put 'all-rules
                                         (cons rune
                                               (rules-used-get 'all-rules
                                                               rp-state))
                                         rp-state)
                       rp-state))
                         
                    (val (1+ (nfix (rules-used-get rune rp-state)))))
                 (rules-used-put rune val rp-state)))
              (t
               (b* (((when failed)
                     rp-state)
                    (rune1 (if ex-counterpart-flg
                               rule
                             (rp-rune rule)))
                    ((when (rules-used-boundp rune1  rp-state))
                     rp-state)
                    (rune2 (if ex-counterpart-flg
                               `(:executable-counterpart ,rule)
                             (rp-rune rule)))
                    (rp-state
                     (rules-used-put 'all-rules
                                     (cons rune2
                                           (rules-used-get 'all-rules
                                                           rp-state))
                                     rp-state))
                    (rp-state (rules-used-put rune1 nil rp-state)))
                 rp-state)))
      rp-state))


  (defund rp-state-print-rules-used-aux (all-rules rp-state)
    (declare (xargs :stobjs (rp-state)))
    (if (atom all-rules)
        nil
      (acons (car all-rules)
             (rules-used-get (car all-rules) rp-state)
             (rp-state-print-rules-used-aux (cdr all-rules) rp-state))))
  
  (defund rp-state-print-rules-used (rp-state)
    (declare (xargs :stobjs (rp-state)
                    :guard-hints (("Goal"
                                   :in-theory (e/d () (rp-statep
                                                       COUNT-USED-RULES-FLG
                                                       SHOW-USED-RULES-FLG
                                                       weak-custom-rewrite-rule-p))))))
    (if (show-used-rules-flg rp-state)
        (cw "~%List of rules used: ~p0 ~%"
            (let* ((all-rules (true-list-fix (rules-used-get 'all-rules rp-state))))
              (if (count-used-rules-flg rp-state)
                  (merge-comperator-sort
                   (true-list-fix (rp-state-print-rules-used-aux all-rules rp-state))
                   'rule-result-comperator)
                (acl2::merge-sort-lexorder
                 all-rules))))
      nil)))

(defund rp-state-push-to-try-to-rw-stack (rule var-bindings rp-context rp-state)
  (declare (xargs :stobjs (rp-state)
                  :guard (WEAK-CUSTOM-REWRITE-RULE-P RULE)))
  (if (and (rp-brr rp-state)
           (not (rp-rule-metap rule)))
      (b* ((old-rw-stack (rw-stack rp-state))
           (index (rw-stack-size rp-state))
           (new-rw-stack
            (acons index
                   (list
                    (list ':type ':trying)
                    (list ':rune (rp-rune rule))
                    (list ':lhs (rp-lhs rule))
                    (list ':rhs (rp-rhs rule))
                    (list ':hyp (rp-hyp rule))
                    (list ':context rp-context)
                    (list ':var-bindings var-bindings))
                   old-rw-stack))
           (rp-state (update-rw-stack new-rw-stack rp-state))
           (rp-state (update-rw-stack-size (1+ index) rp-state)))
        (mv index rp-state))
    (mv 0 rp-state)))

(defund rp-state-push-meta-to-rw-stack (meta-rule old-term new-term rp-state)
  (declare (xargs :stobjs (rp-state)
                  :guard (and (WEAK-CUSTOM-REWRITE-RULE-P meta-rule)
                              (rp-rule-metap meta-rule))))
  (if (rp-brr rp-state)
      (b* ((old-rw-stack (rw-stack rp-state))
           (index (rw-stack-size rp-state))
           (new-rw-stack (acons index
                                (list
                                 (list ':type ':meta-applied)
                                 (list ':meta-fnc (rp-rule-meta-fnc meta-rule))
                                 (list ':trig-fnc (rp-rule-trig-fnc meta-rule))
                                 (list ':new-term new-term)
                                 (list ':old-term old-term))
                                old-rw-stack))
           (rp-state (update-rw-stack new-rw-stack rp-state))
           (rp-state (update-rw-stack-size (1+ index) rp-state)))
        rp-state)
    rp-state))

(defund rp-state-push-to-result-to-rw-stack (rule index failed old-term new-term rp-state)
  (declare (xargs :stobjs (rp-state)
                  :guard (and (WEAK-CUSTOM-REWRITE-RULE-P RULE)
                              (integerp index))))
  (if (rp-brr rp-state)
      (b* ((rune (rp-rune rule))
           ;;; Add the caused frame count.
           (frames (1- (- (rw-stack-size rp-state) index)))
           (old-frame-cnts (rule-frame-cnts rp-state))
           (new-frame-cnt (+ (nfix (cdr (hons-get rune old-frame-cnts)))
                             frames))
           (rp-state (if (> new-frame-cnt 0)
                         (update-rule-frame-cnts (hons-acons rune new-frame-cnt
                                                             old-frame-cnts)
                                                 rp-state)
                       rp-state))
           ;;; push the failed to the stack
           (old-rw-stack (rw-stack rp-state))
           (new-rw-stack (acons index
                                (list*
                                 (cons ':type failed)
                                 (list ':rune rune)
                                 (if new-term (list (list ':new-term new-term)
                                                    (list ':old-term old-term))
                                   nil))
                                old-rw-stack)))
        (update-rw-stack new-rw-stack rp-state))
    rp-state))

(defun untranslate-var-bindinds (alist iff-flg world)
  (declare (xargs :mode :program))
  (if (atom alist)
      nil
    (acons (caar alist)
           (list (untranslate (cdar alist) iff-flg world))
           (untranslate-var-bindinds (cdr alist) iff-flg world))))

(defun assoc-eqs-untranslate (keys alist state)
  (declare (xargs :guard (and (symbol-listp keys)
                              (alistp alist))
                  :stobjs (state)
                  :mode :program))
  (if (atom keys)
      nil
    (acons (car keys)
           (cond ((or (equal (car keys) ':new-term)
                      (equal (car keys) ':old-term)
                      (equal (car keys) ':rhs)
                      (equal (car keys) ':lhs)
                      (equal (car keys) ':hyp))
                  (list (untranslate (cadr (assoc-eq (car keys) alist)) t (w
                                                                           state))))
                 ((equal (car keys) ':var-bindings)
                  (list (untranslate-var-bindinds (cadr (assoc-eq (car keys) alist)) t
                                                  (w state))))
                 (t (cdr (assoc-eq (car keys) alist))))
           (assoc-eqs-untranslate (cdr keys) alist state))))

(defun assoc-eqs (keys alist )
  (declare (xargs :guard (and (symbol-listp keys)
                              (alistp alist))
                  :mode :program))
  (if (atom keys)
      nil
    (cons (assoc-eq (car keys) alist)
          (assoc-eqs (cdr keys) alist))))

(defun search-source-in-stack (rw-stack term)
  (if (atom rw-stack)
      nil
    (b* ((current (car rw-stack))
         (type (cdr (assoc-equal ':type (cdr current))))
         ((unless (or (eq type ':success)
                      (eq type ':meta-applied)))
          (search-source-in-stack (cdr rw-stack) term)))
      (if (subtermp (cadr (assoc-equal ':new-term (cdr current))) term)
          (car current)
        (search-source-in-stack (cdr rw-stack) term)))))

(defun search-source-in-stack-var-bindings (rw-stack var-bindings)
  (if (atom var-bindings)
      nil
    (if (atom (cdar var-bindings))
        (search-source-in-stack-var-bindings rw-stack (cdr var-bindings))
      (acons (caar var-bindings)
             (search-source-in-stack rw-stack (cdar var-bindings))
             (search-source-in-stack-var-bindings rw-stack (cdr var-bindings))))))

(progn
  (define pp-rw-stack-aux (rw-stack omit only evisc-tuple untranslate search-source state)
    (declare (xargs :stobjs (state)
                    :mode :program))
    :verify-guards nil
    (if (atom rw-stack)
        state
      (b* ((entry (car rw-stack))
           ((when (and only
                       (not (or (member-equal (cdr (assoc-equal ':type (cdr entry)))
                                              only)
                                (member-equal (cadr (assoc-equal ':rune (cdr entry)))
                                              only)
                                (member-equal (cadr (assoc-equal ':meta-fnc (cdr entry)))
                                              only)))))
            (pp-rw-stack-aux (cdr rw-stack)
                             omit
                             only
                             evisc-tuple
                             untranslate
                             search-source
                             state))
           ((when (or (member-equal (cdr (assoc-equal ':type (cdr entry)))
                                    omit)
                      (member-equal (cadr (assoc-equal ':rune (cdr entry)))
                                    omit)
                      (member-equal (cadr (assoc-equal ':meta-fnc (cdr entry)))
                                    omit)))
            (pp-rw-stack-aux (cdr rw-stack)
                             omit
                             only
                             evisc-tuple
                             untranslate
                             search-source
                             state))
           (sub-entries
            (if untranslate
                (assoc-eqs-untranslate (set-difference$ (strip-cars (cdr entry))
                                                        omit)
                                       (cdr entry)
                                       state)
              (assoc-eqs (set-difference$ (strip-cars (cdr entry))
                                          omit)
                         (cdr entry))))
           (sub-entries (if (and search-source
                                 (equal (cdr (assoc-equal ':type (cdr entry))) ':trying))
                            (append
                             sub-entries
                             (list (cons ':var-bindings
                                         (search-source-in-stack-var-bindings
                                          rw-stack
                                          (cadr (assoc-equal ':var-bindings
                                                             (cdr entry)))))))
                          sub-entries))
           (sub-entries (if (and search-source
                                 (equal (cdr (assoc-equal ':type (cdr entry))) ':meta-applied))
                            (append
                             sub-entries
                             (list (cons ':old-term
                                         (search-source-in-stack
                                          rw-stack
                                          (cadr (assoc-equal ':old-term
                                                             (cdr entry)))))))
                          sub-entries))
           (state (fms "~p0~%"
                       (list
                        (cons #\0 (cons (car entry) sub-entries)))
                       *standard-co* state evisc-tuple)))
        (pp-rw-stack-aux (cdr rw-stack)
                         omit
                         only
                         evisc-tuple
                         untranslate
                         search-source
                         state))))

  (define take$ (n l)
    (declare (xargs  :mode :program))
    (if (atom l)
        nil
      (if (zp n)
          nil
        (cons (car l)
              (take$ (1- n)
                     (cdr l))))))

  ;; Example print:
  ;; (rp::pp-rw-stack :omit '()
  ;;                :evisc-tuple (evisc-tuple 10 10 nil nil)
  ;;                :frames 100)

  (define pp-rw-stack (&key (rp-state 'rp-state)
                            (state 'state)
                            (frames '-1)
                            (frames-offset '0)
                            (omit 'nil)
                            (only 'nil)
                            (evisc-tuple ''(NIL 6 8 NIL))
                            (untranslate 'nil)
                            (search-source 'nil))
    (declare (xargs :stobjs (rp-state state)
                    :mode :program))
    :verify-guards nil
    :short "Pretty printing of rewrite stack."
    :parents (rp-rewriter/debugging)
    :long "
<p>
Rewrite stack for RP-Rewriter can be enabled with
(rp::update-rp-brr t rp::rp-state) or disabled with (rp::update-rp-brr t
rp::rp-state).  Then users may print the stack with program-mode function
pp-rw-stack. </p>

<code>
@('
 (pp-rw-stack :frames <number>
              :frames-offset <number>
              :omit <list-of-names>
              :only <list-of-names>
              :evisc-tuple <quoted-evisc-tuple>
              :untranslate <t-or-nil>)
')
</code>

<p>
frames: Number of rewriter steps to print. Default value is -1, that is all the
frames.
</p>
<p>
frames-offset: Number of frames to skip. Defualt value = 0.
</p>
<p>
omit: List of runes or entries in a frame to omit. For example, it can have:
(:rewrite some-rule), :context, a-meta-fnc-name etc.. Default value is nil.
</p>
<p>
only: Similar to only, print only the given entries.
</p>
<p>
evisc-tuple: See @(see evisc-tuple). Used in order to shorten long terms.
Default value: '(NIL 3 4 NIL)
</p>
<p>
untranslate: whether or not to untranslate the term. See @(see
untranslate). Default value = t.
</p>
"
    (b* ((rw-stack (rw-stack rp-state))
         ((unless rw-stack)
          (progn$
           (cw "Nothing to print. Run (rp::update-rp-brr t rp-state) ~%")
           state))
         (rw-stack (nthcdr (nfix frames-offset) rw-stack))
         (rw-stack (if (natp frames) (take$ frames rw-stack) rw-stack)))
      (pp-rw-stack-aux rw-stack omit only evisc-tuple untranslate search-source state))))

(defmacro show-rule-frames ()
  `(merge-comperator-sort (fast-alist-clean (rule-frame-cnts rp-state))
                          'rule-result-comperator))

(define increment-rw-stack-size (rp-state)
  (declare (xargs :stobjs (rp-state)))
  (if (rp-brr rp-state)
      (update-rw-stack-size (1+ (rw-stack-size rp-state)) rp-state)
    rp-state))

(in-theory (disable rp-statep))

(xdoc::defxdoc
 rp-rewriter/debugging
 :parents (rp-rewriter)
 :short "Tools that may be used while debugging RP-Rewriter.")

