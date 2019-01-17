; Easy Simplify
; Copyright (C) 2012-2014 Centaur Technology
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
(include-book "std/util/bstar" :dir :system)

(defxdoc easy-simplify-term
  :parents (programming)
  :short "A simple interface for simplifying a term, perhaps under a hypothesis
and equivalence context, and with optional guidance from a hint."

  :long "<p>This provides a straightforward interface for simplifying a term.
It uses the proof checker's pc-rewrite* function.  It can handle rewriting
under some hypotheses, under a user-provided equivalence relation.</p>

<p>Usage:</p>

@({
    (easy-simplify-term (my-fn (foo) (bar baz))
                        ;; optional keyword args:
                        :hyp (and (integerp baz) (<= 0 baz))
                        :hint (:in-theory (enable my-fn) :expand ((foo)))
                        :equiv equal
                        :normalize t
                        :rewrite t
                        :repeat 555
                        :backchain-limit 5)
})

<p>Important NOTE: The HINT keyword should be given a hint keyword/val list, as
in the example above, NOT a list of subgoal or computed hints,
e.g. ((\"Goal\" :foo)).</p>")

;; Note: replaced this with acl2's built-in expand-assumptions-1
;; (defun if-nest-to-hyp-list (x)
;;   (cond ((equal x ''t) nil)
;;         ((or (atom x)
;;              (not (eq (car x) 'if))
;;              (not (equal (fourth x) ''nil)))
;;          (list x))
;;         (t (append (if-nest-to-hyp-list (second x))
;;                    (if-nest-to-hyp-list (third x))))))


;; takes a translated term and an implicitly conjoined list of translated hyps
(defun easy-simplify-term1-fn (term hyps hints equiv
                              normalize rewrite
                              repeat
                              backchain-limit
                              state)
  (declare (xargs :mode :program :stobjs state))
  (b* ((world (w state))

       ((er hint-settings)
        (translate-hint-settings
         'simp-term "Goal" hints 'easy-simplify-term world state))
       (ens (ens state))
       (base-rcnst
        (change rewrite-constant
                *empty-rewrite-constant*
                :current-enabled-structure ens
                :force-info t))
       ((er rcnst)
        (load-hint-settings-into-rcnst
         hint-settings base-rcnst

; Matt K. mod April 2016 to accommodate the issue in :doc note-7-3 regarding a
; slow-array-warning from computed hints.

         :easy-simplify
         world 'easy-simplify-term state))
       (ens (access rewrite-constant rcnst :current-enabled-structure))
       ((mv flg hyps-type-alist ?ttree)
        (hyps-type-alist hyps ens world state))
       ((when flg)
        (mv "Contradiction in the hypotheses"
            nil state))
       ((mv ?step-limit new-term ?new-ttree state)
        (pc-rewrite*
         term hyps-type-alist
         (if (eq equiv 'equal)
             nil
           (list (make congruence-rule
                       :rune *fake-rune-for-anonymous-enabled-rule*
                       :nume nil
                       :equiv equiv)))
         (eq equiv 'iff)
         world rcnst nil nil normalize rewrite ens state
         repeat backchain-limit
         (initial-step-limit world state))))
    (value new-term)))

(defun easy-simplify-term-fn (term hyp-term hints equiv
                              normalize rewrite repeat backchain-limit state)
  (declare (xargs :mode :program :stobjs state))
  (b* ((world (w state))
       ((er trans-term)
        (translate term t nil t 'easy-simplify-term world state))
       ((er trans-hyp-term)
        (translate hyp-term t nil t 'easy-simplify-term world state))
       ;; ;; bozo find out how ACL2 does this, if it does
       ;; (hyps (if-nest-to-hyp-list trans-hyp-term))
       ;; ... like this:
       (hyps (expand-assumptions-1 trans-hyp-term))
       ((er new-term)
        (easy-simplify-term1-fn
         trans-term hyps hints equiv normalize rewrite repeat backchain-limit
         state)))
    (value (untranslate new-term nil (w state)))))

(defmacro easy-simplify-term (term &key
                                   (hyp 't)
                                   hint
                                   (equiv 'equal)
                                   (normalize 't)
                                   (rewrite 't)
                                   (repeat '1000)
                                   (backchain-limit '1000))
  `(easy-simplify-term-fn
    ',term ',hyp ',hint ',equiv
    ',normalize ',rewrite ',repeat ',backchain-limit
    state))


(defxdoc defopen
  :parents (programming)
  :short "A simple event generator that creates a theorem by finding out what a
term simplifies to under some hyp and with some hint."

  :long "<p>In contrast to @('misc/defopener') (see @(see defopener)), the
reductions carried out by @('defopen') may be less powerful because we only do
simplification (no clausify).  However, this seems to produce more compact
expressions than @('defopener'), where the result is formed by combining
several clauses produced from the original term.</p>

<p>General form:</p>

@(ccall defopen)

<p>See also @(see easy-simplify-term).</p>")

(defmacro defopen (name term &key (hyp 't) hint
                        (rule-classes ':rewrite))
  `(make-event
    (b* (((er new-hyp-term)
          (acl2::easy-simplify-term ,hyp :hint ,hint))
         ((er new-term)
          (acl2::easy-simplify-term-fn
           ',term new-hyp-term ',hint 'equal t t 1000 1000 state)))
      (value `(defthm ,',name
                ,(if (not (eq ',hyp t))
                     `(implies ,',hyp (equal ,',term ,new-term))
                   `(equal ,',term ,new-term))
                :hints (("goal" . ,',hint))
                :rule-classes ,',rule-classes)))))
