;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;           __    __        __    __                                        ;;
;;          /  \  /  \      (__)  |  |    ____   ___      __    ____         ;;
;;         /    \/    \      __   |  |   / _  |  \  \ __ /  /  / _  |        ;;
;;        /  /\    /\  \    |  |  |  |  / / | |   \  '  '  /  / / | |        ;;
;;       /  /  \__/  \  \   |  |  |  |  \ \_| |    \  /\  /   \ \_| |        ;;
;;      /__/          \__\  |__|  |__|   \____|     \/  \/     \____|        ;;
;; ~ ~~ \  ~ ~  ~_~~ ~/~ /~ | ~|~ | ~| ~ /~_ ~|~ ~  ~\  ~\~ ~  ~ ~  |~~    ~ ;;
;;  ~ ~  \~ \~ / ~\~ / ~/ ~ |~ | ~|  ~ ~/~/ | |~ ~~/ ~\/ ~~ ~ / / | |~   ~   ;;
;; ~ ~  ~ \ ~\/ ~  \~ ~/ ~~ ~__|  |~ ~  ~ \_~  ~  ~  .__~ ~\ ~\ ~_| ~  ~ ~~  ;;
;;  ~~ ~  ~\  ~ /~ ~  ~ ~  ~ __~  |  ~ ~ \~__~| ~/__~   ~\__~ ~~___~| ~ ~    ;;
;; ~  ~~ ~  \~_/  ~_~/ ~ ~ ~(__~ ~|~_| ~  ~  ~~  ~  ~ ~~    ~  ~   ~~  ~  ~  ;;
;;                                                                           ;;
;;            A   R e f l e c t i v e   P r o o f   C h e c k e r            ;;
;;                                                                           ;;
;;       Copyright (C) 2005-2009 by Jared Davis <jared@cs.utexas.edu>        ;;
;;                                                                           ;;
;; This program is free software; you can redistribute it and/or modify it   ;;
;; under the terms of the GNU General Public License as published by the     ;;
;; Free Software Foundation; either version 2 of the License, or (at your    ;;
;; option) any later version.                                                ;;
;;                                                                           ;;
;; This program is distributed in the hope that it will be useful, but       ;;
;; WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABIL-  ;;
;; ITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public      ;;
;; License for more details.                                                 ;;
;;                                                                           ;;
;; You should have received a copy of the GNU General Public License along   ;;
;; with this program (see the file COPYING); if not, write to the Free       ;;
;; Software Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA    ;;
;; 02110-1301, USA.                                                          ;;
;;                                                                           ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")
(program)
(set-state-ok t)



;; BOZO would like to switch to ACL2's versions, but they don't include :class.
;; Sent Matt an email.  Hopefully this gets fixed in ACL2 3.4.


;; Info functions inspect the various rules and turn them into alists of the
;; form:
;;
;;   (key . (value1 ... valueN))
;;
;; When we print these alists with our "info" function, we only print "key:
;; value1".  This lets you store additional information in later values.  For
;; example, value1 might want to untranslate the term for prettier printing to
;; the user, or decode the type-set, etc.  Value2 can then include the original
;; term or undecoded type-set, so that programs can use that value instead.

(defun MILAWA::info-for-lemmas (lemmas numes ens wrld)
  (if (null lemmas)
      nil
    (let* ((rule                (car lemmas))
           (nume                (access rewrite-rule rule :nume))
           (rune                (access rewrite-rule rule :rune))
           (subclass            (access rewrite-rule rule :subclass))
           (lhs                 (access rewrite-rule rule :lhs))
           (rhs                 (access rewrite-rule rule :rhs))
           (hyps                (access rewrite-rule rule :hyps))
           (equiv               (access rewrite-rule rule :equiv))
           (backchain-limit-lst (access rewrite-rule rule :backchain-limit-lst))
           (heuristic-info      (access rewrite-rule rule :heuristic-info))
           )
      (if (or (eq numes t)
              (member nume numes))
          (cons `((:rune            ,rune)
                  (:nume            ,nume)
                  (:class           :rewrite)
                  (:enabledp        ,(if (enabled-runep rune ens wrld) t nil))
                  ,@(if (eq subclass 'meta)
                        `((:meta-fn ,lhs)
                          (:hyp-fn  ,(or hyps :none) ,hyps))
                      `((:lhs  ,(untranslate lhs nil wrld) ,lhs)
                        (:rhs  ,(untranslate rhs nil wrld) ,rhs)
                        (:hyps ,(untranslate-hyps hyps wrld) ,hyps)))
                  (:equiv               ,equiv)
                  (:backchain-limit-lst ,backchain-limit-lst)
                  (:subclass            ,subclass)
                  ,@(cond ((eq subclass 'backchain)
                           `((:loop-stopper ,heuristic-info)))
                          ((eq subclass 'definition)
                           `((:clique           ,(car heuristic-info))
                             (:controller-alist ,(cdr heuristic-info))))
                          (t
                           nil)))
                (MILAWA::info-for-lemmas (cdr lemmas) numes ens wrld))
        (MILAWA::info-for-lemmas (cdr lemmas) numes ens wrld)))))

(defun MILAWA::info-for-well-founded-relation-rules (rules)

; There is no record class corresponding to well-founded-relation rules.  But
; the well-founded-relation-alist contains triples of the form (rel mp . rune)
; and we assume rules is a list of such triples.

  (if (null rules)
      nil
    (let* ((rule (car rules))
           (rune (cddr rule)))
      (cons (list (list :rune                  rune)
                  (list :class                 :well-founded-relation)
                  (list :domain-predicate      (cadr rule))
                  (list :well-founded-relation (car rule)))
            (MILAWA::info-for-well-founded-relation-rules (cdr rules))))))

(defun MILAWA::info-for-built-in-clause-rules1 (rules numes ens wrld)
  (if (null rules)
      nil
    (let* ((rule   (car rules))
           (nume   (access built-in-clause rule :nume))
           (rune   (access built-in-clause rule :rune))
           (clause (access built-in-clause rule :clause)))
      (if (member nume numes)
          (cons (list (list :rune     rune)
                      (list :nume     nume)
                      (list :class    :built-in-clauses)
                      (list :enabledp (if (enabled-runep rune ens wrld) t nil))
                      (list :clause   (prettyify-clause clause nil wrld) clause))
                (MILAWA::info-for-built-in-clause-rules1 (cdr rules) numes ens wrld))
        (MILAWA::info-for-built-in-clause-rules1 (cdr rules) numes ens wrld)))))

(defun MILAWA::info-for-built-in-clause-rules (alist numes ens wrld)
  (if (null alist)
      nil
    (append (MILAWA::info-for-built-in-clause-rules1 (cdar alist) numes ens wrld)
            (MILAWA::info-for-built-in-clause-rules (cdr alist) numes ens wrld))))

(defun MILAWA::info-for-compound-recognizer-rules (rules numes ens wrld)
  (if (null rules)
      nil
    (let* ((rule     (car rules))
           (nume     (access recognizer-tuple rule :nume))
           (rune     (access recognizer-tuple rule :rune))
           (true-ts  (access recognizer-tuple rule :true-ts))
           (false-ts (access recognizer-tuple rule :false-ts))
           (strongp  (access recognizer-tuple rule :strongp)))
      (if (member nume numes)
          (cons (list (list :rune     rune)
                      (list :nume     nume)
                      (list :class    :compound-recognizer)
                      (list :enabledp (if (enabled-runep rune ens wrld) t nil))
                      (list :fn       (access recognizer-tuple rule :fn))
                      (list :true-ts  (decode-type-set true-ts) true-ts)
                      (list :false-ts (decode-type-set false-ts) false-ts)
                      (list :strongp  strongp))
                (MILAWA::info-for-compound-recognizer-rules (cdr rules) numes ens wrld))
        (MILAWA::info-for-compound-recognizer-rules (cdr rules) numes ens wrld)))))

(defun MILAWA::info-for-generalize-rules (rules numes ens wrld)
  (if (null rules)
      nil
    (let* ((rule    (car rules))
           (nume    (access generalize-rule rule :nume))
           (rune    (access generalize-rule rule :rune))
           (formula (access generalize-rule rule :formula)))
      (if (member nume numes)
          (cons (list (list :rune     rune)
                      (list :nume     nume)
                      (list :class    :generalize)
                      (list :enabledp (if (enabled-runep rune ens wrld) t nil))
                      (list :formula  (untranslate formula t wrld) formula))
                (MILAWA::info-for-generalize-rules (cdr rules) numes ens wrld))
        (MILAWA::info-for-generalize-rules (cdr rules) numes ens wrld)))))

(defun MILAWA::info-for-linear-lemmas (rules numes ens wrld)
  (if (null rules)
      nil
    (let* ((rule                (car rules))
           (nume                (access linear-lemma rule :nume))
           (rune                (access linear-lemma rule :rune))
           (hyps                (access linear-lemma rule :hyps))
           (concl               (access linear-lemma rule :concl))
           (max-term            (access linear-lemma rule :max-term))
           (backchain-limit-lst (access linear-lemma rule :backchain-limit-lst)))
      (if (member nume numes)
          (cons (list (list :rune                rune)
                      (list :nume                nume)
                      (list :class               :linear)
                      (list :enabledp            (if (enabled-runep rune ens wrld) t nil))
                      (list :hyps                (untranslate-hyps hyps wrld)    hyps)
                      (list :concl               (untranslate concl nil wrld)    concl)
                      (list :max-term            (untranslate max-term nil wrld) max-term)
                      (list :backchain-limit-lst backchain-limit-lst))
                (MILAWA::info-for-linear-lemmas (cdr rules) numes ens wrld))
        (MILAWA::info-for-linear-lemmas (cdr rules) numes ens wrld)))))

(defun MILAWA::info-for-eliminate-destructors-rule (rule numes ens wrld)
  (let ((rune             (access elim-rule rule :rune))
        (nume             (access elim-rule rule :nume))
        (hyps             (access elim-rule rule :hyps))
        (lhs              (access elim-rule rule :lhs))
        (rhs              (access elim-rule rule :rhs))
        (destructor-term  (access elim-rule rule :destructor-term))
        (destructor-terms (access elim-rule rule :destructor-terms))
        (crucial-position (access elim-rule rule :crucial-position)))
    (if (member nume numes)
        (list (list :rune             rune)
              (list :nume             nume)
              (list :class            :elim)
              (list :enabledp         (if (enabled-runep rune ens wrld) t nil))
              (list :hyps             (untranslate-hyps hyps wrld)                hyps)
              (list :lhs              (untranslate lhs nil wrld)                  lhs)
              (list :rhs              (untranslate rhs nil wrld)                  rhs)
              (list :destructor-term  (untranslate destructor-term nil wrld)      destructor-term)
              (list :destructor-terms (untranslate-lst destructor-terms nil wrld) destructor-terms)
              (list :crucial-position crucial-position))
      nil)))

;; (defun info-for-congruences (val numes ens wrld)

;; ; val is of the form (equiv geneqv1 ... geneqvk ... geneqvn).
;; ; This seems complicated so we'll punt for now.

;;   (declare (ignore val numes ens wrld))
;;   nil)

;; (defun info-for-coarsenings (val numes ens wrld)

;; ; It is not obvious how to determine which coarsenings are really new, so we
;; ; print nothing.

;;   (declare (ignore val numes ens wrld))
;;   nil)

(defun MILAWA::info-for-forward-chaining-rules (rules numes ens wrld)
  (if (null rules)
      nil
    (let* ((rule    (car rules))
           (rune    (access forward-chaining-rule rule :rune))
           (nume    (access forward-chaining-rule rule :nume))
           (trigger (access forward-chaining-rule rule :trigger))
           (hyps    (access forward-chaining-rule rule :hyps))
           (concls  (access forward-chaining-rule rule :concls)))
      (if (member nume numes)
          (cons (list (list :rune     rune)
                      (list :nume     nume)
                      (list :class    :forward-chaining)
                      (list :enabledp (if (enabled-runep rune ens wrld) t nil))
                      (list :trigger  (untranslate trigger nil wrld) trigger)
                      (list :hyps     (untranslate-hyps hyps wrld)   hyps)
                      (list :concls   (untranslate-hyps concls wrld) concls))
                (MILAWA::info-for-forward-chaining-rules (cdr rules) numes ens wrld))
        (MILAWA::info-for-forward-chaining-rules (cdr rules) numes ens wrld)))))

(defun MILAWA::info-for-type-prescriptions (rules numes ens wrld)
  (if (null rules)
      nil
    (let* ((rule      (car rules))
           (rune      (access type-prescription rule :rune))
           (nume      (access type-prescription rule :nume))
           (term      (access type-prescription rule :term))
           (hyps      (access type-prescription rule :hyps))
           (basic-ts  (access type-prescription rule :basic-ts))
           (vars      (access type-prescription rule :vars))
           (corollary (access type-prescription rule :corollary)))
      (if (member nume numes)
          (cons (list (list :rune      rune)
                      (list :nume      nume)
                      (list :class     :type-prescription)
                      (list :enabledp  (if (enabled-runep rune ens wrld) t nil))
                      (list :term      (untranslate term nil wrld)    term)
                      (list :hyps      (untranslate-hyps hyps wrld)   hyps)
                      (list :basic-ts  (decode-type-set basic-ts)     basic-ts)
                      (list :vars      vars)
                      (list :corollary (untranslate corollary t wrld) corollary))
                (MILAWA::info-for-type-prescriptions (cdr rules) numes ens wrld))
        (MILAWA::info-for-type-prescriptions (cdr rules) numes ens wrld)))))

(defun MILAWA::info-for-induction-rules (rules numes ens wrld)
  (if (null rules)
      nil
    (let* ((rule      (car rules))
           (rune      (access induction-rule rule :rune))
           (nume      (access induction-rule rule :nume))
           (pattern   (access induction-rule rule :pattern))
           (condition (access induction-rule rule :condition))
           (scheme    (access induction-rule rule :scheme)))
      (if (member nume numes)
          (cons (list (list :rune      rune)
                      (list :nume      nume)
                      (list :class     :induction)
                      (list :enabledp  (if (enabled-runep rune ens wrld) t nil))
                      (list :pattern   (untranslate pattern nil wrld) pattern)
                      (list :condition (untranslate condition t wrld) condition)
                      (list :scheme    (untranslate scheme nil wrld)  scheme))
                (MILAWA::info-for-induction-rules (cdr rules) numes ens wrld))
        (MILAWA::info-for-induction-rules (cdr rules) numes ens wrld)))))

(defun MILAWA::info-for-type-set-inverter-rules (rules numes ens wrld)
  (if (null rules)
      nil
    (let* ((rule     (car rules))
           (rune     (access type-set-inverter-rule rule :rune))
           (nume     (access type-set-inverter-rule rule :nume))
           (type-set (access type-set-inverter-rule rule :ts))
           (terms    (access type-set-inverter-rule rule :terms))
           )
      (if (member nume numes)
          (cons (list (list :rune      rune)
                      (list :nume      nume)
                      (list :class     :type-set-inverter)
                      (list :enabledp  (if (enabled-runep rune ens wrld) t nil))
                      (list :type-set  type-set)
                      (list :condition (untranslate-hyps terms wrld) terms))
                (MILAWA::info-for-type-set-inverter-rules (cdr rules) numes ens wrld))
        (MILAWA::info-for-type-set-inverter-rules (cdr rules) numes ens wrld)))))

(defun MILAWA::info-for-x-rules (sym key val numes ens wrld)

; See add-x-rule for an enumeration of rule classes that generate the
; properties shown below.  Keep this function in sync with find-rules-of-rune2.

  (cond
   ((eq key 'global-value)
    (case sym
      (well-founded-relation-alist

; Avoid printing the built-in anonymous rule if that is all we have here.

       (if (consp (cdr val))
           (MILAWA::info-for-well-founded-relation-rules val)
         nil))
      (built-in-clauses        (MILAWA::info-for-built-in-clause-rules val numes ens wrld))
      (type-set-inverter-rules (MILAWA::info-for-type-set-inverter-rules val numes ens wrld))
      (recognizer-alist        (MILAWA::info-for-compound-recognizer-rules val numes ens wrld))
      (generalize-rules        (MILAWA::info-for-generalize-rules val numes ens wrld))
      (otherwise nil)))
   (t
    (case key
      (lemmas                     (MILAWA::info-for-lemmas val numes ens wrld))
      (linear-lemmas              (MILAWA::info-for-linear-lemmas val numes ens wrld))
      (eliminate-destructors-rule (MILAWA::info-for-eliminate-destructors-rule val numes ens wrld))
      (congruences                (info-for-congruences val numes ens wrld))
      (coarsenings                (info-for-coarsenings val numes ens wrld))
      (forward-chaining-rules     (MILAWA::info-for-forward-chaining-rules val numes ens wrld))
      (type-prescriptions         (MILAWA::info-for-type-prescriptions val numes ens wrld))
      (induction-rules            (MILAWA::info-for-induction-rules val numes ens wrld))
      (otherwise nil)))))

(defun MILAWA::info-for-rules1 (props numes ens wrld)
  (cond ((null props)
         nil)
        ((eq (cadar props) *acl2-property-unbound*)
         (MILAWA::info-for-rules1 (cdr props) numes ens wrld))
        (t
         (append (MILAWA::info-for-x-rules (caar props) (cadar props) (cddar props) numes ens wrld)
                 (MILAWA::info-for-rules1 (cdr props) numes ens wrld)))))

(defun MILAWA::info-for-rule-classes-nil (name wrld)

; There is no record class corresponding to :rule-classes nil rules.  But we can at
; least look up the theorem that corresponds to this rule.

  (let ((thm              (getprop name 'theorem nil 'current-acl2-world wrld))
        (untranslated-thm (getprop name 'untranslated-theorem nil 'current-acl2-world wrld)))
    (if thm
        (list (list :name    name)
              (list :class   nil)
              (list :theorem untranslated-thm thm))
      nil)))

(defun info-fn (name state)
  (let ((wrld (w state)))
    (cond ((and (symbolp name)
                (not (keywordp name)))
           (let* ((name (deref-macro-name name (macro-aliases wrld)))
                  (props (actual-props (world-to-next-event (cdr (decode-logical-name name wrld))) nil nil))
                  (numes (strip-cars (getprop name 'runic-mapping-pairs nil 'current-acl2-world wrld))))
             (if (consp numes)
                 ;; There are proper numes for this name
                 (MILAWA::info-for-rules1 props numes (ens state) wrld)
               ;; No proper numes.  Maybe it's a rule-classes nil?
               (list (MILAWA::info-for-rule-classes-nil name wrld)))))
          (t
           (er hard 'pr
               "The argument to info-fn must be a non-keyword symbol.")))))




(defun max-length-of-any-key (symbols max)
  (if (consp symbols)
      (max-length-of-any-key (cdr symbols)
                             (max (length (symbol-name (car symbols))) max))
    max))

(defun downcase-all-but-first (str)
  (let* ((chars (coerce str 'list))
         (first (car chars))
         (rest  (string-downcase1 (cdr chars))))
    (coerce (cons first rest) 'string)))

(defun expand-keys-into-strings (symbols max-len)
  (if (consp symbols)
      (let* ((name (symbol-name (car symbols)))
            (len  (length name)))
        (cons (string-append (downcase-all-but-first name)
                             (cons #\: (make-list (- max-len len) :initial-element #\Space)))
              (expand-keys-into-strings (cdr symbols) max-len)))
    nil))

(defun print-info-entry1 (keys vals state)
  (if (not (consp keys))
      state
    (mv-let (col state)
            (fmt1 "~s0 ~q1"
                  (list (cons #\0 (car keys))
                        (cons #\1 (caar vals)))
                  0
                  *standard-co*
                  state
                  nil)
            (declare (ignore col))
            (print-info-entry1 (cdr keys) (cdr vals) state))))

(defun print-info-entry (entry state)
  (let* ((keys              (strip-cars entry))
         (vals              (strip-cdrs entry))
         (key-column-length (+ 2 (max-length-of-any-key keys 0)))
         (new-keys          (expand-keys-into-strings keys key-column-length)))
    (pprogn
     (print-info-entry1 new-keys vals state)
     (fms "" 0 *standard-co* state nil)
     )))

(defun print-info (info state)
  (if (not (consp info))
      state
    (pprogn (print-info-entry (car info) state)
            (print-info (cdr info) state))))

(defmacro info (name)
  `(let ((state (print-info (info-fn ,name state) state)))
     (mv nil :invisible state)))





#|

(logic)

(defun sample-nonrec-defun (x)
  (+ x 1))

(defun sample-rec-defun (x)
  (if (consp x)
      (+ (nfix (car x))
         (sample-rec-defun (cdr x)))
    0))

(defthm sample-rewrite-rule
  (equal (natp (sample-rec-defun x))
         t))

(defthm sample-type-prescription-rule
  (equal (natp (sample-rec-defun x))
         t)
  :rule-classes :type-prescription)

(defun sample-equiv (x y)
  (equal x y))

(defequiv sample-equiv)

(defcong sample-equiv equal (sample-rec-defun x) 1)

(defthm sample-fc-rule
  (implies (natp x)
           (equal (natp (sample-rec-defun x))
                  t))
  :rule-classes :forward-chaining)

(defthm sample-linear-rule
  (<= 0 (sample-rec-defun x))
  :rule-classes :linear)

(pr 'sample-nonrec-defun)
(info 'sample-nonrec-defun)

(pr 'sample-rewrite-rule)
(info 'sample-rewrite-rule)

(pr 'sample-type-prescription-rule)
(info 'sample-type-prescription-rule)

(pr 'sample-equiv)
(info 'sample-equiv)

(pr 'sample-equiv-implies-equal-sample-rec-defun-1)
(info 'sample-equiv-implies-equal-sample-rec-defun-1)

(pr 'sample-equiv-is-an-equivalence)
(info 'sample-equiv-is-an-equivalence)

(pr 'sample-fc-rule)
(info 'sample-fc-rule)

(pr 'sample-linear-rule)
(info 'sample-linear-rule)

(defaxiom crock
  (equal (car x) (car x))
  :rule-classes nil)

(pr 'crock)
(info 'crock)




|#

