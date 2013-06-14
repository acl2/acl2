; ACL2 Theory Linter
; Copyright (C) 2013 Kookamara LLC
;
; Contact:
;   Kookamara LLC
;   11410 Windermere Meadows
;   Austin, TX 78759
;
; This program is free software; you can redistribute it and/or modify it under
; the terms of the GNU General Public License as published by the Free Software
; Foundation; either version 2 of the License, or (at your option) any later
; version.  This program is distributed in the hope that it will be useful but
; WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
; FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
; more details.  You should have received a copy of the GNU General Public
; License along with this program; if not, write to the Free Software
; Foundation, Inc., 51 Franklin Street, Suite 500, Boston, MA 02110-1335, USA.
;
; Original authors: Jared Davis <jared@kookamara.com>

(in-package "ACL2")
(include-book "cutil/da-base" :dir :system)
(include-book "system/origin" :dir :system)
(include-book "str/cat" :dir :system)
(include-book "tools/rulesets" :dir :system)
(include-book "misc/assert" :dir :system)
(include-book "defsort/duplicated-members" :dir :system)
(include-book "clause-processors/unify-subst" :dir :system)
(set-state-ok t)
(program)


;; (DA-DEFREC-EMULATION REC) -- Adds defaggregate-style emulation for DEFREC records
;;   - Adds foo->bar style accessors
;;   - Adds defaggregate-like b* binders

(defun flatten-defrec-fields (x)
  ;; Flatten a defrec field layout (which can be an arbitrary shaped cons tree)
  ;; into an ordinary list.
  (if (atom x)
      (and x (list x))
    (append (flatten-defrec-fields (car x))
            (flatten-defrec-fields (cdr x)))))

(defun look-up-defrec-fields (rec world)
  ;; Horrible awful thing.  The fields for a defrec aren't saved anywhere
  ;; explicitly, but we can look them up in the body of the MAKE function.
  ;; See the function MAKE-RECORD-MAKER in the acl2 sources.
  (b* ((maker (record-maker-function-name rec))
       (body  (getprop maker 'macro-body nil 'current-acl2-world world))
       ((unless body)
        (er hard? 'look-up-defrec-field-layout
            "Can't find macro-body for maker ~x0 of defrec ~x1.  is ~x1 even ~
             a defrec?" maker rec))
       (quoted-layout (third body))
       ((unless (quotep quoted-layout))
        (er hard? 'look-up-defrec-field-layout
            "Sanity check failed, field layout of ~x0 is not a quotep?" rec)))
    (flatten-defrec-fields
     (unquote quoted-layout))))

(defun da-accessor-for-defrec-field (rec field)
  ;; Create a defaggregate-style accessor foo->bar for field bar of defrec foo
  `(defun-inline ,(cutil::da-accessor-name rec field) (x)
     (declare (xargs :guard (,(intern$ (str::cat "WEAK-" (symbol-name rec) "-P") "ACL2") x)))
     (access ,rec x ,(intern$ (symbol-name field) "KEYWORD"))))

(defun da-accessors-for-defrec-fields (rec fields)
  (if (atom fields)
      nil
    (cons (da-accessor-for-defrec-field rec (car fields))
          (da-accessors-for-defrec-fields rec (cdr fields)))))

(defun da-defrec-emulation-fn (rec world)
  (let ((fields (look-up-defrec-fields rec world)))
    `(progn
       ,@(da-accessors-for-defrec-fields rec fields)
       ,(cutil::da-make-binder rec fields))))

(defmacro da-defrec-emulation (rec)
  `(make-event
    (b* ((world (w state)))
      (value (da-defrec-emulation-fn ',rec world)))))

(da-defrec-emulation rewrite-rule)



;; Gather all rewrite rules in the universal theory

(defun find-rules-of-runes (runes world)
  (if (atom runes)
      nil
    (append (find-rules-of-rune (car runes) world)
            (find-rules-of-runes (cdr runes) world))))

(defun filter-non-rewrite-rules (x)
  (cond ((atom x)
         nil)
        ((not (weak-rewrite-rule-p (car x)))
         (filter-non-rewrite-rules (cdr x)))
        (t
         (cons (car x)
               (filter-non-rewrite-rules (cdr x))))))

(defun get-all-rewrite-rules (world)
  (filter-non-rewrite-rules
   (find-rules-of-runes (rules-of-class :rewrite :here) world)))

(defun filter-disabled-rules (x ens state)
  (cond ((atom x) 
         nil)
        ((active-runep (rewrite-rule->rune (car x)))
         (cons (car x) (filter-disabled-rules (cdr x) ens state)))
        (t
         (filter-disabled-rules (cdr x) ens state))))

(defun get-enabled-rewrite-rules (state)
  (let* ((world (w state))
         (ens   (ens state))
         (rules (get-all-rewrite-rules world)))
    (filter-disabled-rules rules ens state)))



;; Looking for compatible, redundant rules

(defun unforce-hyp (x)
  (if (and (consp x)
           (or (eq (ffn-symb x) 'force)
               (eq (ffn-symb x) 'case-split)))
      (second x)
    x))

(defun unforce-hyps (x)
  (if (atom x)
      nil
    (cons (unforce-hyp (car x))
          (unforce-hyps (cdr x)))))

(defun rule-redundant-p (x y)
  ;; X is "redundant" with respect to Y if its LHS unifies with the LHS of Y,
  ;; and it has the same/worse hyps.
  (b* (((rewrite-rule x) x)
       ((rewrite-rule y) y)

       ((unless (and (or (eq x.subclass 'backchain)
                         (eq x.subclass 'abbreviation))
                     (or (eq y.subclass 'backchain)
                         (eq y.subclass 'abbreviation))))
        ;; Don't try to deal with meta/other future rules
        nil)

       ((when (or (and (eq x.subclass 'backchain) x.heuristic-info)
                  (and (eq y.subclass 'backchain) y.heuristic-info)))
        ;; Don't include any rules with loop-stoppers because they're likely to be
        ;; commutativity rules that look highly redundant with everything else.
        nil)

       ((unless (eq x.equiv y.equiv))
        ;; This may be sort of too strong, but might be pretty useful for filtering
        ;; out noise.
        nil)

       ((mv okp sigma) (simple-one-way-unify x.lhs y.lhs nil))
       ((unless okp)
        nil)

       (xhyps-rw (substitute-into-list (unforce-hyps x.hyps) sigma)))
    (subsetp-equal xhyps-rw (unforce-hyps y.hyps))))

(defun find-redundancy (a x)
  (cond ((atom x)
         nil)
        ((and (rule-redundant-p a (car x))
              (not (equal a (car x))))
         (list (list :redundant a (car x))))
        (t
         (find-redundancy a (cdr x)))))

(defun find-redundancies (x y)
  (if (atom x)
      nil
    (append (find-redundancy (car x) y)
            (find-redundancies (cdr x) y))))

(defun find-redundancies-top (x)
  (find-redundancies x x))



(defun summarize-rule (rule state)
  (b* (((rewrite-rule rule) rule)
       (concl (list rule.equiv rule.lhs rule.rhs))
       (summary (cond ((<= 2 (len rule.hyps))
                       `(implies (and . ,rule.hyps) ,concl))
                      ((consp rule.hyps)
                       `(implies ,(car rule.hyps) ,concl))
                      (t
                       concl)))
       (name (second rule.rune))
       ((mv er origin state) (origin-fn name 'summarize-rule state))
       (origin (if er
                   (prog2$ (cw "Error in summarize-rule: ~x0" er)
                           :error)
                 origin)))
    (mv `(defthm ,name ,summary :from ,origin)
        state)))

(defun summarize-redundancy (x state)
  (b* (((unless (eq (car x) :redundant))
        (er hard? 'summarize-redundancy "expected (:redundant rule rule), found ~x0" x)
        (mv nil state))
       ((mv sum1 state) (summarize-rule (second x) state))
       ((mv sum2 state) (summarize-rule (third x) state)))
    (mv (list :redundant sum1 sum2)
        state)))

(defun summarize-redundancies (x state)
  (b* (((when (atom x))
        (mv nil state))
       ((mv car state) (summarize-redundancy (car x) state))
       ((mv cdr state) (summarize-redundancies (cdr x) state)))
    (mv (cons car cdr) state)))


(defun lint-fn (state)
  (summarize-redundancies
   (find-redundancies-top (get-enabled-rewrite-rules state))
   state))

(defmacro lint ()
  `(lint-fn state))


;; there could probably be some kind of quick filtering based on leading function symbol to
;; narrow the search down...



#|| Example:

(include-book
 "tools/lint" :dir :system)
(include-book
 "centaur/bitops/top" :dir :system)
(lint)

||#
