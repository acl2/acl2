; ACL2 Theory Linter
; Copyright (C) 2013 Kookamara LLC
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
;
; Original author: Jared Davis <jared@kookamara.com>

(in-package "ACL2")
(include-book "std/util/da-base" :dir :system)
(include-book "std/util/defaggrify-defrec" :dir :system)
(include-book "system/origin" :dir :system)
(include-book "std/strings/cat" :dir :system)
(include-book "tools/rulesets" :dir :system)
(include-book "defsort/duplicated-members" :dir :system)
(include-book "clause-processors/unify-subst" :dir :system)
(set-state-ok t)
(program)

(std::defaggrify-defrec rewrite-rule)

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
       ((mv er origin state) (origin-fn name state))
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


;; there could probably be some kind of quick filtering based on leading function symbol to
;; narrow the search down...



#|| Example:

(include-book
 "tools/lint" :dir :system)
(include-book
 "centaur/bitops/top" :dir :system)
(lint-fn state)

||#
