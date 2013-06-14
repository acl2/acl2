
; Def-functional-instance: automates defining theorems that are functional
; instances of existing ones.

; Copyright (C) 2010 Centaur Technology
;
; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/
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
; Original author: Sol Swords <sswords@centtech.com>


(in-package "ACL2")

(include-book "bstar")

(defun look-for-goal-hint (hints)
  (if (atom hints)
      nil
    (or (and (consp (car hints))
             (stringp (caar hints))
             (standard-char-listp (coerce (caar hints) 'list))
             (equal (string-upcase (caar hints)) "GOAL"))
        (look-for-goal-hint (cdr hints)))))

(defun def-functional-instance-fn
  (newname oldname subst hints rule-classes rule-classesp state)
  (declare (xargs :stobjs state
                  :mode :program))
  (b* ((world (w state))
       (body (fgetprop oldname 'theorem nil world))
       (rule-classes (if rule-classesp
                         rule-classes
                       (fgetprop oldname 'classes nil world)))
       ((unless body)
        (er soft 'def-functional-instance-fn
            "Theorem ~x0 not found in the ACL2 world" oldname))
       (alist (pairlis$ (strip-cars subst)
                        (strip-cadrs subst)))
       (new-body (sublis alist body))
       (untrans-body (untranslate new-body nil world))
       (form `(defthm ,newname
                ,untrans-body
                :hints (("goal" :use
                         ((:functional-instance
                           ,oldname
                           . ,subst)))
                        . ,hints)
                :rule-classes ,rule-classes)))
    (and (look-for-goal-hint hints)
         (cw "WARNING:  In DEF-FUNCTIONAL-INSTANCE, any user-provided hint ~
keyed on subgoal \"GOAL\" will be ignored.  If your proof fails, please try ~
again with a computed hint or a subgoal specifier other than \"GOAL\". "))
    (value form)))
       



(defmacro def-functional-instance
  (newname oldname subst &key hints (rule-classes 'nil rule-classesp))
  ":Doc-section Events
Functionally instantiate a pre-existing theorem to prove a new one.~/

Usage:
~bv[]
 (def-functional-instance
   new-thm-name
   orig-thm-name
   ((orig-fn substitute-fn) ...)
   :hints (...)                   ;; optional
   :rule-classes rule-classes)    ;; optional
~ev[]

Def-functional-instance attempts to define a new theorem based on functionally
instantiating an existing one with a user-provided function substitution.  It
looks up the body of the theorem named ORIG-THM-NAME in the ACL2 world and
applies the functional substitution, replacing each ORIG-FN with SUBSTITUTE-FN
in the theorem body.  It then submits this as a new theorem named NEW-THM-NAME
with a hint to prove it using a functional instance of the original theorem.
This theorem has either the given rule-classes or, if this argument is omitted,
the rule-classes of the original theorem.

Sometimes further hints are needed to show that the functional instantiation is
valid.  These may be given by the :hints keyword.  Note, however, that there is
already a hint provided at \"goal\", so that if one of the user-provided hints
uses this as its subgoal specifier, this hint will be ignored.  The extra hints
given should either be computed hints or reference later subgoals. ~/~/
"
  `(make-event
    (def-functional-instance-fn
      ',newname ',oldname ',subst ',hints ',rule-classes ',rule-classesp state)))
