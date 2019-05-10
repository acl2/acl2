; Def-functional-instance: automates defining functional instances of existing theorems
; Copyright (C) 2010 Centaur Technology
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

(defxdoc def-functional-instance
  :parents (functional-instantiation)
  :short "Functionally instantiate a pre-existing theorem to prove a new one."

:long "<p>Usage:</p>

@({
 (def-functional-instance new-thm-name
   orig-thm-name
   ((orig-fn substitute-fn) ...)
   :hints (...)                   ;; optional
   :rule-classes rule-classes)    ;; optional
})

<p>Def-functional-instance attempts to define a new theorem based on
functionally instantiating an existing one with a user-provided function
substitution.  It looks up the body of the theorem named ORIG-THM-NAME in the
ACL2 world and applies the functional substitution, replacing each ORIG-FN with
SUBSTITUTE-FN in the theorem body.  It then submits this as a new theorem named
NEW-THM-NAME with a hint to prove it using a functional instance of the
original theorem.  This theorem has either the given rule-classes or, if this
argument is omitted, the rule-classes of the original theorem.</p>

<p>Sometimes further hints are needed to show that the functional instantiation
is valid.  These may be given by the :hints keyword.  Note, however, that there
is already a hint provided at \"goal\", so that if one of the user-provided
hints uses this as its subgoal specifier, this hint will be ignored.  The extra
hints given should either be computed hints or reference later subgoals.</p>")

(defun look-for-goal-hint (hints)
  (if (atom hints)
      nil
    (or (and (consp (car hints))
             (stringp (caar hints))
             (standard-char-listp (coerce (caar hints) 'list))
             (equal (string-upcase (caar hints)) "GOAL")
             (car hints))
        (look-for-goal-hint (cdr hints)))))

(defun def-functional-instance-fn
  (newname oldname subst hints rule-classes rule-classesp
           translate macro-subst by-hint-p state)
  (declare (xargs :stobjs state :mode :program))
  (b* ((world (w state))
       (body (if translate
                 (fgetprop oldname 'theorem nil world)
               (fgetprop oldname 'untranslated-theorem nil world)))
       (rule-classes (if rule-classesp
                         rule-classes
                       (fgetprop oldname 'classes nil world)))
       ((unless body)
        (er soft 'def-functional-instance-fn
            "Theorem ~x0 not found in the ACL2 world" oldname))
       (alist (append (pairlis$ (strip-cars subst)
                                (strip-cadrs subst))
                      (pairlis$ (strip-cars macro-subst)
                                (strip-cadrs macro-subst))))
       (new-body (sublis alist body))
       (untrans-body (if translate
                         (untranslate new-body nil world)
                       new-body))
       (form `(defthm ,newname
                ,untrans-body
                :hints (("goal"
                         ,@(if by-hint-p
                               `(:by (:functional-instance ,oldname . ,subst))
                             `(:use ((:functional-instance ,oldname . ,subst))))
                         . ,(cdr (look-for-goal-hint hints)))
                        . ,hints)
                :rule-classes ,rule-classes)))
;;     (and (look-for-goal-hint hints)
;;          (cw "WARNING:  In DEF-FUNCTIONAL-INSTANCE, any user-provided hint ~
;; keyed on subgoal \"GOAL\" will be ignored.  If your proof fails, please try ~
;; again with a computed hint or a subgoal specifier other than \"GOAL\". "))
    (value form)))

(defmacro def-functional-instance
  (newname oldname subst &key hints (rule-classes 'nil rule-classesp)
           (translate 't)
           (by-hint-p 'nil)
           macro-subst)
  `(make-event
    (def-functional-instance-fn
      ',newname ',oldname ',subst ',hints ',rule-classes ',rule-classesp ',translate ',macro-subst ',by-hint-p state)))
