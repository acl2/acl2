; CUTIL - Centaur Basic Utilities
; Copyright (C) 2008-2012 Centaur Technology
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
; Original authors: Jared Davis <jared@centtech.com>
;                   Sol Swords <sswords@centtech.com>

(in-package "STD")
(include-book "xdoc/top" :dir :system)
(include-book "support")
(include-book "str/ieqv" :dir :system)
(include-book "tools/rulesets" :dir :system)
(program)

(defxdoc defrule
  :parents (std/util)
  :short "A slightly enhanced version of @(see defthm)."

  :long "<p>@('defrule') is an drop-in replacement for @('defthm') that
adds:</p>

<ul>

<li>A more concise syntax for @(see acl2::hints) that target
@('\"Goal\"').</li>

<li>A very concise syntax for
@({
  (encapsulate ()
    (local (in-theory (e/d ...)))
    (defthm ...))
})
with @(see acl2::rulesets) integration.</li>

<li>Integration with @(see xdoc).  You can give @(':parents'), @(':short'), and
@(':long') documentation right at the top level of the @('defrule').</li>

</ul>

<h3>Top-level Hints</h3>

<p>You can give @('\"Goal\"') hints directly at the top level of the rule.
For example:</p>

@({
  (defrule repeated-insert           -->  (defthm repeated-insert
    (equal (insert a (insert a X))          (equal (insert a (insert a X))
           (insert a X))                           (insert a X))
    :induct t                               :hints((\"Goal\"
    :expand ((...)))                                :induct t
                                                    :expand ((...))))
})

<p>This works for any hint except for @(':instructions').  If you give
top-level hints and a \"Goal\" hint, the top-level hints will be appended onto
the front of the explicit \"Goal\" hint.</p>

<h3>Theory Support</h3>

<p>Theory hints are especially common.</p>

<p>One option is to just give a top-level @(':in-theory') hint, and it just
gets attached to goal.  But note that such hints are not inherited when you
give an in-theory hint in a subgoal.  This can be quite confusing and
annoying.</p>

<p>As an alternative, @('defrule') also adds top-level @(':enable'),
@(':disable'), and @(':e/d') options.  When you use these keywords, they turn
into a local theory event that is submitted before your defthm.  That way,
they're part of the theory that is inherited by all subgoals.</p>

<p>To make @(':enable'), @(':disable'), and @(':e/d') slightly more powerful,
they are actually integrated with the @(see acl2::rulesets) book.  In
particular, these keywords are always translated into an @(see acl2::e/d*).</p>

<p>Some examples:</p>

@({
  (defrule foo            -->  (encapsulate ()
     ...                         (local (in-theory (e/d* (append) (revappend))))
     :enable append              (defthm foo ...))
     :disable revappend)
})

@({
  (defrule bar            -->  (encapsulate ()
     ...                         (local (in-theory (e/d* (append rev)
     :enable (append rev)                                revappend
     :disable revappend                                  (logior)
     :e/d ((logior) (logand)))                           (logand)))
                                 (defthm bar ...))
})")

(defxdoc defruled
  :parents (defrule)
  :short "Variant of @(see defrule) that disables the theorem afterwards."
  :long "<p>This is identical to @('defrule') except that the theorem is
generated using @(see defthmd) instead of @(see defthm).</p>")

(defconst *defrule-keywords*
  (union-equal '(:hints
                 :rule-classes
                 :otf-flg
                 :instructions
                 :doc
                 :parents
                 :short
                 :long
                 :enable
                 :disable
                 :e/d)
               acl2::*hint-keywords*))

(defun split-alist (keys al)
  "Returns (MV NAMED-PART UNNAMED-PART)"
  (b* (((when (atom al))
        (mv nil nil))
       ((mv named-rest unnamed-rest)
        (split-alist keys (cdr al)))
       ((when (member-equal (caar al) keys))
        (mv (cons (car al) named-rest) unnamed-rest)))
    (mv named-rest (cons (car al) unnamed-rest))))

(defun find-goal-entry-in-user-hints (user-hints)
  (cond ((atom user-hints)
         nil)
        ((and (consp (car user-hints))
              (stringp (caar user-hints))
              (str::istreqv "goal" (caar user-hints)))
         (car user-hints))
        (t
         (find-goal-entry-in-user-hints (cdr user-hints)))))

(defun hints-alist-to-plist (hints-al)
  (if (atom hints-al)
      nil
    (list* (caar hints-al)
           (cdar hints-al)
           (hints-alist-to-plist (cdr hints-al)))))

(defun merge-keyword-hints-alist-into-ordinary-hints (hints-al user-hints)
  (b* (((when (atom hints-al))
        user-hints)
       (user-goal-entry (find-goal-entry-in-user-hints user-hints))
       (user-hints      (remove-equal user-goal-entry user-hints))
       (user-goal       (cdr user-goal-entry))
       ;; We just arbitrarily say the top-level hints come first.
       ;; We could eventually try to do some smarter merge, e.g., for
       ;; theory hints, but that's just awful anyway.
       (new-goal        (append (hints-alist-to-plist hints-al)
                                user-goal))
       (new-entry       (cons "Goal" new-goal)))
    (cons new-entry user-hints)))

(defun defrule-fn (name args disablep)
  (b* ((ctx `(defrule ,name))
       ((mv kwd-alist args)
        (extract-keywords ctx *defrule-keywords* args nil))

       ((mv hint-alist &)
        ;; We'll arbitrarily say that :instructions goes to the DEFTHM,
        ;; not to the goal hints.
        (split-alist (remove :instructions acl2::*hint-keywords*)
                     kwd-alist))

       ;; Global enable, disable, e/d with rulesets integration
       (enable  (cdr (assoc :enable kwd-alist)))
       (disable (cdr (assoc :disable kwd-alist)))
       (e/d     (cdr (assoc :e/d kwd-alist)))
       ;; Convenience: supports both :enable foo and :enable (foo bar ...)
       (enable  (if (and enable (atom enable))
                    (list enable)
                  enable))
       (disable (if (and disable (atom disable))
                    (list disable)
                  disable))
       (theory-hint
        (if (or enable disable e/d)
            ;; Merge them into a single e/d* form.  Note that e/d*
            ;; takes alternating list of enables/disables, so this
            ;; is very easy;
            `(local (in-theory (acl2::e/d* ,enable ,disable . ,e/d)))
          nil))

       (hints (cdr (assoc :hints kwd-alist)))
       (hints (merge-keyword-hints-alist-into-ordinary-hints hint-alist hints))

       ((unless (tuplep 1 args))
        (er hard? 'defrule
            (if (atom args)
                "In ~x0: no formula found?"
              "In ~x0: multiple formulas found?")
            ctx))
       (formula (car args))

       (parents   (cdr (assoc :parents kwd-alist)))
       (short     (cdr (assoc :short kwd-alist)))
       (long      (cdr (assoc :long kwd-alist)))
       (want-xdoc (or parents short long))

       (thm `(,(if disablep 'defthmd 'defthm) ,name
               ,formula
               :hints        ,hints
               ,@(let ((look (assoc :rule-classes kwd-alist)))
                   (and look `(:rule-classes ,(cdr look))))
               :otf-flg      ,(cdr (assoc :otf-flg kwd-alist))
               :instructions ,(cdr (assoc :instructions kwd-alist))
               :doc          ,(cdr (assoc :doc kwd-alist)))))

    (if (and (not want-xdoc)
             (not theory-hint))
        thm
      `(defsection ,name
         ,@(and parents `(:parents ,parents))
         ,@(and short   `(:short ,short))
         ,@(and long    `(:long ,long))
         ,theory-hint
         ,thm))))

(defmacro defrule (name &rest args)
  (defrule-fn name args nil))

(defmacro defruled (name &rest args)
  (defrule-fn name args t))
