; Standard Utilities Library
; Copyright (C) 2008-2014 Centaur Technology
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

(in-package "STD")
(include-book "xdoc/top" :dir :system)
(include-book "support")
(include-book "tools/rulesets" :dir :system)
(program)

(defxdoc defrule
  :parents (std/util)
  :short "An enhanced version of @(see defthm)."

  :long "<p>@('defrule') is a drop-in replacement for @('defthm') that
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

<li>The ability to make the theorem local.</li>

<li>The ability to provide lemmas and include books in support of the theorem's
proof.</li>

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

<h3>Support for @('Local')</h3>

<p>Another option is to provide a non-@('nil') value to the keyword argument
@(':local').  This results in surrounding the rule with a @(see
acl2::local).</p>

<h3>Supporting Lemmas and Books</h3>

<p>We often write lemmas in support of one larger theorem.  In this case, you
can provide these lemmas as a list of events with the @(':prep-lemmas')
argument.  Despite the name, it is also possible to include function
definitions with the @(':prep-lemmas') keyword; for instance, when a recursive
function is needed to serve as an induction scheme. Note that including a book
via @(':prep-lemmas') does not work.</p>

<p>To include a book or many books for use in the main theorem you are proving,
supply a list of include-book commands with the @(':prep-books')
argument.</p>

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
})

@({
  (defrule baz            -->  (local
      ...                        (encapsulate ()
      :local t)                    (defthm baz ...)))
})

@({
  (defrule lets-loop                  --> (defsection lets-loop
    (equal (+ x y)                          (local
           (+ y x))                          (encapsulate ()
                                              (defrule pretend-we-need-this
    :prep-lemmas                                ...)
    ((defrule pretend-we-need-this            (defrule pretend-we-need-this-too
       ...)                                     ...)))
     (defrule pretend-we-need-this-too        (local (progn (include-book
       ...))                                                \"arithmetic/top\"
                                                            :dir :system)))
    :prep-books                             (defthm lets-loop (equal (+ x y) (+ y x))
      ((include-book \"arithmetic/top\"             ...))
      :dir :system)))
})
")

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
                 :e/d
                 :local
                 ;; [Jared] BOZO I kind of wish we didn't have prep-lemmas and
                 ;; prep-books; we could just have :prepwork instead, which
                 ;; would be more consistent with, e.g., define.  Maybe a good
                 ;; compromise for backwards compatibility would be to just add
                 ;; a :prepwork option, but continue to support prep-lemmas and
                 ;; prep-books just as they are now, but remove them from the
                 ;; documentation...?
                 :prep-lemmas
                 :prep-books)
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
              (string-equal "goal" (caar user-hints)))
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
       (local (cdr (assoc :local kwd-alist)))
       (prep-lemmas (cdr (assoc :prep-lemmas kwd-alist)))
       (prep-books (cdr (assoc :prep-books kwd-alist)))

       ((unless (tuplep 1 args))
        (er hard? 'defrule
            (if (atom args)
                "In ~x0: no formula found?"
              "In ~x0: multiple formulas found?  Forget parens around a list ~
               of runes?")
            ctx))
       (formula (car args))

       (parents   (cdr (assoc :parents kwd-alist)))
       (short     (cdr (assoc :short kwd-alist)))
       (long      (cdr (assoc :long kwd-alist)))
       (want-xdoc (or parents short long))

       (prep-lemmas-form
        (if prep-lemmas
            `(local (encapsulate () ,@prep-lemmas))
          nil))

       (prep-books-form
        (if prep-books
            `(local (progn ,@prep-books))
          nil))

       (thm `(,(if disablep 'defthmd 'defthm) ,name
               ,formula
               :hints        ,hints
               ,@(let ((look (assoc :rule-classes kwd-alist)))
                   (and look `(:rule-classes ,(cdr look))))
               :otf-flg      ,(cdr (assoc :otf-flg kwd-alist))
               :instructions ,(cdr (assoc :instructions kwd-alist))
; Commented out by Matt K. for post-v-7.1 removal of :doc for defthm:
;              :doc          ,(cdr (assoc :doc kwd-alist))
               ))

       (event
        (if (and (not want-xdoc)
                 (not theory-hint)
                 (not prep-lemmas)
                 (not prep-books))
            thm
          `(with-output
             :stack :push
             :off :all
             (defsection ,name
               ,@(and parents `(:parents ,parents))
               ,@(and short   `(:short ,short))
               ,@(and long    `(:long ,long))
               ,@(and prep-lemmas-form
                      `((with-output :stack :pop ,prep-lemmas-form)))
               ,@(and prep-books-form
                      `((with-output :stack :pop ,prep-books-form)))
               ;; The theory-hint has to come after the inclusion of books, so
               ;; we can disable rules that come from the books.
               ,@(and theory-hint
                      `((with-output
                          ;; I think we don't want to show the user the theory
                          ;; event happening because that'd be verbose.  But
                          ;; the theory hint could cause errors in case of things
                          ;; like theory invariant violations or trying to enable
                          ;; or disable rules that don't exist, so we need to be
                          ;; sure to turn on error output at least.  BOZO maybe
                          ;; we should also turn on warnings here, e.g., for
                          ;; theory warnings?  (but those are usually annoying
                          ;; anyway...)
                          :on (error)
                          ,theory-hint)))
               (with-output :stack :pop ,thm))))))
    (if local
        `(local ,event)
      event)))

(defmacro defrule (name &rest args)
  (defrule-fn name args nil))

(defmacro defruled (name &rest args)
  (defrule-fn name args t))

(defmacro defrulel (name &rest rst)
  `(defrule ,name :local t ,@rst))

(defmacro defruledl (name &rest rst)
  `(defruled ,name :local t ,@rst))


(defxdoc rule
  :parents (defrule thm)
  :short "A @(see thm)-like version of @(see defrule)."
  :long "<p>The @('rule') macro is a thin wrapper around @(see defrule).  It
supports all of the same syntax extensions like top-level @(':enable') and
@(':expand') @(see acl2::hints).  However, like @(see thm), @('rule') does not
take a rule name and does not result in the introduction of a rule
afterward.</p>

<p>Examples:</p>

@({
    (rule (implies x x))                    ;; will work

    (rule (equal (append x y)               ;; will fail
                 (append y x))
          :enable append
          :expand (append y x))

    (rule (equal (consp x)                  ;; will work
                 (if (atom x) nil t))
          :do-not '(generalize fertilize))
})

<p>The @('rule') command is implemented with a simple @(see make-event).
Unlike @(see thm), @('rule') calls are valid embedded events.  However, on
success a @('rule') merely expands into @('(value-triple :success)').  No
record of the rule's existence is found in the world, so there is no way to use
the rule once it has been proven, etc.</p>")

(defmacro rule (&rest args)
  `(with-output
     ;; You might think we shouldn't turn off error here, but the interior
     ;; er-progn is going to run the actual event, and we don't want to see a
     ;; bunch of extra junk about the error here.
     :off :all
     :stack :push
     (make-event
      (er-progn (with-output :stack :pop
                  (defrule temporary-rule
                    ,@args
                    :rule-classes nil))
                (value '(value-triple :invisible))))))
