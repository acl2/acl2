; Copyright (C) 2013, Regents of the University of Texas
; Written by Panagiotis Manolios and J Strother Moore, July 7, 2001
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; (certify-book "/u/moore/priorities")

; Abstract

; This book allows you to attach a non-negative rational priority
; number to your rules.  The priority number inversely indicates the
; importance of the rule: smaller numbers indicate more importance.
; After attaching priorities to your rules, all rules with non-0
; priority are to be disabled.  A default computed hint causes the
; simplifier to behave as follows: when a formula is stable under
; simplification at a given priority level, the priority level is
; bumped up to the next level and the rules at that level are
; additionally enabled.

; Thus, you may think of the rules as being grouped into a set of
; concentric circles.  The innermost circle contains the rules of
; priority 0.  The next circle contains all those rules plus the ones
; given the next highest priority, etc.  The simplifier starts with
; the rules in the innermost circle and simplifies until a subgoal is
; stable in that circle.  Then it wides the circle and starts over.

; Use

; To use priority phased simplification,

; (include-book "books/misc/priorities")

; (set-default-hints (list *priority-phased-simplification* ...))

; where ... includes any other default hints you wish to install.

; Then, establish your priorities with add-priorities, etc.  Make sure
; that all prioritized rules are disabled in the global current
; theory.  This can be done by invoking (DISABLE-PRIORITIZED-RUNES)
; after you've declared the last prioritized rule.  If you add or
; delete prioritized rules, you must manage the disabling/enabling
; yourself.

; Then proceed.

; History

; The idea and utility of priority phased simplification was first
; suggested by Pete Manolios, in 1999.  He and Moore did some early
; experiments, modifying a private copy of ACL2 to support the notion.
; In that design, priorities were assigned when rules were added and
; heuristics were proposed for automatically computing priorities from
; defuns and defthms.  Consideration of priorities were fundamental to
; the operation of the ``waterfall.''  The design was somewhat more
; elaborate than the scheme described here.  But we never implemented
; a production version of the scheme.

; In July, 2001, computed hints were elaborated to include the
; stable-under-simplificationp flag and the :computed-hint-replacement
; feature.  These changes were ``inspired'' by Moore's unhappiness
; over the complexity of his ``staged simplifier hack'' for Rockwell,
; where he introduced bogus :elim rule and exploited it to cause a
; rewrite rule to fire when a subgoal was stable under simplification.
; After returning from Rockwell, Moore was working on various
; ``todos'' in preparation of the release of Version  2.6 and these
; changes involved computed hints, namely a suggestion by Jun Sawada
; that we have a default computed hint and a suggestion by Rob Sumners
; that we allow a hint to specify whether or not it is to be made
; available to its the children of the subgoal to which it applied.
; Kaufmann and Moore then designed the current (as of Version  2.6)
; version of computed hints and documented them.  In the course of
; writing documentation, Moore recalled the Manolios idea of priority
; based rewriting and suggested this book.

(in-package "ACL2")

; We will keep a table, called priorities, that assigns priorities to
; rules.  The table is an alist, of course, accessed by (table-alist
; 'priorities world).  The keys will be assumed to be positive
; rationals.  The values will be assumed to be lists of runes or other
; items suitable for inclusion in a theory.  The operations on the
; table will be to add or delete an item from a given priority list,
; to clear all items from a given priority level, and to clear the
; table.

(table priorities nil nil :guard
       (and (rationalp key)
            (< 0 key)
            (theoryp1 val (macro-aliases world) world)))

(defmacro add-priority (n &rest items)
  `(table priorities ,n
          (union-equal ',items
                       (cdr (assoc-equal ,n
                                         (table-alist 'priorities
                                                      world))))))

(defmacro del-priority (n &rest items)
  `(table priorities ,n
          (set-difference-equal
           (cdr (assoc-equal ,n
                             (table-alist 'priorities
                                          world)))
           ',items)))

(defmacro clr-priority (n)
  `(table priorities ,n nil))

(defmacro clr-priorities ()
  `(table priorities nil nil :clear))

; The user is responsible for insuring that a prioritized rule be
; disabled.  That way, it doesn't become available until it is enabled
; locally by the computed hint.  It is convenient to provide a
; mechanism to disable all the rules mentioned in the priorities
; table.  We considered adding (in-theory (disable ,@items)) to
; add-priority above, so that prioritized runes were disabled when
; they're assigned priorities.  But then what does del-priority do?
; Does it enable the rune?  We don't like the idea of secretly enabling
; a rune.  So we have left the entire enabling/disabling business to
; the user but we have provided this convenient way to disable them
; all.

(defun all-prioritized-items (alist)
  (cond ((endp alist) nil)
        (t (union-equal (cdar alist)
                        (all-prioritized-items (cdr alist))))))

(defmacro disable-prioritized-runes nil
  '(in-theory
    (set-difference-current-theory-fn
     (all-prioritized-items
      (table-alist 'priorities world))
     nil
     world)))

; Here is how we will bump the current priority up to the next level.
; The function next-priority returns either the next priority or nil
; if there is none.

(defun next-priority1 (n candidate alist)

; Here, n is the current priority and we find the next priority in
; alist larger than n.  Candidate is nil if we haven't found one yet.

  (cond ((endp alist) candidate)
        ((< n (caar alist))
         (if candidate
             (if (< (caar alist) candidate)
                 (next-priority1 n (caar alist) (cdr alist))
               (next-priority1 n candidate (cdr alist)))
           (next-priority1 n (caar alist) (cdr alist))))
        (t (next-priority1 n candidate (cdr alist)))))

(defun next-priority (n world)
  (next-priority1 n nil (table-alist 'priorities world)))

; When the current-priority is n, and the current subgoal is stable
; under simplification, the computed hint will enable all the rules of
; priority at or below n.  Here is the way we collect all the
; appropriate rules.

(defun rules-up-to-priority1 (n alist)
  (cond ((endp alist) nil)
        ((<= (caar alist) n)
         (union-equal (cdar alist)
                      (rules-up-to-priority1 n (cdr alist))))
        (t (rules-up-to-priority1 n (cdr alist)))))

(defun rules-up-to-priority (n world)
  (rules-up-to-priority1 n (table-alist 'priorities world)))

; So here is the function that computes the hint.

(defun priority-phased-simplification
  (world stable-under-simplificationp current-priority)
  (if stable-under-simplificationp
      (let ((next (next-priority current-priority world)))
        (if next
            `(:computed-hint-replacement
              ((priority-phased-simplification world
                                               stable-under-simplificationp
                                               ,next))
              :in-theory (enable ,@(rules-up-to-priority next
                                                         world)))
          nil))
    nil))

(defconst *priority-phased-simplification*
  '(priority-phased-simplification world
                                   stable-under-simplificationp
                                   0))
; So here is a simple test, conducted locally.

(local
 (encapsulate
  nil

; The typical user would include this book.  Then, because the default
; hints are in the ACL2-DEFAULTS-TABLE, which is locally reset within
; a book, it is necessary to explicitly install priority phased
; simplification as a default hint.

  (set-default-hints (list *priority-phased-simplification*))

; Now the typical user adds a bunch of rules.  In this case, they are
; all defuns.  The function ccc is identically t, but is defined in a
; way so that ACL2 doesn't notice.  We write arithmetic terms like (+ x
; 3) knowing that simplification will commute them.  That way, we can
; see simplification do something during each priority level.

  (defun ccc (x)
    (equal (car (cons x x)) x))

  (defun bbb (x)
    (and (ccc (+ x 1))
         (ccc (+ x 2))
         (ccc (+ x 3))
         (ccc (+ x 4))
         (ccc (+ x 5))))

  (defun aaa (x)
    (and (bbb (+ x 1))
         (bbb (+ x 2))
         (bbb (+ x 3))
         (bbb (+ x 4))
         (bbb (+ x 5))))

; Now the typical user declares the priorities of his rules.  We want
; aaa opened first, then bbb, then ccc.  The user must disable the
; prioritized rules.

  (add-priority 1/5 aaa)
  (add-priority 2/5 bbb)
  (add-priority 3/5 ccc)
  (disable-prioritized-runes)

; Once this setup has been done, the theorem prover uses priority
; phased simplification.

  (defthm simple-priority-example
    (aaa (+ x 5)))

  ))
