;; Copyright (C) 2015, University of British Columbia
;; Written by Yan Peng (August 2nd 2016)
;;
;; License: A 3-clause BSD license.
;; See the LICENSE file distributed with ACL2
;;

;;
;; This book defines a computed hint that looks for the function
;; "SMT-please"

(in-package "SMT")
(include-book "std/util/bstar" :dir :system)
(include-book "xdoc/top" :dir :system)
(include-book "std/util/define" :dir :system)

(include-book "hint-interface")

(defsection SMT-computed-hints
  :parents (verified)
  :short "This document discusses how computed-hints are used in the
  architecture of Smtlink."
  :long "<p>Smtlink uses @(tsee ACL2::computed-hints) and @(tsee
  ACL2::clause-processor) for controlling the several translation steps. To use
  Smtlink, the user first installs the computed hint,
  @('SMT::SMT-computed-hint'). When the user uses :smtlink in @(tsee ACL2::hints),
  it macro-expands into a :clause-processor hint. This applies the first
  clause-processor for parsing @(tsee SMT::smt-hint). This clause-processor
  also add @('(SMT::hint-please some-hint)') into the clause as the first in
  the disjunction. The SMT::SMT-computed-hint will recognize clauses that
  matches the form @('(('hint-please ) . term)'). It extracts the
  @('some-hint') from the clause, and install below
  @(':computed-hint-replacement'):</p>

@({
`(:computed-hint-replacement ((SMT-delayed-hint clause ',some-hint))
  :clause-processor (remove-hint-please clause))
})

<p>This @(':computed-hint-replacement') does two things: clearing up
the @('SMT::hint-please') disjunct from the clause with the hint
@(':clause-processor (remove-hint-please clause)'), and install another
computed-hint called @('SMT::SMT-delayed-hint') for actually applying
@('some-hint') to the cleaned-up new subgoal.</p>

<p>We started out using just one computed-hint that recognizes
@('SMT::hint-please') and applies the hint. This results in a rewrite-loop that
resembles the one described at @(tsee ACL2::using-computed-hints-6). The
problem is that, when a user supplies a @(':use') hint, the computed-hint would
generate a new subgoal that still contains the @('SMT::hint-please'). The
@('SMT::hint-please') then triggers the computed-hint again, applying the
@(':use') hint, which generates a new subgoal that still contains the
@('SMT::hint-please'). This then triggers the computed-hint again ... you get
the idea. To solve this problem, we add this one additional step of
clause-processor to remove the @('SMT::hint-please') disjunct from the clause.
Then install another computed-hint called @('SMT::SMT-delayed-hint') for
running the real hints on the subgoal. Because this new subgoal doesn't contain
@('SMT::hint-please'), the @('SMT::SMT-computed-hint') won't get in the way.
It works fine even when the @('some-hint') is again a @(':smtlink') hint,
allowing the user to use Smtlink inside of a Smtlink proof.</p>
"

  ;; verified version of split-kwd-alist
  (define my-split-kwd-alist ((key symbolp)
                              (kwd-alist true-listp))
    :returns (mv (pre true-listp)
                 (post true-listp))
    :measure (len kwd-alist)
    :hints (("Goal" :in-theory (disable true-list-fix-preserve-length)
             :use ((:instance true-list-fix-preserve-length
                              (x kwd-alist)))))
    (b* ((kwd-alist (true-list-fix kwd-alist))
         ((unless (consp kwd-alist)) (mv nil nil))
         ((if (eq key (car kwd-alist)))
          (mv nil kwd-alist))
         ((unless (consp (cdr kwd-alist)))
          (prog2$ (er hard? 'computed-hints=>my-split-kwd-alist "Something ~
  is wrong with the kwd-alist: ~q0" kwd-alist)
                  (mv nil nil)))
         ((mv pre post)
          (my-split-kwd-alist key (cddr kwd-alist))))
      (mv (cons (car kwd-alist)
                (cons (cadr kwd-alist)
                      pre))
          post)))

  (define treat-in-theory-hint ((enabled true-listp)
                                (kwd-alist true-listp))
    :returns (new-kwd-alist
              true-listp
              :hints (("Goal"
                       :in-theory (disable
                                   true-listp-of-my-split-kwd-alist.post)
                       :use ((:instance
                              true-listp-of-my-split-kwd-alist.post
                              (key :in-theory)
                              (kwd-alist (true-list-fix kwd-alist)))))))
    :guard-debug t
    (b* ((kwd-alist (true-list-fix kwd-alist))
         ((mv pre post)
          (my-split-kwd-alist :in-theory kwd-alist)))
      (cond ((and (consp post)
                  (consp (cdr post))
                  (consp (cadr post))
                  (equal (caadr post) 'enable))
             `(,@pre
               :in-theory (enable ,@enabled ,@(cdadr post))
               ,@(cddr post)))
            ((and (consp post)
                  (consp (cdr post))
                  (consp (cadr post))
                  (equal (caadr post) 'disable))
             `(,@pre
               :in-theory (e/d ,enabled (,@(cdadr post)))
               ,@(cddr post)))
            ((and (consp post)
                  (consp (cdr post))
                  (consp (cadr post))
                  (consp (cdadr post))
                  (consp (cddadr post))
                  (equal (caadr post) 'e/d))
             `(,@pre
               :in-theory (e/d (,@enabled ,@(car (cdadr post)))
                               (,@(cadr (cdadr post))))
               ,@(cddr post)))
            (t `(;; :do-not '(preprocess)
                 :in-theory (enable ,@enabled)
                            ,@kwd-alist
                            )))))

  (define treat-expand-hint ((expand-lst true-listp) (kwd-alist true-listp))
    :returns (new-kwd-alist
              true-listp
              :hints (("Goal"
                       :in-theory (disable
                                   true-listp-of-my-split-kwd-alist.post)
                       :use ((:instance
                              true-listp-of-my-split-kwd-alist.post
                              (key :expand)
                              (kwd-alist (true-list-fix kwd-alist)))))))
    (b* ((kwd-alist (true-list-fix kwd-alist))
         ((mv pre post)
          (my-split-kwd-alist :expand kwd-alist)))
      (cond ((and (consp post)
                  (consp (cdr post)))
             `(,@pre
               :expand (,@expand-lst
                        ,@(cadr post))
               ,@post))
            (t ; simply extend kwd-alist
             `(:expand ,@expand-lst
                       ,@kwd-alist)))))

  (program)
  (define extract-hint-wrapper (cl)
    (cond ((endp cl) (mv nil nil))
          (t (b* ((lit cl))
               (case-match lit
                 ((('hint-please ('quote kwd-alist)) . term)
                  (mv term kwd-alist))
                 (& (extract-hint-wrapper (cdr cl))))))))

  (define SMT-computed-hint (cl)
    :parents (SMT-computed-hints)
    :short "@('SMT::SMT-computed-hint') extract the actual hints from the
    @('SMT::hint-please') disjunct, apply the @('SMT::remove-hint-please')
    clause-processor, and install the @(tsee SMT::SMT-delayed-hint) for
    applying the actual hints."
    (b* (((mv & kwd-alist) (extract-hint-wrapper cl))
         (- (cw "cl: ~q0" cl))
         (- (cw "kwd-alist: ~q0" kwd-alist)))
      `(:computed-hint-replacement ((SMT-delayed-hint clause ',kwd-alist))
        :clause-processor (remove-hint-please clause))))

  (define SMT-delayed-hint (cl kwd-alist)
    :parents (SMT-computed-hints)
    :short "@('SMT::SMT-delayed-hints') applies the hints @('kwd-alist') and
    install the @(tsee SMT::SMT-computed-hint) back."
    (declare (ignore cl))
    `(:computed-hint-replacement ((SMT-computed-hint clause))
      ,@kwd-alist))

  (logic)

  )
;; Add this line to your code to add a default hint of Smtlink
;; (add-default-hints '((SMT-computed-hint clause)))
;; Remove hint:
;; (remove-default-hints '((SMT-computed-hint clause)))
