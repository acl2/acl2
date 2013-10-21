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

(in-package "MILAWA")
(ACL2::set-current-package "MILAWA" ACL2::*the-live-state*)

;; This is the raw-lisp code for our rule profiler.
;;
;; Our goal is to pretend that the rewriter keeps a stack of the rules it is
;; backchaining through.  For each rule, we want to count:
;;
;;   - cost, the number of stack frames generated because of this rule,
;;   - tries, the number of times the rule was actually tried explicitly, and
;;   - successes, the number of times all the rule's hyps were relieved.
;;
;; Eventually all of this information gets put into the "stored costs" table
;; which maps rule names to cons-structures of the form:
;;
;;    (successes . (cost . tries))
;;
;; We really want profiling to be efficient, so the code is relatively ugly and
;; optimized.  But for a moment, let's consider the most naive implementation
;; of the profiler:
;;
;;   every time a rule is tried,
;;    - increment the "cost" for each "active rule",
;;    - increment the "tries" for this rule,
;;    - increment the "successes" for this rule, if successful
;;
;; But this wouldn't be very efficient because the number of "active rules"
;; will grow during backchaining, so incrementing them all might require quite
;; a bit of work.
;;
;; To make this efficient, we introduce the following strategy.  There are two
;; data structures involved:
;;
;;    - The "stored costs" table, as before, and
;;    - The "active rules" stack, which has the form:
;;         ( (cost1 . rune1) (cost2 . rune2) ... (costN . runeN) )
;;
;; Here, costI is the number of frames which runeN will be blamed for.  We
;; update this structure as follows:
;;
;;   (1) every time a rule is tried, we simply augment the list as:
;;       (1 . newrune) (cost1 . rune1) ... (costN . runeN)
;;
;;   (2) every time a cost1/rule1 are popped, we:
;;        - add cost1 to cost2, so that rune2 will eventually inherit
;           all the blame attributed to rune1
;;        - add cost1 to rune1's cost in the stored costs table, so
;;          that all the frames we want to give to rune1 are recorded
;;        - add 1 to rune1's tried count in the stored costs table,
;;          so that this additional try of rune1 is recorded
;;
;; This approach is dirtier but saves us from having to walk down the list and
;; increment all the costs, and still keeps us from hammering the table all the
;; time.

(ACL2::declaim (ACL2::type ACL2::fixnum *profile.cache-tries*))
(ACL2::declaim (ACL2::type ACL2::fixnum *profile.cache-hits*))
(ACL2::declaim (ACL2::type ACL2::hash-table *profile.stored-costs*))
(ACL2::declaim (ACL2::inline profile.update-stored-costs))
(ACL2::declaim (ACL2::inline profile.push-rune))
(ACL2::declaim (ACL2::inline profile.pop-rune))

;; This size is almost surely excessive, but it's only going to be allocated
;; once and I'd prefer if it never needed to be re-consed.
(ACL2::defparameter *profile.stored-costs* (ACL2::make-hash-table :size 8192 :test #'ACL2::eq))
(ACL2::defparameter *profile.active-rules* nil)
(ACL2::defparameter *profile.cache-tries* 0)
(ACL2::defparameter *profile.cache-hits* 0)

(ACL2::defmacro the-fixnum (n) `(ACL2::the ACL2::fixnum ,n))
(ACL2::defmacro when (&rest args) `(ACL2::when ,@args))
(ACL2::defmacro progn (&rest args) `(ACL2::progn ,@args))
(ACL2::defmacro incf (&rest args) `(ACL2::incf ,@args))
(ACL2::defmacro setf (&rest args) `(ACL2::setf ,@args))
(ACL2::defmacro gethash (&rest args) `(ACL2::gethash ,@args))

(ACL2::defun profile.update-stored-costs (rune cost successp)
             (declare (ACL2::type ACL2::fixnum cost))
             (let ((entry (gethash rune *profile.stored-costs*)))
               (if entry
                   ;; Entry has the form (successes . (cost . tries)); we are going to
                   ;; destructively update each component.
                   (progn
                    (when successp (incf (the-fixnum (ACL2::car entry))))
                    (incf (the-fixnum (ACL2::cadr entry))
                          (the-fixnum cost))
                    (incf (the-fixnum (ACL2::cddr entry)))
                    nil)
                 ;; Otherwise we need to create the initial entry for this rune.  I was
                 ;; quite surprised that (setf entry (cons ...)) didn't seem to work here.
                 ;; Instead I had to repeat the gethash.  I'm not sure why this would be.
                 (progn
                   (setf (gethash rune *profile.stored-costs*)
                         (cons (if successp 1 0)
                               (cons cost 1)))
                   nil))))

(ACL2::defun profile.push-rune (rune)
             (ACL2::push (cons 1 rune) *profile.active-rules*))

(ACL2::defun profile.pop-rune (successp)
             (when (consp *profile.active-rules*)
               ;; This guard is needed in order to properly handle interrupts.
               ;; If you interrupt in the middle of rewriting, generate a
               ;; report, and then hit :go to continue, the rewriter will be
               ;; exiting and trying to pop rules that you've already popped
               ;; when generating the report.  We just silently ignore these
               ;; frames now.  It's not quite accurate, but who really cares.
               ;; Profiling is just to give you an idea of big trends, not
               ;; little things.
               (let* ((pair   (ACL2::pop *profile.active-rules*))
                      (cost   (the-fixnum (ACL2::car pair)))
                      (rune   (ACL2::cdr pair)))
                 ;; Normally there will be subsequent pairs, which will need to be updated.
                 (ACL2::when (consp *profile.active-rules*)
                             (ACL2::incf (the-fixnum (ACL2::caar *profile.active-rules*))
                                         (the-fixnum cost)))
                 ;; And of course we need to update the stored costs.
                 (profile.update-stored-costs rune cost successp))))

(ACL2::defun profile.pop-all ()
             (if (consp *profile.active-rules*)
                 (progn (profile.pop-rune nil)
                        (profile.pop-all))
               nil))




;; We also will profile execution of functions.

(ACL2::defparameter *profile.executed-fns* (ACL2::make-hash-table :size 8192 :test #'ACL2::eq))


(ACL2::defun %profile.clear ()
             (setf *profile.active-rules* nil)
             (setf *profile.cache-tries* 0)
             (setf *profile.cache-hits* 0)
             (ACL2::clrhash *profile.stored-costs*)
             (ACL2::clrhash *profile.executed-fns*)
             nil)


(acl2::defun left-pad (x desired-width)
             (let ((actual-width (ACL2::length x)))
               (STR::cat (STR::implode (repeat #\Space (- desired-width actual-width))) x)))

(acl2::defun pretty-fraction (x places)
  (let* ((pretty-intpart (STR::pretty-number (ACL2::floor x 1)))
         (floatpart      (ACL2::mod (ACL2::floor (ACL2::* (ACL2::expt 10 places) (ACL2::abs x)) 1)
                                    (ACL2::expt 10 places))))
    (STR::cat pretty-intpart
              "."
              (STR::implode (ACL2::explode-atom floatpart 10)))))

(ACL2::defun profile.report-line (alist-entry)
             (let* ((rune        (ACL2::car alist-entry))
                    (successes   (ACL2::cadr alist-entry))
                    (cost        (ACL2::caddr alist-entry))
                    (tries       (ACL2::cdddr alist-entry))
                    (rule        (tactic.find-rule rune (ACL2::w ACL2::*the-live-state*)))
                    (splits      (not (clause.simple-termp (rw.rule->rhs rule))))
                    (true-ratio  (ACL2::/ cost tries))
                    (succ-color  (if (zp successes) *red* *black*))
                    (ratio-color (cond ((ACL2::< true-ratio 20) *green*)
                                       ((ACL2::< true-ratio 100) *blue*)
                                       (t *red*)))
                    (line        (STR::cat succ-color (left-pad (STR::pretty-number successes) 10) *black*
                                           "  " (left-pad (STR::pretty-number tries) 10)
                                           "  " (left-pad (STR::pretty-number cost) 12)
                                           "  " ratio-color (left-pad (pretty-fraction true-ratio 2) 12) *black*
                                           "   " (if splits "*" " ") (ACL2::symbol-name rune))))
               (ACL2::cw! "~s0~%" line)))

(ACL2::defun profile.names-of-unsuccessful-rules (alist)
             (if (consp alist)
                 (let ((alist-entry (ACL2::car alist)))
                   (let ((rune      (ACL2::car alist-entry))
                         (successes (ACL2::cadr alist-entry))
                         (cost      (ACL2::caddr alist-entry)))
                     (if (and (zp successes)
                              (< 99 cost))
                         (cons rune (profile.names-of-unsuccessful-rules (cdr alist)))
                       (profile.names-of-unsuccessful-rules (cdr alist)))))
               nil))

(ACL2::defun profile.report-lines (alist)
             (if (consp alist)
                 (progn (profile.report-line (car alist))
                        (profile.report-lines (cdr alist)))
               nil))

(ACL2::defun profile.exec-report-line (alist-entry)
             (let* ((name      (ACL2::car alist-entry))
                    (tries     (ACL2::cadr alist-entry))
                    (successes (ACL2::cddr alist-entry))
                    (line      (STR::cat
                                (left-pad (STR::pretty-number tries) 10)
                                "   " (left-pad (STR::pretty-number successes) 10)
                                "     " (ACL2::symbol-name name))))
               (ACL2::cw! "~s0~%" line)))

(ACL2::defun profile.exec-report-lines (alist)
             (if (consp alist)
                 (progn (profile.exec-report-line (car alist))
                        (profile.exec-report-lines (cdr alist)))
               nil))

(ACL2::defun %profile.report ()

             ;; If we were interrupted, there may be entries on the active rule
             ;; stack.  We pop them all to put them into stored costs.
             (profile.pop-all)

             (let ((alist nil))
               (ACL2::loop for key being the hash-keys of *profile.stored-costs*
                           using (hash-value value)
                           do (ACL2::push (cons key value) alist))
               (let ((sorted-alist (ACL2::sort alist #'(lambda (x y) (ACL2::> (ACL2::caddr x) (ACL2::caddr y))))))

                 (ACL2::cw "~%The following statistics were gathered since the last (%profile) or ~
                            (%profile.clear) was issued.~%~%")

                 (ACL2::cw (STR::cat *blue* "Rewrite Rule Report~%~%" *black*))

                 (let* ((percent   (acl2::floor (acl2::* 100 *profile.cache-hits*)
                                                (if (acl2::= *profile.cache-tries* 0)
                                                    1
                                                  *profile.cache-tries*)))
                        (pct-color (cond ((< percent 15) *red*)
                                         ((< percent 30) *blue*)
                                         (t *green*))))
                   (ACL2::cw "~s0~%~%"
                             (STR::cat "Cache hit rate: " pct-color percent "%" *black* " ("
                                     (STR::pretty-number *profile.cache-hits*)
                                     " hits in "
                                     (STR::pretty-number *profile.cache-tries*)
                                     " tries)")))

                 (ACL2::cw "In the following table,~% ~
                             - \"Success\" counts how many times all the hyps were relieved.~%  ~
                             - \"Frames\" counts how many rules were tried due to this rule backchaining.~%  ~
                             - \"Tries\" counts how many times this rule itself was tried.~%  ~
                             - \"Ratio\" is the average number of frames per try.~%  ~
                             - A star indicates this rule can cause case splits.~%~%   ~
                             Success       Tries        Frames         Ratio    Rule~%~%")

                 (profile.report-lines sorted-alist)

                 ;; Execution report.
                 (let ((exec-alist nil))
                   (ACL2::loop for key being the hash-keys of *profile.executed-fns*
                               using (hash-value value)
                               do (ACL2::push (cons key value) exec-alist))
                   (let ((sorted-exec-alist
                          (ACL2::sort exec-alist #'(lambda (x y)
                                                     (ACL2::> (ACL2::cadr x) (ACL2::cadr y))))))
                     (ACL2::cw (STR::cat *blue* "~%Execution report.~%~%" *black*))
                     (ACL2::cw "     Tries    Successes     Function~%")
                     (profile.exec-report-lines sorted-exec-alist)))


                 (let ((useless-rules (profile.names-of-unsuccessful-rules sorted-alist)))
                   (if useless-rules
                       (progn
                         (ACL2::cw (STR::cat *blue* "~%~%Useless, Expensive Rules~%~%" *black*))
                         (ACL2::cw "The following rules were never successful and each took over 100 frames.  ~
                                    To speed up your rewriting, you may wish to consider disabling them:~%~%~
                                    ~x0.~%~%" useless-rules))
                     (ACL2::cw "~%~%")))

                 )))

(ACL2::defun %profile ()
              (ACL2::progn
               (ACL2::redef-notinline rw.flag-crewrite)
               (ACL2::redef-notinline rw.fast-flag-crewrite) ;; wtf is this?

               (%profile.clear)

               (CCL:advise rw.try-ground-simplify
                           (let ((x      (ACL2::second CCL::arglist))
                                 (answer (ACL2::first CCL::values)))
                             (when (logic.functionp x)
                               (let* ((name  (logic.function-name x))
                                      ;; Entry ::= (tries . successes) or NIL if not yet entered.
                                      (entry (gethash name *profile.executed-fns*))
                                      (tries (if entry (car entry) 0))
                                      (succs (if entry (cdr entry) 0)))
                                 (setf (gethash name *profile.executed-fns*)
                                       (cons (+ 1 tries)
                                             (if answer (+ 1 succs) succs))))))
                           :when :after)
               (CCL:advise rw.fast-try-ground-simplify
                           (let ((x      (ACL2::second CCL::arglist))
                                 (answer (ACL2::first CCL::values)))
                             (when (logic.functionp x)
                               (let* ((name  (logic.function-name x))
                                      ;; Entry ::= (tries . successes) or NIL if not yet entered.
                                      (entry (gethash name *profile.executed-fns*))
                                      (tries (if entry (car entry) 0))
                                      (succs (if entry (cdr entry) 0)))
                                 (setf (gethash name *profile.executed-fns*)
                                       (cons (+ 1 tries)
                                             (if answer (+ 1 succs) succs))))))
                           :when :after)

               (CCL:advise rw.flag-crewrite
                           (let ((flag (ACL2::first CCL::arglist)))
                             (if (ACL2::eq flag 'match)
                                 (let ((rule[s] (ACL2::fourth CCL::arglist)))
                                   (profile.push-rune (rw.rule->name rule[s])))
                               nil))
                           :when :before)
               (CCL:advise rw.flag-crewrite
                           (let ((flag (ACL2::first CCL::arglist)))
                             (if (ACL2::eq flag 'match)
                                 ;; We have to "car" this twice, because CCL::values supports multiple-value
                                 ;; returns.  The first car gets us to our 3-tuple, and the second car gets
                                 ;; us our trace/nil entry.
                                 (let ((trace/nil (ACL2::car (ACL2::first CCL::values))))
                                   (profile.pop-rune trace/nil))
                               nil))
                           :when :after)

               (CCL:advise rw.fast-flag-crewrite
                           (let ((flag (ACL2::first CCL::arglist)))
                             (if (ACL2::eq flag 'match)
                                 (let ((rule[s] (ACL2::fourth CCL::arglist)))
                                   (profile.push-rune (rw.rule->name rule[s])))
                               nil))
                           :when :before)
               (CCL:advise rw.fast-flag-crewrite
                           (let ((flag (ACL2::first CCL::arglist)))
                             (if (ACL2::eq flag 'match)
                                 ;; We have to "car" this twice, because CCL::values supports multiple-value
                                 ;; returns.  The first car gets us to our 3-tuple, and the second car gets
                                 ;; us our trace/nil entry.
                                 (let ((trace/nil (ACL2::car (ACL2::first CCL::values))))
                                   (profile.pop-rune trace/nil))
                               nil))
                           :when :after)

               (CCL:advise rw.cache-lookup
                           (let ((answer (ACL2::first CCL::values)))
                             (ACL2::incf *profile.cache-tries*)
                             (ACL2::when answer (ACL2::incf *profile.cache-hits*)))
                           :when :after)
               (CCL:advise rw.fast-cache-lookup
                           (let ((answer (ACL2::first CCL::values)))
                             (ACL2::incf *profile.cache-tries*)
                             (ACL2::when answer (ACL2::incf *profile.cache-hits*)))
                           :when :after)
               nil))

(ACL2::defun %profile.stop ()
              (ACL2::progn
               (CCL:unadvise rw.try-ground-simplify)
               (CCL:unadvise rw.fast-try-ground-simplify)
               (CCL:unadvise rw.flag-crewrite)
               (CCL:unadvise rw.fast-flag-crewrite)
               (CCL:unadvise rw.cache-lookup)
               (CCL:unadvise rw.fast-cache-lookup)
               (ACL2::redef-original rw.flag-crewrite) ;; wtf is this?
               (ACL2::redef-original rw.fast-flag-crewrite) ;; wtf is this?
               nil))


#|
(profile.push-rune 'a)
(profile.push-rune 'b)
(profile.push-rune 'c)
(profile.push-rune 'd)
(profile.pop-rune)
(profile.pop-rune)
(profile.push-rune 'e)
(profile.push-rune 'f)
(profile.pop-rune)
(profile.pop-rune)
(profile.pop-rune)
(profile.pop-rune)
(%profile.report)
|#
