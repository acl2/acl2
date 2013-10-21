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

;; Profiling code.
;;
;; This is supposed to be like ACL2's "accumulated-persistence" facility.  As
;; with accumulated-persistence, profiling will considerably slow down the
;; rewriter, so you'll only want to enable it to figure out which rules are
;; expensive, then disable it to do your actual rewriting.  Here is the public
;; interface for using the profiler.

(ACL2::defun %profile ()
  ;; Begin collecting profiling data.
  (declare (xargs :guard t))
  (ACL2::cw "%profile needs to be redefined!~%"))

(ACL2::defun %profile.clear ()
  ;; Erase all the current profiling data
  (declare (xargs :guard t))
  (ACL2::cw "%profile.clear needs to be redefined!~%"))

(ACL2::defun %profile.report ()
  ;; View the current profiling report, and erase current data
  (declare (xargs :guard t))
  (ACL2::cw "%profile.report needs to be redefined!~%"))

(ACL2::defun %profile.stop ()
  ;; Completely turn off the profiler.
  (declare (xargs :guard t))
  (ACL2::cw "%profile.stop needs to be redefined!~%"))



;; There are also some system-level commands.  You should never call these
;; directly.  But, I still need to introduce them as ACL2 functions and then
;; redefine them, so that we can call them from the new trace$ code introduced
;; in ACL2 3.4.

(ACL2::defun %profile-enter-rw.flag-crewrite (flag rule[s])
  ;; Called when we enter rw.flag-crewrite
  ;; We may need to update the rule usage statistics tables
  (declare (xargs :guard t)
           (ignore flag rule[s]))
  (ACL2::cw "%profile-enter-rw.flag-crewrite needs to be redefined!~%"))

(ACL2::defun %profile-exit-rw.flag-crewrite (flag)
  ;; Called when we exit rw.flag-crewrite
  ;; We may need to update the rule usage statistics tables
  (declare (xargs :guard t)
           (ignore flag))
  (ACL2::cw "%profile-exit-rw.flag-crewrite needs to be redefined!~%"))

(ACL2::defun %profile-exit-rw.cache-lookup (answer)
  ;; Called when we exit rw.cache-lookup
  ;; We just update the cache hit-rate statistics
  (declare (xargs :guard t)
           (ignore answer))
  (ACL2::cw "%profile-exit-rw.cache-lookup needs to be redefined!~%"))





(ACL2::defttag profile)

;; ---- this is the new profiling code.  uncomment this when Matt implements
;;      a print-free tracing mechanism


;; (ACL2::progn!
;;  (ACL2::set-raw-mode t)

;;  ;; This is the raw-lisp code for our rule profiler.  We have tried to make
;;  ;; profiling somewhat efficient, so the code is somewhat complex.
;;  ;;
;;  ;; We pretend that the rewriter keeps a stack of the rules it is backchaining
;;  ;; through.  For each rule, we want to count (1) the number of stack frames
;;  ;; generated because of this rule, and (2) the number of times the rule was
;;  ;; actually tried explicitly.
;;  ;;
;;  ;; Eventually all of this information gets put into the "stored costs" alist,
;;  ;; which is just a table of entries of the form <rune, cost, tries>.  The most
;;  ;; naive implementation of the profiler would just be:
;;  ;;
;;  ;;   (1) every time a rule is tried, increment all of the costs of every
;;  ;;       active rule, and increment the tries of the rule being tried.
;;  ;;
;;  ;; This wouldn't be very efficient.  An enhancement would be to associate
;;  ;; costs with each active rule.  Under this idea:
;;  ;;
;;  ;;   (1) every time a rule is tried, increment all of the costs on the
;;  ;;       active rule stack.
;;  ;;
;;  ;;   (2) when a rule is popped, add its cost into the stored costs alist.
;;  ;;
;;  ;; This saves a lot of alist accessing, but it still requires us to increment
;;  ;; many variables.  Our final twist is to change the active rule list into a
;;  ;; funny stack that looks like this:
;;  ;;
;;  ;;   (cost1 rune1 cost2 rune2 ... costN runeN)
;;  ;;
;;  ;; Here, costI is the number of frames which runeN will be blamed for.  We
;;  ;; update this structure as follows:
;;  ;;
;;  ;;   (1) every time a rule is tried, we simply augment the list as:
;;  ;;       (1 newrune cost1 rune1 ... costN runeN)
;;  ;;
;;  ;;   (2) every time a cost1/rule1 are popped, we:
;;  ;;        - add cost1 to cost2, so that rune2 inherits all the blame
;;  ;;          attributed to rune1
;;  ;;        - add cost1 to rune1's cost in the stored costs alist
;;  ;;        - add 1 to rune1's tried count in the stored costs alist
;;  ;;
;;  ;; This approach is dirtier but saves us from having to walk down the list and
;;  ;; increment all the costs, and still keeps us from hammering the alist all the
;;  ;; time.


;;  (ACL2::defparameter *profile.active-rules* nil)
;;  (ACL2::defparameter *profile.stored-costs* nil)
;;  (ACL2::defparameter *profile.cache-tries* 0)
;;  (ACL2::defparameter *profile.cache-hits* 0)



;;  (ACL2::defun %profile.clear ()
;;               (ACL2::setf *profile.active-rules* nil)
;;               (ACL2::setf *profile.stored-costs* nil)
;;               (ACL2::setf *profile.cache-tries* 0)
;;               (ACL2::setf *profile.cache-hits* 0)
;;               nil)



;;  (ACL2::defun profile.update-stored-costs (rune cost)
;;               ;; Arframe is the frame we just popped from the active rule stack.
;;               (let* ((entry              (ACL2::hons-assoc-equal rune *profile.stored-costs*))
;;                      (old-cost-and-tries (cdr entry))
;;                      (old-cost           (first old-cost-and-tries))
;;                      (old-tries          (second old-cost-and-tries))
;;                      (new-cost           (+ cost old-cost))
;;                      (new-tries          (+ old-tries 1)))
;;                 (ACL2::setf *profile.stored-costs*
;;                             (ACL2::hons-acons rune (list new-cost new-tries) *profile.stored-costs*))))

;;  (ACL2::defun profile.push-rune (rune)
;;               (ACL2::setf *profile.active-rules*
;;                           (cons 1 (cons rune *profile.active-rules*))))

;;  (ACL2::defun profile.pop-rune ()
;;               (let ((cost (ACL2::pop *profile.active-rules*))
;;                     (rune (ACL2::pop *profile.active-rules*)))
;;                 (ACL2::progn
;;                  ;; Update cost2 if it exists
;;                  (if (consp *profile.active-rules*)
;;                      (let ((cost2 (ACL2::pop *profile.active-rules*)))
;;                        (ACL2::push (ACL2::+ cost cost2) *profile.active-rules*))
;;                    nil)
;;                  ;; Update the stored costs
;;                  (profile.update-stored-costs rune cost))))

;;  (ACL2::defun profile.pop-all ()
;;               (if (consp *profile.active-rules*)
;;                   (ACL2::prog2$ (profile.pop-rune)
;;                                 (profile.pop-all))
;;                 nil))

;;  (ACL2::defun remove-shadowed-pairs (x acc)
;;               (if (consp x)
;;                   (remove-shadowed-pairs (cdr x)
;;                                          (if (ACL2::assoc (car (car x)) acc)
;;                                              acc
;;                                            (cons (car x) acc)))
;;                 acc))

;;  (ACL2::defun profile.report-line (entry)
;;               (let ((rune  (car entry))
;;                     (cost  (second entry))
;;                     (tries (third entry)))
;;                 (ACL2::cw! "  ~c0  ~c1   (~c2.~f3~f4)   ~x5~%"
;;                            (cons cost 10)
;;                            (cons tries 10)
;;                            (cons (ACL2::floor cost tries) 7)
;;                            (mod  (floor (* 10 cost) tries) 10)
;;                            (mod  (floor (* 100 cost) tries) 10)
;;                            rune)))

;;  (ACL2::defun profile.report-lines (alist)
;;               (if (consp alist)
;;                   (ACL2::prog2$ (profile.report-line (car alist))
;;                                 (profile.report-lines (cdr alist)))
;;                 nil))

;;  (ACL2::defun %profile.report ()
;;               (ACL2::cw "~% ~
;;               - Frames is how many rules were tried due to this rule backchaining.~% ~
;;               - Tries is the actual number of times this rule was tried.~% ~
;;               - Ratio is the average frames per try.~%~%      ~
;;                   Frames       Tries          Ratio   Rule~%~%")
;;               ;; If we were interrupted, there may be entries on the active rule
;;               ;; stack.  We pop them all to put them into stored costs.
;;               (profile.pop-all)
;;               ;; We now remove all the shadowed pairs and sort the list so that
;;               ;; the rules are presented in a sensible order, and print the report.
;;               (profile.report-lines (ACL2::sort (remove-shadowed-pairs *profile.stored-costs* nil)
;;                                                 #'(lambda (x y) (ACL2::> (second x) (second y)))))
;;               (ACL2::cw "~%")
;;               (ACL2::cw "Note: the unconditional rules mentioned above are probably underreported, ~
;;              because they are tracked only in \"crewrite\" and not in \"urewrite.\"~%~
;;              Crewrite cache statistics: ~x0 hits in ~x1 tries (~x2%).~%~%"
;;                         *profile.cache-hits*
;;                         *profile.cache-tries*
;;                         (floor (* 100 *profile.cache-hits*) *profile.cache-tries*))
;;               ;; We have mangled the halist breaking the hons-acons discipline.  We
;;               ;; clear out the stack in case someone wants to profile further.
;;               (%profile.clear)
;;               nil)

;;  (ACL2::defun %profile-enter-rw.flag-crewrite (flag rule[s])
;;               (if (equal flag 'match)
;;                   (profile.push-rune (rw.rule->name rule[s]))
;;                 nil))

;;  (ACL2::defun %profile-exit-rw.flag-crewrite (flag)
;;               (if (equal flag 'match)
;;                   (profile.pop-rune)
;;                 nil))

;;  (ACL2::defun %profile-exit-rw.cache-lookup (answer)
;;               (ACL2::incf *profile.cache-tries*)
;;               (ACL2::when answer
;;                           (ACL2::incf *profile.cache-hits*)))

;;  (ACL2::defun %profile ()
;;               (ACL2::redef-notinline rw.flag-crewrite)
;;               (%profile.clear)
;;               #-openmcl
;;               (ACL2::eval '(ACL2::trace$ (rw.flag-crewrite
;;                                           :entry (%profile-enter-rw.flag-crewrite flag rule[s])
;;                                           :exit (%profile-exit-rw.flag-crewrite flag))))
;;               #-openmcl
;;               (ACL2::eval '(ACL2::trace$ (rw.cache-lookup :exit (%profile-exit-rw.cache-lookup ACL2::value))))
;;               #+opemcl
;;               (CCL:advise rw.flag-crewrite
;;                           (%profile-enter-rw.flag-crewrite (ACL2::car CCL::arglist)
;;                                                            (ACL2::fourth CCL::arglist))
;;                           :when :before)
;;               #+openmcl
;;               (CCL:advise rw.flag-crewrite
;;                           (%profile-exit-rw.flag-crewrite (ACL2::car CCL::arglist))
;;                           :when :after)
;;               #+openmcl
;;               (CCL:advise rw.cache-lookup
;;                           (%profile-exit-rw.cache-lookup (ACL2::car CCL::values))
;;                           :when :after)
;;               nil)

;;  (ACL2::defun %profile.stop ()
;;               (ACL2::redef-original rw.flag-crewrite)
;;               (ACL2::untrace$ rw.flag-crewrite)
;;               (ACL2::untrace$ rw.cache-lookup)
;;               nil))


;; stupid crap thing won't let me use ccl::advise in raw mode??!


(ACL2::progn!
 (ACL2::set-raw-mode t)
 (let* ((tacdir  (ACL2::extend-pathname ACL2::*path-to-milawa-acl2-directory* "interface"       ACL2::*the-live-state*))
        (rawfile (ACL2::extend-pathname tacdir                                "profile-raw.lsp" ACL2::*the-live-state*)))
   (ACL2::load rawfile)))

;;  (ACL2::defparameter *profile.active-rules* nil)
;;  (ACL2::defparameter *profile.stored-costs* nil)
;;  (ACL2::defparameter *profile.cache-tries* 0)
;;  (ACL2::defparameter *profile.cache-hits* 0)

;;  (ACL2::defun profile.update-stored-costs (rune cost)
;;               ;; Arframe is the frame we just popped from the active rule stack.
;;               (let* ((entry              (ACL2::hons-assoc-equal rune *profile.stored-costs*))
;;                      (old-cost-and-tries (cdr entry))
;;                      (old-cost           (first old-cost-and-tries))
;;                      (old-tries          (second old-cost-and-tries))
;;                      (new-cost           (+ cost old-cost))
;;                      (new-tries          (+ old-tries 1)))
;;                 (ACL2::setf *profile.stored-costs*
;;                             (ACL2::hons-acons rune (list new-cost new-tries) *profile.stored-costs*))))

;;  ;; (ACL2::defun profile.increment-arstack-aux (arstack acc)
;;  ;;              ;; Arstack is the active rules stack.  We want to increment every cost.
;;  ;;              (if (consp arstack)
;;  ;;                  (profile.increment-arstack-aux (cdr arstack)
;;  ;;                                                 (let* ((entry (car arstack))
;;  ;;                                                        (rune  (car entry))
;;  ;;                                                        (cost  (cdr entry)))
;;  ;;                                                   (cons (cons rune (ACL2::+ 1 cost))
;;  ;;                                                         acc)))
;;  ;;                (ACL2::reverse acc)))

;;  ;; (ACL2::defun profile.increment-arstack ()
;;  ;;              (ACL2::setf *profile.active-rules*
;;  ;;                          (profile.increment-arstack-aux *profile.active-rules* nil)))

;;  (ACL2::defun profile.push-rune (rune)
;;               (ACL2::setf *profile.active-rules*
;;                           (cons 1 (cons rune *profile.active-rules*))))

;;  (ACL2::defun profile.pop-rune ()
;;               (let ((cost (ACL2::pop *profile.active-rules*))
;;                     (rune (ACL2::pop *profile.active-rules*)))
;;                 (ACL2::progn
;;                  ;; Update cost2 if it exists
;;                  (if (consp *profile.active-rules*)
;;                      (let ((cost2 (ACL2::pop *profile.active-rules*)))
;;                        (ACL2::push (ACL2::+ cost cost2) *profile.active-rules*))
;;                    nil)
;;                  ;; Update the stored costs
;;                  (profile.update-stored-costs rune cost))))

;;  (ACL2::defun profile.pop-all ()
;;               (if (consp *profile.active-rules*)
;;                   (ACL2::prog2$ (profile.pop-rune)
;;                                 (profile.pop-all))
;;                 nil))

;;  (ACL2::defun remove-shadowed-pairs (x acc)
;;               (if (consp x)
;;                   (remove-shadowed-pairs (cdr x)
;;                                          (if (ACL2::assoc (car (car x)) acc)
;;                                              acc
;;                                            (cons (car x) acc)))
;;                 acc))

;;  (ACL2::defun profile.report-line (entry)
;;               (let ((rune  (car entry))
;;                     (cost  (second entry))
;;                     (tries (third entry)))
;;                 (ACL2::cw! "  ~c0  ~c1   (~c2.~f3~f4)   ~x5~%"
;;                            (cons cost 10)
;;                            (cons tries 10)
;;                            (cons (ACL2::floor cost tries) 7)
;;                            (mod  (floor (* 10 cost) tries) 10)
;;                            (mod  (floor (* 100 cost) tries) 10)
;;                            rune)))

;;  (ACL2::defun profile.report-lines (alist)
;;               (if (consp alist)
;;                   (ACL2::prog2$ (profile.report-line (car alist))
;;                                 (profile.report-lines (cdr alist)))
;;                 nil))

;;  (ACL2::defun %profile.clear ()
;;               (ACL2::progn
;;                (ACL2::setf *profile.active-rules* nil)
;;                (ACL2::setf *profile.stored-costs* nil)
;;                (ACL2::setf *profile.cache-tries* 0)
;;                (ACL2::setf *profile.cache-hits* 0)
;;                nil))

;;  (ACL2::defun %profile.report ()
;;               (ACL2::progn
;;                (ACL2::cw "~% ~
;;                           - Frames is how many rules were tried due to this rule backchaining.~% ~
;;                           - Tries is the actual number of times this rule was tried.~% ~
;;                           - Ratio is the average frames per try.~%~%      ~
;;                          Frames       Tries          Ratio   Rule~%~%")
;;                ;; If we were interrupted, there may be entries on the active rule
;;                ;; stack.  We pop them all to put them into stored costs.
;;                (profile.pop-all)
;;                ;; We now remove all the shadowed pairs and sort the list so that
;;                ;; the rules are presented in a sensible order, and print the report.
;;                (profile.report-lines (ACL2::sort (remove-shadowed-pairs *profile.stored-costs* nil)
;;                                                  #'(lambda (x y) (ACL2::> (second x) (second y)))))
;;                (ACL2::cw "~%")
;;                (ACL2::cw "Note: the unconditional rules mentioned above are probably underreported, ~
;;                          because they are tracked only in \"crewrite\" and not in \"urewrite.\"~%~
;;                          Crewrite cache statistics: ~x0 hits in ~x1 tries (~x2%).~%~%"
;;                          *profile.cache-hits*
;;                          *profile.cache-tries*
;;                          (floor (* 100 *profile.cache-hits*) *profile.cache-tries*))
;;                ;; We have mangled the halist breaking the hons-acons discipline.  We
;;                ;; clear out the stack in case someone wants to profile further.
;;                (%profile.clear)
;;                nil))


;;  (ACL2::defun %profile ()
;;               (ACL2::progn
;;                (ACL2::redef-notinline rw.flag-crewrite)
;;                (%profile.clear)
;;                (CCL:advise rw.flag-crewrite
;;                            (let* ((arglist  CCL::arglist)
;;                                   (flag     (nth 0 arglist))
;;                                   (assms    (nth 1 arglist))
;;                                   (x        (nth 2 arglist))
;;                                   (rule[s]  (nth 3 arglist))
;;                                   (sigma[s] (nth 4 arglist))
;;                                   (cache    (nth 5 arglist))
;;                                   (iffp     (nth 6 arglist))
;;                                   (blimit   (nth 7 arglist))
;;                                   (rlimit   (nth 8 arglist))
;;                                   (anstack  (nth 9 arglist))
;;                                   (control  (nth 10 arglist)))
;;                              (declare (ACL2::ignorable flag assms x rule[s] sigma[s] cache iffp blimit rlimit anstack control))
;;                              (if (equal flag 'match)
;;                                  (profile.push-rune (rw.rule->name rule[s]))
;;                                nil))
;;                            :when :before)
;;                (CCL:advise rw.flag-crewrite
;;                            (let* ((arglist  CCL::arglist)
;;                                   (flag     (nth 0 arglist))
;;                                   (assms    (nth 1 arglist))
;;                                   (x        (nth 2 arglist))
;;                                   (rule[s]  (nth 3 arglist))
;;                                   (sigma[s] (nth 4 arglist))
;;                                   (cache    (nth 5 arglist))
;;                                   (iffp     (nth 6 arglist))
;;                                   (blimit   (nth 7 arglist))
;;                                   (rlimit   (nth 8 arglist))
;;                                   (anstack  (nth 9 arglist))
;;                                   (control  (nth 10 arglist)))
;;                              (declare (ACL2::ignorable flag assms x rule[s] sigma[s] cache iffp blimit rlimit anstack control))
;;                              (if (equal flag 'match)
;;                                  (profile.pop-rune)
;;                                nil))
;;                            :when :after)
;;                (CCL:advise rw.cache-lookup
;;                            (let* ((values  CCL::values)
;;                                   (answer  (first values)))
;;                              (ACL2::incf *profile.cache-tries*)
;;                              (ACL2::when answer
;;                                          (ACL2::incf *profile.cache-hits*)))
;;                            :when :after)
;;                nil))

;;  (ACL2::defun %profile.stop ()
;;               (ACL2::progn
;;                (CCL:unadvise rw.crewrite-entry)
;;                (CCL:unadvise rw.crewrite-note-fn)
;;                (CCL:unadvise rw.cache-lookup)
;;                (ACL2::redef-original rw.flag-crewrite)
;;                nil)))

