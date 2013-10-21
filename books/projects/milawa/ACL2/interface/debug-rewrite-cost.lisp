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
(set-verify-guards-eagerness 2)
(set-case-split-limitations nil)
(set-well-founded-relation ord<)
(set-measure-function rank)

(mutual-recursion
 (defun rw.count-forcing-traces (x)
   (declare (xargs :guard (rw.tracep x)
                   :measure (two-nats-measure (rank x) 1)))
   (let ((method (rw.trace->method x))
         (subtraces (rw.trace->subtraces x)))
     (if (equal method 'force)
         (+ 1 (rw.count-forcing-traces-list subtraces))
       (rw.count-forcing-traces-list subtraces))))
 (defun rw.count-forcing-traces-list (x)
   (declare (xargs :guard (rw.trace-listp x)
                   :measure (two-nats-measure (rank x) 0)))
   (if (consp x)
       (+ (rw.count-forcing-traces (car x))
          (rw.count-forcing-traces-list (cdr x)))
     0)))

(mutual-recursion
 (defun rw.count-traces (x)
   (declare (xargs :guard (rw.tracep x)
                   :measure (two-nats-measure (rank x) 1)))
   (let ((subtraces (rw.trace->subtraces x)))
     (+ 1 (rw.count-traces-list subtraces))))
 (defun rw.count-traces-list (x)
   (declare (xargs :guard (rw.trace-listp x)
                   :measure (two-nats-measure (rank x) 0)))
   (if (consp x)
       (+ (rw.count-traces (car x))
          (rw.count-traces-list (cdr x)))
     0)))

(ACL2::mutual-recursion
 (ACL2::defun rw.trace-size-debug (x alist)
   (declare (xargs :mode :program))
   (let ((method    (rw.trace->method x))
         (subtraces (rw.trace->subtraces x)))
     (if (equal method 'crewrite-rule)
         (let* ((rule               (first (rw.trace->extras x)))
                (name               (rw.rule->name rule))
                (num-subtraces      (rw.count-traces-list subtraces))
                (num-fsubtraces     (rw.count-forcing-traces-list subtraces))
                (alist-entry        (cdr (ACL2::hons-assoc-equal name alist)))
                (new-count          (+ num-subtraces (car alist-entry)))
                (new-fcount         (+ num-fsubtraces (cdr alist-entry)))
                (new-alist          (ACL2::hons-acons name
                                                      (cons new-count new-fcount)
                                                      alist)))
           (rw.trace-size-debug-list subtraces new-alist))
       (rw.trace-size-debug-list subtraces alist))))
 (ACL2::defun rw.trace-size-debug-list (x alist)
   (declare (xargs :mode :program))
   (if (consp x)
       (rw.trace-size-debug-list (cdr x)
                                 (rw.trace-size-debug (car x) alist))
     alist)))

(ACL2::memoize 'rw.count-forcing-traces)
(ACL2::memoize 'rw.count-traces)



(defun get-traces-from-ccstep-list (x)
  (declare (xargs :mode :program))
  (if (consp x)
      (if (third (car x))
          (cons (third (car x))
                (get-traces-from-ccstep-list (cdr x)))
        (get-traces-from-ccstep-list (cdr x)))
    nil))

(defun get-traces-from-ccstep-list-list (x)
  (declare (xargs :mode :program))
  (if (consp x)
      (revappend (get-traces-from-ccstep-list (car x))
                 (get-traces-from-ccstep-list-list (cdr x)))
    nil))

(defun get-traces-from-skeleton (x)
  (declare (xargs :mode :program))
  (if (not (tactic.skeleton->tacname x))
      nil
    (let ((name (tactic.skeleton->tacname x)))
      (if (equal name 'crewrite-all)
          (let* ((ccsteps (nth 4 (tactic.skeleton->extras x)))
                 (traces  (get-traces-from-ccstep-list-list ccsteps)))
            (revappend traces
                       (get-traces-from-skeleton (tactic.skeleton->history x))))
        (get-traces-from-skeleton (tactic.skeleton->history x))))))




(defun crewrite-cost-report-line (entry)
  (declare (xargs :mode :program))
  (let ((name (car entry))
        (count (car (cdr entry)))
        (fcount (cdr (cdr entry))))
    (ACL2::cw! "  ~c0  ~c1   ~s2~%"
               (cons count 10)
               (cons fcount 10)
               name)))

(defun crewrite-cost-report (alist)
  (declare (xargs :mode :program))
  (if (consp alist)
      (ACL2::prog2$ (crewrite-cost-report-line (car alist))
                    (crewrite-cost-report (cdr alist)))
    nil))


(defun %debug-crewrite-cost ()
  (declare (xargs :guard t))
  nil)


(ACL2::defttag %debug-crewrite-cost)

(ACL2::progn!
 (ACL2::set-raw-mode t)
 (ACL2::defun %debug-crewrite-cost ()
  (let* ((report-lines (remove-shadowed-pairs
                        (rw.trace-size-debug-list
                         (get-traces-from-skeleton (tactic.harness->skeleton (ACL2::w ACL2::*the-live-state*))) nil)
                        nil))
         (sorted-lines (ACL2::sort report-lines
                                   #'(lambda (x y) (ACL2::> (second x) (second y))))))
    (crewrite-cost-report sorted-lines))))

