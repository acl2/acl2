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

(ACL2::defun ACL2::to-flat-string (x)
  (let ((ACL2::*print-circle* nil)
        (ACL2::*print-escape* t)
        #+DRAFT-ANSI-CL-2 (ACL2::*print-lines* nil)
        #+DRAFT-ANSI-CL-2 (ACL2::*print-miser-width* nil)
        #+DRAFT-ANSI-CL-2 (ACL2::*print-pprint-dispatch* nil)
        #+DRAFT-ANSI-CL-2 (ACL2::*print-readably* t)
        #+DRAFT-ANSI-CL-2 (ACL2::*print-right-margin* nil)
        (ACL2::*readtable* ACL2::*acl2-readtable*)
        (ACL2::*print-case* :upcase)
        (ACL2::*print-pretty* nil)
        (ACL2::*print-level* nil)
        (ACL2::*print-length* nil))
    (ACL2::prin1-to-string x)))

(ACL2::defparameter MILAWA::*rw.crewrite-depth* 0)

(ACL2::defun %untrace-crewrite ()
  (ACL2::progn
   (CCL:unadvise tactic.crewrite-first-tac)
   (CCL:unadvise tactic.crewrite-all-tac)
   (CCL:unadvise rw.crewrite-entry)
   (CCL:unadvise rw.crewrite-note-fn)
   nil))

(ACL2::defun %trace-crewrite ()
  (ACL2::progn
   (CCL:advise tactic.crewrite-first-tac
               (ACL2::setf *rw.crewrite-depth* 0)
               :when :before)
   (CCL:advise tactic.crewrite-all-tac
               (ACL2::setf *rw.crewrite-depth* 0)
               :when :before)
   (CCL:advise rw.crewrite-entry
               (let* ((arglist  CCL::arglist)
                      (flag     (nth 0 arglist))
                      (assms    (nth 1 arglist))
                      (x        (nth 2 arglist))
                      (rule[s]  (nth 3 arglist))
                      (sigma[s] (nth 4 arglist))
                      (hypcache (nth 5 arglist))
                      (iffp     (nth 6 arglist))
                      (blimit   (nth 7 arglist))
                      (rlimit   (nth 8 arglist))
                      (anstack  (nth 9 arglist))
                      (control  (nth 10 arglist)))
                 (declare (ACL2::ignorable flag assms x rule[s] sigma[s] hypcache iffp blimit rlimit anstack control))
                 (cond ((equal flag 'term)
                        (ACL2::prog2$
                         (ACL2::setf *rw.crewrite-depth* (+ *rw.crewrite-depth* 1))
                         (ACL2::fmt1! "~s0~x1> ~x2 ~s3~%~
                                   ~s0~x1> Assms ~s4~%"
                                      (list (cons #\0 (ACL2::coerce (repeat #\Space *rw.crewrite-depth*) 'ACL2::string))
                                            (cons #\1 *rw.crewrite-depth*)
                                            (cons #\2 (if iffp 'RW_IFF 'RW_EQL))
                                            (cons #\3 (ACL2::to-flat-string x))
                                            (cons #\4 (ACL2::to-flat-string (%print-negate-hyps
                                                                             (fast-app
                                                                              (rw.hypbox->left (rw.assms->hypbox assms))
                                                                              (rw.hypbox->right (rw.assms->hypbox assms)))))))
                                      0
                                      ACL2::*standard-co*
                                      ACL2::*the-live-state*
                                      nil)))
                       ((equal flag 'rule)
                        (ACL2::fmt1! "~s0~x1> ~x2: try matching ~s3~%"
                                     (list (cons #\0 (ACL2::coerce (repeat #\Space *rw.crewrite-depth*) 'ACL2::string))
                                           (cons #\1 *rw.crewrite-depth*)
                                           (cons #\2 (rw.rule->name rule[s]))
                                           (cons #\3 (ACL2::to-flat-string (rw.rule->lhs rule[s]))))
                                     0
                                     ACL2::*standard-co*
                                     ACL2::*the-live-state*
                                     nil))
                       ((equal flag 'match)
                        (ACL2::fmt1! "~s0~x1> ~x2: try sigma ~s3~%"
                                     (list (cons #\0 (ACL2::coerce (repeat #\Space *rw.crewrite-depth*) 'ACL2::string))
                                           (cons #\1 *rw.crewrite-depth*)
                                           (cons #\2 (rw.rule->name rule[s]))
                                           (cons #\3 (ACL2::to-flat-string sigma[s])))
                                     0
                                     ACL2::*standard-co*
                                     ACL2::*the-live-state*
                                     nil))
                       ((equal flag 'hyp)
                        (let ((goal (logic.substitute (rw.hyp->term x) sigma[s])))
                          (ACL2::fmt1! "~s0~x1> ~x2: hyp instance: ~s3~%"
                                       (list (cons #\0 (ACL2::coerce (repeat #\Space *rw.crewrite-depth*) 'ACL2::string))
                                             (cons #\1 *rw.crewrite-depth*)
                                             (cons #\2 (rw.rule->name rule[s]))
                                             (cons #\3 (ACL2::to-flat-string goal)))
                                       0
                                       ACL2::*standard-co*
                                       ACL2::*the-live-state*
                                       nil)))
                       (t nil)))
               :when :before)
   (CCL:advise rw.crewrite-note-fn
               (let* ((arglist  CCL::arglist)
                      (flag     (nth 0 arglist))
                      (assms    (nth 1 arglist))
                      (x        (nth 2 arglist))
                      (rule[s]  (nth 3 arglist))
                      (sigma[s] (nth 4 arglist))
                      (hypcache (nth 5 arglist))
                      (iffp     (nth 6 arglist))
                      (blimit   (nth 7 arglist))
                      (rlimit   (nth 8 arglist))
                      (anstack  (nth 9 arglist))
                      (control  (nth 10 arglist))
                      (note     (nth 11 arglist)))
                 (declare (ACL2::ignorable flag assms x rule[s] sigma[s] hypcache iffp blimit rlimit anstack control note))
                 (ACL2::prog2$
                  (ACL2::fmt1! "~s0<~x1 NOTE: ~s2~%"
                               (list (cons #\0 (ACL2::coerce (repeat #\Space *rw.crewrite-depth*) 'ACL2::string))
                                     (cons #\1 *rw.crewrite-depth*)
                                     (cons #\2 (ACL2::to-flat-string note)))
                               0
                               ACL2::*standard-co*
                               ACL2::*the-live-state*
                               nil)
                  (if (equal (car note) 'rewrote-to)
                      (ACL2::setf *rw.crewrite-depth* (- *rw.crewrite-depth* 1))
                    nil)))
               :when :before)
   nil))