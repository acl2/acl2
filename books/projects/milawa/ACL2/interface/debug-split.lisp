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
(include-book "core")


(defmacro %ensure-no-outstanding-goals (note)
  `(ACL2::make-event (%ensure-no-outstanding-goals-fn ',note (ACL2::w ACL2::state))))

(defun %ensure-no-outstanding-goals-fn (note world)
  (declare (xargs :mode :program))
  (if (consp (tactic.harness->goals world))
      (ACL2::er hard '%ensure-no-outstanding-goals
                "Expected no outstanding goals at ~x0.~%"
                note)
    '(ACL2::value-triple :invisible)))



(defmacro %debug-split ()
  `(ACL2::make-event (%debug-split-fn (ACL2::w ACL2::state))))

(defun %aux-debug-split-fn (goals i)
  (declare (xargs :mode :program))
  (if (consp goals)
      (cons `(defsection ,(ACL2::mksym 'debugging-goal- (ACL2::intern-in-package-of-symbol (STR::dwim-string-fix i) 'foo))
               (ACL2::value-triple (ACL2::cw "Now Debugging Goal ~x0.~%" ,i))
               (ACL2::value-triple (ACL2::cw "~x0~%" '(ACL2::table tactic-harness 'skeleton (tactic.initial-skeleton (list ',(car goals))))))
               (ACL2::table tactic-harness 'skeleton (tactic.initial-skeleton (list ',(car goals))))
               (%auto)
               (%ensure-no-outstanding-goals ,i))
            (%aux-debug-split-fn (cdr goals) (+ i 1)))
    nil))

(defun %debug-split-fn (world)
  (declare (xargs :mode :program))
  `(ACL2::progn ,@(%aux-debug-split-fn (tactic.harness->goals world) 1)))
