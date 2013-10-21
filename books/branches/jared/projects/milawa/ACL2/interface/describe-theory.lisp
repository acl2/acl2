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


;; BOZO I had two versions of this.  Not sure which one is better?

;; (ACL2::defun sort-symbol-list (x)
;;              (declare (xargs :mode :program)
;;                       (ignore x))
;;              (ACL2::er hard 'sort-symbol-list "Error: sort-symbol-list has not been redefined!~%"))

;; (ACL2::defttag sort-symbol-list)

;; (ACL2::progn!
;;  (ACL2::set-raw-mode t)
;;  (ACL2::defun sort-symbol-list (x)
;;               (declare (xargs :mode :program))
;;               (ACL2::sort x #'symbol-<)))

;; (defmacro %describe-theory (theoryname)
;;   `(describe-theory-fn ',theoryname (ACL2::w ACL2::state)))

;; (defun describe-theory-fn (theoryname world)
;;   (declare (xargs :mode :program))
;;   (sort-symbol-list (rw.fast-rule-list-names$ (rw.gather-rules-from-theory
;;                                                (tactic.find-theory theoryname world)
;;                                                ''t
;;                                                (tactic.harness->syndefs world)
;;                                                nil)
;;                                               nil)))



(defmacro %describe-theory (theoryname)
  `(describe-theory-fn ',theoryname (ACL2::w ACL2::state)))

(defun describe-theory-fn (theoryname world)
  (declare (xargs :mode :program))
  (let* ((tactic-world (tactic.harness->world world))
         (theory   (or (tactic.find-theory theoryname tactic-world)
                       (acl2::er hard? 'describe-theory-fn "Theory ~x0 not found." theoryname)))
         (defs     (tactic.world->defs tactic-world))
         (rules    (rw.gather-rules-from-theory (cdr theory) ''t defs nil))
         (names    (rw.rule-list-names rules)))
    (sort-symbols names)))

