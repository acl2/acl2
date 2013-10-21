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

(ACL2::defttag hons-proofs)

(ACL2::progn!
 (ACL2::set-raw-mode t)

 (ACL2::defun logic.function (name args)
              (ACL2::hons name args))

 (ACL2::defun logic.lambda (xs b ts)
              (ACL2::hons (ACL2::hist 'lambda xs b) ts))

 (ACL2::defun logic.pequal (a b)
              (ACL2::hist 'pequal* a b))

 (ACL2::defun logic.por (a b)
              (ACL2::hist 'por* a b))

 (ACL2::defun logic.pnot (a)
              (ACL2::hist 'pnot* a))

 (ACL2::defun logic.appeal (method conclusion subproofs extras)
              (if extras
                  (ACL2::hist method conclusion subproofs extras)
                (if subproofs
                    (ACL2::hist method conclusion subproofs)
                  (ACL2::hist method conclusion))))

 (ACL2::defun logic.appeal-identity (x)
              (if (consp x)
                  x
                (ACL2::hons nil nil)))

 (ACL2::defun hons-lookup (key map)
              (ACL2::hons-get key map))

 (ACL2::defun hons-update (key val map)
              (ACL2::hons-acons key val map))

 (ACL2::defun rw.eqtrace (method iffp lhs rhs subtraces)
              (ACL2::hons (ACL2::hons lhs rhs)
                          (ACL2::hons iffp
                                      (ACL2::hons method subtraces))))

 (ACL2::defun rw.trace (method hypbox lhs rhs iffp subtraces extras)
              (ACL2::hons (ACL2::hons method rhs)
                          (ACL2::hons (ACL2::hons lhs iffp)
                                      (ACL2::hons hypbox
                                                  (ACL2::hons extras subtraces)))))

 (ACL2::defun rw.ftrace (rhs fgoals)
              (ACL2::hons rhs fgoals)))








