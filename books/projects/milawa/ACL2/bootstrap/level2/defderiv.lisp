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

(defun %defderiv-fn (name world hintsmap omit-okp)
  (declare (xargs :mode :program))
  (let* ((info-entry     (lookup name (dd.get-info-for-%defderiv world)))
         (local-axioms   (second info-entry))
         (local-thms     (third info-entry))
         (soundness-hint (fourth info-entry))
         (name-okp       (ACL2::mksym name '-okp)))
    `(encapsulate
      ()
      (encapsulate
       ()
       ,@(if (or local-axioms local-thms)
             `((local (%enable default
                               ,@(strip-firsts local-axioms)
                               ,@(strip-firsts local-thms))))
           nil)

       (%autoadmit ,name)
       (%noexec ,name)

       (local (%enable default ,name))

       (%autoprove ,(ACL2::mksym name '-under-iff)
                   ;; BOZO globally disable forcing here after implementing
                   ;; a flag in the control structure for it
                   )
       (%autoprove ,(ACL2::mksym 'forcing-logic.appealp-of- name)
                   ,@(cdr (lookup (ACL2::mksym 'forcing-logic.appealp-of- name) hintsmap)))

       (%autoprove ,(ACL2::mksym 'forcing-logic.conclusion-of- name)
                   ,@(cdr (lookup (ACL2::mksym 'forcing-logic.conclusion-of- name) hintsmap)))

       (%autoprove ,(ACL2::mksym 'forcing-logic.proofp-of- name)
                   ,@(cdr (lookup (ACL2::mksym 'forcing-logic.proofp-of- name) hintsmap))))

      ,@(if omit-okp
            nil
          `((%autoadmit ,name-okp)
            (%autoprove ,(ACL2::mksym 'booleanp-of- name-okp)
                        ,@(or (cdr (lookup (ACL2::mksym 'booleanp-of- name-okp) hintsmap))
                              `((%enable default ,name-okp))))
            (%autoprove ,(ACL2::mksym name-okp '-of-logic.appeal-identity)
                        ,@(or (cdr (lookup (ACL2::mksym name-okp '-of-logic.appeal-identity) hintsmap))
                              `((%enable default ,name-okp))))
            (local (%enable default backtracking-logic.formula-atblp-rules))
            (local (%disable default
                             forcing-logic.formula-atblp-rules
                             forcing-lookup-of-logic.function-name-free
                             forcing-logic.term-list-atblp-of-logic.function-args))
            (%autoprove ,(ACL2::mksym 'lemma-1-for-soundness-of- name-okp)
                        (%enable default ,name-okp)
                        ,@(or (cdr (lookup (ACL2::mksym 'lemma-1-for-soundness-of- name-okp) hintsmap))
                              nil))
            (%autoprove ,(ACL2::mksym 'lemma-2-for-soundness-of- name-okp)
                        (%enable default ,name-okp)
                        ,@(or (cdr (lookup (ACL2::mksym 'lemma-2-for-soundness-of- name-okp) hintsmap))
                              nil))
            (%autoprove ,(ACL2::mksym 'forcing-soundness-of- name-okp)
                        ,@(or (cdr (lookup (ACL2::mksym 'forcing-soundness-of- name-okp) hintsmap))
                              `((%enable default
                                         ,(ACL2::mksym 'lemma-1-for-soundness-of- name-okp)
                                         ,(ACL2::mksym 'lemma-2-for-soundness-of- name-okp))
                                (%use (%instance (%thm forcing-logic.provablep-when-logic.proofp)
                                                 (x (,name ,@soundness-hint))))
                                (%auto :strategy (cleanup split crewrite))
                                (%enable default ,name-okp)
                                (%auto :strategy (cleanup split crewrite)))
                              )))))))

(defmacro %defderiv (name &key hintsmap omit-okp)
  `(ACL2::make-event (%defderiv-fn ',name (ACL2::w ACL2::state) ',hintsmap ',omit-okp)))

(defmacro %deftheorem (name)
  ;; We don't need to bother with proving the theorems.  But, we do want to
  ;; have the theorem functions available.
  `(encapsulate
    ()
    (%autoadmit ,name)
    (%noexec ,name)))
