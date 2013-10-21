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
(include-book "utilities")
(%interactive)

(defun %defmap-fn (map key val key-list val-list val-of-nil)
  (declare (xargs :mode :program))
  (let ((mapp (car map))
        (keyp (car key))
        (valp (car val))
        (key-listp (car key-list))
        (val-listp (car val-list))
        ;(map-formals (cdr map))
        ;(key-formals (cdr key))
        ;(val-formals (cdr val))
        ;(key-list-formals (cdr key-list))
        ;(val-list-formals (cdr val-list))
        )
    `(defsection ,mapp

       (local (%forcingp nil))

       (%autoadmit ,mapp)

       (%autoprove ,(ACL2::mksym mapp '-when-not-consp)
                   (%restrict default ,mapp (equal x 'x)))

       (%autoprove ,(ACL2::mksym mapp '-of-cons)
                   (%restrict default ,mapp (equal x '(cons a x))))

       (%autoprove ,(ACL2::mksym 'consp-when-memberp-of- mapp)
                   (%cdr-induction x))

       (%autoprove ,(ACL2::mksym 'consp-when-memberp-of- mapp '-alt))

       (local (%disable default
                        ,(ACL2::mksym 'consp-when-memberp-of- mapp)
                        ,(ACL2::mksym 'consp-when-memberp-of- mapp '-alt)))

       (%autoprove ,(ACL2::mksym keyp '-of-car-when-memberp-of- mapp)
                   (%cdr-induction x))

       (%autoprove ,(ACL2::mksym keyp '-when-lookup-in- mapp)
                   (%cdr-induction x))

       (%autoprove ,(ACL2::mksym valp '-of-cdr-when-memberp-of- mapp)
                   (%cdr-induction x))

       (%autoprove ,(ACL2::mksym 'booleanp-of- mapp)
                   (%cdr-induction x))

       (%autoprove ,(ACL2::mksym mapp '-of-list-fix)
                   (%cdr-induction x))

       (%autoprove ,(ACL2::mksym mapp '-of-app)
                   (%cdr-induction x))

       (%autoprove ,(ACL2::mksym mapp '-of-rev)
                   (%cdr-induction x))

       (%autoprove ,(ACL2::mksym mapp '-of-remove-all-when- mapp)
                   (%cdr-induction x))

       (%autoprove ,(ACL2::mksym mapp '-of-remove-duplicates)
                   (%cdr-induction x)
                   (%enable default ,(ACL2::mksym 'consp-when-memberp-of- mapp)))

       (%autoprove ,(ACL2::mksym mapp '-of-difference-when- mapp)
                   (%cdr-induction x))

       (%autoprove ,(ACL2::mksym mapp '-of-subset-when- mapp)
                   (%cdr-induction x)
                   (%enable default ,(ACL2::mksym 'consp-when-memberp-of- mapp)))

       (%autoprove ,(ACL2::mksym mapp '-of-subset-when- mapp '-alt))

       ,@(if (not key-list)
             nil
           `((%autoprove ,(ACL2::mksym key-listp '-of-domain-when- mapp)
                         (%cdr-induction x))))

       ,@(if (not val-list)
             nil
           `((%autoprove ,(ACL2::mksym val-listp '-of-range-when- mapp)
                         (%cdr-induction x))))

       (%autoprove ,(ACL2::mksym 'mapp-when- mapp)
                   (%cdr-induction x))

       (%autoprove ,(ACL2::mksym valp '-of-cdr-of-lookup-when- mapp)
                   (%cdr-induction x))

       ,@(if val-of-nil
             nil
           `((%autoprove ,(ACL2::mksym 'cdr-of-lookup-under-iff-when- mapp)
                         (%use (%instance (%thm ,(ACL2::mksym valp '-of-cdr-of-lookup-when- mapp))))
                         (%disable default ,(ACL2::mksym valp '-of-cdr-of-lookup-when- mapp)))))

       )))

(defmacro %defmap (&key map key val key-list val-list (val-of-nil 't))
  (declare (xargs :guard (and (ACL2::symbol-listp map)
                              (ACL2::symbol-listp key)
                              (ACL2::symbol-listp val)
                              (ACL2::symbol-listp key-list)
                              (ACL2::symbol-listp val-list)
                              (consp map)
                              (consp key)
                              (consp val)
                              (or (consp key-list) (not key-list))
                              (or (consp val-list) (not val-list))
                              ;; Argument lists must all be unique
                              (uniquep (cdr map))
                              (uniquep (cdr key))
                              (uniquep (cdr val))
                              (uniquep (cdr key-list))
                              (uniquep (cdr val-list))
                              ;; Argument lists must contain only the names in
                              ;; the map formals
                              (subsetp (cdr key) (cdr map))
                              (subsetp (cdr val) (cdr map))
                              (or (not key-list)
                                  (subsetp (cdr key-list) (cdr map)))
                              (or (not val-list)
                                  (subsetp (cdr val-list) (cdr map)))
                              ;; x must be in each argument list
                              ;; a,b must not be found in any argument list
                              (memberp 'x (cdr map))
                              (not (memberp 'a (cdr map)))
                              (not (memberp 'y (cdr map))))))
  (%defmap-fn map key val key-list val-list val-of-nil))
