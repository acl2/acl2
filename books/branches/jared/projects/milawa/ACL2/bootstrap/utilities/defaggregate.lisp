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


(defun %make-accessors (name fields)
  (declare (xargs :mode :program))
  (if (consp fields)
      (cons `(%autoadmit ,(accessor-name name (car fields)))
            (%make-accessors name (cdr fields)))
    nil))

(defun %make-accessor-of-constructor (name field)
  (declare (xargs :mode :program))
  `(%autoprove ,(ACL2::mksym (accessor-name name field) '-of- (constructor-name name))
               (%enable default
                        ,(accessor-name name field)
                        ,(constructor-name name))))

(defun %make-accessors-of-constructor-aux (name fields)
  (declare (xargs :mode :program))
  (if (consp fields)
      (cons (%make-accessor-of-constructor name (car fields))
            (%make-accessors-of-constructor-aux name (cdr fields)))
    nil))

(defun %make-accessors-of-constructor (name fields)
  (declare (xargs :mode :program))
  (%make-accessors-of-constructor-aux name fields))

(defun %make-requirement-of-recognizer (name require accnames)
  (declare (xargs :mode :program))
  `(%autoprove ,(ACL2::mksym 'forcing- (first require))
               (%enable default
                        ,(recognizer-name name)
                        ,@accnames)))

(defun %make-requirements-of-recognizer-aux (name require accnames)
  (declare (xargs :mode :program))
  (if (consp require)
      (cons (%make-requirement-of-recognizer name (car require) accnames)
            (%make-requirements-of-recognizer-aux name (cdr require) accnames))
    nil))

(defun %make-requirements-of-recognizer (name require fields)
  (declare (xargs :mode :program))
  (%make-requirements-of-recognizer-aux name require (accessor-names name fields)))


(defmacro %defaggregate (name fields &key require)
  ;; BOZO change defaggregate so it stores its name, fields, and requirements
  ;; in a table; then we can change the defaggregate in one place and
  ;; %defaggregate can consult these tables instead of needing to be a whole
  ;; copy of them big form.
  (declare (ACL2::ignorable name fields require))
  (let ((foop (recognizer-name name))
        (make-foo (constructor-name name)))
    (declare (ACL2::ignorable foop make-foo))
    `(encapsulate
      ()
      (%autoadmit ,(recognizer-name name))
      (%autoadmit ,(constructor-name name))

      ,@(%make-accessors name fields)

      (%autoprove ,(ACL2::mksym make-foo '-under-iff)
                  (%enable default ,make-foo))

      (%autoprove ,(ACL2::mksym 'booleanp-of- foop)
                  (%enable default ,foop))

      ,(if (consp require)
           `(%autoprove ,(ACL2::mksym 'forcing- foop '-of- make-foo)
                        (%enable default ,foop ,make-foo))
         `(%autoprove ,(ACL2::mksym foop '-of- make-foo)
                      (%enable default ,foop ,make-foo)))

      ,@(%make-accessors-of-constructor name fields)
      ,@(%make-requirements-of-recognizer name require fields)

      )))
