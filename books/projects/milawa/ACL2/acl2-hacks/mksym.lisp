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

(in-package "ACL2")

(defun concatenate-symbols (x)
  (declare (xargs :guard (symbol-listp x) :mode :program))
  (if (consp x)
      (concatenate 'string
                   (symbol-name (car x))
                   (concatenate-symbols (cdr x)))
    ""))

(defun has-namespace1 (char-list)
  (declare (xargs :mode :program))
  (if (consp char-list)
      (or (equal (car char-list) #\.)
          (has-namespace1 (cdr char-list)))
    nil))

(defun has-namespace (symbol)
  (declare (xargs :mode :program))
  (has-namespace1 (coerce (symbol-name symbol) 'list)))

(defun extract-namespace1 (char-list)
  (declare (xargs :mode :program))
  (if (consp char-list)
      (if (equal (car char-list) #\.)
          nil
        (cons (car char-list)
              (extract-namespace1 (cdr char-list))))
    nil))

(defun extract-namespace (symbol)
  (declare (xargs :mode :program))
  (let* ((char-list (coerce (symbol-name symbol) 'list))
         (namespace (coerce (extract-namespace1 char-list) 'string)))
    (intern-in-package-of-symbol namespace 'MILAWA::foo)))

(defun extract-nonnamespace1 (char-list)
  (declare (xargs :mode :program))
  (if (consp char-list)
      (if (equal (car char-list) #\.)
          (cdr char-list)
        (extract-nonnamespace1 (cdr char-list)))
    nil))

(defun extract-nonnamespace (symbol)
  (declare (xargs :mode :program))
  (let* ((char-list    (coerce (symbol-name symbol) 'list))
         (nonnamespace (coerce (extract-nonnamespace1 char-list) 'string)))
    (intern-in-package-of-symbol nonnamespace 'MILAWA::foo)))

(defmacro mksym (&rest args)
  `(intern-in-package-of-symbol (concatenate-symbols (list ,@args)) 'MILAWA::foo))