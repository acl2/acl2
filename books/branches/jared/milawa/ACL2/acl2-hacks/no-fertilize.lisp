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

;; It is unfortunate that we have to write this file, but ACL2 provides no nice
;; way to disable fertilization and generalization, which usually don't work
;; and are not implemented in Milawa.
;;
;; Originally I implemented a custom "defthm" hint that inserted a :do-not
;; '(generalize fertilize) into my proofs on "Goal" automatically.  But this
;; does not get carried through into forcing rounds, and ACL2 does not provide
;; any kind of "All" target.  So, sometimes in forcing rounds I still had
;; fertilization taking place.
;;
;; Now we just use a default hint that always disables generalization and
;; fertilization when goals are stable under simplification.  This is chatty
;; but I don't have many alternatives.

(table no-fertilize-table 'fertilize-okp nil)
(table no-fertilize-table 'generalize-okp nil)

(defun no-fertilize-hint (world stable-under-simplificationp state)
  (declare (xargs :mode :program :stobjs state))
  (and stable-under-simplificationp
       (let ((generalize-okp (cdr (assoc 'generalize-okp (table-alist 'no-fertilize-table world))))
             (fertilize-okp  (cdr (assoc 'fertilize-okp (table-alist 'no-fertilize-table world)))))
         (cond ((and (not generalize-okp)
                     (not fertilize-okp))
                (prog2$ (if (not (gag-mode))
                            (cw ";; hint: no fertilize/generalize~|")
                          nil)
                        '(:do-not '(generalize fertilize))))
               ((not generalize-okp)
                (prog2$ (if (not (gag-mode))
                            (cw ";; hint: no generalize~|")
                          nil)
                        '(:do-not '(generalize))))
               ((not fertilize-okp)
                (prog2$ (if (not (gag-mode))
                            (cw ";; hint: no fertilize~|")
                          nil)
                        '(:do-not '(fertilize))))
               (t
                nil)))))

(add-default-hints! '((no-fertilize-hint world stable-under-simplificationp state)))

(defmacro allow-generalize (flag)
  (declare (xargs :guard (booleanp flag)))
  `(table no-fertilize-table 'generalize-okp ,flag))

(defmacro allow-fertilize (flag)
  (declare (xargs :guard (booleanp flag)))
  `(table no-fertilize-table 'fertilize-okp ,flag))

