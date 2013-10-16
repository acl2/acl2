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
(include-book "proofp")

(defmacro trace-proofp ()
  ;; Trace proofp, but show only the conclusions and hide the axioms, theorems,
  ;; and arity table.
  `(acl2::trace$ (logic.proofp :entry (list (logic.conclusion (car acl2::arglist))))))

(defmacro untrace$ ()
  `(acl2::untrace$))

(defun collect-axioms-aux (x)
  ;; Collect the appeals to axioms and theorems used throughout a proof, which
  ;; might be useful for debugging.
  (declare (xargs :mode :program))
  (if (consp x)
      (cond ((equal (car x) 'axiom)
             (if (equal (len x) 2)
                 (cons (list (second x)) nil)
               (cons (list 'ERROR-AXIOM-NOT-LEN-2) nil)))
            ((equal (car x) 'theorem)
             (if (equal (len x) 2)
                 (cons nil (list (second x)))
               (cons nil (list 'ERROR-THEOREM-NOT-LEN-2))))
            (t
             (let ((car-part (collect-axioms-aux (car x)))
                   (cdr-part (collect-axioms-aux (cdr x))))
               (cons (app (car car-part)
                          (car cdr-part))
                     (app (cdr car-part)
                          (cdr cdr-part))))))
    nil))

(defun collect-axioms (x)
  (declare (xargs :mode :program))
  (let ((data (collect-axioms-aux x)))
    (list (cons 'axioms (remove-duplicates (car data)))
          (cons 'theorems (remove-duplicates (cdr data))))))
