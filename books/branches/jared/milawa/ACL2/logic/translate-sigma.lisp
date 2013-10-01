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
(include-book "translate")
(include-book "substitute-term")
(set-verify-guards-eagerness 2)
(set-case-split-limitations nil)
(set-well-founded-relation ord<)
(set-measure-function rank)



(defund logic.translate-sigma (x)
  ;; We should be given a true-list of (var term) 2-tuples, where each var is a
  ;; variable symbol and each term is an untranslated term.  We translate each
  ;; term and call the resulting (var . translated term) pairs the answer.
  ;;
  ;; We return (t . answer) if all the terms are successfully translated, or
  ;; nil otherwise.  If we return nil, a message will be printed indicating
  ;; where the error occurs.
  (declare (xargs :guard t))
  (if (consp x)
      (and (tuplep 2 (car x))
           (let* ((var        (first (car x)))
                  (term       (second (car x)))
                  (trans-term (logic.translate term)))
             (and (logic.variablep var)
                  trans-term
                  (let ((others (logic.translate-sigma (cdr x))))
                    (and others
                         (let* ((others-answer (cdr others))
                                (answer        (cons (cons var trans-term) others-answer)))
                           (cons t answer)))))))
    (if (equal x nil)
        (cons t nil)
      nil)))

(defthm logic.sigmap-of-cdr-of-logic.translate-sigma
  (equal (logic.sigmap (cdr (logic.translate-sigma x)))
         t)
  :hints(("Goal" :in-theory (enable logic.translate-sigma))))


(defund logic.translate-sigma-list (x)
  ;; We should be given a true-list of translatable sigmas.  We translate them
  ;; all, producing answer = (sigma1 ... sigmaN), and return (t . answer) upon
  ;; success.  If any sigma is not translatable, we return nil.
  (if (consp x)
      (let ((part1 (logic.translate-sigma (car x))))
        (and part1
             (let ((part2 (logic.translate-sigma-list (cdr x))))
               (and part2
                    (let ((answer (cons (cdr part1) (cdr part2))))
                      (cons t answer))))))
    (if (equal x nil)
        (cons t nil)
      nil)))

(defthm logic.sigma-listp-of-cdr-of-logic.translate-sigma-list
  (equal (logic.sigma-listp (cdr (logic.translate-sigma-list x)))
         t)
  :hints(("Goal" :in-theory (enable logic.translate-sigma-list))))



(defund logic.translate-sigma-list-list (x)
  ;; We should be given a true-list of translatable sigma lists.  We translate
  ;; them all, producing answer = (sigmas1 ... sigmasN), and return (t
  ;; . answer) upon success.  If any sigma is not translatable, we return nil.
  (if (consp x)
      (let ((part1 (logic.translate-sigma-list (car x))))
        (and part1
             (let ((part2 (logic.translate-sigma-list-list (cdr x))))
               (and part2
                    (let ((answer (cons (cdr part1) (cdr part2))))
                      (cons t answer))))))
    (if (equal x nil)
        (cons t nil)
      nil)))

(defthm logic.sigma-list-listp-of-cdr-of-logic.translate-sigma-list-list
  (equal (logic.sigma-list-listp (cdr (logic.translate-sigma-list-list x)))
         t)
  :hints(("Goal" :in-theory (enable logic.translate-sigma-list-list))))