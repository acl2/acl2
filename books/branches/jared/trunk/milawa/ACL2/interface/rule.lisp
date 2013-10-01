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
(set-verify-guards-eagerness 2)
(set-case-split-limitations nil)
(set-well-founded-relation ord<)
(set-measure-function rank)


;; Rule structure creation
;;
;; We provide some macros for generating rewrite rule structures.

(defmacro %hyp (term &key force limit)
  `(%hyp-fn ',term ,force ,limit))

(defun %hyp-fn (term force limit)
  (declare (xargs :mode :program))
  (let ((term-trans (logic.translate term)))
    (cond ((not term-trans)
           (ACL2::er hard '%hyp "The proposed hyp, ~x0, is not translatable.~%" term))
          ((not (rw.force-modep force))
           (ACL2::er hard '%hyp "The proposed force mode, ~x0, is invalid.~%" force))
          (t
           (rw.hyp term-trans
                   force
                   (if limit t nil)
                   (nfix limit))))))

(defun %hyps-fn-aux (terms force limit)
  (declare (xargs :mode :program))
  (if (consp terms)
      (cons `(%hyps ,(car terms) :force ,force :limit ,limit)
            (%hyps-fn-aux (cdr terms) force limit))
    nil))

(defun %hyps-fn (flag hyp force limit)
  (declare (xargs :mode :program))
  (if (equal flag 'term)
      (if (and (consp hyp)
               (equal (car hyp) 'and))
          (%hyps-fn 'list (cdr hyp) force limit)
        (list `(%hyp ,hyp :force ,force :limit ,limit)))
    (if (consp hyp)
        (fast-app (%hyps-fn 'term (car hyp) force limit)
                  (%hyps-fn 'list (cdr hyp) force limit))
      nil)))

(defmacro %hyps (hyp &key force limit)
  (cons 'list (%hyps-fn 'term hyp force limit)))

(defmacro %rule (name &key (type 'inside) hyps lhs rhs (equiv 'equal) syntax)
  `(%rule-fn ',name ',type ,hyps ',lhs ',rhs ',equiv ',syntax))

(defun %rule-fn (name type hyps lhs rhs equiv syntax)
  (declare (xargs :mode :program))
  (let ((lhs-trans (logic.translate lhs))
        (rhs-trans (logic.translate rhs))
        (syntax-trans (logic.translate-list syntax)))
    (cond ((not (symbolp name))
           (ACL2::er hard '%rule "The proposed name, ~x0, is not a symbol.~%" name))
          ((not (memberp type '(inside outside manual)))
           (ACL2::er hard '%rule "The proposed type, ~x0, is not supported.~%" type))
          ((not lhs-trans)
           (ACL2::er hard '%rule "The proposed lhs, ~x0, is not translatable.~%" lhs))
          ((not rhs-trans)
           (ACL2::er hard '%rule "The proposed rhs, ~x0, is not translatable.~%" rhs))
          ((not (car syntax-trans))
           (ACL2::er hard '%rule "The proposed syntax, ~x0, is not translatable.~%" syntax))
          ((not (logic.all-functionsp (cdr syntax-trans)))
           (ACL2::er hard '%rule "The proposed syntax, ~x0, is not a list of function calls.~%" syntax))
          ((not (memberp equiv '(iff equal)))
           (ACL2::er hard '%rule "The proposed equiv, ~x0, is not equal or iff.~%" equiv))
          (t
           (rw.rule name
                    type
                    (rw.limit-hyps lhs-trans hyps)
                    equiv
                    lhs-trans
                    rhs-trans
                    (cdr syntax-trans)
                    (rw.critical-hyps lhs-trans hyps))))))


