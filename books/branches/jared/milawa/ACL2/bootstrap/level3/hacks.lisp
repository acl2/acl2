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




(defthmd bust-up-logic.function-args-expensive
  (implies (and (ACL2::syntaxp (logic.constantp x))
                (consp x))
           (equal (equal x (logic.function-args y))
                  (and (consp (logic.function-args y))
                       (equal (car x) (car (logic.function-args y)))
                       (equal (cdr x) (cdr (logic.function-args y))))))
  :hints(("Goal" :in-theory (disable FORCING-TRUE-LISTP-OF-LOGIC.FUNCTION-ARGS))))

(defthmd bust-up-cdr-of-logic.function-args-expensive
  (implies (and (ACL2::syntaxp (logic.constantp x))
                (consp x))
           (equal (equal x (cdr (logic.function-args y)))
                  (and (consp (cdr (logic.function-args y)))
                       (equal (car x) (car (cdr (logic.function-args y))))
                       (equal (cdr x) (cdr (cdr (logic.function-args y))))))))

(defthmd bust-up-cdr-of-cdr-of-logic.function-args-expensive
  (implies (and (ACL2::syntaxp (logic.constantp x))
                (consp x))
           (equal (equal x (cdr (cdr (logic.function-args y))))
                  (and (consp (cdr (cdr (logic.function-args y))))
                       (equal (car x) (car (cdr (cdr (logic.function-args y)))))
                       (equal (cdr x) (cdr (cdr (cdr (logic.function-args y)))))))))

(%autoprove bust-up-logic.function-args-expensive (%forcingp nil))
(%autoprove bust-up-cdr-of-logic.function-args-expensive (%forcingp nil))
(%autoprove bust-up-cdr-of-cdr-of-logic.function-args-expensive (%forcingp nil))



;; (DEFTHM CDR-OF-CDR-UNDER-IFF-WHEN-TRUE-LISTP-WITH-LEN-FREE-alt
;;   (IMPLIES (AND (EQUAL n (lEN X))
;;                 (SYNTAXP (ACL2::QUOTEP N))
;;                 (TRUE-LISTP X))
;;            (IFF (CDR (CDR X)) (< 2 N))))

;; (%autoprove CDR-OF-CDR-UNDER-IFF-WHEN-TRUE-LISTP-WITH-LEN-FREE-alt
;;             (%use (%instance (%thm CDR-OF-CDR-UNDER-IFF-WHEN-TRUE-LISTP-WITH-LEN-FREE))))

;; (DEFTHM LOGIC.FUNCTION-ARGS-UNDER-IFF-WITH-LEN-FREE-alt
;;   (IMPLIES (AND (EQUAL N (LEN (LOGIC.FUNCTION-ARGS TERM)))
;;                 (SYNTAXP (ACL2::QUOTEP N))
;;                 (< 0 N))
;;            (IFF (LOGIC.FUNCTION-ARGS TERM) T)))

;; (%autoprove LOGIC.FUNCTION-ARGS-UNDER-IFF-WITH-LEN-FREE-alt)

;; (DEFTHM CDR-OF-CDR-OF-CDR-UNDER-IFF-WHEN-TRUE-LISTP-WITH-LEN-FREE-alt
;;   (IMPLIES (AND (EQUAL n (LEN X))
;;                 (SYNTAXP (ACL2::QUOTEP N))
;;                 (TRUE-LISTP X))
;;            (IFF (CDR (CDR (CDR X))) (< 3 N))))

;; (%autoprove CDR-OF-CDR-OF-CDR-UNDER-IFF-WHEN-TRUE-LISTP-WITH-LEN-FREE-alt
;;             (%use (%instance (%thm CDR-OF-CDR-OF-CDR-UNDER-IFF-WHEN-TRUE-LISTP-WITH-LEN-FREE))))





(defthm logic.term-list-atblp-of-cons-gross
  (implies (ACL2::syntaxp (logic.constantp x))
           (equal (logic.term-list-atblp x atbl)
                  (if (consp x)
                      (and (logic.term-atblp (car x) atbl)
                           (logic.term-list-atblp (cdr x) atbl))
                    t))))

(%autoprove logic.term-list-atblp-of-cons-gross)



(defthm logic.sigma-atblp-of-cons-gross
  (implies (ACL2::syntaxp (logic.constantp x))
           (equal (logic.sigma-atblp x atbl)
                  (if (consp x)
                      (and (consp (car x))
                           (logic.variablep (car (car x)))
                           (logic.term-atblp (cdr (car x)) atbl)
                           (logic.sigma-atblp (cdr x) atbl))
                      t))))

(%autoprove logic.sigma-atblp-of-cons-gross)



(defsection logic.substitute-list-of-cons-gross
  ;; This rule fixes a problem that comes up when we run into terms of the form
  ;; (logic.substitute-list '(x y) ...).  Here, our cons rule does not fire
  ;; because our patmatch code does not allow it do.  We should probably fix
  ;; our pattern matcher in the long run, but for now we can emulate it in a
  ;; kind of gross way using a syntactic restriction.
  (%prove (%rule logic.substitute-list-of-cons-gross
                 :hyps (list (%hyp (consp x)))
                 :lhs (logic.substitute-list x sigma)
                 :rhs (cons (logic.substitute (car x) sigma)
                            (logic.substitute-list (cdr x) sigma))
                 :syntax ((logic.constantp x))))
  (%auto)
  (%qed)
  (%enable default logic.substitute-list-of-cons-gross))

