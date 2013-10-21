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
;;                                                                           ;;
;; EXTRA COPYRIGHT NOTICE.                                                   ;;
;;                                                                           ;;
;; This file is derived from type-set-b.lisp in the ACL2 3.1 sources.  I     ;;
;; have copied or adapted many of the comments verbatim, and the functions   ;;
;; have also been adapted to my system.  Of course, ACL2 is also GPL'd       ;;
;; software, so there is no impact on Milawa's license.                      ;;
;;                                                                           ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


;; worse-termp-patch.lsp
;;
;; This file can be used to patch your ACL2 image so that it logs all calls of
;; ACL2::worse-than to the file /tmp/worse-than.log.  Your image will be much
;; slower and you will potentially need many gigabytes of free disk space to do
;; this.
;;
;; Instructions for use:
;;
;;  1. Load this file in acl2-patches.lisp and create a new ACL2 image.
;;
;;  2. Certify whichever books you want to track the calls of worse-than for.
;;
;;  3. DESTROY THE MODIFIED IMAGE.  That is, create a new image without the
;;     tracing so that you don't get an infinite loop in step 5.
;;
;;  4. cd rewrite; omake worse-termp.cert
;;
;;  5. cd rewrite; ../modified-acl2 < worse-termp-tests.lsp to perform the
;;     tests.
;;
;; The test harness makes sure that our rw.worse-termp agrees with acl2's
;; worse-than function for all the "purely milawa" inputs you generate.  That
;; is, we throw out all tests which include rationals, strings, etc.

(mutual-recursion

(defun old-worse-than (term1 term2)

; Term1 is old-worse-than term2 if it is basic-old-worse-than term2 or some
; proper subterm of it is old-worse-than or equal to term2.  However, we
; know that if two terms are pseudo-variants of eachother, then the
; old-worse-than relation does not hold.

  (cond ((basic-old-worse-than term1 term2) t)
        ((pseudo-variantp term1 term2) nil)
        ((variablep term1)

; If term1 is a variable and not basic-old-worse-than term2, what do we know
; about term2?  Term2 might be a variable.  Term2 cannot be quote.
; Term2 might be a function application.  So is X old-worse-than X or Y or
; (F X Y)?  No.

         nil)
        ((fquotep term1)

; If term1 is a quote and not basic-old-worse-than term2, what do we know
; about term2?  Term2 might be a variable.  Also, term2 might be a
; quote, but if it is, term2 is bigger than term1.  Term2 might be a
; function application.  So is term1 old-worse-than a bigger quote?  No.
; Is term1 old-worse-than a variable or function application?  No.

         nil)

        (t (old-worse-than-lst (fargs term1) term2))))



(defun old-worse-than-or-equal (term1 term2)

; This function is not really mutually recursive and could be removed
; from this nest.  It determines whether term1 is term2 or worse than
; term2.  This nest defines old-worse-than and does not use this function
; despite the use of similarly named functions.

; Note:  This function is supposed to be equivalent to
; (or (equal term1 term2) (old-worse-than term1 term2)).

; Clearly, that is equivalent to

; (if (pseudo-variantp term1 term2)
;     (or (equal term1 term2) (old-worse-than term1 term2))
;     (or (equal term1 term2) (old-worse-than term1 term2)))

; But if pseudo-variantp is true, then old-worse-than must return nil.
; And if pseudo-variantp is nil, then the equal returns nil.  So we
; can simplify the if above to:

  (if (pseudo-variantp term1 term2)
      (equal term1 term2)
    (old-worse-than term1 term2)))

(defun basic-old-worse-than-lst1 (args1 args2)

; Is some element of args2 ``uglier'' than the corresponding element
; of args1.  Technically, a2 is uglier than a1 if a1 is atomic (a
; variable or constant) and a2 is not or a2 is old-worse-than a1.

  (cond ((null args1) nil)
        ((or (and (or (variablep (car args1))
                      (fquotep (car args1)))
                  (not (or (variablep (car args2))
                           (fquotep (car args2)))))
             (old-worse-than (car args2) (car args1)))
         t)
        (t (basic-old-worse-than-lst1 (cdr args1) (cdr args2)))))

(defun basic-old-worse-than-lst2 (args1 args2)

; Is some element of arg1 old-worse-than the corresponding element of args2?

  (cond ((null args1) nil)
        ((old-worse-than (car args1) (car args2)) t)
        (t (basic-old-worse-than-lst2 (cdr args1) (cdr args2)))))

(defun basic-old-worse-than (term1 term2)

; We say that term1 is basic-old-worse-than term2 if

; * term2 is a variable and term1 properly contains it, e.g., (F A B)
;   is basic-old-worse-than A;

; * term2 is a quote and term1 is either not a quote or is a bigger
;   quote, e.g., both X and '124 are basic-old-worse-than '17 and '(A B C D
;   E) is worse than 'X; or

; * term1 and term2 are applications of the same function and
;   no argument of term2 is uglier than the corresponding arg of term1, and
;   some argument of term1 is old-worse-than the corresponding arg of term2.

; The last case is illustrated by the fact that (F A B) is
; basic-old-worse-than (F A '17), because B is worse than '17, but (F '17
; B) is not basic-old-worse-than (F A '17) because A is worse than '17.
; Think of term2 as the old goal and term1 as the new goal.  Do we
; want to cut off backchaining?  Yes, if term1 is basic-old-worse-than
; term2.  So would we backchain from (F A '17) to (F '17 B)?  Yes,
; because even though one argument (the second) got worse (it went
; from 17 to B) another argument (the first) got better (it went from
; A to 17).

  (cond ((variablep term2)
         (cond ((eq term1 term2) nil)
               (t (occur term2 term1))))
        ((fquotep term2)
         (cond ((variablep term1) t)
               ((fquotep term1)
                (> (fn-count-evg (cadr term1))
                   (fn-count-evg (cadr term2))))
               (t t)))
        ((variablep term1) nil)
        ((fquotep term1) nil)
        ((cond ((flambda-applicationp term1)
                (equal (ffn-symb term1) (ffn-symb term2)))
               (t (eq (ffn-symb term1) (ffn-symb term2))))
         (cond ((pseudo-variantp term1 term2) nil)
               ((basic-old-worse-than-lst1 (fargs term1) (fargs term2)) nil)
               (t (basic-old-worse-than-lst2 (fargs term1) (fargs term2)))))
        (t nil)))

(defun some-subterm-old-worse-than-or-equal (term1 term2)

; Returns t if some subterm of term1 is old-worse-than or equal to term2.

  (cond ((variablep term1) (eq term1 term2))
        ((if (pseudo-variantp term1 term2)  ; see old-worse-than-or-equal
             (equal term1 term2)
           (basic-old-worse-than term1 term2))
         t)
        ((fquotep term1) nil)
        (t (some-subterm-old-worse-than-or-equal-lst (fargs term1) term2))))

(defun some-subterm-old-worse-than-or-equal-lst (args term2)
  (cond ((null args) nil)
        (t (or (some-subterm-old-worse-than-or-equal (car args) term2)
               (some-subterm-old-worse-than-or-equal-lst (cdr args) term2)))))

(defun old-worse-than-lst (args term2)

; We determine whether some element of args contains a subterm that is
; old-worse-than or equal to term2.  The subterm in question may be the
; element of args itself.  That is, we use ``subterm'' in the ``not
; necessarily proper subterm'' sense.

  (cond ((null args) nil)
        (t (or (some-subterm-old-worse-than-or-equal (car args) term2)
               (old-worse-than-lst (cdr args) term2)))))

)


(defun worse-than (term1 term2)
  ;; Write (test-worse-than term1 term2) to the log file
  (with-open-file
   (logfile "/tmp/worse-than.log"
            :direction :output
            :if-exists :append
            :if-does-not-exist :create)
   (format logfile "~a~%" (list 'test-worse-than term1 term2)))
  ;; Return the old value of worse-than.
  (old-worse-than term1 term2))

