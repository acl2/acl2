; Copyright (C) 2006  University of Texas at Austin

; This program is free software; you can redistribute it and/or modify
; it under the terms of the GNU General Public License as published by
; the Free Software Foundation; either version 2 of the License, or
; (at your option) any later version.

; This program is distributed in the hope that it will be useful,
; but WITHOUT ANY WARRANTY; without even the implied warranty of
; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
; GNU General Public License for more details.

; You should have received a copy of the GNU General Public License
; along with this program; if not, write to the Free Software
; Foundation, Inc., 675 Mass Ave, Cambridge, MA 02139, USA.

; Written by:  Matt Kaufmann
; email:       Kaufmann@cs.utexas.edu
; Department of Computer Sciences
; University of Texas at Austin
; Austin, TX 78712-1188 U.S.A.

; October, 2006

; In a nutshell:

; If you submit (bash term), then the result is a list of goals to which ACL2
; can simplify term when attempting to prove it.  (In particular, if the result
; is nil, then ACL2 can prove term.)  More accurately: (bash term) returns (mv
; nil val state), where: val is a list of terms, in untranslated (user-level)
; form, whose provability implies the provability of the input term.  If ACL2
; cannot simplify the input term (e.g., if there is a translation error), then
; it prints a warning and returns (mv nil input-term state).

; More details:

; This book defines a utility similar to the proof-checker's bash command, but
; for use in the top-level loop.  The input term can be a user-level term,
; i.e., it need not be translated.  Thus this bash utility is given a term, and
; it returns an error triple (mv nil termlist state) where if no error occurs
; in the process, then termlist is the list of goals that ACL2 would get stuck
; on, if you were to attempt to prove the given term with only simplification,
; i.e., with a "Goal" hint of :do-not '(generalize eliminate-destructors
; fertilize eliminate-irrelevance) and with induction turned off.  Bash does
; all the normal simplification stuff, including forward chaining.  Use :hints
; to specify hints using the same syntax as for thm and defthm.  Use a non-nil
; value of :verbose if you want output, including the proof attempt.  The
; keyword values are not evaluated, so :hints could be of the form (("Goal
; ...)) but not '(("Goal" ...)).

; This book also includes a functional (non-macro) version of bash, bash-fn.
; At the end is a variant contributed by Dave Greve, bash-term-to-dnf, that
; returns a list of goals (implicitly conjoined) where each goal has the form
; (lit1 lit2 ... litk), for which the goal is equivalent to the negation of the
; conjunction of the liti.

; Examples:

#|
ACL2 !>(bash (equal (append x y) (append (car (cons x a)) z)))
 ((EQUAL (APPEND X Y) (APPEND X Z)))
ACL2 !>(bash (equal (car (cons x y)) x))
 NIL
ACL2 !>(bash (implies (true-listp x) (equal (append x y) zzz))
	     :hints (("Goal" :expand ((true-listp x)
				      (true-listp (cdr x))
				      (append x y)))))
 ((EQUAL Y ZZZ)
  (IMPLIES (AND (CONSP X)
                (CONSP (CDR X))
                (TRUE-LISTP (CDDR X)))
           (EQUAL (LIST* (CAR X)
                         (CADR X)
                         (APPEND (CDDR X) Y))
                  ZZZ))
  (IMPLIES (AND (CONSP X) (NOT (CDR X)))
           (EQUAL (CONS (CAR X) Y) ZZZ)))
ACL2 !>(bash-term-to-dnf
	'(implies (true-listp x) (equal (append x y) zzz))
	'(("Goal" :expand ((true-listp x)
			   (true-listp (cdr x))
			   (append x y))))
	nil nil state)
 (((EQUAL Y ZZZ))
  ((NOT (CONSP X))
   (NOT (CONSP (CDR X)))
   (NOT (TRUE-LISTP (CDDR X)))
   (EQUAL (LIST* (CAR X)
                 (CADR X)
                 (APPEND (CDDR X) Y))
          ZZZ))
  ((NOT (CONSP X))
   (CDR X)
   (EQUAL (CONS (CAR X) Y) ZZZ)))
ACL2 !>

.....

Here's how one might simplify hypotheses.

(defstub p1 (x) t)
(defstub p2 (x) t)
(defun p3 (x) (if (atom x) (p2 x) (p1 (car x))))
(include-book
 "misc/bash" :dir :system)

Then:

  ACL2 !>(bash (implies (and (p1 x) (p3 x))
			(hide aaa)))
   ((IMPLIES (AND (P1 X) (CONSP X) (P1 (CAR X)))
	     (HIDE AAA))
    (IMPLIES (AND (P1 X) (NOT (CONSP X)) (P2 X))
	     (HIDE AAA)))
  ACL2 !>

Here's how to do what I think you may want to do.

(defun strip-lastcar (lst)
  (if (atom lst)
      lst
    (cons (butlast (car lst) 1)
	  (strip-lastcar (cdr lst)))))

Then:

  ACL2 !>(er-let* ((clauses (bash-term-to-dnf
			     '(implies (and (p1 x) (p3 x))
				       (hide aaa))
			     nil nil t state)))
		  (mv nil (strip-lastcar clauses) state))
   (((NOT (P1 X))
     (NOT (CONSP X))
     (NOT (P1 (CAR X))))
    ((NOT (P1 X)) (CONSP X) (NOT (P2 X))))
  ACL2 !>

|# ; |

(in-package "ACL2")

(program)

(set-state-ok t)

(defun simplify-with-prover (form hints ctx state)

; This is patterned after (define-pc-primitive prove ...).

  (let ((wrld (w state))
        (ens (ens state))
        (name-tree 'bash))
    (er-let*
     ((thints (translate-hints
               name-tree

; Keep the following in sync with the definition of the proof-checker :bash
; command.

               (append
                *bash-skip-forcing-round-hints*
                (add-string-val-pair-to-string-val-alist
                 "Goal"
                 :do-not
                 (list 'quote '(generalize eliminate-destructors fertilize
                                           eliminate-irrelevance))
                 (add-string-val-pair-to-string-val-alist
                  "Goal"
                  :do-not-induct
                  name-tree
                  hints))
                (default-hints wrld))
               ctx wrld state))
      (tterm (translate form t t t ctx wrld state)))
     (mv-let (erp ttree state)
             (state-global-let*
              ((guard-checking-on nil)
               (in-prove-flg t))
              (pc-prove tterm form thints t ens wrld ctx state))
             (cond (erp (mv t nil state))
                   (t (let ((clauses (unproved-pc-prove-terms ttree)))
                        (cond ((and (eql (length clauses) 1)
                                    (eql (length (car clauses)) 1)
                                    (eql (caar clauses) tterm))
                               (mv 'no-change nil state))
                              (t (value clauses))))))))))

(defun bash-fn (form hints verbose ctx state)

; Keep this in sync with bash-term-to-dnf.

  (mv-let
   (erp clauses state)
   (cond (verbose
          (simplify-with-prover form hints ctx state))
         (t
          (state-global-let*
           ((inhibit-output-lst *valid-output-names*))
           (simplify-with-prover form hints ctx state))))
   (cond
    (erp
     (pprogn
      (warning$ ctx "bash"
                "Unable to simplify the input term~@0"
                (cond ((eq erp 'no-change)
                       ".")
                      (t (msg " because an error occurred.~@0"
                              (cond
                               (verbose "")
                               (t "  Try setting the verbose flag to t in ~
                                    order to see what is going on."))))))
      (value (list form))))
    (t
     (value (prettyify-clause-lst clauses (let*-abstractionp state) (w state)))))))

(defmacro bash (term &key verbose hints)
  `(bash-fn ',term ',hints ',verbose 'bash state))

; Dave Greve has contributed the following (only slightly modified here), to
; create a variant bash-term-to-dnf of bash-fn.  This example may suggest other
; variants; feel free to contribute yours to Matt Kaufmann,
; kaufmann@cs.utexas.edu.

(defun goals-to-cnf (goals)
  (cond ((endp goals) nil)
        (t (cons (append (access goal (car goals) :hyps)
                         (list (dumb-negate-lit (access goal (car goals)
                                                        :conc))))
                 (goals-to-cnf (cdr goals))))))

(defun untranslate-lst-lst (list iff-flg wrld)
  (cond
   ((endp list)
    nil)
   (t (cons (untranslate-lst (car list) iff-flg wrld)
	    (untranslate-lst-lst (cdr list) iff-flg wrld)))))

(defun bash-term-to-dnf (form hints verbose untranslate-flg state)

; Keep this in sync with bash-fn.

  (let ((ctx 'bash-term-to-dnf))
    (mv-let
     (erp clauses state)
     (cond (verbose
            (simplify-with-prover form hints ctx state))
           (t
            (state-global-let*
             ((gag-mode nil set-gag-mode-fn)
              (inhibit-output-lst *valid-output-names*)
              (print-clause-ids nil))
             (simplify-with-prover form hints ctx state))))
     (cond
      (erp
       (cond ((eq verbose :all)
              (pprogn
               (warning$ ctx "bash"
                         "Unable to simplify the input term~@0"
                         (cond ((eq erp 'no-change)
                                ".")
                               (t (msg " because an error occurred.~@0"
                                       (cond
                                        (verbose "")
                                        (t "  Try setting the verbose flag to ~
                                            t in order to see what is going ~
                                            on."))))))
               (value (list (list form)))))
             (t
              (value (list (list form))))))
      (untranslate-flg
       (value (untranslate-lst-lst clauses t (w state))))
      (t
       (value clauses))))))

