; Copyright (C) 2006  University of Texas at Austin

; This program is free software; you can redistribute it and/or modify it under
; the terms of Version 2 of the GNU General Public License as published by the
; Free Software Foundation.

; This program is distributed in the hope that it will be useful,
; but WITHOUT ANY WARRANTY; without even the implied warranty of
; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
; GNU General Public License for more details.

; You should have received a copy of the GNU General Public License
; along with this program; if not, write to the Free Software
; Foundation, Inc., 675 Mass Ave, Cambridge, MA 02139, USA.

; Written by:  Matt Kaufmann
; email:       Kaufmann@cs.utexas.edu
; Department of Computer Science
; University of Texas at Austin
; Austin, TX 78701 U.S.A.

; October, 2006

; [Note added by Matt Kaufmann on May 5, 2012: I believe that this book, in
; John Erickson's books/workshops/2007/erickson/bprove/, was based on a version
; of my books/misc/bash.lisp book.  I see a modification to
; simplify-with-prover that comments out fertilize and eliminate-destructors.
; I don't know if anything else was modified, but for now I'll just keep this
; book as it currently stands rather than trying to bring it up to date with
; books/misc/bash.lisp.]

; In a nutshell:

; If you submit (bash term), then the result is a list of goals to which ACL2
; can simplify term when attempting to prove it.  (In particular, if the result
; is nil, then ACL2 can prove term.)  More accurately: (bash term) returns (mv
; erp val state), where: erp is nil unless there is an error; and val is a list
; of terms, in untranslated (user-level) form, whose provability implies the
; provability of the input term.  If ACL2 cannot simplify the input term, then
; there is an error, i.e., erp is not nil.

; More details:

; This book defines a utility similar to the proof-builder's bash command, but
; for use in the top-level loop.  The input term can be a user-level term,
; i.e., it need not be translated.  Thus this bash utility is given a term, and
; it returns an error triple (mv erp termlist state) where if erp is not nil,
; then termlist is the list of goals that ACL2 would get stuck on, if you were
; to attempt to prove the given term with only simplification, i.e., with a
; "Goal" hint of :do-not '(generalize eliminate-destructors fertilize
; eliminate-irrelevance) and with induction turned off.  Bash does all the
; normal simplification stuff, including forward chaining.  Use :hints to
; specify hints using the same syntax as for thm and defthm.  Use a non-nil
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
	nil state)
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
|# ; |

(in-package "ACL2")

(program)

(set-state-ok t)

; The following appears in the ACL2 source code, but is included temporarily
; for a few days pending some users updating to a sufficiently recent
; development snapshot.
(defun unproved-pc-prove-clauses (ttree)
  (reverse-strip-cdrs (tagged-objects :bye ttree) nil))

(defun simplify-with-prover (form hints ctx state)

; This is patterned after (define-pc-primitive prove ...).

  (let ((wrld (w state))
        (ens (ens state))
        (name-tree 'bash))
    (er-let*
     ((thints (translate-hints
               name-tree

; Keep the following in sync with the definition of the proof-builder :bash
; command.

               (append
                *bash-skip-forcing-round-hints*
                (add-string-val-pair-to-string-val-alist
                 "Goal"
                 :do-not
                 (list 'quote '(generalize ;eliminate-destructors
				;fertilize
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
             (pc-prove tterm form thints t ens wrld ctx state)
             (cond (erp (mv t nil state))
                   (t (let ((clauses (unproved-pc-prove-clauses ttree)))
                        (cond ((and (eql (length clauses) 1)
                                    (eql (length (car clauses)) 1)
                                    (eql (caar clauses) tterm))
                               (mv 'no-change nil state))
                              (t (value clauses))))))))))

(defun simplify-with-prover2 (form hints ctx state)

; This is patterned after (define-pc-primitive prove ...).

  (let ((wrld (w state))
        (ens (ens state))
        (name-tree 'bash))
    (er-let*
     ((thints (translate-hints
               name-tree

; Keep the following in sync with the definition of the proof-builder :bash
; command.

               (append
                *bash-skip-forcing-round-hints*
                (add-string-val-pair-to-string-val-alist
                 "Goal"
                 :do-not
                 (list 'quote '(generalize eliminate-destructors
				;fertilize
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
             (pc-prove tterm form thints t ens wrld ctx state)
             (cond (erp (mv t nil state))
                   (t (let ((clauses (unproved-pc-prove-clauses ttree)))
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

(defun bash-term-to-dnf (form hints verbose state)

; Keep this in sync with bash-fn.

  (let ((ctx 'bash-term-to-dnf))
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
        (value (list (list form)))))
      (t
       (value clauses))))))


;no dtor or fertilize
(defun bash-term-to-dnf2 (form hints verbose state)

; Keep this in sync with bash-fn.

  (let ((ctx 'bash-term-to-dnf))
    (mv-let
     (erp clauses state)
     (cond (verbose
            (simplify-with-prover2 form hints ctx state))
           (t
            (state-global-let*
             ((inhibit-output-lst *valid-output-names*))
             (simplify-with-prover2 form hints ctx state))))
     (cond
      (erp
       (pprogn
        (value (list (list form)))))
      (t
       (value clauses))))))
