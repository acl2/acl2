; A tool to bind free vars by searching existing rules
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; This book (still in beta form, in my opinion) provides a way to tell ACL2
;; to bind the free variables of a rule by searching the conclusions of other
;; rules in the database.

;; See tests in bind-from-rules-tests.lisp.

;; TODO: would be nice to somehow figure out which vars are bound in the LHS and skip the :free annotations?
;; TODO: what about multiple matches, the first of which fails??
;; TODO: Exclude matches that introduce unhelpful free vars
;; TODO: Skip disabled rules

;example: search the LHS's of rules for matches of the following template
;(2d-bv-arrayp bytesize (:free numrows) (:free numcols) (:novar item))
;params with neither :free nor :novar are matched against the corresponding part of the rule using one-way-unify
;if any of those attempted matches fails, the template doesn't match the rule
;the :free means bind the given variable to whatever term appears in the rule
;the :novar means fail if the corresponding term in the rule is a variable, else call one-way-unify as normal
; :novar is used to prevent overly general rules from firing.  for example, if we want to know (integerp (foo x)) we may want to use rules that conclude (unsigned-byte-p 16 (foo x))
; but rules that simply conclude (unsigned-byte-p x) are probably too general..

;if there are no :free vars, this returns the empty alist which is intrepreted as failing. is that okay?

;a var shouldn't appear more than once in a template... - relax this?
;returns nil if no match, or an alist with the bindigs of the :free vars from the template

;fixme - do we really want the full one-way-unify?  a complicated function!
(defun try-to-match-template-with-lemma (template-args lemma-args alist)
  (declare (xargs :mode :program))
  (if (endp template-args)
      alist ;return the alist we've built up so far
    (let* ((template-arg (first template-args))
           (lemma-arg (first lemma-args)))
      (if (and (consp template-arg)
               (eq :free (car template-arg)))
          ;; we are matching a free variable in the template, so just return whatever term is in the rule
          (try-to-match-template-with-lemma (cdr template-args)
                                            (cdr lemma-args)
                                            (acons (cadr template-arg) ;strip off the :free
                                                   lemma-arg
                                                   alist
                                                   ))

        (if (and (consp template-arg)
                 (eq :novar (car template-arg)))
            (if (consp lemma-arg) ;this allows quoteps; is that what we want?
                (mv-let (success alist2)
                        (one-way-unify lemma-arg
                                       (cadr template-arg) ;strip off the :novar
                                       )
                        (declare (ignore alist2))
                        (if success
                            (try-to-match-template-with-lemma (cdr template-args) (cdr lemma-args) alist)
                          nil))
              ;; if lemma-arg is just a variable, don't match
              nil)
          ;;otherwise, just do the unify
          (mv-let (success alist2)
                  ;;try to instantiate the lemma-arg to get the template-arg:
                  ;;ex: the lemma is about (foo x).  the (instantiated) template is about (foo (bar (baz y)))
                  (one-way-unify lemma-arg template-arg)
                  (declare (ignore alist2))
                  (if success
                      (try-to-match-template-with-lemma (cdr template-args) (cdr lemma-args) alist)
                    nil)))))))

(defun match-template-from-lemmas (template-args lemmas negated-flg)
  (declare (xargs :mode :program))
  (if (endp lemmas)
      nil
    (let* ((lemma (first lemmas))
           (rhs (access rewrite-rule lemma :rhs)))
      ;;fixme check that the equiv is equal or iff?
      ;;fixme be more liberal here.  if negated-flag is false/true, the rhs should be allowed to be anything but *nil*/*t*?
      (if (not (equal rhs (if negated-flg *nil* *t*))) ;if the rhs isn't what it's supposed to be, skip this lemma
          (match-template-from-lemmas template-args (rest lemmas) negated-flg)
        (let* ((lhs (access rewrite-rule lemma :lhs)) ;what about congruences other than equal?
               (lhs-args (cdr lhs))                   ;hope this is okay
               (possible-match (try-to-match-template-with-lemma template-args lhs-args nil)))
          (or possible-match
              (match-template-from-lemmas template-args (rest lemmas) negated-flg)))))))

;template must be a function call - fixme rename the template since it has been instantiated
;i think this must take both mfc and state (even though it doesn't use mfc)
(defun bind-free-vars-from-rules (template mfc state)
  (declare (xargs :mode :program
                  :stobjs state)
           (ignore mfc))
  (let* ((negated-flg (and (consp template) (eq 'not (ffn-symb template))))
         (template (if negated-flg (second template) template))
         (template-fn (car template))
         (template-args (cdr template))
         ;;get the lemmas for the function symbol (how can we get only the enabled ones?)
         ;;what about rules with multiple conjuncts?
         (lemmas (getprop template-fn 'lemmas nil 'current-acl2-world (w state))))
    (match-template-from-lemmas template-args lemmas negated-flg)))

(mutual-recursion
 (defun strip-frees-and-novars (term)
   (if (atom term)
       term
     (if (quotep term)
         term
       (let* ((fn (ffn-symb term)))
         (if (or (eq fn ':free) (eq fn ':novar))
             (second term)
           (cons fn (strip-frees-and-novars-lst (fargs term))))))))

 (defun strip-frees-and-novars-lst (terms)
   (if (endp terms)
       nil
     (cons (strip-frees-and-novars (car terms))
           (strip-frees-and-novars-lst (cdr terms))))))


;; ;what is the purpose of this step?  is it to avoid errors about :free and :novar not being functions?
;; i guess it quotes vars inside :free and leaves the others for bind-free to instantiate?
(mutual-recursion
 (defun translate-template (term)
   (if (atom term)
       term
     (if (quotep term)
         `',term ;initially i wasn't quoting this term
       (let* ((fn (ffn-symb term)))
         (if (eq fn ':free)
             (list 'cons `',fn (list 'cons `',(second term) ''nil)) ;we quote the arg to a :free (this used to quote a var inside novar, but that was a mistake)
           (if nil ;(eq fn ':novar)
               (list 'cons `',fn (list 'cons `',(second term) ''nil))
             (list 'cons `',fn (translate-template-lst (cdr term)))))))))

 (defun translate-template-lst (terms)
   (if (endp terms)
       ''nil
     (list 'cons (translate-template (car terms))
           (translate-template-lst (cdr terms))))))


;ffixme can the template args be trees?  seems to work?
(defun bind-from-rules-fn (template)
  `(and (bind-free (bind-free-vars-from-rules
                    ,(translate-template template)
                    ;; (cons ',(car template) ,(translate-template-args (cdr template)))
                    mfc
                    state))
        ;;        (,(car template) ,@(strip-frees-and-novars-from-template-args (cdr template)))
        ,(strip-frees-and-novars template)
        ))

(defmacro bind-from-rules (template)
  (bind-from-rules-fn template))
