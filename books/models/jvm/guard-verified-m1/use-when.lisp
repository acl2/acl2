; The Use-When Event
; J Strother Moore
; March, 2013

; (certify-book "use-when")

; This book is adds a default computed hint that automatically adds an instance
; of a named theorem to any goal in which certain annotated patterns appear.
; Each pattern must be fully translated.  Each pattern must be annotated with
; one of the three labels :hyp, :lit, or :subterm, which specify whether the
; pattern is to occur as a hypothesis, a literal, or any subterm.  (We negate
; :hyp patterns and then look for a :lit occurrence.)  The patterns are matched
; sequentially, each extending the substitution produced by the last match.  So
; if asked to match

; patterns:  (f x y) (g y z)

; goal:      (FOO (f A B) (f C D) (g D E))

; we would use the substitution ((x . C) (y . D) (z . E))

; As an example of need for this event, suppose we've defined instructionp and programp
; so that a programp is a list of elements satisfying instructionp.  That is,
; (programp lst) is (forall e \in lst : (instructionp e)).  Then this is a nice
; lemma:

; (defthm instructionp-nth
;   (implies (and (programp lst)
;                 (natp pc)
;                 (< pc (len lst)))
;            (instructionp (nth pc lst))))

; But if instructionp splits into many cases, e.g., one for each family or type
; of instruction, then this lemma is of little use as a :rewrite or
; :forward-chaining rule when executing, say, an ILOAD instruction.  Instead,
; we need to add (instructionp ...) to the hypotheses as soon as we realize we
; are looking at the (nth pc lst) where lst is a programp.  That way, the
; rewriter can expand (instructionp ...) and pick out what we know for ILOAD
; instructions.

; To cause this behavior we could use this event:

;  (use-when instructionp-nth
;            ((:hyp (programp lst))
;             (:subterm (nth pc lst)))
;            nil)

; The last argument to use-when is the initial substitution.  For example, if
; we wanted to restrict this behavior to the case where lst was always bound to
; (program s), we could use:

;  (use-when instructionp-nth
;            ((:hyp (programp lst))
;             (:subterm (nth pc lst)))
;            ((lst . (program s))))

; We can also use the initial alist to specify free vars.

(in-package "ACL2")

(program)

; The following is based on code taken from :DOC using-computed-hints-4.  Here
; we find all instances of pat (extending alist) in term and accumulate the
; resulting substitutions into ans.  The value is a list of alists.

(mutual-recursion

 (defun find-all-subterm-instances (pat term alist ans)
   (mv-let
    (instancep alist)
    (one-way-unify1 pat term alist)

; Note that we exploit the fact that one-way-unify1 is a ``no-change loser''
; meaning that if instancep is nil, the returned alist is the initial alist
; (not some intermediate result formed before we detected the impossibility of
; a match here).

    (let ((ans (if instancep (add-to-set-equal alist ans) ans)))
      (cond
       ((variablep term) ans)
       ((fquotep term) ans)
       (t ; We treat lambda applications just like other function applications.
        (find-all-subterm-instances-list pat (fargs term) alist ans))))))

 (defun find-all-subterm-instances-list (pat list-of-terms alist ans)
   (cond
    ((endp list-of-terms) ans)
    (t (find-all-subterm-instances
        pat
        (car list-of-terms)
        alist
        (find-all-subterm-instances-list pat
                                         (cdr list-of-terms)
                                         alist
                                         ans))))))

(defun find-all-element-instances (pat list-of-terms alist ans)
  (cond ((endp list-of-terms) ans)
        (t (mv-let (instancep alist1)
                   (one-way-unify1 pat (car list-of-terms) alist)
                   (find-all-element-instances pat (cdr list-of-terms) alist
                                               (if instancep
                                                   (add-to-set-equal alist1 ans)
                                                   ans))))))

(mutual-recursion

 (defun find-all-annotated-pattern-instances (apats clause alist ans)
   (cond ((endp apats) (add-to-set-equal alist ans))
         ((or (eq (car (car apats)) :hyp)
              (eq (car (car apats)) :lit))
          (let* ((lit (if (eq (car (car apats)) :hyp)
                          (dumb-negate-lit (cadr (car apats)))
                          (cadr (car apats))))
                 (ans1 (find-all-element-instances lit clause alist nil)))
            (loop-find-all-annotated-pattern-instances (cdr apats) clause ans1 ans)))
         (t ; find subterms
          (let* ((term (cadr (car apats)))
                 (ans1 (find-all-subterm-instances term clause alist nil)))
            (loop-find-all-annotated-pattern-instances (cdr apats) clause ans1 ans)))))

 (defun loop-find-all-annotated-pattern-instances (apats clause alists ans)
   (cond ((endp alists) ans)
         (t (loop-find-all-annotated-pattern-instances
             apats clause (cdr alists)
             (find-all-annotated-pattern-instances apats clause (car alists) ans))))))

; We now turn our attention to converting a list of substitutions into a list
; of lemma instances, each of the form

; (:INSTANCE name (var1 term1) ... (vark termk))

; as written in :use hints. In the code shown above, substitutions are lists of
; pairs of the form (var . term), but in lemma instances we must write
; ``doublets.'' So here we show how to convert from one to the other:

(defun pairs-to-doublets (alist)
  (cond ((null alist) nil)
        (t (cons (list (caar alist) (cdar alist))
                 (pairs-to-doublets (cdr alist))))))

(defun all-lemma-instances (name alists)
  (cond ((endp alists) nil)
        (t (cons `(:instance ,name ,@(pairs-to-doublets (car alists)))
                 (all-lemma-instances name (cdr alists))))))

(defun use-when-fn (name annotated-patterns alist clause)
  (let ((alists
         (loop-find-all-annotated-pattern-instances
          annotated-patterns clause (list alist) nil)))
    (if (null alists)
        nil
        `(:USE ,(all-lemma-instances name alists)))))

(defun flat-annotationsp (lst)
  (cond ((atom lst) (equal lst nil))
        ((atom (cdr lst)) nil)
        ((member (car lst) '(:hyp :lit :subterm))
         (flat-annotationsp (cddr lst)))
        (t nil)))

(defun flat-annotations-to-doublets (lst)
  (cond ((endp lst) nil)
        (t (cons (list (car lst) (cadr lst))
                 (flat-annotations-to-doublets (cddr lst))))))

(defmacro use-when (name alist &rest flat-apats)
  (declare (xargs :guard (and (symbolp name)
                              (alistp alist)
                              (flat-annotationsp flat-apats))))
  `(add-default-hints
    '((use-when-fn ',name ',(flat-annotations-to-doublets flat-apats) ',alist clause))))


