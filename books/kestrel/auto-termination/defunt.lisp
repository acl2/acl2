; Copyright (C) 2018, Regents of the University of Texas
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; See the README file in this directory for a brief summary of the algorithms,
; and see :doc defunt.

(in-package "ACL2")

(include-book "termination-database-utilities")
(include-book "injections")
(include-book "std/util/bstar" :dir :system)
(include-book "xdoc/top" :dir :system)

(deftheory auto-termination-fns
  *auto-termination-fns*)

(program)

(defconst *td-candidates-book*
  '(:system . "system/termination/td-cands.lisp"))

(defun subsumes-t (cl1 cl2)

; Cl1 and cl2 are termination clause-sets, which are disjunctions whose last
; literal is of the form (wf-rel measure/s measure), and whose other literals
; are the negated tests leading to the recursive call that generated this
; inequality.  We are interested in whether cl1 subsumes cl2, and we are
; willing to have a few false negatives in return for efficiency.  So we insist
; that the last literals, which are the measure inequalities, match up.

  (mv-let (ans alist)
    (one-way-unify1 (car (last cl1)) (car (last cl2)) nil)
    (cond ((null ans)
           nil)
          (t (subsumes!-rec (butlast cl1 1) (butlast cl2 1) alist)))))

(defun some-member-subsumes-t (cl-set cl)

; This variant of ACL2 source function some-member-subsumes is suitable for
; clauses whose last literal is of the form (< measure/s measure); thus, it
; calls subsumes-t.

  (cond ((null cl-set) nil)
        (t (or (subsumes-t (car cl-set) cl)
               (some-member-subsumes-t (cdr cl-set) cl)))))

(defun clause-set-subsumes-t (cl-set1 cl-set2)

; This variant of ACL2 source function clause-set-subsumes returns (mv REMOVED
; REMAINING), where REMOVED is the set of clauses in cl-set2 that are subsumed
; by some clause in cl-set1, and REMAINING is the set of clauses in cl-set2
; that are not.  If REMOVED is nil then REMAINING is eq to cl-set2.

  (cond ((null cl-set2) (mv nil nil))
        (t (b* ((car-success (some-member-subsumes-t cl-set1 (car cl-set2)))
                ((mv removed rest)
                 (clause-set-subsumes-t cl-set1 (cdr cl-set2))))
             (cond
              (car-success (mv (cons (car cl-set2) removed) rest))
              (removed (mv removed (cons (car cl-set2) rest)))
              (t (mv nil cl-set2)))))))

(defun clause-set-subsumes-t-top (mp-clause-p cl-set1 cl-set2)

; Mp-clause-p is true when the first clause in cl-set2 is the one asserting
; that the measure satisfies mp, which we call the "mp clause" below.

; This function is a variant of clause-set-subsumes-t that takes into account
; the :mp field of the justification of the function that generated cl-set1
; (and would ultimately generate cl-set2).  In particular, when mp is not t
; then it doesn't give any credit to subsumption of the mp clause, like ((O-P
; (ACL2-COUNT X))).  Such subsumption is likely to be very common so we insist
; that at least one other clause in cl-set1 is subsumed.

  (cond
   ((not mp-clause-p) ; cl-set2 has no mp clause
    (clause-set-subsumes-t cl-set1 cl-set2))
   ((subsumes nil (car cl-set1) (car cl-set2) nil) ; always (same measure)?
    (mv-let (removed cs)
      (clause-set-subsumes-t (cdr cl-set1) (cdr cl-set2))
      (cond (removed (mv (cons (car cl-set2) removed) cs))
            (t

 ; Subsumption for the mp clause will likely (or perhaps necessarily?) hold
 ; when any other clause is subsumed.  So we look for some other cl-set1 to
 ; subsume the mp clause of cl-set2, simply to reduce the number of previous
 ; termination theorems we ultimately use.

             (mv nil cl-set2)))))
   (t (mv nil cl-set2))))

(defun member-book-roots-alist-entry-lst (book-rep roots-alist-entry-lst)
  (cond
   ((endp roots-alist-entry-lst) nil)
   (t (or (equal book-rep
                 (access roots-alist-entry (car roots-alist-entry-lst)
                         :book))
          (member-book-roots-alist-entry-lst book-rep
                                             (cdr roots-alist-entry-lst))))))

(defun roots-alist-known-entry (roots-alist wrld roots-alist-entry-lst)

; This returns a roots-alist-entry record in roots-alist for which the function
; symbol of the record is known in wrld, or else its book is the book of an
; entry in roots-alist-entry-lst.

  (cond ((endp roots-alist) nil)
        ((or (eq (access roots-alist-entry (car roots-alist)
                         :book)
                 nil) ; optimization
             (function-symbolp (access roots-alist-entry (car roots-alist)
                                       :root)
                               wrld)
             (member-book-roots-alist-entry-lst
              (access roots-alist-entry (car roots-alist) :book)
              roots-alist-entry-lst))
         (car roots-alist))
        (t (roots-alist-known-entry (cdr roots-alist)
                                    wrld
                                    roots-alist-entry-lst))))

(defmacro defunt-note (msg &optional skip-header)

; This macro pops a surrounding with-output laid down by defunt that suppresses
; output.  The header "*Defunt note*:" is laid down, followed by a newline,
; unless skip-header is true.  Then msg is printed.

  `(make-event
    (er-progn
     (with-output!
       :stack :pop
       (pprogn (io? prove nil state ()
                    (fms "~s0~@1~|"
                         (list (cons #\0
                                     ,(if skip-header
                                          ""
                                        "*Defunt note*: "))
                               (cons #\1 ,msg))
                         (proofs-co state) state nil))
               (value nil)))
     (value '(value-triple :invisible)))))

(defun td-candidate-event-lemmas (name fn-clauses-alist)

; Name is a function symbol.  Each pair in fn-clauses-alist associates a
; function symbol, root, with a triple (cons arity (cons root-clause-set
; removed-clause-set)), where: arity is the arity of root; root-clause-set is
; the normalized termination clause-set for root; and removed-clause-set is a
; set of clauses from the normalized termination clause-set of name, each of
; which is subsumed by a clause in root-clause-set.  To understand what this
; generates, you can trace this function on examples in defunt-tests.lisp.

  (cond
   ((endp fn-clauses-alist) (mv nil nil))
   (t (b* (((mv lemmas names)
            (td-candidate-event-lemmas name (cdr fn-clauses-alist)))
           (tuple (car fn-clauses-alist))
           (root (car tuple))
           ((cons arity (cons root-clause-set removed-clause-set))
            (cdr tuple))
           (name1 (packn (list name "-TERMINATION-LEMMA-1-" root)))
           (name2 (packn (list name "-TERMINATION-LEMMA-2-" root)))
           (s1-n (termify-clause-set root-clause-set))
           (s2-n (termify-clause-set removed-clause-set)))
        (mv `((local
               (defthm ,name1
                 ,s1-n
                 :hints (("Goal"
                          :use
                          ((:termination-theorem
                            ,root
                            ((,root
                              ,(td-stub-name arity root)))))
                          :in-theory (theory 'auto-termination-fns)))))
              (local
               (defthm ,name2
                 ,s2-n
                 :hints (("Goal" :by ,name1))))
              ,@lemmas)
            (cons name2 names))))))

(defun include-sysfile-form (sysfile)
  (if (sysfile-p sysfile)
      `(include-book ,(sysfile-filename sysfile)
                     :dir :system)
    `(include-book ,sysfile)))

(defun td-candidate-event-books (roots-alist-entry-lst)
  (cond
   ((endp roots-alist-entry-lst)
    '((defunt-note (msg "Concluded local include-books."))))
   (t
    (let* ((entry (car roots-alist-entry-lst))
           (b (access roots-alist-entry entry :book))
           (event `(local ,(include-sysfile-form b))))
      `((defunt-note (msg "Evaluating ~x0~|to define function ~x1."
                          ',event
                          ',(access roots-alist-entry entry :root)))
        ,event
        ,@(td-candidate-event-books (cdr roots-alist-entry-lst)))))))

(defun td-candidate-event-form (name formals declares body
                                     formals-len
                                     new-cl-list-unnorm
                                     fn-clauses-alist
                                     rel new-measure wrld allp)

; We return an event that should admit the definition of name.  Each pair in
; fn-clauses-alist associates a function symbol, root, with a triple (cons
; arity (cons root-clause-set removed-clause-set)), where: arity is the arity
; of root; root-clause-set is the normalized termination clause-set for root;
; and removed-clause-set is a set of clauses from the normalized termination
; clause-set of name, each of which is subsumed by a clause in root-clause-set.
; To understand what this generates, you can trace this function on examples in
; defunt-tests.lisp.

  (b* (((mv lemmas lemma-names)
        (td-candidate-event-lemmas name fn-clauses-alist))
       (rel-defined-p (or (eq rel 'o<) ; optimization
                          (function-symbolp rel wrld)))
       (td-wf-rel-alist
        (unquote (getpropc '*td-wf-rel-alist* 'const nil wrld)))
       (rel-sysfile (and (not rel-defined-p)
                         (cdr (assoc-eq rel td-wf-rel-alist))))
       (- (or rel-defined-p
              rel-sysfile
              (er hard 'defunt
                  "The well-founded relation ~x0 is, suprisingly, neither ~
                   defined nor mentioned in the alist, ~x1.  This could be an ~
                   implementation error."
                  rel '*td-wf-rel-alist*)))
       (books (and (consp allp) ; a list of roots-alist-entry records
                   (td-candidate-event-books allp)))
       (name3 (packn (list name "-TERMINATION-LEMMA-3")))
       (defun-form
         `(defun ,name ,formals
            (declare
             (xargs ,@(and (not (eq rel
                                    (default-well-founded-relation wrld)))
                           `(:well-founded-relation ,rel))
                    :measure ,new-measure
                    :hints
                    (("Goal"
                      :by
                      (:functional-instance
                       ,name3
                       (,(td-stub-name formals-len name)
                        ,name))))))
            ,@declares
            ,body))
       (defun-forms
         (if (function-symbolp rel wrld)
             (list defun-form)
           `((local ,defun-form)
             (defun ,name ,formals
               (declare
                (xargs :well-founded-relation ,rel
                       :measure (:? ,@(all-vars new-measure))))
               ,@declares
               ,body))))
       (encap-form
        `(encapsulate
           ()
           (defunt-note (msg "Using termination theorem~#0~[~/s~] for ~&0."
                             ',(strip-cars fn-clauses-alist)))
           ,@books
           ,@lemmas
           (local
            (defthm ,name3
              ,(termify-clause-set new-cl-list-unnorm)
              :hints (("Goal" :use ,lemma-names
                       :in-theory (theory 'auto-termination-fns)))))
           ,@defun-forms))
       (include-sysfile-lst
        (and (not rel-defined-p)
             (let ((include-sysfile-form
                    (include-sysfile-form rel-sysfile)))
               (list `(defunt-note
                        (msg "Executing the following form in order to ~
                                 define the well-founded relation, ~x0:~|~x1"
                             ',rel ',include-sysfile-form))
                     include-sysfile-form)))))
    `(progn ,@include-sysfile-lst
            ,encap-form
            (defunt-note "" t)
            (value-triple ',name))))

(defun non-subsumed-clauses (td-cand new-clause-list mp rel top-p wrld allp)

; Allp is Boolean or else a list of roots-alist-entry records.  The idea is to
; take the given td-candidate record, td-cand, and see if its :clause-list
; subsumes at least one clause in new-clause-list (which is a subset of the
; normalized termination clause-list for a proposed new definition).  If so,
; then we return (mv root arity old-clause-list removed-cl-list rest-cl-list
; allp2), where: root, arity, and old-clause-list are an old function symbol,
; its arity, and its normalized termination clause-list, resp.; remove-cl-list
; is the set of clauses in new-clause-list that are each subsumed by at least
; one clause in old-clause-list; rest-cl-list is what's left in new-clause-list
; that's not subsumed; and allp2 extends allp in the following sense.  If allp
; is nil then allp2 is nil.  If allp is a cons then it is a list of
; roots-alist-entry records for candidates that have already contributed such
; remove-cl-list lists because the function symbol was not yet defined and
; hence a book needs to be included from that record; in this case, allp2
; extends allp if necessary, i.e., because the new root is not yet defined.  If
; allp is t then allp2 consists of the single new record.

  (b* ((roots-alist (access td-candidate td-cand :roots-alist))
       (entry (roots-alist-known-entry roots-alist wrld nil))
       ((when (and (null entry) (not allp)))
        (mv nil nil nil nil new-clause-list allp))
       (entry
        (or entry ; else allp is t or a list of sysfiles
            (and (consp allp)
                 (roots-alist-known-entry roots-alist wrld allp))))
       ((mv entry allp2)
        (cond
         (entry (mv entry allp))
         ((eq allp t) ; then start accumulating sysfiles
          (mv (car roots-alist)
              (cons (car roots-alist) nil)))
         (t
          (mv (car roots-alist)
              (cons (car roots-alist) nil)))))
       (old-clause-list (access td-candidate td-cand :clause-list))
       ((mv removed-cl-list rest-cl-list)
        (clause-set-subsumes-t-top
         (and top-p (not (eq mp t)))
         old-clause-list
         new-clause-list)))
    (cond
     ((null removed-cl-list)
      (assert$ (equal new-clause-list rest-cl-list) ; in fact, eq
               (mv nil nil nil nil new-clause-list allp)))
     (t
      (b* ((root (access roots-alist-entry entry :root))
           (old-clause-list
            (if (eq root
                    (access roots-alist-entry (car roots-alist) :root))
                old-clause-list
              (let ((root-just (getpropc root 'justification nil wrld)))
                (td-cl-lst (list root)
                           (list (body root nil wrld))
                           (list (access justification root-just
                                         :ruler-extenders))
                           (acons root
                                  (access justification root-just :measure)
                                  nil)
                           mp rel nil wrld)))))
        (mv root
            (access roots-alist-entry entry :arity)
            old-clause-list removed-cl-list rest-cl-list
            allp2))))))

(defun td-candidate-event-2 (new-measure rest-clause-set
                                         clause-set-unnorm mp rel td-cand-lst
                                         names formals declares body
                                         wrld fn-clauses-alist allp)

; We are in the midst of trying to subsume clauses from the normalized
; termination clause-set for a proposed definition, `(defun ,(car names)
; (declare (xargs :measure ,new-measure)) ,formals ,@declares ,body), where mp
; and rel are the measure predicate and the well-founded relation.  The other
; formals are as follows.

; clause-set-unnorm:
; The termination clause-set (not normalized) for the proposed definition using
; new-measure, mp, and rel

; rest-clause-set, removed-clauses, fn-clauses-alist:
; Rest-clause-set is a list of (root arity . removed-clauses) triples, into
; which we accumulate each function symbol, root, with the indicated arity,
; whose normalized termination theorem subsumes the subset, removed-clauses, of
; the suggested normalized termination clauses, C for the new function.
; Rest-clause-set is what is left of C after removing removed-clauses.

; allp:
; a Boolean or else a list of roots-alist-entry records

; td-cand-lst:
; a list of td-candidate records for the given mp and rel

; We recur through td-cand-lst, attempting to subsume more clauses from the
; normalized termination clauses for the new function, as per the discussion
; above.

  (cond
   ((endp td-cand-lst) nil)
   (t (b* (((mv root arity root-clause-set removed-clause-set rest-clause-set
                allp)
            (non-subsumed-clauses (car td-cand-lst) rest-clause-set mp rel
                                  (null fn-clauses-alist) wrld allp))
           (fn-clauses-alist
            (if root
                (acons root
                       (cons arity (cons root-clause-set removed-clause-set))
                       fn-clauses-alist)
              fn-clauses-alist)))
        (cond
         ((null rest-clause-set)
          (td-candidate-event-form (car names)
                                   formals declares body (length formals)
                                   clause-set-unnorm fn-clauses-alist
                                   rel new-measure wrld allp))
         (t (td-candidate-event-2 new-measure rest-clause-set
                                  clause-set-unnorm mp rel (cdr td-cand-lst)
                                  names formals declares body
                                  wrld fn-clauses-alist allp)))))))

(defun td-candidate-event-1 (injections old-measure mp rel
                                        td-cand-lst names formals declares
                                        body tbodies ruler-extenders-lst wrld
                                        allp)

; Allp is nil in the first pass, where we traffic only in known function
; symbols, but is t in the second pass, where we are allowed to generate
; include-book forms.  We recur through the given set of injections from the
; variables of old-measure into the indicated formals of the function symbol of
; the proposed definition, `(defun ,(car names) (declare (xargs :measure
; ,new-measure :ruler-extenders ,(car ruler-extenders-lst))) ,formals
; ,@declares ,body), where mp and rel are the measure predicate and the
; well-founded relation, and tbodies is a one-element list containing the
; translation of body.

  (cond
   ((endp injections) nil)
   (t
    (or (b* ((new-measure (sublis-var (car injections) old-measure))
             (clause-set
              (termination-theorem-clauses
               nil nil ; loop$-recursion-checkedp and loop$-recursion value
               names
               nil ; arglist irrelevant when loop$-recursion-checkedp = nil
               tbodies
               (acons (car names) new-measure nil)
               mp rel
               ruler-extenders-lst
               wrld))
             (new-cl-list-unnormalized
              (td-replace-fn-cl-lst (car names) clause-set wrld))
             (new-cl-list-normalized
              (norm-clause-lst
               (td-remove-lambdas-cl-lst new-cl-list-unnormalized))))
          (td-candidate-event-2 new-measure
                                new-cl-list-normalized
                                new-cl-list-unnormalized
                                mp rel
                                td-cand-lst names formals declares body
                                wrld nil allp))
        (td-candidate-event-1 (cdr injections)
                              old-measure mp rel
                              td-cand-lst names formals
                              declares body tbodies ruler-extenders-lst
                              wrld allp)))))

(defun td-candidate-event-0 (td-cand-alist names formals formals-len declares
                                           body tbodies ruler-extenders wrld
                                           allp)

; Allp is nil in the first pass, where we traffic only in known function
; symbols, but is t in the second pass, where we are allowed to generate
; include-book forms.  See the high-level algorithm explanation in README.

  (cond
   ((endp td-cand-alist) nil)
   (t (or (b* ((just (caar td-cand-alist))
               (subset (access justification just :subset))
               (subset-len (length subset))
               ((when (< formals-len subset-len))
                nil)
               ((when (too-many-embeddings subset-len formals-len))

; We could maybe still check a few embeddings, or at least the obvious one if
; the formals have the same length.  But we don't, for now.

                nil)
               (injections (injections subset formals)))
            (td-candidate-event-1 injections
                                  (access justification just :measure)
                                  (access justification just :mp)
                                  (access justification just :rel)
                                  (cdar td-cand-alist) ; candidates
                                  names formals declares body
                                  tbodies
                                  (list (if (eq ruler-extenders :none)
                                            (access justification just :ruler-extenders)
                                          ruler-extenders))
                                  wrld allp))
          (td-candidate-event-0 (cdr td-cand-alist) names formals formals-len
                                declares body tbodies ruler-extenders wrld
                                allp)))))

(defun td-candidate-event (td-cand-alist names formals formals-len declares
                                         body tbodies ruler-extenders wrld)

; We make two passes (if necessary) through our event-generation algorithm, as
; explained in the high-level algorithm discussion in README.

  (or (td-candidate-event-0 td-cand-alist names formals formals-len declares
                            body tbodies ruler-extenders wrld nil)
      (td-candidate-event-0 td-cand-alist names formals formals-len declares
                            body tbodies ruler-extenders wrld t)))

(defun create-defunt (args error-p ctx state)

; This function creates a make-event expansion on behalf of a defunt form with
; the indicated args.  Error-p is generally t, but can be nil, in which case
; failure results in (value nil) instead of a soft error.

  (declare (xargs :stobjs state))
  (b* ((name (car args))
       (formals (cadr args))
       (declares (butlast (cddr args) 1))
       (body (car (last args)))
       (live-w (w state))
       ((er td-cand-alist)
        (let ((val (unquote (getpropc '*td-candidates* 'const nil live-w))))
          (if val
              (value val)
            (er soft ctx
                "In order to use ~x0, please first evaluate:~|~x1"
                'defunt
                (include-sysfile-form *td-candidates-book*)))))
       ((er edcls)
        (collect-declarations declares
                              formals 'defuns state ctx))
       ((er ruler-extenders)
        (get-ruler-extenders1 *no-ruler-extenders*
                              edcls
                              *no-ruler-extenders*
                              ctx live-w state))
       (new-w (putprop name 'formals formals live-w))
       ((er tbody)
        (translate body t t nil ctx new-w state))
       (event
        (td-candidate-event td-cand-alist (list name)
                            formals (length formals) declares body (list tbody)
                            ruler-extenders new-w)))
    (cond (event (value event))
          (error-p (er soft ctx
                       "Unable to find previous termination theorem!"))
          (t (value nil)))))

(defmacro defunt (&rest args)
  `(with-output
     :off :all
     :on error
     :gag-mode nil
     :stack :push
     (make-event (create-defunt ',args t '(defunt . ,(car args)) state)
                 :on-behalf-of :quiet!)))

(defxdoc defunt
  :parents (kestrel-utilities)
  :short "Variant of @(tsee defun) that re-uses existing termination theorems
 automatically."
  :long "
 @({
 General Form:

 (defunt fn (var1 ... varn) doc-string dcl ... dcl body)
 })

 <p>where the arguments are the same as for @(tsee defun), but without any
 @(tsee xargs) that specify @(':measure'), @(':hints'), or
 @(':well-founded-relation').  Those will be inserted automatically into a
 corresponding @('defun') event, as necessary, by using a database of
 termination theorems from the @(see community-books).</p>

 <p>To use this utility, first evaluate the following event.</p>

 @({
 (include-book \"kestrel/auto-termination/defunt-top\" :dir :system)
 })

 <p>Examples may be found in the community book,
 @('books/kestrel/auto-termination/defunt-tests.lisp').  Here is a log showing
 one such example.</p>

 @({
 ACL2 !>(defunt f0 (x y)
          (if (endp x)
              y
            (list (f0 (cddr x) (cons 23 y)) 100)))

 *Defunt note*: Using termination theorem for EVENS.

  F0
 ACL2 !>:pe f0
            2:x(DEFUNT F0 (X Y) ...)
               \
 >L             (DEFUN
                 F0 (X Y)
                 (DECLARE
                  (XARGS
                     :MEASURE (ACL2-COUNT X)
                     :HINTS
                     ((\"Goal\" :BY (:FUNCTIONAL-INSTANCE F0-TERMINATION-LEMMA-3
                                                        (TD-STUB-2 F0))))))
                 (IF (ENDP X)
                     Y (LIST (F0 (CDDR X) (CONS 23 Y)) 100)))
 ACL2 !>
 })

 <p>@('Defunt') works by consulting a book that contains a database of
 information for generating @(see hints) based on @(':')@(tsee
 termination-theorem) @(see lemma-instance)s.  Information about the
 implementation, which is not necessary for using this utility, may be
 found (for those who are interested) in @(see community-books) file
 @('books/kestrel/auto-termination/README').</p>")

(defpointer auto-termination defunt)
