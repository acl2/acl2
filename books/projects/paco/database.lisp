(in-package "ACL2")

; This file defines the macro db so that (acl2::db acl2::state) is the
; Paco analogue of the current ACL2 logical world.  This file can only
; be loaded after all the Paco files have been loaded, since it might
; conceptually use any Paco record or data structure.

; Does the ACL2 sometimes contain multiple entries for the same key
; and property?  Yes.  Every :logic mode function in axioms.lisp is
; defined twice, so the properties as ABSOLUTE-EVENT-NUMBER, FORMALS,
; GUARD, STOBJS-IN, STOBJS-OUT, SYMBOL-CLASS, and TYPE-PRESCRIPTIONS
; are all duplicated many times.  In addition, even user-defined
; functions may redefine both SYMBOL-CLASS and TYPE-PRESCRIPTIONS, as
; well as all the properties, e.g., LEMMAS, associated with newly
; added rules.  (Some stats, FYI: The boot strap world contains
; approximately 48K triples.  Of these, approximately 27K have unique
; symbol/property pairs.  There are about 3K symbol/property pairs
; that occur multiple times. It takes about a minute to sweep the
; world and find the duplicate entries in the completely naive way.
; The way we implement it here is about 30 times faster.)

; Seen is an alist pairing symbols with all the properties we have so
; far seen.  We say a trip (sym prop . val) is ``in'' seen if prop is
; an element of the value associated with sym in seen.


; Some ACL2 record accessor forms expand into terms involving the
; :program mode function record-error.  (In particular, the access
; forms for "non-cheap" records.)  This means that the functions that
; copy these records over to the Paco world have to be in :program
; mode.  Rather than make a careful determination of which records
; have this problem, I just do the entire development in :program
; mode.

(program)
(set-state-ok t)

(defun trip-seen (trip seen)

; We determine if trip is in seen.

  (let ((temp (assoc-eq (car trip) seen)))
    (cond
     ((null temp) nil)
     (t (member-eq (cadr trip) (cdr temp))))))

(defun mark-as-seen (trip seen)

; Assuming trip is not yet in seen, we put it there.

  (let ((temp (assoc-eq (car trip) seen)))
    (cond
     ((null temp) (cons (cons (car trip) (list (cadr trip))) seen))
     (t (put-assoc-eq (car trip)
                      (cons (cadr trip) (cdr temp))
                      seen)))))

(defun copy-recognizer-alist (alist)
  (cond
   ((endp alist) nil)
   (t (cons
       (paco::make paco::recognizer-tuple
                   :nume (access recognizer-tuple (car alist) :nume)
                   :fn (access recognizer-tuple (car alist) :fn)
                   :true-ts (access recognizer-tuple (car alist) :true-ts)
                   :false-ts (access recognizer-tuple (car alist) :false-ts)
                   :strongp  (access recognizer-tuple (car alist) :strongp))
       (copy-recognizer-alist (cdr alist))))))

(defun copy-type-prescriptions (tp-lst)
  (cond
   ((endp tp-lst) nil)
   (t (cons
       (paco::make paco::type-prescription
                   :nume (access type-prescription (car tp-lst) :nume)
                   :basic-ts (access type-prescription (car tp-lst) :basic-ts)
                   :term (access type-prescription (car tp-lst) :term)
                   :hyps (access type-prescription (car tp-lst) :hyps)
                   :vars (access type-prescription (car tp-lst) :vars))
       (copy-type-prescriptions (cdr tp-lst))))))

(defun acceptable-rewrite-hyps (hyps)
  (cond ((endp hyps) t)
        ((or (variablep (car hyps))
             (fquotep (car hyps)))
         (acceptable-rewrite-hyps (cdr hyps)))
        ((or (eq (ffn-symb (car hyps)) 'FORCE)
             (eq (ffn-symb (car hyps)) 'CASE-SPLIT))
         nil)
        ((and (eq (ffn-symb (car hyps)) 'SYNP)
              (not (eq (car (cadr (fargn (car hyps) 2))) 'SYNTAXP)))
         nil)
        (t (acceptable-rewrite-hyps (cdr hyps)))))

(defun copy-lemmas (lemmas)
  (cond
   ((endp lemmas) nil)
   ((acceptable-rewrite-hyps
     (access rewrite-rule (car lemmas) :hyps))
    (cons
     (paco::make
      paco::rewrite-rule
      :nume
      (access rewrite-rule (car lemmas) :nume)
      :hyps
      (access rewrite-rule (car lemmas) :hyps)
      :equiv
      (access rewrite-rule (car lemmas) :equiv)
      :lhs
      (access rewrite-rule (car lemmas) :lhs)
      :rhs
      (access rewrite-rule (car lemmas) :rhs)
      :subclass
      (let ((subclass (access rewrite-rule (car lemmas) :subclass)))
        (case subclass
          (abbreviation 'paco::backchain)
          (meta         'paco::meta)
          (definition   'paco::definition)
          (otherwise    'paco::backchain)))
      :heuristic-info
      (cond ((eq (access rewrite-rule (car lemmas) :subclass) 'definition)
             (cons (car (access rewrite-rule (car lemmas) :heuristic-info))
                   (list (cdr (access rewrite-rule (car lemmas) :heuristic-info)))))
            (t (access rewrite-rule (car lemmas) :heuristic-info))))
     (copy-lemmas (cdr lemmas))))
   (t (copy-lemmas (cdr lemmas)))))

(defun copy-elim-rule (x)
  (paco::make
   paco::elim-rule
   :nume (access elim-rule x :nume)                           ; nume
   :crucial-position (access elim-rule x :crucial-position)   ; number
   :destructor-term (access elim-rule x :destructor-term)     ; term
   :destructor-terms (access elim-rule x :destructor-terms)   ; terms
   :hyps (access elim-rule x :hyps)                           ; terms
   :equiv 'EQUAL                                              ; fn symbol
   :lhs (access elim-rule x :lhs)                             ; term
   :rhs (access elim-rule x :rhs))                            ; term
  )

(defun copy-built-in-clauses1 (bic-lst)
  (cond ((endp bic-lst) nil)
        (t (cons (paco::make
                  paco::built-in-clause
                  :nume
                  (access built-in-clause (car bic-lst) :nume)
                  :all-fnnames
                  (access built-in-clause (car bic-lst) :all-fnnames)
                  :clause
                  (access built-in-clause (car bic-lst) :clause))
                 (copy-built-in-clauses1 (cdr bic-lst))))))

(defun copy-built-in-clauses (bic-alist)
  (cond ((endp bic-alist) nil)
        (t (cons (cons (caar bic-alist)
                       (copy-built-in-clauses1 (cdar bic-alist)))
                 (copy-built-in-clauses (cdr bic-alist))))))

(defun copy-induction-machine (lst)

; An ACL2 induction-machine is a list of tests-and-calls records.
; Both tests and calls are just lists of terms and so don't need to be
; changed.  Does the record need to be changed?  That would depend on
; whether both records are of type "cheap".  Rather than answer that,
; I copy the record.

  (cond ((endp lst) nil)
        (t (cons (paco::make
                  paco::tests-and-calls
                  :tests (access tests-and-calls (car lst) :tests)
                  :calls (access tests-and-calls (car lst) :calls))
                 (copy-induction-machine (cdr lst))))))


; The quick-block-info for a function is a list of symbols as shown below.
; Paco could test against the ACL2 incarnation of those symbols rather than
; its own.

(defun copy-quick-block-info (lst)
  (cond ((endp lst) nil)
        (t (cons (case (car lst)
                   (self-reflexive 'paco::self-reflexive)
                   (unchanging     'paco::unchanging)
                   (otherwise      'paco::questionable))
                 (copy-quick-block-info (cdr lst))))))

(defun copy-justification (j)
  (paco::make
   paco::justification
   :subset  (access justification j :subset) ; list of vars
   :mp      (access justification j :mp)     ; pred symbol (e.g. E0-ORDINALP)
   :rel     (access justification j :rel)    ; rel symbol (e.g. E0-ORD-<)
   :measure (access justification j :measure); term
   ))

(defun copy-induction-rules (lst)
  (cond
   ((endp lst) nil)
   (t (cons (paco::make
             paco::induction-rule
             :nume      (access induction-rule (car lst) :nume)      ; nume
             :pattern   (access induction-rule (car lst) :pattern)   ; term
             :condition (access induction-rule (car lst) :condition) ; term
             :scheme    (access induction-rule (car lst) :scheme)    ; term
             )
            (copy-induction-rules (cdr lst))))))

(defun copy-type-set-inverter-rules (lst)

; This function exposes a lie in our bland reassurance that an ACL2
; term can be transferred to the Paco world without any changes.
; Type-set inverter rules contains terms in the variable X.  But in
; ACL2 that variable is acl2::x while in Paco it is paco::x.  So we
; have to rename it.

  (cond
   ((endp lst) nil)
   (t (cons
       (paco::make
        paco::type-set-inverter-rule
        :nume  (access type-set-inverter-rule (car lst) :nume)   ; nume
        :ts    (access type-set-inverter-rule (car lst) :ts)     ; type-set
        :terms (subst-var-lst                                    ; terms in X
                'paco::x
                'acl2::x
                (access type-set-inverter-rule (car lst) :terms))
        )
       (copy-type-set-inverter-rules (cdr lst))))))

(defun copy-generalize-rules (lst)
  (cond
   ((endp lst) nil)
   (t (cons
       (paco::make
        paco::generalize-rule
        :nume (access generalize-rule (car lst) :nume)           ; nume
        :formula (access generalize-rule (car lst) :formula)     ; term
        )
       (copy-generalize-rules (cdr lst))))))

(defun copy-trips (w seen a w0 paco-w0 ra state)

; Here, w is the ACL2 world, seen is a structure recording which trips
; we've already seen, a is the emerging Paco world.  It is in reverse
; order.

; Ra is the accumulated recognizer-alist.  (This parameter was added
; after ACL2 8.2 by Matt K. to accommodate an ACL2 change, which
; distributes recognizer-alist on individual properties rather than
; storing it in a world global.  Paco continues to store it as a world
; global, thus making further changes to Paco unnecessary.)

; Finally, w0 is another ACL2 world and paco-w0 is the Paco world
; corresponding to w0.  We use it to short-circuit the construction.

; We return (mv flg paco-w), where flg is t or nil indicating that we
; encountered w0 as a tail of w, and paco-w is the Paco world
; corresponding to w.

; Note: The only reason this function takes state is that it must
; sometimes call fn-rune-nume or getprop and needs the current ACL2
; world to do so.  I thought there were enough ``w's'' among the
; arguments above not to add yet another.  So I get the world out of
; state when I need it.  Nothing fancy is going on with state.

  (cond
   ((equal w w0)
    (mv t (cons (list* 'PACO::RECOGNIZER-ALIST
                       'PACO::GLOBAL-VALUE
                       (revappend ra
                                  (cddr (assoc-eq-equal 'PACO::RECOGNIZER-ALIST
                                                        'PACO::GLOBAL-VALUE
                                                        paco-w0))))
                (revappend a paco-w0))))
   ((endp w)
    (mv nil (cons (list* 'PACO::RECOGNIZER-ALIST
                         'PACO::GLOBAL-VALUE
                         (revappend ra nil))
                  (revappend a nil))))
   ((trip-seen (car w) seen)
    (copy-trips (cdr w) seen a w0 paco-w0 ra state))
   (t (let* ((new-seen (mark-as-seen (car w) seen))
             (sym (caar w))
             (prop (cadar w))
             (val (cddar w))
             (new-a
              (case prop
                (GLOBAL-VALUE
                 (case sym
                   (BUILT-IN-CLAUSES
                    (cons
                     (list* 'PACO::BUILT-IN-CLAUSES
                            'PACO::GLOBAL-VALUE
                            (copy-built-in-clauses val))
                     a))
                   (TYPE-SET-INVERTER-RULES
                    (cons
                     (list* 'PACO::TYPE-SET-INVERTER-RULES
                            'PACO::GLOBAL-VALUE
                            (copy-type-set-inverter-rules val))
                     a))
                   (GENERALIZE-RULES
                    (cons (list* 'PACO::GENERALIZE-RULES
                                 'PACO::GLOBAL-VALUE
                                 (copy-generalize-rules val))
                          a))
                   (otherwise a)))
                (FORMALS

; Every time we see a FORMALS property we know we are dealing with a function
; symbol, fn.  Paco must have some properties for fn that ACL2 does not
; maintain.  The first is a FN-NUMES property, giving the numes for
; (:DEFINITION fn), (:EXECUTABLE-COUNTERPART fn) and (:INDUCTION fn).  (ACL2
; has the runic mapping pairs property from which it recovers the numes.)  Paco
; must also have a BODY property, where ACL2 has the more modern def-bodies
; property.  Paco must also have a CONTROLLER-ALISTS property, which is a list
; of controller-alists.  Each controller-alist is an alist pairing the function
; symbols of a clique with a mask of ts and nils indicating the formals that
; are measured.  ACL2, as of Version 3.3, no longer has such a property and
; instead records a single controller alist in each def-body.  So, when this
; function sees a FORMALS property it takes the occasion to introduce FORMALS
; to Paco's world and also to introduce FN-NUMES and CONTROLLER-ALISTS.

                 (let ((def0
                         (car
                          (last
                           (getprop sym 'def-bodies nil
                                    'current-acl2-world
                                    (w state)))))
                       (formals-trip
                        (list* sym
                               'PACO::FORMALS
                               val))

                       (fn-numes-trip


; If you change the layout of the FN-NUMES value below, change
; fn-nume!

                        (list* sym
                               'PACO::FN-NUMES
                               (list
                                (fnume (list :DEFINITION sym) (w state))
                                (fnume (list :EXECUTABLE-COUNTERPART sym) (w state))
                                (fnume (list :INDUCTION sym) (w state))))))
                   (cond ((and def0
                               (null (access def-body def0 :hyp))

; If we want to allow other than EQUAL as the :equiv, we will need to think
; about possible consequences, perhaps restricting the application of :expand
; hints to suitable contexts.

                               (eq (access def-body def0 :equiv)
                                   'equal))
                          (list*
                           formals-trip
                           (list* sym
                                  'PACO::BODY
                                  (access def-body def0 :concl))
                           fn-numes-trip

; We just use the controller-alist for the first def-body of the
; function.

                           (list* sym
                                  'PACO::CONTROLLER-ALISTS
                                  (list (access def-body def0
                                                :controller-alist)))
                           a))
                         (t (list* formals-trip
                                   fn-numes-trip
                                   a)))))
                ((BODY UNNORMALIZED-BODY RECURSIVEP CONTROLLER-ALISTS
                       PRIMITIVE-RECURSIVE-DEFUNP LEVEL-NO)

; These properties have values that are the same in ACL2 as in Paco.
; Generally speaking, the only time it is safe to make that assumption
; is if the value is composed of terms, function symbols, conses (not
; "records" but just ordinary pairs and true-lists) and T and NIL.  If
; the value contains other symbols, like UNCHANGING, there is the
; possibility of confusion of packages and should be copied.  Note that
; we convert the property name into the PACO package.

                 (cons
                  (list* sym
                         (intern-in-package-of-symbol (symbol-name prop)
                                                      'PACO::REWRITE)
                         val)
                  a))

; For each of the remaining properties of interest we must translate
; from the ACL2 world to the Paco world.

                (TYPE-PRESCRIPTIONS
                 (cons
                  (list* sym
                         'PACO::TYPE-PRESCRIPTIONS
                         (copy-type-prescriptions val))
                  a))
                (LEMMAS
                 (cons
                  (list* sym
                         'PACO::LEMMAS
                         (copy-lemmas val))
                  a))
                (ELIMINATE-DESTRUCTORS-RULE
                 (cond
                  ((equal (access elim-rule val :equiv) 'EQUAL)
                   (cons (list* sym
                                'PACO::ELIMINATE-DESTRUCTORS-RULE
                                (copy-elim-rule val))
                         a))
                  (t a)))
                (INDUCTION-MACHINE
                 (cons (list* sym
                              'PACO::INDUCTION-MACHINE
                              (copy-induction-machine val))
                       a))
                (QUICK-BLOCK-INFO
                 (cons (list* sym
                              'PACO::QUICK-BLOCK-INFO
                              (copy-quick-block-info val))
                       a))
                (JUSTIFICATION
                 (cons (list* sym
                              'PACO::JUSTIFICATION
                              (copy-justification val))
                       a))
                (INDUCTION-RULES
                 (cons (list* sym
                              'PACO::INDUCTION-RULES
                              (copy-induction-rules val))
                       a))
                (otherwise a)))
             (new-ra
              (case prop
                (RECOGNIZER-ALIST
                 (revappend (copy-recognizer-alist val) ra))
                (otherwise ra))))
        (copy-trips (cdr w) new-seen new-a w0 paco-w0 new-ra state)))))

(defun transfer-paco-w1 (w w0 paco-w0 state)

; Logically, prog2$ is the identity function for its second argument,
; so the retract-world is irrelevant.  Logically, extend-world is the
; identity function for its second argument.  So, logically, this
; function is just a call of copy-trips.

; Actually, because of the hidden ACL2 effects of these functions,
; this installs the property list created by copy-trips, say paco-w,
; into the Common Lisp world, under the world name paco::paco.  That
; is, if acl2::getprop is ever invoked on paco-w with world name
; paco::paco, the computation goes directly to the Common Lisp

; The PSIM simulator need not do all this.  In an ideal world of
; memoized functions, it would be just as fast for this function just
; to return paco-w and for paco::getprop to be the slow version.

; Note: The only reason this function takes state is so that it can
; pass it to copy-trips.  The only reason copy-trips takes state is so
; that it can get the world out of it to make the call to
; fn-rune-nume.  This function doesn't do anything fancy with state.

  (mv-let (flg paco-w)
          (copy-trips w nil nil w0 paco-w0 nil state)
          (prog2$ (retract-world 'paco::paco (if flg paco-w0 nil))
                  (extend-world  'paco::paco paco-w))))

; See transfer-environments for the basic invariants concerning
; paco::paco-w and acl2::paco-w.  Roughly, the first is always the
; Paco world corresponding to the second.  In the function below, we
; compute and set the first.  But we do not set the second.  That is
; because we do not want to set it until we've computed all the
; environment variables based on the ACL2 world.

(defun transfer-paco-w (state)

; Note: This function takes state because it deals in error triples
; and sets state globals.

  (let ((paco-w (if (and (boundp-global 'paco::paco-w state)
                         (boundp-global 'acl2::paco-w state))
                    (transfer-paco-w1 (w state)
                                      (@ acl2::paco-w)
                                      (@ paco::paco-w)
                                      state)
                  (transfer-paco-w1 (w state) nil nil state))))
    (er-progn (assign paco::paco-w paco-w)

; You might expect us to do this:
;             (assign acl2::paco-w (w state))
; but we don't because there are other Paco variables we want to transfer.
; If we were to set acl2::paco-w now and then get interrupted while
; computing another variable, that variable would not correspond to
; the new w even though paco-w and (w state) would be equal.

              (value nil))))

; ---------------------------------------------------------------------------
; Section: Mapping ACL2's ENS to Paco's

(defun copy-ens1 (i max array-name array ans)
  (declare (xargs :measure (nfix (+ 1 (- max i)))))
  (cond ((not (and (integerp i)
                   (<= 0 i)
                   (integerp max)
                   (<= 0 max)))
         nil)
        ((> i max) (revappend ans nil))
        ((aref1 array-name array i)
         (copy-ens1 (+ 1 i) max array-name array ans))
        (t (copy-ens1 (+ 1 i) max array-name array (cons i ans)))))

(defun copy-ens (ens)

; We construct a Paco btree containing all the numes that are disabled
; by ens.  If a nume is greater than the :index-of-last-enabling it is
; enabled, so we only look at numes less than or equal to that index.
; The :theory-array of the ens is a bounded-integer-alistp: a true-list of
; pairs (n . x) where each n is either :HEADER or a natural less than
; the car of the :DIMENSIONS list of the :HEADER.

; Therefore, to determine all the disabled numes we map i from 0 to
; the :index-of-last-enabling and collect every i that is not bound in
; the :theory-array.  Since the returned list is ordered ascending, we
; don't have to sort it and so use Paco's make-btree1 instead of
; make-btree.

; WARNING: Some integers in this btree may not actually be numes.  It
; may be possible for ACL2 to skip a number while enumerating rules.
; (Actually, it doesn't as of this writing, but I don't recall that
; being guaranteed.)  But since the structure is only probed with
; numes, this will do.

  (paco::make-btree1
   (copy-ens1 0
              (access enabled-structure ens :index-of-last-enabling)
              (access enabled-structure ens :array-name)
              (access enabled-structure ens :theory-array)
              nil)))

(defun transfer-paco-ens (state)
  (cond ((and (boundp-global 'paco::paco-ens state)
              (boundp-global 'acl2::paco-ens state)
              (equal (@ acl2::paco-ens) (ens state)))
         (value nil))
        (t (er-progn
            (assign paco::paco-ens (copy-ens (ens state)))
            (assign acl2::paco-ens (ens state))
            (value nil)))))

; Paco deals exclusively with numes.  The user may wish to know the
; rune corresponding to a nume seen in a Paco trace.  But ACL2
; provides such map.  We provide one.

(defun transfer-nume-to-rune-map (state)

; This function makes the value of (@ nume-to-rune-map) be a structure
; that maps all numes to their runes.  Actually, the structure is an
; enabled structure and we just use the universal-theory to compute
; it.

  (let ((d (car
            (cadr
             (assoc-keyword
              :dimensions
              (cdr (assoc-eq :header
                             (access enabled-structure (ens state)
                                     :theory-array)))))))
        (name 'NUME-TO-RUNE-MAP-0))

; We re-use the same enabled structure over and over.  We start by
; asking if we've got one and if not build an empty one.  Then we load
; it, if the world has changed since the last loaded it.  The world
; with which it was loaded is (@ acl2::paco-w).

    (er-let*
      ((map
        (cond
         ((boundp-global 'nume-to-rune-map state)
          (value (@ nume-to-rune-map)))
         (t (er-progn
             (assign
              nume-to-rune-map
              (make enabled-structure
                    :index-of-last-enabling -1
                    :theory-array (compress1 name
                                             (cons (list :header
                                                         :dimensions (list d)
                                                         :maximum-length (1+ d)
                                                         :default nil
                                                         :name name)
                                                   nil))
                    :array-name name
                    :array-length d
                    :array-name-root
                    (all-but-last (coerce (symbol-name name) 'list))
                    :array-name-suffix 0))
             (value (@ nume-to-rune-map)))))))
      (cond
       ((and (boundp-global 'acl2::paco-w state)
             (equal (@ acl2::paco-w) (w state)))
        (value nil))
       (t
        (er-let*
          ((map (load-theory-into-enabled-structure
                 '(universal-theory-fn :here (w state)) ;;; theory-expr
                 (universal-theory-fn :here (w state))  ;;; theory
                 nil                                    ;;; augmented-p
                 map                                    ;;; ens
                 nil                                    ;;; incrmt-array-name-flg
                 nil                                    ;;; index-of-last-enabling
                 (w state)                              ;;; wrld
                 'transfer-nume-to-rune-map             ;;; ctx
                 state)                                 ;;; state
                ))
          (er-progn
           (assign nume-to-rune-map map)

; We do not assign acl2::paco-w until we have transferred all environment
; variables.

           (value nil))))))))

; The functions for using the map, nume-to-rune and numes-to-runes, are
; actually defined in the output-module because they are first used there.

; ---------------------------------------------------------------------------
; Section:  Putting It All Together

(defun transfer-environments (state from-scratch-flg)
  (pprogn
   (fms "Computing and transferring the ACL2 environment to Paco..."
        nil *standard-co* state nil)
   (er-progn
    (if from-scratch-flg
        (er-progn
         (assign paco::paco-w nil)
         (assign acl2::paco-w nil))
      (value nil))
    (cond
     ((and (boundp-global 'acl2::paco-w state)
           (equal (@ acl2::paco-w) (w state)))
      (pprogn
       (fms "~%Done.~%" nil *standard-co* state nil)
       (value nil)))
     (t (er-progn
         (transfer-paco-w state) ; set paco::paco-w
         (transfer-paco-ens state) ; set paco::paco-ens (and acl2::paco-ens)
         (transfer-nume-to-rune-map state)
; set acl2::rune-to-nume-map
         (assign acl2::paco-w (w state))
         (pprogn
          (fms "~%Done.~%" nil *standard-co* state nil)
          (value nil))))))))

(defmacro paco::transfer-environments (&optional (from-scratch-flg 'nil))

; If this were defined as a function it would have to take state as an
; argument and since it is normally called from the PACO package we
; would have to write acl2::state which is inconvenient.  Hence, we
; make it a macro.

  `(transfer-environments state ,from-scratch-flg))

(defmacro paco::w nil
  '(@ paco::paco-w))

(defmacro paco::ens nil
  '(@ paco::paco-ens))

(defmacro paco::rune (nume)
  `(nume-to-rune ,nume (@ nume-to-rune-map)))

; ---------------------------------------------------------------------------
; Section:  Paco Hint Translation

(defun probable-paco-clause-id (lst)
  (cond ((atom lst) (equal lst nil))
        ((and (integerp (car lst))
              (< 0 (car lst)))
         (probable-paco-clause-id (cdr lst)))
        (t nil)))

(defun value-nil (key x ctx state)
  (cond ((eq x nil) (value nil))
        (t (er soft ctx "Paco ~x0 hints must end in nil." key))))

(defun translate-paco-use-hint (arg ctx wrld state)
  (cond
   ((atom arg) (value-nil :USE arg ctx state))
   ((and (true-listp (car arg))
         (eq (car (car arg)) :INSTANCE)
         (< 0 (len (cdr (car arg))))
         (symbolp (cadr (car arg))))
    (let ((thm (formula (cadr (car arg)) nil wrld)))
      (er-let*
        ((alist (translate-substitution (cddr (car arg)) ctx wrld state))
         (thm (if thm
                  (value thm)
                (er soft ctx "~x0 does not name a theorem." (cadr (car arg)))))
         (rst (translate-paco-use-hint (cdr arg) ctx wrld state)))
        (value (cons (sublis-var alist thm) rst)))))
   (t (er soft ctx "Ill-formed :INSTANCE ~x0" (car arg)))))

(defun translate-paco-expand-hint (arg ctx wrld state)
  (cond
   ((atom arg) (value-nil :EXPAND arg ctx state))
   (t (er-let*
        ((term (translate (car arg) t t t ctx wrld state)))
        (cond
         ((and (nvariablep term)
               (not (fquotep term))
               (or (flambda-applicationp term)
                   (body (ffn-symb term) t wrld)))
          (er-let*
            ((rst (translate-paco-expand-hint (cdr arg) ctx wrld state)))
            (value (cons term rst))))
         (t (er soft ctx
                "The term ~x0 is not expandable."
                term)))))))

(defun runes-to-numes (lst ctx wrld state)

; This returns a list of numes, with no duplications, or else signals
; an error.

  (cond
   ((atom lst) (value nil))
   ((runep (car lst) wrld)
    (er-let* ((rst (runes-to-numes (cdr lst) ctx wrld state)))
      (value (add-to-set-equal (fnume (car lst) wrld) rst))))
   (t (er soft ctx "~x0 is not a rune." (car lst)))))

(defun translate-paco-in-theory-hint (arg ctx wrld state)
  (cond
   ((and (true-listp arg)
         (case (car arg)
           (paco::e/d (and (equal (len arg) 3)
                           (true-listp (cadr arg))
                           (true-listp (caddr arg))))
           (paco::enable t)
           (paco::disable t)
           (otherwise nil)))
    (er-let* ((numes-to-enable
               (runes-to-numes (case (car arg)
                                 (paco::e/d (cadr arg))
                                 (paco::enable (cdr arg))
                                 (otherwise nil))
                               ctx wrld state))
              (numes-to-disable
               (runes-to-numes (case (car arg)
                                 (paco::e/d (caddr arg))
                                 (paco::enable nil)
                                 (otherwise (cdr arg)))
                               ctx wrld state)))
      (let ((currently-disabled-numes (paco::btree-contents (paco::ens))))
        (value
         (paco::make-btree
          (union-equal
           numes-to-disable
           (set-difference-equal currently-disabled-numes
                                 numes-to-enable)))))))
   (t (er soft ctx "Ill-formed :IN-THEORY hint, ~x0." arg))))

(defun translate-paco-hands-off-hint (arg ctx wrld state)
  (cond
   ((atom arg) (value-nil :HANDS-OFF arg ctx state))
   ((and (consp (car arg))
         (eq (car (car arg)) 'lambda)
         (consp (cdr (car arg)))
         (true-listp (cadr (car arg))))

; At this point we know that the car of arg is of the form (lambda
; (...) . &) and we want to translate it.  To do so, we create a term
; by applying it to a list of terms.  Where do we get a list of the
; right number of terms?  We use its own formals!

    (er-let*
      ((term (translate (cons (car arg) (cadr (car arg)))
                        t t t ctx wrld state))
       (rst (translate-paco-hands-off-hint (cdr arg) ctx wrld state)))

; Below we assume that if you give translate ((lambda ...) ...) and it
; does not cause an error, then it gives you back a function application.

      (value (cons (ffn-symb term) rst))))
   ((and (symbolp (car arg))
         (function-symbolp (car arg) wrld))
    (er-let*
      ((rst (translate-paco-hands-off-hint (cdr arg) ctx wrld state)))
      (value (cons (car arg) rst))))
   (t (er soft ctx
          "The object ~x0 is not a legal element of a :HANDS-OFF ~
           hint."
          (car arg)))))

(defun translate-paco-do-not-hint (arg ctx wrld state)
  (declare (ignore wrld))
  (cond ((and (true-listp arg)
              (subsetp-equal arg paco::*waterfall*))
         (value arg))
        (t (er soft ctx "The :DO-NOT hint requires a subset of ~x0."
               paco::*waterfall*))))


(defun translate-paco-cases-hint (arg ctx wrld state)
  (cond
   ((atom arg) (value-nil :CASES arg ctx state))
   (t (er-let*
        ((term (translate (car arg) t t t ctx wrld state))
         (rst (translate-paco-cases-hint (cdr arg) ctx wrld state)))
        (value (cons term rst))))))

(defun translate-paco-by-hint (arg ctx wrld state)
  (cond ((symbolp arg)
         (let ((thm (formula arg t wrld)))
           (cond (thm (value thm))
                 (t (er soft ctx "~x0 does not name a theorem." arg)))))
        (t (er soft ctx "~x0 does not name a theorem." arg))))

(defun translate-paco-induct-hint (arg ctx wrld state)
  (er-let* ((term (translate arg t t t ctx wrld state)))
    (value (cond ((equal term *nil*) :DO-NOT-INDUCT)
                 ((equal term *t*) t)
                 (t term)))))

(defun translate-paco-x-hint (key val ctx wrld state)
  (case key
    (:USE (translate-paco-use-hint val ctx wrld state))
    (:EXPAND (translate-paco-expand-hint val ctx wrld state))
    (:IN-THEORY (translate-paco-in-theory-hint val ctx wrld state))
    (:HANDS-OFF (translate-paco-hands-off-hint val ctx wrld state))
    (:DO-NOT (translate-paco-do-not-hint val ctx wrld state))
    (:CASES (translate-paco-cases-hint val ctx wrld state))
    (:BY (translate-paco-by-hint val ctx wrld state))
    (:INDUCT (translate-paco-induct-hint val ctx wrld state))
    (otherwise (er soft ctx "Paco does not support ~x0 hints." key))))

(defun translate-paco-hint-key-val-lst (lst ctx wrld state)
  (cond ((endp lst) (value nil))
        ((keywordp (car lst))
         (er-let*
           ((tval (translate-paco-x-hint (car lst) (cadr lst) ctx wrld state))
            (rst (translate-paco-hint-key-val-lst (cddr lst) ctx wrld state)))
           (value (cons (cons (car lst) tval) rst))))
        (t (er soft ctx
               "Every other element of a hint specification must ~
               be a keyword and ~x0 is not."
               (car lst)))))

(defun translate-paco-hint (x ctx wrld state)
  (cond
   ((and (true-listp x)
         (probable-paco-clause-id (car x))
         (evenp (len (cdr x))))
    (er-let* ((alist (translate-paco-hint-key-val-lst (cdr x) ctx wrld state)))
      (value (cons (car x) alist))))
   (t (er soft ctx
          "Each Paco hint must be of the form (id :key1 val1 ... :keyn valn),~
          where id is a true-list of natural numbers.  ~x0 is not of this ~
          form."
          x))))

(defun translate-paco-hints (x ctx wrld state)

;  key                 input                           output

; :USE       (... (:INSTANCE name . subst) ...)  => (... thm ...)
; :EXPAND    (... term ...)                      => (... term ...)
; :IN-THEORY (E/D (... rune ...) (... rune ...)) => ens
; :IN-THEORY (ENABLE ... rune ...)               => ens
; :IN-THEORY (DISABLE ... rune ...)              => ens
; :HANDS-OFF (... fn ...)                        => (... fn ...)
; :DO-NOT    (... process ...)                   => (... process ...)
; :CASES     (... term ...)                      => (... term ...)
; :BY        name                                => thm
; :INDUCT    term                                => t, :DO-NOT-INDUCT, or term

; where (output) thm and term are in translated form, ens is a Paco
; btree, fn is a function symbol or lambda expression, and process is
; member of the *waterfall*.

  (cond ((atom x)
         (if (null x)
             (value nil)
           (er soft ctx ":HINTS must be a true-list.")))
        (t (er-let* ((pair (translate-paco-hint (car x) ctx wrld state))
                     (rst (translate-paco-hints (cdr x) ctx wrld state)))
             (value (cons pair rst))))))

; ---------------------------------------------------------------------------
; Section:  The Paco DEFTHM

(defun paco::defthm-fn (name term waterfall-depth state hints rule-classes)
  (er-progn
   (transfer-environments state nil)
   (er-let* ((tterm (translate term t t t 'paco::defthm (w state) state))
             (hint-settings
              (translate-paco-hints hints (cons 'dthm name)
                                    (w state) state)))
     (let* ((p (paco::prove tterm (paco::ens) (paco::w)
                            hint-settings
                            waterfall-depth)))
       (cond ((eq (paco::describe-proof-attempt p 0) :QED)
              (er-progn (assign last-proof-attempt p)
                        (defaxiom-fn name tterm state
                          rule-classes
                          `(paco::dthm ,name ,term
                                       ,@(if hint-settings
                                             (list :hint-settings
                                                   hint-settings)
                                           nil)
                                       ,@(if (and rule-classes
                                                  (not (equal rule-classes
                                                              '(:REWRITE))))
                                             (list :rule-classes
                                                   rule-classes)
                                           nil)))
                        (value :QED)))
             (t (er-progn
                 (assign last-proof-attempt p)
                 (pprogn
                  (fms *proof-failure-string* nil *standard-co* state nil)
                  (mv t nil state)))))))))

(defmacro paco::dthm (name term &key
                           (hints 'nil)
                           (depth '10)
                           (rule-classes '(:REWRITE)))

  `(paco::defthm-fn ',name ',term ,depth state
                    ,(list 'quote hints)
                    ,(list 'quote rule-classes)))

(defmacro paco::show-proof (d-level)
  `(paco::describe-proof-attempt (@ last-proof-attempt) ,d-level))

; We define prf in the ACL2 package so that we can type :prf 1 after
; a Paco proof attempt and see the proof.

(defmacro prf (d-level)
  `(paco::show-proof ,d-level))

; And we define paco::prf so we can write (prf 1).

(defmacro paco::prf (d-level)
  `(paco::show-proof ,d-level))
