; Copyright (C) 2013, Regents of the University of Texas
; Written by Matt Kaufmann, August, 2007
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; Thanks to Robert Krug for requesting this tool.

(in-package "ACL2")
(include-book "bash")

(program)
(set-state-ok t)

(defun splitter1-p (lit hyps-list found-negation)
  (cond ((null hyps-list)
         found-negation)
        ((member-term lit (car hyps-list))
         (splitter1-p lit (cdr hyps-list) found-negation))
        ((member-complement-term lit (car hyps-list))
         (splitter1-p lit (cdr hyps-list) t))
        (t nil)))

(defun splitter (hyps hyps-list)
  (cond
   ((endp hyps) nil)
   ((splitter1-p (car hyps) hyps-list nil)
    (car hyps))
   (t (splitter (cdr hyps) hyps-list))))

(defun concl-as-equiv-and-lhs-1 (equiv lhs concls)
  (cond
   ((endp concls) nil)
   (t (let ((term (car concls)))
        (case-match term
          ((!equiv !lhs &)
           (concl-as-equiv-and-lhs-1 equiv lhs (cdr concls)))
          (('not !lhs)
           ;; NOTE: This isn't necessarily acceptible for all possible equivs!
           ;; This can be interpreted as (IFF X NIL) or (EQUAL X NIL), for
           ;; example, but in some cases (ARBITRARY-EQUIV X NIL) does not imply
           ;; (NOT X).
           (concl-as-equiv-and-lhs-1 equiv lhs (cdr concls)))
          (& (msg "The last literal of each clause generated is expected to ~
                   be of the form (equiv lhs rhs) for the same equiv and lhs. ~
                   The equiv for the last literal of the first clause is ~x0 ~
                   and its lhs is ~x1; but the last literal of one clause ~
                   generated is:~|~%~x2"
                  equiv lhs term)))))))

(defun concl-as-equiv-and-lhs (concls equiv)
  (assert$
   concls
   (let ((term (car concls)))
     (case-match term
       ((!equiv lhs &)
        (let ((msg (concl-as-equiv-and-lhs-1 equiv lhs (cdr concls))))
          (cond (msg (mv nil msg))
                (t (mv equiv lhs)))))
       (('not lhs)
        ;; See the note in concl-as-equiv-and-lhs-1 for caveats about NOT.
        (let ((msg (concl-as-equiv-and-lhs-1 equiv lhs (cdr concls))))
          (cond (msg (mv nil msg))
                (t (mv equiv lhs)))))
       (& (mv nil (msg "The last literal of each clause generated is expected ~
                        to be of the form (equiv lhs rhs), the but last ~
                        literal of the first clause generated is:~|~%~x0"
                       term)))))))

(defun remove-term (lit cl)

; Keep in sync with member-term/member-complement-term.  Here though we assume
; that there is no literal of the form (not (not &)).

  (cond ((variablep lit) (remove1-eq lit cl))
        ((fquotep lit) (remove1-equal lit cl))
        ((member-equal lit cl)
         (remove1-equal lit cl))
        ((or (eq (ffn-symb lit) 'equal)
             (eq (ffn-symb lit) 'iff))
         (let ((new-lit (fcons-term* (ffn-symb lit)
                                     (fargn lit 2)
                                     (fargn lit 1))))
           (assert$ (member-equal new-lit cl)
                    (remove1-equal new-lit cl))))
        (t (assert$
            (eq (ffn-symb lit) 'not)
            (let ((atm (fargn lit 1)))
              (assert$
               (and (nvariablep atm)
                    (not (fquotep atm))
                    (or (eq (ffn-symb atm) 'equal)
                        (eq (ffn-symb atm) 'iff)))
               (let* ((new-atm (fcons-term* (ffn-symb atm)
                                            (fargn atm 2)
                                            (fargn atm 1)))
                      (new-lit (fcons-term* 'not new-atm)))
                 (assert$ (member-equal new-lit cl)
                          (remove1-equal new-lit cl)))))))))

(defun split-cl-list (splitter hyps-list concls pos-hyps-list pos-concls neg-hyps-list neg-concls)
  (cond ((endp hyps-list)
         (mv (reverse pos-hyps-list) (reverse pos-concls)
             (reverse neg-hyps-list) (reverse neg-concls)))
        ((member-term splitter (car hyps-list))
         (split-cl-list splitter
                        (cdr hyps-list)
                        (cdr concls)
                        (cons (remove-term splitter (car hyps-list))
                              pos-hyps-list)
                        (cons (car concls)
                              pos-concls)
                        neg-hyps-list
                        neg-concls))
        (t
         (assert$
          (member-complement-term splitter (car hyps-list))
          (split-cl-list splitter
                         (cdr hyps-list)
                         (cdr concls)
                         pos-hyps-list
                         pos-concls
                         (cons (remove-term (dumb-negate-lit splitter)
                                            (car hyps-list))
                               neg-hyps-list)
                         (cons (car concls)
                               neg-concls))))))

(defun index-of-shortest-rec (lst-lst len ans i)
  (cond ((endp lst-lst) ans)
        (t (let ((new-len (length (car lst-lst))))
             (if (< new-len len)
                 (index-of-shortest-rec (cdr lst-lst) new-len i (1+ i))
               (index-of-shortest-rec (cdr lst-lst) len ans (1+ i)))))))

(defun index-of-shortest (lst-lst)
  (declare (xargs :guard (and (true-list-listp lst-lst)
                              lst-lst)))
  (index-of-shortest-rec (cdr lst-lst) (length (car lst-lst)) 0 1))

(defun member-equal-all (x lst-lst)
  (cond ((endp lst-lst) t)
        (t (and (member-equal x (car lst-lst))
                (member-equal-all x (cdr lst-lst))))))

(defun intersection-equal-with-all (lst lst-lst)
  (cond ((endp lst) nil)
        ((member-equal-all (car lst) lst-lst) ;
         (cons (car lst)
               (intersection-equal-with-all (cdr lst) lst-lst)))
        (t (intersection-equal-with-all (cdr lst) lst-lst))))

(defun all-set-difference-equal (lst-lst lst)
  (cond ((endp lst-lst) nil)
        (t (cons (set-difference-equal (car lst-lst) lst)
                 (all-set-difference-equal (cdr lst-lst) lst)))))

(defun defopener-remove1-by-position (index lst)

; Note: Renamed after ACL2 4.3 to avoid name conflict with new source function
; remove1-by-position.

  (if (endp lst) ; perhaps impossible for intended application
      nil
    (if (zp index)
        (cdr lst)
      (cons (car lst)
            (defopener-remove1-by-position (1- index) (cdr lst))))))

(defun split-clauses-to-term-rec (hyps-list concls)

; Returns (mv flg term), where flg is t if we do not have a perfect tree of
; possibilities, i.e., we encounter two or more clauses with no splitter.

  (let* ((splitter (splitter (car hyps-list) (cdr hyps-list))))
    (cond (splitter
           (mv-let (pos-hyps-list pos-concls neg-hyps-list neg-concls)
                   (split-cl-list splitter hyps-list concls
                                  nil nil nil nil)
                   (mv-let
                    (flg1 neg)
                    (split-clauses-to-term-rec neg-hyps-list neg-concls)
                    (mv-let
                     (flg2 pos)
                     (split-clauses-to-term-rec pos-hyps-list pos-concls)
                     (mv (or flg1 flg2)
                         (if (equal neg pos) ; maybe impossible?
                             pos
                           (fcons-term* 'if splitter neg pos)))))))
          ((null (cdr concls))
           (mv nil (fargn (car concls) 2))) ; rhs
          (t
           (mv t
               (let* ((i (index-of-shortest hyps-list))
                      (hyps (nth i hyps-list))
                      (concl (nth i concls))
                      (hyps-list (defopener-remove1-by-position i hyps-list))
                      (concls (defopener-remove1-by-position i concls))
                      (common-hyps
                       (intersection-equal-with-all hyps hyps-list))
                      (hyps-list
                       (all-set-difference-equal hyps-list common-hyps))
                      (hyps (set-difference-equal hyps common-hyps))
                      (tbr (fargn concl 2)) ; rhs
                      )
                 (mv-let
                  (flg fbr)
                  (split-clauses-to-term-rec hyps-list concls)
                  (declare (ignore flg))
                  (if (equal tbr fbr)
                      tbr
                    (fcons-term* 'if
                                 (conjoin (dumb-negate-lit-lst hyps))
                                 tbr
                                 fbr)))))))))

(defun split-clauses-to-flg-term-pair (hyps-list concls)

; Returns (cons flg term), where flg is t if we do not have a perfect tree of
; possibilities, i.e., we encounter two or more clauses with no splitter.

  (mv-let (flg term)
          (split-clauses-to-term-rec hyps-list concls)
          (cons flg term)))

(defun split-out-concls (cl-list hyps-list concls)
  (cond ((endp cl-list)
         (mv (reverse hyps-list) (reverse concls)))
        (t (split-out-concls (cdr cl-list)
                             (cons (butlast (car cl-list) 1)
                                   hyps-list)
                             (cons (car (last (car cl-list)))
                                   concls)))))

(defun flatten-ifs-to-cond (term)

; Takes an IF tree and linearizes it, so that we have (if test1 val1 (if test2
; val2 ...)), where no vali is a call of if.

; Example:
; (flatten-ifs-to-cond '(if a (if b c d) (if e f g)))
; evaluates to the following (ignoring issues of translate):
; (cond ((and a b) c)
;       ((and a (not b)) d)
;       (e f) ; could be ((and (not a) e) f) if we prefer that
;       (t g) ; could be ((and (not a) (not e)) g) if we prefer that
;       )

  (case-match term
    (('if tst ('if x y z) fbr)
     (flatten-ifs-to-cond `(if ,(conjoin2 tst x)
                               ,y
                             (if ,(conjoin2 tst (dumb-negate-lit x))
                                 ,z
                               ,fbr))))
    (('if tst tbr fbr)
     `(if ,(conjoin (flatten-ands-in-lit tst))
          ,tbr
        ,(flatten-ifs-to-cond fbr)))
    (& term)))

(defun bash-sim-fn (form hints equiv ctx state)
  (er-let*
   ((cl-list (with-ctx-summarized
              ctx
              (simplify-with-prover form hints ctx state))))
   (mv-let
    (hyps-list concls)
    (split-out-concls cl-list nil nil)
    (mv-let (equiv lhs)
            (concl-as-equiv-and-lhs concls equiv)
            (cond
             (equiv (value (split-clauses-to-flg-term-pair hyps-list concls)))
             (t (er soft ctx "~@0" lhs)))))))

(defun defopener-bodies (call hyp equiv hints flatten ctx state)
  (let* ((equiv (or equiv 'equal))
         (form0 (list equiv (list 'hide call) call))
         (form (if hyp `(implies ,hyp ,form0) form0))
         (wrld (w state)))
    (er-let*
     ((flg-rhs0-pair (bash-sim-fn form hints equiv ctx state)))
     (let* ((flg (car flg-rhs0-pair))
            (rhs0 (cdr flg-rhs0-pair))
            (rhs1 (if flatten (flatten-ifs-to-cond rhs0) rhs0))
            (hidden-rhs (list 'hide (untranslate rhs1 nil wrld)))
            (rhs (untranslate rhs1 nil wrld)))
       (value (if hyp
                  `((implies ,hyp (,equiv ,call ,hidden-rhs))
                    (implies ,hyp (,equiv ,call ,rhs))
                    ,hidden-rhs
                    . ,flg)
                `((,equiv ,call ,hidden-rhs)
                  (,equiv ,call ,rhs)
                  ,hidden-rhs
                  . ,flg)))))))

(defun defopener-hint-def (flatten-failed-flg)
  `(defun defopener-hint (id clause world stable-under-simplificationp)
     (declare (ignore id world))
     (and stable-under-simplificationp
          (let ((term (car (last clause))))
            ,(cond (flatten-failed-flg
                    '(case-match term
                       ((& & ('hide x)) ; (equiv lhs (hide x))
                        (list :expand (list (list 'hide x))))
                       ((& ('hide x) &) ; (equiv (hide x) lhs)
                        (list :expand (list (list 'hide x))))
                       (('not ('hide x))
                        (list :expand (list (list 'hide x))))
                       (& nil)))
                   (t
                    '(case-match term
                       ((& & ('hide x)) ; (equiv lhs (hide x))
                        (list :expand (list (list 'hide x))
                              :in-theory '(theory 'minimal-theory)))
                       ((& ('hide x) &) ; (equiv (hide x) lhs)
                        (list :expand (list (list 'hide x))
                              :in-theory '(theory 'minimal-theory)))
                       (('not ('hide x))
                        (list :expand (list (list 'hide x))
                              :in-theory '(theory 'minimal-theory)))
                       (& nil))))))))

(defmacro chk-name (name ctx ev-form)

; Causes error if name isn't new, except returns (value t) if there is a
; previous defopener event with the given name, call, hyp, equiv, and flatten.
; Otherwise returns (value nil).

  (let ((deflabel-form (list 'deflabel name)))
    `(make-event
      (let ((table-val (cdr (assoc-eq ',name
                                      (table-alist 'defopener-table
                                                   (w state))))))
        (if table-val
            (if (equal table-val ',ev-form)
                (value '(value-triple t))
              (mv-let (erp val state)
                      (er soft ',ctx
                          "The name ~x0 was applied to an earlier, different ~
                           defopener event:~|~X12"
                          ',name
                          table-val
                          nil)
                      (declare (ignore erp val))
                      (mv "Name check failed (see error message above)."
                          nil
                          state)))
          (mv-let (erp val state)
                  (with-output :off :all (ld '(,deflabel-form)
                                             :ld-error-action :error
                                             :ld-user-stobjs-modified-warning

; Matt K. mod: ACL2 now requires keyword :ld-user-stobjs-modified-warning in
; code.  If this macro is only to be evaluated at the top level, that keyword
; isn't needed.  But I'm including it, with value :same to preserve existing
; behavior, just in case someone uses it in code.  Perhaps more thought should
; be given to whether or not we want a warning here when a user stobj is
; modified.

                                             :same))
                  (declare (ignore val))
                  (if erp
                      (mv-let
                       (erp val state)
                       (er soft ',ctx
                           "The name ~x0 appears not to be new, as the form ~
                            ~x1 failed."
                           ',name
                           ',deflabel-form)
                       (declare (ignore erp val))
                       (mv "Name check failed (see error message above)."
                           nil
                           state))
                    (value '(value-triple nil :on-skip-proofs t)))))))))


(defxdoc defopener
  :parents (miscellaneous)
  :short "Create a defthm equating a call with its simplification."
  :long "<p>For a related tool, see @(see defopen).</p>

<p>Example:</p>

@({
  (include-book \"misc/defopener\" :dir :system)
  (defopener append-open
    (append x y)
    :hyp (and (true-listp x) (true-listp (cdr x)))
    :hints ((\"Goal\" :expand ((append x y)))))
})

<p>The above example creates the following theorem.</p>

@({
  (DEFTHM APPEND-OPEN
    (IMPLIES (AND (TRUE-LISTP X)
                  (TRUE-LISTP (CDR X)))
             (EQUAL (APPEND X Y)
                    (IF (NOT X)
                        Y
                        (CONS (CAR X) (APPEND (CDR X) Y))))))
})

<p>In general, the form</p>

@({
  (defopener name
    term
    :hyp hyp
    ...)
})

<p>attempts to create a theorem of the form</p>

@({
  (DEFTHM NAME
    (IMPLIES HYP
             (EQUAL TERM rhs)))
})

<p>where @('rhs') is generated by ACL2's simplification routines.  If @(':hyp') is
omitted, then of course the resulting form has the expected shape:</p>

@({
  (DEFTHM NAME
    (EQUAL TERM rhs)).
})

<p>If an equivalence relation symbol is supplied for @(':equiv'), then
@('EQUAL') above will be replaced by that symbol.</p>

<p>The output can be rather verbose.  Once @('rhs') as above has been produced,
ACL2 will print out the theorem to be proved before starting its proof,
indicated as follows.</p>

@({
  @@@@@@@@@@@@@@@@@@@@@@@@@@@@@@

  >>> STARTING PROOF OF:

  (DEFTHM NAME
          ...)

  @@@@@@@@@@@@@@@@@@@@@@@@@@@@@@
})

<p>To abbreviate the above message, you can specify an @(tsee
evisc-tuple) using the @(':evisc-tuple') keyword of @('defopener'),
which is @('nil') by default.</p>

<p>The simplification that takes place uses a prover interface that is also
used in the distributed book @('misc/bash'), in which the following hint is
automatically generated for @('\"Goal\"'), though they can be overridden if
explicitly supplied in the @('defopener') form for @('\"Goal\"'):</p>

@({
  :do-not (generalize eliminate-destructors fertilize eliminate-irrelevance)
})

<p>A suitable @(':do-not-induct') hint is also generated, so that induction is
avoided during the simplification process.  This too can be overridden.</p>

<p>If you only want to see the generated theorem, and not the attempted proof
of it, use @(':debug t').  Alternatively, you may want to run without that
addition and then submit @(':')@(see pcb!) to grab the generated @(see
encapsulate) form to put into the book that you are developing.  Otherwise, the
@('defopener') form will call the ACL2 simplifier twice each time you certify
your book: once to generate the theorem, and once to prove it.</p>

<p>The @(':flatten') keyword is @('t') by default, and causes the result to be
of the form @('(cond (c1 v1) (c2 v2) ... (ck vk) (t v))').  That result is
actually produced from a more primitive tree-based result, of the form @('(if c
v1 v2)'), where @('v1') and @('v2') can themselves be calls of @('if').  If you
prefer the more primitive form, use @(':flatten nil').</p>

<p>None of the arguments of this macro is evaluated.</p>")

(defmacro defopener (&whole ev-form
                            name call
                            &key hyp equiv hints debug (flatten 't) (evisc-tuple 'nil))
  (let* ((ctx (cons 'defopener name))
         (form `(er-let*
                 ((name-chk (chk-name ,name ,ctx ,ev-form)))
                 (if name-chk ; redundant
                     (value '(value-triple :redundant))
                   (er-let*
                    ((_defopener-bodies ; call the prover to simplify
                      (defopener-bodies ',call ',hyp ',equiv ',hints ',flatten
                        ',ctx state)))
                    (let* ((hidden-body (car _defopener-bodies))
                           (unhidden-body (cadr _defopener-bodies))
                           (hidden-rhs (caddr _defopener-bodies))
                           (flatten-failed-flg (cdddr _defopener-bodies))
                           (defthm-form1
                             (list 'defthm 'defopener-temp hidden-body
                                   ,@(and hints `(:hints ',hints))
                                   :rule-classes nil))
                           (defthm-form2
                             (list 'defthm ',name unhidden-body))
                           (defthm-form
                             (append
                              defthm-form2
                              (list :hints
                                    (list (list "Goal"
                                                :use
                                                'defopener-temp
                                                :expand
                                                (list hidden-rhs)
                                                :in-theory
                                                '(theory 'minimal-theory))))))
                           (table-ev
                            '(table defopener-table
                                    ',name
                                    ',ev-form)))
                      (pprogn
                       (fms "@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@~|~%"
                            nil (proofs-co state) state ,evisc-tuple)
                       (if flatten-failed-flg
                           (warning$ ',ctx nil
                                     "An incomplete case split for ~
                                      distinguishing hypothesis lists may ~
                                      lead to failure.")
                         state)
                       ,(if debug
                            'state
                          `(fms ">>> STARTING PROOF ~
                                 OF:~|~%~x0~|~%@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@~|~%"
                                (list (cons #\0 defthm-form2))
                                (proofs-co state)
                                state
                                ,evisc-tuple))
                       (value `(encapsulate
                                ()
                                ,table-ev
                                (local (encapsulate
                                        ()
                                        (local ,(defopener-hint-def
                                                  flatten-failed-flg))
                                        (add-default-hints '(defopener-hint))
                                        ,defthm-form1))
                                ,defthm-form)))))))))
    (if debug
        form
      `(make-event
        (mv-let (erp val state)
                ,form
                (if erp
                    (mv "Defopener failed.  Error messages above should ~
                         explain."
                        nil
                        state)
                  (value val)))))))
