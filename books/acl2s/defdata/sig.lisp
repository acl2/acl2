#|$ACL2s-Preamble$;
(include-book ;; Newline to fool ACL2/cert.pl dependency scanner
 "../portcullis")
(acl2::begin-book t :ttags :all);$ACL2s-Preamble$|#

#|
Polymorphic signatures (sig macro)
author: harshrc
file name: sig.lisp
date created: [2014-08-06 Sun]
data last modified: [2014-08-07]
|#

(in-package "DEFDATA")

(include-book "defdata-core")

; DEFDATA POLYMORPHIC SUPPORT EVENT GENERATION FUNCTIONS.

(def-const *allowed-type-vars*
  '(:a :b :c :d :a1 :b1 :c1 :d1 :a2 :b2 :c2 :d2))

(def-const *tvar-typename-alist*
  '((:a . A)
    (:b . B)
    (:c . C)
    (:d . D)
    (:a1 . A1)
    (:b1 . B1)
    (:c1 . C1)
    (:d1 . D1)
    (:a2 . A2)
    (:b2 . B2)
    (:c2 . C2)
    (:d2 . D2)))

; type var expr -> psig fun instance template
; where type var expr is the dominating polymorphic argument expr in a sig form
(table psig-template-map nil) ;UNUSED now -- but seems like a more general idea to support arbitrary polymorphic type expressions. REVISIT

(defstub psig-templ-instantiation-ev (* * * * * * *) => *)

(defloop psig-inst-templates
  (tname tvar-sigma templates new-types kwd-alist wrld)
  (for ((templ in templates))
       (append (psig-templ-instantiation-ev
                tname
                tvar-sigma
                templ
                (table-alist 'derived-pred->poly-texp-map wrld)
                new-types
                kwd-alist
                wrld))))

(program)

(defun one-way-unify (pat term)
  (if (and (pseudo-termp pat)
           (pseudo-termp term))
      (acl2::one-way-unify pat term)
    (mv nil nil)))

(defun polymorphic-inst-defdata-events1 (p top-kwd-alist wrld)
  (b* (((cons name A) p)
       ;; (pdef (cdr (assoc-eq 'pdef A)))
       ;; (kwd-alist (cdr (assoc-eq 'kwd-alist A)))
       ((acl2::assocs pdef new-types kwd-alist) A)
;       (- (cw "pdef : ~x0" pdef))
       ((unless (consp pdef)) '())
       (kwd-alist (append kwd-alist top-kwd-alist))
       (comb (car pdef))
       (U (table-alist 'user-combinator-table wrld))
       (C (table-alist 'data-constructor-table wrld))
;TODO: at some time i should support polymorphic cons, but perhaps this is done by tau already SIMPLE BUT GOOD RESEARCH Question/Experiment.
; Or rather simply use a separate table psig-template-map to support polymorphism more generally
       (meta-kwd-alist (or (cdr (assoc-eq comb U)) (cdr (assoc-eq comb C))))

       (template (get1 :polymorphic-events meta-kwd-alist))
       (ptype (get1 :polymorphic-type-form meta-kwd-alist))
;       (- (cw "ptype : ~x0    tmpl: ~x1" ptype template))
       ((when (null ptype)) '()) ;no poly support

       (pdef (remove-names pdef))
;(one-way-unify '(alistof :a :b) '(alistof nat symbol-list))
;(T ((:B . SYMBOL-LIST) (:A . NAT)))
       ((mv yesp tvar-sigma)
        (one-way-unify (acl2::sublis-var *tvar-typename-alist* ptype) pdef))

       (verbose (get1 :verbose kwd-alist t))

        (- (cw? (and (not yesp) verbose) "~|Defdata/Note: Failed to unify ~x0 with ~x1. Skipping polymorphic instantiation events...~%" ptype pdef))
        ((unless yesp) '()))

    (psig-templ-instantiation-ev
     name
     tvar-sigma
     template
     (table-alist 'derived-pred->poly-texp-map wrld)
     new-types
     kwd-alist
     wrld)))

(defloop polymorphic-inst-defdata-events0 (ps kwd-alist wrld)
  (for ((p in ps))
       (append (polymorphic-inst-defdata-events1 p kwd-alist wrld))))

#|

Pete: I added the try-admitting-events-fun function so that when
defdata tries to prove the automatically-generated theorems that
provide polymorphic support, then if any such theorem fails,
instead of stopping, we continue trying to prove the remaining
theorems.  This is useful in cases where one of these theorems
fails, but later theorems would have succeeded. In this way, we
get as much automated polymorphic support as possible.

|#

(defun try-admitting-events-fun (events)
  (if (endp events)
      nil
    (cons `(make-event
            '(:or ,(car events) (value-triple t)))
          (try-admitting-events-fun (cdr events)))))

(defun polymorphic-inst-defdata-events (ps kwd-alist wrld)
  (b* ((events (polymorphic-inst-defdata-events0 ps kwd-alist wrld)))
    (and (consp events)
         (cons
          `(commentary ,(get1 :print-commentary kwd-alist)
                       "~| Polymorphic sig instantiation events...~%")
          (try-admitting-events-fun events)))))

(add-pre-post-hook
 defdata-defaults-table
 :post-pred-hook-fns '(polymorphic-inst-defdata-events))

; The rest of the file concerns with the implementation of the SIG macro

; sig macro for polymorphic support.

; I dont think we are ever going to have more than 3 type parameters, but lets start with 12.
(logic)
(encapsulate
 (((Ap *) => *)
  ((Bp *) => *)
  ((Cp *) => *)
  ((Dp *) => *)
  ((A1p *) => *)
  ((B1p *) => *)
  ((C1p *) => *)
  ((D1p *) => *)
  ((A2p *) => *)
  ((B2p *) => *)
  ((C2p *) => *)
  ((D2p *) => *))

 (local (defun Ap (v)
          (declare (ignore v))
          t))

 (local (defun Bp (v)
          (declare (ignore v))
          t))

 (local (defun Cp (v)
          (declare (ignore v))
          t))

 (local (defun Dp (v)
          (declare (ignore v))
          t))

 (local (defun A1p (v)
          (declare (ignore v))
          t))

 (local (defun B1p (v)
          (declare (ignore v))
          t))

 (local (defun C1p (v)
          (declare (ignore v))
          t))

 (local (defun D1p (v)
          (declare (ignore v))
          t))

 (local (defun A2p (v)
          (declare (ignore v))
          t))

 (local (defun B2p (v)
          (declare (ignore v))
          t))

 (local (defun C2p (v)
          (declare (ignore v))
          t))

 (local (defun D2p (v)
          (declare (ignore v))
          t))

 (defthm Ap-is-predicate
   (booleanp (Ap x)))

 (defthm Bp-is-predicate
   (booleanp (Bp x)))

 (defthm Cp-is-predicate
   (booleanp (Cp x)))

 (defthm Dp-is-predicate
   (booleanp (Dp x)))

 (defthm A1p-is-predicate
   (booleanp (A1p x)))

 (defthm B1p-is-predicate
   (booleanp (B1p x)))

 (defthm C1p-is-predicate
   (booleanp (C1p x)))

 (defthm D1p-is-predicate
   (booleanp (D1p x)))

 (defthm A2p-is-predicate
   (booleanp (A2p x)))

 (defthm B2p-is-predicate
   (booleanp (B2p x)))

 (defthm C2p-is-predicate
   (booleanp (C2p x)))

 (defthm D2p-is-predicate
   (booleanp (D2p x))))

(program)

;(def-const *allowed-type-var->named-type-binding*
;   (pairlis$ *allowed-type-vars* *tvar-typename-alist*))


;ACHTUNG: make sure people dont use names from defdata namespace. Note that A,Ap,... reside in defdata namespace.
(def-const *initial-tvar-M*
  (type-metadata-bases (strip-cdrs *tvar-typename-alist*) "DEFDATA"))

;maps typenames of type vars to metadata like in M.
;e.g. A -> Ap nth-A etc
(table tvar-metadata-table nil *initial-tvar-M* :clear)

(mutual-recursion
 (defun collect-type-vars-texp (texp ctx)
   (cond ((quotep texp) '())
         ((keywordp texp) (list texp))
         ((atom texp) '())
         ((not (true-listp texp)) ;right now we dont support named texp
          (er hard? ctx "~| ~x0 : Named type expressions not supported.~%" texp))
         (t (collect-type-vars-texps (cdr texp) ctx))))
 (defun collect-type-vars-texps (texps ctx)
   (if (endp texps)
       '()
     (union-eq (collect-type-vars-texp (car texps) ctx)
               (collect-type-vars-texps (cdr texps) ctx))))
 )

(mutual-recursion
 (defun collect-undefined-typenames-texp (texp ctx wrld)
   (cond ((quotep texp) '())
         ((keywordp texp) '())
         ((atom texp) (if (predicate-name texp) '() (list texp)))
         ((not (true-listp texp)) ;right now we dont support named texp
          (er hard? ctx "~| ~x0 : Named type expressions not supported.~%" texp))
         (t (collect-undefined-typenames-texps (cdr texp) ctx wrld))))
 (defun collect-undefined-typenames-texps (texps ctx wrld)
   (if (endp texps)
       '()
     (union-eq (collect-undefined-typenames-texp (car texps) ctx wrld)
               (collect-undefined-typenames-texps (cdr texps) ctx wrld))))
 )


;(include-book "coi/util/pseudo-translate" :dir :system)

(def-const *sig-keywords*
  '(:hints :gen-rule-classes :rule-classes :verbose :satisfies :suffix))

;check -- also take care of monomorphic sig, but make sure only tnames are allowed!
(defun parse-sig (args curr-pkg ctx wrld)
  (declare (ignorable wrld))
  (b* (((mv sig kwd-val-list) (separate-kwd-args args '()))
       ((mv kwd-alist rest)
        (extract-keywords ctx *sig-keywords* kwd-val-list '() nil))
       ((unless (null rest)) (er hard? ctx "~| Extra args: ~x0~%" rest))
       (dep-hyp (get1 :satisfies kwd-alist))
       (suffix (get1 :suffix kwd-alist))
       (x123vars (numbered-vars (acl2s::fix-intern$ "X" curr-pkg)
                                (len *allowed-type-vars*)))
       (dep-vars (and dep-hyp (all-vars dep-hyp))) ;BEWARE all-vars works only for terms; it might return nil and t as variables. Use pseudo-translate here.
       ((unless (subsetp dep-vars x123vars))
        (er hard? ctx "~| Only variable arguments allowed in SATISFIES are ~x0; but given ~x1~%" x123vars dep-vars))
       (dep-hyps (cond ((null dep-hyp) nil)
                       ((or (eq dep-hyp 't) (equal dep-hyp ''t)) nil)
                       ((atom dep-hyp) (list dep-hyp))
                       ((eq (car dep-hyp) 'ACL2::AND) (cdr dep-hyp))
                       ((proper-symbolp (car dep-hyp)) (list dep-hyp))
                       (t dep-hyp)))
       (kwd-alist (put-assoc-eq :satisfies dep-hyps kwd-alist))
       (kwd-alist (put-assoc-eq :current-package curr-pkg kwd-alist))
;(- (cw "sig = ~x0  kwd-alist = ~x1 " sig kwd-alist))
       )

    (case-match sig
      ((name arg-type-list 'ACL2S-SHARED::=> return-type)
       (b* (((unless (proper-symbolp name))
             (er hard? ctx "~| Name ~x0 should be a symbol.~%" name))
;simple syntax checks
            (& (check-syntax-texps arg-type-list '() '() ctx wrld))
            (undefined-typenames
             (collect-undefined-typenames-texps
              (cons return-type arg-type-list) ctx wrld))
            ((when (consp undefined-typenames))
             (er hard? ctx "~| Undefined types: ~x0~%" undefined-typenames))
            (arg-type-vars (collect-type-vars-texps arg-type-list ctx))
            (return-type-vars (collect-type-vars-texp return-type ctx))
            ((unless (subsetp return-type-vars arg-type-vars))
             (er hard? ctx "~| Return type variables should be from ~x0.~%"
                 arg-type-vars))
; todo: do the mapping from current keyword type variables to :a :b ...
            ((unless (subsetp arg-type-vars *allowed-type-vars*))
             (er hard? ctx "~| Sorry for the inconvenience, but could you please try again choosing type variables from ~x0.~%" *allowed-type-vars*)))

         (list name suffix arg-type-list return-type kwd-alist)))

      (& (er hard? ctx "~| General form: (sig name arg-type-list => return-type).~%" )))))

(defun to-symbol (obj pkg)
  (declare (xargs :guard (pkgp pkg)))
  (if (symbolp obj)
      obj
    (b* (((mv & str) (acl2::fmt1!-to-string "~x0" (acons #\0 obj '()) 0)))
      (acl2s::fix-intern$ str pkg))))

(defloop to-symbols (objs pkg)
  (declare (xargs :guard (pkgp pkg)))
  (for ((o in objs)) (collect (to-symbol o pkg))))

;; (defun map-fn (lst f rest-args ctx w)
;;   (if (endp lst)
;;       '()
;;     (cons (funcall-w f (cons (car lst) rest-args) ctx w)
;;           (map-fn (cdr lst) f rest-args ctx w))))

;; (defmacro map (lst f w &key rest-args)
;;   `(map-fn ,lst ,f ,rest-args ,w))

(defun assoceqlst1 (key A)
  (let ((entry (assoc-eq key A)))
    (and entry (list entry))))

(defloop assoc-eq-lst (keys A)
  (for ((key in keys)) (append (assoceqlst1 key A))))

(defun stitch-up-defuns (names params-lst decls bodies)
  (if (endp names)
    nil
    (cons (if (consp decls);not null (only include declare if its not empty)
            (list 'DEFUN (car names) (car params-lst) (car decls) (car bodies))
            (list 'DEFUN (car names) (car params-lst) (car bodies)))
          (stitch-up-defuns (cdr names)
                            (cdr params-lst)
                            (cdr decls)
                            (cdr bodies)))))

(defun make-derived-tvar-type-defthm (pred texp pkg)
  (case-match texp
    (('LISTOF &) `((defthm ,(s+ pred '-IMPLIES-TLP :pkg pkg)
                     (implies (,pred x)
                              (true-listp x))
                     :hints (("Goal" :in-theory (enable true-listp)))
                     :rule-classes ((:forward-chaining)
                                    (:compound-recognizer)
                                    ;;(:rewrite :backchain-limit-lst 1)
                                    ))))

    (('ALISTOF & &) `((defthm ,(s+ pred '-IMPLIES-ALISTP :pkg pkg)
                        (implies (,pred x)
                                 (alistp x))
                        :hints (("Goal" :in-theory (enable ,pred alistp)))
                        :rule-classes ((:forward-chaining)))))
    (& '())))

(defloop make-derived-tvar-type-defthms (preds texps pkg)
  (for ((p in preds) (texp in texps))
       (append (make-derived-tvar-type-defthm p texp pkg))))


;TODO.limitation -- Using just name for the clique tnames (LIMITATION)."
(defloop parse-top-texps (names texps ctx wrld)
  (for ((name in names) (texp in texps))
       (collect (parse-top-texp name texp (list name) ctx wrld))))

(defun make-sig-tvar-support-events (texps ctx pkg wrld)
  "for each undefined tvar texp, define its predicate and if possible its type defthm"
  (b* ((M (append (table-alist 'tvar-metadata-table wrld)
                  (table-alist 'type-metadata-table wrld)))
       (texps (remove-names-lst (remove-duplicates-equal texps)))
       (tnames  (to-symbols texps "DEFDATA"))

       (undef-tnames (set-difference-eq tnames (strip-cars (assoc-eq-lst tnames M))))

       (undef-nm-texp-alst (assoc-eq-lst undef-tnames (pairlis$ tnames texps)))
;       (- (cw "nm-texp-alst: ~x0 undef-tnames: ~x1  undef-nm-texp-alst: ~x2" nm-texp-alst undef-tnames undef-nm-texp-alst))
       ((mv undef-tnames undef-texps) (mv (strip-cars undef-nm-texp-alst) (strip-cdrs undef-nm-texp-alst)))
       (undef-n-types (parse-top-texps undef-tnames undef-texps ctx wrld))


       (C (table-alist 'data-constructor-table wrld))
       (B (table-alist 'builtin-combinator-table wrld))
       (new-types (type-metadata-bases undef-tnames "DEFDATA"))
       (M (append new-types M))
       (A (table-alist 'type-alias-table wrld))
       (undef-pred-bodies
        (make-pred-Is undef-n-types
                      (make-list (len undef-n-types)
                                 :initial-element (acl2s::fix-intern$ "X" pkg))
                      nil A M C B wrld))
       (undef-pred-names (make-predicate-symbol-lst undef-tnames "DEFDATA")))
;   in
    (append (stitch-up-defuns
             undef-pred-names
             (make-list (len undef-pred-names)
                        :initial-element `(,(acl2s::fix-intern$ "X" pkg)))
             nil
             undef-pred-bodies)
            (make-derived-tvar-type-defthms undef-pred-names undef-texps pkg))))

(def-const *poly-combinators* '(listof alistof map))

;map: pred name -> actual tvar comb exp
(table derived-pred->poly-texp-map nil)

(defloop table-put-events (tble-name keys vals)
  (for ((key in keys) (val in vals))
       (collect `(TABLE ,tble-name ',key ',val :put))))

(def-const *sig-singular-dominant-poly-comb-limitation-msg*
"~| SIG: Limitation -- There should be one polymorphic combinator argument that dominates all other arguments. ~
But ~x0 does not have this property. Therefore we are unable to functionally instantiate this polymorphic signature. ~
Please send this example to the implementors for considering removal of this restriction.~%")

(defun all-tvars (texp)
  (intersection-eq (strip-cdrs *tvar-typename-alist*) (all-vars texp)))

(defun all-tvars-lst (texps)
  (intersection-eq (strip-cdrs *tvar-typename-alist*)
                   (all-vars1-lst texps '())))

(defun poly-type-size (ptype)
  (if (atom ptype)
      0
    (case (car ptype)
      (oneof 1) ; TODO
      (listof (+ 2 (poly-type-size (cadr ptype))))
      (alistof (+ 3 (+ (poly-type-size (second ptype))
                       (poly-type-size (third ptype)))))
      (map (+ 4 (+ (poly-type-size (second ptype))
                   (poly-type-size (third ptype)))))
      (t 0))))

(defun choose-largest-poly-type (ptypes ans)
  (if (endp ptypes)
      ans
    (if (> (poly-type-size (car ptypes)) (poly-type-size ans))
        (choose-largest-poly-type (cdr ptypes) (car ptypes))
      (choose-largest-poly-type (cdr ptypes) ans))))

(defun pick-dominant-poly-type-expr1 (ptypes all-tvars answers)
  (if (endp ptypes)
      (choose-largest-poly-type answers (car answers))
    (if (subsetp all-tvars (all-tvars (car ptypes)))
        (pick-dominant-poly-type-expr1
         (cdr ptypes) all-tvars (cons (car ptypes) answers))
      (pick-dominant-poly-type-expr1 (cdr ptypes) all-tvars answers))))

(defun pick-dominant-poly-type-expr (ptypes)
  (pick-dominant-poly-type-expr1 ptypes (all-tvars-lst  ptypes) nil))

(defun make-table-append-event2 (tble-name key1 key2 val wrld)
  (b* ((A (table-alist tble-name wrld))
       (existing-alst (get1 key1 A))
       (new-val (append (get1 key2 existing-alst) val))
       (new-alst (put-assoc-eq key2 new-val existing-alst)))
    `(TABLE ,tble-name ',key1 ',new-alst :put)))

(defun filter-texps-with-vars (texps)
  "Filter from normalized texps, the ones which have :a, :b, ... type vars"
  (if (endp texps)
      '()
    (if (consp (all-tvars (car texps)))
        (cons (car texps) (filter-texps-with-vars (cdr texps)))
      (filter-texps-with-vars (cdr texps)))))

(defun register-poly-sig-events (nm atypes rtype templ wrld)
;sig: proper-symbol * texps * texp * template * world -> events
  (b* ((dom-type (pick-dominant-poly-type-expr (append atypes (list rtype))))
;[2015-01-11 Sun] Dont ignore return type here.
       (- (cw? nil "dom-type: ~x0 nm: ~x1" dom-type nm))
       ((when (null dom-type))
        (prog2$ (cw *sig-singular-dominant-poly-comb-limitation-msg*
                    (cons rtype atypes))
                nil)))
    (and
     (consp dom-type)
     (b* ((pcomb (car dom-type))
          ((unless (member-eq pcomb *poly-combinators*))
           (prog2$
            (cw "~x0 currently does not have polymorphic support. Skipping..." pcomb)
            nil))
          (vtypes (filter-texps-with-vars
                   (remove-duplicates-equal (cons rtype atypes))))
          (vtnames (to-symbols vtypes "DEFDATA"))
          (vpreds (make-predicate-symbol-lst vtnames "DEFDATA")))
; now add a table entry to type-var table to map arg-pred names to their arg-types, this will help find the correct instantiation alist.
; then add the template to the corresponding user-combinator polymorphic-events entry!
       `(,@(table-put-events 'derived-pred->poly-texp-map vpreds vtypes)
         ;;possibly redundant
         ,@(table-put-events
            'tvar-metadata-table
            vtnames
            (strip-cdrs (type-metadata-bases vtnames "DEFDATA")))
         ,(make-table-append-event2
           'user-combinator-table pcomb
           :polymorphic-events templ wrld))))))

(defun find-type-name (texp M)
  (if (endp M)
      :undefined
    (b* (((cons tname al) (car M))
         (pdef (get1 :prettyified-def al)))
      (if (equal texp pdef)
          ;;a very strong check == we should have a weaker (better) equality
          tname
        (find-type-name texp (cdr M))))))

;get typenames for certain type expressions e.g (listof nat) has the type name nat-list

(defloop find-type-names1 (texps M)
  (for ((texp in texps))
       (collect (if (and (proper-symbolp texp) (assoc-eq texp M))
                    texp
                  (find-type-name texp M)))))

(defun remove-exprs-with-fns (psigs fns)
  (if (endp psigs)
      '()
    (if (intersection-eq (acl2::all-fnnames (car psigs)) fns)
        (remove-exprs-with-fns (cdr psigs) fns)
      (cons (car psigs)
            (remove-exprs-with-fns (cdr psigs) fns)))))

(defun subst-vals (map sigma)
  "apply sigma to all values in map"
  (if (endp map)
      '()
    (b* (((cons key val) (car map))
         (val~ (acl2::sublis-var sigma val)))
      (cons (cons key val~)
            (subst-vals (cdr map) sigma)))))

; refactor these two functions TODO
(defun undefined-preds (pred->tname-map)
  "return all keys marked :undefined"
  (if (endp pred->tname-map)
      '()
    (if (equal (cdr (car pred->tname-map)) :undefined)
        (cons (caar pred->tname-map)
              (undefined-preds (cdr pred->tname-map)))
      (undefined-preds (cdr pred->tname-map)))))

(defun remove-undefined (map)
"remove all values marked :undefined"
  (if (endp map)
      '()
    (if (equal (cdr (car map)) :undefined)
        (remove-undefined (cdr map))
      (cons (car map)
            (remove-undefined (cdr map))))))

(defun predicate-name/lambda (type A M)
  "find predicate characterization for type (either a symbol or a quoted
constant). In the latter return a lambda expression"
  (declare (xargs :guard (and (or (proper-symbolp type)
                                  (possible-constant-value-p type))
                              (symbol-alistp M))))
  (cond ((proper-symbolp type) (predicate-name type A M))
        ((possible-constant-value-p type) `(lambda (x) (equal x ,type)))
        (t nil)))

(defloop predicate-names/lambdas (types A M)
  (for ((type in types)) (collect (predicate-name/lambda type A M))))

(defun dlistify (alist)
  (declare (xargs :guard (alistp alist)))
  (list-up-lists (strip-cars alist) (strip-cdrs alist)))

(defun polypred-instantiated-pred-alist (ppred->tname-map new-types wrld)
  (b* ((M (append (table-alist 'tvar-metadata-table wrld)
                  new-types
                  (table-alist 'type-metadata-table wrld)))
       (A (table-alist 'type-alias-table wrld))
       (inst-preds (predicate-names (strip-cdrs ppred->tname-map) A M)))
    (pairlis$ (strip-cars ppred->tname-map) inst-preds)))

(defun functional-instantiation-list
    (ppred->tname-map tvar-sigma new-types kwd-alist wrld)
  (b* ((M (append (table-alist 'tvar-metadata-table wrld)
                  new-types
                  (table-alist 'type-metadata-table wrld)))
       (A (table-alist 'type-alias-table wrld))
       (A1 (pairlis$
            (predicate-names/lambdas
             (acl2::sublis-var-lst *tvar-typename-alist*
                                   (strip-cars tvar-sigma))
             A
             M)
            (predicate-names/lambdas (strip-cdrs tvar-sigma) A M)))

       (A2 (polypred-instantiated-pred-alist ppred->tname-map new-types wrld))
       (ans (union-alist2 A2 A1)) ;A2 overrides A1
       (ctx 'functional-instantiation-alist)
       (- (cw? (and (or t (get1 :verbose kwd-alist t))
                    (not (alist-equiv ans (union-alist2 A1 A2))))
               "~|Defdata/Warning:: ~x0 - tvar-sigma ~x1 entries differ from ppred-instpred-map ~x2" ctx A1 A2))
       )
    (dlistify (remove-duplicates-equal ans))))

(defun polypred-typename-map (tvar-sigma derived-pred->poly-texp-map new-types wrld)
  (b* ((ppred->texp-map (subst-vals derived-pred->poly-texp-map tvar-sigma))
       (M (append new-types (table-alist 'type-metadata-table wrld))))
    (pairlis$ (strip-cars ppred->texp-map)
              (find-type-names1 (strip-cdrs ppred->texp-map) M))))

(defloop filter-proper-symbols (xs)
  (for ((x in xs)) (append (and (proper-symbolp x) (list x)))))

(defloop filter-true-lists (xs wrld)
  (for ((x in xs)) (append (and (subtype-p x 'acl2::true-listp wrld) (list x)))))

(defun psig-templ-instantiation-ev-user
    (tname tvar-sigma templ derived-pred->poly-texp-map new-types kwd-alist wrld)
  "For given tvar-sigma, find functional instantiation and return instantiated templ"
  (b* ((ppred->tname-map
        (polypred-typename-map
         tvar-sigma
         derived-pred->poly-texp-map
         new-types
         wrld))
; remove signatures that have no match
       (templ (remove-exprs-with-fns
               templ
               (undefined-preds ppred->tname-map)))

       (fun-inst-dlist
        (functional-instantiation-list
         (remove-undefined ppred->tname-map)
         tvar-sigma
         new-types
         kwd-alist
         wrld))

       (A (table-alist 'type-alias-table wrld))
       (pred (predicate-name
              tname
              A
              (append new-types (table-alist 'type-metadata-table wrld))))
       (disabled (remove-eq
                  pred
                  (union-eq (filter-proper-symbols (strip-cadrs fun-inst-dlist))
                            (get1 :disabled kwd-alist))))
       (disabled (set-difference-eq
                  disabled
                  (filter-true-lists disabled wrld))) ;hack to fix an acl2s-issue. TODO
       (enabled (and pred (list pred))) ;TODO.check later
       (splice-alist
        `((_ENABLED-RUNES_ . ,enabled)
          (_DISABLED-RUNES_ . ,disabled)
          (_FUN-INST-ALIST_ . ,fun-inst-dlist)))
       (ppred-inst-pred-alist
        (polypred-instantiated-pred-alist ppred->tname-map new-types wrld))
       (atom-alist (acons '_PRED_ pred ppred-inst-pred-alist))
       (str-alist (acons "_PRED_"  (symbol-name pred) '())))
    (template-subst templ
                    :features nil
                    :splice-alist splice-alist
                    :atom-alist atom-alist
                    :str-alist str-alist
;The original function name should be used to avoid name clashes e.g between acl2s::rev and acl2::rev
                    :pkg-sym (acl2s::fix-intern$
                              "a" (get1 :current-package kwd-alist)))))

(defttag t)
(defattach (psig-templ-instantiation-ev
            psig-templ-instantiation-ev-user)
  :skip-checks t)
(defttag nil)

(defloop psig-templ-instantiation-events
  (ps templ derived-pred->poly-texp-map new-types kwd-alist wrld)
  (for ((p in ps))
       (append (psig-templ-instantiation-ev
                (car p)
                (cdr p)
                templ
                derived-pred->poly-texp-map
                new-types
                kwd-alist
                wrld))))

;       (n-ret-type (parse-top-texp '* return-type1 ctx wrld))
;       (p-ret-type (untrans-texp '* n-ret-type ctx wrld))

(def-const *map-all-to-a*
  (pairlis$ *allowed-type-vars*
            (make-list (len *allowed-type-vars*)
                       :initial-element ':a)))

(mutual-recursion
 (defun simplify-prop-comb-texp (pdef)
   (cond ((atom pdef) pdef)
         ((possible-constant-value-p pdef) pdef)
         ((member-eq (car pdef) '(or and oneof anyof))
          (b* ((rest (remove-duplicates-equal (simplify-prop-comb-texps (cdr pdef)))))
            (if (consp (cdr rest))
                (cons 'or rest)
              (car rest))))
         (t (cons (car pdef) (simplify-prop-comb-texps (cdr pdef))))))

 (defun simplify-prop-comb-texps (texps)
   (if (endp texps)
       '()
     (cons (simplify-prop-comb-texp (car texps))
           (simplify-prop-comb-texps (cdr texps)))))
 )


(defun find-match (ptype pdef)
  (b* ((pdef (remove-names pdef))
       ((mv yes sigma) (one-way-unify ptype pdef))
       ((when yes) (mv t sigma)))
;exceptional hack
    (if (eq (car ptype) 'LISTOF)
        (b* (((mv yes sigma)
              (one-way-unify
               ptype
               (simplify-prop-comb-texp (acl2::sublis-var *map-all-to-a* pdef))))
             ((unless yes) (mv yes sigma))
             (val (cdr (car sigma))) ;the lone :a mapped value
             (tvars (all-vars pdef))
             (sigma (pairlis$ tvars (make-list (len tvars) :initial-element val))))
          (mv t sigma))
      (mv nil nil))))

(defun find-matches1 (ptype M)
  (if (endp M)
      '()
    (b* (((cons tname al) (car M))
         (pdef (get1 :prettyified-def al))
         ((unless pdef)
          (find-matches1 ptype (cdr M))) ;skip types with NIL prettyified-def
         ((mv yes sigma) (find-match ptype pdef)))
      (if yes
          (cons (cons tname sigma) (find-matches1 ptype (cdr M)))
        (find-matches1 ptype (cdr M))))))

(defun find-matches (ptype wrld)
  (find-matches1
   ptype
   (table-alist 'type-metadata-table wrld)))

(defun find/make-type-name (ptexp M)
  (if (and (proper-symbolp ptexp)
           (assoc ptexp M))
      ptexp
    (to-symbol ptexp "DEFDATA")))

(defloop find/make-type-names (ptexps M)
  (for ((ptexp in ptexps)) (collect (find/make-type-name ptexp M))))

(defun find/make-predicate-name (tname A M)
  (or (predicate-name tname A M)
      (make-predicate-symbol tname (symbol-package-name tname))))

(defloop find/make-predicate-names (tnames A M)
  (for ((tname in tnames)) (collect (find/make-predicate-name tname A M))))

(defun instantiate-poly-sig-events-for-current-types
    (as rtype templ kwd-alist wrld)
  "limited/linear instantiation of poly signatures for all current types of same shape"
  (declare (ignorable rtype))
  (b* ((atype (pick-dominant-poly-type-expr (append as (list rtype)))) ;[2014-11-25 Tue] Dont ignore return type here.
       ((when (null atype)) nil) ;msg has been already shown
       ((when (symbolp atype)) nil) ;TODO.generalize restrict free/single-variable matches.
       (tname-IA-alst (find-matches atype wrld)) ;get type -> (alistof tvar pred)  mapping
       (M (append (table-alist 'tvar-metadata-table wrld)
                  (table-alist 'type-metadata-table wrld)))
       (A (table-alist 'type-alias-table wrld))
       (arg-tnames (find/make-type-names (remove-names-lst as) M))
       (arg-preds (find/make-predicate-names arg-tnames A M))
       (ret-tname (find/make-type-name (remove-names rtype) M))
       (ret-pred (find/make-predicate-name ret-tname A M))
       (derived-pred->poly-texp-map
        (cons (cons ret-pred rtype) (pairlis$ arg-preds as)))
       )
    (psig-templ-instantiation-events
     tname-IA-alst
     templ
     derived-pred->poly-texp-map
     '()
     kwd-alist
     wrld)))

(defloop untrans-top-texps (nms nexps)
  (for ((nm in nms) (nexp in nexps))
       (collect (untrans-top-texp nm nexp '()))))

(defun make-sig-defthm-body (name arg-types ret-type kwd-alist wrld)
  (b* ((M (append (table-alist 'tvar-metadata-table wrld)
                  (table-alist 'type-metadata-table wrld)))
       (A (table-alist 'type-alias-table wrld))
       (arg-tnames (find/make-type-names (remove-names-lst arg-types) M))
       (arg-preds (find/make-predicate-names arg-tnames A M))
       (ret-tname (find/make-type-name (remove-names ret-type) M))
       (ret-pred (find/make-predicate-name ret-tname A M))
       (pkg (get1 :current-package kwd-alist))

       (x1--xk (numbered-vars (acl2s::fix-intern$ "X" pkg) (len arg-preds)))
       (dependent-hyps (get1 :satisfies kwd-alist)) ;they should only use x1, x2 etc
       (hyps (append (list-up-lists arg-preds x1--xk) dependent-hyps))
       (psig-defthm-body `(IMPLIES (AND . ,hyps)
                                   ,(list ret-pred (cons name x1--xk)))))
    psig-defthm-body))

(mutual-recursion
 (defun find-all-instances (pat term alists)
   (declare (xargs :mode :program))
   (mv-let
    (instancep alist)
    (acl2::one-way-unify pat term)
    (let ((alists
           (if instancep
               (acl2::add-to-set-equal alist alists)
             alists)))
      (cond
       ((acl2::variablep term) alists)
       ((acl2::fquotep term) alists)
       (t (find-all-instances-list pat (acl2::fargs term) alists))))))

 (defun find-all-instances-list (pat list-of-terms alists)
   (declare (xargs :mode :program))
   (cond
    ((null list-of-terms) alists)
    (t (find-all-instances
        pat
        (car list-of-terms)
        (find-all-instances-list
         pat (cdr list-of-terms) alists))))))

(defun map-find-all-instances-list (pats list-of-terms acc)
  (declare (xargs :mode :program))
  (if (endp  pats)
      acc
    (let ((instances
           (find-all-instances-list (car pats) list-of-terms nil)))
      (if instances
          (map-find-all-instances-list
           (cdr pats)
           list-of-terms
           (cons instances acc))
        nil))))

(defun common-instancesp (x y)
  (and (consp x)
       (or (member-equal (car x) y)
           (common-instancesp (cdr x) y))))

(defun in-all (a L)
  (or (atom L)
      (and (member-equal a (car L))
           (in-all a (cdr L)))))

(defun common-instances-listp (L)
  (cond ((atom (car L)) nil)
        ((atom (cdr L)) (consp (car L)))
        (t (or (in-all (caar L) (cdr L))
               (common-instances-listp (cons (cdar L) (cdr L)))))))
#|
(defun make-sig-hint-body (name arg-types poly-gen-name kwd-alist wrld)
  (b* ((M (append (table-alist 'tvar-metadata-table wrld)
                  (table-alist 'type-metadata-table wrld)))
       (A (table-alist 'type-alias-table wrld))
       (arg-tnames (find/make-type-names (remove-names-lst arg-types) M))
       (arg-preds (find/make-predicate-names arg-tnames A M))
       (pkg (get1 :current-package kwd-alist))

       (x1--xk (numbered-vars (acl2s::fix-intern$ "X" pkg) (len arg-preds)))
       (dependent-hyps (get1 :satisfies kwd-alist)) ;they should only use x1, x2 etc
       (hyps (append (list-up-lists arg-preds x1--xk) dependent-hyps))
       (psig-hint-body
        `(if (and stable-under-simplificationp
                  (b* ((instances-name
                        (find-all-instances-list
                         '(,name ,@x1--xk) clause nil))
                       ((unless instances-name) nil)
                       (map-instances
                        (map-find-all-instances-list ',hyps clause nil))
                       ((unless map-instances) nil)
                       (common-insts (common-instances-listp
                                      (cons instances-name map-instances))))
                    common-insts))
             ;; Left this here in case I come back and want to trace the code
             ;;(prog2$ (cw "~%*****Chint ~x0, Clause: ~x1~%" ',poly-gen-name clause)
             '(:in-theory (enable ,poly-gen-name))
           ;;)
          ;; (prog2$ (cw "~%XXXXXChint ~x0, Clause: ~x1, ~x2~%"
          ;;             ',poly-gen-name clause stable-under-simplificationp)
           nil)))
    ;;)
    psig-hint-body))
|#

(defun make-sig-hint-body (name arg-types poly-gen-name kwd-alist wrld)
  (b* ((M (append (table-alist 'tvar-metadata-table wrld)
                  (table-alist 'type-metadata-table wrld)))
       (A (table-alist 'type-alias-table wrld))
       (arg-tnames (find/make-type-names (remove-names-lst arg-types) M))
       (arg-preds (find/make-predicate-names arg-tnames A M))
       (pkg (get1 :current-package kwd-alist))

       (x1--xk (numbered-vars (acl2s::fix-intern$ "X" pkg) (len arg-preds)))
       (dependent-hyps (get1 :satisfies kwd-alist)) ;they should only use x1, x2 etc
       (hyps (append (list-up-lists arg-preds x1--xk) dependent-hyps))
       (psig-hint-body
        `(if (and stable-under-simplificationp
                  (member-eq
                   (acl2::access acl2::history-entry (car hist) :processor)
                   '(acl2::fertilize-clause acl2::simplify-clause))
                  (b* ((instances-name
                        (find-all-instances-list
                         '(,name ,@x1--xk) clause nil))
                       ((unless instances-name) nil)
                       (map-instances
                        (map-find-all-instances-list ',hyps clause nil))
                       ((unless map-instances) nil)
                       (common-insts (common-instances-listp
                                      (cons instances-name map-instances))))
                    common-insts))
             ;; Left this here in case I come back and want to trace the code
             ;;(prog2$ (cw "~%*****Chint ~x0, Clause: ~x1~%" ',poly-gen-name clause)
             '(:in-theory (enable ,poly-gen-name))
           ;;)
          ;; (prog2$ (cw "~%XXXXXChint ~x0, Clause: ~x1, ~x2~%"
          ;;             ',poly-gen-name clause stable-under-simplificationp)
           nil)))
    ;;)
    psig-hint-body))

(defun sig-events1 (name suffix arg-types ret-type kwd-alist ctx wrld)
  (b* ((arg-type-list1 (acl2::sublis-var-lst *tvar-typename-alist* arg-types))
       (return-type1 (acl2::sublis-var *tvar-typename-alist* ret-type)) ;instead of *allowed-type-var->named-type-binding*
       (arity (len arg-types))
       (pkg (get1 :current-package kwd-alist))
       (star (acl2s::fix-intern$ "*" pkg))
       (stars (make-list arity :initial-element star))
       (n-arg-types (parse-top-texps stars arg-type-list1 ctx wrld))
       (n-ret-type (parse-top-texp star return-type1 (list star) ctx wrld))
       (p-arg-types (untrans-top-texps stars n-arg-types))
       (p-ret-type (untrans-top-texp star n-ret-type '()))

       (name-pre (if suffix (s+ name '- suffix :pkg pkg) name))
       (psig-name (s+ name-pre "-POLYMORPHIC-SIG" :pkg pkg))
       (poly-inst-name (s+ name-pre "-_PRED_-SIG" :pkg pkg))
       (poly-gen-name (s+ name-pre "-_PRED_-GENRULE-SIG" :pkg pkg))
       (poly-hint-name (s+ name-pre "-_PRED_-GENRULE-HINT-SIG" :pkg pkg))
       (psig-defthm-body
        (make-sig-defthm-body name p-arg-types p-ret-type kwd-alist wrld))
       (psig-hint-body
        (make-sig-hint-body name p-arg-types poly-gen-name kwd-alist wrld))
       (poly-inst-template
        `((DEFTHM ,poly-inst-name
            ,psig-defthm-body
            :hints (("Goal"
                     :in-theory (e/d (_ENABLED-RUNES_) (,name _DISABLED-RUNES_))
                     :use ((:functional-instance ,psig-name
                                                 _fun-inst-alist_))))
            :rule-classes ,(get1 :rule-classes kwd-alist '(:rewrite)))))
       (poly-gen-template
        `((DEFTHMD ,poly-gen-name
            ,psig-defthm-body
            :hints (("Goal" :by ,poly-inst-name))
            :rule-classes :generalize)))
;       (- (cw "args: ~x0 ret: ~x1 derived-pred->poly-texp-map: ~x2 templ: ~x3" p-arg-types p-ret-type derived-pred->poly-texp-map poly-inst-template))

       (poly-hints-defun
        `((defun ,poly-hint-name
              (clause stable-under-simplificationp id hist pspv ctx)
            (declare (ignorable id hist pspv ctx)) ; may need later
            (declare (xargs :mode :program))
            ,psig-hint-body)
          ))

       (poly-computed-hints
        `((add-default-hints!
           '((,poly-hint-name clause stable-under-simplificationp id hist pspv ctx))
           ;:at-end t
           )))
       )

    `(,@(make-sig-tvar-support-events (cons p-ret-type p-arg-types) ctx pkg wrld)

      (DEFTHM ,psig-name  ;restriction: only one sig per function possible!
        ,psig-defthm-body
        :hints ,(or (get1 :hints kwd-alist)  `(("Goal" :in-theory (enable ,name))))
        :rule-classes ,(get1 :gen-rule-classes kwd-alist '(:rewrite)))

; for functional instantiating of future types of same shape
      ,@(register-poly-sig-events name p-arg-types p-ret-type poly-inst-template wrld)

; functionally instantiate all current types of same shape
      ,@(instantiate-poly-sig-events-for-current-types
         p-arg-types
         p-ret-type
         poly-inst-template
         kwd-alist
         wrld)

; functionally generalizations
      ,@(instantiate-poly-sig-events-for-current-types
         p-arg-types
         p-ret-type
         poly-gen-template
         kwd-alist
         wrld)

; computed hints
      ,@(instantiate-poly-sig-events-for-current-types
         p-arg-types
         p-ret-type
         poly-hints-defun
         kwd-alist
         wrld)

      ,@(instantiate-poly-sig-events-for-current-types
         p-arg-types
         p-ret-type
         poly-computed-hints
         kwd-alist
         wrld)
      )))

(defun sig-events (parsed wrld)
  (b* (((list name suffix arg-types ret-type kwd-alist) parsed)
       (cgenp (acl2::logical-namep 'acl2s::acl2s-defaults wrld))
       ;; dont even call acl2s-defaults if cgen/top is not included. This
       ;; allows defdata/sig to be used independently of cgen
       (local-testing-downgraded-form
        (and cgenp
             '((LOCAL (ACL2S::ACL2S-DEFAULTS :SET ACL2S::TESTING-ENABLED nil))))))
    `(WITH-OUTPUT
      :on (acl2::summary acl2::error acl2::comment)
      :SUMMARY-OFF (:OTHER-THAN ACL2::FORM)
      (ENCAPSULATE
       NIL
       (logic)
       ,@local-testing-downgraded-form
       ,@(sig-events1 name suffix arg-types ret-type kwd-alist 'sig wrld)))))

(defmacro sig (&rest args)
  (b* ((verbose (let ((lst (member :verbose args)))
                  (and lst (cadr lst)))))
    `(with-output
      ,@(and (not verbose) '(:off :all :on comment))
      :gag-mode t
      :stack :push
      (make-event
       (sig-events
        (parse-sig ',args (current-package state) 'sig (w state)) (w state))))))
