; Syntheto Library
;
; Copyright (C) 2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Authors: Eric McCarthy (mccarthy@kestrel.edu) and Stephen Westfold (westfold@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Translator for syntheto functions.

;; See the UML diagram:
;; https://git.isis.vanderbilt.edu/midas/acl2.xtext/-/blob/devel/abstract-syntax/functions-uml.png

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "SYNTHETO")

(include-book "types")
(include-book "expressions")
(include-book "kestrel/utilities/doublets" :dir :system)
(include-book "kestrel/untranslated-terms-old/untranslated-terms" :dir :system)
;(include-book "kestrel/lists-light/len" :dir :system) ; Causes circularity!!
(include-book "std/strings/suffixp" :dir :system)
(include-book "std/strings/strpos" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Heuristics for enabling functions

(define filter-out-non-fty-fns ((l symbol-listp))
  :returns (ll symbol-listp :hyp :guard)
  (if (endp l)
      ()
    (b* (((cons sym tl) l)
         (r (filter-out-non-fty-fns tl))
         (nm-str (symbol-name sym)))
      (if (and (equal (symbol-package-name sym)
                      "SYNDEF")
               (or (str::strsuffixp "-P" nm-str)
                   (str::strpos "->" nm-str)
                   (str::strpos "MAKE-" nm-str)))
          r
        (cons sym r)))))

(defconst *s-theorem-dont-enable-fns*
  '(- equal implies endp not len and or cond if + car cdr >= > <= < list cons
      integerp booleanp
      ;; This is a waorkaround of a bug in front end
      syndef::|append_first|
      ))

(defconst *s-theorem-enable-fns*
  '())

(define relevant-fn-names ((expr acl2::untranslated-termp))
  (let ((fns (acl2::get-called-fns-in-untranslated-term expr)))
    (and (true-listp fns)
         (append (set-difference-eq (filter-out-non-fty-fns fns)
                                    *s-theorem-dont-enable-fns*)
                 *s-theorem-enable-fns*
                 (if (member 'syndef::|closed_path_p| fns)
                     '(syndef::|path|)
                   ())))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; process input param specs

;; Each input-spec is a list of two strings ("VAR" "TYPE")
;; where "VAR" is the name of the parameter, which will be put in the SYNDEF package,
;; and "TYPE" is the type of the parameter.

(defun incorporate-condn-into-type-pred (condn type-pred v)
  (if (endp condn)
      (mv condn nil)
    (b* (((cons f args) condn)
         ((when (eq f 's-and))
          (b* (((mv c1 tp1)
                (incorporate-condn-into-type-pred (second condn) type-pred v))
               ((mv c2 tp2)
                (incorporate-condn-into-type-pred (third condn) type-pred v)))
            (mv `(s-and ,c1 ,c2) (or tp1 tp2))))
         ((when (and (member-eq f '(s-gte s-gt))
                     (natp (second args))
                     (equal type-pred '(s-type-integer))
                     (member-eq (car (first args)) '(s-var-ref s-var-ref))
                     (equal v (second (first args)))))
          (mv (if (and (eq f 's-gte)
                       (= (second args) 0))
                  '(s-literal-true)
                condn)
              'natp)))
       (mv condn nil))))

(defun process-s-fun-input (input-spec assumes)
  (b* (((unless (and (listp input-spec)
                     (consp input-spec)
                     (consp (cdr input-spec))
                     (null (cddr input-spec))
                     (stringp (first input-spec))
                     (not (equal "" (first input-spec)))))
        (mv (er hard? 'top-level "bad input-spec") nil nil nil nil))
       ((list param param-type) input-spec)
       ((mv assumes type-pred-from-assumes?)
        (incorporate-condn-into-type-pred assumes param-type param))
       (param-name (intern-syndef param))
       ;; The type must be a valid type descriptor.
       ;; However, we can't check that here, because we don't have access to the world state.
       ;; It would be good if such a check could become part of the defining event.
       (type-name (s-type-to-fty-name-symbol param-type))
       (type-pred (or type-pred-from-assumes?
                      (type-name-to-pred type-name)))
       (fixing-fn (if (equal type-pred-from-assumes? 'natp)
                      'nfix
                    (type-name-to-fix type-name))))
    (mv nil (list param-name type-pred)
        (list param-name (list fixing-fn param-name))
        (list param-type)
        assumes)
    ))

(assert-event (mv-let (erp param-spec fixer types assumes)
                  (process-s-fun-input '("X" (s-type-integer)) nil)
                (equal (list erp param-spec fixer types assumes)
                       '(NIL (SYNDEF::X INTEGERP)
                             (SYNDEF::X (IFIX SYNDEF::X))
                             ((s-type-integer))
                             NIL))))

(defun process-s-fun-inputs (input-specs assumes)
  (b* (((when (endp input-specs))
        (mv nil nil nil nil assumes))
       ((mv erp param fix-binding new-types assumes)
        (process-s-fun-input (car input-specs) assumes))
       ((when erp) (mv t nil nil nil nil))
       ((mv erp params fix-bindings rec-types assumes)
        (process-s-fun-inputs (cdr input-specs) assumes))
       ((when erp) (mv t nil nil nil nil)))
    (mv nil (cons param params)
        (cons fix-binding fix-bindings)
        (append new-types rec-types)
        assumes)))

(assert-event (mv-let (erp param-specs fixers types assumes)
                  (process-s-fun-inputs '(("X" (s-type-character)) ("Y" (s-type-string)) ("Z" (s-type-boolean))
                                          ("A" (s-type-ref "SOMETHING-ELSE")))
                                        nil)
                (equal (list erp param-specs fixers types assumes)
                       '(NIL ((SYNDEF::X CHARACTERP) (SYNDEF::Y STRINGP) (SYNDEF::Z BOOLEANP)
                              (SYNDEF::A SYNDEF::SOMETHING-ELSE-P))
                             ((SYNDEF::X (CHAR-FIX SYNDEF::X))
                              (SYNDEF::Y (STR-FIX SYNDEF::Y))
                              (SYNDEF::Z (BOOL-FIX SYNDEF::Z))
                              (SYNDEF::A (SYNDEF::SOMETHING-ELSE-FIX SYNDEF::A)))
                             ((s-type-character) (s-type-string) (s-type-boolean) (s-type-ref "SOMETHING-ELSE"))
                             NIL))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; process output specs, for the :returns specifier

(defun process-s-fun-output (output-spec ensures)
  (b* (((unless (and (listp output-spec)
                     (consp output-spec)
                     (consp (cdr output-spec))
                     (null (cddr output-spec))
                     (stringp (first output-spec))
                     (not (equal "" (first output-spec)))))
        (mv (er hard? 'top-level "bad output spec") nil nil nil nil))
       ((list output-var output-type) output-spec)
       ((mv ensures type-pred-from-ensures?)
        (incorporate-condn-into-type-pred ensures output-type output-var))
       (output-var-name (intern-syndef (first output-spec)))
       (new-type (second output-spec))
       (type-name (s-type-to-fty-name-symbol new-type))
       (type-pred (or type-pred-from-ensures?
                      (type-name-to-pred type-name)))
       (fixing-fn (type-name-to-fix type-name)))
    (mv nil `(,output-var-name ,type-pred :hyp :guard) fixing-fn (list new-type) ensures)))

(assert-event (mv-let (erp return-spec fixer types ensures)
                  (process-s-fun-output '("R" (s-type-integer)) NIL)
                (equal (list erp return-spec fixer types ensures)
                       '(NIL (SYNDEF::R INTEGERP :HYP :GUARD)
                             IFIX ((S-TYPE-INTEGER)) NIL))))

(defun process-s-fun-outputs (output-specs ensures)
  ;; Currently, there must be exactly one output spec.
  (b* (((when (endp output-specs))
        (mv t nil nil nil ensures))
       ((when (consp (cdr output-specs)))
        (mv t nil nil nil ensures))
       ((mv erp return-spec output-fixer new-types ensures)
        (process-s-fun-output (car output-specs) ensures))
       ((when erp) (mv t nil nil nil nil))
       ;; we would do something like this if we allowed more than one output spec.
       ;; But then we would probably need a top-level process-.. and a recursive process-..
       ;; ((mv erp return-specs output-fixers) (process-s-fun-outputs (cdr output-specs)))
       )
    (mv nil (list return-spec) output-fixer new-types ensures)))

(assert-event (mv-let (erp return-specs fixer types ensures)
                  (process-s-fun-outputs '(("R" (s-type-integer))) nil)
                (equal (list erp return-specs fixer types ensures)
                       '(NIL ((SYNDEF::R INTEGERP :HYP :GUARD))
                             IFIX
                             ((S-TYPE-INTEGER)) NIL))))

;; Returns all calls to fns in tm
(defun get-calls-to-fns (fns tm)
  (if (atom tm)
      ()
    (case-match tm
      (('s-call f . args)
       (let ((rec-calls (get-calls-to-fns fns args)))
         (if (member-equal f fns)
             (cons tm rec-calls)
           rec-calls)))
      (&  ; crude but should be safe
       (append (get-calls-to-fns fns (car tm)) 
               (get-calls-to-fns fns (cdr tm)))))))

;; Not used currently
;; (defun expand-lets (tm sb)
;;   (if (atom tm)
;;       tm
;;     (case-match tm
;;       (('s-var-ref v)
;;        (let ((v-rep (acl2::lookup-equal v sb)))
;;          (if (consp v-rep)
;;              (car v-rep)
;;            tm)))
;;       (('s-let binds body)
;;        (let ((rep-binds (expand-lets binds sb))) ; First substitute vars in binds
;;          (expand-lets body (append rep-binds sb))))
;;       (& (cons (expand-lets (car tm) sb)
;;                (expand-lets (cdr tm) sb))))))

;; (acl2::assert-equal (expand-lets '(s-let (("x" (s-var-ref "v")))
;;                                          (s-let (("x" (s-tail (s-var-ref "x")))
;;                                                  ("y" (s-tail (s-var-ref "x"))))
;;                                                 (s-let (("y" (s-head (s-var-ref "x"))))
;;                                                        (s-conditional (s-var-ref "v")
;;                                                                       (s-var-ref "x")
;;                                                                       (s-var-ref "y")))))
;;                                  ())
;;                     '(s-conditional (s-var-ref "v")
;;                                     (s-tail (s-var-ref "v"))
;;                                     (s-head (s-tail (s-var-ref "v")))))

(defun map-strip-cars (l)
  (if (endp l)
      ()
    (cons (strip-cars (car l))
          (map-strip-cars (cdr l)))))

(defconst *arith-ops*
  '(+ - * acl2::truncate acl2::rem))

(defun term-contains-arithmetic (tm)
  (intersection-eq *arith-ops* (acl2::get-called-fns-in-untranslated-term tm)))

(defun preds-from-typed-vars (params)
  (declare (xargs :mode :program))
  (if (endp params)
      ()
    (cons `(,(second (car params))
            ,(first (car params)))
          (preds-from-typed-vars (cdr params)))))

(defun set-or-sequence-type (simple-return-type)
  (and (symbolp simple-return-type)
       (equal (symbol-package-name simple-return-type)
              "SYNDEF")
       (or (str::strpos "SEQUENCE[" (symbol-name simple-return-type))
           (str::strpos "SET[" (symbol-name simple-return-type)))))

(define default-integer ()
  0)
(define default-nil ()
  nil)

(defun constant-termp (tm)
  (atom tm))                            ; Could extend

(defun restrict-body (body guard-terms simple-return-type)
  (if (endp guard-terms)
      body
    (case-match body
      (('and . conds)
       `(and ,@guard-terms ,@conds))
      (& (if (eq simple-return-type 'booleanp)
             `(and ,@guard-terms ,body)
           (or (case-match body
                 (('if condn then-cl else-cl)
                  (and (constant-termp then-cl)
                       `(if (or (not (mbt (and ,@guard-terms)))
                                ,condn)
                            ,then-cl ,else-cl))))
               `(if (mbt (and ,@guard-terms))
                    ,body
                  ,(if (eq simple-return-type 'integerp)
                       '(default-integer)
                     (if (set-or-sequence-type simple-return-type)
                         '(default-nil)
                       ':undefined)))))))))

(defun simple-bodyp (body)
  (and (not (and (consp body)
                 (member (car body) '(if cond))))
       (< (acl2-count body) 15)))

(defun enable-fun? (body predicatep fn-name)
  (and (simple-bodyp body)
       (not (equal fn-name 'syndef::|append_first|)) ; !! Workaround
       (or (not predicatep)
           (not (consp body))
           (not (member (car body) '(and or))))))

;; Avoid getting (len (nfix v))
(defun premptive-subst (sb)
  (if (endp sb)
      nil
    (let ((r (premptive-subst (cdr sb)))
          (pr (car sb)))
      (or (case-match pr
            ((v1 'acl2::nfix v2)         ; v1 and v2 should be equal
             (cons (cons `(acl2::acl2-count ,v1)
                         `(acl2::nfix ,v2))
                   r))
            )
          r))))

(set-state-ok t)

(defun guess-measure-1 (names param-lists bodies let-fixing-list state)
  (declare (xargs :mode :program))
  (b* ((t-machines (acl2::termination-machines nil nil names param-lists bodies nil))
       ((er measure-alist)
        (acl2::guess-measure-alist names (map-strip-cars param-lists)
                                   '('nil)  ; supplied measures if we add them somehow
                                   t-machines
                                   's-fun
                                   (w state)
                                   state))
       (measure-alist1 (acl2::sublis-equal (cons (cons 'acl2::acl2-count 'acl2::len)
                                                 (premptive-subst (acl2::doublets-to-alist let-fixing-list)))
                                           measure-alist)))
    (value measure-alist1)))

(defun s-fun-pre (input-types output-types)
  (declare (xargs :mode :program))
  (let ((prerequisite-type-defs (defining-forms-for-unnamed-types-in-s-exp
                                  (append input-types output-types))))
    `(with-output :off :all :on error :gag-mode t
       (progn ,@prerequisite-type-defs))))

(defun s-fun-main (namestring param-list body let-fixing-list returns-list
                              assumes ensures measure guard-debug state)
  (declare (xargs :mode :program))
  (b* ((name (intern-syndef namestring))
       (recursive? (get-calls-to-fns (list namestring) body))
       (trans-body (translate-term body))
       ((er translated-body)
        (acl2::translate trans-body nil t t 's-fun
                         (putprop name 'acl2::formals (strip-cars param-list) (w state))
                         state))
       ((er measure-alist)
        (if (and recursive? (not measure))
            (guess-measure-1 (list name) (list param-list) (list translated-body)
                             let-fixing-list state)
          (value nil)))
       (param-type-guards (preds-from-typed-vars param-list))
       (return-type-ensures (preds-from-typed-vars returns-list))
       (trans-assumes (and assumes (translate-term assumes)))
       (single-return-type (and (= (len returns-list) 1)
                                (consp (car returns-list))
                                (consp (cdar returns-list))
                                (cadar returns-list)))
       (predicatep (or (and trans-body
                            (member (car trans-body) '(and or)))
                       (equal single-return-type 'booleanp)))
       (param-list (if predicatep (strip-cars param-list) param-list))
       (guard-terms (append param-type-guards (and assumes
                                                   (not (equal trans-assumes 't))
                                                   (list trans-assumes))))
       (trans-ensures (and ensures (translate-term ensures)))
       (ensure-terms (append return-type-ensures (and ensures
                                                   (not (equal trans-ensures 't))
                                                   (list trans-ensures))))
       (measure1 (if measure
                    (sublis (acl2::doublets-to-alist let-fixing-list) (translate-term measure))
                  (acl2::lookup-eq name measure-alist)))
       (enable? (enable-fun? trans-body predicatep name))
       )
    (value `(with-output :off :all :on error :gag-mode t
              (define ,name ,param-list
                ,@(if measure1 `(:measure ,measure1) ())
                ,@(if (and guard-terms (not predicatep)) `(:guard (and ,@guard-terms)) ())
                :normalize nil
                ,@(if enable? '(:enabled t) ())
                ,@(if guard-debug '(:guard-debug t) ())
                :prepwork ((set-ignore-ok t)
                           ,@(if (and measure (term-contains-arithmetic measure1))
                                 '((local (include-book "arithmetic-5/top" :dir :system)))
                               '((local (include-book "kestrel/lists-light/len" :dir :system)))))
                :no-function t
                :returns ,(if (consp (cdr returns-list)) ; more than one
                              `(mv ,@returns-list) ; not yet being used.. some other things
                                        ; would also need to change to support mv returns
                            (car returns-list))
                ,(restrict-body trans-body guard-terms single-return-type)   ; restrict by default!
                ;; (let ,let-fixing-list
                ;;   ,trans-body)
                ///
                ,@(and ensure-terms
                       `((defret ,(intern-syndef (concatenate 'string namestring "-ENSURES"))
                           :hyp :guard
                           (and ,@ensure-terms)
                           :hints (("Goal" :in-theory (enable ,@(relevant-fn-names
                                                                 `(implies ,trans-assumes
                                                                           (and ,@ensure-terms)))))))))
                ,@(and predicatep
                       guard-terms
                       `((defthm ,(intern-syndef (concatenate 'string namestring "-IMPLIES"))
                           (implies (,name ,@param-list)
                                    (and ,@guard-terms))))))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; s-fun
;; defines a function

;; Example: define a function that adds the two params.
;;
;; (s-fun "FUN0"
;;   :inputs (("X" (s-type-integer)) ("Y" (s-type-integer)))
;;   :outputs (("R" (s-type-integer)))
;;   :body (s-plus (s-var-ref "X") (s-var-ref "Y")))


;; * inputs can be empty but if not, each input must be a pair of strings
;;   The type string must resolve to a meaningful type name.
;; * For now, we require that OUTPUTS be a list with a single pair in it.
;;   Later we may allow more than one output and wrap the output in mv
;;   We will never have zero outputs.
;; 
(defmacro s-fun (namestring &key inputs outputs ;; ensures
                            body assumes ensures measure
                            guard-debug) ; For debugging
  (b* (((mv erp param-list let-fixing-list input-types assumes)
        (process-s-fun-inputs inputs assumes))
       ((when erp) (er hard? 'top-level "Bad :inputs to s-fun"))
       ((mv erp returns-list ?output-fixer output-types ensures)
        (process-s-fun-outputs outputs ensures))
       ((when erp) (er hard? 'top-level "Bad :outputs to s-fun")))
    
    ;; This complicated structure is in order to use acl2::guess-measure-alist, but with unfixed inputs
    ;; and then substituting fixing in the resulting measure. 
    ;; Woud be unnecessary if acl2::guess-measure-alist handled fixing of arguments itself
    `(progn (make-event (s-fun-pre ',input-types ',output-types))
            ;; Above event be in world before evaluating s-fun-main
            (make-event (s-fun-main ,namestring ',param-list ',body ',let-fixing-list ',returns-list
                                    ',assumes ',ensures ',measure ',guard-debug state)))))

;; a test case
(s-fun "HTYGjEAz" :inputs (("X" (s-type-integer)) ("Y" (s-type-integer))) :outputs (("R" (s-type-integer)))
       :body (s-plus (s-var-ref "X") (s-var-ref "Y")))

(assert-event (equal 7 (syndef::|HTYGjEAz| 3 4)))

#|
(s-fun "TEST1"
       :inputs (("X" (s-type-sequence (s-type-set (s-type-integer))))
                ("Y" (s-type-set (s-type-integer))))
       :outputs (("R" (s-type-sequence (s-type-set (s-type-integer)))))
       :body (s-var-ref "X"))
|#
