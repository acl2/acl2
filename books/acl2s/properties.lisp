#|$ACL2s-Preamble$;
(include-book ;; Newline to fool ACL2/cert.pl dependency scanner
 "portcullis")
(begin-book t :ttags :all);$ACL2s-Preamble$|#

(in-package "ACL2S")
(include-book "acl2s/definec" :dir :system :ttags :all)
(include-book "acl2s/acl2s-size" :dir :system)
(include-book "acl2s/ccg/ccg" :dir :system
  :uncertified-okp nil :ttags ((:ccg))
  :load-compiled-file nil)
(include-book "base-lists")

#|

Support for propery-based design and modeling.

To use this book, you should use defunc and definec to define
functions (not defun), using defdata for datatypes.

You should also use property to define properties (not thm and
defthm). See the notes below regarding properties.

The idea is to provide support for design and modeling of systems in
ACL2s. Here are the built-in modes, but note that you can
easily define your own modes by looking at the definitions
below and updating them.

Modeling-start mode:

During the initial stages of design and modeling, there will be
various errors and we want to catch them as quickly as possible. So,
during this stage, ACL2s will accept definitions and properties as
long as there are no syntactic problems and they pass a limited amount
of testing. So, non-terminating functions will be accepted.

modeling-validate-defs mode:

Once you are happy with your model in modeling-start mode, then switch
to this mode and the idea is that ACL2s will validate definitions,
i.e., ACL2s will not skip admissibility and contract checking, but it
will also not be strict. ACL2s is also given twice the time budget as
in the previous mode. In this mode, functions whose contracts have not
been proven have their contracts checked dynamically, which can lead
to significant increases in running time.

modeling-admit-defs mode:

Once you are happy with the modeling-validate-defs mode, then switch
to this mode and ACL2s will be strict when it comes to admissibility
of definitions.  Note that it is not strict wrt properties, so if you
need named properties to admit definitions, ACL2s will accept such
properties as long as it cannot invalidate them.

modeling-admit-all mode:

Once you are happy with the modeling-admit-defs mode, then switch
to this mode and ACL2s will be strict when it comes to admissibility
of definitions and properties. Once you pass this mode,
then you have real ACL2s proofs of correctness.

As mentioned above, you have lots of flexibility because
you can choose a mode and then make project-relevant adjustments.
For example if you are in modeling-admit-all mode, but want
to just assume some properties, you can disable proofs
as follows.

(set-acl2s-property-table-proofsp nil)
(property ...)
...
(set-acl2s-property-table-proofsp t)

|#

(defun gen-property-accessors-updators (tbl a)
  (if (endp a)
      nil
    (b* ((`((,key . &) . &) a)
         (acc (make-symbl `(get- ,tbl - ,key) "ACL2S"))
         (upd (make-symbl `(set- ,tbl - ,key) "ACL2S")))
      (list*
       `(defmacro ,acc () (tbl-get-fn ',tbl ,key))
       `(defmacro ,upd (x) (tbl-set-fn ',tbl ,key x))
       (gen-property-accessors-updators tbl (cdr a))))))

(defmacro gen-property-table (default-alist)
  `(progn
     (table acl2s-property-table nil
            ',default-alist
            :clear)

     (defun acl2s-property-table (wrld)
       "api to get the alist representing property table"
       (declare (xargs :guard (plist-worldp wrld)))
       (table-alist 'acl2s-property-table wrld))

     ,@(gen-property-accessors-updators
        'acl2s-property-table
        default-alist)))

;; Generate events for a table containing settings relevant to
;; properties. Use :trans1 to see what this generates.

(def-const *property-thm-keywords*
  '(:hints :otf-flg))

(def-const *property-just-defthm-keywords*
  '(:rule-classes :instructions))

(def-const *property-core-keywords*
  '(:proofs? :proof-timeout
             :testing? :testing-timeout
             :doc
             :check-contracts? :complete-contracts?
             :debug?))

(def-const *property-conjecture-keywords*
  '(:vars :hyps :body))

(def-const *property-keywords*
  (append *property-conjecture-keywords*
          *property-core-keywords*
          *property-thm-keywords*
          *property-just-defthm-keywords*))

(gen-property-table
 ((:debug? . nil)
  (:proofs? . t)
  (:proof-timeout . 40)
  (:testing? . t)
  (:testing-timeout . 20)
  (:check-contracts? . t)
  (:complete-contracts? . t)))

#|

:trans1 (gen-property-table
         ((:proofs? . t)
          (:proof-timeout . 5)
          (:testing? . t)
          (:testing-timeout . 5)))


(table-alist 'acl2s-property-table (w state))
(defdata::get1 :proofs? (table-alist 'acl2s-property-table (w state)))
(set-acl2s-property-table-proofs? nil)
(table-alist 'acl2s-property-table (w state))
(defdata::get1 :proofs? (table-alist 'acl2s-property-table (w state)))

|#


#|

A named property is one that has a name and is treated like a defthm,
eg,

(property dumb (equal x x))

will cause an error because you cannot have a rewrite rule that
rewrites a variable.

If a property does not have a name, it is treated like a thm, so this
is fine.

(property (equal x x))

You could also do this, which shows that you can provide properties
with the same hints and directives that defthm accepts.

(property not-dumb (equal x x) :rule-classes nil)

|#

; If l has duplicate elements, return a list containing the first duplicate;
; else return nil.
(definec find-first-duplicate (l :tl) :tl
  (cond ((endp l) nil)
        ((in (car l) (cdr l)) (list (car l)))
        (t (find-first-duplicate (cdr l)))))

(sig find-first-duplicate ((listof :a)) => (listof :a))

(definec remove-dups-aux (l :tl seen :tl) :tl
  (cond ((endp l) (revappend seen nil))
        ((in (car l) seen) (remove-dups-aux (cdr l) seen))
        (t (remove-dups-aux (cdr l) (cons (car l) seen)))))

(sig remove-dups-aux ((listof :a) (listof :a)) => (listof :a))

; Remove duplicates, but leave order of elements the same
(definec remove-dups (l :tl) :tl
  (remove-dups-aux l nil))

(sig remove-dups ((listof :a)) => (listof :a))

; (remove-dups '(1 2 3 3 1 3 2 1 1 3))

#|
(definec extract-hyps (x :all) :tl
;(defun extract-hyps (x)
  (b* ((x-hyps (if (and (consp x) (equal (car x) 'implies))
                   (if (and (consp (cdr x))
                            (consp (second x))
                            (equal 'and (car (second x))))
                       (cdr (second x))
                     (list (second x)))
                 nil))
       (find-duplicate-x-hyps (find-first-duplicate x-hyps))
       (- (cw? find-duplicate-x-hyps
               "~|**Warning: Your conjecture has duplicate hypothesis, ~x0. ~
                ~%**This may indicate an error.~%"
               find-duplicate-x-hyps)))
    (remove-dups x-hyps)))
|#

(definec hyps-list-from-hyps (hyps :all) :all
  (case-match hyps
    (('and . l) l)
    (('^ . l) l)
    (& (list hyps))))

(definec extract-hyps (x :all) :tl
  :ic (simple-termp x)
  (b* ((x-hyps (case-match x
                 (('implies hyps &)
                  (hyps-list-from-hyps hyps))
                 (('=> hyps &)
                  (hyps-list-from-hyps hyps))
                 (& nil)))
       (find-duplicate-x-hyps (find-first-duplicate x-hyps))
       (- (cw? find-duplicate-x-hyps
               "~|**Warning: Your conjecture has duplicate hypothesis, ~x0. ~
                ~%**This may indicate an error."
               find-duplicate-x-hyps)))
    (remove-dups x-hyps)))

(definec extract-body (x :all) :all
  (case-match x
    (('implies & body) body)
    (('=> & body) body)
    (& x)))

(definec del1 (e :all x :tl) :tl
  (cond ((endp x) x)
        ((== e (car x)) (cdr x))
        (t (cons (car x) (del1 e (cdr x))))))

#|

I don't need this?

(definec hyps-list-to-hyp (l :ne-tl) :all
  (cond ((endp l) (list x))
        ((endp (cdr l))
         `((implies ,hyps ,x)))
        ((endp x-hyps) `((implies ,hyps ,x) ,hyps))
        (t `((implies ,hyps ,(third x)) ,hyps))))
|#

#|
(defun parse-property (args state)
  ;; Returns (list nm formals ic oc doc decls body kwd-alist)
  (declare (xargs :mode :program :stobjs (state)))
  (b* ((pkg (current-package state))
       (wrld (w state))
       (tbl (table-alist 'type-metadata-table wrld))
       (atbl (table-alist 'type-alias-table wrld))
       (ctx 'property)
       ((unless (consp args))
        (value (er hard? ctx "~| Empty properties are not allowed.~%")))
       (name? (acl2::legal-variablep (car args)))
       (name (and name? (car args)))
       (args (if name? (cdr args) args))
       (PT (acl2s-property-table wrld))
       (PT (defdata::remove1-assoc-eq-lst (filter-keywords args) PT))
       ((mv kwd-alist prop-rest)
        (defdata::extract-keywords ctx *property-keywords* args PT nil))
       (vars? (assoc :vars kwd-alist))
       (hyps? (assoc :hyps kwd-alist))
       (body? (assoc :body kwd-alist))
       ((when (and hyps? (not body?)))
        (value
         (er hard? ctx
             "~| If :hyps is provided, then :body must also be provided.~%")))
       (body (if body?
                 (defdata::get1 :body kwd-alist)
               (extract-body (car prop-rest))))
       (hyps-list (cond (hyps? (defdata::get1 :hyps kwd-alist))
                        (body? nil)
                        (t (extract-hyps (car prop-rest)))))
       (find-duplicate-hyp (find-first-duplicate hyps-list))
       (- (cw? find-duplicate-hyp
               "~|**Warning: Your property has a duplicate hypothesis, ~x0. ~
                ~%**This may indicate an error.~%"
               find-duplicate-hyp))
       (hyps-list (remove-dups hyps-list))
       (user-var-list (defdata::get1 :vars kwd-alist))
       (user-vars (evens user-var-list))
       (user-types (odds user-var-list))
       (user-types (map-intern-types user-types pkg))
       (user-preds (map-preds user-types tbl atbl))
       (type-list1 (make-input-contract user-vars user-preds))
       (type-list (hyps-list-from-hyps type-list1))
       (type-hyps-list (append type-list hyps-list))
       (prop (cond ((endp type-hyps-list) body)
                   ((endp (cdr type-hyps-list))
                    `(implies ,(car type-hyps-list) ,body))
                   (t `(implies (and ,@type-hyps-list) ,body))))
       ((mv ?erp trans-prop)
        (acl2::pseudo-translate prop nil wrld))
       (all-vars (acl2::all-vars trans-prop))
       (vars (if vars? user-vars all-vars))
       ((when (not (perm vars all-vars)))
        (value
         (er hard? ctx
             "~| The :vars provided do not match the actual variables ~
                appearing in the property.~%")))
       ((mv erp val)
        (guard-obligation prop nil nil t ctx state))
       ((when erp)
        (value (er hard? ctx "~%**Guard Error **~%"))))
    (er-let* ((foo (trans-eval `(must-succeed (thm ,val))
                               ctx
                               state
                               t)))
            (value (list name? foo name vars type-hyps-list body kwd-alist)))))
|#

(definec sym-diff (x :tl y :tl) :tl
  (app (set-difference-equal x y)
       (set-difference-equal y x)))

(definec property-varsp (x :tl) :bool
  (v (endp x)
     (^ (consp (cdr x))
        (acl2::legal-variablep (first x))
        (acl2::keywordp (second x))
        (property-varsp (cddr x)))))

; (property-varsp '(x :int y :int ))
; (defdata::get1 :vars '((:vars x :int y :int )))

(defun parse-property (args state)
  ;; Returns (list nm formals ic oc doc decls body kwd-alist)
  (declare (xargs :mode :program :stobjs (state)))
  (b* ((pkg (current-package state))
       (wrld (w state))
       (tbl (table-alist 'type-metadata-table wrld))
       (atbl (table-alist 'type-alias-table wrld))
       (ctx 'property)
       (name? (acl2::legal-variablep (car args)))
       (name (and name? (car args)))
       (args (if name? (cdr args) args))
       (PT (acl2s-property-table wrld))
       (PT (defdata::remove1-assoc-eq-lst (filter-keywords args) PT))
       ((mv kwd-alist prop-rest)
        (defdata::extract-keywords ctx *property-keywords* args PT nil))
       (debug? (defdata::get1 :debug? kwd-alist))
       (vars? (assoc :vars kwd-alist))
       (ivars? (and (! vars?)
                    (property-varsp (car prop-rest))
                    (cons :vars (car prop-rest))))
       (vars? (or vars? ivars?))
       (- (cw? debug? "~%**vars? is: ~x0~%" vars?))
       (prop-rest (if ivars? (cdr prop-rest) prop-rest))
       (hyps? (assoc :hyps kwd-alist))
       (body? (assoc :body kwd-alist))
       (check-contracts? (defdata::get1 :check-contracts? kwd-alist))
;       ((when (and hyps? (not body?)))
;         (er soft ctx
;             "~|**ERROR: If :hyps is provided, then :body must also be provided."))
       (body (if body?
                 (defdata::get1 :body kwd-alist)
               (extract-body (car prop-rest))))
       (hyps-list (cond (hyps? (hyps-list-from-hyps
                                (defdata::get1 :hyps kwd-alist)))
                        (body? nil)
                        (t (extract-hyps (car prop-rest)))))
       (find-duplicate-hyp (find-first-duplicate hyps-list))
       (- (cw? find-duplicate-hyp
               "~%**Warning: Your property has a duplicate hypothesis, ~x0. ~
                ~%**This may indicate an error.~%"
               find-duplicate-hyp))
       (hyps-list (remove-dups hyps-list))
       (user-var-list (cdr vars?))
       (user-vars (evens user-var-list))
       (user-types (odds user-var-list))
       (user-types (map-intern-types user-types pkg))
       (- (cw? debug? "~%**user-types is: ~x0~%" user-types))
       (user-preds (map-preds user-types tbl atbl))
       (- (cw? debug? "~%**user-preds is: ~x0~%" user-preds))
       (type-list1 (make-input-contract user-vars user-preds))
       (type-list (hyps-list-from-hyps type-list1))
       (type-hyps-list (append type-list hyps-list))
       (- (cw? debug? "~%**type-hyps-list is: ~x0~%" type-hyps-list))
       (prop (cond ((endp type-hyps-list) body)
                   ((endp (cdr type-hyps-list))
                    `(implies ,(car type-hyps-list) ,body))
                   (t `(implies (and ,@type-hyps-list) ,body))))
       ((mv erp trans-prop)
        (acl2::pseudo-translate prop nil wrld))
       (all-vars (acl2::all-vars trans-prop))
       (vars (if vars? user-vars all-vars))
       (- (cw? debug? "~%**vars is: ~x0~%" vars))
       (- (cw? debug? "~%**all-vars is: ~x0~%" all-vars))
       (var-diff (sym-diff vars all-vars))
       (- (cw? debug? "~%**prop is: ~x0~%" prop))
       (- (cw? debug? "~%**trans-prop is: ~x0~%" trans-prop))
       (parsed (list name? name prop kwd-alist))
       ((when erp)
        (ecw "~|**ERROR: The translation of prop: ~
              ~x0 ~
              resulted in an error."
             prop
             parsed))
       ((unless (or (consp prop-rest) body?))
        (ecw "~|**ERROR: Empty properties are not allowed."
             parsed))
       ((when var-diff)
        (ecw "~|**ERROR: The :vars provided do not match the actual variables ~
                appearing in the property. An example is ~x0."
             (car var-diff)
             parsed))
       (gprop (sublis-fn-simple '((implies . impliez)) trans-prop))
       (- (cw? debug? "~%**gprop is: ~x0~%" gprop))
       ((mv erp val)
        (if check-contracts?
            (guard-obligation gprop nil nil t ctx state)
          (guard-obligation t nil nil t ctx state)))
       ((when erp)
        (ecw "~|**ERROR During Contract Completion.** ~
              ~%**val is: ~x0"
             val
             parsed))
       ((list* & CL &) val)
       (guards (acl2::prettyify-clause-set CL nil wrld))
       (- (cw? debug? "~|**The Contract Completion Proof Obligation is: ~x0~%" guards))
       (proof-timeout (defdata::get1 :proof-timeout kwd-alist))
       (testing-timeout (defdata::get1 :testing-timeout kwd-alist))
       (- (cw? check-contracts? "~%Form:  ( CONTRACT-CHECKING PROPERTY ...)~%"))
       ((mv te-thm-erp val state)
        (with-time-limit
         proof-timeout
         (trans-eval
          `(with-output
            ,@(if debug?
                  '(:on :all :off (proof-builder proof-tree) :gag-mode nil)
                '(:off :all :on (summary) :summary-off (:other-than time) :gag-mode nil ))
            (encapsulate
             nil
             (with-output
              ,@(if debug?
                    '(:on :all :off (proof-builder proof-tree) :gag-mode nil)
                  '(:off :all))
              (thm-no-test ,guards))))
          ctx state t)))
       ((list* & thm-erp &) val)
       (- (cw? debug? "~|**te-thm-erp is: ~x0~%" te-thm-erp))
       (- (cw? debug? "~|**val is: ~x0~%" val))
       (- (cw? debug? "~|**thm-erp is: ~x0~%" thm-erp))
       ((when thm-erp)
        (ecw "~|**ERROR During Contract Checking.**"
             parsed))
       (- (cw? thm-erp "~|Form:  ( TESTING PROPERTY CONTRACTS ...)"))
       ((mv te-test-erp val state)
        (if thm-erp
            (with-time-limit
             testing-timeout
             (trans-eval `(with-output
                           ,@(if debug?
                                 '(:on :all :off (proof-builder proof-tree) :gag-mode nil)
                               '(:off :all :on (error comment)))
                           (test? ,guards
                             ,@(if debug?
                                   '()
                                 '(:print-cgen-summary nil :num-witnesses 0))))
                         ctx state t))
          (mv nil nil state)))
       ((list* & test-erp &) val)
       (- (cw? debug? "~|**te-test-erp is: ~x0~%" te-test-erp))
       (- (cw? debug? "~|**val is: ~x0~%" val))
       (- (cw? debug? "~|**test-erp is: ~x0~%" test-erp))
       ((when test-erp)
        (ecw "~|**Contract Completion Error. The hypotheses of your property must imply:~
~%  ~x0.~
~%The counterexample above shows that this is not the case."
             guards
             parsed))
       ((when thm-erp)
        (ecw "~|**Contract Completion Error. The hypotheses of your property must imply:~
~%  ~x0."
             guards
             parsed)))
    (value parsed)))

#|
(defmacro ctest? (form &rest kwd-val-lst)
  (progn (contract-check form kwd-val-lst)
         (test? form kwd-val-lst)))
|#

(defun contract-check (form kwd-val-lst state)
  ;; Returns (list nm formals ic oc doc decls body kwd-alist)
  (declare (xargs :mode :program :stobjs (state)))
  (b* ((wrld (w state))
       (ctx 'contract-check)
;       (body (extract-body form))
;       (hyps-list (extract-hyps form))
       (prop form)
       (- (cw? t "~%**Property is: ~x0~%" prop))
       (gprop (sublis-fn-simple '((implies . impliez)) prop))
       ((mv erp val) (guard-obligation gprop nil nil t ctx state))
       ((when erp)
        (er soft ctx "~|**ERROR During Contract Checking.**"))
       ((list* & CL &) val) (guards (acl2::prettyify-clause-set CL nil wrld))
       (- (cw? t "~|**The Contract Completion Proof Obligation is: ~x0~%" guards))
       (- (cw? t "~%Form:  ( CONTRACT-CHECKING PROPERTY ...)~%"))
       (cgen::cgen-state (cgen::make-cgen-state-fn form (cons :USER-DEFINED ctx)
                                                   kwd-val-lst (w state)))
       (timeout (cgen::cget cgen-timeout))
       ((mv te-thm-erp val state)
        (with-time-limit
         timeout
         (trans-eval `(with-output
                       ;;:on :all :off (proof-builder proof-tree) :gag-mode nil
                       :off :all :on (summary) :summary-off (:other-than time) :gag-mode nil
                       (encapsulate
                        nil
                        (with-output
                         ;;:on :all :off (proof-builder proof-tree) :gag-mode nil
                         :off :all
                         (thm-no-test ,guards))))
                     ctx state t)))
       ((list* & thm-erp &) val)
       (- (cw? t "~|**trans-eval-thm-erp is: ~x0~%" te-thm-erp))
       (- (cw? t "~|**val is: ~x0~%" val))
       (- (cw? t "~|**thm-erp is: ~x0~%" thm-erp))
       (- (cw? thm-erp "~|Form:  ( TESTING PROPERTY CONTRACTS ...)"))
       ((mv te-test-erp val state)
        (if thm-erp
            (with-time-limit
             timeout
             (trans-eval `(with-output
                           ;; :on :all :off (proof-builder proof-tree) :gag-mode nil
                           :off :all :on (error comment)
                           (test? ,guards
                             ;;
                             :print-cgen-summary nil :num-witnesses 0
                             ))
                         ctx state t))
          (mv nil nil state)))
       ((list* & test-erp &) val)
       (- (cw? t "~|**trans-eval-test-erp is: ~x0~%" te-test-erp))
       (- (cw? t "~|**val is: ~x0~%" val))
       (- (cw? t "~|**test-erp is: ~x0~%" test-erp))
       ((when test-erp)
        (er soft ctx "~|**Contract Completion Error. The hypotheses of your property must imply:~
~%  ~x0.~
~%The counterexample above shows that this is not the case."
            guards))
       ((when thm-erp)
        (er soft ctx "~|**Contract Completion Error. The hypotheses of your property must imply:~
~%  ~x0."
            guards)))
    (value t)))

#|
()

(contract-check '(implies (symbolp a) (= a a)) nil state)


|#

(definec gen-other-keywords-aux (alist :alist aux :tl) :tl
  (if (endp alist)
      aux
    (gen-other-keywords-aux
     (cdr alist)
     `(,(caar alist) ,(cdar alist) . ,aux))))

(definec gen-other-keywords (alist :alist) :tl
  (gen-other-keywords-aux alist nil))

; (gen-other-keywords '((:hints ("goal" :cases ((< 0 b))))))

(defun property-core (parsed)
  (declare (xargs :mode :program))
  (b* (((list name? name prop kwd-alist) parsed)
       (proofs? (defdata::get1 :proofs? kwd-alist))
       (testing? (defdata::get1 :testing? kwd-alist))
       (debug? (defdata::get1 :debug? kwd-alist))
       (proof-timeout (defdata::get1 :proof-timeout kwd-alist))
       (testing-timeout (defdata::get1 :testing-timeout kwd-alist))
       (prove (if name? 'defthm-no-test 'thm-no-test))
       (other-kwds
        (defdata::remove1-assoc-eq-lst
          (append (if name? nil *property-just-defthm-keywords*)
                  *property-core-keywords*
                  *property-conjecture-keywords*)
          kwd-alist))
       (- (cw? debug? "~|Kwd-alist: ~x0~%" kwd-alist))
       (- (cw? debug? "~|Other-kwds: ~x0~%" other-kwds))
       (flat-kwds (gen-other-keywords other-kwds))
       (- (cw? debug? "~|Flat-kwds: ~x0~%" flat-kwds))
       (args (if name?
                 (list* name prop flat-kwds)
               (list* prop flat-kwds)))
       ((when (and proofs? testing?))
        `(with-output
          :off :all :on comment
          (encapsulate
           ()
           (value-triple (cw "~|Form:  ( TESTING PROPERTY )~%"))
           (with-time-limit ,testing-timeout
                            (with-output :stack :pop (test? ,prop)))
           (value-triple (cw "~|Form:  ( PROVING PROPERTY )~%"))
           (with-time-limit ,proof-timeout
                            (with-output :stack :pop (,prove ,@args)))
           (value-triple (cw "~|Form:  ( ACCEPTED PROPERTY AS THEOREM )~%")))))
       ((when proofs?)
        `(with-output
          :off :all :on comment
          (encapsulate
           ()
           (value-triple (cw "~|Form:  ( PROVING PROPERTY )~%"))
           (with-time-limit ,proof-timeout
                            (with-output :stack :pop (,prove ,@args)))
           (value-triple (cw "~|Form:  ( ACCEPTED PROPERTY AS THEOREM )~%")))))
       ((when (and testing? name?))
        `(with-output
          :off :all :on comment
          (encapsulate
           ()
           (value-triple (cw "~|Form:  ( TESTING PROPERTY )~%"))
           (with-time-limit ,testing-timeout
                            (with-output :stack :pop
                                         (defthm-test-no-proof ,@args)))
           (value-triple
            (cw "~|Form:  ( ACCEPTED PROPERTY AS A THEOREM WITHOUT PROOF )~%")))))
       ((when testing?)
        `(with-output
          :off :all :on comment
          (encapsulate
           ()
           (value-triple (cw "~|Form:  ( TESTING PROPERTY )~%"))
           (with-time-limit ,testing-timeout
                            (with-output :stack :pop (test? ,prop)))
           (value-triple
            (cw "~|Form:  ( PROPERTY PASSED TESTING )~%")))))
       ((when name?)
        `(with-output
          :off :all :on comment
          (encapsulate
           ()
           (value-triple (cw "~|Form:  ( TESTING PROPERTY )~%"))
           (with-time-limit ,proof-timeout
                            (with-output :stack :pop
                                         (defthmskipall ,@args)))
           (value-triple
            (cw "~|Form:  ( ACCEPTED PROPERTY AS A THEOREM WITHOUT PROOF )~%"))))))
    `(value-triple :passed)))

(defun property-fn (args state)
  (declare (xargs :mode :program :stobjs (state)))
  (b* (((mv erp parsed state)
        (parse-property args state))
       ((list - - - kwd-alist) parsed)
       (debug? (defdata::get1 :debug? kwd-alist))
       (debug-hint
        (if debug?
            ""
          " To debug, add \":debug? t\" at the end of your property.~%"))
       ((when erp)
        (ecw "~%~|******** PROPERTY FAILED ********~% ~@0" debug-hint nil)))
    (value `(make-event ',(property-core parsed)))))

(defmacro property (&rest args)
  (b* ((debug? (let ((lst (member :debug? args)))
                 (and lst (cadr lst)))))
    `(with-output
      ;; ,@(and (not debug?) '(:off :all))
      ;;  We take are of debug? later
      :off :all :on (summary comment) :summary-off (:other-than time)
      :gag-mode ,(not debug?)
      :stack :push
      (encapsulate
       ()
       (with-output
        :off :all
        (make-event (property-fn ',args state)))
       (value-triple (cw "~|Form:  ( PROPERTY CHECKING SUCCESSFUL )~%"))))))

(defmacro property-fail (&rest args)
  `(must-fail (property ,@args)))

#|

start-modeling:

You are just starting to design your model, so the goal is quick
responses from ACL2s.  Therefore, testing is done with a short timeout
but admissibility, contract checking and body contract checking are
skipped.

If you want to all skip testing, use one of the above forms.

Properties are just tested with a short timeout.

|#

(defmacro modeling-set-parms (cgen cgen-local defunc table)
  `(progn
     (acl2s-defaults :set cgen-timeout ,cgen)
     (acl2s-defaults :set cgen-local-timeout ,cgen-local)
     (set-defunc-timeout ,defunc)
     (set-acl2s-property-table-proof-timeout ,table)
     (set-acl2s-property-table-testing-timeout ,table)))

(defmacro modeling-start
  (&key (cgen '2) (cgen-local '1) (defunc '5) (table '5))
  `(progn
     (acl2s-defaults :set testing-enabled t)
     (set-defunc-skip-admissibilityp t)
     (set-defunc-skip-function-contractp t)
     (set-defunc-skip-body-contractsp t)
     (set-acl2s-property-table-proofs? nil)
     (set-acl2s-property-table-testing? t)
     (modeling-set-parms ,cgen ,cgen-local ,defunc ,table)))


(defmacro modeling-validate-defs
  (&key (cgen '4) (cgen-local '2) (defunc '10) (table '10))
  `(progn
     (acl2s-defaults :set testing-enabled t)
     (set-defunc-skip-admissibilityp nil)
     (set-defunc-skip-function-contractp nil)
     (set-defunc-skip-body-contractsp nil)
     (set-defunc-termination-strictp nil)
     (set-defunc-function-contract-strictp nil)
     (set-defunc-body-contracts-strictp nil)
     (set-acl2s-property-table-proofs? nil)
     (set-acl2s-property-table-testing? t)
     (modeling-set-parms ,cgen ,cgen-local ,defunc ,table)))

(defmacro modeling-admit-defs
  (&key (cgen '30) (cgen-local '15) (defunc '60) (table '30))
  `(progn
     (acl2s-defaults :set testing-enabled t)
     (set-defunc-skip-admissibilityp nil)
     (set-defunc-skip-function-contractp nil)
     (set-defunc-skip-body-contractsp nil)
     (set-defunc-termination-strictp t)
     (set-defunc-function-contract-strictp t)
     (set-defunc-body-contracts-strictp t)
     (set-acl2s-property-table-proofs? nil)
     (set-acl2s-property-table-testing? t)
     (modeling-set-parms ,cgen ,cgen-local ,defunc ,table)))

(defmacro modeling-admit-all
  (&key (cgen '30) (cgen-local '15) (defunc '60) (table '30))
  `(progn
     (acl2s-defaults :set testing-enabled t)
     (set-defunc-skip-admissibilityp nil)
     (set-defunc-skip-function-contractp nil)
     (set-defunc-skip-body-contractsp nil)
     (set-defunc-termination-strictp t)
     (set-defunc-function-contract-strictp t)
     (set-defunc-body-contracts-strictp t)
     (set-acl2s-property-table-proofs? t)
     (set-acl2s-property-table-testing? t)
     (modeling-set-parms ,cgen ,cgen-local ,defunc ,table)))

#|
(modeling-start)
(modeling-validate-defs)
(modeling-admit-defs)
(modeling-admit-all)
|#
