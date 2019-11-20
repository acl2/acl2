#|$ACL2s-Preamble$;
(include-book ;; Newline to fool ACL2/cert.pl dependency scanner
 "portcullis")
(begin-book t :ttags :all);$ACL2s-Preamble$|#

(in-package "ACL2S")
(include-book "definec" :ttags :all)
(include-book "std/lists/flatten" :dir :system)

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

(defconst *property-thm-keywords*
  '(:hints :otf-flg))

(defconst *property-just-defthm-keywords*
  '(:rule-classes :instructions))

(defconst *property-core-keywords*
  '(:proofs? :proof-timeout :testing? :testing-timeout :doc))
  
(defconst *property-keywords*
  (append *property-core-keywords*
          *property-thm-keywords*
          *property-just-defthm-keywords*))

(gen-property-table 
 ((:proofs? . t)
  (:proof-timeout . 40)
  (:testing? . t)
  (:testing-timeout . 20)))
     
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

(defun parse-property (args wrld)
  ;; Returns (list nm formals ic oc doc decls body kwd-alist)
  (declare (xargs :mode :program))
  (declare (ignorable wrld))
  (b* ((ctx 'property)
       ((unless (consp args))
        (er hard? ctx "~| Empty properties are not allowed.~%"))
       (name? (acl2::legal-variablep (car args)))
       (name (and name? (car args)))
       (args (if name? (cdr args) args))
       (PT (acl2s-property-table wrld))
       (PT (defdata::remove1-assoc-eq-lst (filter-keywords args) PT))
       ((mv kwd-alist prop-rest)
        (defdata::extract-keywords ctx *property-keywords* args PT nil))
       (prop (car prop-rest)))
    (list name? name prop kwd-alist)))

(defmacro property (&rest args)
  `(with-output
    :off :all :stack :push
    (make-event
     (b* (((list name? name prop kwd-alist)
           (parse-property ',args (w state)))
          (proofs? (defdata::get1 :proofs? kwd-alist))
          (testing? (defdata::get1 :testing? kwd-alist))
          (proof-timeout (defdata::get1 :proof-timeout kwd-alist))
          (testing-timeout (defdata::get1 :testing-timeout kwd-alist))
          (prove (if name? 'defthm-no-test 'thm-no-test))
          (other-kwds
           (defdata::remove1-assoc-eq-lst
             (append (if name? nil *property-just-defthm-keywords*)
                     *property-core-keywords*)
             kwd-alist))
          (flat-kwds (flatten other-kwds))
          (args (if name?
                    (list* name prop flat-kwds)
                  (list* prop flat-kwds)))
          ((when (and proofs? testing?))
           `(encapsulate
             ()
             (with-time-limit
              ,testing-timeout
              (with-output
               :stack :pop
               (test? ,prop)))
             (with-time-limit
              ,proof-timeout
              (with-output
               :stack :pop
               (,prove ,@args)))))
          ((when proofs?)
           `(with-time-limit
             ,proof-timeout
             (with-output
              :stack :pop
              (,prove ,@args))))
          ((when (and testing? name?))
           `(with-time-limit
             ,testing-timeout
             (with-output
              :stack :pop
              (defthm-test-no-proof ,@args))))
          ((when testing?)
           `(with-time-limit
             ,testing-timeout
             (with-output
              :stack :pop
              (test? ,prop))))
          ((when name?)
           `(with-time-limit
             ,proof-timeout
             (with-output
              :stack :pop
              (defthmskipall ,@args)))))
       `(value-triple :passed)))))

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

