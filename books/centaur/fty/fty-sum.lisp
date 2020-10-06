; FTY type support library
; Copyright (C) 2014 Centaur Technology
;
; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/
;
; License: (An MIT/X11-style license)
;
;   Permission is hereby granted, free of charge, to any person obtaining a
;   copy of this software and associated documentation files (the "Software"),
;   to deal in the Software without restriction, including without limitation
;   the rights to use, copy, modify, merge, publish, distribute, sublicense,
;   and/or sell copies of the Software, and to permit persons to whom the
;   Software is furnished to do so, subject to the following conditions:
;
;   The above copyright notice and this permission notice shall be included in
;   all copies or substantial portions of the Software.
;
;   THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
;   IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
;   FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
;   AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
;   LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
;   FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
;   DEALINGS IN THE SOFTWARE.
;
; Original author: Sol Swords <sswords@centtech.com>

(in-package "FTY")
(include-book "fty-parseutils")
(include-book "fty-sum-casemacro")
(include-book "xdoc/names" :dir :system)
(program)


; Term Building Utilities -----------------------------------------------------

(define nice-and (x y)
  "Like `(and ,x ,y) but maybe simplify things."
  (cond ((eq x t) y)
        ((eq y t) x)
        ((eq x nil) nil)
        ((eq y nil) nil)
        ((and (consp x) (eq (car x) 'and))
         (if (and (consp y) (eq (car y) 'and))
             (append x (cdr y))
           (append x (list y))))
        ((and (consp y) (eq (car y) 'and))
         `(and ,x . ,(cdr y)))
        (t `(and ,x ,y))))

(define nice-or (x y)
  "Like `(or ,x ,y) but maybe simplify things."
  (cond ((eq x t) t)
        ((eq y t) t)
        ((eq x nil) y)
        ((eq y nil) x)
        ((and (consp x) (eq (car x) 'or))
         (if (eq (car y) 'or)
             (append x (cdr y))
           (append x (list y))))
        ((and (consp y) (eq (car y) 'or))
         `(or ,x . ,(cdr y)))
        (t `(or ,x ,y))))

(define nice-implies (x y)
  "Like `(implies ,x ,y) but maybe simplify things."
  (cond ((eq x t) y)
        ((eq y t) t)
        ((eq x nil) t)
        ((eq y nil) x)
        (t `(implies ,x ,y))))

(define nice-cond (x)
  "Like `(cond ...)` but maybe reduce (cond (t foo)) to just foo."
  (cond ((atom x) nil)
        ((eq (caar x) t) (cadar x))
        (t `(cond . ,x))))



; Flexprod Parsing ------------------------------------------------------------

(defconst *flexprod-field-keywords*
  ;; Keyword arguments the user can write in an individual field of a defprod.
  ;; See the definition of flexprod-field structures for explanation.
  '(:type
    :acc-body
    :acc-name
    :default
    :doc
    :rule-classes
    :reqfix))

(define parse-flexprod-field
  ;; Note: NOT DEFPROD!  This is for an individual flexsum field,
  ;; like `(name :acc-body x :type varp)`
  ((x             "User-level syntax, a single field they are defining.")
   (type-name     "Product type this field is part of.")
   (our-fixtypes  "New fixtypes being defined.")
   (fixtypes      "Previous fixtypes."))
  :returns (field "A flexprod-field-p.")
  (b* (((cons name kws) x)
       ((unless (symbolp name))
        (raise "In ~x0: malformed field ~x1: first element should be the name, a symbol."
               type-name x))
       ((mv kwd-alist rest)
        (extract-keywords (list type-name (list name '[...])) ;; context for errors
                          *flexprod-field-keywords* kws nil))
       ((when rest)
        (raise "In ~x0: malformed field ~x1: after name should be a keyword/value list."
               type-name x))
       (acc-body (getarg :acc-body 0 kwd-alist))
       ((unless (or (symbolp acc-body)
                    (consp acc-body)))
        (raise "In ~x0: malformed field ~x1: :acc-body should be a term."
               type-name x))
       (acc-name (getarg-nonnil! :acc-name
                                 (intern-in-package-of-symbol
                                  (cat (symbol-name type-name) "->" (symbol-name name))
                                  type-name)
                                 kwd-alist))
       ((mv type fix equiv recp)
        (get-pred/fix/equiv (getarg :type nil kwd-alist) our-fixtypes fixtypes))
       (reqfix (getarg :reqfix name kwd-alist)))
    (make-flexprod-field :name name
                         :acc-body acc-body
                         :acc-name acc-name
                         :type type
                         :fix fix
                         :equiv equiv
                         :default (getarg :default nil kwd-alist)
                         :doc (getarg :doc "" kwd-alist)
                         :reqfix reqfix
                         :rule-classes (let ((look (assoc :rule-classes kwd-alist)))
                                         (and look `(:rule-classes ,(cdr look))))
                         :recp recp)))

(define parse-flexprod-fields (x type-name our-fixtypes fixtypes)
  (if (atom x)
      nil
    (cons (parse-flexprod-field (car x) type-name our-fixtypes fixtypes)
          (parse-flexprod-fields (cdr x) type-name our-fixtypes fixtypes))))

(defconst *flexprod-keywords*
  ;; Keywords that the user can write at the top level of a defprod.
  ;; See the definition of flexprod structures for explanation.
  '(:shape
    :fields
    :ctor-body
    :ctor-name
    :ctor-macro
    :remake-name
    :remake-body
    :cond
    :type-name
    :short
    :long
    :inline
    :require
    :count-incr
    :extra-binder-names
    :no-ctor-macros
    :verbosep))

(define dumb-append-conjunct (rev-prev-conds newcond)
  (cond ((or (eq newcond t)
             (equal newcond ''t))
         (reverse rev-prev-conds))
        ((or (eq newcond nil)
             (equal newcond ''nil))
         (list nil))
        (t
         (revappend rev-prev-conds (list newcond)))))

(define parse-flexprod
  ;; Note: NOT DEFPROD!!  This is for a flexsum product, e.g.,
  ;; `(:var :cond (atom x) :fields ...)`
  ((x                 "User-level syntax, the whole product type.")
   (sumname           "The name of the superior sum type, e.g., mysum but not mysum-p.")
   (sumkind           "The kind function for the superior sum type, if applicable.")
   (sum-kwds          "The keyword arguments from the superior sum type.")
   (xvar              "The special @('x') variable to use.")
   (rev-not-prevconds "The previous conditions for the sum type, if applicable.")
   (our-fixtypes      "New fixtypes being defined.")
   (fixtypes          "Previous fixtypes."))
  :returns (prod "A flexprod-p.")
  (b* (((unless (consp x))
        (raise "In ~x0: malformed flexprod ~x1: expected (:kind ...)." sumname x))
       ((cons kind kws) x)
       ((unless (keywordp kind))
        (raise "In ~x0: malformed flexprod ~x1: kind (~x2) should be a keyword"
               sumname x kind))
       ((mv kwd-alist rest)
        (extract-keywords (list kind '[...]) *flexprod-keywords* kws nil))
       ((when rest)
        (raise "In ~x0: malformed flexprod ~x1: after kind keyword ~x1 there ~
                should be only keywords and values." sumname kind))
       (ctor-body-lookup (assoc :ctor-body kwd-alist))
       ((unless ctor-body-lookup)
        (raise "In ~x0: malformed product: ~x1: :ctor-body should be a term."
               sumname kind))
       (ctor-body (cdr ctor-body-lookup))
       (cond       (getarg :cond t kwd-alist))
       (shape      (getarg :shape t kwd-alist))
       (type-name  (getarg-nonnil! :type-name
                                   (intern-in-package-of-symbol
                                    (cat (symbol-name sumname) "-" (symbol-name kind))
                                    sumname)
                                   kwd-alist))
       (ctor-name  (getarg-nonnil! :ctor-name type-name kwd-alist))
       (ctor-macro (getarg-nonnil! :ctor-macro
                                   (intern-in-package-of-symbol
                                    (cat "MAKE-" (symbol-name ctor-name))
                                    ctor-name)
                                   kwd-alist))
       (remake-body (getarg :remake-body nil kwd-alist))
       (remake-name (getarg :remake-name
                            ;; If the user gives a remake-body but no explicit
                            ;; remake-name, provide a default name of
                            ;; REMAKE-XXX.
                            (and remake-body
                                 (intern-in-package-of-symbol
                                  (cat "REMAKE-" (symbol-name ctor-name))
                                  ctor-name))
                            kwd-alist))
       ((when (and remake-name (not remake-body)))
        (raise "In ~x0: malformed product ~x1: :remake-name is ~x2 but ~
                no :remake-body has been provided."
               sumname x remake-name))
       (fields (parse-flexprod-fields (getarg :fields nil kwd-alist) type-name our-fixtypes fixtypes))
       (guard (if sumkind
                  `(equal (,sumkind ,xvar) ,kind)
                (let* ((fullcond-terms (dumb-append-conjunct rev-not-prevconds cond)))
                  (cond ((atom fullcond-terms) t)
                        ((atom (cdr fullcond-terms)) (car fullcond-terms))
                        (t `(and . ,fullcond-terms))))))
       (inline (get-deftypes-inline-opt (getarg :inline *inline-defaults* sum-kwds) kwd-alist))
       (require (getarg :require t kwd-alist))
       (extra-binder-names (getarg :extra-binder-names nil kwd-alist))
       (count-incr (getarg :count-incr nil kwd-alist))
       (no-ctor-macros (getarg :no-ctor-macros nil kwd-alist)))
    (make-flexprod :kind kind
                   :cond cond
                   :guard guard
                   :shape shape
                   :require require
                   :fields fields
                   :type-name type-name
                   :ctor-name ctor-name
                   :ctor-macro ctor-macro
                   :ctor-body ctor-body
                   :remake-name remake-name
                   :remake-body remake-body
                   :extra-binder-names extra-binder-names
                   :short (getarg :short nil kwd-alist)
                   :long (getarg :long nil kwd-alist)
                   :inline inline
                   :count-incr count-incr
                   :no-ctor-macros no-ctor-macros)))

(define dumb-cons-conjunct (newcond conds)
  (cond ((or (eq newcond t)
             (equal newcond ''t))
         conds)
        ((or (eq newcond nil)
             (equal newcond ''nil))
         (list nil))
        (t
         (cons newcond conds))))

(define parse-flexprods (x sumname sumkind sum-kwds xvar rev-not-prevconds our-fixtypes fixtypes)
  (b* (((when (atom x))
        nil)
       (newprod (parse-flexprod (car x) sumname sumkind sum-kwds xvar rev-not-prevconds
                                our-fixtypes fixtypes))
       (rev-not-prevconds (dumb-cons-conjunct (acl2::dumb-negate-lit (flexprod->cond newprod))
                                              rev-not-prevconds)))
    (cons newprod
          (parse-flexprods (cdr x) sumname sumkind sum-kwds xvar rev-not-prevconds
                           our-fixtypes fixtypes))))


; Flexsum Parsing -------------------------------------------------------------

(defconst *flexsum-keywords*
  ;; Keyword the user can provide to a flexsum
  ;; See the definition of flexsum structures for explanation.
  '(:pred
    :fix
    :equiv
    :kind
    :count
    :case
    :measure
    :measure-debug
    :xvar
    :no-count
    :shape
    :kind-body    ;; :exec part of kind function
    :parents
    :short
    :long
    :prepwork
    :post-pred-events
    :post-fix-events
    :post-events
    :inline
    :enable-rules
    :verbosep))

(define some-flexprod-field-recursivep (x)
  (if (atom x)
      nil
    (or (flexprod-field->recp (car x))
        (some-flexprod-field-recursivep (cdr x)))))

(define some-flexprod-recursivep (x)
  (if (atom x)
      nil
    (or (some-flexprod-field-recursivep (flexprod->fields (car x)))
        (some-flexprod-recursivep (cdr x)))))

(define flexsum-infer-xvar
  ((ctx       "Context for error messages.")
   (kwd-alist "Keyword alist that may include :xvar")
   (xvar      "The value of :xvar in the superior deftypes call, if applicable.
               When provided, we use this unless the user explicitly overrides
               it in the sum itself.")
   (prods     "The products in this sum type, not yet parsed, we're just
               dumbly looking for Xes in these."))
  (b* ((xvar (getarg-nonnil! :xvar xvar kwd-alist))
       ((when xvar)
        ;; User says explicitly which one to use, so use it.
        xvar)
       (xsyms (find-symbols-named-x prods))
       ((when (atom xsyms))
        (raise "In ~x0: no variable named X occurs in the defflexsum form. ~
                Specify another variable with :xvar." ctx))
       ((when (consp (cdr xsyms)))
        (raise "In ~x0: more than one symbol named X occurs in the deftypes ~
                form: ~&1.  Specify the variable denoting the typed object ~
                with :xvar." ctx xsyms)))
    (car xsyms)))

(define flexprod-fields-check-xvar (xvar fields prodname)
  (b* (((when (atom fields))
        nil)
       ((flexprod-field x) (car fields))
       ((when (eq x.name xvar))
        (raise "Product ~x0 has a field named ~x1, which is not allowed ~
                because it's also the name of the variable representing the ~
                whole product.  You may change the field name or provide an ~
                explicit :xvar argument.~%" prodname x.name)))
    (flexprod-fields-check-xvar xvar (cdr fields) prodname)))

(define flexprods-check-xvar (xvar prods)
  (b* (((when (atom prods))
        nil)
       ((flexprod x) (car prods)))
    (flexprod-fields-check-xvar xvar x.fields x.kind)
    (flexprods-check-xvar xvar (cdr prods))))

(define parse-flexsum
  ((x             "User-level syntax, the whole defflexsum form.")
   (xvar          "The special x variable to use.  BOZO but we infer it?")
   (our-fixtypes  "New fixtypes being defined.")
   (fixtypes      "Previous fixtypes."))
  :returns (flexsum "A flexsum-p.")
  (b* (((cons name args) x)
       ((unless (symbolp name))
        (raise "Malformed flexsum: ~x0: name must be a symbol" x))
       ((mv pre-/// post-///)     (std::split-/// name args))
       ((mv kwd-alist orig-prods) (extract-keywords name *flexsum-keywords* pre-/// nil))
       (pred    (getarg! :pred  (intern-in-package-of-symbol (cat (symbol-name name) "-P") name) kwd-alist))
       (fix     (getarg! :fix   (intern-in-package-of-symbol (cat (symbol-name name) "-FIX") name) kwd-alist))
       (equiv   (getarg! :equiv (intern-in-package-of-symbol (cat (symbol-name name) "-EQUIV") name) kwd-alist))
       (kind    (getarg! :kind  (intern-in-package-of-symbol (cat (symbol-name name) "-KIND") name) kwd-alist))
       (case    (getarg! :case  (intern-in-package-of-symbol (cat (symbol-name name) "-CASE") name) kwd-alist))
       (inline  (get-deftypes-inline-opt *inline-defaults* kwd-alist))
       (shape   (getarg :shape t kwd-alist))
       (xvar    (flexsum-infer-xvar name kwd-alist xvar orig-prods))
       (measure (getarg! :measure `(acl2-count ,xvar) kwd-alist))
       (count   (flextype-get-count-fn name kwd-alist))
       (prods   (parse-flexprods orig-prods name kind kwd-alist xvar nil our-fixtypes fixtypes))
       ((when (atom prods))
        (raise "Malformed SUM ~x0: Must have at least one product" x))
       (- (flexprods-check-xvar xvar prods))
       (recp   (some-flexprod-recursivep prods)))
    (make-flexsum :name name
                  :pred pred
                  :fix fix
                  :case case
                  :equiv equiv
                  :kind kind
                  :kind-body (getarg :kind-body nil kwd-alist)
                  :count count
                  :prods prods
                  :xvar xvar
                  :inline inline
                  :shape shape
                  :measure measure
                  :kwd-alist (if post-///
                                 (cons (cons :///-events post-///)
                                       kwd-alist)
                               kwd-alist)
                  :orig-prods orig-prods
                  :recp recp
                  :typemacro 'defflexsum)))


;; ------------------ Predicate: flexsum -----------------------

(defun flexprod-fields-pred-bindings (fields)
  (b* (((when (atom fields)) nil)
       ((flexprod-field x) (car fields))
       ((unless x.type)
        (cons (list (intern-in-package-of-symbol (cat "?" (symbol-name x.name)) x.name)
                    x.acc-body)
              (flexprod-fields-pred-bindings (cdr fields)))))
    (cons (list x.name x.acc-body)
          (flexprod-fields-pred-bindings (cdr fields)))))

(defun flexprod-fields-typechecks (fields last)
  (b* (((when (atom fields)) last)
       ((flexprod-field x) (car fields))
       ((unless x.type)
        (flexprod-fields-typechecks (cdr fields) last)))
    (nice-and (list x.type x.name)
              (flexprod-fields-typechecks (cdr fields) last))))

(defun flexsum-pred-prod-case (prod)
  (b* (((flexprod prod) prod)
       (bindings (flexprod-fields-pred-bindings prod.fields))
       (typechecks (flexprod-fields-typechecks
                    prod.fields prod.require))
       (typecheckterm `(b* ,bindings ,typechecks)))
    (nice-and prod.shape typecheckterm)))

(defun flexsum-pred-cases-nokind (prods)
  (if (atom prods)
      nil
    (cons (list (flexprod->cond (car prods))
                (flexsum-pred-prod-case (car prods)))
          (flexsum-pred-cases-nokind (cdr prods)))))

(defun flexsum-predicate-def (sum)
  (b* (((flexsum sum) sum)
       (short (cat "Recognizer for @(see " (xdoc::full-escape-symbol sum.name) ") structures."))
       (consp-when-foo-p (intern-in-package-of-symbol
                          (cat "CONSP-WHEN-" (symbol-name sum.pred))
                          sum.pred)))
    `(define ,sum.pred (,sum.xvar)
       :parents (,sum.name)
       :short ,short
       :measure ,sum.measure
       ,@(and (getarg :measure-debug nil sum.kwd-alist)
              `(:measure-debug t))
       :progn t
       ;; ,(if sum.kind
       ;;      `(case (,sum.kind ,sum.xvar)
       ;;         . ,(flexsum-pred-cases sum.prods))
       ;;    `(cond . ,(flexsum-pred-cases-nokind sum.prods)))
       ,(nice-and sum.shape
                  (nice-cond (flexsum-pred-cases-nokind sum.prods)))
       ///
       (make-event
        '(:or (:do-proofs
               (with-output :off (error)
                 (defthm ,consp-when-foo-p
                   (implies (,sum.pred ,sum.xvar)
                            (consp ,sum.xvar))
                   :hints (("goal" :expand ((,sum.pred ,sum.xvar)))
                           (and stable-under-simplificationp
                                '(:error t)))
                   :rule-classes :compound-recognizer)))
          (value-triple :skip-compound-recognizer))))))



;; --------------- Kind function & case macro (sums) ----------

; We are going to write the kind function for a flexsum.  In the case of
; something like a term, we might end up writing something like this:
;
;   (defun myterm-kind (x)
;     (cond ((not x) :null)
;           ((atom x) :var)
;           ((eq (car x) 'quote) :quote)
;           (t :call)))
;
; Kind Function Optimization.  Consider the special case of a tagsum.  In this
; case we could just follow our above strategy and generate a function like
; this:
;
;   (defun mysum-kind (x)
;     (cond ((eq (tag x) :subtype1) :subtype1)
;           ((eq (tag x) :subtype2) :subtype2)
;           ((eq (tag x) :subtype3) :subtype3)
;           (t :subtype4)))
;
; But we think ACL2 does better with CASE statements so we instead prefer to
; notice this and instead generate
;
;   (defun mysum-kind (x)
;     (if (atom x)
;         :base-case-tag
;       (case (tag x)
;         ((:subtype1) :subtype1)
;         ((:subtype2) :subtype2)
;         ((:subtype3) :subtype3)
;         (otherwise :subtype4))))

(defun flextype-sum-kind-conds-basic (prods)
  ;; Generates the basic cond statements for the basic (unoptimized) form.
  ;; For instance, this might produce:
  ;;          (((not x) :null)
  ;;           ((atom x) :var)
  ;;           ((eq (car x) 'quote) :quote)
  ;;           (t :call)))
  (if (atom prods)
      nil
    (cons `(,(flexprod->cond (car prods)) ,(flexprod->kind (car prods)))
          (flextype-sum-kind-conds-basic (cdr prods)))))

(defun match-optimizable-tag-check (prod.cond xvar)
  ;; Check whether the cond for a single product is simple enough to optimize.
  "Returns (mv matchp possible-tags)"
  (case-match prod.cond
    ((eqsym ('tag var) ('quote foo))
     (if (and (member eqsym '(eq eql equal))
              (eq var xvar))
         (mv t (list foo))
       (mv nil nil)))
    (('or ('not ('mbt ('consp var)))
          tag-cond)
     (if (eq var xvar)
         (match-optimizable-tag-check tag-cond xvar)
       (mv nil nil)))
    (&
     (mv nil nil))))

#||
(match-optimizable-tag-check '(eq (tag my-x) ':foo) 'my-x)
(match-optimizable-tag-check '(equal (tag my-x) ':foo) 'my-x)
(match-optimizable-tag-check '(or (not (mbt (consp my-x)))
                                  (eq (tag my-x) ':foo)) 'my-x)
||#

(define prod-conds-can-be-optimized-p (prods xvar)
  ;; Check whether the cond for each product is simple enough to optimize.
  (b* (((when (atom prods))
        (raise "never get here"))
       ((when (atom (cdr prods)))
        ;; The final condition needs to be T.
        (equal (flexprod->cond (car prods)) t))
       ((mv matchp &)
        (match-optimizable-tag-check (flexprod->cond (car prods)) xvar))
       ((unless matchp)
        nil))
    (prod-conds-can-be-optimized-p (cdr prods) xvar)))

(define flextype-sum-kind-conds-optimized (prods xvar)
  ;; Generates optimized case statements.  Assumes the conditions are simple
  ;; enough to be optimized, i.e., prod-conds-can-be-optimized-p.
  (b* (((when (atom prods))
        (raise "should never get here"))
       (ans1 (flexprod->kind (car prods)))
       ((when (atom (cdr prods)))
        (list `(otherwise ,ans1)))
       ((mv matchp tags1) (match-optimizable-tag-check (flexprod->cond (car prods)) xvar))
       ((unless matchp)
        (raise "expected optimizable tags.")))
    (cons `(,tags1 ,ans1)
          (flextype-sum-kind-conds-optimized (cdr prods) xvar))))

(defun flextype-sum-kind-conds (prods xvar)
  "Returns (mv optimized-p body)"
  (if (prod-conds-can-be-optimized-p prods xvar)
      (mv t `(case (tag ,xvar) . ,(flextype-sum-kind-conds-optimized prods xvar)))
    (mv nil (nice-cond (flextype-sum-kind-conds-basic prods)))))

;; (define pterm-kind (x)
;;   (cond ((not x) :null)
;;         ((atom x) :var)
;;         ((eq (car x) 'quote) :quote)
;;         (t :call))
;;   ///
;;   (defthm pterm-kind-possibilities
;;     (or (equal (pterm-kind x) :null)
;;         (equal (pterm-kind x) :var)
;;         (equal (pterm-kind x) :quote)
;;         (equal (pterm-kind x) :call))
;;     :rule-classes ((:forward-chaining :trigger-terms ((pterm-kind x))))))

(defun flextype-def-sum-kind (sum)
  (b* (((flexsum sum) sum)
       ((when (not sum.kind)) nil)
       ((mv optimized-p condform) (flextype-sum-kind-conds sum.prods sum.xvar))
       (values (flexprods->kinds sum.prods))
       (possibilities (pairlis$ (make-list (len values) :initial-element 'equal)
                                (pairlis$ (make-list (len values) :initial-element `(,sum.kind ,sum.xvar))
                                          (pairlis$ values nil))))
       (short (cat "Get the <i>kind</i> (tag) of a @(see " (xdoc::full-escape-symbol sum.name) ") structure."))
       (foo-kind-possibilities (intern-in-package-of-symbol
                                (cat (symbol-name sum.kind) "-POSSIBILITIES")
                                sum.kind))
       (foo-kind-tag-preservation-helper (intern-in-package-of-symbol
                                          (cat (symbol-name sum.kind) "-TAG-PRESERVATION-HELPER")
                                          sum.kind)))
    `((define ,sum.kind ((,sum.xvar ,sum.pred))
        :parents (,sum.name)
        :short ,short
        :returns ,(intern-in-package-of-symbol "KIND" sum.name)
        ,@(and (member :kind sum.inline) `(:inline t))
        :guard-hints (("Goal"
                       :in-theory (disable open-member-equal-on-list-of-tags))
                      (and stable-under-simplificationp
                           '(:expand ((,sum.pred ,sum.xvar)))))
        :progn t
        ,(if sum.kind-body
             `(mbe :logic ,condform
                   :exec ,sum.kind-body)
           condform)
        ///
        (defthm ,foo-kind-possibilities
          (or . ,possibilities)
          :rule-classes ((:forward-chaining :trigger-terms ((,sum.kind ,sum.xvar)))))
        ;; We add this to tag-reasoning since we rewrite tag of tagsums to
        ;; the kind function
        (add-to-ruleset std::tag-reasoning '(,foo-kind-possibilities))
        ,@(and optimized-p
               `((local (defthmd ,foo-kind-tag-preservation-helper
                          (implies (member-equal (tag x) ',values)
                                   (equal (,sum.kind x) (tag x)))
                          :hints(("Goal" :in-theory (enable consp-when-tag)))))))))))

(defun find-prod-by-kind (kind prods)
  (b* (((when (atom prods)) nil)
       ((flexprod prod) (car prods))
       ((when (eq prod.kind kind)) prod))
    (find-prod-by-kind kind (cdr prods))))



(define flexsum-kind-case-macro-spec-prods (prods)
  (if (atom prods)
      nil
    (b* (((flexprod prod) (car prods)))
      (cons (list prod.kind prod.ctor-name)
            (flexsum-kind-case-macro-spec-prods (cdr prods))))))

(define flexsum-kind-case-macro-spec (sum)
  (b* (((flexsum sum))
       (prods (flexsum-kind-case-macro-spec-prods sum.prods)))
    (list* sum.case sum.kind prods)))

(define flexsum-cond-case-macro-spec-prods (prods)
  (if (atom prods)
      nil
    (b* (((flexprod prod) (car prods)))
      (cons (list prod.kind prod.cond prod.ctor-name)
            (flexsum-cond-case-macro-spec-prods (cdr prods))))))

(define flexsum-cond-case-macro-spec (sum)
  (b* (((flexsum sum))
       (prods (flexsum-cond-case-macro-spec-prods sum.prods)))
    (list* sum.case sum.xvar prods)))


(defun flexsum-def-case-macro (sum)
  (b* (((flexsum sum) sum)
       ((unless sum.case) nil)
       (case-spec (if sum.kind
                      (flexsum-kind-case-macro-spec sum)
                    (flexsum-cond-case-macro-spec sum)))
       (kind-eq (and sum.kind (intern-in-package-of-symbol
                               (concatenate 'string (symbol-name sum.kind) "-EQ")
                               sum.kind))))
    `((defmacro ,sum.case (var-or-expr &rest args)
        ,(if sum.kind
             `(kind-casemacro-fn var-or-expr args ',case-spec)
           `(cond-casemacro-fn var-or-expr args ',case-spec)))
      ,@(and sum.kind
             `((defmacro ,kind-eq (kind keyword)
                 (declare (xargs :guard (member-eq keyword ',(flexprods->kinds sum.prods))))
                 `(eq ,kind ,keyword)))))))

(defun flextype-def-sum-kinds (sums)
  (if (atom sums)
      nil
    (append (and (eq (tag (car sums)) :sum)
                 (flextype-def-sum-kind (car sums)))
            (and (eq (tag (car sums)) :sum)
                 (flexsum-def-case-macro (car sums)))
            (flextype-def-sum-kinds (cdr sums)))))


;; ------------------ Fixing function: flexsum -----------------------

;; ((fn (pfunc-fix (car x)))
;;  (args (ptermlist-fix (cdr x))))
(defun flexprod-fields-typefix-bindings (fields)
  (b* (((when (atom fields)) nil)
       ((flexprod-field x) (car fields)))
    (cons `(,x.name ,(if x.fix
                         `(,x.fix ,x.acc-body)
                       x.acc-body))
          (flexprod-fields-typefix-bindings (cdr fields)))))

(defun flexprod-fields-reqfix-bindings (fields)
  (b* (((when (atom fields)) nil)
       ((flexprod-field x) (car fields)))
    (if (eq x.name x.reqfix)
        (flexprod-fields-reqfix-bindings (cdr fields))
      (cons (list x.name x.reqfix)
            (flexprod-fields-reqfix-bindings (cdr fields))))))

;;-----***

;;        (let* ((fn (pfunc-fix (car x)))
;;               (args (ptermlist-fix (cdr x))))
;;              (cons fn args)))
(defun flexsum-fix-prod-case (prod)
  (b* (((flexprod prod) prod)
       (typefix-bindings (flexprod-fields-typefix-bindings prod.fields))
       (reqfix-bindings (flexprod-fields-reqfix-bindings prod.fields)))
    (if typefix-bindings
        `(b* ,typefix-bindings
           ,(if reqfix-bindings
                `(let ,reqfix-bindings
                   ,prod.ctor-body)
              prod.ctor-body))
      prod.ctor-body)))

(defun flexsum-fix-cases (prods)
  (if (atom prods)
      nil
    (cons (list (flexprod->kind (car prods))
                (flexsum-fix-prod-case (car prods)))
          (flexsum-fix-cases (cdr prods)))))

(defun flexsum-fix-cases-nokind (prods)
  (if (atom prods)
      nil
    (cons (list (flexprod->cond (car prods))
                (flexsum-fix-prod-case (car prods)))
          (flexsum-fix-cases-nokind (cdr prods)))))

;; [Jared] failed attempt to speed up flexsum-fix-def
;; (defun flexsum-expand-hints-for-fix-returns-thm (pred prods)
;;   ;; Generate expand hints like (:free (x) (foo-p (cons :tag1 x)))
;;   (if (atom prods)
;;       nil
;;     (cons `(:free (x) (,pred (cons ,(flexprod->kind (car prods)) x)))
;;           (flexsum-expand-hints-for-fix-returns-thm pred (cdr prods)))))

(defun flexsum-fix-def (sum flagp)
  (b* (((flexsum sum) sum)
       ;; (fixprep (cdr (assoc :fixprep sum.kwd-alist)))
       (body (if sum.kind
                 `(case (,sum.kind ,sum.xvar)
                    . ,(flexsum-fix-cases sum.prods))
               (nice-cond (flexsum-fix-cases-nokind sum.prods))))
       (short (cat "Fixing function for @(see " (xdoc::full-escape-symbol sum.name) ") structures."))
       (newx (intern-in-package-of-symbol "NEW-X" sum.name)))
    `(define ,sum.fix ((,sum.xvar ,sum.pred))
       ;; [Jared]: previously this was:
       ;; ,@(and (member :fix sum.inline) `(:inline t))
       ;; But why not just always make these inline?  They're identity functions
       ;; after all...
       :parents (,sum.name)
       :short ,short
       :inline t
       :measure ,sum.measure
       :hints ,(and sum.kind `(("Goal" :expand ((,sum.kind ,sum.xvar)))))
       ,@(and (getarg :measure-debug nil sum.kwd-alist)
              `(:measure-debug t))
       ,@(and flagp `(:flag ,sum.name))
       :returns (,newx ,sum.pred
                       ;; [Jared] tried various ways to speed this up but it
                       ;; seems hard to come up with something that works well
                       ;; in general.
                       :hints('(:in-theory (disable ,sum.fix ,sum.pred . ,(and sum.kind `(,sum.kind)))
                                :expand ((,sum.fix ,sum.xvar)))
                              (and stable-under-simplificationp
                                   (let ((lit (car (last clause))))
                                     (and (eq (car lit) ',sum.pred)
                                          `(:expand (,lit)))))))
       :progn t
       :verify-guards nil
       (mbe :logic
            ;; ,(if fixprep
            ;; `(let* ((,sum.xvar (,fixprep ,sum.xvar)))
            ;;         ,body)
            ,body
            :exec ,sum.xvar)
       ///)))

;; ------------------ Fixing function post-events -----------------------
(defun flexsum-fix-postevents (x)
  (b* (((flexsum x) x)
       (foo-kind-possibilities (intern-in-package-of-symbol
                                (cat (symbol-name x.kind) "-POSSIBILITIES")
                                x.kind))
       (foo-kind-tag-preservation-helper (intern-in-package-of-symbol
                                          (cat (symbol-name x.kind) "-TAG-PRESERVATION-HELPER")
                                          x.kind)))
    (and x.kind
         `((local (std::enable-if-theorem ,foo-kind-tag-preservation-helper))
           (local (in-theory (disable ,foo-kind-possibilities)))
           (deffixequiv ,x.kind :args ((,x.xvar ,x.pred))
             :hints(("Goal"
                     :in-theory (acl2::e/d* ((:e member-equal) tag-reasoning)
                                            ((:rules-of-class :type-prescription :here)))
                     :expand ((,x.fix ,x.xvar)
                              (,x.kind ,x.xvar)))
                    ;; Fallback to previous hints
                    (and stable-under-simplificationp
                         '(:in-theory (enable ,x.kind)
                           :expand ((,x.fix ,x.xvar))))))

           ;; previous attempt, not sure this is relevant now that we have tag-preservation-hleper
             ;; :hints (("goal"
             ;;          ;; [Jared] this hint seems to speed up tagsums that have
             ;;          ;; a lot of cases.
             ;;          :do-not '(preprocess)
             ;;          :in-theory (union-theories '(car-cons) (theory 'minimal-theory))
             ;;          :expand ((,x.fix ,x.xvar)
             ;;                   (,x.kind ,x.xvar)
             ;;                   (:free (a b) (,x.kind (cons a b)))))
             ;;         ;; [Jared] this shouldn't be necessary for tagsums but it's
             ;;         ;; what we used to do, and it may be a good fallback for
             ;;         ;; flexsums.
             ;;         (and stable-under-simplificationp
             ;;              '(:do-not nil
             ;;                :in-theory (enable ,x.kind)
             ;;                :expand ((,x.fix ,x.xvar))))))
           (local (std::disable-if-theorem ,foo-kind-tag-preservation-helper))

           (make-event
            (b* ((consp-when-foo-p ',(intern-in-package-of-symbol (cat "CONSP-WHEN-" (symbol-name x.pred))
                                                                  x.pred))
                 (sum.xvar ',x.xvar)
                 (sum.fix ',x.fix)
                 (consp-of-fix ',(intern-in-package-of-symbol (cat "CONSP-OF-" (symbol-name x.fix))
                                                              x.fix))
                 ((unless (fgetprop consp-when-foo-p 'acl2::theorem nil (w state)))
                  '(value-triple :skip-type-prescription)))
              `(defthm ,consp-of-fix
                 (consp (,sum.fix ,sum.xvar))
                 :hints (("goal" :use ((:instance ,consp-when-foo-p
                                        (,sum.xvar (,sum.fix ,sum.xvar))))
                          :in-theory (disable ,consp-when-foo-p)))
                 :rule-classes :type-prescription)))))))

(defun flexsum-fix-when-pred-thm (x flagp)
  (b* (((flexsum x) x)
       (foo-fix-when-foo-p (intern-in-package-of-symbol
                            (cat (symbol-name x.fix) "-WHEN-" (symbol-name x.pred))
                            x.fix)))
    `(defthm ,foo-fix-when-foo-p
       (implies (,x.pred ,x.xvar)
                (equal (,x.fix ,x.xvar) ,x.xvar))
       :hints ('(:expand ((,x.pred ,x.xvar)
                          (,x.fix ,x.xvar)
                          ,@(and x.kind `((,x.kind ,x.xvar))))
                 :in-theory (disable ,x.pred ,x.fix)))
       . ,(and flagp `(:flag ,x.name)))))




;; ------------------ Product accessors -----------------------

(defun flexprod-field-acc (x prod sum)
  (b* (((flexsum sum) sum)
       ((flexprod prod) prod)
       ((flexprod-field x) x)
       ;; (fixprep (cdr (assoc :fixprep sum.kwd-alist)))
       (short (b* ((acc nil)
                   (acc (revappend-chars "Get the <tt>@(sym " acc))
                   (acc (revappend-chars (xdoc::full-escape-symbol x.name) acc))
                   (acc (revappend-chars ")</tt> field from a @(see? " acc))
                   (acc (revappend-chars (xdoc::full-escape-symbol prod.type-name) acc))
                   (acc (revappend-chars ")." acc)))
                (rchars-to-string acc)))
       (long  "<p>This is an ordinary field accessor created by @(see fty::defprod).</p>"))
    `((define ,x.acc-name ((,sum.xvar ,sum.pred))
        :parents (,prod.type-name)
        :short ,short
        :long ,long
        ,@(and (member :acc prod.inline) `(:inline t))
        :guard ,prod.guard
        :guard-hints (("goal"
                       :expand ((,sum.pred ,sum.xvar)
                                . ,(and sum.kind `((,sum.kind ,sum.xvar))))))


 ; )
;                       . ,(and sum.kind
;                               `(:in-theory (enable ,sum.kind)))))
        :returns ,(if x.type
                      `(,x.name ,x.type ,@x.rule-classes)
                                ;; . ,(and sum.kind
                                ;;         `(:hints (("goal" :in-theory (enable ,sum.kind))))))
                    `(x.name))
        :progn t
        (mbe :logic ,(if (eq x.reqfix x.name)
                         `(b* ((,sum.xvar (and ,prod.guard ,sum.xvar)))
                            ,(if x.fix
                                 `(,x.fix ,x.acc-body)
                               x.acc-body))
                       `(b* ((,sum.xvar (and ,prod.guard ,sum.xvar))
                             . ,(flexprod-fields-typefix-bindings prod.fields))
                          ,x.reqfix))
             ;; (let* ((unfixbody (nice-and prod.guard x.acc-body))
             ;;                (body (if x.fix
             ;;                          `(,x.fix ,unfixbody)
             ;;                        unfixbody)))
             ;;   body)
             :exec ,x.acc-body)
        ///
        (deffixequiv ,x.acc-name
          :hints (,@(and sum.kind
                         `(("goal"
                            :in-theory (disable ,sum.kind))))
                  (and stable-under-simplificationp
                       '(,@(and sum.kind `(:in-theory (enable ,sum.kind)))
                         :expand ((,sum.fix ,sum.xvar))))))

        ,@(and (not (eq prod.guard t))
               `((defthmd ,(intern-in-package-of-symbol (cat (symbol-name x.acc-name) "-WHEN-WRONG-KIND")
                                                        x.acc-name)
                   (implies (not ,prod.guard)
                            (equal (,x.acc-name ,sum.xvar)
                                   ,(if (eq x.reqfix x.name)
                                        (if x.fix
                                            `(,x.fix nil)
                                          nil)
                                      `(b* ((,sum.xvar nil)
                                            . ,(flexprod-fields-typefix-bindings prod.fields))
                                         ,x.reqfix))))
                   :hints(("Goal" :in-theory
                           (disable ,@(and sum.kind `(,sum.kind)))))))))

      (local (in-theory (enable ,x.acc-name))))))

(defun flexprod-field-acc-lst (fields prod sum)
  (if (atom fields)
      nil
    (append (flexprod-field-acc (car fields) prod sum)
            (flexprod-field-acc-lst (cdr fields) prod sum))))

(defun flexprod-field-accessors (prod sum)
  (flexprod-field-acc-lst (flexprod->fields prod) prod sum))

;; ------------------ Product constructor -----------------------

(defun flexprod-field-names-types (fields)
  (if (atom fields)
      nil
    (cons (b* (((flexprod-field x) (car fields)))
            (if x.type
                (list x.name x.type)
              (list x.name)))
          (flexprod-field-names-types (cdr fields)))))

(defun flexprod-fields-mbe-typefix-bindings (fields)
  (b* (((when (atom fields)) nil)
       ((flexprod-field x) (car fields))
       ((unless x.fix)
        (flexprod-fields-mbe-typefix-bindings (cdr fields))))
    (cons `(,x.name (mbe :logic (,x.fix ,x.name)
                         :exec ,x.name))
          (flexprod-fields-mbe-typefix-bindings (cdr fields)))))

(defun flexprod-fields-mbe-reqfix-bindings (fields)
  (b* (((when (atom fields)) nil)
       ((flexprod-field x) (car fields))
       ((when (eq x.reqfix x.name))
        (flexprod-fields-mbe-reqfix-bindings (cdr fields))))
    (cons `(,x.name (mbe :logic ,x.reqfix
                         :exec ,x.name))
          (flexprod-fields-mbe-reqfix-bindings (cdr fields)))))

(defun flexprod-ctor-call (prod)
  (b* (((flexprod prod) prod))
    (cons prod.ctor-name (flexprod-fields->names prod.fields))))

(defun flexprod-fields-ignorable-typefix-bindings (fields)
  (b* (((when (atom fields)) nil)
       ((flexprod-field x) (car fields))
       ((unless x.fix)
        (flexprod-fields-mbe-typefix-bindings (cdr fields))))
    (cons `(,(intern-in-package-of-symbol (concatenate 'string "?" (symbol-name x.name)) x.name)
            (,x.fix ,x.name))
          (flexprod-fields-ignorable-typefix-bindings (cdr fields)))))

;;     (defthm pterm-varname-of-pterm-var
;;       (equal (pterm-varname (pterm-var varname))
;;              (var-fix varname)))
(defun flexprod-acc-of-ctor-thms1 (fields all-fields ctor-call)
  (b* (((when (atom fields)) nil)
       ((flexprod-field x) (car fields))
       (fixterm (if (eq x.reqfix x.name)
                    (if x.fix
                      `(,x.fix ,x.name)
                    x.name)
                  `(b* ,(flexprod-fields-ignorable-typefix-bindings all-fields)
                     ,x.reqfix)))
       (foo->bar-of-foo (intern-in-package-of-symbol
                         (cat (symbol-name x.acc-name) "-OF-" (symbol-name (car ctor-call)))
                         x.acc-name)))
    (cons `(defthm ,foo->bar-of-foo
             (equal (,x.acc-name ,ctor-call)
                    ,fixterm)
             :hints(("Goal" :in-theory (e/d (,x.acc-name)
                                            (,(car ctor-call))))
                    (and stable-under-simplificationp
                         '(:in-theory (enable ,(car ctor-call))))))
          (flexprod-acc-of-ctor-thms1 (cdr fields) all-fields ctor-call))))

(defun flexprod-acc-of-ctor-thms (prod)
  (flexprod-acc-of-ctor-thms1 (flexprod->fields prod)
                              (flexprod->fields prod)
                              (flexprod-ctor-call prod)))

(defun flexprod-fields-acc-calls (fields xvar)
  (if (atom fields)
      nil
    (cons `(,(flexprod-field->acc-name (car fields)) ,xvar)
          (flexprod-fields-acc-calls (cdr fields) xvar))))

(defun flexprod-equal-of-field-accessors (fields all-fields xvar)
  (if (atom fields)
      nil
    (cons (b* (((flexprod-field x) (car fields)))
            `(equal (,x.acc-name ,xvar)
                    ,(if (eq x.reqfix x.name)
                         (if x.fix
                             `(,x.fix ,x.name)
                           x.name)
                       `(b* ,(flexprod-fields-ignorable-typefix-bindings all-fields)
                          ,x.reqfix))))
          (flexprod-equal-of-field-accessors (cdr fields) all-fields xvar))))

(defun flexprod-fields-macro-args (x)
  (b* (((when (atom x)) nil)
       ((flexprod-field f) (car x)))
    (cons `(,f.name ',f.default)
          (flexprod-fields-macro-args (cdr x)))))

(defun flexprod-fields-bind-accessors (x xvar)
  (b* (((when (atom x)) nil)
       ((flexprod-field f) (car x)))
    (cons (list (intern-in-package-of-symbol (cat "?" (symbol-name f.name))
                                             f.name)
                `(,f.acc-name ,xvar))
          (flexprod-fields-bind-accessors (cdr x) xvar))))



(defun flexprod-remaker (prod sum)
  ;; Returns EVENTS
  (b* (((flexsum sum) sum)
       ((flexprod prod) prod)
       ((unless prod.remake-name)
        ;; This product isn't going to have a remake function.
        nil)
       (fieldnames   (flexprod-fields->names prod.fields))
       (fields/types (flexprod-field-names-types prod.fields)))
    `((define ,prod.remake-name
        ;; The formals: the original "X" followed by the new values for its fields
        ((,sum.xvar ,sum.pred) . ,fields/types)
        :guard ,(nice-and prod.guard   ;; The guard for "X"
                          prod.require ;; Dependent requirements if applicable
                          )
        ;; We won't generate any documentation for the remake function, because
        ;; it's just an implementation detail of the change macro.  The user
        ;; should always use the change macro instead and ideally nobody ever
        ;; needs to know that remake functions even exist.
        :parents nil
        ;; Do we want to inline this?  Probably not.  But since the remake
        ;; function is essentially another constructor, let's inline it exactly
        ;; if we are inlining the constructor.
        ,@(and (member :xtor prod.inline) `(:inline t))
        ;; We don't need to provide a :returns specifier because we're just
        ;; going to leave this enabled.
        :hooks nil
        :progn t
        :enabled t
        ;; I don't think we need to do any special fixing here because our
        ;; logical story is that we're just calling the constructor.
        (mbe :logic (,prod.ctor-name . ,fieldnames)
             :exec ,prod.remake-body)
        :guard-hints(("Goal"
                      :in-theory (enable ,sum.pred . ,(and sum.kind `(,sum.kind)))
                      :expand ((,prod.ctor-name . ,fieldnames)
                               (,sum.pred ,sum.xvar))))))))

(defun flexprod-constructor (prod sum)
  (b* (((flexsum sum) sum)
       ((flexprod prod) prod)
       (field-calls (flexprod-fields-acc-calls prod.fields sum.xvar))
       (fieldnames (flexprod-fields->names prod.fields))
       (field-accs (pairlis$ fieldnames
                             (flexprod-fields->acc-names prod.fields)))
       (binder-accs (append field-accs
                            (append
                             (extra-binder-names->acc-alist
                              prod.extra-binder-names prod.type-name))))
       (foo-of-fields
        (intern-in-package-of-symbol (cat (symbol-name prod.ctor-name) "-OF-FIELDS")
                                     prod.ctor-name))
       (foo-fix-when-foo-kind
        (intern-in-package-of-symbol (cat (symbol-name sum.fix) "-WHEN-" (symbol-name prod.kind))
                                     sum.fix))
       (equal-of-foo
        (intern-in-package-of-symbol (cat "EQUAL-OF-" (symbol-name prod.ctor-name))
                                     prod.ctor-name))

       (typefixes (flexprod-fields-mbe-typefix-bindings prod.fields))
       (reqfixes (flexprod-fields-mbe-reqfix-bindings prod.fields))

       (reqfix-body (if reqfixes
                        `(let ,reqfixes ,prod.ctor-body)
                      prod.ctor-body))

       (typefix-body (if typefixes
                         `(b* ,typefixes ,reqfix-body)
                       reqfix-body))

       ;; (othervar (intern-in-package-of-symbol
       ;;            (if (equal (symbol-name sum.xvar) "X") "Y" "X")
       ;;            prod.ctor-name))
       )
    `((define ,prod.ctor-name ,(flexprod-field-names-types prod.fields)
        ;; explicitly turn off parents because it's likely to be the same as
        ;; the name for the type.
        :parents nil
        ,@(and (member :xtor prod.inline) `(:inline t))
        :guard ,prod.require
        :returns (,sum.xvar ,(if (eq prod.guard t)
                                 sum.pred
                               `(and (,sum.pred ,sum.xvar)
                                     ,prod.guard)) ;; (equal (,sum.kind ,sum.xvar) ,prod.kind)
                        :hints(("Goal" :in-theory (enable ,sum.pred
                                                          . ,(and sum.kind `(,sum.kind))))))
        :progn t
        ,typefix-body
        ///
        ;; [Jared] delaying the fixequiv until after the equal-of proof seems to
        ;; be better for large products.
        ;; (deffixequiv ,prod.ctor-name)

        ,@(flexprod-acc-of-ctor-thms prod)

        ,@(and (not (eq prod.require t))
               (let ((foo-requirements (intern-in-package-of-symbol
                                        (cat (symbol-name prod.ctor-name) "-REQUIREMENTS")
                                        prod.ctor-name)))
                 `((defthm ,foo-requirements
                     (b* ,(flexprod-fields-bind-accessors prod.fields sum.xvar)
                       ,prod.require)))))

        ,@(and
           ;; special case: we can have an empty product, in which case we don't
           ;; want a rule like (equal (my-const-product) (my-sum-fix x))
           (consp prod.fields)
           `((defthm ,foo-of-fields
               ,(nice-implies prod.guard
                              `(equal (,prod.ctor-name . ,field-calls)
                                      (,sum.fix ,sum.xvar)))
               :hints(("Goal" ;; :in-theory (enable ,sum.fix)
                       :expand ((,sum.fix ,sum.xvar)))))))

        (,(if (atom prod.fields) 'defthm 'defthmd)
               ;; ,(if (eq prod.guard t) 'defthmd 'defthm)
         ,foo-fix-when-foo-kind
          ,(nice-implies prod.guard
                         `(equal (,sum.fix ,sum.xvar)
                                 (,prod.ctor-name . ,field-calls)))
          :hints(("Goal" ;; :in-theory (enable ,sum.fix)
                  :expand ((,sum.fix ,sum.xvar))))
          . ,(and (not (eq prod.guard t))
                  '(:rule-classes ((:rewrite :backchain-limit-lst 0)))))

        (defthm ,equal-of-foo
          (equal (equal ,(flexprod-ctor-call prod) ,sum.xvar)
                 (and (,sum.pred ,sum.xvar)
                      ,@(and (not (eq prod.guard t)) (list prod.guard))
                      . ,(flexprod-equal-of-field-accessors prod.fields prod.fields sum.xvar)))
          :hints (("goal" :in-theory (acl2::disable*
                                      ,prod.ctor-name
                                      ,@(flexprod-fields->acc-names prod.fields)
                                      ,@(and sum.kind `(,sum.kind))
                                      ,@(if (consp prod.fields)
                                            `(,foo-of-fields)
                                          `(,foo-fix-when-foo-kind))
                                      ;; [Jared] speed hint
                                      deftypes-temp-thms
                                      (:rules-of-class :forward-chaining :here)
                                      (:rules-of-class :type-prescription :here)
                                      )
                   ,@(if (consp prod.fields)
                         `(:use ,foo-of-fields)
                       `(:use ,foo-fix-when-foo-kind)))
                  (and stable-under-simplificationp
                       '(:in-theory (acl2::e/d*
                                     (,prod.ctor-name)
                                     (,@(flexprod-fields->acc-names prod.fields)
                                      ,@(and sum.kind `(,sum.kind))
                                      ,@(if (consp prod.fields)
                                            `(,foo-of-fields)
                                          `(,foo-fix-when-foo-kind))
                                      ;; [Jared] speed hint
                                      deftypes-temp-thms
                                      (:rules-of-class :forward-chaining :here)
                                      (:rules-of-class :type-prescription :here)
                                      ))))))

        ;; [Jared] delaying the fixequiv until after the equal-of proof seems to
        ;; be better for large products.
        (deffixequiv ,prod.ctor-name)

        ;; :hints (("goal" :expand ((,sum.pred ,sum.xvar))
        ;;          :in-theory (disable ,(intern-in-package-of-symbol
        ;;                                (cat
        ;;                                             (symbol-name sum.fix)
        ;;                                             "-WHEN-"
        ;;                                             (symbol-name prod.kind))
        ;;                                sum.fix))))

        ;; ,@(and (consp prod.fields)
        ;;        `((defthm ,(intern-in-package-of-symbol
        ;;                    (cat
        ;;                                 "EQUAL-OF-"
        ;;                                 (symbol-name sum.fix)
        ;;                                 "-WHEN-"
        ;;                                 (symbol-name prod.kind))
        ;;                    prod.ctor-name)
        ;;            ,(nice-implies prod.guard
        ;;                           (equal (equal (,sum.fix ,sum.xvar) ,othervar)
        ;;                                  (and (,sum.pred ,othervar)
        ;;                                       ,@(and (not (eq prod.guard t))
        ;;                                              `(let ((,sum.xvar ,othervar))
        ;;                                                 (list prod.guard)))
        ;;                                       . ,(flexprod-equal-of-field-accessors prod.fields sum.xvar)))
        ;;                           :hints (("goal" :expand ((,sum.pred ,sum.xvar))
        ;;                                    :in-theory (disable ,(intern-in-package-of-symbol
        ;;                                                          (cat
        ;;                                                                       (symbol-name sum.fix)
        ;;                                                                       "-WHEN-"
        ;;                                                                       (symbol-name prod.kind))
        ;;                                                          sum.fix))))))))

        (acl2::def-b*-binder ,prod.ctor-name
          :body
          (std::da-patbind-fn ',prod.ctor-name
                              ',binder-accs
                              acl2::args acl2::forms acl2::rest-expr))

        ,@(and (not prod.no-ctor-macros)
               `(,(std::da-make-maker prod.ctor-name fieldnames
                                      (flexprod-fields->defaults prod.fields))
                 ,(std::da-make-changer prod.ctor-name fieldnames prod.remake-name))))

      (local (in-theory (enable ,prod.ctor-name))))))


;; ------------ Collect accessor/constructor names ---------------

(defun flexprod-fns (prod)
  (b* (((flexprod prod) prod))
    (cons prod.ctor-name
          (flexprod-fields->acc-names prod.fields))))

(defun flexsum-prod-fns (prods)
  (if (atom prods)
      nil
    (append (flexprod-fns (car prods))
            (flexsum-prod-fns (cdr prods)))))

(defun flexsum-prod-ctors (prods)
  (if (atom prods)
      nil
    (cons (flexprod->ctor-name (car prods))
          (flexsum-prod-ctors (cdr prods)))))

(defun flexsum-fns (x)
  (b* (((flexsum x) x)
       (fns1
        (list* x.pred
               x.fix
               (flexsum-prod-fns x.prods))))
    (if x.kind
        (cons x.kind fns1)
      fns1)))

;; ------------ Collect accessor/constructor definitions ---------------
(defun flexprod-accessor/constructors (prod sum)
  (append (flexprod-field-accessors prod sum)
          (flexprod-constructor prod sum)
          (flexprod-remaker prod sum)))

(defun flexsum-prods-accessor/constructors (prods sum)
  (if (atom prods)
      nil
    (append (flexprod-accessor/constructors (car prods) sum)
            (flexsum-prods-accessor/constructors (Cdr prods) sum))))

(defun flexprod-x-dot-fields (xvar fields)
  (if (atom fields)
      nil
    (cons (let ((name (flexprod-field->name (car fields))))
            (intern-in-package-of-symbol (cat (symbol-name xvar) "." (symbol-name name))
                                         name))
          (flexprod-x-dot-fields xvar (cdr fields)))))

(defun flexsum-fix-redef-prod-cases (prods xvar)
  (if (atom prods)
      nil
    (b* (((flexprod prod) (car prods)))
      (cons `(,prod.kind (,prod.ctor-name . ,(flexprod-fields-acc-calls prod.fields xvar)))
            (flexsum-fix-redef-prod-cases (cdr prods) xvar)))))

(defun flexsum-fix-redef-prod-cases-nokind (prods xvar)
  (if (atom prods)
      nil
    (b* (((flexprod prod) (car prods)))
      (cons `(,prod.cond (,prod.ctor-name . ,(flexprod-fields-acc-calls prod.fields xvar)))
            (flexsum-fix-redef-prod-cases-nokind (cdr prods) xvar)))))

(defun flextypelist-fixes (types)
  (if (atom types)
      nil
    (cons (with-flextype-bindings (x (car types)) x.fix)
          (flextypelist-fixes (cdr types)))))

(defun flexsum-acc/ctor-events (sum types)
  (declare (ignorable types))
  (b* (((flexsum sum) sum)
       (foo-fix-redef (intern-in-package-of-symbol (cat (symbol-name sum.fix) "-REDEF")
                                                   sum.fix)))
    (append (flexsum-prods-accessor/constructors sum.prods sum)
            `((defthmd ,foo-fix-redef
                (equal (,sum.fix ,sum.xvar)
                       ,(if sum.kind
                            `(case (,sum.kind ,sum.xvar)
                               . ,(flexsum-fix-redef-prod-cases sum.prods sum.xvar))
                          (nice-cond (flexsum-fix-redef-prod-cases-nokind sum.prods sum.xvar))))
                :hints(("Goal" :in-theory (e/d ,(and sum.kind
                                                     (list (intern-in-package-of-symbol
                                                            (cat (symbol-name sum.kind) "-POSSIBILITIES")
                                                            sum.kind)))
                                               ,(flexsum-fns sum)))
                       (and stable-under-simplificationp
                            '(:expand (,sum.fix ,sum.xvar))))
                :rule-classes :definition)))))

(defun flextypes-sum-accessor/constructors (types alltypes)
  (if (atom types)
      nil
    (append (and (eq (tag (car types)) :sum)
                 (flexsum-acc/ctor-events (car types) alltypes))
            (flextypes-sum-accessor/constructors (cdr types) alltypes))))



;; ------------------ Count definition: flexsum -----------------------

(defun flexprod-field-count (x xvar types)
  (b* (((flexprod-field x) x)
       ((unless x.type) nil)
       (type-count (flextypes-find-count-for-pred x.type types))
       ((unless type-count) nil))
    `((,type-count (,x.acc-name ,xvar)))))

(defun flexprod-field-counts (fields xvar types)
  (if (atom fields)
      nil
    (append (flexprod-field-count (car fields) xvar types)
            (flexprod-field-counts (cdr fields) xvar types))))

(defun flexsum-prod-counts (prods xvar types)
  (b* (((when (atom prods)) nil)
       ((flexprod x) (car prods))
       (fieldcounts (flexprod-field-counts x.fields xvar types))
       (count (if fieldcounts `(+ ,(+ 1 (len x.fields)) . ,fieldcounts) 1))
       (count (if x.count-incr `(+ 1 ,count) count)))
    (cons `(,x.kind ,count)
          (flexsum-prod-counts (cdr prods) xvar types))))

(defun flexsum-prod-counts-nokind (prods xvar types)
  (b* (((when (atom prods)) nil)
       ((flexprod x) (car prods))
       (fieldcounts (flexprod-field-counts x.fields xvar types))
       (prodcount (if fieldcounts
                      `(+ ,(+ 1 (len x.fields)) . ,fieldcounts)
                    1))
       (prodcount (if x.count-incr `(+ 1 ,prodcount) prodcount)))
    (cons `(,x.cond ,prodcount)
          (flexsum-prod-counts-nokind (cdr prods) xvar types))))

(defun flexsum-count (x types)
  (b* (((flexsum x) x)
       ((unless x.count) nil)
       (short (cat "Measure for recurring over @(see "
                   (xdoc::full-escape-symbol x.name)
                   ") structures.")))
    `((define ,x.count ((,x.xvar ,x.pred))
        :parents (,x.name)
        :short ,short
        :verify-guards nil
        :returns (count natp
                        :rule-classes :type-prescription
                        :hints ('(:expand (,x.count ,x.xvar)
                                  :in-theory (e/d ,(and x.kind
                                                        (list (intern-in-package-of-symbol
                                                               (cat (symbol-name x.kind) "-POSSIBILITIES")
                                                               x.kind)))
                                                  (,x.count . ,(flexsum-prod-fns x.prods))))))
        :measure (let ((,x.xvar (,x.fix ,x.xvar)))
                   ,x.measure)
       ,@(and (getarg :measure-debug nil x.kwd-alist)
              `(:measure-debug t))
        :progn t
        ,(if x.kind
             `(case (,x.kind ,x.xvar)
                . ,(flexsum-prod-counts x.prods x.xvar types))
           (nice-cond (flexsum-prod-counts-nokind x.prods x.xvar types)))))))

;; ------------------ Count post-events: flexsum -----------------------
(defun flexprod-field-count-thm (x prod sum types)
  (b* (((flexprod-field x) x)
       ((unless x.type) nil)
       (type-count (flextypes-find-count-for-pred x.type types))
       ((unless type-count) nil)
       ((flexprod prod) prod)
       ((flexsum sum) sum)
       (bar-count-of-foo->bar (intern-in-package-of-symbol
                               (cat (symbol-name type-count) "-OF-" (symbol-name x.acc-name))
                               x.acc-name)))
    `((defthm ,bar-count-of-foo->bar
        ,(nice-implies prod.guard
                       `(< (,type-count (,x.acc-name ,sum.xvar))
                           (,sum.count ,sum.xvar)))
        :hints (("goal" :in-theory (disable ,type-count
                                            ,x.acc-name
                                            ,sum.count
                                            . ,(and sum.kind `(,sum.kind)))
                 :expand ((,sum.count ,sum.xvar))))
        :rule-classes :linear))))

(defun flexprod-field-count-thms (fields prod sum types)
  (if (atom fields)
      nil
    (append (flexprod-field-count-thm (car fields) prod sum types)
            (flexprod-field-count-thms (cdr fields) prod sum types))))

(defun flexprod-field-count-var (x types)
  (b* (((flexprod-field x) x)
       ((unless x.type) nil)
       (type-count (flextypes-find-count-for-pred x.type types))
       ((unless type-count) nil))
    `((,type-count ,x.name))))

(defun flexprod-field-counts-vars (fields types)
  (if (atom fields)
      nil
    (append (flexprod-field-count-var (car fields) types)
            (flexprod-field-counts-vars (cdr fields) types))))

(defun flexprod-ctor-count-thm (prod sum types)
  (b* (((flexprod x) prod)
       ;; ((unless (flexprod-fields-check-reqfixes x.fields types)) nil)
       ((flexsum sum) sum)
       (call (flexprod-ctor-call prod))
       (field-counts (flexprod-field-counts-vars x.fields types))
       ((when (not field-counts)) nil)
       (body `(< (+ . ,field-counts)
                 (,sum.count ,call)))
       (foo-count-of-foo (intern-in-package-of-symbol
                          (cat (symbol-name sum.count) "-OF-" (symbol-name x.ctor-name))
                          sum.count)))
    `((defthm ,foo-count-of-foo
        ,(if x.require
             ;; NOTE: Not sure this makes sense, but is necessary in at least
             ;; some cases, e.g.: requirement that arglist arity matches lambda
             ;; formals arity.
             `(implies ,x.require
                       ,body)
           body)
        :hints (("goal" :expand ((,sum.count ,call))))
        :rule-classes :linear))))

(defun flexsum-prod-count-thms (prods sum types)
  (if (atom prods)
      nil
    (append (flexprod-ctor-count-thm (car prods) sum types)
            (flexprod-field-count-thms (flexprod->fields (car prods))
                                       (car prods) sum types)
            (flexsum-prod-count-thms (cdr prods) sum types))))

(defun flexsum-count-post-events (x alltypes)
  (b* (((flexsum x) x)
       ((unless x.count) nil))
    (flexsum-prod-count-thms x.prods x alltypes)))




;; ------------

(defun flexprod-fields-collect-fix/pred-pairs (fields)
  (if (atom fields)
      nil
    (b* (((flexprod-field x) (car fields)))
      (if (and x.fix x.type)
          (cons (cons x.fix x.type)
                (flexprod-fields-collect-fix/pred-pairs (cdr fields)))
        (flexprod-fields-collect-fix/pred-pairs (cdr fields))))))

(defun flexprods-collect-fix/pred-pairs (prods)
  (if (atom prods)
      nil
    (append (flexprod-fields-collect-fix/pred-pairs (flexprod->fields (car prods)))
            (flexprods-collect-fix/pred-pairs (cdr prods)))))

(defun flexsum-collect-fix/pred-pairs (sum)
  (flexprods-collect-fix/pred-pairs (flexsum->prods sum)))
