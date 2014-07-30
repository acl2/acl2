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
(include-book "std/util/da-base" :dir :system)
(include-book "std/util/deflist-base" :dir :system)
(include-book "fixequiv")
(include-book "tools/rulesets" :dir :system)
(include-book "misc/hons-help" :dir :system) ;; for hons-list
(include-book "xdoc/names" :dir :system)
(set-state-ok t)

(def-ruleset! std::tag-reasoning nil)

;; Lemmas for deftagprod.
(defthmd equal-of-strip-cars
  (implies (syntaxp (quotep y))
           (equal (equal (strip-cars x) y)
                  (if (atom y)
                      (and (not y) (atom x))
                    (and (consp x)
                         (equal (strip-cars (cdr x)) (cdr y))
                         (if (car y)
                             (and (consp (car x))
                                  (equal (caar x) (car y)))
                           (or (atom (car x))
                               (equal (caar x) nil))))))))

;; seems generally good so we'll leave it enabled
(defthm strip-cars-under-iff
  (iff (strip-cars x) (consp x)))


#||
(define symbol-fix (x)
  :returns (xx symbolp)
  (declare (xargs :guard t))
  (if (symbolp x) x 'foo)
  ///
  (defthm symbol-fix-when-symbolp
    (implies (symbolp x)
             (equal (symbol-fix x) x)))
  (deffixtype symbol :pred symbolp :fix symbol-fix :equiv symbol-equiv :define t)

  (defthm symbol-fix-not-quote
    (equal (equal (symbol-fix x) 'quote)
           (equal x 'quote))))

(define symbol-list-fix (x)
  :returns (xx symbol-listp)
  (declare (xargs :guard t))
  (if (atom x)
      nil
    (cons (symbol-fix (car X))
          (symbol-list-fix (cdr x))))
  ///
  (defthm symbol-list-fix-when-symbol-listp
    (implies (symbol-listp x)
             (equal (symbol-list-fix x) x)))
  (deffixtype symbol :pred symbol-listp :fix symbol-list-fix
    :equiv symbol-list-equiv :define t))

(deftypes pterm3
  (defflexsum pterm3
    (:var
     :cond (atom x)
     :fields ((name :acc-body x :type symbolp))
     :ctor-body name)
    (:quote
     :cond (eq (car x) 'quote)
     :shape (and (consp (cdr x))
                   (not (cddr x)))
     :fields ((val :acc-body (cadr x)))
     :ctor-body (list 'quote val))
    (:call
     :fields ((fn :acc-body (car x) :type pfun3-p)
              (args :acc-body (cdr x) :type pterm3list-p))
     :ctor-body (cons fn args)))
  (defflexsum pfun3
    (:sym
     :cond (atom x)
     :fields ((fnname :acc-body x :type symbolp))
     :ctor-body fnname)
    (:lambda
     :shape (and (eq (car x) 'lambda)
                   (true-listp x)
                   (eql (len x) 3))
     :fields ((formals :acc-body (cadr x) :type symbol-listp)
              (body :acc-body (caddr x) :type pterm3-p))
     :ctor-body (list 'lambda formals body)))

  (deflist pterm3list :elt-type pterm3-p))
||#

(program)

;; ------------------------- Misc Utilities ------------------------

(defmacro revappend-chars (x y)
  `(str::revappend-chars ,x ,y))

(defmacro rchars-to-string (x)
  `(str::rchars-to-string ,x))

(defun html-encode-str (x acc)
  (xdoc::simple-html-encode-str x 0 (length x) acc))

(defmacro cat (&rest args)
  `(str::cat . ,args))

(defconst *nl* (str::implode (list #\Newline)))

(defun nice-and (x y)
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

(defun nice-or (x y)
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

(defun nice-implies (x y)
  (cond ((eq x t) y)
        ((eq y t) t)
        ((eq x nil) t)
        ((eq y nil) x)
        (t `(implies ,x ,y))))

(defun nice-cond (x)
  (cond ((atom x) nil)
        ((eq (caar x) t) (cadar x))
        (t `(cond . ,x))))

(defun find-fixtype (typename alist)
  (or (find-fixtype-for-typename typename alist)
      (find-fixtype-for-pred typename alist)))

(defun get-pred/fix/equiv (kwd-alist our-fixtypes fixtypes typekw)
  (b* ((type (getarg typekw nil kwd-alist))
       ((unless type) (mv nil nil 'equal nil))
       (fixtype1 (find-fixtype type our-fixtypes))
       (fixtype (or fixtype1 (find-fixtype type fixtypes)))
       ((unless fixtype)
        (er hard? 'get-type-and-fix
            "Type ~x0 doesn't have an associated fixing function.  Please ~
             provide that association using ~x1.~%" type 'deffixtype)
        (mv nil nil 'equal nil)))
    (mv (fixtype->pred fixtype) (fixtype->fix fixtype)
        (fixtype->equiv fixtype)
        (and fixtype1 t))))

(defmacro getarg-nonnil! (key default kwd-alist)
  `(let* ((getarg-look (assoc ,key ,kwd-alist)))
     (or (and getarg-look
              (cdr getarg-look))
         ,default)))

(defmacro getarg!  (key default kwd-alist)
  `(let* ((getarg-look (assoc ,key ,kwd-alist)))
     (if getarg-look
         (cdr getarg-look)
       ,default)))

(defun dumb-append-conjunct (rev-prev-conds newcond)
  (cond ((or (eq newcond t)
             (eq newcond ''t)) (reverse rev-prev-conds))
        ((or (eq newcond nil)
             (eq newcond ''nil)) (list nil))
        (t (revappend rev-prev-conds (list newcond)))))

(defun dumb-cons-conjunct (newcond conds)
  (cond ((or (eq newcond t)
             (eq newcond ''t)) conds)
        ((or (eq newcond nil)
             (eq newcond ''nil)) (list nil))
        (t (cons newcond conds))))

(defconst *inline-keywords* '(:kind :fix :acc :xtor))
(defconst *inline-defaults* '(:kind :fix :acc))

(defun get-deftypes-inline-opt (default kwd-alist)
  (b* ((inline (getarg :inline default kwd-alist))
       (inline (if (eq inline :all) *inline-keywords* inline))
       ((unless (subsetp inline *inline-keywords*))
        (er hard? 'get-deftypes-inline-opt
            ":inline must be a subset of ~x0, but is ~x1"
            *inline-keywords* inline)))
    inline))

(defun flextype-get-count-fn (name kwd-alist)
  ;; :count nil means the same as no-count
  (b* ((count-look (assoc :count kwd-alist))
       (no-count (getarg :no-count nil kwd-alist))
       ((when (and (cdr count-look) no-count))
        (er hard? 'defflextype
            "Confused: a count function name was provided with :no-count t")))
    (if count-look
        (cdr count-look)
      (and (not (getarg :no-count nil kwd-alist))
           (intern-in-package-of-symbol (cat (symbol-name name) "-COUNT")
                                        name)))))


;; ------------------------- Flexsum Parsing -----------------------

;; --- Flexprod Fields ---
(def-primitive-aggregate flexprod-field
  (name     ;; field name
   acc-body ;; accessor body, without fixing
   acc-name  ;; accessor function name
   type     ;; element type, or nil
   fix      ;; element fix, or nil
   equiv    ;; element equiv, or nil
   ;; require ;; dependent type constraint (term) -- now associated with product, not field
   reqfix  ;; dependent type fix (term)
   default  ;; default value
   doc      ;; not yet used
   rule-classes ;; for return type theorem, either empty (default) or of the form (:rule-classes ...)
   recp ;; is the field type part of the mutual recursion
   ))

(defconst *flexprod-field-keywords*
  '(:type
    :acc-body
    :acc-name
    :default
    :doc
    :rule-classes
    :reqfix))

(defun parse-flexprod-field (x type-name our-fixtypes fixtypes)
  (b* (((cons name kws) x)
       ((unless (symbolp name))
        (er hard? 'parse-flexprod-field
            "Malformed field: ~x0: first element should be the name, a symbol." x))
       ((mv kwd-alist rest)
        (extract-keywords 'parse-flexprod-field *flexprod-field-keywords* kws nil))
       ((when rest)
        (er hard? 'parse-flexprod-field
            "Malformed field: ~x0: after name should be a keyword/value list." x))
       (acc-body (getarg :acc-body 0 kwd-alist))
       ((unless (or (symbolp acc-body)
                    (consp acc-body)))
        (er hard? 'parse-flexprod-field
            "Malformed field: ~x0: :acc-body should be a term." x))
       (acc-name (getarg-nonnil!
                  :acc-name
                  (intern-in-package-of-symbol
                   (cat (symbol-name type-name) "->" (symbol-name name))
                   type-name)
                  kwd-alist))
       ((mv type fix equiv recp) (get-pred/fix/equiv kwd-alist our-fixtypes fixtypes :type))
       (reqfix (getarg :reqfix name kwd-alist)))
    (make-flexprod-field
     :name name
     :acc-body acc-body
     :acc-name acc-name
     :type type
     :fix fix
     :equiv equiv
     :default (getarg :default nil kwd-alist)
     :doc (getarg :doc "" kwd-alist)
     ;; :require require
     :reqfix reqfix
     :rule-classes (let ((look (assoc :rule-classes kwd-alist)))
                     (and look `(:rule-classes ,(cdr look))))
     :recp recp)))

(defun parse-flexprod-fields (x type-name our-fixtypes fixtypes)
  (if (atom x)
      nil
    (cons (parse-flexprod-field (car x) type-name our-fixtypes fixtypes)
          (parse-flexprod-fields (cdr x) type-name our-fixtypes fixtypes))))

;; --- Flexprods ---
(def-primitive-aggregate flexprod
  (kind       ;; kind symbol
   cond       ;; term to check whether x is of this kind, after checking previous ones
   guard      ;; additional guard for accessors
   shape      ;; other requirements, given kindcheck
   require    ;; dependent type requirement (term)
   fields     ;; flexprod-field list
   type-name   ;; base for constructing default accessor names
   ctor-name  ;; constructor function name
   ctor-macro ;; constructor macro (keyword args) name
   ctor-body  ;; constructor body, without fixing
   short      ;; xdoc
   long       ;; xdoc
   inline     ;; inline keywords
   ))

(defconst *flexprod-keywords*
  '(:shape :fields :ctor-body :ctor-name :ctor-macro :cond :type-name :short :long :inline :require))

(defun parse-flexprod (x sumname sumkind sum-kwds xvar rev-not-prevconds our-fixtypes fixtypes)
  (b* (((cons kind kws) x)
       ((unless (keywordp kind))
        (er hard? 'parse-flexprod
            "Malformed flexprod: ~x0: kind (~x1) should be a keyword" x kind))
       ((mv kwd-alist rest)
        (extract-keywords 'parse-flexprod *flexprod-keywords* kws nil))
       ((when rest)
        (er hard? 'parse-flexprod-field
            "Malformed flexprod: ~x0: after kind should be a keyword/value list." x))
       (ctor-body-lookup (assoc :ctor-body kwd-alist))
       ((unless ctor-body-lookup)
        (er hard? 'parse-flexprod-field
            "Malformed product: ~x0: :ctor-body should be a term." x))
       (ctor-body (cdr ctor-body-lookup))
       (cond (getarg :cond t kwd-alist))
       (shape (getarg :shape t kwd-alist))
       (type-name (getarg-nonnil! :type-name
                                  (intern-in-package-of-symbol
                                   (cat (symbol-name sumname) "-" (symbol-name kind))
                                   sumname)
                                  kwd-alist))
       (ctor-name (getarg-nonnil! :ctor-name type-name kwd-alist) )
       (ctor-macro (getarg-nonnil! :ctor-macro
                                   (intern-in-package-of-symbol
                                    (cat "MAKE-" (symbol-name ctor-name))
                                    ctor-name)
                                   kwd-alist))
       (fields (parse-flexprod-fields (getarg :fields nil kwd-alist) type-name our-fixtypes fixtypes))
       (guard (if sumkind
                  `(equal (,sumkind ,xvar) ,kind)
                (let* ((fullcond-terms (dumb-append-conjunct rev-not-prevconds cond)))
                  (cond ((atom fullcond-terms) t)
                        ((atom (cdr fullcond-terms)) (car fullcond-terms))
                        (t `(and . ,fullcond-terms))))))
       (inline (get-deftypes-inline-opt (getarg :inline *inline-defaults* sum-kwds) kwd-alist))
       (require (getarg :require t kwd-alist)))
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
                  :short (getarg :short nil kwd-alist)
                  :long (getarg :long nil kwd-alist)
                  :inline inline)))

(defun parse-flexprods (x sumname sumkind sum-kwds xvar rev-not-prevconds our-fixtypes fixtypes)
  (if (atom x)
      nil
    (let* ((newprod (parse-flexprod (car x) sumname sumkind sum-kwds xvar rev-not-prevconds our-fixtypes fixtypes))
           (rev-not-prevconds (dumb-cons-conjunct
                               (acl2::dumb-negate-lit
                                (flexprod->cond newprod))
                               rev-not-prevconds)))
    (cons newprod
          (parse-flexprods (cdr x) sumname sumkind sum-kwds xvar rev-not-prevconds our-fixtypes fixtypes)))))

;; --- Flexsum ---
(def-primitive-aggregate flexsum
  (name        ;; name of this type
   pred        ;; predicate function name
   fix         ;; fix function name
   equiv       ;; equiv function name
   kind        ;; kind function name
   kind-body   ;; :exec part of kind function
   count       ;; count function name
   case        ;; case macro name
   prods       ;; flexprod structures
   measure     ;; measure for termination
   shape       ;; shape for all prods
   xvar        ;; variable name denoting the object
   kwd-alist   ;; original keyword arguments
   orig-prods  ;; original products
   inline      ;; inline kind, fix functions
   recp        ;; has a recusive field in some product
   typemacro   ;; defflexsum, deftagsum, defprod
   )
  :tag :sum)

(defconst *flexsum-keywords*
  '(:pred :fix :equiv :kind :count ;; function names
    :case ;; macro name
    :measure ;; term
    :xvar  ;; var name
    :no-count
    :shape
    :kind-body ;; :exec part of kind function
    :parents :short :long  ;; xdoc
    ;; :fixprep
    :prepwork
    :post-pred-events
    :post-fix-events
    :post-events
    :inline
    ))

(defun find-symbols-named-x (tree)
  (if (atom tree)
      (and (symbolp tree)
           (equal (symbol-name tree) "X")
           (list tree))
    (union-eq (find-symbols-named-x (car tree))
              (find-symbols-named-x (cdr tree)))))

(defun flexsum-infer-xvar (kwd-alist xvar prods)
  (b* ((xvar (getarg-nonnil! :xvar xvar kwd-alist))
       ((when xvar) xvar)
       (xsyms (find-symbols-named-x prods))
       ((when (atom xsyms))
        (er hard? 'flexsum-infer-xvar
            "No variable named X occurs in the defflexsum form.  Specify ~
             another variable with :xvar."))
       ((when (consp (cdr xsyms)))
        (er hard? 'flexsum-infer-xvar
            "More than one symbol named X occurs in the deftypes form.  Specify ~
             the variable denoting the typed object with :xvar.")))
    (car xsyms)))

(defun flexprod-fields-recursivep (x)
  (if (atom x)
      nil
    (or (flexprod-field->recp (car x))
        (flexprod-fields-recursivep (cdr x)))))

(defun flexprods-recursivep (x)
  (if (atom x)
      nil
    (or (flexprod-fields-recursivep (flexprod->fields (car x)))
        (flexprods-recursivep (cdr x)))))

(defun parse-flexsum (x xvar our-fixtypes fixtypes)
  (b* (((cons name args) x)
       ((unless (symbolp name))
        (er hard? 'parse-flexsum
            "Malformed flexsum: ~x0: name must be a symbol" x))
       ((mv pre-/// post-///) (std::split-/// 'parse-flexsum args))
       ((mv kwd-alist orig-prods)
        (extract-keywords 'parse-flexsum *flexsum-keywords* pre-/// nil))
       (pred (or (getarg :pred nil kwd-alist)
                 (intern-in-package-of-symbol (cat (symbol-name name) "-P")
                                              name)))
       (fix (or (getarg :fix nil kwd-alist)
                (intern-in-package-of-symbol (cat (symbol-name name) "-FIX")
                                             name)))
       (equiv (or (getarg :equiv nil kwd-alist)
                  (intern-in-package-of-symbol (cat (symbol-name name) "-EQUIV")
                                               name)))
       (kind (getarg! :kind
                      (intern-in-package-of-symbol (cat (symbol-name name) "-KIND")
                                                   name)
                      kwd-alist))
       (case (getarg! :case
                      (intern-in-package-of-symbol (cat (symbol-name name) "-CASE")
                                                   name)
                      kwd-alist))
       (inline (get-deftypes-inline-opt *inline-defaults* kwd-alist))
       (shape (getarg :shape t kwd-alist))
       (count (flextype-get-count-fn name kwd-alist))
       (xvar (flexsum-infer-xvar kwd-alist xvar orig-prods))
       (prods (parse-flexprods orig-prods name kind kwd-alist xvar nil our-fixtypes fixtypes))
       ((when (atom prods))
        (er hard? 'parse-flexsum
            "Malformed SUM ~x0: Must have at least one product"))
       (measure (or (getarg :measure nil kwd-alist)
                    `(acl2-count ,xvar)))
       (recp (flexprods-recursivep prods)))
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


;; ------------------------- Defprod/tagsum Parsing -----------------------

;; --- Extended formals parsing for defprod/tagsum ---
;; NOTE: We're reusing the std::formal data structure and some of the
;; associated parsing code, but some things are a bit different: mainly, the
;; guard field gets the function predicate symbol, not the whole term.

;; This is used for both tagsum and defprod.  In tagsum, xvar is actually `(cdr
;; ,xvar) because this doesn't involve the tag.
(defun tagprod-parse-formal-item
  ;; parses guard/doc item inside an extended formal
  ;;   (doesn't deal with keyword/value opts)
  (ctx      ; context for error messages
   varname  ; name of this formal
   item     ; the actual thing we're parsing
   guards   ; accumulator for guards (for this formal only)
   docs     ; accumulator for docs (for this formal only)
   )
  "Returns (mv guards docs)"
  (declare (xargs :guard (legal-variablep varname)))
  (b* ((__function__ 'tagprod-parse-formal-item)
       ((when (eq item t))
        (mv guards docs))
       ((when (eq item nil))
        (raise "~x0, formal ~x1: don't know what to do with an element with a guard of NIL"
               ctx varname)
        (mv guards docs))
       ((when (symbolp item))
        (mv (cons item guards) docs))
       ((when (and (consp item)
                   (not (eq (car item) 'quote))))
        (if (and (consp (cdr item))
                 (not (cddr item))
                 (eq (cadr item) varname))
            (mv (cons (car item) guards) docs)
          (prog2$ (raise "~x0, formal ~x1: can't handle a complicated guard like ~x2"
                         ctx varname item)
                  (mv guards docs))))
       ((when (stringp item))
        (mv guards (cons item docs))))
    (raise "~x0: formal ~x1: expected guard specifiers or documentation ~
            strings, but found ~x2."
           ctx varname item)
    (mv guards docs)))

(defun tagprod-parse-formal-items (ctx varname items guards docs)
  "Returns (mv guards docs)"
  (declare (xargs :guard (legal-variablep varname)))
  (b* ((__function__ 'tagprod-parse-formal-items)
       ((when (not items))
        (mv guards docs))
       ((when (atom items))
        (raise "~x0: formal ~x1: extended formal items should be ~
                nil-terminated; found ~x2 as the final cdr."
               ctx varname items)
        (mv guards docs))
       ((mv guards docs)
        (tagprod-parse-formal-item ctx varname (car items) guards docs)))
    (tagprod-parse-formal-items ctx varname (cdr items) guards docs)))

(defun tagprod-parse-formal
  (ctx        ; context for error messages
   formal     ; thing the user wrote for this formal
   legal-kwds ; what keywords are allowed in the item list
   )
  "Returns a formal-p"
  (declare (xargs :guard t))
  (b* ((__function__ 'parse-formal)
       ((when (atom formal))
        (b* ((varname (std::parse-formal-name ctx formal)))
          (std::make-formal :name varname
                            :guard nil
                            :doc ""
                            :opts nil)))
       (varname (std::parse-formal-name ctx (car formal)))
       (items   (cdr formal))
       ((mv opts items)  (extract-keywords (cons ctx varname) legal-kwds items nil))
       ((mv guards docs) (tagprod-parse-formal-items ctx varname items nil nil))
       (guard (cond ((atom guards) nil)
                    ((atom (cdr guards))
                     (if (eq (car guards) t) nil (car guards)))
                    (t (raise "~x0: formal ~x1: expected a single guard term, ~
                               but found ~&2." ctx varname guards))))
       (doc   (cond ((atom docs) "")
                    ((atom (cdr docs)) (car docs))
                    (t (progn$
                        (raise "~x0: formal ~x1: expected a single xdoc ~
                                string, but found ~&2." ctx varname docs)
                        "")))))
    (std::make-formal :name varname
                      :guard guard
                      :doc doc
                      :opts opts)))

(defun tagprod-parse-formals (ctx formals legal-kwds)
  ;; Assumes lambda-list keywords have already been removed from formals.
  (declare (xargs :guard t))
  (b* ((__function__ 'parse-formals)
       ((when (not formals))
        nil)
       ((when (atom formals))
        (raise "~x0: expected formals to be nil-terminated, but found ~x1 as ~
                the final cdr." ctx formals)))
    (cons (tagprod-parse-formal ctx (car formals) legal-kwds)
          (tagprod-parse-formals ctx (cdr formals) legal-kwds))))

;; --- Extended formals processing for defprod/tagsum ---
(defun tagsum-acc-for-tree (pos num expr)
  (if (zp num)
      (er hard? 'tagsum-acc-for-tree "bad programmer")
    (if (eql num 1)
        expr
      (let ((half (floor num 2)))
        (if (< pos half)
            (tagsum-acc-for-tree pos half `(car ,expr))
          (tagsum-acc-for-tree (- pos half) (- num half) `(cdr ,expr)))))))

(defun tagsum-formal-to-flexsum-field (x pos num xvar layout)
  ;; num is the total number of fields, pos is x's position
  (b* (((std::formal x) x)
       (accessor (case layout
                   (:alist `(cdr (std::da-nth ,pos ,xvar)))
                   (:tree (tagsum-acc-for-tree pos num xvar))
                   (:list `(std::da-nth ,pos ,xvar)))))
    `(,x.name :acc-body ,accessor :doc ,x.doc :type ,x.guard
              :default ,(cdr (assoc :default x.opts))
              ,@(let ((look (assoc :rule-classes x.opts)))
                  (and look `(:rule-classes ,(cdr look))))
              ,@(let ((look (assoc :reqfix x.opts)))
                  (and look `(:reqfix ,(cdr look)))))))

(defun tagsum-formals-to-flexsum-fields (x pos num xvar layout)
  (if (atom x)
      nil
    (cons (tagsum-formal-to-flexsum-field (car x) pos num xvar layout)
          (tagsum-formals-to-flexsum-fields (cdr x) (1+ pos) num xvar layout))))


;; --- Constructor ---
;; the cons argument to the following functions is either CONS or HONS.
(defun tagsum-alist-ctor-elts (fieldnames cons)
  (if (atom fieldnames)
      nil
    (cons `(,cons ',(car fieldnames) ,(car fieldnames))
          (tagsum-alist-ctor-elts (cdr fieldnames) cons))))

(defun tagsum-tree-ctor (fieldnames len cons)
  (if (zp len)
      (er hard? 'tagsum-tree-ctor "bad programmer")
    (if (eql len 1)
        (car fieldnames)
      (let ((half (floor len 2)))
        `(,cons ,(tagsum-tree-ctor (take half fieldnames) half cons)
                ,(tagsum-tree-ctor (nthcdr half fieldnames) (- len half) cons))))))

(defun tagsum-fields-to-ctor-body (fieldnames layout honsp)
  (b* ((cons (if honsp 'hons 'cons))
       (list (if honsp 'acl2::hons-list 'list)))
    (case layout
      (:alist `(,list . ,(tagsum-alist-ctor-elts fieldnames cons)))
      (:tree (tagsum-tree-ctor fieldnames (len fieldnames) cons))
      (:list `(,list . ,fieldnames)))))

;; --- Shape ---
(defun tagsum-tree-shape (len expr)
  (if (zp len)
      (er hard? 'tagsum-tree-shape "bad programmer")
    (if (eql len 1)
        nil
      (let ((half (floor len 2)))
        (cons `(consp ,expr)
              (append (tagsum-tree-shape half `(car ,expr))
                      (tagsum-tree-shape (- len half) `(cdr ,expr))))))))

;; This is used for both tagsum and defprod.  In tagsum, xvar is actually `(cdr
;; ,xvar) because this doesn't involve the tag.
(defun tagsum-fields-to-shape (fields xvar layout)
  (case layout
    (:alist `(and (alistp ,xvar)
                  (equal (strip-cars ,xvar) ',(strip-cars fields))))
    (:list `(and (true-listp ,xvar)
                 (eql (len ,xvar) ,(len fields))))
    (:tree `(and . ,(tagsum-tree-shape (len fields) xvar)))))

;; --- Tagsum parsing ---
(defun tagsum-prod-check-base-case (formals our-fixtypes)
  (if (atom formals)
      t
    (and (not (find-fixtype (std::formal->guard (car formals)) our-fixtypes))
         (tagsum-prod-check-base-case (cdr formals) our-fixtypes))))

(defconst *tagprod-formal-keywords* '(:rule-classes :default :reqfix))
(defconst *tagprod-keywords*
  '(:layout :hons :inline :base-name :require :short :long))

(defun tagsum-prod-to-flexprod (x xvar sum-kwds lastp have-basep our-fixtypes)
  (b* (((cons kind args) x)
       ((mv kwd-alist fields)
        (extract-keywords 'tagsum-prod *tagprod-keywords* args nil))
       ((when (not (eql (len fields) 1)))
        (er hard? 'parse-tagsum "Should have exactly one set of field specifiers: ~x0~%" fields)
        (mv nil nil))
       (layout (getarg :layout (getarg :layout :list sum-kwds) kwd-alist))
       (inlinep (assoc :inline kwd-alist))
       (requirep (assoc :require kwd-alist))
       (shortp (assoc :short kwd-alist))
       (longp (assoc :long kwd-alist))
       (hons (getarg :hons nil kwd-alist))
       (fields (car fields))
       (field-formals (tagprod-parse-formals 'parse-tagsum fields
                                             *tagprod-formal-keywords*))
       (basep (and (if have-basep
                       (eq have-basep kind)
                     (tagsum-prod-check-base-case field-formals our-fixtypes))
                   kind))
       (flexsum-fields (tagsum-formals-to-flexsum-fields
                        field-formals 0 (len field-formals) `(cdr ,xvar) layout))
       (base-name (getarg :base-name nil kwd-alist))
       (ctor-body1 (tagsum-fields-to-ctor-body (strip-cars flexsum-fields) layout hons))
       (shape1 (tagsum-fields-to-shape flexsum-fields `(cdr ,xvar) layout)))
    (mv `(,kind
          :cond ,(if lastp
                     t
                   (if basep
                       `(or (atom ,xvar)
                            (eq (car ,xvar) ,kind))
                     `(eq (car ,xvar) ,kind)))
          :shape ,(if lastp
                        `(and (eq (car ,xvar) ,kind) ,shape1)
                      shape1)
          :fields ,flexsum-fields
          ,@(and inlinep `(:inline ,(cdr inlinep)))
          ,@(and requirep `(:require ,(cdr requirep)))
          ,@(and base-name `(:type-name ,base-name))
          ,@(and shortp `(:short ,(cdr shortp)))
          ,@(and longp `(:long ,(cdr longp)))
          :ctor-body (,(if hons 'hons 'cons) ,kind ,ctor-body1))
        basep)))

(defun tagsum-prods-to-flexprods (prods xvar sum-kwds have-base-or-override our-fixtypes tagsum-name)
  (if (atom prods)
      (prog2$ (and (not have-base-or-override)
                   (er hard? 'tagsum-prods-to-flexprods
                       "We couldn't find a base case for tagsum ~x0, so we ~
                        don't know what its fixing function should return ~
                        when the input is an atom.  To override this, add ~
                        keyword arg :base-case-override [product], where ~
                        [product] is one of your product keywords, and provide ~
                        a measure that will allow the fixing function to ~
                        terminate."
                       tagsum-name))
              nil)
    (mv-let (first basep)
      (tagsum-prod-to-flexprod
       (car prods) xvar sum-kwds (atom (cdr prods)) have-base-or-override our-fixtypes)
      (cons first
            (tagsum-prods-to-flexprods
             (cdr prods) xvar sum-kwds (or have-base-or-override basep) our-fixtypes tagsum-name)))))

(defconst *tagsum-keywords*
  '(:pred :fix :equiv :kind :count ;; function names
    :measure ;; term
    :xvar  ;; var name
    :no-count
    :parents :short :long  ;; xdoc
    :inline
    :layout ;; :list, :tree, :alist
    :case
    :base-case-override
    :prepwork
    :post-pred-events
    :post-fix-events
    :post-events))

(defun parse-tagsum (x xvar these-fixtypes fixtypes)
  (b* (((cons name args) x)
       ((unless (symbolp name))
        (er hard? 'parse-tagsum
            "Malformed tagsum: ~x0: name must be a symbol" x))
       ((mv pre-/// post-///) (std::split-/// 'parse-tagsum args))
       ((mv kwd-alist orig-prods)
        (extract-keywords 'parse-tagsum *tagsum-keywords* pre-/// nil))
       (pred (or (getarg :pred nil kwd-alist)
                 (intern-in-package-of-symbol (cat (symbol-name name) "-P")
                  name)))
       (fix (or (getarg :fix nil kwd-alist)
                (intern-in-package-of-symbol (cat (symbol-name name) "-FIX")
                                             name)))
       (equiv (or (getarg :equiv nil kwd-alist)
                  (intern-in-package-of-symbol (cat (symbol-name name) "-EQUIV")
                                               name)))
       (kind (getarg! :kind
                      (intern-in-package-of-symbol (cat (symbol-name name) "-KIND")
                                                   name)
                      kwd-alist))
       (case (getarg! :case
                      (intern-in-package-of-symbol (cat (symbol-name name) "-CASE")
                                                   name)
                      kwd-alist))
       (inline (get-deftypes-inline-opt *inline-defaults* kwd-alist))
       (count (flextype-get-count-fn name kwd-alist))
       (xvar (or (getarg :xvar xvar kwd-alist)
                 (car (find-symbols-named-x (getarg :measure nil kwd-alist)))
                 (intern-in-package-of-symbol "X" name)))
       (layout (getarg :layout :alist kwd-alist))
       ((unless (member layout '(:tree :list :alist)))
        (er hard? 'parse-tagsum "Bad layout type ~x0~%" layout))
       (base-override (getarg :base-case-override nil kwd-alist))
       (flexprods-in (tagsum-prods-to-flexprods orig-prods xvar kwd-alist base-override these-fixtypes name))
       ((unless (or (not base-override)
                    (member base-override (strip-cars flexprods-in))))
        (er hard? 'parse-tagsum
            ":Base-case-override value must be one of the product names"))
       (prods (parse-flexprods flexprods-in name kind kwd-alist xvar nil these-fixtypes fixtypes))
       ((when (atom prods))
        (er hard? 'parse-tagsum
            "Malformed SUM ~x0: Must have at least one product"))
       (measure (or (getarg :measure nil kwd-alist)
                    `(acl2-count ,xvar))))
    (make-flexsum :name name
                  :pred pred
                  :fix fix
                  :equiv equiv
                  :kind kind
                  :case case
                  :kind-body `(car ,xvar)
                  :shape `(consp ,xvar)
                  :count count
                  :prods prods
                  :xvar xvar
                  :inline inline
                  :measure measure
                  :kwd-alist (if post-///
                                 (cons (cons :///-events post-///)
                                       kwd-alist)
                               kwd-alist)
                  :orig-prods orig-prods
                  :recp (flexprods-recursivep prods)
                  :typemacro 'deftagsum)))

;; --- Defprod parsing ---
(defconst *defprod-keywords*
  '(:pred :fix :equiv :count ;; function names
    :measure ;; term
    :xvar  ;; var name
    :no-count
    :parents :short :long  ;; xdoc
    :inline
    :require
    :layout ;; :list, :tree, :alist
    :tag
    :hons
    :prepwork
    :post-pred-events
    :post-fix-events
    :post-events
    ))

(defun defprod-fields-to-flexsum-prod (fields xvar name kwd-alist)
  (b* ((layout (getarg :layout :alist kwd-alist))
       ((unless (member layout '(:tree :list :alist)))
        (er hard? 'parse-defprod "Bad layout type ~x0~%" layout))
       (tag (getarg :tag nil kwd-alist))
       (hons (getarg :hons nil kwd-alist))
       (field-formals (tagprod-parse-formals 'parse-defprod fields *tagprod-formal-keywords*))
       (xbody (if tag `(cdr ,xvar) xvar))
       (flexsum-fields (tagsum-formals-to-flexsum-fields
                        field-formals 0 (len field-formals) xbody layout))
       (ctor-body1 (tagsum-fields-to-ctor-body (strip-cars flexsum-fields) layout hons))
       (ctor-body (if tag `(,(if hons 'hons 'cons) ,tag ,ctor-body1) ctor-body1))
       (shape (tagsum-fields-to-shape flexsum-fields xbody layout))
       (requirep (assoc :require kwd-alist))
       (kind (or tag (intern$ (symbol-name name) "KEYWORD"))))
    `(,kind
      :shape ,(if tag
                    (nice-and `(eq (car ,xvar) ,tag) shape)
                  shape)
      :fields ,flexsum-fields
      :type-name ,name
      :ctor-body ,ctor-body
      ,@(and requirep `(:require ,(cdr requirep))))))

(defun flexprod-fields->names (fields)
  (if (atom fields)
      nil
    (cons (flexprod-field->name (car fields))
          (flexprod-fields->names (cdr fields)))))

(defun defprod-tag-events (pred xvar tag name formals)
  (b* ((foop pred)
       (x xvar))
    `((defthmd ,(intern-in-package-of-symbol (cat "TAG-WHEN-" (symbol-name foop))
                                             name)
        (implies (,foop ,x)
                 (equal (tag ,x)
                        ,tag))
        :rule-classes ((:rewrite :backchain-limit-lst 0)
                       (:forward-chaining))
        :hints(("Goal" :in-theory (enable tag ,foop))))

      (defthmd ,(intern-in-package-of-symbol (cat (symbol-name foop) "-WHEN-WRONG-TAG")
                                             name)
        (implies (not (equal (tag ,x) ,tag))
                 (equal (,foop ,x)
                        nil))
        :rule-classes ((:rewrite :backchain-limit-lst 1))
        :hints(("Goal" :in-theory (enable tag ,foop))))

      (defthm ,(intern-in-package-of-symbol (cat "TAG-OF-" (symbol-name name))
                                            name)
        (equal (tag (,name . ,formals))
               ,tag)
        :hints (("goal" :in-theory (enable ,name tag))))

      (add-to-ruleset std::tag-reasoning
                      '(,(intern-in-package-of-symbol (cat "TAG-WHEN-" (symbol-name foop))
                                                      name)
                        ,(intern-in-package-of-symbol (cat (symbol-name foop) "-WHEN-WRONG-TAG")
                                                      name))))))

(defun parse-defprod (x xvar our-fixtypes fixtypes)
  (b* (((cons name args) x)
       ((unless (symbolp name))
        (er hard? 'parse-defprod
            "Malformed defprod: ~x0: name must be a symbol" x))
       ((mv pre-/// post-///) (std::split-/// 'parse-defprod args))
       ((mv kwd-alist fields)
        (extract-keywords 'parse-defprod *defprod-keywords* pre-/// nil))
       ((when (atom fields))
        (er hard? 'parse-defprod "List of fields is missing~%"))
       ((when (consp (cdr fields)))
        (er hard? 'parse-defprod "More than one list of fields present~%"))
       (fields (car fields))
       (pred (or (getarg :pred nil kwd-alist)
                 (intern-in-package-of-symbol (cat (symbol-name name) "-P")
                                              name)))
       (fix (or (getarg :fix nil kwd-alist)
                (intern-in-package-of-symbol (cat (symbol-name name) "-FIX")
                                             name)))
       (equiv (or (getarg :equiv nil kwd-alist)
                  (intern-in-package-of-symbol (cat (symbol-name name) "-EQUIV")
                                               name)))
       (inline (get-deftypes-inline-opt *inline-defaults* kwd-alist))
       (count (flextype-get-count-fn name kwd-alist))
       (xvar (or (getarg :xvar xvar kwd-alist)
                 (car (find-symbols-named-x (getarg :measure nil kwd-alist)))
                 (intern-in-package-of-symbol "X" name)))

       (tag (getarg :tag nil kwd-alist))
       ((unless (or (not tag) (keywordp tag)))
        (er hard? 'parse-defprod ":Tag, if provided, must be a keyword symbol"))
       (orig-prod (defprod-fields-to-flexsum-prod fields xvar name kwd-alist))
       (orig-prods (list orig-prod))
       (prods (parse-flexprods orig-prods name nil kwd-alist xvar nil our-fixtypes fixtypes))

       (measure (or (getarg :measure nil kwd-alist)
                    `(acl2-count ,xvar)))
       (field-names (flexprod-fields->names (flexprod->fields (car prods))))
       (post-events (if tag 
                        (append (defprod-tag-events pred xvar tag name field-names)
                                (cdr (assoc :post-events kwd-alist)))
                      (cdr (assoc :post-events kwd-alist)))))
    (make-flexsum :name name
                  :pred pred
                  :fix fix
                  :equiv equiv
                  :kind nil
                  :shape (if tag `(consp ,xvar) t)
                  :count count
                  :prods prods
                  :xvar xvar
                  :measure measure
                  :kwd-alist (list* (cons :///-events post-///)
                                    (cons :post-events post-events)
                                    kwd-alist)
                  :orig-prods orig-prods
                  :inline inline
                  :recp (flexprods-recursivep prods)
                  :typemacro 'defprod)))

;; ------------------------- Deflist Parsing -----------------------
(def-primitive-aggregate flexlist
  (name       ;; name of the type
   pred       ;; preducate function name
   fix        ;; fix function name
   equiv      ;; equiv function name
   count      ;; count function name
   elt-type   ;; element type name
   elt-fix    ;; element fixing function
   elt-equiv  ;; element equiv function
   measure    ;; termination measure
   xvar       ;; variable name denoting the object
   kwd-alist  ;; original keyword alist
   true-listp ;; require nil final cdr
   elementp-of-nil
   cheap            ;; passed to std::deflist
   recp       ;; elt-type is recursive
   )
  :tag :list)

(defconst *flexlist-keywords*
  '(:pred :fix :equiv :count
    :elt-type
    :measure
    :xvar
    :true-listp
    :elementp-of-nil
    :cheap
    :parents :short :long  ;; xdoc
    :no-count
    :prepwork
    :post-pred-events
    :post-fix-events
    :post-events))

(defun parse-flexlist (x xvar our-fixtypes fixtypes)
  (b* (((cons name args) x)
       ((unless (symbolp name))
        (er hard? 'parse-flexlist
            "Malformed flexlist: ~x0: name must be a symbol" x))
       ((mv pre-/// post-///) (std::split-/// 'parse-flexlist args))
       ((mv kwd-alist rest)
        (extract-keywords 'parse-flexlist *flexlist-keywords* pre-/// nil))
       ((when rest)
        (er hard? 'parse-flexlist
            "Malformed flexlist: ~x0: after kind should be a keyword/value list." x))
       (elt-type (getarg :elt-type nil kwd-alist))
       ((unless (and (symbolp elt-type) elt-type))
        (er hard? 'parse-flexlist
            "Bad flexlist ~x0: Element type must be a symbol" x))
       ((mv elt-type elt-fix elt-equiv recp)
        (get-pred/fix/equiv kwd-alist our-fixtypes fixtypes :elt-type))
       (pred (or (getarg :pred nil kwd-alist)
                 (intern-in-package-of-symbol (cat (symbol-name name) "-P")
                                              name)))
       (fix (or (getarg :fix nil kwd-alist)
                (intern-in-package-of-symbol (cat (symbol-name name) "-FIX")
                                             name)))
       (equiv (or (getarg :equiv nil kwd-alist)
                  (intern-in-package-of-symbol (cat (symbol-name name) "-EQUIV")
                                               name)))
       (elementp-of-nil (getarg :elementp-of-nil :unknown kwd-alist))
       (cheap           (getarg :cheap           nil kwd-alist))
       (count (flextype-get-count-fn name kwd-alist))
       (xvar (or (getarg :xvar nil kwd-alist)
                 xvar
                 (car (find-symbols-named-x (getarg :measure nil kwd-alist)))
                 (intern-in-package-of-symbol "X" name)))
       (measure (or (getarg :measure nil kwd-alist)
                    `(acl2-count ,xvar)))
       (true-listp (getarg :true-listp nil kwd-alist)))
    (make-flexlist :name name
                  :pred pred
                  :fix fix
                  :equiv equiv
                  :count count
                  :elt-type elt-type
                  :elt-fix elt-fix
                  :elt-equiv elt-equiv
                  :true-listp true-listp
                  :elementp-of-nil elementp-of-nil
                  :cheap cheap
                  :measure measure
                  :kwd-alist (if post-///
                                 (cons (cons :///-events post-///)
                                       kwd-alist)
                               kwd-alist)
                  :xvar xvar
                  :recp recp)))

;; ------------------------- Defalist Parsing -----------------------
(def-primitive-aggregate flexalist
  (name       ;; name of the type
   pred       ;; predicate function name
   fix        ;; fix function name
   equiv      ;; equiv function name
   count      ;; count function name
   key-type   ;; key type name
   key-fix    ;; key fixing function
   key-equiv  ;; key equiv function
   val-type   ;; value type name
   val-fix    ;; value fixing function
   val-equiv  ;; value equiv function
   measure    ;; termination measure
   xvar       ;; variable name denoting the object
   kwd-alist  ;; original keyword alist
   ;; get get-fast ;; more fn names
   ;; set set-fast
   true-listp
   recp
   )
  :tag :alist)

(defconst *flexalist-keywords*
  '(:pred :fix :equiv :count
    :get :get-fast
    :set :set-fast
    :key-type :val-type
    :measure
    :xvar
    :parents :short :long  ;; xdoc
    :no-count :true-listp
    :prepwork
    :post-pred-events
    :post-fix-events
    :post-events))

(defun parse-flexalist (x xvar our-fixtypes fixtypes)
  (b* (((cons name args) x)
       ((unless (symbolp name))
        (er hard? 'parse-flexalist
            "Malformed flexalist: ~x0: name must be a symbol" x))
       ((mv pre-/// post-///) (std::split-/// 'parse-flexalist args))
       ((mv kwd-alist rest)
        (extract-keywords 'parse-flexalist *flexalist-keywords* pre-/// nil))
       ((when rest)
        (er hard? 'parse-flexalist
            "Malformed flexalist: ~x0: after kind should be a keyword/value list." x))
       (key-type (getarg :key-type nil kwd-alist))
       ((unless (symbolp key-type))
        (er hard? 'parse-flexalist
            "Bad flexalist ~x0: Element type must be a symbol" x))
       ((mv key-type key-fix key-equiv key-recp)
        (get-pred/fix/equiv kwd-alist our-fixtypes fixtypes :key-type))
       (val-type (getarg :val-type nil kwd-alist))
       ((unless (symbolp val-type))
        (er hard? 'parse-flexalist
            "Bad flexalist ~x0: Element type must be a symbol" x))
       ((mv val-type val-fix val-equiv val-recp)
        (get-pred/fix/equiv kwd-alist our-fixtypes fixtypes :val-type))
       (pred (or (getarg :pred nil kwd-alist)
                 (intern-in-package-of-symbol (cat (symbol-name name) "-P")
                                              name)))
       (fix (or (getarg :fix nil kwd-alist)
                (intern-in-package-of-symbol (cat (symbol-name name) "-FIX")
                                             name)))
       (equiv (or (getarg :equiv nil kwd-alist)
                  (intern-in-package-of-symbol (cat (symbol-name name) "-EQUIV")
                                               name)))
       (count (flextype-get-count-fn name kwd-alist))
       (xvar (or (getarg :xvar nil kwd-alist)
                 xvar
                 (car (find-symbols-named-x (getarg :measure nil kwd-alist)))
                 (intern-in-package-of-symbol "X" name)))
       (measure (or (getarg :measure nil kwd-alist)
                    `(acl2-count ,xvar)))
       (true-listp (getarg :true-listp nil kwd-alist)))
    (make-flexalist :name name
                    :pred pred
                    :fix fix
                    :equiv equiv
                    :count count
                    :key-type key-type
                    :key-fix key-fix
                    :key-equiv key-equiv
                    :val-type val-type
                    :val-fix val-fix
                    :val-equiv val-equiv
                    :measure measure
                    :kwd-alist (if post-///
                                   (cons (cons :///-events post-///)
                                         kwd-alist)
                                 kwd-alist)
                    :xvar xvar
                    :true-listp true-listp
                    :recp (or key-recp val-recp))))

;; --- With-flextype-bindings ---
(defun replace-*-in-symbol-with-str (x str)
  (b* ((name (symbol-name x))
       (idx (search "*" name))
       ((unless idx) x)
       (newname (cat (subseq name 0 idx) str (subseq name (+ 1 idx) nil))))
    (intern-in-package-of-symbol newname x)))

(defun replace-*-in-symbols-with-str-rec (x str)
  (b* (((when (atom x))
        (if (symbolp x)
            (let* ((newx (replace-*-in-symbol-with-str x str)))
              (if (eq newx x)
                  (mv nil x)
                (mv t newx)))
          (mv nil x)))
       ((mv changed1 car) (replace-*-in-symbols-with-str-rec (car x) str))
       ((mv changed2 cdr) (replace-*-in-symbols-with-str-rec (cdr x) str))
       ((unless (or changed1 changed2))
        (mv nil x)))
    (mv t (cons car cdr))))

(defun has-vardot-syms (x vardot)
  (if (atom x)
      (and (symbolp x)
           (eql (search vardot (symbol-name x)) 0))
    (or (has-vardot-syms (car x) vardot)
        (has-vardot-syms (cdr x) vardot))))

(defun replace-*-in-symbols-with-str (x str)
  (b* (((mv ?ch newx) (replace-*-in-symbols-with-str-rec x str)))
    newx))

(defun with-flextype-bindings-fn (binding body)
  (b* ((var (if (consp binding) (car binding) binding))
       (add-binds (has-vardot-syms body (cat (symbol-name var) ".")))
       (sumbody (replace-*-in-symbols-with-str body "SUM"))
       (listbody (replace-*-in-symbols-with-str body "LIST"))
       (alistbody (replace-*-in-symbols-with-str body "ALIST"))
       (cases
        `(case (tag ,var)
           (:sum ,(if add-binds `(b* (((flexsum ,var) ,var)) ,sumbody) sumbody))
           (:list ,(if add-binds `(b* (((flexlist ,var) ,var)) ,listbody) listbody))
           (:alist ,(if add-binds `(b* (((flexalist ,var) ,var)) ,alistbody) alistbody)))))
    (if (consp binding)
        `(let ((,var ,(cadr binding))) ,cases)
      cases)))

(defmacro with-flextype-bindings (binding body)
  (with-flextype-bindings-fn binding body))


;; ------------------------- Deftypes Parsing -----------------------
(defconst *known-flextype-generators* '(defflexsum deflist deftagsum defprod defalist))

(defun parse-flextypelist (x xvar our-fixtypes fixtypes)
  (if (atom x)
      nil
    (cons (case (caar x)
            (defflexsum (parse-flexsum (cdar x) xvar our-fixtypes fixtypes))
            (defprod   (parse-defprod (cdar x) xvar our-fixtypes fixtypes))
            (deftagsum (parse-tagsum (cdar x) xvar our-fixtypes fixtypes))
            (deflist (parse-flexlist (cdar x) xvar our-fixtypes fixtypes))
            (defalist (parse-flexalist (cdar x) xvar our-fixtypes fixtypes))
            (otherwise (er hard? 'parse-flextypelist
                           "Recognized flextypes are ~x0, not ~x1~%"
                           *known-flextype-generators* (caar x))))
          (parse-flextypelist (cdr x) xvar our-fixtypes fixtypes))))

(defun flextype-form->fixtype (x)
  ;; This takes a whole deflist/defflexsum/?? form, gets the
  ;; type/pred/fix/equiv, and bundles it into a fixtype structure.
  (b* (((list* & name args) x)
       (fix (or (cadr (member :fix args))
                (intern-in-package-of-symbol (cat (symbol-name name) "-FIX")
                                             name)))
       (pred (or (cadr (member :pred args))
                 (intern-in-package-of-symbol (cat (symbol-name name) "-P")
                                              name)))
       (equiv (or (cadr (member :equiv args))
                  (intern-in-package-of-symbol (cat (symbol-name name) "-EQUIV")
                                               name))))
    (cons name
          (make-fixtype :name name
                        :pred pred
                        :fix fix
                        :equiv equiv
                        :executablep t
                        :equiv-means-fixes-equal equiv))))

;; The fields may reference fixtypes that we're introducing, so we need to
;; collect the fixtypes before we properly parse all the types.
(defun collect-flextypelist-fixtypes (x)
  (if (atom x)
      nil
    (cons (flextype-form->fixtype (car x))
          (collect-flextypelist-fixtypes (cdr X)))))

(def-primitive-aggregate flextypes
  (name
   types      ;; flexlist and flexsums
   no-count   ;; skip the count function
   kwd-alist
   ;; prepwork
   ;; post-pred-events
   ;; post-fix-events
   ;; post-events
   recp))

(defconst *flextypes-keywords*
  '(:xvar :no-count
    :parents :short :long ;; xdoc
    :prepwork
    :post-pred-events
    :post-fix-events
    :post-events
    ))

(defun flextypelist-recp (x)
  (if (atom x)
      nil
    (or (with-flextype-bindings (x (car x)) x.recp)
        (flextypelist-recp (cdr x)))))

(defun parse-flextypes (x wrld)
  (b* (((cons name x) x)
       ((unless (symbolp name))
        (er hard? 'parse-flextypes
            "Malformed flextypes: name must be a symbol, but found ~x0" name))
       ((mv pre-/// post-///) (std::split-/// 'parse-flexsum x))
       ((mv kwd-alist typedecls)
        (extract-keywords 'parse-flextypes *flextypes-keywords* pre-/// nil))
       (our-fixtypes (collect-flextypelist-fixtypes typedecls))
       (fixtype-al (append our-fixtypes
                           (get-fixtypes-alist wrld)))
       (xvar (getarg :xvar nil kwd-alist))
       (no-count (getarg :no-count nil kwd-alist))
       (types (parse-flextypelist typedecls xvar our-fixtypes fixtype-al)))
    (make-flextypes :name name
                    :types types
                    :no-count no-count
                    :kwd-alist (if post-///
                                   (cons (cons :///-events post-///)
                                         kwd-alist)
                                 kwd-alist)
                    :recp (flextypelist-recp types))))

;; ------------------ Predicate: flexsum -----------------------

;; ((fn (car x))
;;  (args (cdr x)))
(defun flexprod-fields-pred-bindings (fields)
  (b* (((when (atom fields)) nil)
       ((flexprod-field x) (car fields))
       ((unless x.type)
        (cons (list (intern-in-package-of-symbol (cat "?" (symbol-name x.name))
                                                 x.name) x.acc-body)
              (flexprod-fields-pred-bindings (cdr fields)))))
    (cons (list x.name x.acc-body)
          (flexprod-fields-pred-bindings (cdr fields)))))

;; ((pfunc-p fn)
;;  (ptermlist-p args))
(defun flexprod-fields-typechecks (fields last)
  (b* (((when (atom fields)) last)
       ((flexprod-field x) (car fields))
       ((unless x.type)
        (flexprod-fields-typechecks (cdr fields) last)))
    (nice-and (list x.type x.name)
              (flexprod-fields-typechecks (cdr fields) last))))

;;        (let* ((fn (car x))
;;               (args (cdr x)))
;;          (and (pfunc-p fn)
;;               (ptermlist-p args))))
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
       (bool  (intern-in-package-of-symbol "BOOL" sum.name)))
    `(define ,sum.pred (,sum.xvar)
       :parents (,sum.name)
       :short ,short
       :returns ,bool
       :measure ,sum.measure
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
                 (defthm ,(intern-in-package-of-symbol (cat "CONSP-WHEN-" (symbol-name sum.pred))
                                                       sum.pred)
                   (implies (,sum.pred ,sum.xvar)
                            (consp ,sum.xvar))
                   :hints (("goal" :expand ((,sum.pred ,sum.xvar)))
                           (and stable-under-simplificationp
                                '(:error t)))
                   :rule-classes :compound-recognizer)))
          (value-triple :skip-compound-recognizer))))))

;; ------------------ Predicate: deflist -----------------------

(defun flexlist-predicate-def (list)
  (b* (((flexlist list) list)
       ;; std::deflist-compatible variable names
       (stdx (intern-in-package-of-symbol "X" list.pred))
       ;; (stda (intern-in-package-of-symbol "A" 'acl2::foo))
       )
    `(define ,list.pred (,list.xvar)
       ;; BOZO not exactly clear when/where to add docs for the predicate
       :parents nil
       :progn t
       :measure ,list.measure
       (if (atom ,list.xvar)
           ,(if list.true-listp
                `(eq ,list.xvar nil)
              t)
         (and (,list.elt-type (car ,list.xvar))
              (,list.pred (cdr ,list.xvar))))
       ///
       (local (in-theory (disable ,list.pred)))
       (std::deflist ,list.pred (,stdx)
         (,list.elt-type ,stdx)
         :already-definedp t
         ,@(and (not (eq list.elementp-of-nil :unknown))
                `(:elementp-of-nil ,list.elementp-of-nil))
         :true-listp ,list.true-listp
         :cheap ,list.cheap)
       ;; (defthm ,(intern-in-package-of-symbol (cat (symbol-name list.pred) "-OF-CONS")
       ;;                                       list.pred)
       ;;   ;; Use special symbols for std::deflist compatibility
       ;;   (equal (,list.pred (cons ,stda ,stdx))
       ;;          (and (,list.elt-type ,stda)
       ;;               (,list.pred ,stdx)))
       ;;   :hints (("Goal" :Expand ((,list.pred (cons ,stda ,stdx))))))

       ;; (defthm ,(intern-in-package-of-symbol (cat (symbol-name list.pred) "-OF-CDR")
       ;;                                       list.pred)
       ;;   (implies (,list.pred ,list.xvar)
       ;;            (,list.pred (cdr ,list.xvar)))
       ;;   :hints (("goal" :expand ((,list.pred ,list.xvar)))
       ;;           (and stable-under-simplificationp
       ;;                '(:expand ((,list.pred (cdr ,list.xvar)))))))

       ;; (defthm ,(intern-in-package-of-symbol
       ;;           (cat (symbol-name list.elt-type) "-CAR-OF-" (symbol-name list.pred))
       ;;           list.pred)
       ;;   (implies (and (consp ,stdx)
       ;;                 (,list.pred ,stdx))
       ;;            (,list.elt-type (car ,stdx)))
       ;;   :hints (("goal" :expand ((,list.pred ,stdx))))
       ;;   :rule-classes ((:rewrite :backchain-limit-lst (0 nil))))

       ;; ,@(and list.true-listp
       ;;        `((defthm ,(intern-in-package-of-symbol
       ;;                    (cat (symbol-name list.pred) "-COMPOUND-RECOGNIZER")
       ;;                    list.pred)
       ;;            (implies (,list.pred ,list.xvar)
       ;;                     (true-listp ,list.xvar))
       ;;            :hints (("goal" :expand ((,list.pred ,list.xvar))
       ;;                     :induct (true-listp ,list.xvar)
       ;;                     :in-theory (enable true-listp)))
       ;;            :rule-classes :compound-recognizer)))
       )))

;; ------------------ Predicate: defalist -----------------------

(defun flexalist-predicate-def (alist)
  (b* (((flexalist alist) alist)
       ;; std::deflist-compatible variable names
       (stdx (intern-in-package-of-symbol "X" alist.pred))
       (stda (intern-in-package-of-symbol "A" alist.pred)))
    `(define ,alist.pred (,alist.xvar)
       :parents nil ;; BOZO not clear when to add docs for this
       :progn t
       :measure ,alist.measure
       (if (atom ,alist.xvar)
           ,(if alist.true-listp
                `(eq ,alist.xvar nil)
              t)
         (and (consp (car ,alist.xvar))
              ,@(and alist.key-type
                     `((,alist.key-type (caar ,alist.xvar))))
              ,@(and alist.val-type
                     `((,alist.val-type (cdar ,alist.xvar))))
              (,alist.pred (cdr ,alist.xvar))))
       ///
       (local (in-theory (disable ,alist.pred)))
       (defthm ,(intern-in-package-of-symbol
                 (cat (symbol-name alist.pred) "-OF-CONS")
                 alist.pred)
         ;; Use special symbols for std::defalist compatibility
         (equal (,alist.pred (cons ,stda ,stdx))
                (and (consp ,stda)
                     ,@(and alist.key-type
                            `((,alist.key-type (car ,stda))))
                     ,@(and alist.val-type
                            `((,alist.val-type (cdr ,stda))))
                     (,alist.pred ,stdx)))
         :hints (("goal" :expand ((,alist.pred (cons ,stda ,stdx))))))

       (defthm ,(intern-in-package-of-symbol
                 (cat (symbol-name alist.pred) "-OF-CDR")
                 alist.pred)
         (implies (,alist.pred ,alist.xvar)
                  (,alist.pred (cdr ,alist.xvar)))
         :hints (("goal" :expand ((,alist.pred ,alist.xvar)))
                 (and stable-under-simplificationp
                      '(:expand ((,alist.pred (cdr ,alist.xvar)))))))

       ;; (defthm ,(intern-in-package-of-symbol
       ;;           (cat (symbol-name alist.pred)
       ;;                        "-WHEN-CONSP")
       ;;           alist.pred)
       ;;   ;; Use special symbols for std::defalist compatibility
       ;;   (implies (consp ,stdx)
       ;;            (equal (,alist.pred ,stdx)
       ;;                   (and (consp (car ,stdx))
       ;;                        ,@(and alist.key-type
       ;;                               `((,alist.key-type (car (car ,stdx)))))
       ;;                        ,@(and alist.val-type
       ;;                               `((,alist.val-type (cdr (car ,stdx)))))
       ;;                        (,alist.pred (cdr ,stdx)))))
       ;;   :rule-classes ((:rewrite :backchain-limit-lst 0)))

       ,@(and alist.key-type
              `((defthm ,(intern-in-package-of-symbol
                          (cat (symbol-name alist.key-type) "-CAAR-OF-" (symbol-name alist.pred))
                          alist.pred)
                  (implies (and (consp ,alist.xvar)
                                (,alist.pred ,alist.xvar))
                           (,alist.key-type (caar ,alist.xvar)))
                  :hints (("goal" :expand ((,alist.pred ,alist.xvar))))
                  :rule-classes ((:rewrite :backchain-limit-lst (0 nil))))))

       ,@(and alist.val-type
              `((defthm ,(intern-in-package-of-symbol
                          (cat (symbol-name alist.val-type) "-CDAR-OF-" (symbol-name alist.pred))
                          alist.pred)
                  (implies (and (consp ,alist.xvar)
                                (,alist.pred ,alist.xvar))
                           (,alist.val-type (cdar ,alist.xvar)))
                  :hints (("goal" :expand ((,alist.pred ,alist.xvar))))
                  :rule-classes ((:rewrite :backchain-limit-lst (0 nil))))))

       ,@(and alist.true-listp
              `((defthm ,(intern-in-package-of-symbol
                          (cat (symbol-name alist.pred) "-COMPOUND-RECOGNIZER")
                          alist.pred)
                  (implies (,alist.pred ,alist.xvar)
                           (true-listp ,alist.xvar))
                  :hints (("goal" :expand ((,alist.pred ,alist.xvar))
                           :induct (true-listp ,alist.xvar)
                           :in-theory (enable true-listp)))
                  :rule-classes :compound-recognizer))))))


;; ------------------ Predicates: deftypes -----------------------

(defun flextypelist-predicate-defs (types)
  (if (atom types)
      nil
    (cons (with-flextype-bindings (x (car types))
            (flex*-predicate-def x))
          (flextypelist-predicate-defs (cdr types)))))

(defun flextypelist-predicates (types)
  (if (atom types)
      nil
    (cons (with-flextype-bindings (x (car types)) x.pred)
          (flextypelist-predicates (cdr types)))))

(defun flextypes-predicate-def (x)
  (b* (((flextypes x) x)
       (defs (flextypelist-predicate-defs x.types)))
    (if (atom (cdr x.types))
        `(,(car defs)
          (local (in-theory (disable . ,(flextypelist-predicates x.types)))))
      `((defines ,(intern-in-package-of-symbol (cat (symbol-name x.name) "-P")
                                               x.name)
          :progn t
          ,@defs)
        (local (in-theory (disable . ,(flextypelist-predicates x.types))))))))



;; --------------- Kind function & case macro (sums) ----------

(defun flexprods->kinds (prods)
  (if (atom prods)
      nil
    (cons (flexprod->kind (car prods))
          (flexprods->kinds (cdr prods)))))

;; returns something like:
;;          (((not x) :null)
;;           ((atom x) :var)
;;           ((eq (car x) 'quote) :quote)
;;           (t :call)))
(defun flextype-sum-kind-conds (prods)
  (if (atom prods)
      nil
    (cons `(,(flexprod->cond (car prods)) ,(flexprod->kind (car prods)))
          (flextype-sum-kind-conds (cdr prods)))))

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
       (conds (flextype-sum-kind-conds sum.prods))
       (values (flexprods->kinds sum.prods))
       (possibilities (pairlis$ (make-list (len values) :initial-element 'equal)
                                (pairlis$ (make-list (len values) :initial-element `(,sum.kind ,sum.xvar))
                                          (pairlis$ values nil))))
       (condform (nice-cond conds))
       (short (cat "Get the <i>kind</i> (tag) of a @(see " (xdoc::full-escape-symbol sum.name) ") structure.")))
    `((define ,sum.kind ((,sum.xvar ,sum.pred))
        :parents (,sum.name)
        :short ,short
        :returns ,(intern-in-package-of-symbol "KIND" sum.name)
        ,@(and (member :kind sum.inline) `(:inline t))
        :guard-hints ((and stable-under-simplificationp '(:expand ((,sum.pred ,sum.xvar)))))
        :progn t
        ,(if sum.kind-body
             `(mbe :logic ,condform
                   :exec ,sum.kind-body)
           condform)
        ///
        (defthm ,(intern-in-package-of-symbol (cat (symbol-name sum.kind) "-POSSIBILITIES")
                                              sum.kind)
          (or . ,possibilities)
          :rule-classes ((:forward-chaining :trigger-terms ((,sum.kind ,sum.xvar))))))
      (local (in-theory (enable ,sum.kind))))))

(defun flexsum-case-macro-kinds (var prods kwd-alist)
  (b* (((when (atom prods)) nil)
       ((flexprod prod) (car prods)))
    (cons `(,(if (atom (cdr prods))
                 'otherwise
               prod.kind)
            (b* (((,prod.ctor-name ,var :quietp t) ,var))
              ,(cdr (assoc prod.kind kwd-alist))))
          (flexsum-case-macro-kinds var (cdr prods) kwd-alist))))

(defun flexsum-case-macro-conds (var prods kwd-alist)
  (b* (((when (atom prods)) nil)
       ((flexprod prod) (car prods)))
    (cons `(,(if (atom (cdr prods))
                 t
               prod.cond)
            (b* (((,prod.ctor-name ,var :quietp t) ,var))
              ,(cdr (assoc prod.kind kwd-alist))))
          (flexsum-case-macro-conds var (cdr prods) kwd-alist))))

(defun flexsum-case-macro-fn (var-or-binding rest-args sum)
  (b* (((flexsum sum) sum)
       (var (if (consp var-or-binding) (car var-or-binding) var-or-binding))
       (kinds (flexprods->kinds sum.prods))
       ((mv kwd-alist rest)
        (extract-keywords sum.case
                          kinds ;; add other allowed keywords here
                          rest-args nil))
       ((when (and rest (intersectp kinds ;; remove other allowed keywords here?
                                    (strip-cars kwd-alist))))
        ;; We don't know whether the
        ;; (sum-case x :kind1 term1 ...) or
        ;; (sum-case x (:kind1 term1) ...) syntax was intended.
        (er hard? sum.case "Inconsistent syntax: ~x0" rest-args))
       ((unless (and (alistp rest)
                     (true-list-listp rest)
                     ;; weaken this?
                     (subsetp (strip-cars rest) kinds)))
        (er hard? sum.case "Malformed cases: ~x0~%" rest))
       (kind-kwd-alist (append (pairlis$ (strip-cars rest)
                                         (pairlis$ (make-list (len rest) :initial-element 'progn$)
                                                   (strip-cdrs rest)))
                               kwd-alist))
       (body
        (if sum.kind
            `(case (,sum.kind ,var)
               . ,(flexsum-case-macro-kinds var sum.prods kind-kwd-alist))
          (nice-cond (flexsum-case-macro-conds var sum.prods kind-kwd-alist)))))
    (if (consp var-or-binding)
        `(let* ((,var ,(cadr var-or-binding))) ,body)
      body)))

(defun flexsum-def-case-macro (sum)
  (b* (((flexsum sum) sum)
       ((unless sum.case) nil))
    `((defmacro ,sum.case (var-or-binding &rest args)
        (declare (xargs :guard (or (symbolp var-or-binding)
                                   (and (true-listp var-or-binding)
                                        (eql (len var-or-binding) 2)
                                        (symbolp (car var-or-binding))))))
        (flexsum-case-macro-fn var-or-binding args ',sum)))))

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
       ,@(and flagp `(:flag ,sum.name))
       :returns (,newx ,sum.pred
                       :hints('(:in-theory (disable ,sum.fix ,sum.pred)
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
            :exec ,sum.xvar))))

;; ------------------ Fixing function: deflist -----------------------

;; ((fn (pfunc-fix (car x)))
;;  (args (ptermlist-fix (cdr x))))
(defun flexlist-fix-def (list flagp)
  (b* (((flexlist list) list))
    `(define ,list.fix ((,list.xvar ,list.pred))
       :measure ,list.measure
       ,@(and flagp `(:flag ,list.name))
       :returns (newx ,list.pred
                      :hints('(:in-theory (disable ,list.fix ,list.pred)
                               :expand ((,list.fix ,list.xvar)
                                        (:free (a b) (,list.pred (cons a b)))
                                        (,list.pred ,list.xvar)
                                        (,list.pred nil)))))
       :verify-guards nil
       :progn t
       ;; [Jared]: inlining this since it's just an identity function
       :inline t
       (mbe :logic (if (atom ,list.xvar)
                       ,(if list.true-listp
                            nil
                          list.xvar)
                     (cons (,list.elt-fix (car ,list.xvar))
                           (,list.fix (cdr ,list.xvar))))
            :exec ,list.xvar))))

;; ------------------ Fixing function: defalist -----------------------
(defun flexalist-fix-def (alist flagp)
  (b* (((flexalist alist) alist))
    `(define ,alist.fix ((,alist.xvar ,alist.pred))
       :measure ,alist.measure
       ,@(and flagp `(:flag ,alist.name))
       :returns (newx ,alist.pred
                      :hints('(:in-theory (disable ,alist.fix ,alist.pred)
                               :expand ((,alist.fix ,alist.xvar)
                                        (:free (a b) (,alist.pred (cons a b)))
                                        (,alist.pred ,alist.xvar)
                                        (,alist.pred nil)))))
       :verify-guards nil
       :progn t
       ;; [Jared]: inlining this since it's just an identity function
       :inline t
       (mbe :logic (if (atom ,alist.xvar)
                       ,(if alist.true-listp nil alist.xvar)
                     (if (consp (car ,alist.xvar))
                         (cons (cons ,(if alist.key-fix
                                          `(,alist.key-fix (caar ,alist.xvar))
                                        `(caar ,alist.xvar))
                                     ,(if alist.val-fix
                                          `(,alist.val-fix (cdar ,alist.xvar))
                                        `(cdar ,alist.xvar)))
                               (,alist.fix (cdr ,alist.xvar)))
                       (,alist.fix (cdr ,alist.xvar))))
            :exec ,alist.xvar))))

;; ------------------ Fixing function: deftypes -----------------------
(defun flextypelist-fix-defs (types flagp)
  (if (atom types)
      nil
    (cons (with-flextype-bindings (x (car types))
            (flex*-fix-def x flagp))
          (flextypelist-fix-defs (cdr types) flagp))))

(defun flextypelist-fixes (types)
  (if (atom types)
      nil
    (cons (with-flextype-bindings (x (car types)) x.fix)
          (flextypelist-fixes (cdr types)))))

(defun flextypelist-equivs (types)
  (if (atom types)
      nil
    (cons (with-flextype-bindings (x (car types)) x.equiv)
          (flextypelist-equivs (cdr types)))))

;; ------------------ Fixing function post-events -----------------------
(defun flexsum-fix-postevents (x)
  (b* (((flexsum x) x))
    (and x.kind
         `((deffixequiv ,x.kind :args ((,x.xvar ,x.pred))
             :hints (("goal" :expand ((,x.fix ,x.xvar)))))))))

(defun flexlist-fix-postevents (x)
  (b* (((flexlist x) x)
       ;; std::defprojection-compatible variable names
       (stdx (intern-in-package-of-symbol "X" x.pred))
       (stda (intern-in-package-of-symbol "A" x.pred)))
    `((deffixcong ,x.equiv ,x.elt-equiv (car x) x
        :hints (("goal" :expand ((,x.fix x)))))

      (deffixcong ,x.equiv ,x.equiv (cdr x) x
        :hints (("goal" :expand ((,x.fix x)))))

      (deffixcong ,x.elt-equiv ,x.equiv (cons x y) x
        :hints (("goal" :Expand ((:free (a b) (,x.fix (cons a b)))))))

      (deffixcong ,x.equiv ,x.equiv (cons x y) y
        :hints (("goal" :Expand ((:free (a b) (,x.fix (cons a b)))))))

      (defthm ,(intern-in-package-of-symbol (cat "CONSP-OF-" (symbol-name x.fix))
                                            x.fix)
        (equal (consp (,x.fix x))
               (consp x))
        :hints (("goal" :expand ((,x.fix x)))))

      (defthm ,(intern-in-package-of-symbol (cat (symbol-name x.fix) "-OF-CONS")
                                            x.fix)
        ;; bozo make sure this is compatible with defprojection
        (equal (,x.fix (cons ,stda ,stdx))
               (cons (,x.elt-fix ,stda)
                     (,x.fix ,stdx)))
        :hints (("goal" :Expand ((:free (a b) (,x.fix (cons a b)))))))

      (defthm ,(intern-in-package-of-symbol (cat "LEN-OF-" (symbol-name x.fix))
                                            x.fix)
        (equal (len (,x.fix x))
               (len x))
        :hints (("goal" :expand ((,x.fix x))
                 :in-theory (enable len)))))))

(defun flexalist-fix-postevents (x)
  (b* (((flexalist x) x)
       ;; std::defprojection-compatible variable names
       (stdx (intern-in-package-of-symbol "X" x.pred)))
    `(,@(and x.key-type
             `((deffixcong ,x.key-equiv ,x.equiv (cons (cons k v) x) k
                 :hints (("goal" :Expand ((:free (a b) (,x.fix (cons a b)))))))))

      ,@(and x.val-type
             `((deffixcong ,x.val-equiv ,x.equiv (cons (cons k v) x) v
                 :hints (("goal" :Expand ((:free (a b) (,x.fix (cons a b)))))))))

      (deffixcong ,x.equiv ,x.equiv (cons x y) y
        :hints (("goal" :Expand ((:free (a b) (,x.fix (cons a b)))))))

      (defthm ,(intern-in-package-of-symbol (cat (symbol-name x.fix) "-OF-ACONS")
                                            x.fix)
        ;; bozo make sure this is compatible with defprojection
        (equal (,x.fix (cons (cons a b) ,stdx))
               (cons (cons ,(if x.key-fix `(,x.key-fix a) 'a)
                           ,(if x.val-fix `(,x.val-fix b) 'b))
                     (,x.fix ,stdx)))
        :hints (("goal" :Expand ((:free (a b) (,x.fix (cons a b))))))))))

(defun flextypelist-fix-postevents (types)
  (if (atom types)
      nil
    (append (with-flextype-bindings (x (car types))
              (flex*-fix-postevents x))
            (flextypelist-fix-postevents (cdr types)))))

;; ------------------ Fix-when-predicate theorem -----------------------
(defun flexsum-fix-when-pred-thm (x flagp)
  (b* (((flexsum x) x))
    `(defthm ,(intern-in-package-of-symbol (cat (symbol-name x.fix) "-WHEN-" (symbol-name x.pred))
                                           x.fix)
       (implies (,x.pred ,x.xvar)
                (equal (,x.fix ,x.xvar) ,x.xvar))
       :hints ('(:expand ((,x.pred ,x.xvar)
                          (,x.fix ,x.xvar))
                 :in-theory (disable ,x.pred ,x.fix)))
       . ,(and flagp `(:flag ,x.name)))))

(defun flexlist-fix-when-pred-thm (x flagp)
  (b* (((flexlist x) x))
    `(defthm ,(intern-in-package-of-symbol (cat (symbol-name x.fix) "-WHEN-" (symbol-name x.pred))
                                           x.fix)
       (implies (,x.pred ,x.xvar)
                (equal (,x.fix ,x.xvar) ,x.xvar))
       :hints ('(:expand ((,x.pred ,x.xvar)
                          (,x.fix ,x.xvar))
                 :in-theory (disable ,x.fix ,x.pred)))
       . ,(and flagp `(:flag ,x.name)))))

(defun flexalist-fix-when-pred-thm (x flagp)
  (b* (((flexalist x) x))
    `(defthm ,(intern-in-package-of-symbol (cat (symbol-name x.fix) "-WHEN-" (symbol-name x.pred))
                                           x.fix)
       (implies (,x.pred ,x.xvar)
                (equal (,x.fix ,x.xvar) ,x.xvar))
       :hints ('(:expand ((,x.pred ,x.xvar)
                          (,x.fix ,x.xvar))
                 :in-theory (disable ,x.fix ,x.pred)))
       . ,(and flagp `(:flag ,x.name)))))

(defun flextypelist-fix-when-pred-thms (types flagp)
  (if (atom types)
      nil
    (cons (with-flextype-bindings (x (car types))
            (flex*-fix-when-pred-thm x flagp))
          (flextypelist-fix-when-pred-thms (cdr types) flagp))))

(defun flextypelist-pred-calls (types)
  (if (atom types)
      nil
    (cons (with-flextype-bindings (x (car types))
            (list x.pred x.xvar))
          (flextypelist-pred-calls (cdr types)))))

(defun flextypelist-fixtypes (types)
  (if (atom types)
      nil
    (append (with-flextype-bindings (x (car types))
              `((deffixtype ,x.name
                  :pred ,x.pred
                  :fix ,x.fix
                  :equiv ,x.equiv
                  :define t :forward t)
                (local (in-theory (enable ,x.equiv)))))
            (flextypelist-fixtypes (cdr types)))))

(defun flextypes-form-append-hints (new-hints form)
  (b* ((mem (member :hints form))
       ((unless mem) (append form `(:hints ,new-hints)))
       (prefix (take (- (len form) (len mem)) form)))
    (append prefix (cons :hints (cons (append new-hints (cadr mem))
                                      (cddr mem))))))

(defun flextypes-fix-def (x)
  (b* (((flextypes x) x)
       (flagp (consp (cdr x.types)))
       (defs (flextypelist-fix-defs x.types flagp))
       (flag-name (and flagp
                       (intern-in-package-of-symbol (cat (symbol-name x.name) "-FIX-FLAG")
                                                    x.name)))
       (flag-defthm-name (and flagp
                              (flag::thm-macro-name flag-name)))
       (fix-when-pred-thms
        (flextypelist-fix-when-pred-thms x.types flagp)))
    `(,(append (if flagp
                   `(defines ,(intern-in-package-of-symbol (cat (symbol-name x.name) "-FIX")
                                                           x.name)
                      :flag ,flag-name
                      :progn t
                      . ,defs)
                 (car defs))
               `(///
                 (local (in-theory (disable . ,(pairlis$
                                                (make-list (len x.types) :initial-element :d)
                                                (pairlis$ (flextypelist-fixes x.types) nil)))))
                 ,(if flagp
                      `(,flag-defthm-name . ,fix-when-pred-thms)
                    (if x.recp
                        (flextypes-form-append-hints
                         '(("goal" :induct t))
                         (car fix-when-pred-thms))
                      (car fix-when-pred-thms)))

                 (verify-guards+ ,(cadr (car defs))
                   :hints (("goal"
                            :expand ,(flextypelist-pred-calls x.types))))

                 ,@(flextypelist-fixtypes x.types)

                 . ,(flextypelist-fix-postevents x.types)))
      (local (in-theory (enable . ,(flextypelist-equivs x.types))))
      (local (in-theory (disable . ,(flextypelist-fixes x.types))))
      )))


;; ------------------ Product accessors -----------------------

(defun flexprod-field-acc (x prod sum)
  (b* (((flexsum sum) sum)
       ((flexprod prod) prod)
       ((flexprod-field x) x)
       ;; (fixprep (cdr (assoc :fixprep sum.kwd-alist)))
       (short (b* ((acc nil)
                   (acc (revappend-chars "Get the <tt>" acc))
                   (acc (html-encode-str (xdoc::name-low (symbol-name x.name)) acc))
                   (acc (revappend-chars "</tt> field from a @(see? " acc))
                   (acc (revappend-chars (xdoc::full-escape-symbol prod.type-name) acc))
                   (acc (revappend-chars ")." acc)))
                (rchars-to-string acc)))
       (long  "<p>This is an ordinary field accessor created by @(see fty::defprod).</p>"))
    `((define ,x.acc-name ((,sum.xvar ,sum.pred))
        :parents (,prod.type-name)
        :short ,short
        :long ,long
        ,@(and (member :acc prod.inline) `(:inline t))
        ;; :prepwork ((local (in-theory (enable ,sum.fix ,sum.pred))))
        :guard ,prod.guard
        :guard-hints (("goal" :expand ((,sum.pred ,sum.xvar))))
        :returns ,(if x.type
                      `(,x.name ,x.type . ,x.rule-classes)
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
                                   ,(if x.fix
                                        `(,x.fix nil)
                                      nil)))
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

(defun flexprod-fields->acc-names (fields)
  (if (atom fields)
      nil
    (cons (flexprod-field->acc-name (car fields))
          (flexprod-fields->acc-names (cdr fields)))))

;;     (defthm pterm-varname-of-pterm-var
;;       (equal (pterm-varname (pterm-var varname))
;;              (var-fix varname)))
(defun flexprod-acc-of-ctor-thms1 (fields ctor-call)
  (b* (((when (atom fields)) nil)
       ((flexprod-field x) (car fields))
       (fixterm (if (eq x.reqfix x.name)
                    (if x.fix
                      `(,x.fix ,x.name)
                    x.name)
                  (if x.fix
                        `(let ((,x.name (,x.fix ,x.name)))
                           ,x.reqfix)
                      x.reqfix))))
    (cons `(defthm ,(intern-in-package-of-symbol
                     (cat (symbol-name x.acc-name) "-OF-" (symbol-name (car ctor-call)))
                     x.acc-name)
             (equal (,x.acc-name ,ctor-call)
                    ,fixterm)
             :hints(("Goal" :in-theory (e/d (,x.acc-name)
                                            (,(car ctor-call))))
                    (and stable-under-simplificationp
                         '(:in-theory (enable ,(car ctor-call))))))
          (flexprod-acc-of-ctor-thms1 (cdr fields) ctor-call))))

(defun flexprod-acc-of-ctor-thms (prod)
  (flexprod-acc-of-ctor-thms1 (flexprod->fields prod)
                              (flexprod-ctor-call prod)))

(defun flexprod-fields-acc-calls (fields xvar)
  (if (atom fields)
      nil
    (cons `(,(flexprod-field->acc-name (car fields)) ,xvar)
          (flexprod-fields-acc-calls (cdr fields) xvar))))

(defun flexprod-equal-of-field-accessors (fields xvar)
  (if (atom fields)
      nil
    (cons (b* (((flexprod-field x) (car fields)))
            `(equal (,x.acc-name ,xvar)
                    ,(if (eq x.reqfix x.name)
                         (if x.fix
                             `(,x.fix ,x.name)
                           x.name)
                       (if x.fix
                           `(let ((,x.name (,x.fix ,x.name)))
                              ,x.reqfix)
                         x.reqfix))))
          (flexprod-equal-of-field-accessors (cdr fields) xvar))))

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

(defun flexprod-constructor (prod sum)
  (b* (((flexsum sum) sum)
       ((flexprod prod) prod)
       (field-calls (flexprod-fields-acc-calls prod.fields sum.xvar))
       (fieldnames (flexprod-fields->names prod.fields))
       (field-accs (pairlis$ fieldnames
                             (flexprod-fields->acc-names prod.fields)))
       (ctor-of-fields-thmname
        (intern-in-package-of-symbol (cat (symbol-name prod.ctor-name) "-OF-FIELDS")
                                     prod.ctor-name))
       (fix-when-kind-thmname
        (intern-in-package-of-symbol (cat (symbol-name sum.fix) "-WHEN-" (symbol-name prod.kind))
                                     sum.fix))

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
                        :hints(("Goal" :in-theory (enable ,sum.pred))))
        :progn t
        ,typefix-body
        ///
        (deffixequiv ,prod.ctor-name)

        ,@(flexprod-acc-of-ctor-thms prod)

        ,@(and (not (eq prod.require t))
               `((defthm ,(intern-in-package-of-symbol (cat (symbol-name prod.ctor-name) "-REQUIREMENTS")
                                                       prod.ctor-name)
                   (b* ,(flexprod-fields-bind-accessors prod.fields sum.xvar)
                     ,prod.require))))

        ,@(and
           ;; special case: we can have an empty product, in which case we don't
           ;; want a rule like (equal (my-const-product) (my-sum-fix x))
           (consp prod.fields)
           `((defthm ,ctor-of-fields-thmname
               ,(nice-implies prod.guard
                              `(equal (,prod.ctor-name . ,field-calls)
                                      (,sum.fix ,sum.xvar)))
               :hints(("Goal" ;; :in-theory (enable ,sum.fix)
                       :expand ((,sum.fix ,sum.xvar)))))))

        (,(if (atom prod.fields) 'defthm 'defthmd)
               ;; ,(if (eq prod.guard t) 'defthmd 'defthm)
         ,fix-when-kind-thmname
          ,(nice-implies prod.guard
                         `(equal (,sum.fix ,sum.xvar)
                                 (,prod.ctor-name . ,field-calls)))
          :hints(("Goal" ;; :in-theory (enable ,sum.fix)
                  :expand ((,sum.fix ,sum.xvar))))
          . ,(and (not (eq prod.guard t))
                  '(:rule-classes ((:rewrite :backchain-limit-lst 0)))))

        (defthm ,(intern-in-package-of-symbol (cat "EQUAL-OF-" (symbol-name prod.ctor-name))
                                              prod.ctor-name)
          (equal (equal ,(flexprod-ctor-call prod) ,sum.xvar)
                 (and (,sum.pred ,sum.xvar)
                      ,@(and (not (eq prod.guard t)) (list prod.guard))
                      . ,(flexprod-equal-of-field-accessors prod.fields sum.xvar)))
          :hints (("goal" :in-theory (disable ,prod.ctor-name
                                              ,@(flexprod-fields->acc-names prod.fields)
                                              ,@(and sum.kind `(,sum.kind))
                                              ,@(if (consp prod.fields)
                                                    `(,ctor-of-fields-thmname)
                                                  `(,fix-when-kind-thmname)))
                   ,@(if (consp prod.fields)
                         `(:use ,ctor-of-fields-thmname)
                       `(:use ,fix-when-kind-thmname)))
                  (and stable-under-simplificationp
                       '(:in-theory (e/d (,prod.ctor-name)
                                         (,@(flexprod-fields->acc-names prod.fields)
                                            ,@(and sum.kind `(,sum.kind))
                                            ,@(if (consp prod.fields)
                                                  `(,ctor-of-fields-thmname)
                                                `(,fix-when-kind-thmname))))))))

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

        (defmacro ,prod.ctor-macro (&key . ,(flexprod-fields-macro-args prod.fields))
          (list ',prod.ctor-name
                . , (flexprod-fields->names prod.fields)))

        (acl2::def-b*-binder ,prod.ctor-name
          :body
          (std::da-patbind-fn ',prod.ctor-name
                              ',field-accs
                              acl2::args acl2::forms acl2::rest-expr))

        ,(std::da-make-changer-fn-gen prod.ctor-name field-accs)
        ,(std::da-make-changer prod.ctor-name fieldnames))

      (local (in-theory (enable ,prod.ctor-name))))))

;; ------------ Collect accessor/constructor names ---------------
(defun flexprod-field-accs (fields)
  (if (atom fields)
      nil
    (cons (flexprod-field->acc-name (car fields))
          (flexprod-field-accs (cdr fields)))))

(defun flexprod-fns (prod)
  (b* (((flexprod prod) prod))
    (cons prod.ctor-name
          (flexprod-field-accs prod.fields))))

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
          (flexprod-constructor prod sum)))

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

(defun flextype-fix-fns (types)
  (if (atom types)
      nil
    (cons (with-flextype-bindings (x (car types)) x.fix)
          (flextype-fix-fns (cdr types)))))

(defun flexsum-acc/ctor-events (sum types)
  (declare (ignorable types))
  (b* (((flexsum sum) sum))
    (append (flexsum-prods-accessor/constructors sum.prods sum)
            `((defthmd ,(intern-in-package-of-symbol (cat (symbol-name sum.fix) "-REDEF")
                                                     sum.fix)
                (equal (,sum.fix ,sum.xvar)
                       ,(if sum.kind
                            `(case (,sum.kind ,sum.xvar)
                               . ,(flexsum-fix-redef-prod-cases sum.prods sum.xvar))
                          (nice-cond (flexsum-fix-redef-prod-cases-nokind sum.prods sum.xvar))))
                :hints(("Goal" :in-theory (disable . ,(flexsum-fns sum)))
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
(defun flextypes-find-count-for-pred (pred types)
  (if (atom types)
      nil
    (or (with-flextype-bindings (x (car types))
          (and (eq pred x.pred) x.count))
        (flextypes-find-count-for-pred pred (cdr types)))))

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
       (count (if fieldcounts `(+ ,(+ 1 (len x.fields)) . ,fieldcounts) 1)))
    (cons `(,x.kind ,count)
          (flexsum-prod-counts (cdr prods) xvar types))))

(defun flexsum-prod-counts-nokind (prods xvar types)
  (b* (((when (atom prods)) nil)
       ((flexprod x) (car prods))
       (fieldcounts (flexprod-field-counts x.fields xvar types))
       (prodcount (if fieldcounts `(+ ,(+ 1 (len x.fields)) . ,fieldcounts) 1)))
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
        :returns (count natp :rule-classes :type-prescription
                        :hints ('(:expand (,x.count ,x.xvar)
                                  :in-theory (disable ,x.count
                                                      . ,(flexsum-prod-fns x.prods)))))
        :measure (let ((,x.xvar (,x.fix ,x.xvar)))
                   ,x.measure)
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
       ((flexsum sum) sum))
    `((defthm ,(intern-in-package-of-symbol (cat (symbol-name type-count) "-OF-" (symbol-name x.acc-name))
                                            x.acc-name)
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
                 (,sum.count ,call))))
    `((defthm ,(intern-in-package-of-symbol (cat (symbol-name sum.count) "-OF-" (symbol-name x.ctor-name))
                                            sum.count)
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


;; ------------------ Count events: deflist -----------------------
(defun flexlist-count (x types)
  (b* (((flexlist x) x)
       ((unless x.count) nil)
       (eltcount (flextypes-find-count-for-pred x.elt-type types)))
    `((define ,x.count ((,x.xvar ,x.pred))
       :returns (count natp :rule-classes :type-prescription
                       :hints ('(:expand (,x.count ,x.xvar)
                                 :in-theory (disable ,x.count))))
       :measure (let ((,x.xvar (,x.fix ,x.xvar)))
                  ,x.measure)
       :verify-guards nil
       :progn t
       (if (atom ,x.xvar)
           1
         (+ 1
            ,@(and eltcount `((,eltcount (car ,x.xvar))))
            (,x.count (cdr ,x.xvar))))))))

(defun flexlist-count-post-events (x types)
  (b* (((flexlist x) x)
       ((unless x.count) nil)
       (eltcount (flextypes-find-count-for-pred x.elt-type types))
       ;; ((when (not eltcount)) nil)
       )
    `((defthm ,(intern-in-package-of-symbol (cat (symbol-name x.count) "-OF-CONS")
                                            x.count)
        (> (,x.count (cons a b))
           ,(if eltcount
                `(+ (,eltcount a) (,x.count b))
              `(,x.count b)))
        :hints (("goal" :expand ((:free (a b) (,x.count (cons a b))))))
        :rule-classes :linear)

      ,@(and
         eltcount
         `((defthm ,(intern-in-package-of-symbol (cat (symbol-name eltcount) "-OF-CAR")
                                                 x.count)
             (implies (consp ,x.xvar)
                      (< (,eltcount (car ,x.xvar)) (,x.count ,x.xvar)))
             :rule-classes :linear)))

      (defthm ,(intern-in-package-of-symbol (cat (symbol-name x.count) "-OF-CDR")
                                            x.count)
        (implies (consp ,x.xvar)
                 (< (,x.count (cdr ,x.xvar)) (,x.count ,x.xvar)))
        :rule-classes :linear))))


;; ------------------ Count events: defalist -----------------------
(defun flexalist-count (x types)
  (b* (((flexalist x) x)
       ((unless x.count) nil)
       (keycount (flextypes-find-count-for-pred x.key-type types))
       (valcount (flextypes-find-count-for-pred x.val-type types)))
    `((define ,x.count ((,x.xvar ,x.pred))
        :returns (count natp :rule-classes :type-prescription
                        :hints ('(:expand (,x.count ,x.xvar)
                                  :in-theory (disable ,x.count))))
        :measure (let ((,x.xvar (,x.fix ,x.xvar)))
                   ,x.measure)
        :verify-guards nil
        :progn t
        (let ((,x.xvar (mbe :logic (,x.fix ,x.xvar) :exec ,x.xvar)))
          (if (atom ,x.xvar)
              1
            (+ 1
               ,@(and (or keycount valcount)
                      (if keycount
                          (if valcount
                              `((+ (,keycount (caar ,x.xvar))
                                   (,valcount (cdar ,x.xvar))))
                            `((,keycount (caar ,x.xvar))))
                        `((,valcount (cdar ,x.xvar)))))
               (,x.count (cdr ,x.xvar)))))))))

(defun flexalist-count-post-events (x types)
  (b* (((flexalist x) x)
       ((unless x.count) nil)
       (keycount (flextypes-find-count-for-pred x.key-type types))
       (valcount (flextypes-find-count-for-pred x.val-type types))
       ;; ((when (not eltcount)) nil)
       )
    `((defthm ,(intern-in-package-of-symbol (cat (symbol-name x.count) "-OF-CONS")
                                            x.count)
        (>= (,x.count (cons a b))
            (,x.count b))
        :hints (("goal" :expand ((:free (a b) (,x.count (cons a b)))
                                 (,x.fix (cons a b))))
                (and stable-under-simplificationp
                     '(:expand ((,x.count b)))))
        :rule-classes :linear)

      ,@(and (or keycount valcount)
             `((defthm ,(intern-in-package-of-symbol (cat (symbol-name x.count) "-OF-ACONS")
                                                     x.count)
                 (> (,x.count (cons (cons a b) c))
                    (+ ,@(if keycount
                             (if valcount
                                 `((,keycount a)
                                   (,valcount b))
                               `((,keycount a)))
                           `((,valcount b)))
                       (,x.count c)))
                 :hints (("goal" :expand ((:free (a b) (,x.count (cons a b))))))
                 :rule-classes :linear)))
      ,@(and
         keycount
         `((defthm ,(intern-in-package-of-symbol (cat (symbol-name keycount) "-OF-CAAR-"
                                                      (symbol-name x.count))
                                                 x.count)
             (implies (and (consp ,x.xvar)
                           (consp (car ,x.xvar)))
                      (< (,keycount (caar ,x.xvar)) (,x.count ,x.xvar)))
             :rule-classes :linear)))

      ,@(and
         valcount
         `((defthm ,(intern-in-package-of-symbol (cat (symbol-name valcount) "-OF-CDAR-"
                                                      (symbol-name x.count))
                     x.count)
             (implies (and (consp ,x.xvar)
                           (consp (car ,x.xvar)))
                      (< (,valcount (cdar ,x.xvar)) (,x.count ,x.xvar)))
             :rule-classes :linear)))

      (defthm ,(intern-in-package-of-symbol (cat (symbol-name x.count) "-OF-CDR")
                                            x.count)
        (<= (,x.count (cdr ,x.xvar)) (,x.count ,x.xvar))
        :hints (("goal" :expand ((,x.fix ,x.xvar)
                                 (,x.count ,x.xvar)
                                 (,x.count (cdr ,x.xvar))
                                 (:free (a b) (,x.count (cons a b))))
                 :in-theory (enable acl2::default-cdr)))
        :rule-classes :linear))))


;; ------------------ Collect function names -----------------------
(defun flexlist-fns (x)
  (b* (((flexlist x) x))
    (list x.pred
          x.fix)))

(defun flexalist-fns (x)
  (b* (((flexalist x) x))
    (list x.pred
          x.fix)))

(defun flextypes-fns (types)
  (if (atom types)
      nil
    (append (with-flextype-bindings (x (car types)) (flex*-fns x))
            (flextypes-fns (cdr types)))))

(defun flextypes-acc/ctors (types)
  (if (atom types)
      nil
    (append (and (eq (caar types) :sum)
                 (flexsum-prod-fns (flexsum->prods (car types))))
            (flextypes-acc/ctors (cdr types)))))

(defun flextypes-ctors (types)
  (if (atom types)
      nil
    (append (and (eq (caar types) :sum)
                 (flexsum-prod-ctors (flexsum->prods (car types))))
            (flextypes-ctors (cdr types)))))


;; ------------------ Count events: deftypes -----------------------
(defun flextypes-count-defs (x alltypes)
  (if (atom x)
      nil
    (append (with-flextype-bindings (x (car x))
              (flex*-count x alltypes))
            (flextypes-count-defs (cdr x) alltypes))))

(defun flextypes-count-expands (types)
  (if (atom types)
      nil
    (append (with-flextype-bindings (x (car types))
              (and x.count
                   `((,x.count ,x.xvar)
                     (,x.count (,x.fix ,x.xvar)))))
            (flextypes-count-expands (cdr types)))))

(defun flextypes-count-names (x)
  (if (atom x)
      nil
    (append (with-flextype-bindings (x (car x))
              (and x.count (list x.count)))
            (flextypes-count-names (cdr x)))))

(defun flextypes-count-post-events (types alltypes)
  (if (atom types)
      nil
    (append (with-flextype-bindings (x (car types))
              (flex*-count-post-events x alltypes))
            (flextypes-count-post-events (cdr types) alltypes))))

(defun flextypes-nokind-expand-fixes (types)
  (if (atom types)
      nil
    (if (and (eq (tag (car types)) :sum)
             (not (flexsum->kind (car types))))
        (cons `(,(flexsum->fix (car types)) ,(flexsum->xvar (car types)))
              (flextypes-nokind-expand-fixes (cdr types)))
      (flextypes-nokind-expand-fixes (cdr types)))))

(defun flextypes-expand-fixes (types)
  (if (atom types)
      nil
    (cons (with-flextype-bindings (x (car types))
            `(,x.fix ,x.xvar))
          (flextypes-expand-fixes (cdr types)))))

(defun flexprods-ctor-of-fields-thms (prods)
  (if (atom prods)
      nil
    (if (consp (flexprod->fields (car prods)))
        (cons (intern-in-package-of-symbol (cat (symbol-name (flexprod->ctor-name (car prods))) "-OF-FIELDS")
                                           (flexprod->ctor-name (car prods)))
              (flexprods-ctor-of-fields-thms (cdr prods)))
      (flexprods-ctor-of-fields-thms (cdr prods)))))

(defun flextypes-ctor-of-fields-thms (types)
  (if (atom types)
      nil
    (append (and (eq (caar types) :sum)
                 (flexprods-ctor-of-fields-thms (flexsum->prods (car types))))
            (flextypes-ctor-of-fields-thms (cdr types)))))

(defun flexprods-fix-when-kind-thms (prods sum)
  (if (atom prods)
      nil
    (if (consp (flexprod->fields (car prods)))
        (cons (intern-in-package-of-symbol (cat (symbol-name (flexsum->fix sum))
                                                "-WHEN-" (symbol-name (flexprod->kind (car prods))))
                                           (flexsum->fix sum))
              (flexprods-fix-when-kind-thms (cdr prods) sum))
      (flexprods-fix-when-kind-thms (cdr prods) sum))))

(defun flextypes-fix-when-kind-thms (types)
  (if (atom types)
      nil
    (append (and (eq (caar types) :sum)
                 (flexprods-fix-when-kind-thms (flexsum->prods (car types)) (car types)))
            (flextypes-fix-when-kind-thms (cdr types)))))

(defun flextypes-count (x)
  (b* (((flextypes x) x)
       ((when x.no-count) nil)
       (defs (flextypes-count-defs x.types x.types))
       (names (flextypes-count-names x.types))
       ((when (not defs)) ;; none of the types have a count
        nil)
       (flagp (consp (cdr defs)))
       (measure-hints
        ;; original
        ;; `((and stable-under-simplificationp
        ;;        '(:in-theory (enable . ,(flextypes-acc/ctors x.types))))
        ;;   (and stable-under-simplificationp
        ;;        '(:expand ,(flextypes-nokind-expand-fixes x.types))))
        `((and stable-under-simplificationp
               '(:expand ,(flextypes-expand-fixes x.types)
                 :in-theory (e/d  ,(flextypes-ctors x.types))
                 )))
        )
       (prepwork `((local (in-theory (e/d ,(flextypes-fix-when-kind-thms x.types)
                                          ,(flextypes-ctor-of-fields-thms x.types)))))))
    (if flagp
        (let ((defines-name (intern-in-package-of-symbol (cat (symbol-name x.name) "-COUNT")
                                                         x.name)))
          `((defines ,defines-name
              :hints ,measure-hints
              :prepwork ,prepwork
              :progn t
              ,@defs
              ///
              (local (in-theory (disable . ,(flextypes-count-names x.types))))
              (verify-guards+ ,(cadr (car defs)))
              (deffixequiv-mutual ,defines-name
                :hints (;; ("goal" :expand ,(flextypes-count-expands x.types))
                        (and stable-under-simplificationp
                             (let ((lit (car (last clause))))
                               (and (eq (car lit) 'equal)
                                    (let ((expands (append (and (consp (cadr lit))
                                                                (member (car (cadr lit))
                                                                        ',names)
                                                                (list (cadr lit)))
                                                           (and (consp (caddr lit))
                                                                (member (car (caddr lit))
                                                                        ',names)
                                                                (list (caddr lit))))))
                                      (and expands
                                           `(:expand ,expands))))))))

              . ,(flextypes-count-post-events x.types x.types))))
      (list
       (append
        (car defs)
        `(:hints ,measure-hints
          :prepwork ,prepwork
          ///
          (local (in-theory (disable . ,(flextypes-count-names x.types))))
          (verify-guards+ ,(cadr (car defs))
                          :hints ((and stable-under-simplificationp
                                       '(:expand ,(flextypes-nokind-expand-fixes x.types)))))
          (deffixequiv ,(cadr (car defs))
            :hints (("goal" :expand ,(flextypes-count-expands x.types))
                    (and stable-under-simplificationp
                         '(:expand ,(flextypes-nokind-expand-fixes x.types)))))
          . ,(flextypes-count-post-events x.types x.types)))))))

;; ------------------ Xdoc processing -----------------------

(defun flexlist->defxdoc (x parents state)
  ;; Returns (mv events state)
  (declare (ignorable x parents state))
  (mv nil state))

(defun flexalist->defxdoc (x parents state)
  ;; Returns (mv events state)
  (declare (ignorable x parents state))
  (mv nil state))

(defun defprod-field-doc (x acc base-pkg state)
  (b* (((flexprod-field x) x)
       (acc (revappend-chars "<dt>" acc))
       ((mv name-str state) (xdoc::fmt-to-str-orig x.name base-pkg state))
       (acc (html-encode-str name-str acc))
       (acc (b* (((when (eq x.type nil))
                  acc)
                 (acc (revappend-chars " &mdash; @(see? " acc))
                 (acc (revappend-chars (xdoc::full-escape-symbol x.type) acc))
                 (acc (revappend-chars ")" acc)))
              acc))
       (acc (revappend-chars "</dt>" acc))
       (acc (cons #\Newline acc))
       (acc (b* (((when (equal x.doc ""))
                  acc)
                 (acc (revappend-chars "<dd>" acc))
                 (acc (revappend-chars x.doc acc))
                 (acc (revappend-chars "</dd>" acc))
                 (acc (cons #\Newline acc)))
              acc))
       (acc (cons #\Newline acc)))
    (mv acc state)))

(defun defprod-fields-doc-aux (x acc base-pkg state)
  (b* (((when (atom x))
        (mv acc state))
       ((mv acc state)
        (defprod-field-doc (car x) acc base-pkg state)))
    (defprod-fields-doc-aux (cdr x) acc base-pkg state)))

(defun defprod-fields-doc (x acc base-pkg state)
  (b* ((acc (revappend-chars "<ul>" acc))
       ((mv acc state) (defprod-fields-doc-aux x acc base-pkg state))
       (acc (revappend-chars "</ul>" acc)))
    (mv acc state)))

(defun defprod-main-description (prod base-pkg acc state)
  ;; Returns (mv acc state)
  (b* (((flexprod prod) prod)
       (acc  (revappend-chars "<h5>Fields</h5>" acc))
       (acc  (cons #\Newline acc))
       ((mv acc state)
        ;; BOZO this is all wrong
        (defprod-fields-doc prod.fields acc base-pkg state))
       ((when (eq prod.require t))
        ;; Don't show stupidly trivial requirement
        (mv acc state))
       (acc (revappend-chars "<h5>Additional Requirements</h5>" acc))
       (acc (revappend-chars "<p>The following invariant is enforced on the fields:</p>" acc))
       ((mv req-str state) (xdoc::fmt-to-str-orig prod.require base-pkg state))
       (acc (revappend-chars "<code>" acc))
       (acc (html-encode-str req-str acc))
       (acc (revappend-chars "</code>" acc)))
    (mv acc state)))

(defun defprod-main-autodoc (x parents base-pkg state)
  ;; Returns (mv events state)
  (b* (((flexsum x) x)
       (prod  (car x.prods))
       (short (cdr (assoc :short x.kwd-alist)))
       (long  (cdr (assoc :long x.kwd-alist)))
       (acc  nil)
       (acc  (revappend-chars "<p>This is a product type introduced by @(see fty::defprod).</p>" acc))
       (acc  (cons #\Newline acc))
       ((mv acc state) (defprod-main-description prod base-pkg acc state))
       (acc  (revappend-chars (or long "") acc))
       (long (rchars-to-string acc)))
    (mv `((defxdoc ,x.name
            :parents ,parents
            :short ,short
            :long ,long))
        state)))

(defun defprod-ctor-optional-fields (field-names)
  (declare (xargs :guard (symbol-listp field-names)))
  (b* (((when (atom field-names))
        nil)
       (name1 (xdoc::name-low (symbol-name (car field-names))))
       (acc   nil)
       (acc   (revappend-chars "[:" acc))
       (acc   (html-encode-str name1 acc))
       (acc   (revappend-chars " &lt;" acc))
       (acc   (html-encode-str name1 acc))
       (acc   (revappend-chars "&gt;]" acc)))
    (cons (rchars-to-string acc)
          (defprod-ctor-optional-fields (cdr field-names)))))

(defun defprod-ctor-optional-call (name        ; e.g., make-honsed-foo
                                   field-strs  ; e.g., ("[:field1 <field1>]" "[field2 <field2>"])
                                   )
  (declare (xargs :guard (and (symbolp name)
                              (string-listp field-strs))))
  (b* ((ctor-name (xdoc::name-low (symbol-name name)))
       ;; +2 to account for the leading paren and trailing space after ctor-name
       (len       (+ 2 (length ctor-name)))
       (pad       (str::implode (cons #\Newline (make-list len :initial-element #\Space))))
       (args      (str::join field-strs pad)))
    (str::cat "<code>" *nl* "(" ctor-name " " args ")" *nl* "</code>")))

#||
(defprod-ctor-optional-call 'make-honsed-foo
                            '("[:lettuce <lettuce>]"
                              "[:cheese <cheese>]"
                              "[:meat <meat>]"))
||#

(defun defprod-ctor-autodoc (prod)
  (b* (((flexprod prod)      prod)
       (foo                  prod.type-name)
       (make-foo-fn          prod.ctor-name)
       (make-foo             prod.ctor-macro)
       ;; It doesn't seem like these are stored in the product itself.
       (change-foo-fn        (std::da-changer-fn-name foo))
       (change-foo           (std::da-changer-name foo))

       (plain-foo            (str::cat "<tt>" (xdoc::name-low (symbol-name foo)) "</tt>"))
       (see-foo              (xdoc::see foo))
       (see-make-foo         (xdoc::see make-foo))
       (see-change-foo       (xdoc::see change-foo))

       ;; For make-foo, change-foo, etc., it's nicer to present a list of [:fld <fld>] options
       ;; rather than just saying &rest args, which is what @(call ...) would do.
       (opt-fields           (defprod-ctor-optional-fields (flexprod-fields->names prod.fields)))
       (call-make-foo        (defprod-ctor-optional-call make-foo opt-fields))
       (call-change-foo      (defprod-ctor-optional-call change-foo (cons "x" opt-fields)))

       (def-foo              (str::cat "@(def " (xdoc::full-escape-symbol foo)           ")"))
       (def-make-foo-fn      (str::cat "@(def " (xdoc::full-escape-symbol make-foo-fn)   ")"))
       (def-make-foo         (str::cat "@(def " (xdoc::full-escape-symbol make-foo)      ")"))
       (def-change-foo-fn    (str::cat "@(def " (xdoc::full-escape-symbol change-foo-fn) ")"))
       (def-change-foo       (str::cat "@(def " (xdoc::full-escape-symbol change-foo)    ")")))

    `(;; Unlike defaggregate, I think we don't want to document the raw
      ;; constructor, because it is going to share its name with the type.  I
      ;; also won't try to include honsing information here, for now at least.
      (defxdoc ,make-foo
        :parents (,foo)
        :short ,(str::cat "Basic constructor macro for " see-foo " structures.")
        :long ,(str::cat
                "<h5>Syntax</h5>"
                call-make-foo

                "<p>This is the usual way to construct " see-foo
                " structures.  It simply conses together a structure with the
                specified fields.</p>

                <p>This macro generates a new " plain-foo " structure from
                scratch.  See also " see-change-foo ", which can \"change\" an
                existing structure, instead.</p>"

                "<h3>Definition</h3>

                <p>This is an ordinary @('make-') macro introduced by @(see
                fty::defprod).</p>"

                def-make-foo
                def-make-foo-fn
                def-foo))

      (defxdoc ,change-foo
        :parents (,foo)
        :short ,(str::cat "Modifying constructor for " see-foo " structures.")
        :long ,(str::cat
                "<h5>Syntax</h5>"
                call-change-foo

                "<p>This is an often useful alternative to " see-make-foo ".</p>

                <p>We construct a new " see-foo " structure that is a copy of
                @('x'), except that you can explicitly change some particular
                fields.  Any fields you don't mention just keep their values
                from @('x').</p>

                <h3>Definition</h3>

                <p>This is an ordinary @('change-') macro introduced by @(see
                fty::defprod).</p>"

                def-change-foo
                def-change-foo-fn
                def-foo)))))

(defun defprod->defxdoc (x parents base-pkg state)
  ;; Returns (mv events state)
  (b* (((flexsum x)      x)
       (prod             (car x.prods))
       ((flexprod prod)  prod)
       (foo              x.name)
       (foo-p            x.pred)
       (foo-fix          x.fix)
       (make-foo         prod.ctor-macro)
       (change-foo       (std::da-changer-name foo))

       ((mv main-doc state) (defprod-main-autodoc x parents base-pkg state))
       (make/change         (defprod-ctor-autodoc prod))
       (doc-events (append main-doc
                           make/change
                           ;; Special hack to make the subtopic order for a
                           ;; structure look really nice.  We omit the
                           ;; accessors.  XDOC will put them at the end in
                           ;; alphabetical order.
                           `((xdoc::order-subtopics ,foo
                             (,foo-p ,foo-fix ,make-foo ,change-foo))))))
    (mv doc-events state)))

(defun deftagsum-prod-doc (sum  ; the containing sum type
                           prod ; one of the products within it
                           base-pkg state)
  ;; Returns (mv events state)
  (b* (((flexsum sum) sum)
       ((flexprod prod) prod)
       (acc  nil)
       (acc  (revappend-chars "<p>This is a product type, introduced by @(see " acc))
       (acc  (revappend-chars (xdoc::full-escape-symbol sum.typemacro) acc))
       (acc  (revappend-chars ") in support of @(see " acc))
       (acc  (revappend-chars (xdoc::full-escape-symbol sum.name) acc))
       (acc  (revappend-chars ").</p>" acc))
       (acc  (cons #\Newline acc))
       ((mv acc state) (defprod-main-description prod base-pkg acc state))
       (acc  (revappend-chars (or prod.long "") acc))
       (long (rchars-to-string acc))
       (top-doc `((defxdoc ,prod.type-name
                    :parents (,sum.name)
                    :short ,prod.short
                    :long ,long)))
       (make/change (defprod-ctor-autodoc prod))

       (make-foo         prod.ctor-macro)
       (change-foo       (std::da-changer-name prod.type-name))
       ;; Unlike a standalone defprod, these don't have a fix function
       ;; They also don't have a recognizer
       )
    (mv (append top-doc
                make/change
                `((xdoc::order-subtopics ,prod.type-name (,make-foo ,change-foo)))
                )
        state)))

(defun deftagsum-prods-doc (sum prods base-pkg state)
  ;; Returns (mv events state)
  (b* (((when (atom prods))
        (mv nil state))
       ((mv events1 state) (deftagsum-prod-doc sum (car prods) base-pkg state))
       ((mv events2 state) (deftagsum-prods-doc sum (cdr prods) base-pkg state)))
    (mv (append events1 events2)
        state)))

(defun deftagsum-summarize-prod (sum prod base-pkg acc state)
  ;; Returns (mv acc state)
  (declare (ignorable sum base-pkg))
  (b* (((flexprod prod) prod)
       (acc (revappend-chars "<dt><tt>" acc))
       ((mv kind-str state) (xdoc::fmt-to-str-orig prod.kind base-pkg state))
       (acc (html-encode-str kind-str acc))
       (acc (revappend-chars "</tt> &rarr; @(see " acc))
       (acc (revappend-chars (xdoc::full-escape-symbol prod.type-name) acc))
       (acc (revappend-chars ")</dt>" acc))
       (acc (cons #\Newline acc))

       ((unless prod.short)
        (mv acc state))
       (acc (revappend-chars "<dd>" acc))
       (acc (revappend-chars prod.short acc))
       (acc (revappend-chars "</dd>" acc))
       (acc (cons #\Newline acc)))
    (mv acc state)))

(defun deftagsum-summarize-prods (sum prods base-pkg acc state)
  ;; Returns (mv acc state)
  (b* (((when (atom prods))
        (mv acc state))
       ((mv acc state) (deftagsum-summarize-prod sum (car prods) base-pkg acc state))
       ((mv acc state) (deftagsum-summarize-prods sum (cdr prods) base-pkg acc state)))
    (mv acc state)))

(defun flexprodlist->type-names (x)
  (if (atom x)
      nil
    (cons (flexprod->type-name (car x))
          (flexprodlist->type-names (cdr x)))))

(defun deftagsum->defxdoc (x parents base-pkg state)
  ;; Returns (mv events state)
  (declare (ignorable x parents base-pkg))
  (b* (((flexsum x) x)
       (short (cdr (assoc :short x.kwd-alist)))
       (long  (cdr (assoc :long x.kwd-alist)))
       (acc   nil)
       (acc   (revappend-chars "<p>This is a tagged union type, introduced by @(see fty::deftagsum).</p>" acc))
       (acc   (cons #\Newline acc))
       (acc   (revappend-chars "<h5>Member Tags &rarr; Types</h5>" acc))
       (acc   (revappend-chars "<dl>" acc))
       ((mv acc state) (deftagsum-summarize-prods x x.prods base-pkg acc state))
       (acc   (revappend-chars "</dl>" acc))
       (acc   (cons #\Newline acc))
       (acc   (revappend-chars (or long "") acc))
       (long  (rchars-to-string acc))
       (main-doc `((defxdoc ,x.name
                     :parents ,parents
                     :short ,short
                     :long ,long)))
       ((mv prods-doc state)
        (deftagsum-prods-doc x x.prods base-pkg state)))
    (mv (append main-doc
                prods-doc
                `((xdoc::order-subtopics ,x.name
                                         (,x.pred ,x.fix ,x.kind ,x.equiv ,x.count
                                          . ,(flexprodlist->type-names x.prods)))))
        state)))

(defun defflexsum->defxdoc (x parents base-pkg state)
  ;; Returns (mv events state)
  (declare (ignorable x parents base-pkg))
  (b* (((flexsum x) x)
       (short (cdr (assoc :short x.kwd-alist)))
       (long  (cdr (assoc :long x.kwd-alist)))
       (acc   nil)
       (acc   (revappend-chars "<p>This is a sum-of-products (i.e., union) type, introduced by @(see fty::defflexsum).</p>" acc))
       (acc   (cons #\Newline acc))
       (acc   (revappend-chars "<h5>Members</h5>" acc))
       (acc   (revappend-chars "<dl>" acc))
       ((mv acc state) (deftagsum-summarize-prods x x.prods base-pkg acc state))
       (acc   (revappend-chars "</dl>" acc))
       (acc   (cons #\Newline acc))
       (acc   (revappend-chars (or long "") acc))
       (long  (rchars-to-string acc))
       (main-doc `((defxdoc ,x.name
                     :parents ,parents
                     :short ,short
                     :long ,long)))
       ((mv prods-doc state)
        (deftagsum-prods-doc x x.prods base-pkg state)))
    (mv (append main-doc
                prods-doc
                `((xdoc::order-subtopics ,x.name
                                         (,x.pred ,x.fix ,x.kind ,x.equiv ,x.count
                                          . ,(flexprodlist->type-names x.prods)))))
        state)))

(defun flexsum->defxdoc (x parents state)
  ;; Returns (mv events state)
  (b* ((__function__ 'flexsum->defxdoc)
       ((flexsum x) x)
       (parents (or (cdr (assoc :parents x.kwd-alist)) parents))
       (base-pkg (pkg-witness (acl2::f-get-global 'acl2::current-package state)))
       ((unless (symbol-listp parents))
        (mv (raise "~x0: :parents must be a list of symbols." x.name) state)))
    (case x.typemacro
      (defprod    (defprod->defxdoc x parents base-pkg state))
      (deftagsum  (deftagsum->defxdoc x parents base-pkg state))
      (defflexsum (defflexsum->defxdoc x parents base-pkg state))
      (t (mv (raise "~x0: unknown typemacro" x.name) state)))))

(defun flextype->defxdoc (x parents state)
  ;; Returns (mv event state)
  (b* ((__function__ 'flextype->defxdoc)
       ((mv events state)
        ;; Can't use this because its otherwise case is just NIL.
        ;;(with-flextype-bindings x
        ;;  (flex*->defxdoc x parents state))
        (case (tag x)
          (:sum (flexsum->defxdoc x parents state))
          (:list (flexlist->defxdoc x parents state))
          (:alist (flexalist->defxdoc x parents state))
          (otherwise (mv (raise "Unexpected flex type: ~x0." (tag x))
                         state)))))
    (mv `(progn . ,events) state)))

(defun flextypes-collect-defxdoc (types parents)
  (if (atom types)
      nil
    (cons `(make-event (b* (((mv val state)
                             (flextype->defxdoc ',(car types) ',parents state)))
                         (value val)))
          (flextypes-collect-defxdoc (cdr types) parents))))

(defun remove-topic (name x)
  (declare (xargs :mode :program))
  (if (atom x)
      nil
    (if (equal (cdr (assoc :name (car x))) name)
        (cdr x)
      (cons (car x) (remove-topic name (cdr x))))))

(defun flextypes-final-xdoc-fn (x world)
  (b* (((flextypes x) x)
       (parents-look (assoc :parents x.kwd-alist))
       (short        (getarg :short nil x.kwd-alist))
       (long         (getarg :long nil x.kwd-alist))
       (parents      (or (cdr parents-look)
                         (xdoc::get-default-parents world)
                         '(acl2::undocumented)))
       ;; x.name may or may not agree with the names of any of the things
       ;; inside it.  For instance:
       ;;   (deftypes pseudo-termp
       ;;     (defprod pseudo-termp ...)
       ;;     (deflist pseudo-term-listp ...))
       ;; or
       ;;   (deftypes statements
       ;;     (defsum vl-stmt-p ...)
       ;;     (deflist vl-stmtlist-p ...))
       (topic (xdoc::find-topic x.name (xdoc::get-xdoc-table world)))
       (sub-short (and (not (equal (cdr (assoc :short topic)) ""))
                       (cdr (assoc :short topic))))
       (sub-long  (and (not (equal (cdr (assoc :long topic)) ""))
                       (cdr (assoc :long topic))))
       ((when (and short sub-short))
        (er hard? 'deftypes "Can't give a top-level :short when you are also ~
                   putting :short documentation on the interior ~x0." x.name))
       ((when (and long sub-long))
        (er hard? 'deftypes "Can't give a top-level :long when you are also ~
                   putting :long documentation on the interior ~x0." x.name))
       (short (or short sub-short))
       (long  (or long sub-long))
       (new-defxdoc `(defxdoc ,x.name :parents ,parents :short ,short :long ,long))
       ((unless topic)
        new-defxdoc))
    ;; There's existing sub-documentation, so remove it because we're going to
    ;; overwrite it and we don't want redundant xdoc warnings.
    `(progn
       (table xdoc::xdoc 'xdoc::doc
              (remove-topic ',x.name (xdoc::get-xdoc-table world)))
       ,new-defxdoc)))

(defmacro flextypes-final-xdoc (x)
  `(make-event (flextypes-final-xdoc-fn ',x (w state))))

(defun flextypes-defxdoc (x world)
  (b* (((flextypes x) x)
       (parents-look (assoc :parents x.kwd-alist))
       (mutually-recursive-p (consp (cdr x.types)))
       (parents      (or (cdr parents-look)
                         (xdoc::get-default-parents world)
                         '(acl2::undocumented)))
       (parents-for-each-type
        (if mutually-recursive-p
            (list x.name)
          parents)))
    (append (flextypes-collect-defxdoc x.types parents-for-each-type)
            `((flextypes-final-xdoc ,x)))))

;; ------------------ Ambient Theory Managment -----------------------
(defun find-fix-when-pred-thm-aux (fix pred fix-rules)
  (if (atom fix-rules)
      (let ((body `(implies (,pred x)
                            (equal (,fix x) x))))
        (mv nil `(local (make-event
                         '(:or (defthm ,(intern-in-package-of-symbol
                                         (cat "TMP-DEFTYPES-" (symbol-name fix) "-WHEN-" (symbol-name pred))
                                         'fty)
                                 ,body)
                           (value-triple
                            (er hard? 'deftypes
                                "To use ~x0/~x1 as a fixing function/predicate, we must ~
                       be able to prove the following: ~x2.  But this proof ~
                       failed! Please try to prove this rule yourself."
                                ',fix ',pred ',body)))))))
    (let ((rune (b* ((rule (car fix-rules))
                     (subclass (acl2::access acl2::rewrite-rule rule :subclass))
                     ((unless (eq subclass 'acl2::backchain)) nil)
                     (lhs (acl2::access acl2::rewrite-rule rule :lhs))
                     ((unless (symbolp (cadr lhs))) nil)
                     (var (cadr lhs))
                     (rhs (acl2::access acl2::rewrite-rule rule :rhs))
                     ((unless (eq rhs var)) nil)
                     (hyps (acl2::access acl2::rewrite-rule rule :hyps))
                     ((unless (and (consp hyps)
                                   (not (cdr hyps))
                                   (consp (car hyps))
                                   (eq pred (caar hyps))
                                   (eq var (cadr (car hyps)))))
                      nil)
                     (equiv (acl2::access acl2::rewrite-rule rule :equiv))
                     ((unless (eq equiv 'equal)) nil))
                  (acl2::access acl2::rewrite-rule rule :rune))))
      (if rune
          (mv t rune)
        (find-fix-when-pred-thm-aux fix pred (cdr fix-rules))))))

(defun find-pred-of-fix-thm-aux (fix pred pred-rules)
  (if (atom pred-rules)
      (let ((body `(,pred (,fix x))))
        (mv nil
            `(local (make-event
                     '(:or (defthm ,(intern-in-package-of-symbol
                                     (cat "TMP-DEFTYPES-" (symbol-name PRED) "-OF-" (symbol-name fix))
                                     'fty)
                             ,body)
                       (value-triple
                        (er hard? 'deftypes
                            "To use ~x0/~x1 as a fixing function/predicate, we must ~
                       be able to prove the following: ~x2.  But this proof ~
                       failed! Please try to prove this rule yourself."
                            ',fix ',pred ',body)))))))
    (let ((rune (b* ((rule (car pred-rules))
                     (subclass (acl2::access acl2::rewrite-rule rule :subclass))
                     ((unless (eq subclass 'acl2::abbreviation)) nil)
                     (lhs (acl2::access acl2::rewrite-rule rule :lhs))
                     ((unless (and (consp (cadr lhs))
                                   (eq fix (car (cadr lhs)))
                                   (symbolp (cadr (cadr lhs)))))
                      nil)
                     (rhs (acl2::access acl2::rewrite-rule rule :rhs))
                     ((unless (equal rhs ''t)) nil)
                     (hyps (acl2::access acl2::rewrite-rule rule :hyps))
                     ((unless (atom hyps))
                      nil)
                     (equiv (acl2::access acl2::rewrite-rule rule :equiv))
                     ((unless (member equiv '(equal iff))) nil))
                  (acl2::access acl2::rewrite-rule rule :rune))))
      (if rune
          (mv t rune)
        (find-pred-of-fix-thm-aux fix pred (cdr pred-rules))))))

(defun fix-rule-disablep (rule)
  ;; not including the fix-when-pred rule, which is enabled later
  (b* (((when (acl2::access acl2::rewrite-rule rule :hyps)) t)
       ((unless (eq (acl2::access acl2::rewrite-rule rule :subclass)
                    'acl2::abbreviation))
        t)
       (arg (cadr (acl2::access acl2::rewrite-rule rule :lhs)))
       ((unless (symbolp arg)) t)
       ((unless (eq (acl2::access acl2::rewrite-rule rule :rhs) arg)) t))
    nil))

(defun collect-fix-runes-to-disable (rules)
  (if (atom rules)
      nil
    (if (fix-rule-disablep (car rules))
        (cons (acl2::access acl2::rewrite-rule (car rules) :rune)
              (collect-fix-runes-to-disable (cdr rules)))
      (collect-fix-runes-to-disable (cdr rules)))))


(defun pred-rule-disablep (rule)
  ;; disable backchain rules, rules that target (pred x), i.e. where the
  ;; argument to pred doesn't have a function symbol, and rules that rewrite
  ;; pred to something other than t
  (b* (((unless (eq (acl2::access acl2::rewrite-rule rule :subclass)
                    'acl2::abbreviation))
        t)
       ((when (symbolp (cadr (acl2::access acl2::rewrite-rule rule :lhs)))) t)
       ((unless (equal (acl2::access acl2::rewrite-rule rule :rhs) ''t)) t))
    nil))

(defun collect-pred-runes-to-disable (rules)
  (if (atom rules)
      nil
    (if (pred-rule-disablep (car rules))
        (cons (acl2::access acl2::rewrite-rule (car rules) :rune)
              (collect-pred-runes-to-disable (cdr rules)))
      (collect-pred-runes-to-disable (cdr rules)))))

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

(defun flexlist-collect-fix/pred-pairs (list)
  (b* (((flexlist list) list))
    (and list.elt-type list.elt-fix
         (list (cons list.elt-fix list.elt-type)))))

(defun flexalist-collect-fix/pred-pairs (alist)
  (b* (((flexalist alist) alist))
    (append (and alist.key-type alist.key-fix
                 (list (cons alist.key-fix alist.key-type)))
            (and alist.val-type alist.val-fix
                 (list (cons alist.val-fix alist.val-type))))))

(defun flextypes-collect-fix/pred-pairs-aux (types)
  (if (atom types)
      nil
    (append (with-flextype-bindings (x (car types))
              (flex*-collect-fix/pred-pairs x))
            (flextypes-collect-fix/pred-pairs-aux (cdr types)))))

(defun flextypes-collect-fix/pred-pairs (types)
  (remove-duplicates-equal (flextypes-collect-fix/pred-pairs-aux types)))

(defun collect-disable-runes-fixes (x world)
  (if (atom x)
      nil
    (append (collect-fix-runes-to-disable
             (getprop (car x) 'acl2::lemmas nil 'acl2::current-acl2-world world))
            (collect-disable-runes-fixes (cdr x) world))))

(defun collect-disable-runes-preds (x world)
  (if (atom x)
      nil
    (append (collect-pred-runes-to-disable
             (getprop (car x) 'acl2::lemmas nil 'acl2::current-acl2-world world))
            (collect-disable-runes-preds (cdr x) world))))

(defun collect-fix/pred-enable-rules (pairs world)
  ;; returns (mv runes-to-enable thms-to-admit)
  (if (atom pairs)
      (mv nil nil)
    (b* (((cons fix pred) (car pairs))
         (fix (acl2::deref-macro-name fix (acl2::macro-aliases world)))
         (pred (acl2::deref-macro-name pred (acl2::macro-aliases world)))
         (fix-exists (not (eq :none (getprop fix 'acl2::formals :none 'acl2::current-acl2-world world))))
         (pred-exists (not (eq :none (getprop pred 'acl2::formals :none 'acl2::current-acl2-world world))))
         ((unless (and fix-exists pred-exists))
          ;; These pairs include types that we are about to define, so if the
          ;; function isn't yet defined, don't complain.  But if one is defined
          ;; but the other isn't, it's strange.
          (and (or fix-exists pred-exists)
               (cw "WARNING: ~x0 is defined but ~x1 is not"
                   (if fix-exists fix pred) (if fix-exists pred fix)))
          (collect-fix/pred-enable-rules (cdr pairs) world))
         (fix-rules (getprop fix 'acl2::lemmas nil 'acl2::current-acl2-world world))
         (pred-rules (getprop pred 'acl2::lemmas nil 'acl2::current-acl2-world world))
         ((mv fix-rule-exists fix-rule) (find-fix-when-pred-thm-aux fix pred fix-rules))
         ((mv pred-rule-exists pred-rule) (find-pred-of-fix-thm-aux fix pred pred-rules))
         ((mv enables thms)
          (collect-fix/pred-enable-rules (cdr pairs) world))
         ((mv enables thms)
          (if fix-rule-exists
              (mv (cons fix-rule enables) thms)
            (mv enables (cons fix-rule thms))))
         ((mv enables thms)
          (if pred-rule-exists
              (mv (cons pred-rule enables) thms)
            (mv enables (cons pred-rule thms)))))
      (mv enables thms))))

;; ------------------ Deftypes-events -----------------------
;; --- Flextype-collect-events ---
(defun flextypelist-append-events (kwd types)
  (if (atom types)
      nil
    (append (with-flextype-bindings (x (car types))
              (cdr (assoc kwd x.kwd-alist)))
            (flextypelist-append-events kwd (cdr types)))))

(defun flextype-collect-events (kwd kwd-alist types)
  (append (getarg kwd nil kwd-alist)
          (flextypelist-append-events kwd types)))

(defun deftypes-events (x world)
  (b* (((flextypes x) x)
       (fix/pred-pairs (flextypes-collect-fix/pred-pairs x.types))
       (disable-rules (append (collect-disable-runes-fixes (strip-cars fix/pred-pairs) world)
                              (collect-disable-runes-preds (strip-cdrs fix/pred-pairs) world)))
       ((mv enable-rules temp-thms) (collect-fix/pred-enable-rules fix/pred-pairs world)))
    `(with-output :off (prove event observation)
       :summary (acl2::form time)
       (encapsulate nil       ;; was: defsection ,x.name
         (with-output :summary (acl2::form)
           (progn
             ,@(flextype-collect-events :prepwork x.kwd-alist x.types)
             (set-bogus-defun-hints-ok t)
             (set-ignore-ok t)
             (set-irrelevant-formals-ok t)
             (local (deftheory deftypes-orig-theory (current-theory :here)))
             (progn . ,temp-thms)
             (local (in-theory (disable . ,disable-rules)))
             (local (in-theory (enable . ,enable-rules)))

             ;; Don't try to automatically define equivalences while we're setting up types
             (local (std::remove-default-post-define-hook :fix))

             ,@(flextypes-predicate-def x)

             ,@(flextype-collect-events :post-pred-events x.kwd-alist x.types)

             ,@(flextype-def-sum-kinds x.types)

             ,@(flextypes-fix-def x)

             ,@(flextype-collect-events :post-fix-events x.kwd-alist x.types)

             ,@(flextypes-sum-accessor/constructors x.types x.types)

             (local (in-theory (disable . ,(flextypes-fns x.types))))

             ,@(flextypes-count x)

             (local (in-theory (enable deftypes-orig-theory)))

             ,@(flextype-collect-events :post-events x.kwd-alist x.types)
             
             ,@(flextype-collect-events :///-events x.kwd-alist x.types)

             (table flextypes-table ',x.name ',x)

             . ,(flextypes-defxdoc x world)))))))

;; ------------------ Interface Macros -----------------------
(defun deftypes-fn (args wrld)
  (b* ((x (parse-flextypes args wrld)))
    (deftypes-events x wrld)))

(defmacro deftypes (&rest args)
  `(make-event (deftypes-fn ',args (w state))))

(defun defflexsum-fn (whole wrld)
  (b* ((our-fixtypes (list (flextype-form->fixtype whole)))
       (fixtype-al (append our-fixtypes
                           (get-fixtypes-alist wrld)))
       (x (parse-flexsum (cdr whole) nil our-fixtypes fixtype-al))
       (x (if (or (flexsum->recp x)
                  (member :count (cdr whole)))
              x
            ;; don't make a count if it's not recursive
            (change-flexsum x :count nil)))
       ((flexsum x) x)
       (flextypes (make-flextypes :name x.name
                                  :types (list x)
                                  :no-count (not x.count)
                                  :kwd-alist nil
                                  :recp x.recp)))
    (deftypes-events flextypes wrld)))

(defmacro defflexsum (&whole form &rest args)
  (declare (ignore args))
  `(make-event (defflexsum-fn ',form (w state))))

(defun deflist-fn (whole wrld)
  (b* ((our-fixtypes (list (flextype-form->fixtype whole)))
       (fixtype-al (append our-fixtypes
                           (get-fixtypes-alist wrld)))
       (x (parse-flexlist (cdr whole) nil our-fixtypes fixtype-al))
       (x (if (member :count (cdr whole))
              x
            (change-flexlist x :count nil)))
       ((flexlist x) x)
       (flextypes (make-flextypes :name x.name
                                  :types (list x)
                                  :no-count (not x.count)
                                  :kwd-alist nil
                                  :recp x.recp)))
    (deftypes-events flextypes wrld)))

(defmacro deflist (&whole form &rest args)
  (declare (ignore args))
  `(make-event (deflist-fn ',form (w state))))

(defun defalist-fn (whole wrld)
  (b* ((our-fixtypes (list (flextype-form->fixtype whole)))
       (fixtype-al (append our-fixtypes
                           (get-fixtypes-alist wrld)))
       (x (parse-flexalist (cdr whole) nil our-fixtypes fixtype-al))
       (x (if (member :count (cdr whole))
              x
            (change-flexalist x :count nil)))
       ((flexalist x) x)
       (flextypes (make-flextypes :name x.name
                                  :types (list x)
                                  :no-count (not x.count)
                                  :kwd-alist nil
                                  :recp x.recp)))
    (deftypes-events flextypes wrld)))

(defmacro defalist (&whole form &rest args)
  (declare (ignore args))
  `(make-event (defalist-fn ',form (w state))))

(defun deftagsum-fn (whole wrld)
  (b* ((fixtype (flextype-form->fixtype whole))
       (fixtype-al (cons fixtype
                         (get-fixtypes-alist wrld)))
       (x (parse-tagsum (cdr whole) nil (list fixtype) fixtype-al))
       (x (if (or (flexsum->recp x)
                  (member :count (cdr whole)))
              x
            ;; don't make a count if it's not recursive
            (change-flexsum x :count nil)))
       ((flexsum x) x)
       (flextypes (make-flextypes :name x.name
                                  :types (list x)
                                  :no-count (not x.count)
                                  :kwd-alist nil
                                  :recp x.recp)))
    (deftypes-events flextypes wrld)))

(defmacro deftagsum (&whole form &rest args)
  (declare (ignore args))
  `(make-event (deftagsum-fn ',form (w state))))

(defun defprod-fn (whole wrld)
  (b* ((fixtype (flextype-form->fixtype whole))
       (fixtype-al (cons fixtype
                         (get-fixtypes-alist wrld)))
       (x (parse-defprod (cdr whole) nil (list fixtype) fixtype-al))
       (x (if (member :count (cdr whole))
              x
            (change-flexsum x :count nil))) ;; no count for a single product
       ((flexsum x) x)
       (flextypes (make-flextypes :name x.name
                                  :types (list x)

                                  :no-count (not x.count)
                                  :kwd-alist '((:prepwork . ((local (in-theory (enable equal-of-strip-cars))))))
                                  :recp x.recp)))
    (deftypes-events flextypes wrld)))

(defmacro defprod (&whole form &rest args)
  (declare (ignore args))
  `(make-event (defprod-fn ',form (w state))))


;; ------------------ Documentation -----------------------
(defxdoc deftypes
  :parents (fty)
  :short "Generate mutually recursive types with equivalence relations and fixing functions."
  :long "<p>@('Deftypes') generates mutually-recursive types.  We'll begin with an example.</p>

@({
 ;; preparation: associate fixing functions/equivalence relations with component types
 ;; Note: this is done for most basic types in the book centaur/fty/basetyptes.lisp.
 (deffixtype integer :pred integerp :fix ifix :equiv int-equiv :define t)
 (deffixtype symbol :pred symbolp :fix symbol-fix :equiv sym-equiv :define t)

 (deftypes intterm
   (defflexsum intterm
     (:num :cond (atom x)
      :fields ((val :type integerp :acc-body x))
      :ctor-body val)
     (:call
      :fields ((fn :type symbol :acc-body (car x))
               (args :type inttermlist :acc-body (cdr x)))
      :ctor-body (cons fn args)))
   (deflist inttermlist
     :elt-type intterm))
})

<p>This generates recognizers and fixing functions for two new types:</p>
<ul>
<li>intterm, which is either a \"num\" consisting of a single integer or a
\"call\" consisting of a symbol consed onto an inttermlist,</li>
<li>inttermlist, which is a list of intterms.</li>
</ul>

<p>The @('deftypes') form just bundles together two other forms -- a @(see
defflexsum) and a @(see deflist).  These two forms would be admissible by
themselves, except that the types they are defining are mutually recursive, and
therefore so are their recognizer predicates and fixing functions.</p>

<p>The syntax and behavior of individual type generators is documented further
in their own topics.  So far, the supported type generators are:</p>
<ul>
<li>@(see deflist): a list of elements of a particular type</li>
<li>@(see defprod): a product (AKA record, aggregate, struct) type</li>
<li>@(see defalist): an alist mapping keys of some type to values of some type</li>
<li>@(see deftagsum): a sum-of-products (AKA tagged union) type</li>
<li>@(see defflexsum): a very flexible (and not as automated) sum-of-products
type used to implement @(see defprod) and @(see deftagsum).</li>
</ul>

<p>@('Deftypes') and its component type generators are intended to
implement the type discipline described in the @(see fty) topic.  In
particular, this means:</p>
<ul>
<li>the type predicates generated by any these events each have an associated
fixing function and equivalence relation, and is association is recorded using
a @(see deffixtype) event</li>
<li>accessors and constructors of the sum and product types unconditionally
return values of the appropriate type</li>
<li>accessors and constructors have equality congruences based on the types of
their arguments.</li>
</ul>

<p>To support these nice properties, all the component types (the fields of
products, elements of lists, keys and values of alists) are required to also
have an associated fixing function and equivalence relation, either produced by
a @('deftypes') compatible type generator or recorded by a @(see deffixtype)
event.  (They may also be untyped.)  The \"preparation\" forms in the example
above show how this can be done.  Also see @(see basetypes) for some base types
with fixing functions.</p>")

(defxdoc deflist
  :parents (fty deftypes)
  :short "Define a list type with a fixing function, supported by @(see deftypes)"
  :long "<p>@('Deflist') provides a recognizer predicate, fixing function, and
a few theorems defining a list of elements of a certain type.</p>

<p>@('Deflist') is compatible with @(see deftypes), and can be
mutually-recursive with other @('deftypes') compatible type generators.  As
with all @(see deftypes)-compatible type generators, its element type must
either be one produced by a compatible type generator or else have an
associated fixing function given by @(see deffixtype).  See @(see basetypes) for
some base types with fixing functions.</p>

<p>The syntax of deflist is:</p>
@({
  (deflist foolist
    :elt-type foo      ;; required, must have a known fixing function
    :parents (...)     ;; xdoc
    :short \"...\"       ;; xdoc
    :long \"...\"        ;; xdoc
    :measure (+ 1 (* 2 (acl2-count x)))
                       ;; default: (acl2-count x)
    :xvar x            ;; default: x, or find x symbol in measure
    :prepwork          ;; admit these events before starting
    :pred foolistp     ;; default: foolist-p
    :fix foolistfix    ;; default: foolist-fix
    :equiv foolist-=   ;; default: foolist-equiv
    :count foolistcnt  ;; default: foolist-count
                       ;; (may be nil; skipped unless mutually recursive)
    :no-count t        ;; default: nil, same as :count nil
    :true-listp t      ;; default: nil, require nil final cdr
  )
 })

<p>Only the name and the @(':elt-type') argument is required.</p>

<p>@('Deflist') does not attempt to be as comprehensive in the theorems it
proves as is @(see std::deflist).  However, it is compatible with
@(see std::deflist) and @(see std::defprojection) using their
@(':already-definedp') arguments.  For example: </p>

@({
  (fty::deflist symlist :elt-type symbol)

  (std::deflist symlist-p (x)
    (symbolp x)
    :true-listp t
    :already-definedp t)

  (std::defprojection symlist-fix (x)
    (symbol-fix x)
    :guard (symlist-p x)
    :already-definedp t)

 })")

(defxdoc defalist
  :parents (fty deftypes)
  :short "Define an alist type with a fixing function, supported by @(see deftypes)"
  :long "<p>@('Defalist') provides a recognizer predicate, fixing function, and
a few theorems defining an alist with keys of some type mapping to values of some type.</p>

<p>@('Defalist') is compatible with @(see deftypes), and can be
mutually-recursive with other @('deftypes') compatible type generators.  As
with all @(see deftypes)-compatible type generators, its key and value types
must either be one produced by a compatible type generator or else have an
associated fixing function given by @(see deffixtype).  (They may also be
untyped.)  See @(see basetypes) for some base types with fixing
functions.</p>

<p>The syntax of defalist is:</p>
@({
  (defalist fooalist
    :key-type symbol
    :val-type foo
    :parents (...)     ;; xdoc
    :short \"...\"       ;; xdoc
    :long \"...\"        ;; xdoc
    :measure (+ 1 (* 2 (acl2-count x)))
                       ;; default: (acl2-count x)
    :xvar x            ;; default: x, or find x symbol in measure
    :prepwork          ;; admit these events before starting
    :pred fooalistp     ;; default: fooalist-p
    :fix fooalistfix    ;; default: fooalist-fix
    :equiv fooalist-=   ;; default: fooalist-equiv
    :count fooalistcnt  ;; default: fooalist-count
                       ;; (may be nil; skipped unless mutually recursive)
    :no-count t        ;; default: nil, same as :count nil
    :true-listp t      ;; default: nil, require nil final cdr
  )
 })

<p>The keyword arguments are all optional, although it doesn't make much sense
to define an alist with neither a key-type nor value-type.</p>

<p>@('Defalist') does not attempt to be as comprehensive in the theorems it
proves as is @(see std::defalist).  However, it is compatible with
@(see std::defalist) using its @(':already-definedp') and @(':true-listp')
arguments.  For example: </p>

@({
  (fty::defalist symnatalist :key-type symbol :val-type nat)

  (std::defalist symnatalist-p (x)
    :key (symbolp x) :val (natp x)
    :true-listp t
    :already-definedp t)

 })")

(defxdoc defprod
  :parents (fty deftypes)
  :short "Define a product type with recognizer, constructor, accessors, and a fixing function"
  :long "<p>@('Defprod') produces a record type, similar in spirit to @(see
std::defaggregate), @(see acl2::defrec), and so on.</p>

<p>@('Defprod') is compatible with @(see deftypes), and can be
mutually-recursive with other @('deftypes') compatible type generators.  As
with all @(see deftypes)-compatible type generators, its field types must each
either be one produced by a compatible type generator or else have an
associated fixing function given by @(see deffixtype).  (Fields can also be
untyped.)  See @(see basetypes) for some base types with fixing
functions.</p>

<p>The syntax of defprod is:</p>
@({
 (defprod prodname
    (list-of-fields)
    keyword-options)
 })

<p>The fields are @(see std::extended-formals), except that the guard must be
either simply a predicate or the call of a unary predicate on the field name.
Acceptable keyword arguments for each field are:</p>
<ul>
<li>@(':default'): default value of the field in its constructor macro</li>
<li>@(':rule-classes'): rule-classes for the return type theorem of the accessor.</li>
</ul>

<h4>Example</h4>

@({
 (defprod sandwich
   ((bread symbolp :default 'sourdough)
    (coldcut meatp)
    (spread condimentp))
 })

<p>This produces the following functions and macros:</p>

<ul>
<li>recognizer @('sandwich-p')</li>
<li>fixing function @('sandwich-fix')</li>
<li>equivalence relation @('sandwich-equiv')</li>
<li>constructor @('(sandwich bread coldcut spread)')</li>
<li>accessors @('sandwich->bread'), @('sandwich->coldcut'), and @('sandwich->field')</li>
<li>constructor macro @('(make-sandwich :bread bread ...)'), which simply
expands to a constructor call but uses the given defaults</li>
<li>changer macro @('(change-sandwich x :bread bread ...)')</li>
<li>@(see B*) binder @('sandwich') (as in @(see std::defaggregate)).</li>
</ul>

<h4>Options</h4>
<p>Keyword options for @('defprod') include:</p>
<ul>

<li>@(':pred'), @(':fix'), @(':equiv'), @(':count'): override default function
names, which are (respectively) @('name-p'), @('name-fix'), @('name-equiv'),
and @('name-count').  As a special case, @(':count') may be nil, meaning no
count function is produced.  (A count function is only produced when this is
mutually-recursive with other type generators.)</li>

<li>@(':parents'), @(':short'), @(':long'): add xdoc about the type.  (Note:
xdoc support is half-baked; e.g. documentation strings for fields are allowed
but not yet used.</li>

<li>@(':layout'): must be one of @(':tree'), @(':list'), or @(':alist'),
defaulting to @(':alist').  This determines how the fields are laid out in the
object; e.g., a 5-element product will be laid out as follows for each case:
@({
  `((,a . ,b) . (,c . (,d . e)))                   ;; :tree
  `(,a ,b ,c ,d ,e)                                ;; :list
  `((a . ,a) (b . ,b) (c . ,c) (d . ,d) (e . ,e))  ;; :alist
 })
</li>

<li>@(':tag'): defaults to NIL, meaning it isn't present; otherwise it must be
a keyword symbol, which is consed onto every occurrence of the object.</li>

<li>@(':measure'): Only necessary in the mutually-recursive case, but probably
necessary then.  The default measure is @('(acl2-count x)'), but this is
unlikely to work in the mutually-recursive case because of the possibility that
@('x') could be (say) an atom, in which case the @('acl2-count') of @('x') will
be no greater than the @('acl2-count') of a field.  Often something like
@('(two-nats-measure (acl2-count x) 5)') is a good measure for the product,
where the other mutually-recursive types have a similar measure with smaller
second component.</li>

<li>@(':hons'), NIL by default; when T, the constructor is defined using @(see
hons) rather than cons.</li>

<li>@(':inline') is @('(:acc :fix)') by default, which causes the accessors and
fixing function (which for execution purposes is just the identity) to be
inlined.  The list may also contain @(':xtor'), which causes the constructor to
be inlined as well; @(':all') (not in a list) is also possible.</li>

<li>@(':require') adds a dependent type requirement; see the section on this feature below.</li>
</ul>

<h4>Experimental Dependent Type Option</h4>

<p>An additional top-level keyword, @(':require'), can add a requirement that
the fields satisfy some relation.  Using this option requires that one or more
fields be given a @(':reqfix') option; it must be a theorem that applying the
regular fixing functions followed by the @(':reqfix') of each field
independently yields fields that satisfy the requirement.  (It should also be
the case that applying the reqfixes to fields already satisfying the
requirement leaves them unchanged.) For example:</p>

@({
 (defprod sizednum
   ((size natp)
    (bits natp :reqfix (loghead size bits)))
   :require (unsigned-byte-p size bits))
 })

<p>If there is more than one field with a @(':reqfix') option, these reqfixes
are applied to each field independently, after applying all of their types' fixing functions.
For example, for the following to succeed:</p>

@({
 (defprod foo
   ((a atype :reqfix (afix a b c))
    (b btype :reqfix (bfix a b c))
    (c       :reqfix (cfix a b c)))
   :require (foo-req a b c))
 })

<p>the following must be a theorem (assuming @('afix') and @('bfix') are the
fixing functions for @('atype') and @('btype'), respectively):</p>

@({
  (let ((a (afix a))
        (b (bfix b)))
    (let ((a (afix a b c))
          (b (bfix a b c))
          (c (cfix a b c)))
      (foo-req a b c)))
 })

<p>Notice the LET, rather than LET*, binding the fields to their reqfixes.  It
would NOT be sufficient for this to be true with a LET*.</p>
")

(defxdoc deftagsum
  :parents (fty deftypes)
  :short "Define a (possibly recursive) tagged union/sum of products type."

  :long "<p>@('Deftagsum') produces a tagged union type consisting of several
product types, each with a tag to distinguish them.  It is similar in spirit to
ML or Haskell's recursive data types, although without the dependent-type
features.</p>

<p>@('Deftagsum') is compatible with @(see deftypes), and can be
mutually-recursive with other @('deftypes') compatible type generators.  As
with all @(see deftypes)-compatible type generators, the types of the fields of
its products must each either be one produced by a compatible type generator or
else have an associated fixing function given by @(see deffixtype).  (Fields
can also be untyped.)  See @(see basetypes) for some base types with fixing
functions.</p>

<h3>Example</h3>

<p>Note: It may be helpful to be familiar with @(see defprod).</p>

@({
  (deftagsum arithtm
    (:num ((val integerp)))
    (:plus ((left arithtm-p)
            (right arithtm-p)))
    (:minus ((arg arithtm-p))))
 })

<p>This defines the following functions and macros:</p>

<ul>
<li>Recognizer @('arithtm-p')</li>
<li>Fixing function @('arithtm-fix')</li>
<li>Equivalence relation @('arithtm-equiv')</li>
<li>@('arithtm-kind'), which returns either @(':num'), @(':plus'), or
@(':minus) to distinguish the different kinds of arithtm objects</li>
<li>Constructors @('arithtm-num'), @('arithtm-plus'), @('arithtm-minus')</li>
<li>Accessors @('arithtm-num->val'), @('arithtm-plus->left'),
@('arithtm-plus->right'), and @('arithtm-minus->arg')</li>
<li>Constructor macros @('make-aritherm-num'), @('make-arithtm-plus'),
@('make-arithtm-minus')</li>
<li>Changer macros @('change-arithtm-num'), @('change-arithtm-plus'),
@('change-arithtm-minus')</li>
<li>@(see B*) binders @('arithtm-num'), @('arithtm-plus'),
@('arithtm-minus')</li>
<li>@('arithtm-case'), a macro that combines case splitting and accessor binding.</li>
</ul>



<p>Note: The individual products in a @('deftagsum') type are not themselves
types: they have no recognizer or fixing function of their own.  The guard for
accessors is the sum type and the kind, e.g., for @('arithtm-plus->right'),</p>
@({
 (and (arithtm-p x) (equal (arithtm-kind x) :plus))
 })

<h4>Using Tagsum Objects</h4>

<p>The following example shows how to use an arithtm object.  We define an
evaluator function that computes the value of an arithtm and a transformation
that doubles every leaf in an arithtm, and prove that the doubling function
doubles the value according to the evaluator.  The doubling function also shows
how the arithtm-case macro is used.  Note that the return type theorems and
the theorem about the evaluation of arithtm-double are all hypothesis-free --
a benefit of following a consistent type-fixing convention.</p>

@({
  (define arithtm-eval ((x arithtm-p))
    :returns (val integerp :rule-classes :type-prescription)
    :measure (arithtm-count x)
    :verify-guards nil
    (case (arithtm-kind x)
      (:num (arithtm-num->val x))
      (:plus (+ (arithtm-eval (arithtm-plus->left x))
                (arithtm-eval (arithtm-plus->right x))))
      (:minus (- (arithtm-eval (arithtm-minus->arg x)))))
    ///
    (verify-guards arithtm-eval))


  (define arithtm-double ((x arithtm-p))
    :returns (xx arithtm-p)
    :measure (arithtm-count x)
    :verify-guards nil
    (arithtm-case x
     :num (arithtm-num (* 2 x.val))
     :plus (arithtm-plus (arithtm-double x.left)
                         (arithtm-double x.right))
     :minus (arithtm-minus (arithtm-double x.arg)))
    ///
    (verify-guards arithtm-double)

    (local (include-book \"arithmetic/top-with-meta\" :dir :system))

    (defthm arithtm-eval-of-double
      (equal (arithtm-eval (arithtm-double x))
             (* 2 (arithtm-eval x)))
      :hints((\"Goal\" :in-theory (enable arithtm-eval)))))
 })

<h3>Deftagsum Usage and Options</h3>

<p>A @('deftagsum') form consists of the type name, a list of product
specifiers, and some optional keyword arguments.</p>

<h4>Product specifiers</h4>

<p>A product specifier consists of a tag (a keyword symbol), a list of fields
given as @(see std::extended-formals), and some optional keyword arguments.
The possible keyword arguments are:</p>

<ul>
<li>@(':layout'), one of @(':tree'), @(':list'), or @(':alist'), determining
the arrangement of fields within the product object (as in @(see defprod)),</li>
<li>@(':inline), determining whether the constructor and accessors are inlined
or not.  This may be @(':all') or a subset of @('(:xtor :acc)').  Defaults to
@('(:acc)') if not overridden.</li>
<li>@(':hons'), NIL by default, determining whether objects are constructed
with @(see hons).</li>
<li>@(':base-name'), overrides the name of the constructor and the base name
used to generate accessors.</li>
<li>@(':require') adds a dependent type requirement; see the section on this
feature in @(see defprod).</li>
</ul>

<h4>Tagsum Options</h4>

<p>The following keyword options are recognized at the top level of a
@('deftagsum') form (as opposed to inside the individual product forms):</p>
<ul>

<li>@(':pred'), @(':fix'), @(':equiv'), @(':kind'), @(':count'): override
default function names.  @(':count') may also be set to NIL, to turn of
generation of the count function.</li>

<li>@(':parents'), @(':short'), @(':long'): add xdoc about the type.  (Note:
xdoc support is half-baked; e.g. documentation strings for fields are allowed
but not yet used.</li>

<li>@(':measure'): override the measures used to admit the recognizer, fixing
function, and count function; the default is @('(acl2-count x)').</li>

<li>@(':prepwork'): events submitted before</li>

<li>@(':inline'): sets default for inlining of products and determines whether
the kind and fixing functions are inlined.  This may be @(':all') or a subset
of @('(:kind :fix :acc :xtor)'), defaulting to @('(:kind :fix :acc)').</li>

<li>@(':layout'): sets default layout for products</li>

<li>@(':base-case-override'): Override which product is the base case.  This
may affect termination of the fixing function; see below.</li>

</ul>

<h3>Dealing with Base Cases</h3>

<p>Consider the following type definition:</p>

@({
  (deftypes fntree
    (deftagsum fntree
      (:pair ((left fntree-p) (right fntree-p)))
      (:call ((fn symbol) (args fntreelist-p))))
    (deflist fntreelist-p :elt-type fntree))
 })

<p>As is, deftypes will fail to admit this event, saying:</p>

<blockquote>
We couldn't find a base case for tagsum FNTREE, so we don't know what its
fixing function should return when the input is an atom.  To override this, add
keyword arg :base-case-override [product], where [product] is one of your
product keywords, and provide a measure that will allow the fixing function to
terminate.
</blockquote>

<p>What is the problem?  As the text suggests, the problem lies in what we
should do when given an atom as input to the fixing function.  With the default
measure of @('(acl2-count x)'), we're not allowed to recur on, say, @('NIL'),
because its acl2-count is already 0.  This is fine as long as we can pick a
product type that has no recursive components, but in this case, the @(':pair')
and @(':call') product both do.  However, the @(':call') product could have an
empty list as its arguments, and this seems like a reasonable thing to use as
the fix of an atom.  To give @('deftagsum') the hint to do this, we need to
tell it which product to fix an atom to, and what measure to use.  The
following modification of the above form works:</p>

@({
  (deftypes fntree
    (deftagsum fntree
      (:pair ((left fntree-p) (right fntree-p)))
      (:call ((fn symbol) (arg fntreelist-p)))
      :base-case-override :call
      :measure (two-nats-measure (acl2-count x) 1))
    (deflist fntreelist-p :elt-type fntree
      :measure (two-nats-measure (acl2-count x) 0)))
 }) ")

(defxdoc defflexsum
  :parents (fty deftypes)
  :short "Define a (possibly recursive) sum of products type."
  :long "
<h3>Caveat</h3>

<p>@('Defflexsum') is not very user-friendly or automatic; it is easy to create
instances that fail in incomprehensible ways.  It is used as a backend to
define the @(see deftagsum) and @(see defprod) type generators, which are easier to
use.</p>

<h4>Example</h4>

<p>This is essentially the same as the example in @(see deftagsum).  Logically,
the way these types work are very similar; only the representation is
different.</p>
@({
  (defflexsum arithterm
    (:num :cond (atom x)
     :fields ((val :type integerp :acc-body x))
     :ctor-body val)
    (:plus
     :cond (eq (car x) '+)
     :shape (and (true-listp x) (eql (len x) 3))
     :fields ((left :type arithterm :acc-body (cadr x))
              (right :type arithterm :acc-body (caddr x)))
     :ctor-body (list '+ left right))
    (:minus
     :shape (and (eq (car x) '-)
                   (true-listp x)
                   (eql (len x) 2))
     :fields ((arg :type arithterm :acc-body (cadr x)))
     :ctor-body (list '- arg)))

  (define arithterm-eval ((x arithterm-p))
    :returns (xval integerp :rule-classes :type-prescription)
    :measure (arithterm-count x)
    (case (arithterm-kind x)
      (:num (arithterm-num->val x))
      (:plus (+ (arithterm-eval (arithterm-plus->left x))
                (arithterm-eval (arithterm-plus->right x))))
      (t (- (arithterm-eval (arithterm-minus->arg x)))))
    ///
    (deffixequiv arithterm-eval))

  (define arithterm-double ((x arithterm-p))
    :verify-guards nil ;; requires return type theorem first
    :returns (xx arithterm-p)
    :measure (arithterm-count x)
    (arithterm-case x
      :num (arithterm-num (* 2 x.val))
      :plus (arithterm-plus (arithterm-double x.left)
                            (arithterm-double x.right))
      :minus (arithterm-minus (arithterm-double x.arg)))
    ///
    (verify-guards arithterm-double)

    (deffixequiv arithterm-double)

    (local (include-book \"arithmetic/top-with-meta\" :dir :system))

    (defthm arithterm-double-correct
      (equal (arithterm-eval (arithterm-double x))
             (* 2 (arithterm-eval x)))
      :hints((\"Goal\" :in-theory (enable arithterm-eval)))))
 })

<p>@('Mbe') allows the function to logically apply fixing functions to its
arguments without a performance penalty when running with guards checked.</p>

<h3>More on the above Caveat</h3>

<p>@('defflexsum') is less automatic than most other type-defining utilities.
It requires certain information to be provided by the user that must then be
proved to be self-consistent.  For example, the @(':ctor-body') argument in a
product spec determines how that product is constructed, and the @(':acc-body')
argument to a product field spec determines how that field is accessed.  These
could easily be inconsistent, or the @(':ctor-body') could produce an object
that is not recognized as that product.  If either of these is the case, some
proof within the @('defflexsum') event will fail and it will be up to the user
to figure out what that proof was and why it failed.</p>


<h3>Syntax and Options</h3>

<h4>@('Defflexsum') top-level arguments</h4>

<p>@('Defflexsum') takes the following keyword arguments, in addition to a list
of products, which are described further below.</p>

<ul>

<li>@(':pred'), @(':fix'), @(':equiv'), @(':kind'), @(':case'), and @(':count')
override the default names for the various generated functions (and case
macro).  If any of these is not provided, a default name is used instead.  If
@(':kind nil') is provided, then no @('-kind') function is generated and
instead the products are distinguished by their bare @(':cond') fields.  If
@(':count nil') is provided, then no count function is defined for this
type.</li>

<li>@(':xvar') sets the variable name used to represent the SUM object.  By
default, we look for a symbol whose name is \"X\" that occurs in the product
declarations.</li>

<li>@(':measure') provides the measure for the predicate, fixing function, and
count function.  It defaults to @('(acl2-count x)'), which is usually
appropriate for stand-alone products, but sometimes a special measure must be
used, especially when @('defflexsum') is used inside a mutually-recursive
@('deftypes') form.</li>

<li>@(':prepwork') is a list of events to be submitted at the beginning of the
process; usually these are local lemmas needed for the various proofs.</li>

<li>@(':parents'), @(':short'), and @(':long') provide xdoc for the type</li>

<li>@(':inline'): sets default for inlining of products and determines whether
the kind and fixing functions are inlined.  This may be @(':all') or a subset
of @('(:kind :fix :acc :xtor)'), defaulting to @('(:kind :fix :acc)').</li>

</ul>

<h4>Products</h4>

<p>Each product starts with a keyword naming its kind; this is the symbol that
the SUM kind function returns on an object of that product type.  The rest of
the form is a list of keyword arguments:</p>

<ul>

<li>@(':cond') describes how to tell whether an object is of this product type.
To determine the kind of an SUM object, the SUM kind function checks each of
the product conditions in turn, returning the name of the first matching
condition.  So the condition for a given product assumes the negations of the
conditions of the previous listed products.  The @(':cond') field defaults to
@('t'), so typically it can be left off the last product type.</li>

<li>@(':shape') adds well-formedness requirements for a product.  One purpose
these may serve is to make well-formed objects canonical: it must be a theorem
that the fixing function applied to a well-formed object is the same object.
So if a product is (e.g.) a tuple represented as a list, and the constructor
creates it as a true-list, then there should be a requirement that the object
be a true-list of the appropriate length; otherwise, an object that had a
non-nil final cdr would be recognized as well-formed, but fix to a different
value.</li>

<li>@(':fields') list the fields of the product; these are described further
below.</li>

<li>@(':ctor-body') describes how to make a product object from the fields.
This must be consistent with the field accessor bodies (described below) and
with the @(':cond') and @(':shape') fields of this product and the previous
ones (i.e., it can't produce something that could be mistaken for one of the
previous products listed).  The actual constructor function will have fixing
functions added; these should not be present in the @(':ctor-body')
argument.</li>

<li>@(':type-name') overrides the type-name, which by default is
@('[SUMNAME]-[KIND]'), e.g. @('arithterm-plus') from the example above.  This
is used as a base for generating the field accessor names.</li>

<li>@(':ctor-name') overrides the name of the product constructor function,
which by default is the type-name.</li>

<li>@(':inline), determining whether the constructor and accessors are inlined
or not.  This may be @(':all') or a subset of @('(:xtor :acc)').  Defaults to
@('(:acc)') if not overridden.</li>

<li>@(':require') adds a dependent type requirement; see the section on this
feature in @(see defprod).</li>

</ul>

<h4>Product Fields</h4>

<p>Each product field is a name followed by a keyword list, in which the
following keywords are allowed:</p>
<ul>
<li>@(':acc-body') must be present: a term showing how to fetch the field from
the object.</li>
<li>@(':acc-name') overrides the accessor name</li>
<li>@(':type'), the type (fixtype name or predicate) of the field; may be empty
for an untyped field</li>
<li>@(':default'), the default value of the field in the constructor macro</li>
<li>@(':doc') will eventually generate xdoc, but is currently ignored</li>
<li>@(':rule-classes'), the rule classes for the return type of the accessor
function.  This is @(':rewrite') by default; you may wish to change it to
@(':type-prescription') when the type is something basic like
@('integerp').</li>
</ul>
")





