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
(include-book "fty-sum")
(include-book "std/util/cons" :dir :system)
(program)

; We now introduce defoption, defprod, and deftagsum.  These macros are
; "syntactic sugar" instead of core fixtypes.  They just expand to flexsums.

; NOTE: We're reusing the std::formal data structure and some of the associated
; parsing code, but some things are a bit different: mainly, the guard field
; gets the function predicate symbol, not the whole term.

(define tagprod-parse-formal-item
  ;; parses guard/doc item inside an extended formal, doesn't deal with kwd/val options
  ((ctx      "Context for error messages.")
   (varname  "Name of this formal (i.e., field).")
   (item     "A single user-level item that occurs within the formal.")
   (guards   "Accumulator for guards (for this formal/field only).")
   (docs     "Accumulator for docs (for this formal/field only)."))
  :returns (mv guards docs)
  (declare (xargs :guard (legal-variablep varname)))
  (b* (((when (eq item t))
        (mv guards docs))
       ((when (eq item nil))
        (raise "~x0, field ~x1: don't know what to do with an element with a guard of NIL"
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
          (prog2$ (raise "~x0, field ~x1: can't handle a complicated guard like ~x2"
                         ctx varname item)
                  (mv guards docs))))
       ((when (stringp item))
        (mv guards (cons item docs))))
    (raise "~x0: field ~x1: expected guard specifiers or documentation ~
            strings, but found ~x2."
           ctx varname item)
    (mv guards docs)))

(define tagprod-parse-formal-items (ctx varname items guards docs)
  :returns (mv guards docs)
  (declare (xargs :guard (legal-variablep varname)))
  (b* (((when (not items))
        (mv guards docs))
       ((when (atom items))
        (raise "~x0: field ~x1 should be nil-terminated; found ~x2 as the ~
                final cdr."
               ctx varname items)
        (mv guards docs))
       ((mv guards docs)
        (tagprod-parse-formal-item ctx varname (car items) guards docs)))
    (tagprod-parse-formal-items ctx varname (cdr items) guards docs)))

(define tagprod-parse-formal
  ((ctx        "Context for error messages.")
   (formal     "User-level field description.")
   (legal-kwds "What keywords are allowed in the item list."))
  :returns (formal "A formal-p.")
  (declare (xargs :guard t))
  (b* (((when (atom formal))
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
                    (t (raise "~x0: field ~x1: expected a single guard term, ~
                               but found ~&2." ctx varname guards))))
       (doc   (cond ((atom docs) "")
                    ((atom (cdr docs)) (car docs))
                    (t (progn$
                        (raise "~x0: field ~x1: expected a single xdoc ~
                                string, but found ~&2." ctx varname docs)
                        "")))))
    (std::make-formal :name varname
                      :guard guard
                      :doc doc
                      :opts opts)))

(define tagprod-parse-formals (ctx formals legal-kwds)
  (declare (xargs :guard t))
  (b* (((when (not formals))
        nil)
       ((when (atom formals))
        (raise "~x0: expected fields to be nil-terminated, but found ~x1 as ~
                the final cdr." ctx formals)))
    (cons (tagprod-parse-formal ctx (car formals) legal-kwds)
          (tagprod-parse-formals ctx (cdr formals) legal-kwds))))

; We now translate the user's field descriptions into the flexsum format.

(define tagsum-acc-for-tree (pos num expr car cdr)
  ;; Construct the correct CAR/CDR nest to get to the POS'th field out of NUM
  ;; fields in a tree layout.  EXPR starts as X and gets extended with
  ;; CAR/CDRs.
  (b* (((when (zp num))
        (raise "bad programmer"))
       ((when (eql num 1))
        expr)
       (half (floor num 2))
       ((when (< pos half))
        (tagsum-acc-for-tree pos half `(,car ,expr) car cdr)))
    (tagsum-acc-for-tree (- pos half) (- num half) `(,cdr ,expr) car cdr)))

(define tagsum-formal-to-flexsum-field
  ((x      "A single field, already parsed into a formal.")
   (pos    "X's position in the list of fields.")
   (num    "Total number of fields.")
   (xvar   "Special x variable.")
   (layout "How the fields are laid out."))
  :returns (flexsum-syntax "User-level(!) flexsum syntax for this field.")
  (b* (((std::formal x) x)
       (accessor (case layout
                   (:alist    `(cdr (std::da-nth ,pos ,xvar)))
                   (:tree     (tagsum-acc-for-tree pos num xvar 'prod-car 'prod-cdr))
                   (:fulltree (tagsum-acc-for-tree pos num xvar 'car 'cdr))
                   (:list     `(std::da-nth ,pos ,xvar)))))
    `(,x.name :acc-body ,accessor
              :doc ,x.doc
              :type ,x.guard
              :default ,(cdr (assoc :default x.opts))
              ,@(let ((look (assoc :rule-classes x.opts)))
                  (and look `(:rule-classes ,(cdr look))))
              ,@(let ((look (assoc :reqfix x.opts)))
                  (and look `(:reqfix ,(cdr look)))))))

(define tagsum-formals-to-flexsum-fields (x pos num xvar layout)
  (if (atom x)
      nil
    (cons (tagsum-formal-to-flexsum-field (car x) pos num xvar layout)
          (tagsum-formals-to-flexsum-fields (cdr x) (1+ pos) num xvar layout))))

(define tagsum-alist-ctor-elts ((fieldnames) (cons "Either cons or hons."))
  (if (atom fieldnames)
      nil
    (cons `(,cons ',(car fieldnames) ,(car fieldnames))
          (tagsum-alist-ctor-elts (cdr fieldnames) cons))))

(define tagsum-tree-ctor (fieldnames len cons)
  (b* (((when (zp len))
        ;; (raise "bad programmer")
        nil)
       ((when (eql len 1))
        (car fieldnames))
       (half (floor len 2)))
    `(,cons ,(tagsum-tree-ctor (take half fieldnames) half cons)
            ,(tagsum-tree-ctor (nthcdr half fieldnames) (- len half) cons))))

(define tagsum-fields-to-ctor-body (fieldnames layout honsp)
  (b* ((list (if honsp 'acl2::hons-list 'list)))
    (case layout
      (:alist   `(,list . ,(tagsum-alist-ctor-elts fieldnames (if honsp 'hons 'cons))))
      (:tree     (tagsum-tree-ctor fieldnames (len fieldnames) (if honsp 'prod-hons 'prod-cons)))
      (:fulltree (tagsum-tree-ctor fieldnames (len fieldnames) (if honsp 'hons      'cons)))
      (:list     `(,list . ,fieldnames)))))

(define tagsum-fields-to-remake-aux ((fieldnames     "as in tagsum-tree-ctor")
                                     (len            "as in tagsum-tree-ctor")
                                     (path           "current path into the original structure")
                                     (cons-with-hint "cons-with-hint or prod-cons-with-hint")
                                     (car            "car or prod-car")
                                     (cdr            "cdr or prod-car"))
  (b* (((when (zp len))
        (raise "bad programmer"))
       ((when (eql len 1))
        (car fieldnames))
       (half (floor len 2))
       (rest (- len half)))
    `(,cons-with-hint
      ,(tagsum-fields-to-remake-aux (take half fieldnames)   half `(,car ,path) cons-with-hint car cdr)
      ,(tagsum-fields-to-remake-aux (nthcdr half fieldnames) rest `(,cdr ,path) cons-with-hint car cdr)
      ,path)))

(define tagsum-fields-to-remake-body (fieldnames path layout)
  (b* (((mv cons-with-hint car cdr)
        (cond ((eq layout :fulltree) (mv 'cons-with-hint      'car      'cdr))
              ((eq layout :tree)     (mv 'prod-cons-with-hint 'prod-car 'prod-cdr))
              (t (mv (er hard? 'tagsum-fields-to-remake-body "Bad layout ~x0" layout) nil nil)))))
    (tagsum-fields-to-remake-aux fieldnames (len fieldnames) path cons-with-hint car cdr)))

#||
(tagsum-fields-to-remake-body '(aa bb cc) 'x :fulltree)
(tagsum-fields-to-remake-body '(aa bb cc) '(cdr x) :tree)
||#

(define tagsum-tree-shape (len expr consp car cdr)
  (b* (((when (zp len))
        ;; (raise "bad programmer")
        `((eq ,expr nil)))
       ((when (eql len 1))
        nil)
       (half (floor len 2)))
    (cons `(,consp ,expr)
          (append (tagsum-tree-shape half `(,car ,expr) consp car cdr)
                  (tagsum-tree-shape (- len half) `(,cdr ,expr) consp car cdr)))))

(logic)

;; Checks that ALIST is an alist whose cars are exactly CARS, in that order.
;; Unlike, strip-cars, this avoids consing.
(defund alist-with-carsp (alist cars)
  (declare (xargs :guard (symbol-listp cars)))
  (if (atom cars)
      (null alist)
    (and (consp alist)
         (let ((entry (first alist)))
           (and (consp entry)
                (eq (first cars) (car entry))
                (alist-with-carsp (rest alist) (rest cars)))))))

(defthm alist-with-carsp-correct
  (implies (true-listp cars)
           (equal (alist-with-carsp alist cars)
                  (and (alistp alist)
                       (equal (strip-cars alist) cars))))
  :hints (("Goal" :in-theory (enable alist-with-carsp))))

(program)

(define tagsum-fields-to-shape (fields xvar layout)
  ;; This is used for both tagsum and defprod.  In tagsum, xvar is actually `(cdr
  ;; ,xvar) because this doesn't involve the tag.
  (case layout
    (:alist    `(mbe :logic
                     (and (alistp ,xvar)
                          (equal (strip-cars ,xvar) ',(strip-cars fields)))
                     :exec
                     (alist-with-carsp ,xvar ',(strip-cars fields))))
    (:list     `(and (true-listp ,xvar)
                     (eql (len ,xvar) ,(len fields))))
    (:tree     `(and . ,(tagsum-tree-shape (len fields) xvar 'prod-consp 'prod-car 'prod-cdr)))
    (:fulltree `(and . ,(tagsum-tree-shape (len fields) xvar 'consp 'car 'cdr)))))


; Tagsum Parsing --------------------------------------------------------------

(define tagsum-prod-check-base-case (formals our-fixtypes)
  (if (atom formals)
      t
    (and (not (find-fixtype (std::formal->guard (car formals)) our-fixtypes))
         (tagsum-prod-check-base-case (cdr formals) our-fixtypes))))

(defconst *tagprod-formal-keywords*
  '(:rule-classes
    :default
    :reqfix))

(defconst *tagprod-keywords*
  '(:layout
    :hons
    :inline
    :base-name
    :require
    :short
    :long
    :extra-binder-names
    :count-incr
    :no-ctor-macros
    :verbosep))

(defun fty-layout-supports-remake-p (fields honsp layout)
  (and (member layout '(:tree :fulltree))
       (not honsp)
       (consp fields)))

(define tagsum-prod-to-flexprod (x xvar sum-kwds lastp have-basep our-fixtypes)
  (b* (((cons kind args) x)
       ((mv kwd-alist fields)
        (extract-keywords kind *tagprod-keywords* args nil))
       ((when (not (eql (len fields) 1)))
        (raise "Should have exactly one set of field specifiers: ~x0~%" fields)
        (mv nil nil))
       (layout      (getarg :layout (getarg :layout :list sum-kwds) kwd-alist))
       (inlinep     (assoc :inline kwd-alist))
       (requirep    (assoc :require kwd-alist))
       (shortp      (assoc :short kwd-alist))
       (longp       (assoc :long kwd-alist))
       (count-incrp (assoc :count-incr kwd-alist))
       (hons        (getarg :hons nil kwd-alist))
       (fields (car fields))
       (field-formals (tagprod-parse-formals kind fields *tagprod-formal-keywords*))
       (basep (and (if have-basep
                       (eq have-basep kind)
                     (tagsum-prod-check-base-case field-formals our-fixtypes))
                   kind))
       (flexsum-fields (tagsum-formals-to-flexsum-fields
                        field-formals 0 (len field-formals) `(cdr ,xvar) layout))
       (base-name  (getarg :base-name nil kwd-alist))
       (fieldnames (strip-cars flexsum-fields))
       (ctor-body1 (tagsum-fields-to-ctor-body fieldnames layout hons))
       (remake-body (and (fty-layout-supports-remake-p fieldnames hons layout)
                         `(cons-with-hint ,kind
                                          ,(tagsum-fields-to-remake-body fieldnames `(cdr ,xvar) layout)
                                          ,xvar)))
       (shape1 (tagsum-fields-to-shape flexsum-fields `(cdr ,xvar) layout))
       (extra-binder-names (getarg :extra-binder-names nil kwd-alist))
       (no-ctor-macros (getarg :no-ctor-macros nil kwd-alist)))
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
          ,@(and inlinep     `(:inline ,(cdr inlinep)))
          ,@(and requirep    `(:require ,(cdr requirep)))
          ,@(and base-name   `(:type-name ,base-name))
          ,@(and shortp      `(:short ,(cdr shortp)))
          ,@(and longp       `(:long ,(cdr longp)))
          ,@(and count-incrp `(:count-incr ,(cdr count-incrp)))
          :ctor-body (,(if hons 'hons 'cons) ,kind ,ctor-body1)
          ,@(and remake-body `(:remake-body ,remake-body))
          ,@(and extra-binder-names `(:extra-binder-names ,extra-binder-names))
          ,@(and no-ctor-macros `(:no-ctor-macros ,no-ctor-macros)))
        basep)))

(define tagsum-prods-to-flexprods (prods xvar sum-kwds have-base-or-override our-fixtypes tagsum-name)
  (b* (((when (and (atom prods)
                   (not have-base-or-override)))
        (raise "We couldn't find a base case for tagsum ~x0, so we don't know ~
                what its fixing function should return when the input is an ~
                atom.  To override this, add keyword arg :base-case-override ~
                [product], where [product] is one of your product keywords, ~
                and provide a measure that will allow the fixing function to ~
                terminate."
               tagsum-name))
       ((when (atom prods))
        nil)
       ((mv first basep)
        (tagsum-prod-to-flexprod (car prods)
                                 xvar sum-kwds (atom (cdr prods)) have-base-or-override
                                 our-fixtypes)))
    (cons first
          (tagsum-prods-to-flexprods (cdr prods)
                                     xvar sum-kwds (or have-base-or-override basep)
                                     our-fixtypes tagsum-name))))



(defconst *tagsum-keywords*
  '(:pred
    :fix
    :equiv
    :kind
    :count
    :measure ;; term
    :measure-debug
    :xvar  ;; var name
    :no-count
    :parents :short :long  ;; xdoc
    :inline
    :layout ;; :list, :tree, :fulltree, :alist
    :case
    :base-case-override
    :prepwork
    :post-pred-events
    :post-fix-events
    :post-events
    :enable-rules
    :verbosep))


(define tagsum-tag-events-post-fix (pred fix xvar name kind)
  ;; [Jared] as with defprod tags (see defprod-tag-events-post-fix), I don't
  ;; think we should need this:
  ;;
  ;; '((defthm ,(intern-in-package-of-symbol (cat (symbol-name pred) "-OF-" (symbol-name fix) "-TAG-FORWARD")
  ;;                                         name)
  ;;     (,pred (,fix ,xvar))
  ;;     :rule-classes ((:forward-chaining :trigger-terms ((tag (,fix ,xvar))))))))
  ;;
  ;; For that matter, how do we even want to handle the tag of a tagsum?  We
  ;; don't normally want to take the tag of a tagsum, instead we should use the
  ;; kind function.  And the kind function already has its -possibilities
  ;; theorem, which is basically what we want.
  ;;
  ;; But, the relationship between tag and kind is unusual.  For a tagsum we
  ;; have that (tag x) == (kind x), which isn't true in general for a flexsum,
  ;; and which isn't anything we have to deal with in the case of a transsum
  ;; where we aren't introducing our own kind function.
  ;;
  ;; I think it's probably important to know about the relationship between tag
  ;; and kind in order to support nesting tagsums within transsums.  This is a
  ;; little bit tricky because we really only have a conditional equality, i.e.,
  ;;
  ;;    (implies (vl-expr-p x)
  ;;             (equal (tag x) (vl-expr-kind x)))
  ;;
  ;; And we probably don't really want backchain on this.  Well, it seems like
  ;; a pretty decent forward-chaining rule for tag-reasoning.  We can also get
  ;; an unconditional tag of fix rule, which seems really helpful for proving
  ;; the congruences for a deftranssum kind function.
  (b* ((tag-when-foo-p-forward (intern-in-package-of-symbol
                                (cat "TAG-WHEN-" (symbol-name pred) "-FORWARD")
                                name))
       (tag-of-foo-fix (intern-in-package-of-symbol
                        (cat "TAG-OF-" (symbol-name fix))
                        name)))
    `((defthmd ,tag-when-foo-p-forward
        (implies (,pred ,xvar)
                 (equal (tag ,xvar) (,kind ,xvar)))
        :rule-classes ((:forward-chaining :trigger-terms ((,pred ,xvar))))
        :hints(("Goal" :expand ((tag ,xvar)
                                (,pred ,xvar)
                                (,kind ,xvar)))))
      (defthm ,tag-of-foo-fix
        (equal (tag (,fix ,xvar))
               (,kind ,xvar))
        :hints(("Goal"
                :in-theory (disable ,tag-when-foo-p-forward tag ,pred ,kind)
                :use ((:instance ,tag-when-foo-p-forward (,xvar (,fix ,xvar)))))))

      (add-to-ruleset std::tag-reasoning '(,tag-when-foo-p-forward
                                           ,tag-of-foo-fix)))))


(define parse-tagsum (x xvar these-fixtypes fixtypes)
  (b* (((cons name args) x)
       ((unless (symbolp name))
        (raise "Malformed tagsum: ~x0: name must be a symbol" x))
       ((mv pre-/// post-///)     (std::split-/// name args))
       ((mv kwd-alist orig-prods) (extract-keywords name *tagsum-keywords* pre-/// nil))
       (pred   (getarg! :pred  (intern-in-package-of-symbol (cat (symbol-name name) "-P") name) kwd-alist))
       (fix    (getarg! :fix   (intern-in-package-of-symbol (cat (symbol-name name) "-FIX") name) kwd-alist))
       (equiv  (getarg! :equiv (intern-in-package-of-symbol (cat (symbol-name name) "-EQUIV") name) kwd-alist))
       (kind   (getarg! :kind  (intern-in-package-of-symbol (cat (symbol-name name) "-KIND") name) kwd-alist))
       (case   (getarg! :case  (intern-in-package-of-symbol (cat (symbol-name name) "-CASE") name) kwd-alist))
       (inline (get-deftypes-inline-opt *inline-defaults* kwd-alist))
       (count  (flextype-get-count-fn name kwd-alist))
       (xvar   (or (getarg :xvar xvar kwd-alist)
                   (car (find-symbols-named-x (getarg :measure nil kwd-alist)))
                   (intern-in-package-of-symbol "X" name)))
       (layout (getarg :layout :alist kwd-alist))
       ((unless (member layout '(:tree :fulltree :list :alist)))
        (raise "In tagsum ~x0: Bad layout type ~x1~%" name layout))
       (base-override (getarg :base-case-override nil kwd-alist))
       (flexprods-in (tagsum-prods-to-flexprods orig-prods xvar kwd-alist base-override these-fixtypes name))
       ((unless (or (not base-override)
                    (member base-override (strip-cars flexprods-in))))
        (raise "In tagsum ~x0: :base-case-override value must be one of the ~
                product names (~x1) but found ~x2."
               name (strip-cars flexprods-in) base-override))
       (prods (parse-flexprods flexprods-in name kind kwd-alist xvar nil these-fixtypes fixtypes))
       (- (flexprods-check-xvar xvar prods))
       ((when (atom prods))
        (raise "In tagsum ~s0: Must have at least one product." name))
       (recp (some-flexprod-recursivep prods))
       (measure (getarg! :measure `(acl2-count ,xvar) kwd-alist))
       (post-fix-events (append (tagsum-tag-events-post-fix pred fix xvar name kind)
                                (cdr (assoc :post-fix-events kwd-alist)))))
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
                  :kwd-alist (cons (cons :post-fix-events post-fix-events)
                                   (if post-///
                                       (cons (cons :///-events post-///)
                                             kwd-alist)
                                     kwd-alist))
                  :orig-prods orig-prods
                  :recp recp
                  :typemacro 'deftagsum)))

;; --- Defprod parsing ---
(defconst *defprod-keywords*
  '(:pred
    :fix
    :equiv
    :count
    :measure ;; term
    :measure-debug
    :xvar  ;; var name
    :no-count
    :parents
    :short
    :long  ;; xdoc
    :inline
    :require
    :layout ;; :list, :tree, :fulltree, :alist
    :tag
    :hons
    :prepwork
    :post-pred-events
    :post-fix-events
    :post-events
    :enable-rules
    :extra-binder-names
    :no-ctor-macros
    :verbosep
    ))

(define defprod-fields-to-flexsum-prod (fields xvar name kwd-alist)
  (b* ((layout (getarg :layout :alist kwd-alist))
       ((unless (member layout '(:tree :fulltree :list :alist)))
        (raise "In ~x0: bad layout type ~x1~%" name layout))
       (tag (getarg :tag nil kwd-alist))
       (hons (getarg :hons nil kwd-alist))
       (field-formals (tagprod-parse-formals name fields *tagprod-formal-keywords*))
       (xbody (if tag `(cdr ,xvar) xvar))
       (flexsum-fields (tagsum-formals-to-flexsum-fields
                        field-formals 0 (len field-formals) xbody layout))
       (fieldnames (strip-cars flexsum-fields))
       (ctor-body1 (tagsum-fields-to-ctor-body fieldnames layout hons))
       (ctor-body (if tag `(,(if hons 'hons 'cons) ,tag ,ctor-body1) ctor-body1))
       (remake-body1 (and (fty-layout-supports-remake-p fieldnames hons layout)
                          (tagsum-fields-to-remake-body fieldnames xbody layout)))
       (remake-body (and remake-body1
                         (if tag `(cons-with-hint ,tag ,remake-body1 ,xvar) remake-body1)))
       (shape (tagsum-fields-to-shape flexsum-fields xbody layout))
       (requirep (assoc :require kwd-alist))
       (kind (or tag (intern$ (symbol-name name) "KEYWORD")))
       (extra-binder-names (getarg :extra-binder-names nil kwd-alist))
       (no-ctor-macros (getarg :no-ctor-macros nil kwd-alist)))
    `(,kind
      :shape ,(if tag
                    (nice-and `(eq (car ,xvar) ,tag) shape)
                  shape)
      :fields ,flexsum-fields
      :type-name ,name
      :ctor-body ,ctor-body
      ,@(and remake-body `(:remake-body ,remake-body))
      ,@(and extra-binder-names `(:extra-binder-names ,extra-binder-names))
      ,@(and no-ctor-macros `(:no-ctor-macros ,no-ctor-macros))
      ,@(and requirep `(:require ,(cdr requirep))))))

(define defprod-tag-events-post-pred (pred xvar tag name)
  (b* ((tag-when-foo-p (intern-in-package-of-symbol (cat "TAG-WHEN-" (symbol-name pred)) name))
       (foo-p-when-wrong-tag (intern-in-package-of-symbol (cat (symbol-name pred) "-WHEN-WRONG-TAG") name)))
    `((defthmd ,tag-when-foo-p
        (implies (,pred ,xvar)
                 (equal (tag ,xvar)
                        ,tag))
        :rule-classes ((:rewrite :backchain-limit-lst 0)
                       (:forward-chaining))
        :hints(("Goal" :in-theory (enable tag ,pred))))

      (defthmd ,foo-p-when-wrong-tag
        (implies (not (equal (tag ,xvar) ,tag))
                 (equal (,pred ,xvar)
                        nil))
        :rule-classes ((:rewrite :backchain-limit-lst 1))
        :hints(("Goal" :in-theory (enable tag ,pred))))

      (add-to-ruleset std::tag-reasoning
                      '(,tag-when-foo-p
                        ,foo-p-when-wrong-tag)))))

(define defprod-tag-events-post-fix (pred fix xvar name tag)
  (declare (ignorable pred))
  (let ((tag-of-foo-fix (intern-in-package-of-symbol (cat "TAG-OF-" (symbol-name fix)) name))
        (tag-when-foo-p (intern-in-package-of-symbol (cat "TAG-WHEN-" (symbol-name pred)) name)))
    `(;; [Jared] this rule seems really weird to me.  I think we should unconditionally
      ;; know that the predicate holds of its fixing function, so do we really need to
      ;; ever forward chain to that?  I'm going to try commenting this out.
      ;;
      ;; (defthm ,(intern-in-package-of-symbol (cat (symbol-name pred) "-OF-" (symbol-name fix) "-TAG-FORWARD")
      ;;                                       name)
      ;;   (,pred (,fix ,xvar))
      ;;   :rule-classes ((:forward-chaining :trigger-terms ((tag (,fix ,xvar))))))
      ;;
      ;; Meanwhile, particularly for the kind-of-fix functions for transparent
      ;; sums, I think it *would* be really nice to know what the tag of the
      ;; fixing function must be.  This seems like a safe rule to leave enabled
      ;; even if we don't have tag-reasoning active, because it should only
      ;; ever unify with (tag (foo-fix ...))
      (defthm ,tag-of-foo-fix
        (equal (tag (,fix ,xvar))
               ,tag)
        :hints(("Goal" :in-theory (enable ,tag-when-foo-p)
                :cases ((,pred (,fix ,xvar))))))
      (add-to-ruleset std::tag-reasoning '(,tag-of-foo-fix)))))

(define defprod-tag-events-post-ctor (tag name formals)
  (let ((tag-of-foo (intern-in-package-of-symbol (cat "TAG-OF-" (symbol-name name))
                                                 name)))
    `((defthm ,tag-of-foo
        (equal (tag (,name . ,formals))
               ,tag)
        :hints (("goal" :in-theory (enable ,name tag))))
      (add-to-ruleset std::tag-reasoning '(,tag-of-foo)))))

(define parse-defprod (x xvar our-fixtypes fixtypes)
  (b* (((cons name args) x)
       ((unless (symbolp name))
        (raise "Malformed defprod: ~x0: name must be a symbol" x))
       ((mv pre-/// post-///) (std::split-/// name args))
       ((mv kwd-alist fields)
        (extract-keywords name *defprod-keywords* pre-/// nil))
       ((when (atom fields))
        (raise "In defprod ~x0: List of fields is missing~%" name))
       ((when (consp (cdr fields)))
        (raise "In defprod ~x0: More than one list of fields present~%" name))
       (fields (car fields))
       (pred  (getarg! :pred  (intern-in-package-of-symbol (cat (symbol-name name) "-P") name) kwd-alist))
       (fix   (getarg! :fix   (intern-in-package-of-symbol (cat (symbol-name name) "-FIX") name) kwd-alist))
       (equiv (getarg! :equiv (intern-in-package-of-symbol (cat (symbol-name name) "-EQUIV") name) kwd-alist))
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
       (- (flexprods-check-xvar xvar prods))
       (measure (getarg! :measure `(acl2-count ,xvar) kwd-alist))
       (field-names (flexprod-fields->names (flexprod->fields (car prods))))
       (post-events (if tag
                        (append (defprod-tag-events-post-ctor tag name field-names)
                                (cdr (assoc :post-events kwd-alist)))
                      (cdr (assoc :post-events kwd-alist))))
       (post-pred-events (if tag
                             (append (defprod-tag-events-post-pred
                                       pred xvar tag name)
                                     (cdr (assoc :post-pred-events kwd-alist)))
                           (cdr (assoc :post-pred-events kwd-alist))))
       (post-fix-events (if tag
                             (append (defprod-tag-events-post-fix
                                       pred fix xvar name tag)
                                     (cdr (assoc :post-fix-events kwd-alist)))
                           (cdr (assoc :post-fix-events kwd-alist)))))
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
                                    (cons :post-pred-events post-pred-events)
                                    (cons :post-fix-events post-fix-events)
                                    kwd-alist)
                  :orig-prods orig-prods
                  :inline inline
                  :recp (some-flexprod-recursivep prods)
                  :typemacro 'defprod)))

;; --- Defoption parsing ---

(defconst *option-keywords*
  '(:pred
    :fix
    :equiv
    :count
    :measure ;; term
    :measure-debug
    :xvar  ;; var name
    :no-count
    :parents :short :long  ;; xdoc
    :inline
    ;; bozo we had layout here?? are the rest of these sensible?
    ;; :layout ;; :list, :tree, :fulltree, :alist
    :case
    :base-case-override
    :prepwork
    :post-pred-events
    :post-fix-events
    :post-events
    :enable-rules
    :verbosep))

(define defoption-post-pred-events (x)
  (b* (((flexsum x))
       ((fixtype base) (cdr (assoc :basetype x.kwd-alist)))
       (maybe-foo-p-when-foo-p (intern-in-package-of-symbol
                                (cat (symbol-name x.pred) "-WHEN-" (symbol-name base.pred))
                                x.pred))
       (foo-p-when-maybe-foo-p (intern-in-package-of-symbol
                                (cat (symbol-name base.pred) "-WHEN-" (symbol-name x.pred))
                                x.pred)))
    `((defthm ,maybe-foo-p-when-foo-p
        (implies (,base.pred ,x.xvar)
                 (,x.pred ,x.xvar))
        :hints(("Goal" :in-theory (enable ,x.pred))))
      (defthm ,foo-p-when-maybe-foo-p
        (implies (and (,x.pred ,x.xvar)
                      (double-rewrite ,x.xvar))
                 (,base.pred ,x.xvar))
        :hints(("Goal" :in-theory (enable ,x.pred)))))))

(define defoption-post-fix-events (x)
  (b* (((flexsum x))
       ((fixtype base) (cdr (assoc :basetype x.kwd-alist)))
       (maybe-foo-fix-under-iff (intern-in-package-of-symbol
                                 (cat (symbol-name x.fix) "-UNDER-IFF")
                                 x.pred))
       (defoption-lemma-foo-fix-nonnil (intern-in-package-of-symbol
                                        (cat "DEFOPTION-LEMMA-" (symbol-name base.fix) "-NONNIL")
                                        base.fix)))
    `((local
       (defthm ,defoption-lemma-foo-fix-nonnil
         (,base.fix x)
         :hints (("goal" :use ((:theorem (,base.pred (,base.fix x)))
                               (:theorem (not (,base.pred nil))))
                  :in-theory '((,base.pred)))
                 (and stable-under-simplificationp
                      '(:in-theory (enable))))
         :rule-classes :type-prescription))
      (defthm ,maybe-foo-fix-under-iff
        (iff (,x.fix ,x.xvar) ,x.xvar)
        :hints(("Goal" :in-theory (enable ,x.fix))))
      (defrefinement ,x.equiv ,base.equiv
        :hints (("Goal" :in-theory (enable ,x.fix))
                (and stable-under-simplificationp
                     '(:in-theory (enable ,base.equiv))))))))

(define parse-option (x xvar these-fixtypes fixtypes)
  (b* (((list* name basetype args) x)
       ((unless (symbolp name))
        (raise "Malformed option: ~x0: name must be a symbol" x))
       ((unless (symbolp basetype))
        (raise "Malformed option: ~x0: basetype must be a symbol, found ~x1"
               name basetype))
       (base-fixtype (or (find-fixtype basetype these-fixtypes)
                         (find-fixtype basetype fixtypes)))
       ((mv pre-/// post-///)     (std::split-/// name args))
       ((mv kwd-alist orig-prods) (extract-keywords name *option-keywords* pre-/// nil))
       (pred   (getarg! :pred  (intern-in-package-of-symbol (cat (symbol-name name) "-P") name) kwd-alist))
       (fix    (getarg! :fix   (intern-in-package-of-symbol (cat (symbol-name name) "-FIX") name) kwd-alist))
       (equiv  (getarg! :equiv (intern-in-package-of-symbol (cat (symbol-name name) "-EQUIV") name) kwd-alist))
       (case   (getarg! :case  (intern-in-package-of-symbol (cat (symbol-name name) "-CASE") name) kwd-alist))
       (inline (get-deftypes-inline-opt *inline-defaults* kwd-alist))
       (count  (flextype-get-count-fn name kwd-alist))
       (xvar (or (getarg :xvar xvar kwd-alist)
                 (car (find-symbols-named-x (getarg :measure nil kwd-alist)))
                 (intern-in-package-of-symbol "X" name)))
       (name-link (xdoc::see name))
       (flexprods-in
        `((:none
           :cond (not ,xvar)
           :ctor-body nil
           :short ,(cat "Represents that no " name-link " is available, i.e., Nothing or None."))
          (:some
           :cond t
           :fields ((val :type ,basetype :acc-body ,xvar))
           :ctor-body val
           :short ,(cat "An available " name-link ", i.e., <i>Just val</i> or <i>Some val</i>."))))
       (prods (parse-flexprods flexprods-in name nil kwd-alist xvar nil these-fixtypes fixtypes))
       (- (flexprods-check-xvar xvar prods))
       ((when (atom prods))
        (raise "Malformed SUM ~x0: Must have at least one product" name))
       (measure (or (getarg :measure nil kwd-alist)
                    `(acl2-count ,xvar)))
       (kwd-alist (cons (cons :basetype base-fixtype)
                        (if post-///
                            (cons (cons :///-events post-///)
                                  kwd-alist)
                          kwd-alist)))
       (flexsum (make-flexsum :name name
                              :pred pred
                              :fix fix
                              :equiv equiv
                              :case case
                              :count count
                              :prods prods
                              :shape t
                              :xvar xvar
                              :inline inline
                              :measure measure
                              :kwd-alist kwd-alist
                              :orig-prods orig-prods
                              :recp (some-flexprod-recursivep prods)
                              :typemacro 'defoption))
       (post-pred-events
        (append (defoption-post-pred-events flexsum)
                (cdr (assoc :post-pred-events kwd-alist))))
       (post-fix-events
        (append (defoption-post-fix-events flexsum)
                (cdr (assoc :post-fix-events kwd-alist))))
       (kwd-alist `((:post-pred-events . ,post-pred-events)
                    (:post-fix-events . ,post-fix-events)
                    . ,kwd-alist)))
    (change-flexsum flexsum :kwd-alist kwd-alist)))
