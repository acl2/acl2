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
(include-book "fixtype")
(include-book "fixequiv")
(include-book "fty-parseutils")
(include-book "std/util/define" :dir :system)
(include-book "ihs/basic-definitions" :dir :system)
(include-book "basetypes")
(include-book "std/basic/arith-equiv-defs" :dir :system)
;; (include-book "centaur/bitops/part-select" :dir :system)
(include-book "bitstruct-theory")
(include-book "misc/without-waterfall-parallelism" :dir :system)
(local (include-book "centaur/bitops/equal-by-logbitp" :dir :system))
(local (include-book "centaur/bitops/ihsext-basics" :dir :system))
(local (include-book "arithmetic/top-with-meta" :dir :system))
(local (in-theory (disable part-install part-select)))
(program)

(def-primitive-aggregate bitstruct-field
  (name
   width lsb
   accessor
   updater
   type pred fix equiv fullp
   signedp
   rule-classes
   doc
   subfield-hierarchy ;; for subfields -- list of fields, innermost first
   kwd-alist))

(defconst *bitstruct-field-keywords*
  '(:accessor :updater :default :subfields :rule-classes))

(def-primitive-aggregate bitstruct
  (name
   fields ;; list of bitstruct-field structures
   width ;; full width
   pred fix equiv
   xvar
   fullp
   kwd-alist
   orig-fields
   signedp inline
   defs-ruleset
   r-o-w-ruleset
   update-to-ctor-ruleset
   extra-binder-names
   equiv-under-mask))

(defconst *defbitstruct-keywords*
  '(:pred :fix :equiv :xvar :signedp :inline :fullp
    :parents :short :long :msb-first))

(define lookup-bitstruct (name bitstruct-table)
  (cond ((atom bitstruct-table) nil)
	((eq name (caar bitstruct-table)) (cdar bitstruct-table))
	((eq name (bitstruct->pred (cdar bitstruct-table))) (cdar bitstruct-table))
	(t (lookup-bitstruct name (cdr bitstruct-table)))))

(defines parse-bitstruct-subfields
  (define parse-bitstruct-subfields (subfield-treelst fields hier lsb x.name bitstruct-table)
    (if (atom fields)
	(and (consp subfield-treelst)
	     (raise "Bad subfield tree: ran out of primary fields under ~x0" hier))
      (if (bitstruct-field->subfield-hierarchy (car fields))
	  ;; Only process primary fields
	  (parse-bitstruct-subfields subfield-treelst (cdr fields) hier lsb x.name bitstruct-table)
	(append (parse-bitstruct-subfield (car subfield-treelst) (car fields) hier lsb x.name bitstruct-table)
		(parse-bitstruct-subfields (cdr subfield-treelst) (cdr fields) hier lsb x.name bitstruct-table)))))

  (define parse-bitstruct-subsubfield (subfield-treelst field hier lsb x.name bitstruct-table)
    (b* (((bitstruct-field field))
	 (type (lookup-bitstruct field.type bitstruct-table))
	 ((unless type) (raise "Didn't find bitstruct type for field ~x0 at ~x1" field.name hier))
	 ((bitstruct type)))
      (parse-bitstruct-subfields subfield-treelst
				 type.fields
				 hier x.name
				 (+ lsb field.lsb)
				 bitstruct-table)))

  (define parse-bitstruct-subfield (subfield-tree field hier lsb x.name bitstruct-table)
    (b* (((unless subfield-tree) nil)
	 ((bitstruct-field field))
	 (hier (cons field hier))
	 ;; process sub-subfields-if any
	 ((mv subfield-name sub-subfields)
	  (if (consp subfield-tree)
	      (mv (car subfield-tree)
		  (parse-bitstruct-subsubfield (cdr subfield-tree) field hier lsb x.name bitstruct-table))
	    (mv subfield-tree nil))))
      (cons (make-bitstruct-field
	     :name subfield-name
	     :width field.width
	     :lsb (+ lsb field.lsb)
	     :accessor (intern-in-package-of-symbol
			(cat (symbol-name x.name) "->" (symbol-name subfield-name))
			x.name)
	     :updater (intern-in-package-of-symbol
		       (cat "!" (symbol-name x.name) "->" (symbol-name subfield-name))
			x.name)
	     :rule-classes field.rule-classes
	     :type field.type
	     :pred field.pred
	     :fix field.fix
	     :fullp t
	     :equiv field.equiv
	     :signedp field.signedp
	     :subfield-hierarchy hier
	     :kwd-alist nil)
	    sub-subfields))))



(define parse-bitstruct-field (x lsb structname bitstruct-table)
  (b* (((unless (>= (len x) 2))
	(raise "Malformed bitstruct field: must have at least a field name and a type: ~x0" x))
       ((list* fieldname type rest) x)
       ((mv field-kwd-alist docs) (extract-keywords fieldname *bitstruct-field-keywords* rest nil))
       (doc (if (atom docs) nil (car docs)))
       ((unless (or (not doc) (stringp doc))) (raise "Found ~x0 in place of a doc string in bitstruct field ~x1" doc x))
       (accessor (getarg! :accessor (intern-in-package-of-symbol
				     (cat (symbol-name structname) "->" (symbol-name fieldname))
				     structname)
			  field-kwd-alist))
       (updater (getarg! :updater (intern-in-package-of-symbol
				   (cat "!" (symbol-name structname) "->" (symbol-name fieldname))
				   structname)
			 field-kwd-alist))
       (rule-classes (getarg :rule-classes :rewrite field-kwd-alist))
       (bitstruct (lookup-bitstruct type bitstruct-table))
       ((unless bitstruct)
	(raise "In field ~x0, ~x1 is not a valid bitstruct type" x type))
       ((bitstruct bitstruct))
       (field (make-bitstruct-field
	       :name fieldname
	       :width bitstruct.width
	       :lsb lsb
	       :fullp bitstruct.fullp
	       :accessor accessor
	       :updater updater
	       :rule-classes rule-classes
	       :type bitstruct.name
	       :pred bitstruct.pred
	       :fix bitstruct.fix
	       :doc doc
	       :equiv bitstruct.equiv
	       :signedp bitstruct.signedp
	       :kwd-alist field-kwd-alist))
       (subfield-treelst (getarg :subfields nil field-kwd-alist))
       (subfields (and subfield-treelst
		       (parse-bitstruct-subfields subfield-treelst bitstruct.fields
						  (list field)
						  lsb structname bitstruct-table))))
    ;; Note: parse-bitstruct-fields-aux depends on the primary field preceding subfields
    (cons field subfields)))

(table bitstruct-table 'bit (make-bitstruct :name 'bit
					    :width 1
					    :pred 'bitp
					    :fix 'acl2::bfix
					    :equiv 'bit-equiv
					    :fullp t))

(table bitstruct-table 'boolean (make-bitstruct :name 'boolean
						:width 1
						:pred 'booleanp
						:fix 'acl2::bool-fix
						:equiv 'iff
						:fullp t))


(define parse-bitstruct-fields-aux (x lsb structname bitstruct-table)
  ;; returns (mv fields with fullp)
  (b* (((when (atom x))
	(mv nil lsb t)) ;; width
       (fields (parse-bitstruct-field (car x) lsb structname bitstruct-table))
       ((bitstruct-field field1) (car fields))
       ((mv rest width fullp)
	(parse-bitstruct-fields-aux
	 (cdr x) (+ lsb field1.width) structname bitstruct-table)))
    (mv (append fields rest)
	width
	(and fullp field1.fullp))))

(define parse-bitstruct-fields (x lsb structname bitstruct-table)
  ;; returns (mv fields with fullp)
  (if (natp x)
      (mv nil x t)
    (parse-bitstruct-fields-aux x lsb structname bitstruct-table)))




(define bitstruct-primary-fields->names (x)
  (if (atom x)
      nil
    (if (bitstruct-field->subfield-hierarchy (Car x))
	(bitstruct-primary-fields->names (cdr x))
      (cons (bitstruct-field->name (car x))
	    (bitstruct-primary-fields->names (cdr x))))))

(define bitstruct-fields->names (x)
  (if (atom x)
      nil
    (cons (bitstruct-field->name (car x))
	  (bitstruct-fields->names (cdr x)))))

(define bitstruct-fields->accessors (x)
  (if (atom x)
      nil
    (cons (bitstruct-field->accessor (car x))
	  (bitstruct-fields->accessors (cdr x)))))






(define parse-defbitstruct (x bitstruct-table)
  (b* (((cons name args) x)
       ((unless (symbolp name))
	(raise "Malformed defbitstruct: ~x0: name must be a symbol" x))
       ((mv pre-/// post-///) (std::split-/// name args))
       ((mv kwd-alist fields)
	(extract-keywords name *defbitstruct-keywords* pre-/// nil))
       ((when (atom fields))
	(raise "In defbitstruct ~x0: List of fields is missing~%" name))
       ((when (consp (cdr fields)))
	(raise "In defbitstruct ~x0: More than one list of fields present~%" name))
       (orig-fields (car fields))
       (pred  (getarg! :pred  (intern-in-package-of-symbol (cat (symbol-name name) "-P") name) kwd-alist))
       (fix   (getarg! :fix   (intern-in-package-of-symbol (cat (symbol-name name) "-FIX") name) kwd-alist))
       (equiv (getarg! :equiv (intern-in-package-of-symbol (cat (symbol-name name) "-EQUIV") name) kwd-alist))
       (fullp (getarg :fullp t kwd-alist))
       (signedp (getarg :signedp nil kwd-alist))
       (inline (getarg :inline nil kwd-alist))
       (msb-first (getarg :msb-first nil kwd-alist))
       (xvar (or (getarg :xvar nil kwd-alist)
		 (intern-in-package-of-symbol "X" name)))


       ((mv fields width fields-fullp)
        (parse-bitstruct-fields
         (if msb-first (rev orig-fields) orig-fields)
         0 name bitstruct-table)))
    (make-bitstruct :name name
		    :pred pred
		    :fix fix
		    :fullp (and fullp fields-fullp)
		    :equiv equiv
		    :width width
		    :fields fields
		    :xvar xvar
		    :signedp signedp
		    :inline inline
		    :kwd-alist (list* (cons :///-events post-///)
				    kwd-alist)
		    :orig-fields orig-fields
		    :defs-ruleset
		    (intern-in-package-of-symbol (cat (symbol-name name) "-DEFS") name)
		    :r-o-w-ruleset
		    (intern-in-package-of-symbol (cat (symbol-name name) "-READ-OVER-WRITE") name)
		    :update-to-ctor-ruleset
		    (intern-in-package-of-symbol (cat (symbol-name name) "-UPDATERS-TO-CTOR") name)
		    :equiv-under-mask
		    (intern-in-package-of-symbol (cat (symbol-name equiv) "-UNDER-MASK") name))))



(define bitstruct-accessor-term-logic-form (field xvar)
  (b* (((bitstruct-field field))
       (logic-form-base `(bitops::part-select ,xvar :low ,field.lsb :width ,field.width)))
    (cond ((eq field.pred 'booleanp)
	   `(bit->bool ,logic-form-base))
	  (field.signedp `(acl2::logext ,field.width ,logic-form-base))
	  (t logic-form-base))))

;; (define bitstruct-accessor-term-exec-form (field xvar)
;;   (b* (((bitstruct-field field)))
;;     (if (eql field.width 1)
;;         (if (eq field.pred 'booleanp)
;;             `(logbitp ,field.lsb ,xvar)
;;           (if field.signedp
;;               `(acl2::logext 1 (acl2::logbit ,field.lsb ,xvar))
;;             `(acl2::logbit ,field.lsb ,xvar)))
;;       (bitstruct-accessor-term-logic-form field xvar))))

(define bitstruct-accessor-term-exec-form (fullwidth fullsigned field xvar)
  (b* (((bitstruct-field field))
       (widthleft (- fullwidth field.lsb))
       (field-type (if field.signedp 'signed-byte 'unsigned-byte))
       (full-type (if fullsigned 'signed-byte 'unsigned-byte))
       (exec-form-base
	(if (eql field.lsb 0)
	    `(the (,full-type ,fullwidth) ,xvar)
	  `(the (,full-type ,widthleft)
	     (ash
	      (the (,full-type ,fullwidth) ,xvar)
	      ,(- field.lsb)))))
       (exec-form
	`(the (,field-type ,field.width)
	   ,(if field.signedp
		`(fast-logext ,field.width ,exec-form-base)
	      `(logand (the (,field-type ,field.width)
			 ,(1- (expt 2 field.width)))
		       ,exec-form-base)))))
    (if (eq field.pred 'booleanp)
	`(bit->bool ,exec-form)
      exec-form)))

(define bitstruct-field-preds (fields xvar)
  ;; Returns the list of predicates applied to non-fullp fields.
  (b* (((when (atom fields)) nil)
       ((bitstruct-field field) (car fields))
       (rest (bitstruct-field-preds (cdr fields) xvar))
       ((when field.fullp) rest))
    (cons `(,field.pred ,(bitstruct-accessor-term-logic-form field xvar)) rest)))




(define bitstruct-pred (x)
  (b* (((bitstruct x))
       (short (cat "Recognizer for @(see " (xdoc::full-escape-symbol x.name) ") bit structures."))
       (def (if x.signedp
		`(signed-byte-p ,x.width ,x.xvar)
	      `(unsigned-byte-p ,x.width ,x.xvar)))
       (field-preds (bitstruct-field-preds x.fields x.xvar))
       (base-def `(mbe :logic ,def
		       :exec ,(if x.signedp
				  `(and (integerp ,x.xvar)
					(<= ,(- (ash 1 (1- x.width))) ,x.xvar)
					(< ,x.xvar ,(ash 1 (1- x.width))))
				`(and (natp ,x.xvar)
				      (< ,x.xvar ,(ash 1 x.width))))))
       (full-def (if field-preds
		     `(and ,base-def . ,field-preds)
		   base-def)))
    `(define ,x.pred (,x.xvar)
       :parents (,x.name)
       :short ,short
       :progn t
       :guard-hints (("goal" :in-theory (enable unsigned-byte-p signed-byte-p)))
       ,full-def
       ///
       ,@(and x.fullp
	      `((defthm ,(intern-in-package-of-symbol
			  (cat (symbol-name x.pred)
			       (if x.signedp
				   "-WHEN-SIGNED-BYTE-P"
				 "-WHEN-UNSIGNED-BYTE-P"))
			  x.name)
		  (implies ,def (,x.pred ,x.xvar)))))

       (defthm ,(intern-in-package-of-symbol
		 (cat (if x.signedp
			  "SIGNED-BYTE-P-WHEN-"
			"UNSIGNED-BYTE-P-WHEN-")
		      (symbol-name x.pred))
		 x.name)
	 (implies (,x.pred ,x.xvar) ,def))

       (defthm ,(intern-in-package-of-symbol
		 (cat (symbol-name x.pred) "-COMPOUND-RECOGNIZER")
		 x.name)
	 (implies (,x.pred ,x.xvar)
		  (,(if x.signedp 'integerp 'natp) ,x.xvar))
	 :rule-classes :compound-recognizer))))

(define bitstruct-fields-fix (fields xvar)
  (b* (((when (atom fields)) xvar)
       ((bitstruct-field field) (car fields))
       (sel `(bitops::part-select ,xvar :width ,field.width :low ,field.lsb))
       (signed (if field.signedp
		   `(logext ,field.width ,sel)
		 sel))
       (fix (if field.fullp
		signed
	      `(,field.fix ,signed)))
       ((when (atom (cdr fields))) fix))
    `(logapp ,field.width
	     ,fix
	     ,(bitstruct-fields-fix (cdr fields) xvar))))


(define bitstruct-fix (x)
  (b* (((bitstruct x))
       (short (cat "Fixing function for @(see " (xdoc::full-escape-symbol x.name) ") bit structures."))
       (x-fields-fixed (if x.fullp
			   x.xvar
			 (bitstruct-fields-fix x.fields x.xvar)))
       (x-length-fixed (cond (x.signedp
			      `(acl2::logext ,x.width ,x-fields-fixed))
			     (t ;; x.fullp
			      `(acl2::loghead ,x.width ,x-fields-fixed))
			     ;; (t x-fields-fixed)
			     )))
    `(define ,x.fix ((,x.xvar ,x.pred))
       :guard-hints (("goal" :in-theory (enable acl2::loghead-identity acl2::logext-identity
						logext-part-select-at-0-identity
						,@(and (not x.fullp)
						       `(,x.pred)))))
       :parents (,x.name)
       :short ,short
       :returns (fixed ,x.pred
		       ,@(and (not x.fullp)
			      `(:hints (("goal" :in-theory
					 (enable ,x.pred
						 part-select-at-0-of-unsigned-byte-identity
						 logext-part-select-at-0-identity))))))
       :progn t
       (mbe :logic ,x-length-fixed
	    :exec ,x.xvar)
       ///
       (defthm ,(intern-in-package-of-symbol
		 (cat (symbol-name x.fix) "-WHEN-" (symbol-name x.pred))
		 x.name)
	 (implies (,x.pred ,x.xvar)
		  (equal (,x.fix ,x.xvar) ,x.xvar))
	 :hints(("Goal" :in-theory (enable acl2::loghead-identity acl2::logext-identity
					   logext-part-select-at-0-identity
					   ,@(and (not x.fullp)
						  `(,x.pred))))))

       (local (in-theory (disable ,x.fix)))
       (fty::deffixtype ,x.name :pred ,x.pred :fix ,x.fix :equiv ,x.equiv :define t))))

(define bitstruct-fields->ctor-formals (fields)
  (if (atom fields)
      nil
    (b* (((bitstruct-field field) (car fields))
	 ((when field.subfield-hierarchy)
	  ;; skip non-primary
	  (bitstruct-fields->ctor-formals (cdr fields))))
      (cons (list field.name field.pred)
	    (bitstruct-fields->ctor-formals (cdr fields))))))

(define bitstruct-fields->ctor-fixes (fields)
  (if (atom fields)
      nil
    (b* (((bitstruct-field field) (car fields))
	 ((when field.subfield-hierarchy)
	  ;; skip non-primary
	  (bitstruct-fields->ctor-fixes (cdr fields))))
      (cons `(,field.name ,(if (eq field.pred 'booleanp)
			       `(acl2::bool->bit ,field.name)
			     `(mbe :logic (,field.fix ,field.name) :exec ,field.name)))
	    (bitstruct-fields->ctor-fixes (cdr fields))))))

(define bitstruct-fields->ctor-body (fields signedp)
  (b* (((when (atom fields)) nil)
       ((bitstruct-field field) (car fields))
       (rest (bitstruct-fields->ctor-body (cdr fields) signedp))
       ((when field.subfield-hierarchy)
	rest)
       ((when (not rest))
	(if (iff signedp field.signedp)
	    field.name
	  (if signedp
	      `(acl2::logext ,field.width ,field.name)
	    `(acl2::loghead ,field.width ,field.name)))))
    `(acl2::logapp ,field.width ,field.name ,rest)))


(define bitstruct-fields->defaults (fields)
  (if (atom fields)
      nil
    (b* (((bitstruct-field field) (car fields))
	 ((when field.subfield-hierarchy)
	  (bitstruct-fields->defaults (cdr fields))))
      (cons (or (cdr (assoc :default field.kwd-alist))
		(if (eq field.pred 'booleanp) nil 0))
	    (bitstruct-fields->defaults (cdr fields))))))

(define bitstruct-ctor (x)
  (b* (((bitstruct x))
       (fieldnames (bitstruct-primary-fields->names x.fields)))
    `(define ,x.name ,(bitstruct-fields->ctor-formals x.fields)
       ;; The parent is nil here to avoid xdoc topic name clash with the
       ;; defsection introduced by the defbitstruct event.
       :parents nil
       :returns (,x.name ,x.pred
			 ,@(and (not x.fullp)
				`(:hints (("goal" :in-theory
					   (enable ,x.pred
						   part-select-at-0-of-unsigned-byte-identity
						   logext-part-select-at-0-identity))))))
       :progn t
       (b* ,(bitstruct-fields->ctor-fixes x.fields)
	 ,(bitstruct-fields->ctor-body x.fields x.signedp))
       ///

       (fty::deffixequiv ,x.name)

       ,(std::da-make-maker x.name fieldnames (bitstruct-fields->defaults x.fields) )
       ,(std::da-make-changer x.name fieldnames nil))))

(define bitstruct-equiv-under-mask (x)
  (b* (((bitstruct x))
       (xvar1 (intern-in-package-of-symbol (cat (symbol-name x.xvar) "1") x.name))
       (mask (intern-in-package-of-symbol "MASK" x.name)))
    `(define ,x.equiv-under-mask ((,x.xvar ,x.pred)
				  (,xvar1 ,x.pred)
				  (,mask  integerp))
       (int-equiv-under-mask (,x.fix ,x.xvar)
			     (,x.fix ,xvar1)
			     ,mask))))

(define bitstruct-subfield-accessor-form (hier xvar)
  (b* (((when (atom hier)) xvar)
       (subterm (bitstruct-subfield-accessor-form (cdr hier) xvar))
       ((bitstruct-field field) (car hier)))
    `(,field.accessor ,subterm)))

(define bitstruct-subfield-accessor-fns (hier)
  (b* (((when (atom hier)) nil)
       ((bitstruct-field field) (car hier)))
    (cons field.accessor
	  (bitstruct-subfield-accessor-fns (cdr hier)))))

(define bitstruct-field-accessor (field x)
  (b* (((bitstruct x))
       ((bitstruct-field field))
       (short (cat "Access the " (xdoc::full-escape-symbol field.name)
		   " field of a @(see " (xdoc::full-escape-symbol x.name)
		   ") bit structure."))
       (logic-form (bitstruct-accessor-term-logic-form field x.xvar))
       ;; (exec-form (bitstruct-accessor-term-exec-form field x.xvar))
       (exec-form (bitstruct-accessor-term-exec-form x.width x.signedp field x.xvar))
       (logic-form (cond (field.subfield-hierarchy
			  (bitstruct-subfield-accessor-form field.subfield-hierarchy x.xvar))
			 ;; (field.fullp logic-form)
			 ;; (t `(,field.fix ,logic-form))
			 (t logic-form)))
       (subfield-accs (bitstruct-subfield-accessor-fns field.subfield-hierarchy))
       (fieldnames (bitstruct-primary-fields->names x.fields)))
    `(define ,field.accessor ((,x.xvar ,x.pred))
       :returns (,field.name ,field.pred
			     ,@(and (not field.fullp)
				    `(:hints (("goal" :in-theory
					       (enable ,x.fix
						       part-select-at-0-of-unsigned-byte-identity
						       logext-part-select-at-0-identity))))))
       :no-function t
       ,@(and x.inline `(:inline ,x.inline))

       :parents (,x.name)
       :short ,short
       ;; :progn t
       ,@(and field.subfield-hierarchy '(:enabled t))
       :guard-hints
       (("goal" :in-theory
	 (enable
	  ,@(and (not field.fullp) `(,x.pred))
	  ,@(and (eql field.width 1)
		 '(part-select-is-logbit
		   logbit-at-zero-is-loghead-of-1
		   unsigned-byte-p-of-bool->bit
		   signed-byte-p-of-bool->bit))
	  part-select-width-low-in-terms-of-loghead-and-logtail
          remove-inner-logext-from-logext-logtail-nest
          remove-outer-logtail-from-logtail-logext-nest
	  . ,subfield-accs)))
       ;; ,@(cond ((eql field.width 1)
       ;;          `(:guard-hints (("goal" :in-theory (enable part-select-is-logbit
       ;;                                                     . ,subfield-accs)))))
       ;;         ((not field.fullp)
       ;;          `(:guard-hints (("goal" :in-theory (enable ,x.pred))))))

       (mbe :logic (let ((,x.xvar (,x.fix ,x.xvar)))
		     ,logic-form)
	    :exec ,exec-form)
       ///
       (acl2::add-to-ruleset ,x.defs-ruleset ,field.accessor)
       (fty::deffixequiv ,field.accessor)

       ,@(and
	  (not field.subfield-hierarchy)
	  `((defthm ,(intern-in-package-of-symbol
		      (cat (symbol-name field.accessor) "-OF-" (symbol-name x.name))
		      x.name)
	      (equal (,field.accessor (,x.name . ,fieldnames))
		     ,(if field.subfield-hierarchy
			  (bitstruct-subfield-accessor-form
			   (butlast field.subfield-hierarchy 1)
			   (bitstruct-field->name (car (last field.subfield-hierarchy))))
			`(,field.fix ,field.name)))
	      ,@(and (not field.subfield-hierarchy)
		     `(:hints(("Goal" :in-theory (enable ,x.name
							 ,@(and (not x.fullp)
								`(,x.fix
								  part-select-at-0-of-unsigned-byte-identity))))
			      (and stable-under-simplificationp
				   '(:in-theory (enable logext-part-select-at-0-identity
							acl2::logext-identity)))))))

	    (local (in-theory (enable equal-of-bool->bit)))

	    (local
             (acl2::without-waterfall-parallelism ; because of bitstruct-logbitp-reasoning
              (defthm defbitstruct-write-with-mask-lemma
                (implies (,x.equiv-under-mask ,x.xvar y ,(ash (logmask field.width) field.lsb))
                         (equal (,field.accessor ,x.xvar)
                                (,field.accessor y)))
                :hints (("goal" :in-theory (enable ,x.equiv-under-mask
                                                   int-equiv-under-mask
                                                   equal-of-bit->bool
                                                   logand-mask-logxor-equal-0
                                                   logand-const-of-logapp
                                                   ,@(and (not field.fullp)
                                                          `(,x.fix))
                                                   . ,subfield-accs))
                        (bitstruct-logbitp-reasoning)
                        (and stable-under-simplificationp
                             '(:in-theory (enable bool->bit))))
                :rule-classes nil)))


	    ;; ,@(and (not field.fullp)
	    ;;        `((local
	    ;;           (defthm defbitstruct-write-with-mask-lemma
	    ;;             (implies (and (,x.equiv-under-mask ,x.xvar y mask)
	    ;;                           (equal (logand (lognot mask) ,(ash (logmask field.width) field.lsb)) 0))
	    ;;                      (equal ,(bitstruct-accessor-term-logic-form field x.xvar)
	    ;;                             ,(bitstruct-accessor-term-logic-form field 'y)))
	    ;;             :hints (("goal" :in-theory (enable ,x.equiv-under-mask
	    ;;                                                int-equiv-under-mask
	    ;;                                                equal-of-bit->bool
	    ;;                                                ,x.fix
	    ;;                                                . ,subfield-accs))
	    ;;                     (bitstruct-logbitp-reasoning))
	    ;;             :rule-classes nil))))

	    (defthm ,(intern-in-package-of-symbol
		      (cat (symbol-name field.accessor) "-OF-WRITE-WITH-MASK")
		      x.name)
	      (implies (and (bitstruct-read-over-write-hyps ,x.xvar ,x.equiv-under-mask)
			    (,x.equiv-under-mask ,x.xvar y mask)
			    (equal (logand (lognot mask) ,(ash (logmask field.width) field.lsb)) 0))
		       (equal (,field.accessor ,x.xvar)
			      (,field.accessor y)))
	      :hints (("goal" :in-theory (enable ,x.equiv-under-mask
						 int-equiv-under-mask-of-submask)
		       :use defbitstruct-write-with-mask-lemma))
	      ;; :hints (("goal" :in-theory (enable ,x.equiv-under-mask
	      ;;                                    int-equiv-under-mask
	      ;;                                    equal-of-bit->bool
	      ;;                                    logand-mask-logxor-equal-0
	      ;;                                    ,@(and (not field.fullp)
	      ;;                                           `(,x.fix))
	      ;;                                    . ,subfield-accs))
	      ;;         (bitstruct-logbitp-reasoning))
	      ))))))


(define bitstruct-subfield-updater-form-aux (hier subfield-term xvar)
  ;; (b* ((b (a->b a))
  ;;      (b1 (b* ((c (b->c b))
  ;;               (c1 (b* ((d (c->d c))
  ;;                        (d1 (!d->e e d)))
  ;;                     (!c->d d1 c))))
  ;;            (!b->c c1 b))))
  ;;   (!a->b b1 a))

  ;; innermost first.  we need to pass in the term (!d->e e d) at the top
  ;; level, then we're starting with field d with accessor/updater c->d, !c->d.
  ;; We peek up the hierarchy to get the variable name (c) to operate on (at
  ;; the top level it's xvar).
      (b* (((bitstruct-field field) (car hier))
	   (name1 (intern-in-package-of-symbol
		   (cat (symbol-name field.name) "1") field.name))
	   ((when (atom (cdr hier)))
	    `(b* ((,field.name (,field.accessor ,xvar))
		  (,name1 ,subfield-term))
	       (,field.updater ,name1 ,xvar)))
	   (next-var (bitstruct-field->name (cadr hier)))
	   (next-term
	    `(b* ((,field.name (,field.accessor ,next-var))
		  (,name1 ,subfield-term))
	       (,field.updater ,name1 ,next-var))))
	(bitstruct-subfield-updater-form-aux (cdr hier) next-term xvar)))

(define bitstruct-subfield-updater-form (hier field-var xvar)
  (b* (((bitstruct-field field) (car hier))
       (next-var (bitstruct-field->name (cadr hier)))
       (next-term `(,field.updater ,field-var ,next-var)))
    (bitstruct-subfield-updater-form-aux (cdr hier) next-term xvar)))





;; (define bitstruct-subfield-updater-form (hier ;; outermost first
;;                                          valname xvar)
;;   ;; (b* ((b (a->b a))
;;   ;;      (c (b->c b))
;;   ;;      (d (c->d c))
;;   ;;      (d1 (!d->e e d))
;;   ;;      (c1 (!c->d d1 c))
;;   ;;      (b1 (!b->c c1 b)))
;;   ;;   (!a->b b1 a))

;;   ;; but properly nested like:
;;   ;; (b* ((b (a->b a))
;;   ;;      (b1 (b* ((c (b->c b))
;;   ;;               (c1 (b* ((d (c->d c))
;;   ;;                        (d1 (!d->e e d)))
;;   ;;                     (!c->d d1 c))))
;;   ;;            (!b->c c1 b))))
;;   ;;   (!a->b b1 a))

;;   (b* (((bitstruct-field field) (car hier))
;;        (subterm
;;         (if (atom (cdr hier))
;;             `(,field.updater ,valname ,xvar)
;;           (bitstruct-subfield-updater-form (cdr hier) valname field.name)))
;;        (name1 (intern-in-package-of-symbol
;;                (cat (symbol-name field.name) "1") field.name)))
;;     `(b* ((,field.name (,field.accessor ,xvar))
;;           (,name1 ,subterm))
;;        (,field.updater ,name1 ,field.name))))



(define bitstruct-subfield-updater-fns (hier)
  (b* (((when (atom hier)) nil)
       ((bitstruct-field field) (car hier)))
    (cons field.updater
	  (bitstruct-subfield-updater-fns (cdr hier)))))

(define bitstruct-updater-term-exec-form (fullwidth fullsignedp field xvar)
  (b* (((bitstruct-field field))
       (field-type (if field.signedp 'signed-byte 'unsigned-byte))
       (full-type (if fullsignedp 'signed-byte 'unsigned-byte))
       (mask (lognot (ash (logmask field.width) field.lsb)))
       (field-msb (+ field.lsb field.width))
       (mask-size (+ 1 field-msb))
       (fname (if (eq field.pred 'booleanp)
		  `(bool->bit ,field.name)
		field.name))
       (exec-form-ash-base
	(cond
	 ((eql field.lsb 0)
	  (if field.signedp
	      `(the (unsigned-byte ,field.width)
		 (logand ,(1- (expt 2 field.width))
			 (the (,field-type ,field.width) ,fname)))
	    `(the (,field-type ,field.width) ,fname)))
	 (field.signedp
	  `(the (unsigned-byte ,field-msb)
	     (ash
	      (the (unsigned-byte ,field.width)
		(logand ,(1- (expt 2 field.width))
			(the (,field-type ,field.width) ,fname)))
	      ,field.lsb)))
	 (t
	  `(the (,field-type ,field-msb)
	     (ash (the (,field-type ,field.width) ,fname)
		  ,field.lsb)))))
       (exec-form
	(let ((new-fullwidth
	       (if fullsignedp
		   (max fullwidth mask-size)
		 fullwidth)))
	  `(the (,full-type ,new-fullwidth)
	     (logior
	      (the (,full-type ,new-fullwidth)
		(logand
		 (the (,full-type ,fullwidth) ,xvar)
		 (the (signed-byte ,mask-size) ,mask)))
	      ,exec-form-ash-base)))))
    exec-form))

(define bitstruct-field-updater (field x)
  (b* (((bitstruct x))
       ((bitstruct-field field))
       (short (cat "Update the " (xdoc::full-escape-symbol field.name)
		   " field of a @(see " (xdoc::full-escape-symbol x.name)
		   ") bit structure."))
       ;; (first-field (equal field.lsb 0))
       (last-field (equal (+ field.lsb field.width) x.width))
       ;; (update-form
       ;;  (cond ((and first-field last-field)
       ;;         `(acl2::logext ,field.width ,field.name))
       ;;        (first-field
       ;;         `(acl2::logapp ,field.width ,field.name
       ;;                        (acl2::logtail ,field.width ,x.xvar)))
       ;;        (last-field
       ;;         `(acl2::logapp ,field.lsb ,x.xvar
       ;;                        ,(cond ((eq field.signedp x.signedp) field.name)
       ;;                               (x.signedp `(acl2::logext ,field.width ,field.name))
       ;;                               (t         `(acl2::loghead ,field.width ,field.name)))))
       ;;        (t
       ;;         `(acl2::logapp ,field.lsb ,x.xvar
       ;;                        (acl2::logapp ,field.width ,field.name
       ;;                                      (acl2::logtail ,(+ field.width field.lsb) ,x.xvar))))))
       (logic-form-base `(bitops::part-install ,field.name ,x.xvar :width ,field.width :low ,field.lsb))
       ;; (exec-form-base (if (eql field.width 1)
       ;;                     `(install-bit ,field.lsb ,field.name ,x.xvar)
       ;;                   logic-form-base))
       ;; (exec-form (if (eq field.pred 'booleanp)
       ;;                `(let ((,field.name (acl2::bool->bit ,field.name)))
       ;;                   ,exec-form-base)
       ;;              exec-form-base))
       (exec-form
	(bitstruct-updater-term-exec-form x.width x.signedp field x.xvar))

       (body (if field.subfield-hierarchy
		 `(mbe :logic ,(bitstruct-subfield-updater-form  field.subfield-hierarchy field.name x.xvar)
		       :exec ,(if (and last-field x.signedp (not field.signedp))
				  `(fast-logext ,x.width ,exec-form)
				exec-form))
	       (b* ((body-base `(mbe :logic (b* ((,field.name ,(if (eq field.pred 'booleanp)
								   `(acl2::bool->bit ,field.name)
								 `(mbe :logic (,field.fix ,field.name) :exec ,field.name)))
						 (,x.xvar (,x.fix ,x.xvar)))
					      ,logic-form-base)
				     :exec ,exec-form)))
		 (if (and last-field x.signedp)
		     `(fast-logext ,x.width ,body-base)
		   body-base))))

       (subfield-fns (append (bitstruct-subfield-accessor-fns field.subfield-hierarchy)
			     (bitstruct-subfield-updater-fns field.subfield-hierarchy)))


       (new-x (intern-in-package-of-symbol (cat "NEW-" (symbol-name x.xvar)) x.name))
       (type-incr-rule (if x.signedp
			   'bitops::signed-byte-p-incr
			 'bitops::unsigned-byte-p-incr))
       (type-incr-use-hint-1
	`((:instance ,type-incr-rule
		     (a ,(if (and x.signedp (eql field.width 1))
			     (+ 1 field.width)
			   field.width))
		     (x ,(if (eq field.pred 'booleanp)
			     `(bool->bit ,field.name)
			   field.name))
		     (b ,(- x.width field.lsb)))))
       (type-incr-use-hint-2
	`((:instance ,type-incr-rule
		     (a ,(if (and x.signedp (eql field.width 1))
			     (+ 1 field.width)
			   field.width))
		     (x ,(if (eq field.pred 'booleanp)
			     `(bool->bit ,field.name)
			   field.name))
		     (b ,x.width))))
       (type-incr-use-hint-3
	`((:instance ,type-incr-rule
		     (a ,x.width)
		     (x ,x.xvar)
		     (b ,(+ 1 x.width))))))
    `(define ,field.updater ((,field.name ,field.pred)
			     (,x.xvar ,x.pred))
       :returns (,new-x ,x.pred
			,@(and (not x.fullp)
			       `(:hints (("goal" :in-theory (enable ,x.pred ,x.fix
								    part-select-at-0-of-unsigned-byte-identity
								    logext-part-select-at-0-identity))))))
       :no-function t
       ,@(and x.inline `(:inline ,x.inline))
       :parents (,x.name)
       :short ,short
       :progn t
       ,@(and field.subfield-hierarchy '(:enabled t))
       :guard-hints ;; ,(if field.subfield-hierarchy
		    ;;      `(("goal" :in-theory (enable part-select-at-0-of-unsigned-byte-is-x
		    ;;                                   install-bit-is-part-install
		    ;;                                   . ,subfield-fns)))
		    ;;    `(("goal" :in-theory (enable install-bit-is-part-install))))
       (("goal"
	 :in-theory
	 (e/d
	  (part-install-width-low-in-terms-of-logior-logmask-ash
           ,@(and (eql field.width 1)
		  '(logbit-at-zero-is-loghead-of-1
		    unsigned-byte-p-of-bool->bit
		    signed-byte-p-of-bool->bit))
	   ,@(and (or x.signedp field.signedp)
		  '(signed-byte-p-+1
		    signed-byte-p-one-bigger-when-unsigned-byte-p))
	   ,@(and field.subfield-hierarchy
                  `(,@subfield-fns
                    simplify-subfield-updater-guard-expression-with-inner-logext
                    simplify-subfield-updater-guard-expression-with-more-logext
                    remove-inner-logext-from-logext-logtail-nest)))
	  (,type-incr-rule
	   bitops::logand-with-negated-bitmask
	   ,@(and (eql field.width 1)
		  (if x.signedp
		      '(signed-byte-p-2-when-bitp)
		    '(unsigned-byte-p-1-when-bitp)))))
	 :use
	 (,@type-incr-use-hint-1
	  ,@type-incr-use-hint-2
	  ,@type-incr-use-hint-3
	  ,@(and (eql field.width 1)
		 `((:instance
		    ,@(if x.signedp
			  `(signed-byte-p-2-when-bitp (x ,field.name))
			`(unsigned-byte-p-1-when-bitp (x ,field.name)))))))))
       ,body
       ///
       (acl2::add-to-ruleset ,x.defs-ruleset ,field.updater)
       (fty::deffixequiv ,field.updater)

       ,@(and
	  (not field.subfield-hierarchy)
	  `((defthmd ,(intern-in-package-of-symbol
			  (cat (symbol-name field.updater) "-IS-" (symbol-name x.name))
			  x.name)
		  (equal (,field.updater ,field.name ,x.xvar)
			 (,(std::da-changer-name x.name) ,x.xvar
			  ,(intern$ (symbol-name field.name) "KEYWORD") ,field.name))
		  :hints(("Goal" :in-theory (enable ,x.name
						    ,(intern-in-package-of-symbol
						      (cat (symbol-name x.fix) "-IN-TERMS-OF-" (symbol-name x.name))
						      x.name)))
			 (and stable-under-simplificationp
			      '(:in-theory (enable part-install-identity
						   part-install-identity-signed
						   acl2::loghead-identity
						   bitops::cancel-loghead-under-logext)))
			 ;; (bitstruct-logbitp-reasoning)
			 ))

	    (defret ,(intern-in-package-of-symbol
			  (cat (symbol-name field.accessor) "-OF-" (symbol-name field.updater))
			  x.name)
		  (equal (,field.accessor ,new-x)
			 (,field.fix ,field.name))
		  :hints(("Goal" :in-theory (e/d (,field.accessor)
						 (,field.updater))) ;; allow the fixing to cancel
			 (and stable-under-simplificationp
			      '(:in-theory (enable ,field.updater)))
			 ;; (bitstruct-logbitp-reasoning)
			 ))

            (acl2::without-waterfall-parallelism ; because of bitstruct-logbitp-reasoning
             (defret ,(intern-in-package-of-symbol
                       (cat (symbol-name field.updater) "-EQUIV-UNDER-MASK")
                       x.name)
               (,x.equiv-under-mask ,new-x ,x.xvar
                                    ,(if last-field
                                         (lognot (ash -1 field.lsb))
                                       (lognot (ash (logmask field.width) field.lsb))))
               :hints(("Goal" :in-theory (e/d (,x.equiv-under-mask
                                               int-equiv-under-mask)
                                              (,field.updater)))
                      (and stable-under-simplificationp
                           '(:in-theory (enable ,field.updater)))
                      (bitstruct-logbitp-reasoning)))))))))


(define bitstruct-field-accessors (fields x)
  (if (atom fields)
      nil
    (cons (bitstruct-field-accessor (car fields) x)
	  (bitstruct-field-accessors (cdr fields) x))))

(define bitstruct-field-updaters (fields x)
  (if (atom fields)
      nil
    (cons (bitstruct-field-updater (car fields) x)
	  (bitstruct-field-updaters (cdr fields) x))))


(define bitstruct-debug-field-pairs (fields x)
  (b* (((when (atom fields)) nil)
       ((bitstruct x))
       ((bitstruct-field field) (car fields)))
    `(cons (cons ',field.name ,(intern-in-package-of-symbol
				(str::cat (symbol-name x.xvar) "." (symbol-name field.name))
				x.name))
	   ,(bitstruct-debug-field-pairs (cdr fields) x))))

(define bitstruct-debugger (x)
  (b* (((bitstruct x))
       (debug (intern-in-package-of-symbol
	       (cat (symbol-name x.name) "-DEBUG") x.name)))
    `(define ,debug ((,x.xvar ,x.pred))
       (b* (((,x.name ,x.xvar)))
	 ,(bitstruct-debug-field-pairs x.fields x)))))

;; BOZO redundant with docgen.lisp
(defun html-encode-str (x acc)
  (xdoc::simple-html-encode-str x 0 (length x) acc))

(define bitstruct-field-xdoc (field acc state)
  (b* (((bitstruct-field field))
       (acc (revappend-chars "<dt>" acc))
       ((mv name-str state) (xdoc::fmt-to-str-orig field.name field.name state))
       (acc (html-encode-str name-str acc))
       (acc (b* (((when (eq field.type nil))
		  acc)
		 ;; (fixtype (find-fixtype field.type (get-fixtypes-alist (w state))))
		 ;; (target  (if fixtype
		 ;;              (fixtype->topic fixtype)
		 ;;            field.type))
		 ;; (acc (revappend-chars " &mdash; @(see? " acc))
		 ;; (acc (revappend-chars (xdoc::full-escape-symbol target) acc))
		 (acc (revappend-chars " &mdash; @(see? " acc))
		 (acc (revappend-chars (xdoc::full-escape-symbol field.type) acc))
		 (acc (revappend-chars ")" acc)))
	      acc))
       (acc (revappend-chars "</dt>" acc))
       (acc (cons #\Newline acc))
       (acc (b* (((when (or (not field.doc)
			    (equal field.doc "")))
		  acc)
		 (acc (revappend-chars "<dd>" acc))
		 (acc (revappend-chars field.doc acc))
		 (acc (revappend-chars "</dd>" acc))
		 (acc (cons #\Newline acc)))
	      acc))
       (acc (cons #\Newline acc)))
    (mv acc state)))

(define bitstruct-fields-xdoc (fields acc state)
  (b* (((when (atom fields))
	(mv acc state))
       ((mv acc state) (bitstruct-field-xdoc (car fields) acc state)))
    (bitstruct-fields-xdoc (cdr fields) acc state)))

(define bitstruct-xdoc-long (x state)
  (b* (((bitstruct x))
       (long (or (cdr (assoc :long x.kwd-alist)) ""))
       (acc nil)
       (acc (revappend-chars "<p>This is a bitstruct type introduced by @(see fty::defbitstruct)," acc))
       (acc (revappend-chars " represented as a " acc))
       (acc (revappend-chars (if x.signedp "signed " "unsigned ") acc))
       (acc (revappend-chars (str::natstr x.width) acc))
       (acc (revappend-chars "-bit integer.</p>" acc))
       (acc (cons #\Newline acc))
       ((mv acc state)
	(if (consp x.fields)
	    (b* ((acc (revappend-chars "<h5>Fields</h5>" acc))
		   (acc (cons #\Newline acc))
		   (acc (revappend-chars "<dl>" acc))
		   ((mv acc state) (bitstruct-fields-xdoc x.fields acc state))
		   (acc (revappend-chars "</dl>" acc)))
		(mv acc state))
	      (mv (revappend-chars "<p>This is an atomic/empty structure; it has no fields.</p>" acc)
		state)))
       (acc (revappend-chars long acc))
       (long (rchars-to-string acc)))
    (mv long state)))

(define bitstruct-events (x state)
  (b* (((bitstruct x))
       ((mv long state) (bitstruct-xdoc-long x state))
       (field-accs (pairlis$ (bitstruct-fields->names x.fields)
			     (bitstruct-fields->accessors x.fields)))
       (binder-alist (append field-accs
			     (extra-binder-names->acc-alist (cdr (assoc :extra-binder-names x.kwd-alist)) x.name))))

    (value
     `(with-output
        :off (event acl2::prove)
        :summary-off (:other-than acl2::form time)
        (defsection ,x.name
          :parents ,(or (cdr (assoc :parents x.kwd-alist))
                        (xdoc::get-default-parents (w state))
                        '(acl2::undocumented))
          :short ,(or (cdr (assoc :short x.kwd-alist))
                      (cat "An " (str::natstr x.width) "-bit "
                           (if x.signedp "signed" "unsigned")
                           " bitstruct type."))
          :long ,long
          (set-inhibit-warnings "non-rec" "disable" "subsume") ;; implicitly local
          (local (include-book "centaur/bitops/ihsext-basics" :dir :system))
          (local (include-book "centaur/bitops/equal-by-logbitp" :dir :system))
          (local (include-book "arithmetic/top-with-meta" :dir :system))
          (local (in-theory (disable unsigned-byte-p signed-byte-p
                                     part-select part-install
                                     acl2::bit->bool)))
          ,(bitstruct-pred x)
          ,(bitstruct-fix x)
          ,@(and (consp x.fields)
                 (list `(def-ruleset! ,x.defs-ruleset nil)
                       (bitstruct-ctor x)
                       (bitstruct-equiv-under-mask x)))
          ,@(bitstruct-field-accessors x.fields x)
          ,@(and (Consp x.fields)
                 `((defthmd ,(intern-in-package-of-symbol
                              (cat (symbol-name x.fix) "-IN-TERMS-OF-" (symbol-name x.name))
                              x.name)
                     (equal (,x.fix ,x.xvar)
                            (,(std::da-changer-name x.name) ,x.xvar))
                     :hints(("Goal" :in-theory (enable ,x.fix ,x.name . ,(bitstruct-fields->accessors x.fields)))
                            (and stable-under-simplificationp
                                 '(:in-theory (enable logext-part-select-at-0-identity
                                                      part-select-at-0-of-unsigned-byte-identity)))
;; (bitops::logbitp-reasoning)
                            ))))
          ,@(bitstruct-field-updaters x.fields x)
          ,@(and (consp x.fields)
                 `((acl2::def-b*-binder ,x.name
                     :body
                     (std::da-patbind-fn ',x.name
                                         ',binder-alist
                                         acl2::args acl2::forms acl2::rest-expr))
                   ,(bitstruct-debugger x)))
          (table bitstruct-table ',x.name ',x))))))

(define defbitstruct-fn (args state)
  (b* ((bitstruct-table (table-alist 'bitstruct-table (w state)))
       (x (parse-defbitstruct args bitstruct-table)))
    (bitstruct-events x state)))

(defmacro defbitstruct (&rest args)
  `(make-event (defbitstruct-fn ',args state)))


(defxdoc defbitstruct
  :parents (fty)
  :short "Define a bitvector type with accessors for its fields."
  :long "<p>This macto defines a bitstruct type.  A bitstruct can either be a
base type, which is a single fixed-width integer, or a product type containing
fields that are bits, Booleans, or other bitstructs.  Such a product is
represented as a single integer produced by concatenating all the fields
together, where the first field is least significant.</p>

<h5>Examples:</h5>

<p>A bitstruct can be made up of single bits and Booleans.  (The difference is
only in the return type of the accessors and the input type of the updaters;
the representation is the same.)  The fields are ordered LSB first, so @('a')
is bit 0 of the representation and @('c') is bit 2.  This defines a predicate,
fixing function, accessors, and a constructor similar to @('defprod'), but also
updaters such as @('!foo->a').</p> @({
 (defbitstruct foo
   ((a bitp)
    (b booleanp)
    (c bitp)))
})

<p>A bitstruct can also contain fields that are other bitstructs.  Here, the
first field is a @('foo'), which is three bits wide, so the @('b') and @('c')
fields are bits 3 and 4, respectively.  Also, since @(':signedp t') was
specified, the representation is signed: the product is represented as a 5-bit
signed integer rather than a 5-bit natural.</p>
@({
 (defbitstruct bar
   ((myfoo foo-p)
    (b booleanp)
    (c bitp))
   :signedp t)
 })

<p>A bitstruct can also be defined without any fields, giving only a
width. These are mainly useful as fields of other bitstructs.  This makes sense
when the individual bits aren't meaningful, and their combined value is what's
important.  This defines a rounding-control as a 2-bit unsigned value.</p>
@({
 (defbitstruct rounding-control 2)
 })

<p>Sometimes we may want to nest one bitstruct inside another, but also
directly access the fields of the internal struct.  Providing the
@(':subfields') keyword causes defbitstruct to produce direct accessors and
updaters for the subfields of the nested struct.  The following definition of
@('mxcsr') produces the usual accesors and updaters including @('mxcsr->flags')
and @('mxcsr->masks'), but also @('mxcsr->ie') and @('mxcsr->im'), etc.</p>
@({
 (defbitstruct fp-flags
   ((ie bitp)
    (de bitp)
    (ze bitp)
    (oe bitp)
    (ue bitp)
    (pe bitp)))

 (defbitstruct mxcsr
   ((flags fp-flags :subfields (ie de ze oe ue pe))
    (daz bitp)
    (masks fp-flags :subfields (im dm zm om um pm))
    (rc  rounding-control)
    (ftz bitp)))
 })

<h5>Syntax</h5>
<p>A @('defbitstruct') form is one of:</p>
@({
 (defbitstruct typename fields [ options ] )
 })
<p>or</p>
@({
 (defbitstruct typename width [ options ] ).
 })
<p>The syntax of fields is described below.</p>

<h5>Top-level options</h5>

<ul>

<li>@(':pred'), @(':fix'), @(':equiv') -- override the default names (foo-p,
foo-fix, and foo-equiv) for the predicate, fixing function, and equivalence
relation.</li>

<li>@(':parents'), @(':short'), @(':long') -- provide xdoc for the bitstruct</li>

<li>@(':signedp') -- when true, represents the structure as a signed integer
rather than an unsigned one.  (Signed and unsigned fields can be used inside
unsigned and signed bitstructs -- they are simply sign- or zero-extended as
necessary when accessed.)</li>

</ul>

<h5>Field Syntax</h5>
<p>A field has the following form:</p>
@({
 (fieldname type [ docstring ] [ options ... ] )
 })

<p>The type can be either a predicate or type name, i.e., @('bit') or
@('bitp'), and must refer to either a single-bit type (bit or boolean) or a
previously-defined bitstruct type.  The docstring is a string which may contain
xdoc syntax.</p>

<h5>Field Options</h5>
<ul>

<li>@(':accessor'), @(':updater') -- override the default names
@('struct->field'), @('!struct->field') for the accessor and updater
functions.</li>

<li>@(':default') -- change the default value for the field in the
@('make-foo') macro.  The default default is NIL for Boolean fields and 0 for
everything else.</li>

<li>@(':rule-classes') -- override the rule classes of the accessor function's
return type theorem.  The default is @(':rewrite'); it may be appealing to use
@(':type-prescription'), but typically the type prescription for the accessor
should be determined automatically anyway.</li>

<li>@(':subfields') -- Indicates that accessors and updaters should be created
for subfields of this field, and gives their subfield names.  See the section
on subfields below.</li> </ul>

<h5>Subfields</h5>

<p>The @(':subfields') field option may only be used on a field whose type is
itself a bitstruct type containing fields.  The value of the @(':subfields')
argument should be a list of @('subfield_entries'), according to the following
syntax:</p>
 @({ subfield_entry ::= name | ( name ( subfield_entry ... ) ) })

<p>Each top-level entry corresponds to a subfield of the field type.  If the
entry uses the second syntax, which itself has a list of entries, those entries
correspond to sub-subfields of the subfield type.  For example:</p>

@({
 (defbitstruct innermost
   ((aa bitp)
    (bb bitp)))

 (defbitstruct midlevel
   ((ii innermost :subfields (iaa ibb))
    (qq bitp)
    (jj innermost :subfields (jaa jbb))))

 (defbitstruct toplevel
   ((ss innermost :subfields (saa sbb))
    (tt midlevel  :subfields ((tii (tiaa tibb))
                              tqq
                              tjj))))
 })

<p>For the @('toplevel') bitstruct, this generates the following subfield
accessors, in addition to the direct accessors @('toplevel->ss') and
@('toplevel->tt'):</p>

@({
 (toplevel->saa x)    == (innermost->aa (toplevel->ss x))
 (toplevel->sbb x)    == (innermost->bb (toplevel->ss x))
 (toplevel->tii x)    == (midlevel->ii (toplevel->ss x))
 (toplevel->tiaa x)   == (innermost->aa (midlevel->ii (toplevel->tt x)))
 (toplevel->tibb x)   == (innermost->bb (midlevel->ii (toplevel->tt x)))
 (toplevel->tqq x)    == (midlevel->qq (toplevel->tt x))
 (toplevel->tjj x)    == (midlevel->jj (toplevel->tt x))
 })
")


(defconst *fixtype-to-bitstruct-keywords*
  '(:width :signedp :fullp))

(define fixtype-to-bitstruct-fn (name args wrld)
  (b* (((fixtype fty) (find-fixtype name (get-fixtypes-alist wrld)))
       ((mv kwd-alist rest) (extract-keywords name *fixtype-to-bitstruct-keywords*
					      args nil))
       ((when rest)
	(raise "Extra arguments to fixtype-to-bitstruct: ~x0" rest))
       (width (cdr (assoc :width kwd-alist)))
       ((unless width)
	(raise "Must specify :width for fixtype-to-bitstruct"))
       (signedp (getarg :signedp nil kwd-alist))
       (fullp (getarg :fullp nil kwd-alist))
       (bitstruct (make-bitstruct :name fty.name
				  :pred fty.pred
				  :fix fty.fix
				  :equiv fty.equiv
				  :width width
				  :signedp signedp
				  :fullp fullp)))
    `(table bitstruct-table ',fty.name ',bitstruct)))

(defmacro fixtype-to-bitstruct (name &rest args)
  `(make-event (fixtype-to-bitstruct-fn ',name ',args (w state))))




(logic)






#||

(logic)

(local (include-book "centaur/bitops/ihsext-basics" :dir :System))



(defbitstruct foo
  ((a bitp)
   (b booleanp)
   (c bitp)))
(defbitstruct bar
  ((a bitp)
   (b booleanp)
   (c foo-p)
   (d bitp))
  :signedp t)

(defbitstruct signed3 3 :signedp t)
(defbitstruct unsigned5 5)

(defbitstruct baz
  ((a foo-p)
   (b signed3-p)
   (c unsigned5-p)
   (d bar-p)))

(defbitstruct rc 2)

(defbitstruct fp-flags
  ((ie bitp)
   (de bitp)
   (ze bitp)
   (oe bitp)
   (ue bitp)
   (pe bitp)))

(defbitstruct mxcsr
  ((flags fp-flags
	  :subfields (ie de ze oe ue pe))
   (daz bitp)
   (masks fp-flags
	  :subfields (im dm zm om um pm))
   (rc  rc)
   (ftz bitp)))

;; (defbitstruct mxcsr
;;   ((ie bitp)
;;    (de bitp)
;;    (ze bitp)
;;    (oe bitp)
;;    (ue bitp)
;;    (pe bitp)
;;    (daz bitp)
;;    (im bitp)
;;    (dm bitp)
;;    (zm bitp)
;;    (om bitp)
;;    (um bitp)
;;    (pm bitp)
;;    (rc  rc)
;;    (ftz bitp)))

(define ternary-p (x)
  (and (natp x)
       (<= x 2))
  ///
  (defthm unsigned-byte-2-when-ternary-p
    (implies (ternary-p x)
	     (unsigned-byte-p 2 x)))

  (defthm ternary-p-compound-recognizer
    (implies (ternary-p x)
	     (natp x))
    :rule-classes :compound-recognizer))

(define ternary-fix ((x ternary-p))
  :prepwork ((local (in-theory (enable ternary-p))))
  :returns (xx ternary-p
	       :rule-classes (:rewrite (:type-prescription :typed-term xx)))
  (if (ternary-p x) x 0)
  ///
  (defthm ternary-fix-when-ternary-p
    (implies (ternary-p x)
	     (equal (ternary-fix x) x)))

  (defthm unsigned-byte-p-of-ternary-fix
    (unsigned-byte-p 2 (ternary-fix x)))

  (fty::deffixtype ternary :pred ternary-p :fix ternary-fix :equiv ternary-equiv :define t :forward t))

(fixtype-to-bitstruct ternary :width 2)
;; (table bitstruct-table
;;        'ternary
;;        (fty::make-bitstruct :name 'ternary
;;                             :pred 'ternary-p
;;                             :fix 'ternary-fix
;;                             :equiv 'ternary-equiv
;;                             :width 2
;;                             :fullp nil))

(defbitstruct fafaf
  ((a ternary)
   (b baz)
   (c bit)
   (d ternary)
   (e boolean)
   (f ternary)))

(defbitstruct fafafa
  :signedp t
  ((a ternary)
   (b baz)
   (c bit)
   (d ternary)
   (e boolean)
   (f ternary)))

(defbitstruct bababa
  :signedp t
  ((a rc)
   (b baz)
   (c bit)
   (d rc)
   (e boolean)
   (f rc)))




(define sternary-p (x)
  (or (equal x 0)
      (equal x 1)
      (equal x -1))
  ///
  (defthm signed-byte-2-when-sternary-p
    (implies (sternary-p x)
	     (signed-byte-p 2 x)))

  (defthm sternary-p-compound-recognizer
    (implies (sternary-p x)
	     (and (integerp x)
		  (<= x 1)))
    :rule-classes :compound-recognizer))

(define sternary-fix ((x sternary-p))
  :prepwork ((local (in-theory (enable sternary-p))))
  :returns (xx sternary-p
	       :rule-classes (:rewrite (:type-prescription :typed-term xx)))
  (if (sternary-p x) x 0)
  ///
  (defthm sternary-fix-when-sternary-p
    (implies (sternary-p x)
	     (equal (sternary-fix x) x)))

  (defthm signed-byte-p-of-sternary-fix
    (signed-byte-p 2 (sternary-fix x)))

  (fty::deffixtype sternary :pred sternary-p :fix sternary-fix :equiv sternary-equiv :define t :forward t))

(fixtype-to-bitstruct sternary :width 2 :signedp t)
;; (table bitstruct-table
;;        'sternary
;;        (fty::make-bitstruct :name 'sternary
;;                             :pred 'sternary-p
;;                             :fix 'sternary-fix
;;                             :equiv 'sternary-equiv
;;                             :signedp t
;;                             :width 2
;;                             :fullp nil))

(defbitstruct afafaf
  ((a sternary)
   (b baz)
   (c bit)
   (d sternary)
   (e boolean)
   (f sternary)))

(defbitstruct afafafa
  :signedp t
  ((a sternary)
   (b baz)
   (c bit)
   (d sternary)
   (e boolean)
   (f sternary)))

(defbitstruct s2 2 :signedp t)

(defbitstruct abababa
  :signedp t
  ((a s2)
   (b baz)
   (c bit)
   (d s2)
   (e boolean)
   (f s2)))

||#
