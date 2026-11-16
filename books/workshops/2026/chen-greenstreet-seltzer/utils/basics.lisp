;; Copyright (C) 2015, University of British Columbia
;; Written by Yan Peng (June 25th 2019)
;;
;; License: A 3-clause BSD license.
;; See the LICENSE file distributed with ACL2
;;
(in-package "SMT")
(include-book "centaur/fty/top" :dir :system)
(include-book "xdoc/top" :dir :system)
(include-book "std/util/define" :dir :system)
(include-book "std/strings/cat" :dir :system)

;; (symcat [sym0 ...]) is a macro for "concatenating" atoms into a symbol
;; (symcat) returns nil
;; Otherwise, we concatenate the strings for each atom in the list of arguments
;;   and intern a symbol in the same package as sym0.
;; If (symbol-name sym0) is "IGNORE", then we still use it to determine the
;;   package in which to intern the symbol we create, but we ignore it when
;;   constructing the symbol name.  For example,
;;     (symcat :IGNORE a 2 b)
;;   returns the symbol :a2b.  If you really want to create a symbol whose
;;   name starts with "IGNORE" you can just say "IGNORE" twice, only the 
;;   first one is ignored.  For example,
;;     (symcat 'IGNORE 'IGNORE 42)
;;   returns the symbol 'IGNORE42 in the current package.  
;;
;; BOZO: Other developers must need a function similar to this.  If I find
;;   such a function in the community books, I'll be happy to use it.
(defun symcat-fn (syms)
  (if (consp syms)
    (cons (list 'explode-atom (car syms) 10) (symcat-fn (cdr syms)))
    nil))

(defmacro symcat (&rest syms)
  (if (consp syms)
    (list 'if (list 'equal (list 'symbol-name (car syms)) "IGNORE")
	    (if (consp (cdr syms))
              `(intern-in-package-of-symbol
		(coerce (append ,@(symcat-fn (cdr syms))) 'string)
		,(car syms))
	      nil)
	    `(intern-in-package-of-symbol
	      (coerce (append ,@(symcat-fn syms)) 'string)
	      ,(car syms)))
    nil))


(defmacro keycat (&rest syms)
  (if (consp syms)
    `(intern
      (coerce (append ,@(symcat-fn syms)) 'string)
      "keyword")
    nil))


;; easy-fix is a macro for defining a fty::deffixtype when we've got a
;;   recognizer function and a default value.
(define easy-fix-fn ((type-name symbolp) (default-value acl2::any-p))
  (b* ((type-pred (symcat type-name '-p))
       (type-fix (symcat type-name '-fix))
       (type-fix-lemma (symcat type-name 'fix-when- type-name '-p))
       (type-equiv (symcat type-name '-equiv)))
    `(defsection ,type-name
       (define ,type-fix ((x ,type-pred))
         :returns(fix-x ,type-pred)
         (mbe :logic (if (,type-pred x) x ,default-value)
              :exec  x)
         ///
         (more-returns
          (fix-x (implies (,type-pred x) (equal fix-x x))
                 :hints(("Goal" :in-theory (enable ,type-fix)))
                 :name ,type-fix-lemma)))
       (deffixtype ,type-name
         :pred   ,type-pred
         :fix    ,type-fix
         :equiv  ,type-equiv
         :define t
         :topic  ,type-name))))

(defmacro easy-fix (type-name default-value)
  `(make-event (easy-fix-fn ',type-name ',default-value)))

; true-list is same as fty::list -- probably remove this,
; but, I'll have to figure out the various changes.
(define true-list-fix ((lst true-listp))
  :parents (SMT-hint-interface)
  :short "Fixing function for true-listp."
  :returns (fixed-lst true-listp)
  (mbe :logic (if (consp lst)
                  (cons (car lst)
                        (true-list-fix (cdr lst)))
                nil)
       :exec lst))

(defthm true-list-fix-idempotent-lemma
  (equal (true-list-fix (true-list-fix x))
         (true-list-fix x))
  :hints (("Goal" :in-theory (enable true-list-fix))))

(defthm true-list-fix-preserve-length
  (equal (len (true-list-fix x))
         (len x))
  :hints (("Goal" :in-theory (enable true-list-fix))))

(defthm true-list-fix-when-true-listp
  (implies (true-listp x)
           (equal (true-list-fix x) x))
  :hints (("Goal" :in-theory (enable true-listp true-list-fix))))

(deffixtype true-list
  :fix true-list-fix
  :pred true-listp
  :equiv true-list-equiv
  :define t
  :forward t
  :topic true-listp)

(defalist symbol-symbol-alist
  :key-type symbolp
  :val-type symbolp
  :pred symbol-symbol-alistp
  :true-listp t)

(defthm cdr-of-symbol-symbol-alistp
  (implies (symbol-symbol-alistp x)
           (symbol-symbol-alistp (cdr x))))

(defthm strip-cars-of-symbol-symbol-alistp
  (implies (symbol-symbol-alistp x)
           (symbol-listp (strip-cars x))))

(defthm strip-cdrs-of-symbol-symbol-alistp
  (implies (symbol-symbol-alistp x)
           (symbol-listp (strip-cdrs x))))

(deflist symbol-list-list
  :elt-type symbol-listp
  :pred symbol-list-listp
  :true-listp t)

(define symbol-alist-fix ((x symbol-alistp))
  :returns (fix-x symbol-alistp)
  (mbe :logic (if (symbol-alistp x) x nil)
       :exec x)
  ///
  (more-returns
   (fix-x (implies (symbol-alistp x) (equal fix-x x))
          :name symbol-alist-fix-when-symbol-alistp)))

(deffixtype symbol-alist
  :pred symbol-alistp
  :fix symbol-alist-fix
  :equiv symbol-alist-equiv
  :define t
  :topic symbol-alist)

(local
 (defthm symbol-alistp-of-pairlis$-of-symbol-listp
   (implies (symbol-listp x)
            (symbol-alistp (pairlis$ x y)))
   :hints (("Goal" :in-theory (enable symbol-alistp))))
 )


(defalist symbol-symbol-list-alist
  :key-type symbolp
  :val-type symbol-listp
  :true-listp t
  :pred symbol-symbol-list-alistp)

(defthm assoc-equal-of-symbol-symbol-list-alistp-1
  (implies (symbol-symbol-list-alistp x)
           (symbol-listp (cdr (assoc-equal y x)))))

(defthm assoc-equal-of-symbol-symbol-list-alistp-2
  (implies (and (symbol-symbol-list-alistp x)
                (assoc-equal y x))
           (consp (assoc-equal y x))))

(defalist symbol-integer-alist
  :key-type symbolp
  :val-type integerp
  :true-listp t
  :pred symbol-integer-alistp)

(defthm assoc-equal-of-symbol-integer-alistp
  (implies (and (symbol-integer-alistp x)
                (assoc-equal y x))
           (and (consp (assoc-equal y x))
                (integerp (cdr (assoc-equal y x))))))

(defalist symbol-boolean-alist
  :key-type symbolp
  :val-type booleanp
  :true-listp t
  :pred symbol-boolean-alistp)

(defthm assoc-equal-of-symbol-boolean-alistp
  (implies (and (symbol-boolean-alistp x)
                (assoc-equal y x))
           (and (consp (assoc-equal y x))
                (booleanp (cdr (assoc-equal y x))))))

(defalist integer-integer-list-alist
  :key-type integerp
  :val-type integer-listp
  :true-listp t
  :pred integer-integer-list-alistp)

(defthm assoc-equal-of-integer-integer-alistp-1
  (implies (integer-integer-list-alistp x)
           (and (true-listp (cdr (assoc-equal y x)))
                (integer-listp (cdr (assoc-equal y x))))))

(defthm assoc-equal-of-integer-integer-alistp-2
  (implies (and (integer-integer-list-alistp x)
                (assoc-equal y x))
           (consp (assoc-equal y x))))

(defalist integer-symbol-list-alist
  :key-type integerp
  :val-type symbol-listp
  :true-listp t
  :pred integer-symbol-list-alistp)

(defoption maybe-integer integerp :pred maybe-integerp)

(deflist maybe-integer-list
  :elt-type maybe-integerp
  :pred maybe-integer-listp
  :true-listp t)

(defthm alistp-of-pairlis$
  (alistp (acl2::pairlis$ a b)))

;; The list of fields for a given FTY product type
(define fty-prod-fields ((name symbolp)
                          state)
  :mode :program
  (b* ((type-table (fty::get-flextypes (w state)))
       ((mv & type-obj) (fty::search-deftypes-table name type-table))
       ((unless (consp type-obj)) nil)
       (products (fty::flexsum->prods type-obj))
       ((unless (consp products)) nil)
       (fields (fty::flexprod->fields (car products))))
    (fty::flexprod-fields->names fields)))
