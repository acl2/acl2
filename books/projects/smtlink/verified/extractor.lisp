;; Copyright (C) 2015, University of British Columbia
;; Written (originally) by Yan Peng (13th March, 2014)
;;
;; License: A 3-clause BSD license.
;; See the LICENSE file distributed with ACL2


(in-package "SMT")
(include-book "centaur/fty/top" :dir :system)
(include-book "xdoc/top" :dir :system)
(include-book "std/util/define" :dir :system)

(include-book "hint-interface")
(include-book "basics")

(set-state-ok t)

(defsection SMT-extract
  :parents (verified)
  :short "SMT-extract extracts type hypotheses from the clause. The SMT solver requires knowing type declarations."

  (define trim-flextype-suffix ((name symbolp))
    :returns (trimmed symbolp)
    :short "trim -P or P suffixes"
    (b* ((name (symbol-fix name))
         (name-str (symbol-name name))
         (pkg-str (symbol-package-name name))
         (l (length name-str))
         ((if (and (>= l 2) (equal (subseq name-str (- l 2) l) "-P")))
          (intern$ (subseq name-str 0 (- l 2)) pkg-str))
         ((if (and (>= l 1) (equal (subseq name-str (1- l) l) "P")))
          (intern$ (subseq name-str 0 (- l 1)) pkg-str)))
      name))


  (defthm acl2::search-from-end-lemma
    (implies (and (stringp str1)
                  (stringp str2)
                  (>= start 0)
                  (<= start (len (acl2::explode str2)))
                  (not (equal
                        (acl2::search-from-end str1 str2
                                               start (len (acl2::explode str2))
                                               acc)
                        acc))
                  )
             (and (>= (acl2::search-from-end str1 str2
                                             start (len (acl2::explode str2))
                                             acc)
                      0)
                  (<= (acl2::search-from-end str1 str2
                                             start (len (acl2::explode str2))
                                             acc)
                      (len (acl2::explode str2))))))


  (define trim-flextype-related-suffix ((name symbolp))
    :returns (mv (type symbolp)
                 (suffix symbolp))
    :short "trim suffixes separated with dash"
    (b* ((name (symbol-fix name))
         (name-str (symbol-name name))
         (pkg-str (symbol-package-name name))
         ;; find the last "-"
         (pos1 (search "-" name-str :from-end t))
         ;; ;; find the last "->"
         ;; (pos2 (search "->" name-str :from-end t))
         ;; ;; if there is "-" but no "->", if it's -fix$inline
         ;; ((if (and pos1 (null pos2)
         ;;           (equal (subseq name-str pos1 nil) "-FIX$INLINE")))
         ;;  (intern$ (subseq name-str 0 pos1) pkg-str))
         ;; ;; if it is -kind$inline
         ;; ((if (and pos1 (null pos2)
         ;;           (equal (subseq name-str pos1 nil) "-KIND$INLINE")))
         ;;  (intern$ (subseq name-str 0 pos1) pkg-str))
         ;; ;; maybe tagged constructors?
         ;; ((if (and pos1 (null pos2)))
         ;;  (intern$ (subseq name-str 0 pos1) pkg-str))
         ;; ;; else if it is "->"
         ;; ((if (and pos1 pos2))
         ;;  (intern$ (subseq name-str 0 pos1) pkg-str))
         ;; Above code can be simplified into
         ((if pos1)
          (mv (intern$ (subseq name-str 0 pos1) pkg-str)
              (intern$ (subseq name-str pos1 (length name-str)) pkg-str)))
         )
      ;; there's no "-" nor "->"
      (mv name nil)))

  (define flextype-related? ((type symbolp) (suffix symbolp) (state))
    :returns (yes booleanp)
    :guard-debug t
    (b* ((type (symbol-fix type))
         (suffix (symbol-fix suffix))
         ;; (pkg-str (symbol-package-name suffix))
         (suffix-str (symbol-name suffix))
         (flex-table (table-alist 'fty::flextypes-table (w state)))
         ((unless (alistp flex-table)) nil)
         (cars-flex (strip-cars flex-table))
         ((if (equal suffix nil))
          (not (null (member-equal type cars-flex))))
         ;; type recognizer or fixing functions
         ((if (or (equal suffix '-P)
                  (equal suffix '-FIX$INLINE)))
          (not (null (member-equal type cars-flex))))
         ;; if not defprod accessor ->
         ((unless (and (>= (length suffix-str) 2)
                       (equal (subseq suffix-str 0 2) "->")))
          nil)
         ;; else treat the field accessor
         ;; (field (intern$ (subseq suffix 2 nil) pkg-str))
         (item (assoc-equal type flex-table))
         ((unless item) nil)
         ;; (agg (cdr item))
         ;; (types (fty::flextypes->types agg))
         )
      t))

  (define typedecl-of-flextype ((fn-name symbolp) (state))
    :returns (flex? booleanp)
    :short "Checking if a function is a flextype type declaration.  Will be
    extracted out and declared as algebraic datatypes in SMT solver"
    (b* ((fn-name (symbol-fix fn-name))
         (trimmed (trim-flextype-suffix fn-name)))
      (flextype-related? trimmed nil state)))

  (define fncall-of-flextype ((fn-name symbolp) (state))
    :returns (flex? booleanp)
    :short "Checking if a function call is a flextype related call.  These calls
    will be translated directly to SMT solver, therefore won't need to be expanded."
    :long "<p>There are five categories of flextype supported in Smtlink.  Examples
    are taken from @('fty::defprod'), @('fty::deflist'), @('fty::defalist')
    and @('fty::defoption').</p>
    <p>Supported functions for @(see fty::defprod):</p>
    <ul>
    <li>Type recognizers, for example, @('sandwich-p')</li>
    <li>Fixing functions, for example, @('sandwich-fix$inline')</li>
    <li>Constructors, for example, @('sandwich')</li>
    <li>Field accessors, for example, @('sandwich->bread$inline')</li>
    </ul>
    <p>Supported functions for @(see fty::deflist): (note Smtlink only support
    deflists that are true-listp)</p>
    <ul>
    <li>Type recognizers, for example, @('foolist-p')</li>
    <li>Fixing functions, for example, @('foolist-fix$inline')</li>
    <li>Constructor @('cons')</li>
    <li>Destructors @('car') and @('cdr')</li>
    <li>Base list @('nil'), this is not a function, but needs special care</li>
    </ul>
    <p>Supported functions for @(see fty::defalist): (note Smtlink only support
    defalists that are true-listp)</p>
    <ul>
    <li>Type recognizers, for example, @('fooalist-p')</li>
    <li>Fixing functions, for example, @('fooalist-fix$inline')</li>
    <li>Constructor @('acons')</li>
    <li>Destructors are not supported for alists due to soundness issues</li>
    <li>Search function @('assoc-equal'), we support this version of assoc for
    simplicity</li>
    </ul>
    <p>Supported functions for @(see fty::defoption): </p>
    <ul>
    <li>Type recognizers, for example, @('maybe-foop')</li>
    <li>Fixing functions, for example, @('maybe-foo-fix$inline')</li>
    <li>Nothing case @('nil'), this is not a function, but needs special
    care</li>
    </ul>"
    (b* ((fn-name (symbol-fix fn-name))
         ;; for constructors, except for tagsum constructors
         ((if (flextype-related? fn-name nil state)) t)
         (flex-type? (trim-flextype-suffix fn-name))
         ((if flex-type?) t)
         ((mv type suffix) (trim-flextype-related-suffix fn-name))
         ;; special cases
         ((if (and
               ;; lists
               (equal fn-name 'CONS)
               (equal fn-name 'CAR)
               (equal fn-name 'CDR)
               ;; alists
               (equal fn-name 'ACONS)
               (equal fn-name 'ASSOC-EQUAL)
               ))
          t)
         )
      (flextype-related? type suffix state)))

  ;; TODO: can alistp and eqlable-listp be proved?
  (define extract-is-decl ((expr pseudo-termp) (state))
    :returns (is-decl? booleanp)
    (b* (((unless (equal (len expr) 2)) nil)
         (fn-name (car expr))
         ((unless (symbolp fn-name)) nil)
         ((unless
              (or ;; basic types
               (member-equal fn-name (strip-cars *SMT-types*))
               ;; fty types
               (typedecl-of-flextype fn-name state)))
          nil)
         ((unless (and (symbolp (cadr expr)) (cadr expr))) nil))
      t))

  (defthm pseudo-term-listp-of-append-of-pseudo-term-listp
    (implies (and (pseudo-term-listp x) (pseudo-term-listp y))
             (pseudo-term-listp (append x y))))

  (local (in-theory (enable pseudo-termp pseudo-term-listp
                            pseudo-term-fix
                            pseudo-term-list-fix)))

  (defines extract
    :parents (SMT-extractor)
    :short "Functions for extracting type declarations from clause."

    (define extract-disjunct ((term pseudo-termp) (state))
      :returns (mv (decl-list pseudo-term-listp) (theorem pseudo-termp))
      :verify-guards nil
      :guard-debug t
      ;; looking for (typep var) where var *not* satisfying typep make term trivially true
      (b* ((term (pseudo-term-fix term)))
        (cond ((not (consp term)) (mv nil term))
              ((and (equal (car term) 'if) (equal (caddr term) ''t))
               (b* (((mv decl1 term1) (extract-disjunct (cadr term) state))
                    ((mv decl2 term2) (extract-disjunct (cadddr term) state)))
                 (mv (append decl1 decl2)
                     (cond ((or (equal term1 ''t) (equal term2 ''t)) ''t)
                           ((equal term1 ''nil) term2)
                           ((equal term2 ''nil) term1)
                           (t `(if ,term1 't ,term2))))))
              ((equal (car term) 'not)
               (b* (((mv decl0 term0) (extract-conjunct (cadr term) state)))
                 (mv decl0
                     (cond ((equal term0 ''nil) ''t)
                           ((equal term0 ''t)   ''nil)
                           (t `(not ,term0))))))
              ((equal (car term) 'implies)
               (b* (((mv decl1 term1) (extract-conjunct (cadr term) state))
                    ((mv decl2 term2) (extract-disjunct (caddr term) state)))
                 (mv (append decl1 decl2)
                     (cond ((or (equal term1 ''nil) (equal term2 ''t)) ''t)
                           ((equal term1 ''t) term2)
                           ((equal term2 ''nil) `(not ,term1))
                           (t `(implies ,term1 ,term2))))))
              (t (mv nil term)))))

    (define extract-conjunct ((term pseudo-termp) (state))
      :returns (mv (decl-list pseudo-term-listp) (theorem pseudo-termp))
      :verify-guards nil
      :guard-debug t
      ;; looking for (typep var) where var *not* satisfying typep make term trivially false
      (b* ((term (pseudo-term-fix term)))
        (cond ((not (consp term)) (mv nil term))
              ((and (equal (car term) 'if) (equal (cadddr term) ''nil))
               (b* (((mv decl1 term1) (extract-conjunct (cadr term) state))
                    ((mv decl2 term2) (extract-conjunct (caddr term) state)))
                 (mv (append decl1 decl2)
                     (cond ((or (equal term1 ''nil) (equal term2 ''nil)) ''nil)
                           ((equal term1 ''t) term2)
                           ((equal term2 ''t) term1)
                           (t `(if ,term1 ,term2 'nil))))))
              ((equal (car term) 'not)
               (b* (((mv decl0 term0) (extract-disjunct (cadr term) state)))
                 (mv decl0
                     (cond ((equal term0 ''nil) ''t)
                           ((equal term0 ''t)   ''nil)
                           (t `(not ,term0))))))
              ((extract-is-decl term state)
               (mv (list term) ''t))
              (t (mv nil term)))))
    )

  (verify-guards extract-conjunct)
  (verify-guards extract-disjunct)

  (define SMT-extract ((term pseudo-termp) (state))
    :returns (mv (decl-list pseudo-term-listp) (theorem pseudo-termp))
    (b* (((mv decl-list theorem) (extract-disjunct term state)))
      ;; (prog2$ (cw "decl-list:~q0~%theorem:~q1~%" decl-list theorem)
      (mv decl-list theorem)
      )) ;;)

  )

