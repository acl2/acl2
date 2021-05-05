; FTY Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Stephen Westfold (westfold@kestrel.edu), Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "FTY")

(include-book "centaur/fty/database" :dir :system)
(include-book "centaur/fty/fty-parseutils" :dir :system)
(include-book "std/lists/list-defuns" :dir :system)
;(include-book "std/osets/top" :dir :system)
(include-book "std/util/defrule" :dir :system)
(include-book "xdoc/constructors" :dir :system)
(include-book "kestrel/utilities/omaps/core" :dir :system)
(include-book "kestrel/event-macros/proof-preparation" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc defomap

  :parents (fty-extensions fty omap::omaps)

  :short "Generate a <see topic='@(url fty::fty)'>fixtype</see>
          of <see topic='@(url omap::omaps)'>omaps</see>
          whose keys and values have specified fixtypes."

  :long

  (xdoc::topstring

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::h3 "Introduction")

   (xdoc::p
    "This is analogous to
     @(tsee fty::deflist),
     @(tsee fty::defalist), and
     @(tsee fty::defset).
     Besides the fixtype itself,
     this macro also generates some theorems about the fixtype.
     Future versions of this macro may generate more theorems, as needed.")

   (xdoc::p
    "Aside from the recognizer, fixer, and equivalence for the fixtype,
     this macro does not generate any operations on the typed omaps.
     Instead, the "
    (xdoc::seetopic "omap::omaps" "generic omap operations")
    " can be used on typed omaps.
     This macro generates theorems about
     the use of these generic operations on typed omaps.")

   (xdoc::p
    "Future versions of this macro may be modularized to provide
     a ``sub-macro'' that generates only the recognizer and theorems about it,
     without the fixtype (and without the fixer and equivalence),
     similarly to @(tsee std::deflist) and @(tsee std::defalist).
     That sub-macro could be called @('omap::defomet').")

   (xdoc::p
    "This macro differs from @(tsee fty::defmap),
     which generates an alist.")

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::h3 "General Form")

   (xdoc::codeblock
    "(defomap type"
    "         :key-type ..."
    "         :val-type ..."
    "         :pred ..."
    "         :fix ..."
    "         :equiv ..."
    "         :parents ..."
    "         :short ..."
    "         :long ...")

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::h3 "Inputs")

   (xdoc::desc
    "@('type')"
    (xdoc::p
     "The name of the new fixtype."))

   (xdoc::desc
    "@(':key-type')"
    (xdoc::p
     "The (existing) fixtype of the keys of the new map fixtype."))

   (xdoc::desc
    "@(':val-type')"
    (xdoc::p
     "The (existing) fixtype of the values of the new map fixtype."))

   (xdoc::desc
    (list
     "@(':pred')"
     "@(':fix')"
     "@(':equiv')")
    (xdoc::p
     "The name of the recognizer, fixer, and equivalence for the new fixtype.")
    (xdoc::p
     "The defaults are @('type') followed by
      @('-p'), @('-fix'), and @('-equiv')."))

   (xdoc::desc
    (list
     "@(':parents')"
     "@(':short')"
     "@(':long')")
    (xdoc::p
     "These are used to generate XDOC documentation
      for the topic @('name').")
    (xdoc::p
     "If any of these is not supplied, the corresponding component
      is omitted from the generated XDOC topic."))

   (xdoc::p
    "This macro currently does not perform a thorough validation of its inputs.
     Erroneous inputs may result in failures of the generated events.
     Errors should be easy to diagnose,
     also since this macro has a very simple and readable implementation.
     Future versions of this macro
     should perform more thorough input validation.")

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::h3 "Generated Events")

   (xdoc::p
    "The following are generated, inclusive of XDOC documentation:")

   (xdoc::ul

    (xdoc::li
     "The recognizer, the fixer, the equivalence, and the fixtype.")

    (xdoc::li
     "Several theorems about the recognizer, fixer, equivalence,
      and omap operations applied to this type of omaps."))

   (xdoc::p
    "See the implementation, which uses a readable backquote notation,
     for details.")))

(defxdoc defomap-implementation
  :parents (defomap)
  :short "Implementation of @(tsee defomap).")

(program)

(define check-flexomap-already-defined (pred kwd-alist our-fixtypes ctx state)
  (declare (ignorable kwd-alist))
  ;; Special function for inferring already-definedp
  (b* (((when (< 1 (len our-fixtypes)))
        ;; Defining more than one fixtype.  We don't currently support this for
        ;; already-defined lists/alists, so assume we're not already-defined.
        nil)
       (existing-formals (fgetprop pred 'acl2::formals t (w state)))
       (already-defined (not (eq existing-formals t)))
       (- (and already-defined
               (cw "NOTE: Using existing definition of ~x0.~%" pred)))
       (- (or (not already-defined)
              (eql (len existing-formals) 1)
              (er hard? ctx
                  "~x0 is already defined in an incompatible manner: it ~
                   should take exactly 1 input, but its formals are ~x1"
                  pred existing-formals))))
    already-defined))

(define check-flexomap-fix-already-defined (fix kwd-alist our-fixtypes ctx state)
  (declare (ignorable kwd-alist))
  ;; Special function for inferring already-definedp
  (b* (((when (< 1 (len our-fixtypes)))
        ;; Defining more than one fixtype.  We don't currently support this for
        ;; already-defined lists/alists, so assume we're not already-defined.
        nil)
       (fix$inline (acl2::add-suffix fix acl2::*inline-suffix*))
       (existing-formals (fgetprop fix$inline 'acl2::formals t (w state)))
       (already-defined (not (eq existing-formals t)))
       (- (and already-defined
               (cw "NOTE: Using existing definition of ~x0.~%" fix)))
       (- (or (not already-defined)
              (eql (len existing-formals) 1)
              (er hard? ctx
                  "~x0 is already defined in an incompatible manner: it ~
                   should take exactly 1 input, but its formals are ~x1"
                  fix existing-formals)))
       )
    already-defined))


(define flexomap-fns (x)
  (b* (((flexomap x)))
    (list x.pred
          x.fix)))

(define flexomap-collect-fix/pred-pairs (omap)
  (b* (((flexomap omap) omap))
    (append (and omap.key-type
                 omap.key-fix ;; bozo how could this not hold?
                 (list (cons omap.key-fix omap.key-type)))
            (and omap.val-type
                 omap.val-fix ;; bozo how could this not hold?
                 (list (cons omap.val-fix omap.val-type))))))

(defconst *flexomap-keywords*
  '(:pred
    :fix
    :equiv
    :count
    :get
    :set
    :key-type
    :val-type
    :measure
    :measure-debug
    :xvar
    :parents
    :short
    :long
    ;; The following are NYI
    ;; :no-count
    ;; :prepwork
    ;; :strategy
    ;; :keyp-of-nil
    ;; :valp-of-nil
    ;; :post-pred-events
    ;; :post-fix-events
    ;; :post-events
    ;; :enable-rules
    ;; :already-definedp
    ;; :verbosep
    ))

(define parse-flexomap (x xvar our-fixtypes fixtypes state)
  (b* (((cons name args) x)
       ((unless (symbolp name))
        (raise "Malformed flexomap: ~x0: name must be a symbol" x))
       ((mv pre-/// post-///) (std::split-/// name args))
       ((mv kwd-alist rest)
        (extract-keywords name *flexomap-keywords* pre-/// nil))
       ((when rest)
        (raise "Malformed flexomap: ~x0: after kind should be a keyword/value omap."
               name))
       (key-type (getarg :key-type nil kwd-alist))
       ((unless (symbolp key-type))
        (raise "Bad flexalist ~x0: Element type must be a symbol" name))
       ((mv key-type key-fix key-equiv key-recp)
        (get-pred/fix/equiv (getarg :key-type nil kwd-alist) our-fixtypes fixtypes))
       (val-type (getarg :val-type nil kwd-alist))
       ((unless (symbolp val-type))
        (raise "Bad flexalist ~x0: Element type must be a symbol" name))
       ((mv val-type val-fix val-equiv val-recp)
        (get-pred/fix/equiv (getarg :val-type nil kwd-alist) our-fixtypes fixtypes))
       (pred  (getarg! :pred  (intern-in-package-of-symbol (cat (symbol-name name) "-P") name) kwd-alist))
       (fix   (getarg! :fix   (intern-in-package-of-symbol (cat (symbol-name name) "-FIX") name) kwd-alist))
       (equiv (getarg! :equiv (intern-in-package-of-symbol (cat (symbol-name name) "-EQUIV") name) kwd-alist))
       (count (flextype-get-count-fn name kwd-alist))
       (xvar (or (getarg :xvar xvar kwd-alist)
                 (car (find-symbols-named-x (getarg :measure nil kwd-alist)))
                 (intern-in-package-of-symbol "X" name)))
       (measure (getarg! :measure `(acl2-count ,xvar) kwd-alist))
       (already-defined
        (check-flexomap-already-defined pred kwd-alist our-fixtypes 'defomap state))
       (fix-already-defined
        (check-flexomap-fix-already-defined fix kwd-alist our-fixtypes 'defomap state)))

    (make-flexomap :name name
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
                   :recp (or key-recp val-recp)
                   :already-definedp already-defined
                   :fix-already-definedp fix-already-defined)))

(define flexomap-predicate-def (omap)
  (b* (((flexomap omap))
       ;; package for the generated theorem and variable names:
       (pkg (symbol-package-name omap.pred))
       (pkg (if (equal pkg *main-lisp-package-name*) "ACL2" pkg))
       (pkg-witness (pkg-witness pkg))
       ;; variables to use in the generated functions and theorems:
       (y (intern-in-package-of-symbol "Y" pkg-witness))
       (k (intern-in-package-of-symbol "K" pkg-witness))
       (v (intern-in-package-of-symbol "V" pkg-witness))
       ;; names of the generated theorems:
       (booleanp-of-pred (acl2::packn-pos (list 'booleanp-of- omap.pred) pkg-witness))
       (mapp-when-pred (acl2::packn-pos (list 'mapp-when- omap.pred) pkg-witness))
       (pred-of-tail (acl2::packn-pos (list omap.pred '-of-tail) pkg-witness))
       (key-pred-of-head-key-when-pred
        (acl2::packn-pos (list omap.key-type '-of-head-key-when- omap.pred) pkg-witness))
       (val-pred-of-head-val-when-pred
        (acl2::packn-pos (list omap.val-type '-of-head-val-when- omap.pred) pkg-witness))
       (pred-of-update (acl2::packn-pos (list omap.pred '-of-update) pkg-witness))
       (pred-of-update* (acl2::packn-pos (list omap.pred '-of-update*) pkg-witness))
       (pred-of-delete (acl2::packn-pos (list omap.pred '-of-delete) pkg-witness))
       (pred-of-delete* (acl2::packn-pos (list omap.pred '-of-delete*) pkg-witness))
       (key-pred-when-in-pred
        (acl2::packn-pos (list omap.key-type '-when-in- omap.pred '-binds-free- omap.xvar)
                         pkg-witness))
       (key-pred-of-car-of-in-pred
        (acl2::packn-pos (list omap.key-type '-of-car-of-in- omap.pred) pkg-witness))
       (val-pred-of-cdr-of-in-pred
        (acl2::packn-pos (list omap.val-type '-of-cdr-of-in- omap.pred) pkg-witness))
       (val-pred-of-lookup-when-pred
        (acl2::packn-pos (list omap.val-type '-of-lookup-when- omap.pred) pkg-witness))
       ;; reference to the fixtype for the generated XDOC documentation:
       (type-ref (concatenate 'string
                              "@(tsee "
                              (acl2::string-downcase (symbol-package-name omap.name))
                              "::"
                              (acl2::string-downcase (symbol-name omap.name))
                              ")")))
    (if omap.already-definedp
        '(progn)
      `(define ,omap.pred (,omap.xvar)
           :parents (,omap.name)
           :short ,(concatenate 'string "Recognizer for " type-ref ".")
           ,@(if omap.measure `(:measure ,omap.measure)
               ())
           ,@(and (getarg :measure-debug nil omap.kwd-alist)
                `(:measure-debug t))
           (if (atom ,omap.xvar)
               (null ,omap.xvar)
             (and (consp (car ,omap.xvar))
                  (,omap.key-type (caar ,omap.xvar))
                  (,omap.val-type (cdar ,omap.xvar))
                  (or (null (cdr ,omap.xvar))
                      (and (consp (cdr ,omap.xvar))
                           (consp (cadr ,omap.xvar))
                           (acl2::fast-<< (caar ,omap.xvar) (caadr ,omap.xvar))
                           (,omap.pred (cdr ,omap.xvar))))))
           :no-function t
           ///
           (defrule ,booleanp-of-pred
             (booleanp (,omap.pred ,omap.xvar)))
           (defrule ,mapp-when-pred
             (implies (,omap.pred ,omap.xvar)
                      (omap::mapp ,omap.xvar))
             :rule-classes (:rewrite :forward-chaining)
             :enable omap::mapp)
           (defrule ,pred-of-tail
             (implies (,omap.pred ,omap.xvar)
                      (,omap.pred (omap::tail ,omap.xvar)))
             :enable omap::tail
             :cases ((null (cdr ,omap.xvar)))
             )
           (defrule ,key-pred-of-head-key-when-pred
             (implies (and (,omap.pred ,omap.xvar)
                           (not (omap::empty ,omap.xvar)))
                      (,omap.key-type (mv-nth 0 (omap::head ,omap.xvar))))
             :enable omap::head)
           (defrule ,val-pred-of-head-val-when-pred
             (implies (and (,omap.pred ,omap.xvar)
                           (not (omap::empty ,omap.xvar)))
                      (,omap.val-type (mv-nth 1 (omap::head ,omap.xvar))))
             :enable omap::head)
           (defrule ,pred-of-update
             (implies (and (,omap.pred ,omap.xvar)
                           (,omap.key-type ,k)
                           (,omap.val-type ,v))
                      (,omap.pred (omap::update ,k ,v ,omap.xvar)))
             :enable (omap::update omap::head omap::tail)
             ,@(and (not omap.recp) '(:disable ((:induction omap::update))))
             :expand (,omap.pred ,omap.xvar)) ; sjw: not sure if there is a better way to do this
           (defrule ,pred-of-update*
             (implies (and (,omap.pred ,omap.xvar)
                           (,omap.pred ,y))
                      (,omap.pred (omap::update* ,omap.xvar ,y)))
             :enable omap::update*)
           (defrule ,pred-of-delete
             (implies (,omap.pred ,omap.xvar)
                      (,omap.pred (omap::delete ,k ,omap.xvar)))
             :enable omap::delete)
           (defrule ,pred-of-delete*
             (implies (,omap.pred ,omap.xvar)
                      (,omap.pred (omap::delete* ,k ,omap.xvar)))
             :enable omap::delete*)
           (defrule ,key-pred-when-in-pred
             (implies (and (omap::in ,k ,omap.xvar) ; binds free X
                           (,omap.pred ,omap.xvar))
                      (,omap.key-type ,k))
             :enable omap::in)
           (defrule ,key-pred-of-car-of-in-pred
             (implies (and (,omap.pred ,omap.xvar)
                           (omap::in ,k ,omap.xvar))
                      (,omap.key-type (car (omap::in ,k ,omap.xvar))))
             :enable omap::in)
           (defrule ,val-pred-of-cdr-of-in-pred
             (implies (and (,omap.pred ,omap.xvar)
                           (omap::in ,k ,omap.xvar))
                      (,omap.val-type (cdr (omap::in ,k ,omap.xvar))))
             :enable omap::in)
           (defrule ,val-pred-of-lookup-when-pred
             (implies (and (,omap.pred ,omap.xvar)
                           (omap::in ,k ,omap.xvar))
                      (,omap.val-type (omap::lookup ,k ,omap.xvar)))
             :enable omap::lookup)))))

(define flexomap-fix-def (omap flagp)
  (b* (((flexomap omap))
       (pred-of-fix (acl2::packn-pos (list omap.pred '-of- omap.fix) omap.name))
       (fix-when-pred (acl2::packn-pos (list omap.fix '-when- omap.pred) omap.name))
       (empty-fix (acl2::packn-pos (list 'empty- omap.fix) omap.name))
       (empty-of-fix (acl2::packn-pos (list 'empty-of- omap.fix '-to-not- omap.name '-or-empty)
                                      omap.name)))
    (if omap.fix-already-definedp
        '(progn)
      `(define ,omap.fix ((,omap.xvar ,omap.pred))
         :parents (,omap.name)
         :short ,(cat "@(call " (xdoc::full-escape-symbol omap.fix)
                      ") is a usual @(see fty::fty) omap fixing function.")
         ,@(and (getarg :measure-debug nil omap.kwd-alist)
                `(:measure-debug t))
         ,@(and flagp `(:flag ,omap.name))
         :progn t
         ; :inline t
         (mbe :logic (if (,omap.pred ,omap.xvar) ,omap.xvar nil)
              :exec ,omap.xvar)
         :no-function t
         ///
         (defrule ,pred-of-fix
           (,omap.pred (,omap.fix ,omap.xvar)))
         (defrule ,fix-when-pred
           (implies (,omap.pred ,omap.xvar)
                    (equal (,omap.fix ,omap.xvar) ,omap.xvar)))
         (defrule ,empty-fix
           (implies (or (omap::empty ,omap.xvar)
                        (not (,omap.pred ,omap.xvar)))
                    (omap::empty (,omap.fix ,omap.xvar))))
         (defrule ,empty-of-fix
           (equal (omap::empty (,omap.fix ,omap.xvar))
                  (or (not (,omap.pred ,omap.xvar))
                      (omap::empty ,omap.xvar)))
           :enable omap::empty)))))

(define flexomap-fix-postevents (omap)
  :ignore-ok t
  :irrelevant-formals-ok t
  ;; sjw: The list versions do not carry over. I don't know what might be useful here.
  ())

(define flexomap-fix-when-pred-thm (x flagp)
  (b* (((flexomap x))
       (foo-fix-when-foo-p (intern-in-package-of-symbol
                            (cat (symbol-name x.fix) "-WHEN-" (symbol-name x.pred))
                            x.fix)))
    `(defthm ,foo-fix-when-foo-p
       (implies (,x.pred ,x.xvar)
                (equal (,x.fix ,x.xvar) ,x.xvar))
       :hints (,@(and (not flagp)
                      `(("goal" :induct (,x.fix ,x.xvar))))
                 '(:expand ((,x.pred ,x.xvar)
                          (,x.fix ,x.xvar))
                 :in-theory (disable ,x.fix ,x.pred)))
       . ,(and flagp `(:flag ,x.name)))))

(defun flexomap-count (omap types)
  (b* (((flexomap omap))
       ((unless omap.count) nil)
       (keycount (flextypes-find-count-for-pred omap.key-type types))
       (keycount (or keycount 'acl2::acl2-count))
       (valcount (flextypes-find-count-for-pred omap.val-type types))
       (valcount (or valcount 'acl2::acl2-count)))
    `((define ,omap.count ((,omap.xvar ,omap.pred))
        :returns (count natp
                        :rule-classes :type-prescription
                        :hints ('(:expand (,omap.count ,omap.xvar)
                                  :in-theory (disable ,omap.count))))
        :measure (let ((,omap.xvar (,omap.fix ,omap.xvar)))
                   ,omap.measure)
        ,@(and (getarg :measure-debug nil omap.kwd-alist)
               `(:measure-debug t))
        :verify-guards nil
        :no-function t
        :progn t
        (if (or (omap::empty ,omap.xvar)
                (not (,omap.pred ,omap.xvar)))
            1
          (mv-let (key val)
              (omap::head ,omap.xvar)
            (declare (ignorable key val))
            (+ 1
               ,@(and keycount `((,keycount key)))
               ,@(and valcount `((,valcount val)))
               (,omap.count (omap::tail ,omap.xvar)))))))))

(defun flexomap-count-post-events (omap types)
  (b* (((flexomap omap))
       ((unless omap.count) nil)
       (keycount (flextypes-find-count-for-pred omap.key-type types))
       (keycount (or keycount 'acl2::acl2-count)) ; Seems reasonable
       (valcount (flextypes-find-count-for-pred omap.val-type types))
       (valcount (or valcount 'acl2::acl2-count)) ; Seems reasonable
       ;; ((when (not eltcount)) nil)
       (omap-count-of-update (intern-in-package-of-symbol (cat (symbol-name omap.count) "-OF-UPDATE") omap.count))
       (omap-count-of-head (intern-in-package-of-symbol (cat (symbol-name omap.count) "-OF-HEAD") omap.count))
       (omap-count-of-head-fix (intern-in-package-of-symbol (cat (symbol-name omap.count) "-OF-HEAD-FIX") omap.count))
       (omap-count-of-tail (intern-in-package-of-symbol (cat (symbol-name omap.count) "-OF-TAIL") omap.count))
       (omap-count-of-tail-fix (intern-in-package-of-symbol (cat (symbol-name omap.count) "-OF-TAIL-FIX") omap.count))
       (omap-count-of-lookup  (intern-in-package-of-symbol (cat (symbol-name omap.count) "-OF-LOOKUP") omap.count))
       (omap-count-when-empty  (intern-in-package-of-symbol (cat (symbol-name omap.count) "-WHEN-EMPTY") omap.count))
       (omap-count-when-not-empty  (intern-in-package-of-symbol (cat (symbol-name omap.count) "-WHEN-NOT-EMPTY") omap.count)))

    `((acl2::evmac-prepare-proofs)      ; Proofs should not need default-hints

      (defthm ,omap-count-when-empty
        (implies (omap::empty ,omap.xvar)
                 (equal (,omap.count ,omap.xvar)
                        1))
        :hints (("Goal" :in-theory (enable ,omap.count))))

      (defthm ,omap-count-when-not-empty
        (implies (and (not (omap::empty ,omap.xvar))
                      (,omap.pred ,omap.xvar))
                 (equal (,omap.count ,omap.xvar)
                        (+ 1
                           ,@(and keycount `((,keycount (mv-nth 0 (omap::head ,omap.xvar)))))
                           ,@(and valcount `((,valcount (mv-nth 1 (omap::head ,omap.xvar)))))
                           (,omap.count (omap::tail ,omap.xvar)))))
        :hints (("Goal" :in-theory (enable ,omap.count))))

      ,@(and keycount valcount
             `((defthm ,omap-count-of-head
                 (implies (and (not (omap::empty ,omap.xvar))
                               (,omap.pred ,omap.xvar))
                          (< (+ (,keycount (mv-nth 0 (omap::head ,omap.xvar)))
                                (,valcount (mv-nth 1 (omap::head ,omap.xvar))))
                             (,omap.count ,omap.xvar)))
                 :rule-classes :linear)))
      ,@(and keycount valcount
             `((defthm ,omap-count-of-head-fix
                 (implies (consp (,omap.fix ,omap.xvar))
                          (< (+ (,keycount (mv-nth 0 (omap::head (,omap.fix ,omap.xvar))))
                                (,valcount (mv-nth 1 (omap::head (,omap.fix ,omap.xvar)))))
                             (,omap.count ,omap.xvar)))
                 :hints (("Goal" :in-theory (enable ,omap.fix omap::mapp-non-nil-implies-non-empty)))
                 :rule-classes :linear)))

      (defthm ,omap-count-of-tail
        (implies (and (not (omap::empty ,omap.xvar))
                      (,omap.pred ,omap.xvar))
                 (< (,omap.count (omap::tail ,omap.xvar))
                    (,omap.count ,omap.xvar)))
        :rule-classes :linear
        :hints (("Goal" :in-theory (enable ,omap.count))))
      (defthm ,omap-count-of-tail-fix
        (implies (consp (,omap.fix ,omap.xvar))
                 (< (,omap.count (omap::tail (,omap.fix ,omap.xvar)))
                    (,omap.count ,omap.xvar)))
        :rule-classes :linear
        :hints (("Goal" :in-theory (enable ,omap.count ,omap.fix omap::mapp-non-nil-implies-non-empty))))

      (defthm ,omap-count-of-lookup
        (implies (and (not (omap::empty map))
                      (,omap.pred map))
                 (< (,valcount (omap::lookup key map))
                    (,omap.count map)))
        :hints (("Goal" :in-theory (enable omap::lookup omap::in omap::in-when-empty ,valcount))
                ("Goal''" :induct (omap::in key map))))

      (defthm ,omap-count-of-update
        (implies (and (,omap.pred ,omap.xvar)
                      (,omap.key-type key)
                      (,omap.val-type val)
                      (not (omap::in key ,omap.xvar)))
                 ,(if (or keycount valcount)
                      `(equal (,omap.count (omap::update key val ,omap.xvar))
                              (+ 1
                                 ,@(and keycount `((,keycount key)))
                                 ,@(and valcount `((,valcount val)))
                                 (,omap.count ,omap.xvar)))
                    `(> (,omap.count (omap::update key val ,omap.xvar))
                        (,omap.count ,omap.xvar))))
        :hints (("Goal" :in-theory (enable omap::head-key
                                           omap::empty
                                           omap::head-key-of-update-of-nil
                                           omap::head-value-of-update-when-head-key-equal
                                           omap::in-when-empty
                                           omap::in-when-in-tail
                                           omap::mfix-when-mapp
                                           omap::tail-of-update-empty
                                           omap::update-not-empty
                                           omap::update-when-empty
                                           (:induction omap::use-weak-update-induction)
                                           (:induction omap::weak-update-induction)
                                           omap::weak-update-induction-helper-1
                                           omap::weak-update-induction-helper-2
                                           omap::weak-update-induction-helper-3)))
        :rule-classes :linear))))
