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
(include-book "std/osets/top" :dir :system)
(include-book "std/util/defrule" :dir :system)
(include-book "xdoc/constructors" :dir :system)


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc defset

  :parents (fty-extensions fty set::std/osets)

  :short "Generate a <see topic='@(url fty::fty)'>fixtype</see>
          of <see topic='@(url set::std/osets)'>osets</see>
          whose elements have a specified fixtype."

  :long

  (xdoc::topstring

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::h3 "Introduction")

   (xdoc::p
    "This is analogous to
     @(tsee fty::deflist),
     @(tsee fty::defalist), and
     @(tsee fty::defomap).
     Besides the fixtype itself,
     this macro also generates some theorems about the fixtype.
     Future versions of this macro may generate more theorems, as needed.")

   (xdoc::p
    "Aside from the recognizer, fixer, and equivalence for the fixtype,
     this macro does not generate any operations on the typed osets.
     Instead, the "
    (xdoc::seetopic "acl2::std/osets" "generic oset operations")
    " can be used on typed osets.
     This macro generates theorems about
     the use of these generic operations on typed osets.")

   (xdoc::p
    "Future versions of this macro may be modularized to provide
     a ``sub-macro'' that generates only the recognizer and theorems about it,
     without the fixtype (and without the fixer and equivalence),
     similarly to @(tsee std::deflist) and @(tsee std::defalist).
     That sub-macro could be called @('set::defset').")

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::h3 "General Form")


   (xdoc::codeblock
    "(defset type"
    "        :elt-type ..."
    "        :elementp-of-nil ..."
    "        :pred ..."
    "        :fix ..."
    "        :equiv ..."
    "        :measure ..."
    "        :parents ..."
    "        :short ..."
    "        :long ..."
    "  )")

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::h3 "Inputs")

   (xdoc::desc
    "@('type')"
    (xdoc::p
     "The name of the new fixtype."))

   (xdoc::desc
    "@(':elt-type')"
    (xdoc::p
     "The (existing) fixtype of the elements of the new set fixtype."))

   (xdoc::desc
    "@(':elementp-of-nil')"
    (xdoc::p
     "Specifies whether @('nil') is in the element fixtype @(':elt-type').
      It must be @('t'), @('nil'), or @(':unknown') (the default).
      When @('t') or @('nil'), slightly better theorems are generated."))

   (xdoc::desc
    "@(':pred')
     <br/>
     @(':fix')
     <br/>
     @(':equiv')"
    (xdoc::p
     "The name of the recognizer, fixer, and equivalence for the new fixtype.")
    (xdoc::p
     "The defaults are @('type') followed by
      @('-p'), @('-fix'), and @('-equiv')."))

   (xdoc::desc
    "@(':parents')
     <br/>
     @(':short')
     <br/>
     @(':long')"
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
     "Several theorems about the recognizer, fixer, and equivalence."))

   (xdoc::p
    "See the implementation, which uses a readable backquote notation,
     for details.")))

(defxdoc defset-implementation
  :parents (defset)
  :short "Implementation of @(tsee defset).")

(program)

(define check-flexset-already-defined (pred kwd-alist our-fixtypes ctx state)
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

(define check-flexset-fix-already-defined (fix kwd-alist our-fixtypes ctx state)
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

(defconst *flexset-keywords*
  '(:pred
    :fix
    :equiv
    :count
    :elt-type
    ;:non-emptyp
    :measure
    :measure-debug
    :xvar
    ;; :true-listp
    :elementp-of-nil
    ;; :cheap
    :parents
    :short
    :long
    :no-count
    ;; :prepwork
    ;; :post-pred-events
    ;; :post-fix-events
    ;; :post-events
    ;; :enable-rules
    ;; :verbosep
    ))

(define parse-flexset (x xvar our-fixtypes fixtypes state)
  (b* (((cons name args) x)
       ((unless (symbolp name))
        (raise "Malformed flexset: ~x0: name must be a symbol" x))
       ((mv pre-/// post-///) (std::split-/// name args))
       ((mv kwd-alist rest)
        (extract-keywords name *flexset-keywords* pre-/// nil))
       ((when rest)
        (raise "Malformed flexset: ~x0: after kind should be a keyword/value set."
               name))
       (elt-type (getarg :elt-type nil kwd-alist))
       ((unless (and (symbolp elt-type) elt-type))
        (raise "Bad flexset ~x0: Element type must be a symbol" name))
       ((mv elt-type elt-fix elt-equiv recp)
        (get-pred/fix/equiv (getarg :elt-type nil kwd-alist) our-fixtypes fixtypes))
       (pred  (getarg! :pred  (intern-in-package-of-symbol (cat (symbol-name name) "-P") name) kwd-alist))
       (fix   (getarg! :fix   (intern-in-package-of-symbol (cat (symbol-name name) "-FIX") name) kwd-alist))
       (equiv (getarg! :equiv (intern-in-package-of-symbol (cat (symbol-name name) "-EQUIV") name) kwd-alist))
       ;(non-emptyp (getarg :non-emptyp nil kwd-alist))
       (elementp-of-nil (getarg :elementp-of-nil :unknown kwd-alist))
       (count (flextype-get-count-fn name kwd-alist))
       (xvar (or (getarg :xvar xvar kwd-alist)
                 (car (find-symbols-named-x (getarg :measure nil kwd-alist)))
                 (intern-in-package-of-symbol "X" name)))
       (measure (getarg! :measure `(acl2-count ,xvar) kwd-alist))
       (already-defined
        (check-flexset-already-defined pred kwd-alist our-fixtypes 'defset state))
       (fix-already-defined
        (check-flexset-fix-already-defined fix kwd-alist our-fixtypes 'defset state)))

    (make-flexset :name name
                  :pred pred
                  :fix fix
                  :equiv equiv
                  :count count
                  :elt-type elt-type
                  :elt-fix elt-fix
                  :elt-equiv elt-equiv
                  :elementp-of-nil elementp-of-nil
                  :measure measure
                  :kwd-alist (if post-///
                                 (cons (cons :///-events post-///)
                                       kwd-alist)
                               kwd-alist)
                  :xvar xvar
                  :recp recp
                  :already-definedp already-defined
                  :fix-already-definedp fix-already-defined)))



(define flexset-fns (x)
  (b* (((flexset x)))
    (list x.pred
          x.fix)))

(define flexset-collect-fix/pred-pairs (x)
  (b* (((flexset x)))
    (and x.elt-type
         x.elt-fix   ;; BOZO how could this happen?
         (list (cons x.elt-fix x.elt-type)))))

(define flexset-predicate-def (x)
  (b* (((flexset x))
       ;; std::defset-compatible variable names
       ;;(stdx (intern-in-package-of-symbol "X" x.pred))
       ;; (stda (intern-in-package-of-symbol "A" 'acl2::foo)))
       (type-ref (concatenate 'string
                              "@(tsee "
                              (acl2::string-downcase (symbol-package-name x.name))
                              "::"
                              (acl2::string-downcase (symbol-name x.name))
                              ")"))
       (y (intern-in-package-of-symbol "Y" x.pred))
       (a (intern-in-package-of-symbol "A" x.pred))
       (booleanp-of-pred (acl2::packn-pos (list 'booleanp-of x.pred) x.pred))
       (setp-when-pred (acl2::packn-pos (list 'setp-when- x.pred) x.pred))
       (elt-type-of-head-when-pred (acl2::packn-pos (list x.elt-type '-of-head-when- x.pred)
                                                    x.pred))
       (pred-of-tail-when-pred (acl2::packn-pos (list x.pred '-of-tail-when- x.pred)
                                                 x.pred))
       (pred-of-insert (acl2::packn-pos (list x.pred '-of-insert) x.pred))
       (elt-type-when-in-pred-binds-free-xvar
        (acl2::packn-pos (list x.elt-type '-when-in- x.pred '-binds-free- x.xvar)
                         x.pred))
       (pred-of-union (acl2::packn-pos (list x.pred '-of-union) x.pred))
       (pred-of-difference (acl2::packn-pos (list x.pred '-of-difference) x.pred))
       (pred-of-delete (acl2::packn-pos (list x.pred '-of-delete) x.pred))
       )
    (if x.already-definedp
        '(progn)
      `(define ,x.pred (,x.xvar)
         :parents (,x.name)
         :short ,(concatenate 'string "Recognizer for " type-ref ".")
         ,@(if x.measure `(:measure ,x.measure)
             ())
         (if (atom ,x.xvar)
             (null ,x.xvar)
           (and (,x.elt-type (car ,x.xvar))
                (or (null (cdr ,x.xvar))
                    (and (consp (cdr ,x.xvar))
                         (acl2::fast-<< (car ,x.xvar) (cadr ,x.xvar))
                         (,x.pred (cdr ,x.xvar))))))
         :no-function t
         ///
         (defrule ,booleanp-of-pred
           (booleanp (,x.pred ,x.xvar)))
         (defrule ,setp-when-pred
           (implies (,x.pred ,x.xvar)
                    (set::setp ,x.xvar))
           :enable set::setp
           :rule-classes (:rewrite ;; :forward-chaining
                                   )) ; ??
         (defrule ,elt-type-of-head-when-pred
           (implies (,x.pred ,x.xvar)
                    ,(cond ((eq x.elementp-of-nil t)
                            `(,x.elt-type (set::head ,x.xvar)))
                           ((eq x.elementp-of-nil nil)
                            `(equal (,x.elt-type (set::head ,x.xvar))
                                    (not (set::empty ,x.xvar))))
                           (t `(implies (not (set::empty ,x.xvar))
                                        (,x.elt-type (set::head ,x.xvar))))))
           :enable (set::head set::empty))
         (defrule ,pred-of-tail-when-pred
           (implies (,x.pred ,x.xvar)
                    (,x.pred (set::tail ,x.xvar)))
           :enable set::tail)
         (defrule ,pred-of-insert
           (equal (,x.pred (set::insert ,a ,x.xvar))
                  (and (,x.elt-type ,a)
                       (,x.pred (set::sfix ,x.xvar))))
           :enable (set::insert set::empty set::head set::tail set::setp))
         (defrule ,elt-type-when-in-pred-binds-free-xvar
           (implies (and (set::in ,a ,x.xvar) ; binds free X
                         (,x.pred ,x.xvar))
                    (,x.elt-type ,a))
           :enable (set::in set::head))
         (defrule ,pred-of-union
           (equal (,x.pred (set::union ,x.xvar ,y))
                  (and (,x.pred (set::sfix ,x.xvar))
                       (,x.pred (set::sfix ,y))))
           :enable (set::union set::empty set::setp set::head set::tail))
         (defrule ,pred-of-difference
           (implies (,x.pred ,x.xvar)
                    (,x.pred (set::difference ,x.xvar ,y)))
           :enable set::difference)
         (defrule ,pred-of-delete
           (implies (,x.pred ,x.xvar)
                    (,x.pred (set::delete ,a ,x.xvar)))
           :enable set::delete)))))


(define flexset-fix-def (x flagp)
  (b* (((flexset x))
       (pred-of-fix (acl2::packn-pos (list x.pred '-of- x.fix) x.name))
       (fix-when-pred (acl2::packn-pos (list x.fix '-when- x.pred) x.name))
       (empty-fix (acl2::packn-pos (list 'empty- x.fix) x.name)))
    (if x.fix-already-definedp
        '(progn)
      `(define ,x.fix ((,x.xvar ,x.pred))
         :parents (,x.name)
         :short ,(cat "@(call " (xdoc::full-escape-symbol x.fix)
                      ") is a usual @(see fty::fty) set fixing function.")
         :long ,(cat "<p>In the logic, we apply @(see? "
                     (xdoc::full-escape-symbol x.elt-fix)
                     ") to each member of the x.  In the execution, none of
                    that is actually necessary and this is just an inlined
                    identity function.</p>")
         ,@(and (getarg :measure-debug nil x.kwd-alist)
                `(:measure-debug t))
         ,@(and flagp `(:flag ,x.name))
         :progn t
         ; :inline t
         (mbe :logic ;; (if (set::empty ,x.xvar)
                     ;;     nil
                     ;;   (set::insert (,x.elt-fix (set::head ,x.xvar))
                     ;;                (,x.fix (set::tail ,x.xvar))))
              (if (,x.pred ,x.xvar) ,x.xvar nil)
              :exec ,x.xvar)
         :no-function t
         ///
         (defrule ,pred-of-fix
           (,x.pred (,x.fix ,x.xvar)))
         (defrule ,fix-when-pred
           (implies (,x.pred ,x.xvar)
                    (equal (,x.fix ,x.xvar) ,x.xvar)))
         (defrule ,empty-fix
           (implies (or (set::empty ,x.xvar)
                        (not (,x.pred ,x.xvar)))
                    (set::empty (,x.fix ,x.xvar))))))))

(define flexset-fix-postevents (x)
  :ignore-ok t
  :irrelevant-formals-ok t
  ;; sjw: The list versions do not carry over. I don't know what might be useful here.
  ())

(define flexset-fix-when-pred-thm (x flagp)
  (b* (((flexset x))
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


(defun flexset-count (x types)
  (b* (((flexset x))
       ((unless x.count) nil)
       (eltcount (flextypes-find-count-for-pred x.elt-type types)))
    `((define ,x.count ((,x.xvar ,x.pred))
        :returns (count natp
                        :rule-classes :type-prescription
                        :hints ('(:expand (,x.count ,x.xvar)
                                  :in-theory (disable ,x.count))))
        :measure (let ((,x.xvar (,x.fix ,x.xvar)))
                   ,x.measure)
        ,@(and (getarg :measure-debug nil x.kwd-alist)
               `(:measure-debug t))
        :verify-guards nil
        :progn t
        (if (or (set::empty ,x.xvar)
                (not (,x.pred ,x.xvar)))
            1
          (+ 1
             ,@(and eltcount `((,eltcount (set::head ,x.xvar))))
             (,x.count (set::tail ,x.xvar))))))))


(defun flexset-count-post-events (x types)
  (b* (((flexset x))
       ((unless x.count) nil)
       (eltcount (flextypes-find-count-for-pred x.elt-type types))
       ;; ((when (not eltcount)) nil)
       (foo-count-of-insert (intern-in-package-of-symbol (cat (symbol-name x.count) "-OF-INSERT") x.count))
       (foo-count-of-head  (intern-in-package-of-symbol (cat (symbol-name x.count) "-OF-HEAD") x.count))
       (foo-count-of-tail  (intern-in-package-of-symbol (cat (symbol-name x.count) "-OF-TAIL") x.count))
       (foo-count-when-empty  (intern-in-package-of-symbol (cat (symbol-name x.count) "-WHEN-EMPTY") x.count))
       (foo-count-when-not-empty  (intern-in-package-of-symbol (cat (symbol-name x.count) "-WHEN-NOT-EMPTY") x.count)))
    `((defthm ,foo-count-when-empty
        (implies (empty ,x.xvar)
                 (equal (,x.count ,x.xvar)
                        1))
        :hints (("Goal" :in-theory (enable ,x.count))))

      (defthm ,foo-count-when-not-empty
        (implies (and (not (empty ,x.xvar))
                      (,x.pred ,x.xvar))
                 (equal (,x.count ,x.xvar)
                        (+ 1
                           ,@(and eltcount `((,eltcount (set::head ,x.xvar))))
                           (,x.count (tail ,x.xvar)))))
        :hints (("Goal" :in-theory (enable ,x.count))))

      ,@(and eltcount
             `((defthm ,foo-count-of-head
                 (implies (and (not (empty ,x.xvar))
                               (,x.pred ,x.xvar))
                          (< (,eltcount (set::head ,x.xvar)) (,x.count ,x.xvar)))
                 :rule-classes :linear)))

      (defthm ,foo-count-of-tail
        (implies (and (not (empty ,x.xvar))
                      (,x.pred ,x.xvar))
                 (< (,x.count (set::tail ,x.xvar)) (,x.count ,x.xvar)))
        :rule-classes :linear
        :hints (("Goal" :in-theory (enable ,x.count))))

      (defthm ,foo-count-of-insert
        (implies (and (,x.pred b)
                      (,x.elt-type a)
                      (not (set::in a b)))
                 ,(if eltcount
                      `(equal (,x.count (set::insert a b))
                             (+ 1 (,eltcount a) (,x.count b)))
                    `(> (,x.count (set::insert a b))
                        (,x.count b))))
        :hints (("Goal" :expand ((:free (a b) (,x.count (set::insert a b))))))
        :rule-classes :linear))))
