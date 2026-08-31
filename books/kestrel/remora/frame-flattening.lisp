; Remora Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Authors: Alessandro Coglio (www.alessandrocoglio.info)
;          Sarah Johnson

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "REMORA")

(include-book "abstract-syntax-structurals")
(include-book "abstract-syntax-core")
(include-book "desugaring") ; char-lit-list-desugar

(include-book "kestrel/fty/deffold-map" :dir :system)

(local (include-book "kestrel/utilities/ordinals" :dir :system))
(local (include-book "std/typed-lists/nat-listp" :dir :system))

(acl2::controlled-configuration)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(local (in-theory (enable* ast-corep-rules)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ frame-flattening
  :parents (abstract-syntax)
  :short "Frame flattening."
  :long
  (xdoc::topstring
   (xdoc::p
    "This unnests nested frame, bracket, and array expressions,
     according to the conditions specified by @(tsee flatten-merge).
     It could be thought of as
     a normalizing transformation.
     It is part of [impl],
     and [tutor] describes it as syntactic sugar,
     but it is not part of @(see desugaring).")
   (xdoc::p
    "Currently in [impl], it is applied at each bracket
     expression's parse site to the frame that the bracket
     notation denotes. Here, it is applied as a pass over
     the post-parse AST prior to desugaring, arranged to yield
     the same results as [impl]. @(tsee expr-flatten-brackets)
     walks the AST looking for bracket expressions, and
     @(tsee flatten-frames-in-expr) does the merging at each
     one it finds following only frame and bracket spines.
     So a frame written explicitly with @('frame') is merged
     into its parent only when an enclosing bracket reaches it."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define all-same-len-p ((xss true-list-listp))
  :returns (yes/no booleanp)
  :short "Check whether all the lists in a list have the same length."
  :long
  (xdoc::topstring
   (xdoc::p
    "This belongs to a more general library."))
  (or (endp xss)
      (endp (cdr xss))
      (and (equal (len (car xss))
                  (len (cadr xss)))
           (all-same-len-p (cdr xss)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define expr-array-likep ((expr exprp))
  :returns (yes/no booleanp)
  :short "Recognizer for array-like expressions."
  :long
  (xdoc::topstring
   (xdoc::p
    "An expression is array-like if it "
     (xdoc::seetopic "desugaring" "desugars")
     " to a non-empty array.")
   (xdoc::p
    "This matches [impl], whose parser turns atoms and strings
     into arrays as it parses, so its flattening sees arrays
     where we still see atoms and strings."))
  (expr-case expr
             :array t
             :atom t
             :string (consp expr.chars)
             :otherwise nil))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::deflist expr-array-like-listp (x)
  :guard (expr-listp x)
  :short "Recognizer for a true list of array-like expressions."
  (expr-array-likep x))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define expr-array-like->dims ((expr exprp))
  :guard (expr-array-likep expr)
  :returns (dims nat-listp)
  :short "Get the dimensions of an array-like expression."
  (expr-case expr
             :array expr.dims
             :atom nil
             :string (list (len expr.chars))
             :otherwise nil)
  :guard-hints (("Goal" :in-theory (enable expr-array-likep))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::defprojection expr-array-like-list->dims ((x expr-listp))
  :guard (expr-array-like-listp x)
  :returns (dimss nat-list-listp)
  :short "Lift @(tsee expr-array-like->dims) to lists."
  (expr-array-like->dims x))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define expr-array-like->atoms ((expr exprp))
  :guard (expr-array-likep expr)
  :returns (atoms atom-listp)
  :short "Get the atoms of an array-like expression."
  :long
  (xdoc::topstring
   (xdoc::p
    "For a string expression, these are the atoms obtained by "
    (xdoc::seetopic "char-lit-list-desugar" "desugaring")
    "."))
  (expr-case expr
             :array expr.atoms
             :atom (list expr.atom)
             :string (atom-base-list
                      (base-lit-int-list
                       (char-lit-list-desugar expr.chars)))
             :otherwise nil)
  :guard-hints (("Goal" :in-theory (enable expr-array-likep))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::defprojection expr-array-like-list->atoms ((x expr-listp))
  :guard (expr-array-like-listp x)
  :returns (atomss atom-list-listp)
  :short "Lift @(tsee expr-array-like->atoms) to lists."
  (expr-array-like->atoms x))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define expr-frame-likep ((expr exprp))
  :returns (yes/no booleanp)
  :short "Recognizer for frame-like expressions."
  :long
  (xdoc::topstring
   (xdoc::p
    "An expression is frame-like if it "
     (xdoc::seetopic "desugaring" "desugars")
     " to a non-empty frame.")
   (xdoc::p
    "This matches [impl], whose parser builds the frame that
     bracket notation denotes as it parses, so its flattening
     sees frames where we still see brackets."))
  (expr-case expr
             :bracket t
             :frame t
             :otherwise nil))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::deflist expr-frame-like-listp (x)
  :guard (expr-listp x)
  :short "Recognizer for a true list of frame-like expressions."
  (expr-frame-likep x))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define expr-frame-like->dims ((expr exprp))
  :guard (expr-frame-likep expr)
  :returns (dims nat-listp)
  :short "Get the dimensions of a frame-like expression."
  (expr-case expr
             :bracket (list (len expr.exprs))
             :frame expr.dims
             :otherwise nil)
  :guard-hints (("Goal" :in-theory (enable expr-frame-likep))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::defprojection expr-frame-like-list->dims ((x expr-listp))
  :guard (expr-frame-like-listp x)
  :returns (dimss nat-list-listp)
  :short "Lift @(tsee expr-frame-like->dims) to lists."
  (expr-frame-like->dims x))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define expr-frame-like->exprs ((expr exprp))
  :guard (expr-frame-likep expr)
  :returns (exprs expr-listp)
  :short "Get the sub-expressions of a frame-like expression."
  (expr-case expr
             :bracket expr.exprs
             :frame expr.exprs
             :otherwise nil)
  :guard-hints (("Goal" :in-theory (enable expr-frame-likep))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::defprojection expr-frame-like-list->exprs ((x expr-listp))
  :guard (expr-frame-like-listp x)
  :returns (exprss expr-list-listp)
  :short "Lift @(tsee expr-frame-like->exprs) to lists."
  (expr-frame-like->exprs x))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define flatten-merge ((dims nat-listp)
                       (exprs expr-listp)
                       (bracketp booleanp))
  :guard (consp exprs)
  :returns (expr exprp)
  :hooks nil
  :short "Merge already-flattened sub-expressions into their parent."
  :long
  (xdoc::topstring
   (xdoc::p
    "Given the dimensions @('[a1 ... aN]') of the parent expression
     and its already-flattened sub-expressions @('f1') to @('fQ'),
     there are three cases.")
   (xdoc::ul
    (xdoc::li
     "If all of @('f1') to @('fQ') are frame-like expressions
      with identical dimensions @('[b1 ... bM]') and the same number
      of sub-expressions, we return a frame with dimensions
      @('[a1 ... aN b1 ... bM]') and all the sub-expressions of
      @('f1') to @('fQ').")
    (xdoc::li
     "If all of @('f1') to @('fQ') are array-like expressions
      with identical dimensions and the same number
      of atoms, we return an array formed analogously.")
    (xdoc::li
     "Otherwise, we return the parent with @('f1') to @('fQ')
      as its sub-expressions, denoted @('no-further'), conveying
      that we do not further flatten it. A bracket parent stays
      a bracket so that @(see desugaring) can turn it into a frame
      later.")))
  (b* ((no-further (if bracketp
                       (make-expr-bracket :exprs exprs)
                     (make-expr-frame :dims dims :exprs exprs)))
       ((when (expr-frame-like-listp exprs))
        (b* ((dimss (expr-frame-like-list->dims exprs))
             (exprss (expr-frame-like-list->exprs exprs))
             ((unless (list-repeatp dimss)) no-further)
             ((unless (all-same-len-p exprss)) no-further)
             ((unless (consp (append-all exprss))) no-further))
          (make-expr-frame :dims (append dims (car dimss))
                           :exprs (append-all exprss))))
       ((when (expr-array-like-listp exprs))
        (b* ((dimss (expr-array-like-list->dims exprs))
             (atomss (expr-array-like-list->atoms exprs))
             ((unless (list-repeatp dimss)) no-further)
             ((unless (all-same-len-p atomss)) no-further)
             ((unless (consp (append-all atomss))) no-further))
          (make-expr-array :dims (append dims (car dimss))
                           :atoms (append-all atomss)))))
    no-further)
  :guard-hints
  (("Goal" :in-theory (enable true-list-listp-when-expr-list-listp
                              true-list-listp-when-atom-list-listp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines flatten-frames-in-exprs
  :short "Flatten frames in expressions and lists of expressions."

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define flatten-frames-in-expr ((expr exprp))
    :returns (flat-expr exprp)
    :short "Flatten frames in an expression."
    :long
    (xdoc::topstring
     (xdoc::p
      "This is the counterpart of [impl]'s @('flattenExp'), which
       is applied at each bracket expression's parse site.
       We recursively flatten the sub-expressions of a frame
       or bracket expression, then merge them into it according
       to @(tsee flatten-merge). This traversal follows only
       frame and bracket spines. To reach the bracket expressions
       elsewhere in an AST, use @(tsee expr-flatten-brackets)."))
    (expr-case
     expr
     :frame (b* ((exprs (flatten-frames-in-expr-list expr.exprs)))
              (flatten-merge expr.dims exprs nil))
     :bracket (b* ((exprs (flatten-frames-in-expr-list expr.exprs)))
                (flatten-merge (list (len exprs)) exprs t))
     :otherwise (expr-fix expr))
    :measure (expr-count expr))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define flatten-frames-in-expr-list ((exprs expr-listp))
    :returns (flat-exprs expr-listp)
    :short "Flatten frames in a list of expressions."
    :long
    (xdoc::topstring
     (xdoc::p
      "Each expression in the list is processed independently."))
    (cond ((endp exprs) nil)
          (t (cons (flatten-frames-in-expr (car exprs))
                   (flatten-frames-in-expr-list (cdr exprs)))))
    :measure (expr-list-count exprs)

    ///

    (defret consp-of-flatten-frames-in-expr-list
      (equal (consp flat-exprs)
             (consp exprs))
      :hints (("Goal" :expand ((flatten-frames-in-expr-list exprs))))))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  :verify-guards nil ; done below

  :flag-local nil

  ///

  (fty::deffixequiv-mutual flatten-frames-in-exprs)

  (verify-guards flatten-frames-in-expr
    :hints (("Goal" :in-theory (enable
                                true-list-listp-when-expr-list-listp
                                true-list-listp-when-atom-list-listp)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deffold-map flatten-brackets
  :short "Flatten the bracket expressions in an AST."
  :long
  (xdoc::topstring
   (xdoc::p
    "This walks the whole AST and applies @(tsee flatten-frames-in-expr)
       at each bracket expression, which is where [impl] applies its
       flattening.")
   (xdoc::p
    "A frame expression written explicitly with @('frame')
       has no override here, so it is not merged into its parent;
       it is only merged if some enclosing bracket expression
       reaches it via @(tsee flatten-frames-in-expr)."))
  :types (shapes/ispaces
          types
          type-option
          var+type?
          var+type?-list
          exprs/atoms/binds)
  :override
  ((expr :bracket (b* ((exprs (expr-list-flatten-brackets expr.exprs)))
                    (flatten-frames-in-expr
                     (make-expr-bracket :exprs exprs)))))
  :name ast-flatten-brackets)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection corep-of-flatten-frames
  :short "Frame flattening core ASTs yields core ASTs."

  (defrulel atom-list-list-corep-of-expr-array-like-list->atoms
    (implies (and (expr-list-corep exprs)
                  (expr-array-like-listp exprs))
             (atom-list-list-corep (expr-array-like-list->atoms exprs)))
    :induct t
    :enable (expr-array-like-list->atoms
             expr-array-like->atoms
             expr-array-like-listp
             expr-array-likep))

  (defrulel expr-list-list-corep-of-expr-frame-like-list->exprs
    (implies (and (expr-list-corep exprs)
                  (expr-frame-like-listp exprs))
             (expr-list-list-corep (expr-frame-like-list->exprs exprs)))
    :induct t
    :enable (expr-frame-like-list->exprs
             expr-frame-like->exprs
             expr-frame-like-listp
             expr-frame-likep))

  (defrulel expr-corep-of-flatten-merge
    (implies (and (expr-list-corep exprs)
                  (consp exprs)
                  (not bracketp))
             (expr-corep (flatten-merge dims exprs bracketp)))
    :enable (flatten-merge
             expr-array-likep
             expr-frame-likep
             expr-array-like->atoms
             expr-frame-like->exprs
             expr-array-like-listp
             expr-frame-like-listp))

  (defret-mutual corep-of-flatten-frames
    (defret expr-corep-of-flatten-frames-in-expr
      (expr-corep flat-expr)
      :hyp (expr-corep expr)
      :fn flatten-frames-in-expr)
    (defret expr-list-corep-of-flatten-frames-in-expr-list
      (expr-list-corep flat-exprs)
      :hyp (expr-list-corep exprs)
      :fn flatten-frames-in-expr-list)
    :mutual-recursion flatten-frames-in-exprs
    :hints (("Goal" :in-theory (enable flatten-frames-in-expr
                                       flatten-frames-in-expr-list)))))
