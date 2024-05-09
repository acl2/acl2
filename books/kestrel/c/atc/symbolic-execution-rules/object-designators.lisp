; C Library
;
; Copyright (C) 2024 Kestrel Institute (http://www.kestrel.edu)
; Copyright (C) 2024 Kestrel Technology LLC (http://kestreltechnology.com)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C")

(include-book "../../language/computation-states")
(include-book "../symbolic-computation-states")

(local (xdoc::set-default-parents atc-symbolic-execution-rules))

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection atc-object-designator-rules
  :short "Rules about object designators."
  :long
  (xdoc::topstring
   (xdoc::p
    "The first rule serves to handle access to static objects.
     We need to reduce @(tsee objdesign-of-var),
     which arises when opening @(tsee exec-ident),
     to the object designator of the static object,
     under the hypothesis that
     @(tsee read-static-var) on that variable yields a value
     and that the variable is not in automatic storage.")
   (xdoc::p
    "The second and third rules are used in the @(tsee defstruct)-specific
     theorems generated for symbolic execution of array member accesses.")
   (xdoc::p
    "The remaining rules are used in the modular proofs
     about variables in symbol tables.")
   (xdoc::p
    "The constant that collects the rules also includes
     some rules proved elsewhere."))

  (defruled objdesign-of-var-when-static
    (implies (and (valuep (read-static-var id compst))
                  (not (var-autop id compst)))
             (equal (objdesign-of-var id compst)
                    (objdesign-static id)))
    :enable (objdesign-of-var
             var-autop
             read-static-var)
    :disable omap::assoc-when-assoc-tail
    :prep-lemmas
    ((defrule lemma
       (iff (objdesign-of-var-aux var frame scopes)
            (var-in-scopes-p var scopes))
       :induct t
       :enable (objdesign-of-var-aux
                var-in-scopes-p))))

  (defruled not-nil-when-objdesignp
    (implies (objdesignp x)
             x)
    :rule-classes :compound-recognizer)

  (defruled read-object-of-objdesign-member
    (implies (and (valuep (read-object objdes compst))
                  (value-case (read-object objdes compst) :struct))
             (equal (read-object (objdesign-member objdes mem) compst)
                    (value-struct-read mem (read-object objdes compst))))
    :do-not-induct t
    :expand (read-object (objdesign-member objdes mem) compst))

  (defruled objdesign-of-var-of-add-var-iff
    (iff (objdesign-of-var var (add-var var2 val compst))
         (or (equal (ident-fix var)
                    (ident-fix var2))
             (objdesign-of-var var compst)))
    :enable (objdesign-of-var
             objdesign-of-var-aux
             add-var
             push-frame
             pop-frame
             top-frame
             compustate-frames-number
             len))

  (defruled objdesign-of-var-of-enter-scope-iff
    (implies (> (compustate-frames-number compst) 0)
             (iff (objdesign-of-var var (enter-scope compst))
                  (objdesign-of-var var compst)))
    :enable (objdesign-of-var
             objdesign-of-var-aux
             enter-scope
             push-frame
             pop-frame
             top-frame
             compustate-frames-number
             len))

  (defruled objdesign-of-var-of-add-frame-when-read-object-static
    (implies (valuep (read-object (objdesign-static var) compst))
             (equal (objdesign-of-var var (add-frame fun compst))
                    (objdesign-static var)))
    :enable (objdesign-of-var
             objdesign-of-var-aux
             add-frame
             push-frame
             top-frame
             read-object)
    :disable omap::assoc-when-assoc-tail)

  (defruled objdesign-of-var-aux-iff-var-in-scopes
    (iff (objdesign-of-var-aux var frame scopes)
         (var-in-scopes-p var scopes))
    :induct t
    :enable (objdesign-of-var-aux
             var-in-scopes-p))

  (defruled objdesign-of-var-of-update-var-iff
    (iff (objdesign-of-var var (update-var var2 val compst))
         (or (equal (ident-fix var)
                    (ident-fix var2))
             (objdesign-of-var var compst)))
    :enable (objdesign-of-var
             update-var
             push-frame
             pop-frame
             top-frame
             compustate-frames-number
             var-in-scopes-p
             objdesign-of-var-aux-iff-var-in-scopes
             var-in-scopes-p-of-update-var-aux
             len))

  (defruled objdesign-of-var-of-update-static-var-iff
    (iff (objdesign-of-var var (update-static-var var2 val compst))
         (or (equal (ident-fix var) (ident-fix var2))
             (objdesign-of-var var compst)))
    :enable (objdesign-of-var
             update-static-var
             top-frame))

  (defruled read-object-of-objdesign-of-var-of-add-var
    (implies (objdesign-of-var var (add-var var2 val compst))
             (equal (read-object (objdesign-of-var var (add-var var2 val compst))
                                 (add-var var2 val compst))
                    (if (equal (ident-fix var2)
                               (ident-fix var))
                        (remove-flexible-array-member val)
                      (read-object (objdesign-of-var var compst) compst))))
    :enable (read-object-of-objdesign-of-var-to-read-var
             read-var-of-add-var
             objdesign-of-var-of-add-var-iff))

  (defruled read-object-of-objdesign-of-var-of-enter-scope
    (implies (and (> (compustate-frames-number compst) 0)
                  (objdesign-of-var var (enter-scope compst)))
             (equal (read-object (objdesign-of-var var (enter-scope compst))
                                 (enter-scope compst))
                    (read-object (objdesign-of-var var compst) compst)))
    :enable (read-object-of-objdesign-of-var-to-read-var
             read-var-of-enter-scope
             objdesign-of-var-of-enter-scope-iff))

  (defruled read-object-of-objdesign-of-var-of-update-var
    (implies (objdesign-of-var var (update-var var2 val compst))
             (equal (read-object
                     (objdesign-of-var var (update-var var2 val compst))
                     (update-var var2 val compst))
                    (if (equal (ident-fix var2)
                               (ident-fix var))
                        (remove-flexible-array-member val)
                      (read-object (objdesign-of-var var compst) compst))))
    :enable (read-object-of-objdesign-of-var-to-read-var
             read-var-of-update-var
             objdesign-of-var-of-update-var-iff))

  (defruled objdesign-of-var-of-update-object-iff
    (iff (objdesign-of-var var (update-object objdes val compst))
         (objdesign-of-var var compst))
    :enable (objdesign-of-var
             update-object
             top-frame))

  (defruled objdesign-of-var-of-update-object
    (equal (objdesign-of-var var (update-object objdes val compst))
           (objdesign-of-var var compst))
    :enable (objdesign-of-var
             update-object
             top-frame))

  (defruled read-object-auto/static-of-update-object-alloc
    (implies (and (member-equal (objdesign-kind objdes) '(:auto :static))
                  (equal (objdesign-kind objdes2) :alloc))
             (equal (read-object objdes (update-object objdes2 val compst))
                    (read-object objdes compst)))
    :enable (read-object
             update-object))

  (defruled read-object-of-objdesign-of-var-of-update-static-var-different
    (implies (and (objdesign-of-var var (update-static-var var2 val compst))
                  (not (equal (ident-fix var)
                              (ident-fix var2))))
             (equal (read-object
                     (objdesign-of-var var (update-static-var var2 val compst))
                     (update-static-var var2 val compst))
                    (read-object (objdesign-of-var var compst) compst)))
    :enable (objdesign-of-var-of-update-static-var-iff
             read-object-of-objdesign-of-var-to-read-var
             read-var-of-update-static-var-different))

  (defruled read-object-of-objdesign-of-var-of-update-static-var-same
    (implies (not (var-autop var compst))
             (equal (read-object
                     (objdesign-of-var var (update-static-var var val compst))
                     (update-static-var var val compst))
                    (remove-flexible-array-member val)))
    :enable (read-object-of-objdesign-of-var-to-read-var
             read-var-of-update-static-var-same
             objdesign-of-var-of-update-static-var-iff))

  (defruled objdesign-of-var-of-if*-when-both-objdesign-of-var
    (implies (and (objdesign-of-var var b)
                  (objdesign-of-var var c))
             (objdesign-of-var var (if* a b c)))
    :enable if*)

  (defruled read-object-of-objdesign-static-to-objdesign-of-var
    (implies (and (objdesign-of-var id compst)
                  (not (var-autop id compst)))
             (equal (read-object (objdesign-static id) compst)
                    (read-object (objdesign-of-var id compst) compst)))
    :enable (read-object-of-objdesign-of-var-to-read-var
             read-var-to-read-static-var
             read-object
             read-static-var))

  (defval *atc-object-designator-rules*
    '(objdesign-of-var-when-static
      not-nil-when-objdesignp
      read-object-of-objdesign-member
      objdesignp-of-objdesign-of-var-when-valuep-of-read-var
      read-object-of-objdesign-of-var-to-read-var
      objdesign-of-var-when-valuep-of-read-var)))
