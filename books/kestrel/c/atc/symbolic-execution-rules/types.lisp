; C Library
;
; Copyright (C) 2022 Kestrel Institute (http://www.kestrel.edu)
; Copyright (C) 2022 Kestrel Technology LLC (http://kestreltechnology.com)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C")

(include-book "../../language/types")

(local (xdoc::set-default-parents atc-symbolic-execution-rules))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection atc-tyname-to-type-rules
  :short "Rules for turning type names into types."
  :long
  (xdoc::topstring
   (xdoc::p
    "Type names arise, in quoted constant form,
     from the abstract syntax that is symbolically executed.
     In some circumstance, these type names are turned into types,
     via @(tsee tyname-to-type).
     If we just enabled the executable counterpart of this function
     we would end up with types in quoted constant form.
     Instead, we want to keep types as terms with constructors,
     particularly because some types include identifiers (e.g. structure types),
     and we want to keep identifiers as terms with constructors
     instead of in quoted constant form (see @(see atc-identifier-rules).")
   (xdoc::p
    "Thus, here we collect rules to rewrite quoted type names
     to types that are terms with constructors."))

  (defval *atc-tyname-to-type-rules*
    '(tyname-to-type
      tyname-to-type-aux
      (:e tyname->tyspec)
      (:e tyname->declor)
      (:e obj-adeclor-kind)
      (:e obj-adeclor-pointer->decl)
      (:e obj-adeclor-array->decl)
      tyspecseq-to-type
      (:e tyspecseq-kind)
      (:e tyspecseq-struct->tag))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection atc-type-kind-rules
  :short "Rules for resolving @(tsee type-kind) on given types."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are used to relieve certain hypotheses in rules
     that involve @(tsee type-kind) being applied to
     certain constructed types."))

  (defruled type-kind-of-type-schar
    (equal (type-kind (type-schar))
           :schar))

  (defruled type-kind-of-type-uchar
    (equal (type-kind (type-uchar))
           :uchar))

  (defruled type-kind-of-type-sshort
    (equal (type-kind (type-sshort))
           :sshort))

  (defruled type-kind-of-type-ushort
    (equal (type-kind (type-ushort))
           :ushort))

  (defruled type-kind-of-type-sint
    (equal (type-kind (type-sint))
           :sint))

  (defruled type-kind-of-type-uint
    (equal (type-kind (type-uint))
           :uint))

  (defruled type-kind-of-type-slong
    (equal (type-kind (type-slong))
           :slong))

  (defruled type-kind-of-type-ulong
    (equal (type-kind (type-ulong))
           :ulong))

  (defruled type-kind-of-type-sllong
    (equal (type-kind (type-sllong))
           :sllong))

  (defruled type-kind-of-type-ullong
    (equal (type-kind (type-ullong))
           :ullong))

  (defval *atc-type-kind-rules*
    '(type-kind-of-type-schar
      type-kind-of-type-uchar
      type-kind-of-type-sshort
      type-kind-of-type-ushort
      type-kind-of-type-sint
      type-kind-of-type-uint
      type-kind-of-type-slong
      type-kind-of-type-ulong
      type-kind-of-type-sllong
      type-kind-of-type-ullong)))
