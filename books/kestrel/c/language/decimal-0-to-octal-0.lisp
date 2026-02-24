; C Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
; Copyright (C) 2026 Kestrel Technology LLC (http://kestreltechnology.com)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C")

(include-book "abstract-syntax")

(include-book "kestrel/fty/deffold-map" :dir :system)

(local (include-book "kestrel/utilities/ordinals" :dir :system))

(acl2::controlled-configuration)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ decimal-0-to-octal-0
  :parents (abstract-syntax)
  :short "Mapping of decimal 0 to octal 0."
  :long
  (xdoc::topstring
   (xdoc::p
    "The abstract syntax for integer constants (see @(tsee iconst))
     allows constants with value 0 and decimal base.
     This is more liberal than the actual C syntax,
     where an integer constant starting with (of consisting just of) 0,
     and without a hexadecimal prefix, is always octal.
     Here we define a family of operations on the abstract syntax
     to map any decimal 0 integer constant to an octal 0 integer constant;
     signedness and length suffixes are preserved."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deffold-map dec0-to-oct0
  :short "Map integer constants in decimal base with value 0
          to integer constants in octal base with value 0."
  :types (iconst
          iconst-option
          const
          obj-declor
          obj-adeclor
          tyname
          expr-fixtypes
          expr-option
          struct-declon
          struct-declon-list
          tag-declon
          param-declon
          param-declon-list
          fun-declor
          fun-adeclor
          fun-declon
          initer
          initer-option
          obj-declon
          label
          stmt-fixtypes
          fundef
          ext-declon
          ext-declon-list
          transunit
          transunit-ensemble)
  :override
  ((iconst (if (and (iconst-base-case (iconst->base iconst) :dec)
                    (equal (iconst->value iconst) 0))
               (change-iconst iconst :base (iconst-base-oct))
             (iconst-fix iconst)))))
