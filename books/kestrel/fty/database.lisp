; C Library
;
; Copyright (C) 2025 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "FTY")

(include-book "centaur/fty/database" :dir :system)
(include-book "std/util/deflist" :dir :system)
(include-book "xdoc/defxdoc-plus" :dir :system)

(local (include-book "std/typed-lists/symbol-listp" :dir :system))

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(acl2::defxdoc+ database
  :parents (fty-extensions)
  :short "Extensions for the FTY database."
  :long
  (xdoc::topstring
   (xdoc::p
    "The file @('[books]/centaur/fty/database.lisp') defines aggregates
     that encode fixtype information in the fixtype table.
     Here we define some extensions of these aggregates,
     e.g. lists of some of those types,
     and operations on those aggregates."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::deflist flexprod-field-listp (x)
  :short "Recognize lists of @('flexprod-field-p') values."
  (flexprod-field-p x)
  :true-listp t
  :elementp-of-nil nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::deflist flexprod-listp (x)
  :short "Recognize lists of @('flexprod') values."
  (flexprod-p x)
  :true-listp t
  :elementp-of-nil nil)

;;;;;;;;;;;;;;;;;;;;

(define flexprod-list->kind-list ((prods flexprod-listp))
  :returns (kinds true-listp)
  :short "Lift @('flexprod->kind') to lists."
  (cond ((endp prods) nil)
        (t (cons (flexprod->kind (car prods))
                 (flexprod-list->kind-list (cdr prods))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define flex->name (info)
  :returns (name symbolp)
  :short "Name of a sum, list, alist, transparent sum, set, or omap type,
          given the information associated to the type."
  (b* ((name (cond ((flexsum-p info) (flexsum->name info))
                   ((flexlist-p info) (flexlist->name info))
                   ((flexalist-p info) (flexalist->name info))
                   ((flextranssum-p info) (flextranssum->name info))
                   ((flexset-p info) (flexset->name info))
                   ((flexomap-p info) (flexomap->name info))
                   (t (raise "Internal error: malformed type ~x0." info))))
       ((unless (symbolp name))
        (raise "Internal error: malformed type name ~x0." name)))
    name))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define flex-list->name-list ((infos true-listp))
  :returns (names symbol-listp)
  :short "Lift @(tsee flex->name) to lists."
  (cond ((endp infos) nil)
        (t (cons (flex->name (car infos))
                 (flex-list->name-list (cdr infos))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
