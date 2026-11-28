; Unicode Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "UNICODE")

(include-book "runs")

(acl2::controlled-configuration)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ block-tables
  :parents (tables)
  :short "Tables of runs of code points that are in the same block."
  :long
  (xdoc::topstring
   (xdoc::p
    "The @('Block') property assigns to every code point
     the block that it is in.
     A block is a named range of code points,
     such as @('Basic Latin'), from U+0000 to U+007F;
     blocks do not overlap [Unicode, Section 3.4, D10b].
     A code point that is in no block
     has the value @('No_Block').")
   (xdoc::p
    "The values are the names of the blocks, as strings,
     written as in the file @('Blocks.txt')
     of the Unicode Character Database,
     with spaces between their words;
     there are some three hundred and fifty of them,
     and each version of Unicode adds a few.
     The property is represented as a list of @(see runs).
     The runs of the generated tables
     are the blocks and the gaps between them,
     which are runs with the value @('No_Block')."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruns block
  :property "Block"
  :value-type stringp
  :value-pred stringp
  :value-fix acl2::str-fix
  :default "No_Block")

;;;;;;;;;;;;;;;;;;;;

(define block-run-list-names ((runs block-run-listp))
  :returns (names string-listp
                  :hints (("Goal"
                           :induct t
                           :in-theory (enable string-listp))))
  :short "The names of the blocks of a list of runs."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are the values of the runs, in order,
     without the value @('No_Block') of the gaps between blocks.
     In each generated table no name occurs twice,
     that is, each block is one run;
     this is checked by evaluation in the book that has the table."))
  (cond ((endp runs) nil)
        (t (b* (((block-run run) (car runs))
                (names (block-run-list-names (cdr runs))))
             (if (equal run.value "No_Block")
                 names
               (cons run.value names)))))
  :verify-guards :after-returns
  :hooks (:fix)

  ///

  (defrule len-of-block-run-list-ranges-when-not-member-of-names
    (implies (and (not (member-equal (acl2::str-fix name)
                                     (block-run-list-names runs)))
                  (not (equal (acl2::str-fix name) "No_Block")))
             (equal (block-run-list-ranges name runs)
                    nil))
    :induct t
    :enable (block-run-list-ranges
             member-equal))

  (defrule len-of-block-run-list-ranges-when-no-duplicatesp-of-names
    (implies (and (no-duplicatesp-equal (block-run-list-names runs))
                  (not (equal (acl2::str-fix name) "No_Block")))
             (<= (len (block-run-list-ranges name runs)) 1))
    :rule-classes (:rewrite :linear)
    :induct t
    :enable (block-run-list-ranges
             no-duplicatesp-equal
             len)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection block-run-table
  :short "Write a list of runs of @('Block') compactly."
  :long
  (xdoc::topstring
   (xdoc::p
    "Each run is written as a triple
     of the minimum code point, the maximum code point,
     and the name of the block, as a string:")
   (xdoc::codeblock
    "(block-run-table"
    " (#x0000 #x007F \"Basic Latin\")"
    " (#x0080 #x00FF \"Latin-1 Supplement\"))")
   (xdoc::p
    "This expands to a call of @('list')
     on one call of the constructor of runs for each triple:
     see @(see run-tables)."))

  (defmacro block-run-table (&rest triples)
    `(list ,@(run-table-forms triples
                              :literal
                              nil
                              'block-run
                              'block-run-table))))
