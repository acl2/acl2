; Unicode Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "UNICODE")

(include-book "ranges")

(acl2::controlled-configuration)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ runs
  :parents (tables)
  :short "Tables of runs of code points
          that have the same value of a property."
  :long
  (xdoc::topstring
   (xdoc::p
    "Some properties of the Unicode Character Database
     give every code point one of many values,
     and have no value that most code points share
     and that a table could leave out:
     @('General_Category'), @('Script') and @('Bidi_Class') are like that.
     But code points that are next to each other often have the same value.
     So we represent such a property as a list of runs.
     A run consists of a first code point, a last code point,
     and the value that every code point from the first to the last has.")
   (xdoc::p
    "The generated tables list the runs in increasing order,
     and the runs cover every code point exactly once.
     That is a checkable property of a list of runs,
     and under it the value of a code point
     is the value of the one run that contains it.")
   (xdoc::p
    "The code points that have a given value form a list of @(see ranges),
     which is obtained from the list of runs
     by keeping the runs with that value.
     A theorem relates the two views,
     so that what is proved or computed with lists of ranges
     (see @(see range-operations))
     applies to the values of the property.
     This is how facts about all the code points are proved here:
     by evaluation on a few thousand ranges,
     not on more than a million code points.")
   (xdoc::p
    "The value of a property can also be a set of values,
     as for @('Script_Extensions').
     Then the value of a run is a list,
     and the list of ranges of interest is that of the code points
     whose list contains a given element.")
   (xdoc::p
    "The types, the functions and the theorems are the same
     for every such property, except for the type of the values.
     The macro @(tsee defruns) introduces them for a property."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection defruns
  :short "Introduce the tables of runs of a property."
  :long
  (xdoc::topstring
   (xdoc::p
    "The call")
   (xdoc::codeblock
    "(defruns general-category"
    "  :property \"General_Category\""
    "  :value-type general-category"
    "  :value-pred general-category-p"
    "  :value-fix general-category-fix"
    "  :default (general-category-unassigned))")
   (xdoc::p
    "introduces the following,
     where @('general-category') is the name given
     and stands for the name of any property:")
   (xdoc::ul
    (xdoc::li
     "@('general-category-run'),
      the fixtype of the runs: a product of
      a minimum code point, a maximum code point
      and a value of the type @(':value-type').")
    (xdoc::li
     "@('general-category-run-list'),
      the fixtype of the lists of runs.")
    (xdoc::li
     "@('general-category-run-list-lookup'),
      which returns the value of the first run of a list
      that contains a code point,
      or the default value @(':default') if no run does.")
    (xdoc::li
     "@('general-category-run-list-ranges'),
      which returns the ranges of the runs of a list
      that have a given value.")
    (xdoc::li
     "@('general-category-run-list-covers-p'),
      which checks that the runs of a list cover,
      in order and exactly once,
      the code points from a minimum to a maximum.")
    (xdoc::li
     "The theorem @('code-point-in-general-category-run-list-ranges'):
      if a list of runs covers every code point,
      a code point is in the ranges of a value
      exactly when its value in the list is that value.
      There are three more theorems,
      of which this one is a consequence."))
   (xdoc::p
    "With @(':elements t') the values are lists
     and stand for sets of elements
     of the type recognized by @(':element-pred').
     Then, in place of the function for the ranges of a value,
     the macro introduces @('...-run-list-member-ranges'),
     which returns the ranges of the runs
     whose list contains a given element,
     and the theorem @('code-point-in-...-run-list-member-ranges'):
     if a list of runs covers every code point,
     a code point is in the ranges of an element
     exactly when the element is in its list.")
   (xdoc::p
    "The string @(':property') is the name of the property,
     for the documentation of what is introduced.")
   (xdoc::@def "defruns"))

  (defmacro defruns (name &key
                          property
                          value-type
                          value-pred
                          value-fix
                          default
                          elements
                          element-pred
                          element-fix)
    (declare (xargs :guard (and (symbolp name)
                                (stringp property)
                                (symbolp value-type)
                                (symbolp value-pred)
                                (symbolp value-fix)
                                (booleanp elements)
                                (symbolp element-pred)
                                (symbolp element-fix))))
    (b* (;; the new names go in the package of the given name,
         ;; or in the package of this macro
         ;; if the name is a Common Lisp symbol, such as BLOCK:
         (pkg (if (equal (symbol-package-name name) "COMMON-LISP")
                  'defruns
                name))
         (run (acl2::packn-pos (list name '-run) pkg))
         (run-p (acl2::packn-pos (list name '-run-p) pkg))
         (run-list (acl2::packn-pos (list name '-run-list) pkg))
         (run-listp (acl2::packn-pos (list name '-run-listp) pkg))
         (lookup (acl2::packn-pos (list name '-run-list-lookup) pkg))
         (ranges (acl2::packn-pos (list name '-run-list-ranges) pkg))
         (member-ranges
          (acl2::packn-pos (list name '-run-list-member-ranges) pkg))
         (covers-p (acl2::packn-pos (list name '-run-list-covers-p) pkg))
         (lookup-when-in-ranges
          (acl2::packn-pos (list name '-run-list-lookup-when-in-ranges)
                           pkg))
         (in-ranges-when-lookup
          (acl2::packn-pos (list 'in- name '-run-list-ranges-when-lookup)
                           pkg))
         (in-ranges-when-between
          (acl2::packn-pos
           (list 'code-point-in- name '-run-list-ranges-when-between)
           pkg))
         (in-ranges
          (acl2::packn-pos (list 'code-point-in- name '-run-list-ranges)
                           pkg))
         (member-of-lookup-when-in-member-ranges
          (acl2::packn-pos
           (list 'member-equal-of- name
                 '-run-list-lookup-when-in-member-ranges)
           pkg))
         (in-member-ranges-when-member-of-lookup
          (acl2::packn-pos
           (list 'in- name '-run-list-member-ranges-when-member-equal)
           pkg))
         (in-member-ranges-when-between
          (acl2::packn-pos
           (list 'code-point-in- name
                 '-run-list-member-ranges-when-between)
           pkg))
         (in-member-ranges
          (acl2::packn-pos
           (list 'code-point-in- name '-run-list-member-ranges)
           pkg))
         (of-the-property
          (concatenate 'string "of the @('" property "') property")))
      `(progn

         (fty::defprod ,run
           :short ,(concatenate
                    'string
                    "Fixtype of runs of code points that have the same value "
                    of-the-property ".")
           :long
           (xdoc::topstring
            (xdoc::p
             "A run consists of a minimum and a maximum code point,
              and a value of the property.
              It says that the code points
              from the minimum to the maximum, both included,
              have that value.
              See @(see runs)."))
           ((min code-point)
            (max code-point)
            (value ,value-type))
           :pred ,run-p)

         (fty::deflist ,run-list
           :short ,(concatenate
                    'string
                    "Fixtype of lists of runs of code points
                     that have the same value "
                    of-the-property ".")
           :elt-type ,run
           :true-listp t
           :elementp-of-nil nil
           :pred ,run-listp)

         (define ,lookup ((cp code-point-p) (runs ,run-listp))
           :returns (value ,value-pred)
           :short ,(concatenate
                    'string
                    "The value " of-the-property
                    " that a list of runs gives to a code point.")
           :long
           (xdoc::topstring
            (xdoc::p
             "This is the value of the first run of the list
              that contains the code point.
              If no run contains the code point,
              the result is the default value of the property;
              that case does not arise with the generated tables,
              whose runs cover every code point."))
           (cond ((endp runs) ,default)
                 (t (b* (((,run run) (car runs))
                         (fixed-cp (code-point-fix cp)))
                      (if (and (<= run.min fixed-cp)
                               (<= fixed-cp run.max))
                          run.value
                        (,lookup cp (cdr runs))))))
           :hooks (:fix))

         ,@(if elements

               `((define ,member-ranges ((element ,element-pred)
                                         (runs ,run-listp))
                   :returns (ranges range-listp)
                   :short ,(concatenate
                            'string
                            "The ranges of the runs of a list
                             whose value " of-the-property
                             " contains a given element.")
                   :long
                   (xdoc::topstring
                    (xdoc::p
                     "The result has one range for each such run,
                      in the same order."))
                   (cond ((endp runs) nil)
                         (t (b* (((,run run) (car runs))
                                 (ranges (,member-ranges element (cdr runs))))
                              (if (member-equal (,element-fix element)
                                                run.value)
                                  (cons (range run.min run.max) ranges)
                                ranges))))
                   :hooks (:fix)))

             `((define ,ranges ((value ,value-pred) (runs ,run-listp))
                 :returns (ranges range-listp)
                 :short ,(concatenate
                          'string
                          "The ranges of the runs of a list
                           that have a given value "
                          of-the-property ".")
                 :long
                 (xdoc::topstring
                  (xdoc::p
                   "The result has one range for each run with that value,
                    in the same order."))
                 (cond ((endp runs) nil)
                       (t (b* (((,run run) (car runs))
                               (ranges (,ranges value (cdr runs))))
                            (if (equal run.value (,value-fix value))
                                (cons (range run.min run.max) ranges)
                              ranges))))
                 :hooks (:fix))))

         (define ,covers-p ((min code-point-p)
                            (max code-point-p)
                            (runs ,run-listp))
           :returns (yes/no booleanp)
           :short "Check if the runs of a list cover, in order and exactly once,
                   the code points from a minimum to a maximum."
           :long
           (xdoc::topstring
            (xdoc::p
             "That is: the first run starts at the minimum,
              each run after it starts
              right after the one before it ends,
              the last run ends at the maximum,
              and no run is empty.
              In particular the list has at least one run.")
            (xdoc::p
             "Each generated table satisfies this predicate
              with the minimum 0 and the maximum @('#x10FFFF'),
              which is checked by evaluation in the book that has the table.
              Then every code point is in exactly one run,
              and the theorems below apply to every code point."))
           (b* (((when (endp runs)) nil)
                ((,run run) (car runs))
                (min (code-point-fix min))
                (max (code-point-fix max))
                ((unless (and (equal run.min min)
                              (<= run.min run.max)))
                 nil)
                ((when (endp (cdr runs))) (equal run.max max)))
             (and (< run.max max)
                  (,covers-p (+ 1 run.max) max (cdr runs))))
           :guard-hints (("Goal" :in-theory (enable code-point-p)))
           :measure (acl2-count runs)
           :hooks (:fix)

           ///

           (defrulel code-point-fix-upper-bound
             (<= (code-point-fix x) #x10FFFF)
             :rule-classes :linear
             :enable (code-point-fix code-point-p))

           ,@(if elements

                 `((defruled ,member-of-lookup-when-in-member-ranges
                     (implies (and (,covers-p min max runs)
                                   (code-point-in-ranges-p
                                    cp (,member-ranges element runs)))
                              (and (<= (code-point-fix min)
                                       (code-point-fix cp))
                                   (member-equal (,element-fix element)
                                                 (,lookup cp runs))))
                     :induct (,covers-p min max runs)
                     :enable (,lookup
                              ,member-ranges
                              code-point-in-range-p
                              code-point-p))

                   (defruled ,in-member-ranges-when-member-of-lookup
                     (implies (and (,covers-p min max runs)
                                   (<= (code-point-fix min)
                                       (code-point-fix cp))
                                   (<= (code-point-fix cp)
                                       (code-point-fix max))
                                   (member-equal (,element-fix element)
                                                 (,lookup cp runs)))
                              (code-point-in-ranges-p
                               cp (,member-ranges element runs)))
                     :induct (,covers-p min max runs)
                     :enable (,lookup
                              ,member-ranges
                              code-point-in-range-p
                              code-point-p))

                   (defruled ,in-member-ranges-when-between
                     (implies (and (,covers-p min max runs)
                                   (<= (code-point-fix min)
                                       (code-point-fix cp))
                                   (<= (code-point-fix cp)
                                       (code-point-fix max)))
                              (iff (code-point-in-ranges-p
                                    cp (,member-ranges element runs))
                                   (member-equal (,element-fix element)
                                                 (,lookup cp runs))))
                     :enable (,member-of-lookup-when-in-member-ranges
                              ,in-member-ranges-when-member-of-lookup))

                   (defruled ,in-member-ranges
                     (implies (,covers-p 0 #x10FFFF runs)
                              (iff (code-point-in-ranges-p
                                    cp (,member-ranges element runs))
                                   (member-equal (,element-fix element)
                                                 (,lookup cp runs))))
                     :enable ,in-member-ranges-when-between))

               `((defruled ,lookup-when-in-ranges
                   (implies (and (,covers-p min max runs)
                                 (code-point-in-ranges-p
                                  cp (,ranges value runs)))
                            (and (<= (code-point-fix min) (code-point-fix cp))
                                 (equal (,lookup cp runs)
                                        (,value-fix value))))
                   :induct (,covers-p min max runs)
                   :enable (,lookup
                            ,ranges
                            code-point-in-range-p
                            code-point-p))

                 (defruled ,in-ranges-when-lookup
                   (implies (and (,covers-p min max runs)
                                 (<= (code-point-fix min) (code-point-fix cp))
                                 (<= (code-point-fix cp) (code-point-fix max))
                                 (equal (,lookup cp runs)
                                        (,value-fix value)))
                            (code-point-in-ranges-p
                             cp (,ranges value runs)))
                   :induct (,covers-p min max runs)
                   :enable (,lookup
                            ,ranges
                            code-point-in-range-p
                            code-point-p))

                 (defruled ,in-ranges-when-between
                   (implies (and (,covers-p min max runs)
                                 (<= (code-point-fix min) (code-point-fix cp))
                                 (<= (code-point-fix cp) (code-point-fix max)))
                            (equal (code-point-in-ranges-p
                                    cp (,ranges value runs))
                                   (equal (,lookup cp runs)
                                          (,value-fix value))))
                   :enable (,lookup-when-in-ranges
                            ,in-ranges-when-lookup))

                 (defruled ,in-ranges
                   (implies (,covers-p 0 #x10FFFF runs)
                            (equal (code-point-in-ranges-p
                                    cp (,ranges value runs))
                                   (equal (,lookup cp runs)
                                          (,value-fix value))))
                   :enable ,in-ranges-when-between))))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection run-tables
  :short "Write a list of runs compactly."
  :long
  (xdoc::topstring
   (xdoc::p
    "The generated tables have a few thousand runs each.
     So that they are short to write and easy to compare
     with the files of the Unicode Character Database,
     each run is written as a list
     of the minimum code point, the maximum code point,
     and the abbreviation of the value, as a string.
     For example, with the macro for @('General_Category'),")
   (xdoc::codeblock
    "(general-category-run-table"
    " (#x0041 #x005A \"Lu\")"
    " (#x005B #x005B \"Ps\"))")
   (xdoc::p
    "expands to a call of @('list')
     on one call of the constructor of runs for each entry,
     with the constructor of the value
     that the abbreviation stands for:")
   (xdoc::codeblock
    "(list (general-category-run #x0041 #x005A"
    "                            (general-category-uppercase-letter))"
    "      (general-category-run #x005B #x005B"
    "                            (general-category-open-punctuation)))")
   (xdoc::p
    "So the list is built by the typed constructors,
     and it is a list of runs by construction.
     An entry that is not of this form,
     or whose string is not one of the abbreviations of the property,
     is an error when the macro is expanded.")
   (xdoc::p
    "Each property has its own macro,
     which calls the function @('run-table-forms') defined here
     with the constructor of its runs
     and with the list that pairs
     each abbreviation with the constructor of a value.
     The function has three ways to read an entry:
     as one abbreviation, as above;
     as any number of abbreviations after the two code points,
     for a property whose values are sets,
     which gives a call of @('list') on the constructors;
     and as a value that is written as it is,
     for a property whose values are strings."))

  (define run-table-value-forms ((abbreviations true-listp)
                                 (constructors alistp)
                                 (macro symbolp))
    :returns (forms true-listp)
    :parents nil
    (b* (((when (endp abbreviations)) nil)
         (constructor (cdr (assoc-equal (car abbreviations) constructors)))
         ((unless constructor)
          (er hard? macro
              "~x0 is not the abbreviation of a value."
              (car abbreviations))))
      (cons (list constructor)
            (run-table-value-forms (cdr abbreviations) constructors macro)))
    :hooks nil)

  (define run-table-forms ((entries true-listp)
                           (kind symbolp)
                           (constructors alistp)
                           (run-constructor symbolp)
                           (macro symbolp))
    :returns (forms true-listp)
    :parents nil
    (b* (((when (endp entries)) nil)
         (entry (car entries))
         ((unless (and (true-listp entry)
                       (<= 3 (len entry))
                       (or (eq kind :elements)
                           (equal (len entry) 3))))
          (er hard? macro "~x0 is not an entry of a table of runs." entry))
         (value
          (case kind
            (:literal (third entry))
            (:elements (cons 'list
                             (run-table-value-forms (cddr entry)
                                                    constructors
                                                    macro)))
            (t (car (run-table-value-forms (list (third entry))
                                           constructors
                                           macro))))))
      (cons (list run-constructor (first entry) (second entry) value)
            (run-table-forms (cdr entries)
                             kind
                             constructors
                             run-constructor
                             macro)))
    :hooks nil))
