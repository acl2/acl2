; Bitcoin Library
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "BITCOIN")

(include-book "bip32")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc bip32-executable-attachments
  :parents (bip32)
  :short "Executable attachments for the BIP 32 formalization."
  :long
  (xdoc::topstring
   (xdoc::p
    "Some functions in the BIP 32 formalization are not executable.
     Here we provide executable attachments for some of them.")))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ bip32-path-set-closedp-executable-attachment
  :parents (bip32-executable-attachments bip32-path-set-closedp)
  :short "Executable attachment for @(tsee bip32-path-set-closedp)."
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define bip32-path-set-closedp-exec ((paths bip32-path-setp))
  :returns (yes/no booleanp)
  :short "Executable version of @(tsee bip32-path-set-closedp)."
  :long
  (xdoc::topstring
   (xdoc::p
    "Roughly, @(tsee bip32-path-set-closedp) has the form")
   (xdoc::codeblock
    "(forall (path prefix)"
    "  (implies (and (in path paths)"
    "                (true-listp prefix)"
    "                (prefixp prefix path))"
    "           (in prefix paths)))")
   (xdoc::p
    "which can be written as")
   (xdoc::codeblock
    "(forall (path)"
    "        (implies (in path paths)"
    "                 (forall (prefix)"
    "                         (implies (and (true-listp prefix)"
    "                                       (prefixp prefix path))"
    "                                  (in prefix paths)))))")
   (xdoc::p
    "We execute this via
     an outer iteration of @('path') over @('paths')
     and an inner iteration of @('prefix') over the prefixes of @('path');
     these two iterations are realized via recursive functions.
     Their @('all-paths') argument never changes;
     it is the initial set of all paths,
     that the prefixes must be checked to be in.
     The @('cur-path') argument is the path in the outer iteration,
     and the @('cur-paths') argument is the subset of paths
     that remains to process in the outer iteration."))
  (bip32-path-set-closedp-exec-outer paths paths)
  :no-function t
  :hooks (:fix)

  :prepwork

  ((define bip32-path-set-closedp-exec-inner ((cur-path ubyte32-listp)
                                              (all-paths bip32-path-setp))
     :returns (yes/no booleanp)
     (and (in (ubyte32-list-fix cur-path)
              (bip32-path-sfix all-paths))
          (or (endp cur-path)
              (bip32-path-set-closedp-exec-inner (butlast cur-path 1)
                                                 all-paths)))
     :no-function t
     :measure (len cur-path)
     :hooks (:fix))

   (define bip32-path-set-closedp-exec-outer ((cur-paths bip32-path-setp)
                                              (all-paths bip32-path-setp))
     :returns (yes/no booleanp)
     (or (not (mbt (bip32-path-setp cur-paths)))
         (empty cur-paths)
         (and (bip32-path-set-closedp-exec-inner (head cur-paths) all-paths)
              (bip32-path-set-closedp-exec-outer (tail cur-paths) all-paths)))
     :no-function t
     ///
     (fty::deffixequiv bip32-path-set-closedp-exec-outer
       :hints (("Goal" :in-theory (enable
                                   bip32-path-sfix
                                   bip32-path-set-closedp-exec-inner)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection bip32-path-set-closedp-exec-correctness
  :short "Correctness of @(tsee bip32-path-set-closedp-exec)."
  :long
  (xdoc::topstring
   (xdoc::p
    "We prove that @(tsee bip32-path-set-closedp-exec)
     is equivalent to @(tsee bip32-path-set-closedp).")
   (xdoc::p
    "We first prove that each one implies the other,
     and then the equality follows from the fact that
     these functions are boolean-valued.")
   (xdoc::p
    "To prove that @(tsee bip32-path-set-closedp-exec)
     implies @(tsee bip32-path-set-closedp),
     first recall the nested quantification of the latter
     illustrated in the documentation of @(tsee bip32-path-set-closedp-exec):
     we prove that @(tsee bip32-path-set-closedp-exec-inner)
     implies the inner matrix,
     and that @(tsee bip32-path-set-closedp-exec-outer)
     implies the outer matrix.
     From these two lemmas, the desired theorem follows.")
   (xdoc::p
    "To prove that @(tsee bip32-path-set-closedp)
     implies @(tsee bip32-path-set-closedp-exec),
     we first prove that it implies
     @(tsee bip32-path-set-closedp-exec-inner)
     and @(tsee bip32-path-set-closedp-exec-outer)."))

  (defruled bip32-path-set-closedp-exec-inner-implies-inner-matrix
    (implies (and (bip32-path-set-closedp-exec-inner cur-path all-paths)
                  (ubyte32-listp cur-path)
                  (true-listp prefix)
                  (prefixp prefix cur-path))
             (in prefix all-paths))
    :enable (bip32-path-set-closedp-exec-inner list-equiv bip32-path-sfix)
    :prep-books
    ((include-book "std/lists/top" :dir :system)
     (include-book "kestrel/utilities/lists/prefixp-theorems" :dir :system))
    :rule-classes
    ((:rewrite :corollary
      (implies (and (prefixp prefix cur-path) ; binds free CUR-PATH
                    (bip32-path-set-closedp-exec-inner cur-path all-paths)
                    (ubyte32-listp cur-path)
                    (true-listp prefix))
               (in prefix all-paths)))))

  (defruled bip32-path-set-closedp-exec-outer-implies-outer-matrix
    (implies (and (bip32-path-set-closedp-exec-outer cur-paths all-paths)
                  (in cur-path (bip32-path-sfix cur-paths)))
             (bip32-path-set-closedp-exec-inner cur-path all-paths))
    :enable (bip32-path-set-closedp-exec-outer
             bip32-path-set-closedp-exec-inner
             bip32-path-sfix))

  (defruled bip32-path-set-closedp-when-bip32-path-set-closedp-exec
    (implies (bip32-path-set-closedp-exec paths)
             (bip32-path-set-closedp paths))
    :enable (bip32-path-set-closedp-definition
             bip32-path-set-closedp-exec
             bip32-path-set-closedp-exec-inner-implies-inner-matrix
             bip32-path-set-closedp-exec-outer-implies-outer-matrix))

  (defruled bip32-path-set-closedp-exec-inner-when-bip32-path-set-closedp
    (implies (and (bip32-path-set-closedp all-paths)
                  (bip32-path-setp all-paths)
                  (ubyte32-listp cur-path)
                  (in cur-path all-paths))
             (bip32-path-set-closedp-exec-inner cur-path all-paths))
    :enable (bip32-path-set-closedp-exec-inner)
    :hints ('(:use (:instance bip32-path-set-closedp-necc
                    (prefix (butlast cur-path 1))
                    (path cur-path)
                    (paths all-paths))))
    :prep-books ((include-book "std/lists/prefixp" :dir :system)))

  (defruled bip32-path-set-closedp-exec-outer-when-bip32-path-set-closedp
    (implies (and (bip32-path-set-closedp all-paths)
                  (bip32-path-setp all-paths)
                  (subset cur-paths all-paths))
             (bip32-path-set-closedp-exec-outer cur-paths all-paths))
    :enable (bip32-path-set-closedp-exec-outer
             bip32-path-set-closedp-exec-inner-when-bip32-path-set-closedp
             set::subset-in)
    :prep-books ((include-book "kestrel/utilities/oset-theorems" :dir :system)))

  (defruled bip32-path-set-closedp-exec-when-bip32-path-set-closedp
    (implies (bip32-path-set-closedp paths)
             (bip32-path-set-closedp-exec paths))
    :enable (bip32-path-set-closedp-exec)
    :use (:instance
          bip32-path-set-closedp-exec-outer-when-bip32-path-set-closedp
          (cur-paths (bip32-path-sfix paths))
          (all-paths (bip32-path-sfix paths))))

  (defruled bip32-path-set-closedp-exec-is-bip32-path-set-closedp
    (equal (bip32-path-set-closedp-exec paths)
           (bip32-path-set-closedp paths))
    :use (bip32-path-set-closedp-when-bip32-path-set-closedp-exec
          bip32-path-set-closedp-exec-when-bip32-path-set-closedp)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection bip32-path-set-closedp-exec-attach
  :short "Attachment of @(tsee bip32-path-set-closedp-exec)
          to @(tsee bip32-path-set-closedp)."
  :long
  (xdoc::topstring
   (xdoc::p
    "The fact that the executable function satisfies
     all the constraints of the non-executable one
     follows from their equivalence.")
   (xdoc::p
    "We prove two of the constraints as separate theorems.
     Attempts at proving the attachment directly fail."))

  (defruled bip32-path-set-closedp-exec-constraint1
    (equal (bip32-path-set-closedp-exec paths)
           (mv-let (path prefix)
             (bip32-path-set-closedp-witness paths)
             (let ((paths (bip32-path-sfix paths)))
               (implies (and (in path paths)
                             (true-listp prefix)
                             (prefixp prefix path))
                        (in prefix paths)))))
    :enable (bip32-path-set-closedp-exec-is-bip32-path-set-closedp
             bip32-path-set-closedp-definition))

  (defruled bip32-path-set-closedp-exec-constraint2
    (implies (bip32-path-set-closedp-exec paths)
             (let ((paths (bip32-path-sfix paths)))
               (implies (and (in path paths)
                             (true-listp prefix)
                             (prefixp prefix path))
                        (in prefix paths))))
    :enable (bip32-path-set-closedp-exec-is-bip32-path-set-closedp
             bip32-path-set-closedp-necc))

  (defattach (bip32-path-set-closedp bip32-path-set-closedp-exec)
    :hints (("Goal" :use (bip32-path-set-closedp-exec-constraint1
                          bip32-path-set-closedp-exec-constraint2)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ bip32-valid-keys-p-executable-attachment
  :parents (bip32-executable-attachments bip32-valid-keys-p)
  :short "Executable attachment for @(tsee bip32-valid-keys-p)."
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define bip32-valid-keys-p-exec ((root bip32-ext-key-p) (paths bip32-path-setp))
  :returns (yes/no booleanp)
  :short "Executable version of @(tsee bip32-valid-keys-p)."
  :long
  (xdoc::topstring
   (xdoc::p
    "We iterate through the paths in the set,
    checking that each one has a valid key.")
   (xdoc::p
    "If this executable function holds,
     then any member of the set satisfies the key validity condition.
     This fact is used in the correctness proof of the attachment."))
  (or (not (mbt (bip32-path-setp paths)))
      (empty paths)
      (and (b* (((mv error? &) (bip32-ckd* root (head paths))))
             (not error?))
           (bip32-valid-keys-p-exec root (tail paths))))
  :no-function t
  ///

  (fty::deffixequiv bip32-valid-keys-p-exec
    :hints (("Goal" :in-theory (enable bip32-path-sfix))))

  (defrule bip32-valid-keys-p-exec-member
    (implies (and (bip32-valid-keys-p-exec root paths)
                  (in path (bip32-path-sfix paths)))
             (not (mv-nth 0 (bip32-ckd* root path))))
    :enable bip32-path-sfix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection bip32-valid-keys-p-exec-correctness
  :short "Correctness of @(tsee bip32-valid-keys-p-exec)."
  :long
  (xdoc::topstring
   (xdoc::p
    "We prove that @(tsee bip32-valid-keys-p-exec)
     is equivalent to @(tsee bip32-valid-keys-p).")
   (xdoc::p
    "We first prove that each one implies the other,
     and then the equality follows from the fact that
     these functions are boolean-valued."))

  (defruled bip32-valid-keys-p-when-bip32-valid-keys-p-exec
    (implies (bip32-valid-keys-p-exec root paths)
             (bip32-valid-keys-p root paths))
    :enable (bip32-valid-keys-p-definition))

  (defruled bip32-valid-keys-p-exec-when-bip32-valid-keys-p
    (implies (bip32-valid-keys-p root paths)
             (bip32-valid-keys-p-exec root paths))
    :enable (bip32-valid-keys-p-exec bip32-valid-keys-p-necc))

  (defruled bip32-valid-keys-p-exec-is-bip32-valid-keys-p
    (equal (bip32-valid-keys-p-exec root paths)
           (bip32-valid-keys-p root paths))
    :use (bip32-valid-keys-p-when-bip32-valid-keys-p-exec
          bip32-valid-keys-p-exec-when-bip32-valid-keys-p)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection bip32-valid-keys-p-exec-attach
  :short "Attachment of @(tsee bip32-valid-keys-p-exec)
          to @(tsee bip32-valid-keys-p)."
  :long
  (xdoc::topstring
   (xdoc::p
    "The fact that the executable function satisfies
     all the constraints of the non-executable one
     follows from their equivalence.")
   (xdoc::p
    "We prove two of the constraints as separate theorems.
     Attempts at proving the attachment directly fail."))

  (defruled bip32-valid-keys-p-exec-constraint1
    (equal (bip32-valid-keys-p-exec root paths)
           (let ((path (bip32-valid-keys-p-witness root paths)))
             (implies (in path (bip32-path-sfix paths))
                      (not (mv-nth 0 (bip32-ckd* root path))))))
    :enable (bip32-valid-keys-p-exec-is-bip32-valid-keys-p
             bip32-valid-keys-p-definition))

  (defruled bip32-valid-keys-p-exec-constraint2
    (implies (bip32-valid-keys-p-exec root paths)
             (implies (in path (bip32-path-sfix paths))
                      (not (mv-nth 0 (bip32-ckd* root path)))))
    :enable (bip32-valid-keys-p-exec-is-bip32-valid-keys-p
             bip32-valid-keys-p-necc))

  (defattach (bip32-valid-keys-p bip32-valid-keys-p-exec)
    :hints (("Goal" :use (bip32-valid-keys-p-exec-constraint1
                          bip32-valid-keys-p-exec-constraint2)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ bip32-valid-depths-p-executable-attachment
  :parents (bip32-executable-attachments bip32-valid-depths-p)
  :short "Executable attachment for @(tsee bip32-valid-depths-p)."
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define bip32-valid-depths-p-exec ((init bytep) (paths bip32-path-setp))
  :returns (yes/no booleanp)
  :short "Executable version of @(tsee bip32-valid-depths-p)."
  :long
  (xdoc::topstring
   (xdoc::p
    "We iterate through the paths in the set,
    checking that each one has a valid depth.")
   (xdoc::p
    "If this executable function holds,
     then any member of the set satisfies the depth validity condition.
     This fact is used in the correctness proof of the attachment."))
  (or (not (mbt (bip32-path-setp paths)))
      (empty paths)
      (and (bytep (+ (byte-fix init) (len (head paths))))
           (bip32-valid-depths-p-exec init (tail paths))))
  :no-function t
  ///

  (fty::deffixequiv bip32-valid-depths-p-exec
    :hints (("Goal" :in-theory (enable bip32-path-sfix))))

  (defrule bip32-valid-depths-p-exec-member
    (implies (and (bip32-valid-depths-p-exec init paths)
                  (in path (bip32-path-sfix paths)))
             (bytep (+ (byte-fix init) (len path))))
    :enable bip32-path-sfix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection bip32-valid-depths-p-exec-correctness
  :short "Correctness of @(tsee bip32-valid-depths-p-exec)."
  :long
  (xdoc::topstring
   (xdoc::p
    "We prove that @(tsee bip32-valid-depths-p-exec)
     is equivalent to @(tsee bip32-valid-depths-p).")
   (xdoc::p
    "We first prove that each one implies the other,
     and then the equality follows from the fact that
     these functions are boolean-valued."))

  (defruled bip32-valid-depths-p-when-bip32-valid-depths-p-exec
    (implies (bip32-valid-depths-p-exec init paths)
             (bip32-valid-depths-p init paths))
    :enable (bip32-valid-depths-p-definition))

  (defruled bip32-valid-depths-p-exec-when-bip32-valid-depths-p
    (implies (bip32-valid-depths-p init paths)
             (bip32-valid-depths-p-exec init paths))
    :enable (bip32-valid-depths-p-exec bip32-valid-depths-p-necc))

  (defruled bip32-valid-depths-p-exec-is-bip32-valid-depths-p
    (equal (bip32-valid-depths-p-exec init paths)
           (bip32-valid-depths-p init paths))
    :use (bip32-valid-depths-p-when-bip32-valid-depths-p-exec
          bip32-valid-depths-p-exec-when-bip32-valid-depths-p)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection bip32-valid-depths-p-exec-attach
  :short "Attachment of @(tsee bip32-valid-depths-p-exec)
          to @(tsee bip32-valid-depths-p)."
  :long
  (xdoc::topstring
   (xdoc::p
    "The fact that the executable function satisfies
     all the constraints of the non-executable one
     follows from their equivalence.")
   (xdoc::p
    "We prove two of the constraints as separate theorems.
     Attempts at proving the attachment directly fail."))

  (defruled bip32-valid-depths-p-exec-constraint1
    (equal (bip32-valid-depths-p-exec init paths)
           (let ((path (bip32-valid-depths-p-witness init paths)))
             (implies (in path (bip32-path-sfix paths))
                      (bytep (+ (byte-fix init) (len path))))))
    :enable (bip32-valid-depths-p-exec-is-bip32-valid-depths-p
             bip32-valid-depths-p-definition))

  (defruled bip32-valid-depths-p-exec-constraint2
    (implies (bip32-valid-depths-p-exec init paths)
             (implies (in path (bip32-path-sfix paths))
                      (bytep (+ (byte-fix init) (len path)))))
    :enable (bip32-valid-depths-p-exec-is-bip32-valid-depths-p
             bip32-valid-depths-p-necc))

  (defattach (bip32-valid-depths-p bip32-valid-depths-p-exec)
    :hints (("Goal" :use (bip32-valid-depths-p-exec-constraint1
                          bip32-valid-depths-p-exec-constraint2)))))
