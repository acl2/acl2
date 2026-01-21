; C Library
;
; Copyright (C) 2025 Kestrel Institute (http://www.kestrel.edu)
; Copyright (C) 2025 Kestrel Technology LLC (http://kestreltechnology.com)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C")

(include-book "../language/computation-states")

(local (include-book "arithmetic/top" :dir :system))
(local (include-book "kestrel/utilities/nfix" :dir :system))
(local (include-book "std/lists/nth" :dir :system))
(local (include-book "std/lists/update-nth" :dir :system))

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruledl update-nth-of-rev
  (implies (and (< (nfix i) (len x)))
           (equal (update-nth i a (rev x))
                  (rev (update-nth (- (1- (len x)) (nfix i)) a x))))
  :induct t
  :enable (update-nth len rev fix nfix))

(defruledl nth-of-minus1-and-cdr
  (implies (and (natp i)
                (< 0 i)
                (< i (len x)))
           (equal (nth (1- i) (cdr x))
                  (nth i x)))
  :enable nth)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ read-write-variables
  :parents (atc-event-and-code-generation)
  :short "Functions to read and write variables."
  :long
  (xdoc::topstring
   (xdoc::p
    "These used to be part of the "
    (xdoc::seetopic "dynamic-semantics" "dynamic semantics")
    ", which was since then extended and generalized
     to no longer use these functions.
     However, these functions are still used by ATC,
     and so for now we keep them here.
     We may remove them altogether in the future,
     after changing ATC to no longer used them."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define read-auto-var ((var identp) (compst compustatep))
  :guard (> (compustate-frames-number compst) 0)
  :returns (val value-optionp)
  :short "Read a variable in automatic storage."
  :long
  (xdoc::topstring
   (xdoc::p
    "That is, read the variable in the scopes in the top frame.
     We search the scopes from innermost (leftmost) to outermost (rightmost),
     according to the scoping rules for variables,
     where variables in inner scopes may hide variables in outer scopes.")
   (xdoc::p
    "If the variable is not found, we return @('nil'), not an error.
     The reason is that this ACL2 function is used
     as a subroutine of @(tsee read-var),
     where if a variable is not found in automatic storage,
     it is looked up in static storage.
     Thus, not finding a variable in automatic storage,
     in this ACL2 function, is not necessarily an error.")
   (xdoc::p
    "We do not look at other frames,
     because the variables in other frames are not in scope
     when running in the top frame."))
  (read-auto-var-aux var (frame->scopes (top-frame compst)))
  :hooks (:fix)

  :prepwork
  ((define read-auto-var-aux ((var identp) (scopes scope-listp))
     :returns (val value-optionp)
     :parents nil
     (b* (((when (endp scopes)) nil)
          (scope (car scopes))
          (pair (omap::assoc (ident-fix var) (scope-fix scope)))
          ((when (not pair)) (read-auto-var-aux var (cdr scopes))))
       (cdr pair))
     :hooks (:fix))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define read-static-var ((var identp) (compst compustatep))
  :returns (val value-resultp)
  :short "Read a variable in static storage."
  :long
  (xdoc::topstring
   (xdoc::p
    "If the variable is not found, we return an error."))
  (b* ((pair (omap::assoc (ident-fix var) (compustate->static compst)))
       ((when (not pair))
        (error (list :static-var-not-found (ident-fix var)))))
    (cdr pair))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define read-var ((var identp) (compst compustatep))
  :returns (val value-resultp)
  :short "Read a variable in a computation state."
  :long
  (xdoc::topstring
   (xdoc::p
    "First we try automatic storage (if there are frames), then static storage.
     Indeed, file scope is outside all the block scopes,
     so it must be tried last."))
  (if (> (compustate-frames-number compst) 0)
      (b* ((val (read-auto-var var compst)))
        (or val
            (read-static-var var compst)))
    (read-static-var var compst))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define write-auto-var ((var identp) (val valuep) (compst compustatep))
  :guard (> (compustate-frames-number compst) 0)
  :returns (new-compst compustate-option-resultp)
  :short "Write a variable in automatic storage."
  :long
  (xdoc::topstring
   (xdoc::p
    "That is, write the variable in the scopes of the top frame.
     The scopes are searched in the same way as @(tsee read-auto-var).
     The variable must exist in order to write to it, i.e. it is not created;
     variables are created only via @(tsee create-var).
     The new value must have the same type as the old value;
     note that, in our restricted dynamic semantics of C,
     variables always have values, they are never uninitialized.")
   (xdoc::p
    "If the variable is not found, we return @('nil'), not an error.
     The reason is that this ACL2 function is used
     as a subroutine of @(tsee write-var),
     where if a variable is not found in automatic storage,
     it is looked up in static storage.
     Thus, not finding a variable in automatic storage,
     in this ACL2 function, is not necessarily an error.
     If the auxiliary recursive function returns @('nil'),
     it means that the variable was not found:
     since a frame always has at least one scope (see @(tsee frame)),
     this cannot be confused with a result where
     the variable was just not found in the scopes.")
   (xdoc::p
    "We do not look at other frames,
     because the variables in other frames are not in scope
     when running in the top frame.")
   (xdoc::p
    "Prior to storing the value, we remove its flexible array member, if any.
     See @(tsee remove-flexible-array-member)."))
  (b* ((frame (top-frame compst))
       (new-scopes (write-auto-var-aux var val (frame->scopes frame)))
       ((when (errorp new-scopes)) new-scopes)
       ((when (endp new-scopes)) nil)
       (new-frame (change-frame frame :scopes new-scopes)))
    (push-frame new-frame (pop-frame compst)))
  :hooks (:fix)

  :prepwork
  ((define write-auto-var-aux ((var identp) (val valuep) (scopes scope-listp))
     :returns (new-scopes
               scope-list-resultp
               :hints (("Goal"
                        :induct t
                        :in-theory
                        (enable
                         scope-listp-when-scope-list-resultp-and-not-errorp))))
     :parents nil
     (b* (((when (endp scopes)) nil)
          (scope (scope-fix (car scopes)))
          (pair (omap::assoc (ident-fix var) scope))
          ((when (consp pair))
           (if (equal (type-of-value (cdr pair))
                      (type-of-value val))
               (cons (omap::update (ident-fix var)
                                   (remove-flexible-array-member val)
                                   scope)
                     (scope-list-fix (cdr scopes)))
             (error (list :write-auto-object-mistype (ident-fix var)
                          :old (type-of-value (cdr pair))
                          :new (type-of-value val)))))
          (new-cdr-scopes (write-auto-var-aux var val (cdr scopes)))
          ((when (errorp new-cdr-scopes)) new-cdr-scopes)
          ((when (endp new-cdr-scopes)) nil))
       (cons scope new-cdr-scopes))
     :hooks (:fix)

     ///

     (defret consp-of-write-auto-var-aux
       (implies (and (scope-listp new-scopes)
                     (consp new-scopes))
                (equal (consp new-scopes)
                       (consp scopes)))
       :hints (("Goal" :in-theory (enable error))))

     (defret len-of-write-auto-var-aux
       (implies (and (scope-listp new-scopes)
                     (consp new-scopes))
                (equal (len new-scopes)
                       (len scopes)))
       :hints (("Goal"
                :induct t
                :in-theory (enable error errorp len))))))

  ///

  (defret compustate-frames-number-of-write-auto-var
    (implies (and (> (compustate-frames-number compst) 0)
                  (compustatep new-compst))
             (equal (compustate-frames-number new-compst)
                    (compustate-frames-number compst)))
    :hints (("Goal" :in-theory (enable not-errorp-when-compustatep
                                       fix))))

  (defret compustate-scopes-numbers-of-write-auto-var
    (implies (and (> (compustate-frames-number compst) 0)
                  (compustatep new-compst))
             (equal (compustate-scopes-numbers new-compst)
                    (compustate-scopes-numbers compst)))
    :hints (("Goal" :in-theory (enable top-frame
                                       push-frame
                                       pop-frame
                                       compustate-frames-number
                                       compustate-scopes-numbers
                                       compustate-scopes-numbers-aux
                                       errorp-when-scope-list-resultp)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define write-static-var ((var identp) (val valuep) (compst compustatep))
  :returns (new-compst compustate-resultp)
  :short "Write a varible in static storage."
  :long
  (xdoc::topstring
   (xdoc::p
    "If the variable is not found, we return an error.
     If the variable is found but its current value
     has a different type from the one of the new value,
     we return an error.
     Otherwise, we overwrite the old value with the new one.")
   (xdoc::p
    "Prior to storing the value, we remove its flexible array member, if any.
     See @(tsee remove-flexible-array-member)."))
  (b* ((static (compustate->static compst))
       (pair (omap::assoc (ident-fix var) static))
       ((when (not pair)) (error (list :static-var-not-found (ident-fix var))))
       ((unless (equal (type-of-value (cdr pair))
                       (type-of-value val)))
        (error (list :static-var-mistype (ident-fix var)
                     :required (type-of-value (cdr pair))
                     :supplied (type-of-value val))))
       (new-static (omap::update (ident-fix var)
                                 (remove-flexible-array-member val)
                                 static))
       (new-compst (change-compustate compst :static new-static)))
    new-compst)
  :hooks (:fix)
  ///

  (defret compustate-frames-number-of-write-static-var
    (implies (compustatep new-compst)
             (equal (compustate-frames-number new-compst)
                    (compustate-frames-number compst)))
    :hints (("Goal" :in-theory (enable compustate-frames-number))))

  (defret compustate-scopes-numbers-of-write-static-var
    (implies (compustatep new-compst)
             (equal (compustate-scopes-numbers new-compst)
                    (compustate-scopes-numbers compst)))
    :hints (("Goal" :in-theory (enable compustate-scopes-numbers)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define write-var ((var identp) (val valuep) (compst compustatep))
  :returns (new-compst
            compustate-resultp
            :hints
            (("Goal"
              :in-theory
              (enable
               compustate-resultp-when-compustate-option-result-and-not-nil))))
  :short "Write a variable in the computation state."
  :long
  (xdoc::topstring
   (xdoc::p
    "First we try automatic storage, if there are frames.
     If there is an error, we propagate it.
     If instead the variable was not found,
     we try static storage."))
  (if (> (compustate-frames-number compst) 0)
      (b* ((new-compst (write-auto-var var val compst))
           ((when (errorp new-compst)) new-compst))
        (or new-compst
            (write-static-var var val compst)))
    (write-static-var var val compst))
  :hooks (:fix)
  ///

  (defret compustate-frames-number-of-write-var
    (implies (compustatep new-compst)
             (equal (compustate-frames-number new-compst)
                    (compustate-frames-number compst))))

  (defret compustate-scopes-numbers-of-write-var
    (implies (compustatep new-compst)
             (equal (compustate-scopes-numbers new-compst)
                    (compustate-scopes-numbers compst)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection objdesign-of-var-and-read/write-var-theorems
  :short "Some theorems about @(tsee objdesign-of-var)
          and the functions to read and write variables."

  (defruled objdesign-of-var-aux-iff-read-auto-var-aux
    (iff (objdesign-of-var-aux var frame scopes)
         (read-auto-var-aux var scopes))
    :induct t
    :enable (objdesign-of-var-aux
             read-auto-var-aux
             cdr-of-assoc-when-scopep))

  (defruled objdesign-of-var-when-valuep-of-read-var
    (implies (valuep (read-var id compst))
             (objdesign-of-var id compst))
    :enable (read-var
             read-static-var
             read-auto-var
             objdesign-of-var-aux-iff-read-auto-var-aux
             objdesign-of-var))

  (defruled write-auto-var-aux-iff-objdesign-of-var-aux
    (iff (write-auto-var-aux var val scopes)
         (objdesign-of-var-aux var frame scopes))
    :induct t
    :enable (objdesign-of-var-aux
             write-auto-var-aux))

  (defruled objdesignp-of-objdesign-of-var-when-valuep-of-read-var
    (implies (valuep (read-var id compst))
             (objdesignp (objdesign-of-var id compst)))
    :enable objdesign-of-var-when-valuep-of-read-var))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled read-object-of-objdesign-of-var-to-read-var
  :short "Equivalence of @(tsee read-object) and @(tsee read-var)
          for object designators of variables."
  (b* ((objdes (objdesign-of-var var compst)))
    (implies objdes
             (equal (read-object objdes compst)
                    (read-var var compst))))
  :enable (objdesign-of-var
           compustate-frames-number
           read-var-to-read-object-when-auto
           read-var-to-read-object-when-static)

  :prep-lemmas

  ((defruled read-auto-var-aux-to-nth-of-objdesign
     (b* ((objdes (objdesign-of-var-aux var frame scopes)))
       (implies objdes
                (equal (read-auto-var-aux var scopes)
                       (cdr (omap::assoc (ident-fix var)
                                         (scope-fix
                                          (nth (objdesign-auto->scope objdes)
                                               (rev scopes))))))))
     :induct t
     :enable (read-auto-var-aux
              objdesign-of-var-aux
              len
              fix
              nth-of-minus1-and-cdr
              natp))

   (defruled read-var-to-read-object-when-auto
     (implies (> (compustate-frames-number compst) 0)
              (b* ((objdes (objdesign-of-var-aux
                            var
                            (1- (compustate-frames-number compst))
                            (frame->scopes (top-frame compst)))))
                (implies objdes
                         (equal (read-var var compst)
                                (read-object objdes compst)))))
     :enable (read-object
              read-var
              read-auto-var
              read-auto-var-aux-to-nth-of-objdesign
              top-frame
              compustate-frames-number
              fix
              cdr-of-assoc-when-scopep)
     :use
     ((:instance objdesign-of-var-aux-lemma
                 (frame (+ -1 (len (compustate->frames compst))))
                 (scopes (frame->scopes (car (compustate->frames compst)))))))

   (defruled read-var-to-read-object-when-static
     (b* ((objdes (objdesign-of-var var compst))
          (objdes0 (objdesign-of-var-aux var
                                         (1- (compustate-frames-number compst))
                                         (frame->scopes (top-frame compst)))))
       (implies (and objdes
                     (or (equal (compustate-frames-number compst) 0)
                         (not objdes0)))
                (and (equal (objdesign-kind objdes) :static)
                     (equal (objdesign-static->name objdes) (ident-fix var))
                     (equal (read-var var compst)
                            (read-object objdes compst)))))
     :enable (objdesign-of-var
              compustate-frames-number
              read-object
              read-var
              read-auto-var
              read-static-var
              objdesign-of-var-aux-iff-read-auto-var-aux))))

;;;;;;;;;;;;;;;;;;;;

(defruled read-var-to-read-object-of-objdesign-of-var
  :parents (read-object-of-objdesign-of-var-to-read-var)
  :short "Converse of @(tsee read-object-of-objdesign-of-var-to-read-var)."
  (b* ((objdes (objdesign-of-var var compst)))
    (implies objdes
             (equal (read-var var compst)
                    (read-object objdes compst))))
  :enable read-object-of-objdesign-of-var-to-read-var)

(theory-invariant
 (incompatible (:rewrite read-object-of-objdesign-of-var-to-read-var)
               (:rewrite read-var-to-read-object-of-objdesign-of-var)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled write-object-of-objdesign-of-var-to-write-var
  :short "Equivalence of @(tsee write-object) and @(tsee write-var)
          for object designators of variables."
  (b* ((objdes (objdesign-of-var var compst)))
    (implies objdes
             (equal (write-object objdes val compst)
                    (write-var var val compst))))
  :enable (objdesign-of-var
           compustate-frames-number
           write-var-to-write-object-when-auto
           write-var-to-write-object-when-static)

  :prep-lemmas

  ((defruled write-auto-var-aux-to-update-nth-of-objdesign
     (b* ((objdes (objdesign-of-var-aux var frame scopes)))
       (implies
        objdes
        (equal (write-auto-var-aux var val scopes)
               (if (equal (type-of-value val)
                          (type-of-value
                           (cdr (omap::assoc (ident-fix var)
                                             (scope-fix
                                              (nth (objdesign-auto->scope objdes)
                                                   (rev scopes)))))))
                   (rev
                    (update-nth
                     (objdesign-auto->scope objdes)
                     (omap::update (ident-fix var)
                                   (remove-flexible-array-member val)
                                   (scope-fix
                                    (nth (objdesign-auto->scope objdes)
                                         (rev scopes))))
                     (rev (scope-list-fix scopes))))
                 (error (list :write-auto-object-mistype (ident-fix var)
                              :old (type-of-value
                                    (cdr
                                     (omap::assoc
                                      (ident-fix var)
                                      (scope-fix
                                       (nth (objdesign-auto->scope objdes)
                                            (rev scopes))))))
                              :new (type-of-value val)))))))
     :induct t
     :enable (write-auto-var-aux
              objdesign-of-var-aux
              nth-of-minus1-and-cdr
              update-nth-of-rev
              len
              fix
              not-errorp-when-scope-listp))

   (defruled write-var-to-write-object-when-auto
     (implies
      (> (compustate-frames-number compst) 0)
      (b* ((objdes (objdesign-of-var-aux
                    var
                    (1- (compustate-frames-number compst))
                    (frame->scopes (top-frame compst)))))
        (implies
         objdes
         (equal (write-var var val compst)
                (write-object objdes val compst)))))
     :enable (write-object
              write-var
              write-auto-var
              write-auto-var-aux-to-update-nth-of-objdesign
              top-frame
              push-frame
              pop-frame
              compustate-frames-number
              fix
              not-errorp-when-scope-listp)
     :cases ((consp (compustate->frames compst)))
     :use
     ((:instance objdesign-of-var-aux-lemma
                 (frame (+ -1 (len (compustate->frames compst))))
                 (scopes (frame->scopes (car (compustate->frames compst))))))
     :prep-lemmas
     ((defrule lemma
        (implies (and (true-listp x)
                      (consp x))
                 (equal (rev (update-nth (1- (len x)) a (rev x)))
                        (cons a (cdr x))))
        :enable (len fix))))

   (defruled write-var-to-write-object-when-static
     (b* ((objdes (objdesign-of-var var compst))
          (objdes0 (objdesign-of-var-aux var
                                         (1- (compustate-frames-number compst))
                                         (frame->scopes (top-frame compst)))))
       (implies (and objdes
                     (or (equal (compustate-frames-number compst) 0)
                         (not objdes0)))
                (and (equal (objdesign-kind objdes) :static)
                     (equal (objdesign-static->name objdes) (ident-fix var))
                     (equal (write-var var val compst)
                            (write-object objdes val compst)))))
     :use (:instance write-auto-var-aux-iff-objdesign-of-var-aux
                     (frame (+ -1 (len (compustate->frames compst))))
                     (scopes (frame->scopes (top-frame compst))))
     :enable (objdesign-of-var
              compustate-frames-number
              write-object
              write-var
              write-auto-var
              write-static-var
              push-frame
              pop-frame
              top-frame))))
