; XDOC Documentation System for ACL2
;
; Copyright (C) 2024 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "std/util/bstar" :dir :system)
(include-book "xdoc/constructors" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection defxdoc+
  :parents (xdoc defxdoc)
  :short "@('defxdoc+') extends @(tsee defxdoc) with some conveniences."
  :long
  (xdoc::topstring
   (xdoc::p
    "In addition to the arguments of @(tsee defxdoc),
     @('defxdoc+') takes the following keyword arguments:")
   (xdoc::ul
    (xdoc::li
     "@(':order-subtopics'), which must be
      @('t') or @('nil') or a non-empty list of symbols.
      If it is @('t'),
      a call @('(xdoc::order-subtopics t)') is generated.
      If it is a non-empty list @('(sym1 ... symN)') of symbols
      whose last element is not @('t'),
      a call @('(xdoc::order-subtopics (sym1 ... symN))') is generated.
      If it is a non-empty list of symbols @('(sym1 ... symN t)')
      whose last element is @('t'),
      a call @('(xdoc::order-subtopics (sym1 ... symN) t)') is generated.
      If it is @('nil') (the default),
      no call of @(tsee xdoc::order-subtopics) is generated.
      See @(tsee xdoc::order-subtopics) for
      a description of what the generated calls do.")
    (xdoc::li
     "@(':default-parent'), which must be @('t') or @('nil').
      If it is @('t'),
      a book-@(see local) call of @(tsee set-default-parents) is generated
      to use the singleton list of this topic as default parents.
      The default is @('nil')."))
   (xdoc::@def "defxdoc+"))

  (defmacro defxdoc+ (&rest args)
    (b* ((name (car args))
         (keyargs (cdr args))
         ((unless (keyword-value-listp keyargs))
          `(with-output :gag-mode nil :off :all :on error
             (make-event (er soft 'defxdoc+
                             "Malformed keyed options: ~x0" ',keyargs)
                         :on-behalf-of :quiet!)))
         (must-be-nil (set-difference-eq (evens keyargs)
                                         '(:parents
                                           :short
                                           :long
                                           :pkg
                                           :no-override
                                           :order-subtopics
                                           :default-parent)))
         ((when must-be-nil)
          `(with-output :gag-mode nil :off :all :on error
             (make-event (er soft 'defxdoc+
                             "Unrecognized keyed option(s): ~x0" ',must-be-nil)
                         :on-behalf-of :quiet!)))
         (parents (cadr (assoc-keyword :parents keyargs)))
         (short (cadr (assoc-keyword :short keyargs)))
         (long (cadr (assoc-keyword :long keyargs)))
         (pkg (cadr (assoc-keyword :pkg keyargs)))
         (no-override (cadr (assoc-keyword :no-override keyargs)))
         (order-subtopics (cadr (assoc-keyword :order-subtopics keyargs)))
         (default-parent (cadr (assoc-keyword :default-parent keyargs)))
         ((unless (or (eq order-subtopics t)
                      (symbol-listp order-subtopics)))
          `(with-output :gag-mode nil :off :all :on error
             (make-event (er soft 'defxdoc+
                             "Malformed :ORDER-SUBTOPICS input: ~x0"
                             ',order-subtopics)
                         :on-behalf-of :quiet!))))
      `(progn
         (defxdoc ,name
           :parents ,parents
           :short ,short
           :long ,long
           :pkg ,pkg
           :no-override ,no-override)
         ,@(cond ((eq order-subtopics t)
                  `((xdoc::order-subtopics ,name
                                           nil
                                           t)))
                 ((eq order-subtopics nil)
                  nil)
                 ((eq (car (last order-subtopics)) t)
                  `((xdoc::order-subtopics ,name
                                           ,(butlast order-subtopics 1)
                                           t)))
                 (t `((xdoc::order-subtopics ,name
                                             ,order-subtopics
                                             nil))))
         ,@(and default-parent
                `((local (set-default-parents ,name)))))))

  (table acl2::ppr-special-syms 'defxdoc+ 1))
