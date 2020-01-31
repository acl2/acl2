; XDOC Documentation System for ACL2
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

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
     "@(':order-subtopics'), which must be @('t') or @('nil').
      If it is @('t'),
      a call of @(tsee xdoc::order-subtopics) is generated
      to order all the subtopics of this topic.")
    (xdoc::li
     "@(':default-parent'), which must be @('t') or @('nil').
      If it is @('t'),
      a book-@(see local) call of @(tsee set-default-parents) is generated
      to use the singleton list of this topic as default parents."))
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
                             "Unrecognized keyed options: ~x0" ',must-be-nil)
                         :on-behalf-of :quiet!)))
         (parents (cadr (assoc-keyword :parents keyargs)))
         (short (cadr (assoc-keyword :short keyargs)))
         (long (cadr (assoc-keyword :long keyargs)))
         (pkg (cadr (assoc-keyword :pkg keyargs)))
         (no-override (cadr (assoc-keyword :no-override keyargs)))
         (order-subtopics (cadr (assoc-keyword :order-subtopics keyargs)))
         (default-parent (cadr (assoc-keyword :default-parent keyargs))))
      `(progn
         (defxdoc ,name
           :parents ,parents
           :short ,short
           :long ,long
           :pkg ,pkg
           :no-override ,no-override)
         ,@(and order-subtopics
                `((xdoc::order-subtopics ,name nil t)))
         ,@(and default-parent
                `((local (set-default-parents ,name))))))))
