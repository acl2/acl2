; ACL2 Programming Language Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2PL")

(include-book "translated-terms")

(include-book "kestrel/fty/defset" :dir :system)
(include-book "kestrel/std/system/formals-plus" :dir :system)
(include-book "kestrel/std/system/ubody-plus" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ functions
  :parents (acl2-programming-language)
  :short "A formalization of ACL2 defined functions."
  :long
  (xdoc::topstring
   (xdoc::p
    "Functions are defined via @(tsee defun) in ACL2.
     Its arguments include a list of formal parameters and a body,
     among others.")
   (xdoc::p
    "In our formalization, for now we only consider a function's
     name, parameters, and body.
     Thus, we introduce a notion of function as consisting of
     a name (a symbol),
     a list of parameters (symbols),
     and a body (a translated term);
     here we capture the unnormalized body of the function.
     This notion may be extended in the future as needed,
     e.g. to include a function's guard.")
   (xdoc::p
    "This is distinct from the notion of translated functions
     introduced as part of translated terms.
     Those (see the fixtype @(tsee tfunction))
     consist of symbols (i.e. just function names)
     and lambda expressions (i.e. unnamed functions)."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod function
  :short "Fixtype of (defined) functions."
  ((name symbol-value)
   (params symbol-value-list)
   (body tterm))
  :layout :list
  :pred functionp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defset function-set
  :short "Fixtype of finite sets of functions."
  :elt-type function
  :elementp-of-nil nil
  :pred function-setp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defoption maybe-function
  function
  :short "Fixtype of functions and @('nil')."
  :pred maybe-functionp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define function-lookup ((name symbol-valuep) (functions function-setp))
  :returns (function? maybe-functionp)
  :short "Look up a function in a set, by name."
  :long
  (xdoc::topstring
   (xdoc::p
    "We return the first function in the set with the given name, if any.
     If there is none, we return @('nil').")
   (xdoc::p
    "When a set of functions represents
     all the function definitions in an ACL2 environment,
     the list will have unique function names;
     this will be formalized elsewhere.
     Under this condition,
     returning the first function found
     is as good as returning any function with that name in the set,
     since there can be at most one."))
  (b* (((when (or (not (mbt (function-setp functions)))
                  (empty functions)))
        nil)
       (function (head functions))
       ((when (symbol-value-equiv name
                                  (function->name function)))
        function))
    (function-lookup name (tail functions)))
  ///
  (fty::deffixequiv function-lookup
    :hints (("Goal" :in-theory (enable function-set-fix)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define lift-function ((fn symbolp) (wrld plist-worldp))
  :returns (function functionp)
  :short "Lift a defined function from the current ACL2 environment
          to the meta level."
  :long
  (xdoc::topstring
   (xdoc::p
    "This must be used only on function symbols
     with an unnormalized body property.
     Otherwise, this causes an error.")
   (xdoc::p
    "If those conditions hold, we retrieve the function's
     formal parameters and (unnormalized) body,
     and we lift them to the meta level together with the name."))
  (b* (((when (not (function-symbolp fn wrld)))
        (raise "The symbol ~x0 does not name a function." fn)
        (ec-call (function-fix :irrelevant)))
       (params (formals+ fn wrld))
       (body (ubody+ fn wrld))
       ((unless (good-pseudo-termp body))
        (raise "Internal error: the term ~x0 is not good." body)
        (ec-call (function-fix :irrelevant)))
       ((when (null body))
        (raise "The function ~x0 has no unnormalized body." fn)
        (ec-call (function-fix :irrelevant))))
    (make-function :name (lift-symbol fn)
                   :params (lift-symbol-list params)
                   :body (lift-term body))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define lift-function-list ((fns symbol-listp) (wrld plist-worldp))
  :returns (functions function-setp)
  :short "Lift a list of functions (specified by symbol)
          from the current ACL2 environment to the meta level,
          obtaining a set of functions."
  (cond ((endp fns) nil)
        (t (insert (lift-function (car fns) wrld)
                   (lift-function-list (cdr fns) wrld)))))
