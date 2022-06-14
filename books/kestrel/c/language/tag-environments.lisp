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

(include-book "types")
(include-book "errors")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ tag-environments
  :parents (language)
  :short "C tag environments."
  :long
  (xdoc::topstring
   (xdoc::p
    "C code is statically checked and dynamically executed
     in the context of structure, union, and enumeration types.
     This context is captured via tag environments,
     where `tag' refers to the fact that tags identify
     structure, union, and enumeration types.
     These tag environments are used
     in both the static and dynamic semantics."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum tag-info
  :short "Fixtype of information about
          a structure, union, or enumeration type."
  :long
  (xdoc::topstring
   (xdoc::p
    "For now we only capture information about structure types;
     we use placeholders for union and enumeration types.")
   (xdoc::p
    "The information about a structure type consists of
     a list of member types (see @(see member-type)).
     This mirrors (the @(':struct') case of) @(tsee tag-declon).")
   (xdoc::p
    "The members must have unique names [C:6.2.3].
     There must be at least one member [C:6.2.5/20].
     Currently we do not capture these requirements in this fixtype."))
  (:struct ((members member-type-list)))
  (:union ())
  (:enum ())
  :pred tag-infop)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defoption tag-info-option
  tag-info
  :short "Fixtype of optional tag information."
  :pred tag-info-optionp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defomap tag-env
  :short "Fixtype of tag environments."
  :long
  (xdoc::topstring
   (xdoc::p
    "A tag environment is a finite map
     from tags (identifiers)
     to tag information.
     Since these tags form one name space [C:6.2.3],
     they must all be distinct,
     e.g. a structure and a union type cannot have the same tag."))
  :key-type ident
  :val-type tag-info
  :pred tag-envp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum tag-env-option
  :short "Fixtype of optional tag environments."
  (:some ((val tag-env)))
  (:none ())
  :pred tag-env-optionp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defresult tag-env "tag environments")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define tag-env-lookup ((tag identp) (env tag-envp))
  :returns (info tag-info-optionp
                 :hints (("Goal" :in-theory (enable tag-info-optionp))))
  :short "Look up a tag in a tag environment."
  (cdr (omap::in (ident-fix tag) (tag-env-fix env)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define tag-env-init ()
  :returns (env tag-envp)
  :short "Initial tag environment."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is empty."))
  nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define tag-env-add ((tag identp) (info tag-infop) (env tag-envp))
  :returns (new-env tag-env-optionp)
  :short "Add tag information to a tag environment."
  :long
  (xdoc::topstring
   (xdoc::p
    "We return the updated environment if the tag is not already present,
     otherwise we return no tag environment."))
  (b* ((tag (ident-fix tag))
       (info (tag-info-fix info))
       (env (tag-env-fix env)))
    (if (omap::in tag env)
        (tag-env-option-none)
      (tag-env-option-some (omap::update tag info env))))
  :hooks (:fix))
