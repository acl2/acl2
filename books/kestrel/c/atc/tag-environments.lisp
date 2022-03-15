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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ tag-environments
  :parents (atc-static-semantics atc-dynamic-semantics)
  :short "C tag environments for ATC."
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

(fty::defprod member-info
  :short "Fixtype of member information."
  :long
  (xdoc::topstring
   (xdoc::p
    "This contains information about
     the members of structure and union types [C:6.7.2.1].
     This information consists of a name and a type.
     We do not capture bit fields (including anonymous ones)
     and we do not capture static assertions.
     This information mirrors @(tsee struct-declon)."))
  ((name ident)
   (type type))
  :tag :member-info
  :pred member-infop)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deflist member-info-list
  :short "Fixtype of lists of member information."
  :elt-type member-info
  :true-listp t
  :elementp-of-nil nil
  :pred member-info-listp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum member-info-list-option
  :short "Fixtype of optional lists of member information."
  (:some ((val member-info-list)))
  (:none ())
  :pred member-info-list-optionp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defresult member-info-list "lists of member information")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define member-lookup ((name identp) (members member-info-listp))
  :returns (type type-optionp)
  :short "Look up a member by name in a list of member information."
  :long
  (xdoc::topstring
   (xdoc::p
    "We search from the beginning and stop at the first hit;
     since the names are unique (see @(tsee tag-info)),
     the exact search strategy makes no difference
     We return the type of the member if the search is successful."))
  (b* (((when (endp members)) nil)
       ((when (equal (ident-fix name)
                     (member-info->name (car members))))
        (member-info->type (car members))))
    (member-lookup name (cdr members)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define member-add-first ((name identp)
                          (type typep)
                          (members member-info-listp))
  :returns (new-members member-info-list-optionp)
  :short "Add a member at the beginning of a list of member information."
  :long
  (xdoc::topstring
   (xdoc::p
    "We check that the a member with the same name is not already in the list,
     to maintain the invariant mentioned in @(tsee tag-info)."))
  (b* ((found (member-lookup name members))
       ((when found) (member-info-list-option-none)))
    (member-info-list-option-some
     (cons (make-member-info :name name :type type)
           members)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define member-add-last ((name identp)
                         (type typep)
                         (members member-info-listp))
  :returns (new-members member-info-list-optionp)
  :short "Add a member at the end of a list of member information."
  :long
  (xdoc::topstring
   (xdoc::p
    "We check that the a member with the same name is not already in the list,
     to maintain the invariant mentioned in @(tsee tag-info)."))
  (b* ((found (member-lookup name members))
       ((when found) (member-info-list-option-none)))
    (member-info-list-option-some
     (rcons (make-member-info :name name :type type)
            members)))
  :guard-hints (("Goal" :in-theory (enable rcons)))
  ///
  (fty::deffixequiv member-add-last
    :hints (("Goal" :in-theory (enable rcons)))))

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
     a list of member information (see @(see member-info)).
     This mirrors (the @(':struct') case of) @(tsee tag-declon).")
   (xdoc::p
    "The members must have unique names [C:6.2.3].
     There must be at least one member [C:6.2.5/20].
     Currently we do not capture these requirements in this fixtype."))
  (:struct ((members member-info-list)))
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

(define tag-lookup ((tag identp) (env tag-envp))
  :returns (info tag-info-optionp
                 :hints (("Goal" :in-theory (enable tag-info-optionp))))
  :short "Look up a tag in a tag environment."
  (cdr (omap::in (ident-fix tag) (tag-env-fix env)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define tag-add ((tag identp) (info tag-infop) (env tag-envp))
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
        (tag-env-option-some (omap::update tag info env))
      (tag-env-option-none)))
  :hooks (:fix))
