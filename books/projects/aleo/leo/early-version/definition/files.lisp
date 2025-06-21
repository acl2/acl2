; Leo Library
;
; Copyright (C) 2025 Provable Inc.
;
; License: See the LICENSE file distributed with this library.
;
; Authors: Alessandro Coglio (www.alessandrocoglio.info)
;          Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "LEO-EARLY")

(include-book "annotations")
(include-book "statements")

(include-book "std/util/defprojection" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ files
  :parents (abstract-syntax)
  :short "Leo files."
  :long
  (xdoc::topstring
   (xdoc::p
    "Here we formalize an abstract syntactic representation of Leo files,
     including the top-level declarations that form the files."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum var/const-sort
  :short "Fixtype of sorts of variables and constants."
  :long
  (xdoc::topstring
   (xdoc::p
    "There are currently four sorts (i.e. kinds) of variables and constants:
     public variables,
     private variables,
     @('constant')-designated constants,
     and @('const')-designated constants.
     It is likely that the latter two will be unified,
     but for now we follow the grammar and have two.")
   (xdoc::p
    "These variable and constant sorts are used
     for function parameters and for input file items."))
  (:public ())
  (:private ())
  (:constant ())
  (:const ())
  :pred var/const-sortp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deflist var/const-sort-list
  :short "Fixtype of lists of variable and constant sorts."
  :elt-type var/const-sort
  :true-listp t
  :elementp-of-nil nil
  :pred var/const-sort-listp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defresult var/const-sort-result
  :short "Fixtype of errors and Leo variable or constant sorts."
  :ok var/const-sort
  :pred var/const-sort-resultp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum fun-sort
  :short "Fixtype of sorts of Leo functions."
  :long
  (xdoc::topstring
   (xdoc::p
    "There are currently two sorts (i.e. kinds) of functions:
     standard and transition.")
   ;; We expect 'inline' to be aother sort.
   ;; The finalize block is sort of like a function
   ;; but we represent it differently since it is
   ;; not processed like a function in most contexts.
   )
  (:standard ())
  (:transition ())
  :pred fun-sortp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defresult fun-sort-result
  :short "Fixtype of errors and Leo function sorts."
  :ok fun-sort
  :pred fun-sort-resultp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod funparam
  :short "Fixtype of Leo function parameters."
  :long
  (xdoc::topstring
   (xdoc::p
    "A function parameter consists of
     a name, a sort, and a type."))
  ((name identifier)
   (sort var/const-sort)
   (type type))
  :tag :funparam
  :pred funparamp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deflist funparam-list
  :short "Fixtype of lists of Leo function parameters."
  :elt-type funparam
  :true-listp t
  :elementp-of-nil nil
  :pred funparam-listp)

;;;;;;;;;;;;;;;;;;;;

(std::defprojection funparam-list->name-list (x)
  :guard (funparam-listp x)
  :returns (names identifier-listp)
  :short "Lift @(tsee funparam->name) to lists."
  (funparam->name x)
  ///
  (fty::deffixequiv funparam-list->name-list
    :args ((x funparam-listp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defresult funparam-result
  :short "Fixtype of errors and Leo function parameters."
  :ok funparam
  :pred funparam-resultp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defresult funparam-list-result
  :short "Fixtype of errors and lists of Leo function parameters."
  :ok funparam-list
  :pred funparam-list-resultp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod finalizer
  :short "Fixtype of Leo finalizer blocks."
  ((name identifier)
   (inputs funparam-list)
   (output type-option)
   (body statement-list))
  :tag :finalizer
  :pred finalizerp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defresult finalizer-result
  :short "Fixtype of errors and Leo finalizer blocks."
  :ok finalizer
  :pred finalizer-resultp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defoption finalizer-option
  finalizer
  :short "Fixtype of optional Leo finalizer blocks."
  :pred finalizer-optionp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defresult finalizer-option-result
  :short "Fixtype of errors and optional Leo finalizer blocks."
  :ok finalizer-optionp
  :pred finalizer-option-resultp
  :prepwork ((local (in-theory (enable finalizerp)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod fundecl
  :short "Fixtype of Leo function/transition declarations."
  :long
  (xdoc::topstring
   (xdoc::p
    "A function or transition declaration consists of zero or more annotations,
     a name,
     zero or more parameters,
     an output type,
     and a body block.")
   (xdoc::p
    "The @('sort') field differentiates between standard and transition functions.")
   (xdoc::p
    "If it is a transition, then it can have a finalizer."))
  ((annotations annotation-list)
   (sort fun-sort)
   (name identifier)
   (inputs funparam-list)
   (output type)
   (body statement-list)
   (finalizer finalizer-option))
  :tag :fundecl
  :pred fundeclp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deflist fundecl-list
  :short "Fixtype of lists of Leo function declarations."
  :elt-type fundecl
  :true-listp t
  :elementp-of-nil nil
  :pred fundecl-listp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defoption fundecl-option
  fundecl
  :short "Fixtype of optional Leo function declarations."
  :pred fundecl-optionp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defresult fundecl-result
  :short "Fixtype of errors and Leo function declarations."
  :ok fundecl
  :pred fundecl-resultp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod compdecl
  :short "Fixtype of struct component declarations."
  :long
  (xdoc::topstring
   (xdoc::p
    "A struct component declaration consists of a name and a type."))
  ((name identifier)
   (type type))
  :tag :compdecl
  :pred compdeclp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defresult compdecl-result
  :short "Fixtype of errors and Leo struct component declarations."
  :ok compdecl
  :pred compdecl-resultp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deflist compdecl-list
  :short "Fixtype of lists of struct component declarations."
  :elt-type compdecl
  :true-listp t
  :elementp-of-nil nil
  :pred compdecl-listp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defresult compdecl-list-result
  :short "Fixtype of errors and lists of Leo struct component declarations."
  :ok compdecl-list
  :pred compdecl-list-resultp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod structdecl
  :short "Fixtype of struct and record declarations."
  :long
  (xdoc::topstring
   (xdoc::p
    "A struct declaration consists of a name (identifier)
     and a list of struct component declarations.
     We do not require the list to be non-empty,
     at the abstract syntax level.")
   (xdoc::p
    "We also include a boolean flag that says whether
     the struct type is a record type or not.
     If the flag is set, we do not require, at the level of abstract syntax,
     that it has the required components for records;
     instead, this is enforced in the static semantics."))
  ((name identifier)
   (components compdecl-list)
   (recordp bool))
  :tag :structdecl
  :pred structdeclp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defresult structdecl-result
  :short "Fixtype of errors and Leo struct declarations."
  :ok structdecl
  :pred structdecl-resultp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod mappingdecl
  :short "Fixtype of mapping declarations."
  :long
  (xdoc::topstring
   (xdoc::p
    "A mapping declaration consists of a name (identifier)
     and domain and range types."))
  ((name identifier)
   (domain-type type)
   (range-type type))
  :tag :mappingdecl
  :pred mappingdeclp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defresult mappingdecl-result
  :short "Fixtype of errors and Leo mapping declarations."
  :ok mappingdecl
  :pred mappingdecl-resultp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum topdecl
  :short "Fixtype of Leo declarations at the top level in a program."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are function/transition, struct/record, and mapping declarations."))
  (:function ((get fundecl)))
  (:struct ((get structdecl)))
  (:mapping ((get mappingdecl)))
  :pred topdeclp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deflist topdecl-list
  :short "Fixtype of Leo top-level declarations."
  :elt-type topdecl
  :true-listp t
  :elementp-of-nil nil
  :pred topdecl-listp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defresult topdecl-result
  :short "Fixtype of errors and Leo top-level declarations."
  :ok topdecl
  :pred topdecl-resultp
  :prepwork ((local (in-theory (enable topdecl-kind)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defresult topdecl-list-result
  :short "Fixtype of errors and lists of Leo top-level declarations."
  :ok topdecl-list
  :pred topdecl-list-resultp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod importdecl
  :short "Fixtype of Leo import declarations."
  ((program programid))
  :tag :importdecl
  :pred importdeclp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deflist importdecl-list
  :short "Fixtype of lists of Leo import declarations."
  :elt-type importdecl
  :true-listp t
  :elementp-of-nil nil
  :pred importdecl-listp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defresult importdecl-result
  :short "Fixtype of errors and Leo import declarations."
  :ok importdecl
  :pred importdecl-resultp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defresult importdecl-list-result
  :short "Fixtype of errors and lists of Leo import declarations."
  :ok importdecl-list
  :pred importdecl-list-resultp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod programdecl
  :short "Fixtype of Leo program declarations."
  ((id programid)
   (items topdecl-list))
  :tag :programdecl
  :pred programdeclp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deflist programdecl-list
  :short "Fixtype of lists of Leo program declarations."
  :elt-type programdecl
  :true-listp t
  :elementp-of-nil nil
  :pred programdecl-listp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defresult programdecl-result
  :short "Fixtype of errors and Leo program declarations."
  :ok programdecl
  :pred programdecl-resultp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defresult programdecl-list-result
  :short "Fixtype of errors and lists of Leo program declarations."
  :ok programdecl-list
  :pred programdecl-list-resultp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod file
  :short "Fixtype of Leo files."
  :long
  (xdoc::topstring
   (xdoc::p
    "A file consists of a list of declarations.")
   (xdoc::p
    "We formalize a file as a one-component record,
     instead of directly as a list of definitions,
     so that we can capture more information about the file in the future.
     Furthermore, that provides a bit more abstraction."))
  ((imports importdecl-list)
   (program programdecl))
  :pred filep)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defresult file-result
  :short "Fixtype of errors and Leo files."
  :ok file
  :pred file-resultp)
