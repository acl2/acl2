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

(include-book "abstract-syntax")
(include-book "arrays")

(include-book "../language/portable-ascii-identifiers")

(include-book "kestrel/fty/pseudo-event-form" :dir :system)
(include-book "kestrel/std/system/table-alist-plus" :dir :system)
(include-book "kestrel/std/util/tuple" :dir :system)
(include-book "kestrel/utilities/er-soft-plus" :dir :system)

(local (include-book "std/typed-lists/symbol-listp" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ shallow-structures
  :parents (atc-shallow-embedding)
  :short "A model of C structures in the shallow embedding."
  :long
  (xdoc::topstring
   (xdoc::p
    "Since C structure types are user-defined,
     we provide a macro @(tsee defstruct) to define
     an ACL2 representation of a C structure type.
     The user must call this macro
     to introduce the structure types that the C code must use.")
   (xdoc::p
    "The @(tsee defstruct) macro takes as inputs
     the name (i.e. tag [C:6.7.2.3]) of the structure type
     and a sequence of members;
     each member consists of a name and a designation of
     an integer type or of a sized integer array type
     (for now we only support members of these types).
     The names of the structure type and of the members
     must be symbols whose @(tsee symbol-name) is a portable ASCII identifier;
     the members must have all different @(tsee symbol-name)s
     (it is not enough for the symbols to be different).")
   (xdoc::p
    "The designation of each member type is one of")
   (xdoc::ul
    (xdoc::li "@('schar')")
    (xdoc::li "@('uchar')")
    (xdoc::li "@('sshort')")
    (xdoc::li "@('ushort')")
    (xdoc::li "@('sint')")
    (xdoc::li "@('uint')")
    (xdoc::li "@('slong')")
    (xdoc::li "@('ulong')")
    (xdoc::li "@('sllong')")
    (xdoc::li "@('ullong')")
    (xdoc::li "@('(schar <pos>)')")
    (xdoc::li "@('(uchar <pos>)')")
    (xdoc::li "@('(sshort <pos>)')")
    (xdoc::li "@('(ushort <pos>)')")
    (xdoc::li "@('(sint <pos>)')")
    (xdoc::li "@('(uint <pos>)')")
    (xdoc::li "@('(slong <pos>)')")
    (xdoc::li "@('(ulong <pos>)')")
    (xdoc::li "@('(sllong <pos>)')")
    (xdoc::li "@('(ullong <pos>)')"))
   (xdoc::p
    "where @('<pos>') is a positive integer not exceeding @(tsee ullong-max).
     That is, the type of a member of integer type is specified by
     the name of the fixtype of the integer type,
     while the type of a member of integer array type is specified by
     the name of the fixtype of the integer type and a size;
     the size must be representable as an integer constant
     (i.e. not exceed @(tsee ullong-max),
     which is the maximum integer representable as an integer constant).")
   (xdoc::p
    "Let @('<tag>') be the tag of the structure type.")
   (xdoc::p
    "The @(tsee defstruct) macro introduces:")
   (xdoc::ul
    (xdoc::li
     "A recognizer @('struct-<tag>-p') for the structures.")
    (xdoc::li
     "A fixer @('struct-<tag>-fix') for the structures.")
    (xdoc::li
     "A fixtype @('struct-<tag>') for the structures."))
   (xdoc::p
    "For each member named @('<member>') of integer type,
     the @(tsee defstruct) macro introduces:")
   (xdoc::ul
    (xdoc::li
     "A reader @('struct-<tag>-read-<member>')
      that returns the value of the member.")
    (xdoc::li
     "A writer @('struct-<tag>-write-<member>')
      that updates the value of the member."))
   (xdoc::p
    "For each member named @('<member>') of integer array type,
     the @(tsee defstruct) macro introduces:")
   (xdoc::ul
    (xdoc::li
     "A checker @('struct-<tag>-<member>-index-okp)
      that checks whether an ACL2 integer index
      is within the range of the array.")
    (xdoc::li
     "A checker @('struct-<tag>-<member>-<type>-index-okp'),
      for each @('<type>') that is the name of a fixtype of a C integer type,
      that checks whether an index of the C integer type denoted by @('<type>')
      is within the range of the array.")
    (xdoc::li
     "A reader @('struct-<tag>-read-<member>')
      that returns the value of an element of the array,
      where the element is indexed by an ACL2 integer.
      This reader uses @('struct-<tag>-<member>-index-okp')
      in the guard.")
    (xdoc::li
     "A reader @('struct-<tag>-read-<member>-<type>'),
      for each @('<type>') that is the name of a fixtype of a C integer type,
      that returns the value of an element of the array,
      where the element is indexed by a C integer type denoted by @('<type>').
      This reader has @('struct-<tag>-<member>-<type>-index-okp')
      in the guard.")
    (xdoc::li
     "A writer @('struct-<tag>-write-<member>')
      that updates the value of an element of the array,
      where the element is indexed by an ACL2 integer.
      This writer uses @('struct-<tag>-<member>-index-okp')
      in the guard.")
    (xdoc::li
     "A writer @('struct-<tag>-write-<member>-<type>'),
      for each @('<type>') that is the name of a fixtype of a C integer type,
      that udpates the value of an element of the array,
      where the element is indexed by a C integer type denoted by @('<type>').
      This writer has @('struct-<tag>-<member>-<type>-index-okp')
      in the guard."))
   (xdoc::p
    "C code shallowly embedded in ACL2 can use
     the recognizers @('struct-<tag>-p') in guards
     to specify structure types for parameters;
     more precisely, pointers to structure types, for now.
     That is, similarly to arrays, structures are in the heap,
     and pointers to them are passed to the represented C functions,
     which may side-effect those structures via the member writers,
     which represent assignments to structure members
     accessed via the C @('->') operator (not the @('.') operator).
     C structures may also be passed around by value in general,
     but initially we support only passing by pointer.
     Note that C arrays may only be passed by pointers, in effect,
     as arrays are not first-class entities in C,
     but merely collections of contiguous objects,
     normally accessed via pointers to the first object of the collections.")
   (xdoc::p
    "The @(tsee defstruct) macro also records, in an ACL2 table,
     information about the shallowly embedded structures it defines."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defval *defstruct-table*
  :short "Name of the table of shallowly embedded C structures."
  'defstruct-table)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod defstruct-member-info
  :short "Fixtype of information about
          members of shallowly embedded C structures."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are part of @(tsee defstruct-info).")
   (xdoc::p
    "For each member, we store:")
   (xdoc::ul
    (xdoc::li
     "The member type, which consists of the name and type of the member.
      See @(tsee member-type) in the deep embedding.")
    (xdoc::li
     "The named of the readers of the member.
      For an integer member, it is a singleton list of the one reader.
      For an array member, it is a list of ten readers,
      one for each supported integer type for the index.")
    (xdoc::li
     "The names of the writers of the member.
      For an integer member, it is a singleton list of the one writer.
      For an array member, it is a list of ten writers,
      one for each supported integer type for the index.")
    (xdoc::li
     "The names of the checkers of the member.
      This is the empty list for an integer member,
      while it consists of ten checkers for an array member,
      one for each supported integer type for the index.")
    (xdoc::li
     "The names of the return type theorems
      for all the readers, in the same order as the list of readers.")
    (xdoc::li
     "The names of the return type theorems
      for all the writers, in the same order as the list of writers.")))
  ((memtype member-type)
   (readers symbol-listp)
   (writers symbol-listp)
   (checkers symbol-listp)
   (reader-return-thms symbol-listp)
   (writer-return-thms symbol-listp))
  :pred defstruct-member-infop)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deflist defstruct-member-info-list
  :short "Fixtype of lists of information about
          members of shallowly embedded C structures."
  :elt-type defstruct-member-info
  :true-listp t
  :elementp-of-nil nil
  :pred defstruct-member-info-listp)

;;;;;;;;;;;;;;;;;;;;

(std::defprojection defstruct-member-info-list->memtype-list (x)
  :guard (defstruct-member-info-listp x)
  :returns (memtypes member-type-listp)
  :short "Lift @(tsee defstruct-member-info->memtype) to lists."
  (defstruct-member-info->memtype x)
  ///
  (fty::deffixequiv defstruct-member-info-list->memtype-list
    :args ((x defstruct-member-info-listp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod defstruct-info
  :short "Fixtype of information about shallowly embedded C structures."
  :long
  (xdoc::topstring
   (xdoc::p
    "For each C structure type defined via @(tsee defstruct), we store:")
   (xdoc::ul
    (xdoc::li
     "The tag, as an identifier.
      While currently @(tsee ident) is just a wrapper of @(tsee string),
      it may include invariants in the future.
      Thus, having the tag stored as an identifier in the structure information
      will spare us from having to double-check the invariants
      if we were to construct the identifier from the string.")
    (xdoc::li
     "Information for the members; see @(tsee defstruct-member-info).")
    (xdoc::li
     "The recognizer of the structures.")
    (xdoc::li
     "The fixer of the structures.")
    (xdoc::li
     "The name of the theorem that rewrites away the fixer
      when the recognizer holds.")
    (xdoc::li
     "The name of a theorem asserting that
      if something is a structure of this type
      then it is not an error.")
    (xdoc::li
     "The name of the theorem asserting that
      the recognizer implies @(tsee valuep).")
    (xdoc::li
     "The name of the theorem asserting that
      the recognizer implies that @(tsee value-kind) is @(':struct').")
    (xdoc::li
     "The name of the theorem asserting that
      the recognizer implies that @(tsee type-of-value)
      returns the struct type."))
   (xdoc::p
    "The call of @(tsee defstruct).
     This supports redundancy checking."))
  ((tag ident)
   (members defstruct-member-info-list)
   (recognizer symbolp)
   (fixer symbolp)
   (fixer-recognizer-thm symbolp)
   (not-error-thm symbolp)
   (valuep-thm symbolp)
   (value-kind-thm symbolp)
   (type-of-value-thm symbolp)
   (call pseudo-event-form))
  :pred defstruct-infop)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defoption defstruct-info-option
  defstruct-info
  :short "Fixtype of
          optional information about shallowly embedded C structures."
  :pred defstruct-info-optionp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defstruct-info->readers ((info defstruct-infop))
  :returns (readers symbol-listp)
  :short "Names of all the readers of a @(tsee defstruct)."
  (defstruct-info->readers-aux (defstruct-info->members info))
  :prepwork
  ((define defstruct-info->readers-aux ((members defstruct-member-info-listp))
     :returns (readers symbol-listp)
     :parents nil
     (cond ((endp members) nil)
           (t (append (defstruct-member-info->readers (car members))
                      (defstruct-info->readers-aux (cdr members))))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defstruct-info->writers ((info defstruct-infop))
  :returns (writers symbol-listp)
  :short "Names of all the writers of a @(tsee defstruct)."
  (defstruct-info->writers-aux (defstruct-info->members info))
  :prepwork
  ((define defstruct-info->writers-aux ((members defstruct-member-info-listp))
     :returns (writers symbol-listp)
     :parents nil
     (cond ((endp members) nil)
           (t (append (defstruct-member-info->writers (car members))
                      (defstruct-info->writers-aux (cdr members))))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defstruct-info->reader-return-thms ((info defstruct-infop))
  :returns (thms symbol-listp)
  :short "Names of all the reader return theorems of a @(tsee defstruct)."
  (defstruct-info->reader-return-thms-aux (defstruct-info->members info))
  :prepwork
  ((define defstruct-info->reader-return-thms-aux
     ((members defstruct-member-info-listp))
     :returns (thms symbol-listp)
     :parents nil
     (cond
      ((endp members) nil)
      (t (append (defstruct-member-info->reader-return-thms (car members))
                 (defstruct-info->reader-return-thms-aux (cdr members))))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defstruct-info->writer-return-thms ((info defstruct-infop))
  :returns (thms symbol-listp)
  :short "Names of all the writer return theorems of a @(tsee defstruct)."
  (defstruct-info->writer-return-thms-aux (defstruct-info->members info))
  :prepwork
  ((define defstruct-info->writer-return-thms-aux
     ((members defstruct-member-info-listp))
     :returns (thms symbol-listp)
     :parents nil
     (cond
      ((endp members) nil)
      (t (append (defstruct-member-info->writer-return-thms (car members))
                 (defstruct-info->writer-return-thms-aux (cdr members))))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection defstruct-table-definition
  :short "Definition of the table of shallowly embedded C structures."
  :long
  (xdoc::topstring
   (xdoc::p
    "The keys are strings that are @(tsee symbol-name)s of
     symbols that represent the tags of the structures.
     The name of each such symbol is a portable ASCII C identifier,
     but this constraint is not enforced in the table's guard.
     The keys in the table are unique.")
   (xdoc::p
    "The values are the information about the structures.
     See @(tsee defstruct-info)."))

  (make-event
   `(table ,*defstruct-table* nil nil
      :guard (and (stringp acl2::key)
                  (defstruct-infop acl2::val)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defstruct-table-lookup ((tag stringp) (wrld plist-worldp))
  :returns (info? defstruct-info-optionp
                  :hints (("Goal" :in-theory (enable defstruct-info-optionp))))
  :short "Retrieve information about a shallowly embedded C structure."
  (b* ((pair (assoc-equal tag (table-alist+ *defstruct-table* wrld)))
       ((when (not (consp pair))) nil)
       (info (cdr pair))
       ((unless (defstruct-infop info))
        (raise "Internal error: malformed DEFSTRUCT information ~x0." info)))
    info))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defstruct-table-record-event ((tag stringp) (info defstruct-infop))
  :returns (event pseudo-event-formp)
  :short "Event to update the table of shallowly embedded C structures
          by recording a new C structure in it."
  `(table ,*defstruct-table* ,tag ',info))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defstruct-process-members ((members true-listp) (ctx ctxp) state)
  :returns (mv erp (memtypes member-type-listp) state)
  :short "Process the member inputs of a @(tsee defstruct) call."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are the inputs of @(tsee defstruct) after the first one,
     which specifies the structure tag.
     Each such input must be a doublet.")
   (xdoc::p
    "The first component of the doublet represents the member name.
     It must be a symbol whose name is a portable ASCII C identifier
     that is distinct from the other member names.")
   (xdoc::p
    "The second component of the doublet represents the member type.
     It must be
     either one of the fixtype names of the C integer types,
     or a doublet @('(<type> <pos>)')
     consisting of one of the fixtype names of the C integer types
     followed by a positive integer."))
  (b* ((typelist '(schar
                   uchar
                   sshort
                   ushort
                   sint
                   uint
                   slong
                   ulong
                   sllong
                   ullong))
       ((when (endp members)) (acl2::value nil))
       (member (car members))
       ((unless (std::tuplep 2 member))
        (er-soft+ ctx t nil
                  "Each input after the first one ~
                   must be a doublet (NAME TYPE), ~
                   but the input ~x0 does not have this form."
                  member))
       (name (first member))
       (type (second member))
       ((unless (symbolp name))
        (er-soft+ ctx t nil
                  "Each input after the first one ~
                   must be a doublet (NAME TYPE) of symbols, ~
                   but the first component of ~x0 is not a symbol."
                  member))
       (name (symbol-name name))
       ((unless (ident-stringp name))
        (er-soft+ ctx t nil
                  "Each input after the first one ~
                   must be a doublet (NAME TYPE) of symbols ~
                   where the SYMBOL-NAME of NAME is ~
                   a portable ASCII C identifier (see ATC user documentation), ~
                   but the SYMBOL-NAME of the first component of ~x0 ~
                   is not a portable ASCII C identifier."
                  member))
       ((er type)
        (if (symbolp type)
            (b* ((type (fixtype-to-integer-type type))
                 ((when (not type))
                  (er-soft+ ctx t nil
                            "Each input after the first one ~
                             must be a doublet (NAME TYPE) ~
                             where TYPE is ~
                             either one of the symbols in ~&0, ~
                             or a doublet (ELEM SIZE) ~
                             where ELEM is one of the symbols in ~&0
                             and SIZE is a positive intger.
                             The second component of ~x1 ~
                             is a symbol, but not among ~&0."
                            typelist
                            member)))
              (acl2::value type))
          (b* (((unless (std::tuplep 2 type))
                (er-soft+ ctx t nil
                          "Each input after the first one ~
                           must be a doublet (NAME TYPE) ~
                           where TYPE is ~
                           either one of the symbols in ~&0, ~
                           or a doublet (ELEM SIZE) ~
                           where ELEM is one of the symbols in ~&0
                           and SIZE is a positive intger.
                           The second component of ~x1 ~
                           is neither a symbol nor a doublet."
                          typelist
                          member))
               (elem (first type))
               (size (second type))
               ((unless (symbolp elem))
                (er-soft+ ctx t nil
                          "Each input after the first one ~
                           must be a doublet (NAME TYPE) ~
                           where TYPE is ~
                           either one of the symbols in ~&0, ~
                           or a doublet (ELEM SIZE) ~
                           where ELEM is one of the symbols in ~&0
                           and SIZE is a positive intger.
                           The second component of ~x1 is a doublet, ~
                           but its first component is not a symbol."
                          typelist
                          member))
               (elem (fixtype-to-integer-type elem))
               ((when (not elem))
                (er-soft+ ctx t nil
                          "Each input after the first one ~
                           must be a doublet (NAME TYPE) ~
                           where TYPE is ~
                           either one of the symbols in ~&0, ~
                           or a doublet (ELEM SIZE) ~
                           where ELEM is one of the symbols in ~&0
                           and SIZE is a positive intger.
                           The second component of ~x1 is a doublet, ~
                           but its first component is not ~
                           one of the symbols in ~&0."
                          typelist
                          member))
               ((unless (posp size))
                (er-soft+ ctx t nil
                          "Each input after the first one ~
                           must be a doublet (NAME TYPE) ~
                           where TYPE is ~
                           either one of the symbols in ~&0, ~
                           or a doublet (ELEM SIZE) ~
                           where ELEM is one of the symbols in ~&0
                           and SIZE is a positive intger.
                           The second component of ~x1 is a doublet, ~
                           but its second component is not a positive integer."
                          typelist
                          member))
               ((unless (<= size (ullong-max)))
                (er-soft+ ctx t nil
                          "Each input after the first one ~
                           must be a doublet (NAME TYPE) ~
                           where TYPE is ~
                           either one of the symbols in ~&0, ~
                           or a doublet (ELEM SIZE) ~
                           where ELEM is one of the symbols in ~&0
                           and SIZE is a positive intger.
                           The second component of ~x1 is a doublet, ~
                           its second component is a positive integer, ~
                           but it exceeds ~x2, ~
                           which is the maximum integer ~
                           representable in an unsigned long long int."
                          typelist
                          member
                          (ullong-max))))
            (acl2::value (make-type-array :of elem :size size)))))
       (memtype (make-member-type :name (ident name) :type type))
       ((er memtypes) (defstruct-process-members (cdr members) ctx state))
       ((when (member-equal (ident name)
                            (member-type-list->name-list memtypes)))
        (er-soft+ ctx t nil
                  "There are distinct members with the same name ~x0."
                  name)))
    (acl2::value (cons memtype memtypes)))
  :verify-guards :after-returns)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defstruct-process-inputs ((args true-listp)
                                  (call pseudo-event-formp)
                                  (ctx ctxp)
                                  state)
  :returns (mv erp
               (val (tuple (tag symbolp)
                           (tag-ident identp)
                           (memtypes member-type-listp)
                           (redundant booleanp)
                           val))
               state)
  :short "Process the inputs of a @(tsee defstruct) call."
  :long
  (xdoc::topstring
   (xdoc::p
    "We process the tag and the members.
     If the table already contains an entry for this tag,
     the call must be identical, in which case the call is redundant;
     if the call is not identical, it is an error."))
  (b* ((irrelevant (list nil (irr-ident) nil nil))
       ((unless (consp args))
        (er-soft+ ctx t irrelevant
                  "There must be at least one input, ~
                   but no inputs were supplied."))
       (tag (car args))
       ((unless (symbolp tag))
        (er-soft+ ctx t irrelevant
                  "The first input must be a symbol, ~
                   but ~x0 is not."
                  tag))
       (tag-name (symbol-name tag))
       ((unless (ident-stringp tag-name))
        (er-soft+ ctx t irrelevant
                  "The name ~x0 of the symbol ~x1 passed as first input, ~
                   which defines the name of the structure, ~
                   must be a portable ASCII C identifier."
                  tag-name tag))
       (tag-ident (ident tag-name))
       (info (defstruct-table-lookup tag-name (w state)))
       ((when info)
        (if (equal (defstruct-info->call info) call)
            (acl2::value (list tag (irr-ident) nil t))
          (er-soft+ ctx t irrelevant
                    "There is already a structure with tag ~x0 ~
                     recorded in the table of shallowly embedded C structures, ~
                     but its call ~x1 differs from the current ~x2, ~
                     so the call is not redundant."
                    tag-name (defstruct-info->call info) call)))
       (members (cdr args))
       ((unless (consp members))
        (er-soft+ ctx t irrelevant
                  "There must be at least one member."))
       ((mv erp memtypes state) (defstruct-process-members members ctx state))
       ((when erp) (mv erp irrelevant state)))
    (acl2::value (list tag tag-ident memtypes nil)))
  ///
  (more-returns
   (val true-listp :rule-classes :type-prescription)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defstruct-gen-recognizer-conjuncts ((memtype member-typep))
  :returns (terms true-listp "A list of untranslated terms.")
  :short "Generate conjuncts for a member in the recognizer of the structures."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is used by @(tsee defstruct-gen-recognizer).
     For each member, there is one or more conjunct that constrains its value.
     An integer member has just one conjunct saying that
     the value satisfies the predicate that recognizes those integer values.
     An array member has two conjuncts,
     one saying that the value is an array of the appropriate type,
     and one saying that the length of the array
     is the one indicated in the type.")
   (xdoc::p
    "The value of the member is retrieved via @('value-struct-read-aux')
     (see @(tsee value-struct-read)),
     which is a lookup function on member values
     (and perhaps it should be renamed to something better
     than an @('aux')(iliary) function)."))
  (b* ((name (member-type->name memtype))
       (type (member-type->type memtype)))
    (type-case
     type
     :void (raise "Internal error: type ~x0." type)
     :char (raise "Internal error: type ~x0." type)
     :schar `((scharp (value-struct-read-aux ',name
                                             (value-struct->members x))))
     :uchar `((ucharp (value-struct-read-aux ',name
                                             (value-struct->members x))))
     :sshort `((sshortp (value-struct-read-aux ',name
                                               (value-struct->members x))))
     :ushort `((ushortp (value-struct-read-aux ',name
                                               (value-struct->members x))))
     :sint `((sintp (value-struct-read-aux ',name
                                           (value-struct->members x))))
     :uint `((uintp (value-struct-read-aux ',name
                                           (value-struct->members x))))
     :slong `((slongp (value-struct-read-aux ',name
                                             (value-struct->members x))))
     :ulong `((ulongp (value-struct-read-aux ',name
                                             (value-struct->members x))))
     :sllong `((sllongp (value-struct-read-aux ',name
                                               (value-struct->members x))))
     :ullong `((ullongp (value-struct-read-aux ',name
                                               (value-struct->members x))))
     :struct (raise "Internal error: type ~x0." type)
     :pointer (raise "Internal error: type ~x0." type)
     :array (if (not type.size)
                (raise "Internal error: type ~x0." type)
              (type-case
               type.of
               :void (raise "Internal error: type ~x0." type)
               :char (raise "Internal error: type ~x0." type)
               :schar `((schar-arrayp
                         (value-struct-read-aux
                          ',name
                          (value-struct->members x)))
                        (equal (schar-array-length
                                (value-struct-read-aux
                                 ',name
                                 (value-struct->members x)))
                               ,type.size))
               :uchar `((uchar-arrayp
                         (value-struct-read-aux
                          ',name
                          (value-struct->members x)))
                        (equal (uchar-array-length
                                (value-struct-read-aux
                                 ',name
                                 (value-struct->members x)))
                               ,type.size))
               :sshort `((sshort-arrayp
                          (value-struct-read-aux
                           ',name
                           (value-struct->members x)))
                         (equal (sshort-array-length
                                 (value-struct-read-aux
                                  ',name
                                  (value-struct->members x)))
                                ,type.size))
               :ushort `((ushort-arrayp
                          (value-struct-read-aux
                           ',name
                           (value-struct->members x)))
                         (equal (ushort-array-length
                                 (value-struct-read-aux
                                  ',name
                                  (value-struct->members x)))
                                ,type.size))
               :sint `((sint-arrayp
                        (value-struct-read-aux
                         ',name
                         (value-struct->members x)))
                       (equal (sint-array-length
                               (value-struct-read-aux
                                ',name
                                (value-struct->members x)))
                              ,type.size))
               :uint `((uint-arrayp
                        (value-struct-read-aux
                         ',name
                         (value-struct->members x)))
                       (equal (uint-array-length
                               (value-struct-read-aux
                                ',name
                                (value-struct->members x)))
                              ,type.size))
               :slong `((slong-arrayp
                         (value-struct-read-aux
                          ',name
                          (value-struct->members x)))
                        (equal (slong-array-length
                                (value-struct-read-aux
                                 ',name
                                 (value-struct->members x)))
                               ,type.size))
               :ulong `((ulong-arrayp
                         (value-struct-read-aux
                          ',name
                          (value-struct->members x)))
                        (equal (ulong-array-length
                                (value-struct-read-aux
                                 ',name
                                 (value-struct->members x)))
                               ,type.size))
               :sllong `((sllong-arrayp
                          (value-struct-read-aux
                           ',name
                           (value-struct->members x)))
                         (equal (sllong-array-length
                                 (value-struct-read-aux
                                  ',name
                                  (value-struct->members x)))
                                ,type.size))
               :ullong `((ullong-arrayp
                          (value-struct-read-aux
                           ',name
                           (value-struct->members x)))
                         (equal (ullong-array-length
                                 (value-struct-read-aux
                                  ',name
                                  (value-struct->members x)))
                                ,type.size))
               :struct (raise "Internal error: type ~x0." type)
               :pointer (raise "Internal error: type ~x0." type)
               :array (raise "Internal error: type ~x0." type)))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defstruct-gen-recognizer-all-conjuncts ((memtypes member-type-listp))
  :returns (terms true-listp "A list of untranslated terms.")
  :short "Generate conjuncts for all members
          in the recognizer of the structures."
  :long
  (xdoc::topstring
   (xdoc::p
    "This calls @(tsee defstruct-gen-recognizer-conjuncts) on all the members.
     See that function for details on the conjuncts."))
  (cond ((endp memtypes) nil)
        (t (append (defstruct-gen-recognizer-conjuncts (car memtypes))
                   (defstruct-gen-recognizer-all-conjuncts (cdr memtypes)))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defstruct-gen-recognizer ((struct-tag-p symbolp)
                                  (tag symbolp)
                                  (memtypes member-type-listp))
  :returns (mv (event pseudo-event-formp)
               (not-error-thm symbolp)
               (valuep-thm symbolp)
               (value-kind-thm symbolp)
               (type-of-value-thm symbolp))
  :short "Generate the recognizer of
          the structures defined by the @(tsee defstruct)."
  :long
  (xdoc::topstring
   (xdoc::p
    "This recognizes structures
     with the appropriate types, member names, and member types.")
   (xdoc::p
    "We also generate several theorems;
     see @(tsee defstruct-info)."))
  (b* ((not-errorp-when-struct-tag-p
        (packn-pos (list 'not-errorp-when- struct-tag-p)
                   struct-tag-p))
       (valuep-when-struct-tag-p
        (packn-pos (list 'valuep-when- struct-tag-p)
                   struct-tag-p))
       (value-kind-when-struct-tag-p
        (packn-pos (list 'value-kind-when- struct-tag-p)
                   struct-tag-p))
       (type-of-value-when-struct-tag-p
        (packn-pos (list 'type-of-value-when- struct-tag-p)
                   struct-tag-p))
       (event
        `(define ,struct-tag-p (x)
           :returns (yes/no booleanp)
           (and (valuep x)
                (value-case x :struct)
                (equal (value-struct->tag x)
                       (ident ,(symbol-name tag)))
                (equal (member-value-list->name-list (value-struct->members x))
                       ',(member-type-list->name-list memtypes))
                ,@(defstruct-gen-recognizer-all-conjuncts memtypes))
           :hooks (:fix)
           ///
           (defruled ,not-errorp-when-struct-tag-p
             (implies (,struct-tag-p x)
                      (not (errorp x)))
             :enable (errorp ,struct-tag-p valuep))
           (defruled ,valuep-when-struct-tag-p
             (implies (,struct-tag-p x)
                      (valuep x))
             :in-theory '(,struct-tag-p))
           (defruled ,value-kind-when-struct-tag-p
             (implies (,struct-tag-p x)
                      (equal (value-kind x) :struct))
             :in-theory '(,struct-tag-p))
           (defruled ,type-of-value-when-struct-tag-p
             (implies (,struct-tag-p x)
                      (equal (type-of-value x)
                             (type-struct (ident ,(symbol-name tag)))))
             :in-theory '(,struct-tag-p
                          type-of-value)))))
    (mv event
        not-errorp-when-struct-tag-p
        valuep-when-struct-tag-p
        value-kind-when-struct-tag-p
        type-of-value-when-struct-tag-p)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defstruct-gen-fixing-term ((type typep))
  :returns (term "An untranslated term.")
  :short "Generate the fixing term for a member of a given type."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is used in @(tsee defstruct-gen-fixer).
     We only the types allowed for structure memberd by @(tsee defstruct)."))
  (type-case
   type
   :void (raise "Internal error: type ~x0." type)
   :char (raise "Internal error: type ~x0." type)
   :schar '(schar 0)
   :uchar '(uchar 0)
   :sshort '(sshort 0)
   :ushort '(ushort 0)
   :sint '(sint 0)
   :uint '(uint 0)
   :slong '(slong 0)
   :ulong '(ulong 0)
   :sllong '(sllong 0)
   :ullong '(ullong 0)
   :struct (raise "Internal error: type ~x0." type)
   :pointer (raise "Internal error: type ~x0." type)
   :array (if (not type.size)
              (raise "Internal error: type ~x0." type)
            (type-case
             type.of
             :void (raise "Internal error: type ~x0." type)
             :char (raise "Internal error: type ~x0." type)
             :schar `(make-value-array
                      :elemtype (type-schar)
                      :elements (repeat ,type.size (schar 0)))
             :uchar `(make-value-array
                      :elemtype (type-uchar)
                      :elements (repeat ,type.size (uchar 0)))
             :sshort `(make-value-array
                       :elemtype (type-sshort)
                       :elements (repeat ,type.size (sshort 0)))
             :ushort `(make-value-array
                       :elemtype (type-ushort)
                       :elements repeat ,type.size (ushort 0))
             :sint `(make-value-array
                     :elemtype (type-sint)
                     :elements (repeat ,type.size (sint 0)))
             :uint `(make-value-array
                     :elemtype (type-uint)
                     :elements (repeat ,type.size (uint 0)))
             :slong `(make-value-array
                      :elemtype (type-slong)
                      :elements (repeat ,type.size (slong 0)))
             :ulong `(make-value-array
                      :elemtype (type-ulong)
                      :elements (repeat ,type.size (ulong 0)))
             :sllong `(make-value-array
                       :elemtype (type-sllong)
                       :elements (repeat ,type.size (sllong 0)))
             :ullong `(make-value-array
                       :elemtype (type-ullong)
                       :elements (repeat ,type.size (ullong 0)))
             :struct (raise "Internal error: type ~x0." type)
             :pointer (raise "Internal error: type ~x0." type)
             :array (raise "Internal error: type ~x0." type))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defstruct-gen-fixer ((struct-tag-fix symbolp)
                             (struct-tag-p symbolp)
                             (tag symbolp)
                             (memtypes member-type-listp))
  :returns (mv (event pseudo-event-formp)
               (fixer-recognizer-thm symbolp))
  :short "Generate the fixer of
          the structures defined by the @(tsee defstruct)."
  :long
  (xdoc::topstring
   (xdoc::p
    "As the fixing value,
     we pick a structure with the right tag,
     the right member names,
     zero integer values of appropriate types for the integer members,
     and arrays of zeros of appropriate types and appropriate lengths
     for the integer array mmbers.")
   (xdoc::p
    "We also return the name of the theorem that
     rewrites the fixer away when the recognizer holds."))
  (b* ((event
        `(std::deffixer ,struct-tag-fix
           :pred ,struct-tag-p
           :param x
           :body-fix (make-value-struct
                      :tag (ident ,(symbol-name tag))
                      :members (list ,@(defstruct-gen-fixer-aux memtypes)))))
       (thm (packn-pos (list struct-tag-fix '-when- struct-tag-p)
                       struct-tag-fix)))
    (mv event thm))

  :prepwork
  ((define defstruct-gen-fixer-aux ((memtypes member-type-listp))
     :returns (terms true-listp)
     :parents nil
     (b* (((when (endp memtypes)) nil)
          ((member-type member) (car memtypes))
          (val (defstruct-gen-fixing-term member.type))
          (term `(make-member-value :name ',member.name :value ,val))
          (terms (defstruct-gen-fixer-aux (cdr memtypes))))
       (cons term terms)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defstruct-gen-fixtype ((struct-tag symbolp)
                               (struct-tag-p symbolp)
                               (struct-tag-fix symbolp)
                               (struct-tag-equiv symbolp))
  :returns (event pseudo-event-formp)
  :short "Generate the fixtype of
          the structures defined by the @(tsee defstruct)."
  `(fty::deffixtype ,struct-tag
     :pred ,struct-tag-p
     :fix ,struct-tag-fix
     :equiv ,struct-tag-equiv
     :define t
     :forward t))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defstruct-gen-integer-member-ops ((struct-tag symbolp)
                                          (struct-tag-p symbolp)
                                          (struct-tag-fix symbolp)
                                          (name identp)
                                          (type typep))
  :guard (type-integerp type)
  :returns (mv (event pseudo-event-formp)
               (reader symbolp)
               (writer symbolp)
               (reader-return-thm symbolp)
               (writer-return-thm symbolp))
  :short "Generate the operations for an integer member of
          the structures defined by the @(tsee defstruct)."
  :long
  (xdoc::topstring
   (xdoc::p
    "This are one reader and one writer.
     The reader is a wrapper of @(tsee value-struct-read),
     and the writer is a wrapper of @(tsee value-struct-write),
     but they have more specialized input and output types;
     in particular, they never return errors.
     To prove the output type of the reader,
     we just need to open some definitions.
     To prove the output type of the writer,
     we use an intermediate lemma.")
   (xdoc::p
    "Also return the information about the member
     for the @(tsee defstruct) table."))
  (b* ((fixtype (integer-type-to-fixtype type))
       (typep (pack fixtype 'p))
       (type-fix (pack fixtype '-fix))
       (struct-tag-read-name (packn-pos (list struct-tag
                                              '-read-
                                              (ident->name name))
                                        struct-tag))
       (struct-tag-write-name (packn-pos (list struct-tag
                                               '-write-
                                               (ident->name name))
                                         struct-tag))
       (reader-return-thm (packn-pos (list typep
                                           '-of-
                                           struct-tag-read-name)
                                     struct-tag-read-name))
       (writer-return-thm (packn-pos (list struct-tag-p
                                           '-of-
                                           struct-tag-write-name)
                                     struct-tag-write-name))
       (event
        `(encapsulate ()
           (defrulel lemma
             (implies (and (,struct-tag-p struct)
                           (,typep val))
                      (,struct-tag-p (value-struct-write ',name val struct)))
             :enable (,struct-tag-p
                      value-struct-write
                      member-value-listp-of-value-struct-write-aux
                      member-value-list->name-list-of-struct-write-aux
                      value-struct-read-aux-of-value-struct-write-aux
                      not-errorp-when-member-value-listp
                      ,(packn-pos (list 'type-of-value-when- typep)
                                  'type-of-value)))
           (define ,struct-tag-read-name ((struct ,struct-tag-p))
             :returns (val ,typep
                           :hints
                           (("Goal" :in-theory (enable value-struct-read
                                                       ,struct-tag-p
                                                       ,struct-tag-fix))))
             (value-struct-read (ident ,(ident->name name))
                                (,struct-tag-fix struct))
             :hooks (:fix))
           (define ,struct-tag-write-name ((val ,typep) (struct ,struct-tag-p))
             :returns (new-struct ,struct-tag-p)
             (value-struct-write (ident ,(ident->name name))
                                 (,type-fix val)
                                 (,struct-tag-fix struct))
             :hooks (:fix)))))
    (mv event
        struct-tag-read-name
        struct-tag-write-name
        reader-return-thm
        writer-return-thm)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defstruct-gen-array-member-ops ((struct-tag symbolp)
                                        (struct-tag-p symbolp)
                                        (struct-tag-fix symbolp)
                                        (name identp)
                                        (type typep)
                                        (size posp))
  :guard (type-integerp type)
  :returns (mv (event pseudo-event-formp)
               (checkers symbol-listp)
               (readers symbol-listp)
               (writers symbol-listp)
               (reader-return-thms symbol-listp)
               (writer-return-thms symbol-listp))
  :short "Generate the operations for an array member of
          the structures defined by @(tsee defstruct)."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is only for integer arrays.
     The @('type') parameter of this ACL2 function is
     the type of the elements of the array.")
   (xdoc::p
    "The readers and writers read and write elements of the array,
     not the whole array, unlike for integer members.
     However, these operations are internally defined as a combination of
     reading/writing the whole arrays and reading/writing their elements.")
   (xdoc::p
    "We generate local lemmas about
     the writing of the whole arrays
     yielding results of the expected types
     that in particular are not errors.
     In fact, the generated (readers and) writers never return errors.")
   (xdoc::p
    "Similarly to the operations on integer arrays in @(see atc-arrays),
     we generate 11 readers and 11 writers,
     which only differ in the type of the index,
     namely ACL2 integers or (10 types of) C integers;
     the latter are defined in terms of the former.")
   (xdoc::p
    "Besides readers and writers, we also generate 11 checkers,
     which check that the index is within the array bounds.
     These are used in the guards of the readers and writers,
     again analogously to the operations on integer arrays in @(see atc-arrays).
     One is for ACL2 integers, and the other 10 are for C integers,
     with again the latter defined in terms of the form.")
   (xdoc::p
    "The reason for generating the index checkers,
     as opposed to using the existing ones on integer arrays,
     is that, like for readers as explained above,
     we do not provide operations to read the whole array,
     but rather its elements.
     Thus, it makes sense that the checking functions are also provided here.
     Note that the definition of the checkers
     is in terms of the known length of the array member,
     and that guard verification for functions involving these structures
     is performed by opening the checkers."))
  (b* ((fixtype (integer-type-to-fixtype type))
       (arr-typep (pack fixtype '-arrayp))
       (arr-length (pack fixtype '-array-length))
       (arr-length-alt-def (pack arr-length '-alt-def))
       (arr-index-okp (pack fixtype '-array-index-okp))
       (arr-read (pack fixtype '-array-read))
       (arr-write (pack fixtype '-array-write))
       (elem-typep (pack fixtype 'p))
       (type-of-value-when-arr-typep (pack 'type-of-value-when- arr-typep))
       (index-okp (packn-pos (list struct-tag
                                   '-
                                   (ident->name name)
                                   '-index-okp)
                             struct-tag))
       (reader (packn-pos (list struct-tag
                                '-read-
                                (ident->name name))
                          struct-tag))
       (writer (packn-pos (list struct-tag
                                '-write-
                                (ident->name name))
                          struct-tag))
       (reader-return-thm (packn-pos (list elem-typep
                                           '-of-
                                           reader)
                                     reader))
       (writer-return-thm (packn-pos (list struct-tag-p
                                           '-of-
                                           writer)
                                     writer))
       (events
        `((define ,index-okp ((index integerp))
            :returns (yes/no booleanp)
            (integer-range-p 0 ,size (ifix index))
            :hooks (:fix))
          (define ,reader ((index integerp) (struct ,struct-tag-p))
            :guard (,index-okp index)
            :returns (val ,elem-typep)
            (b* ((array (value-struct-read (ident ,(ident->name name))
                                           (,struct-tag-fix struct))))
              (,arr-read array index))
            :guard-hints (("Goal" :in-theory (enable ,index-okp
                                                     ,arr-index-okp
                                                     ,arr-length
                                                     ,struct-tag-p
                                                     value-struct-read)))
            :hooks (:fix))
          (defruledl writer-lemma
            (implies (and (,struct-tag-p struct)
                          (,arr-typep array)
                          (equal (,arr-length array) ,size))
                     (,struct-tag-p (value-struct-write ',name array struct)))
            :enable (,struct-tag-p
                     value-struct-write
                     member-value-listp-of-value-struct-write-aux
                     member-value-list->name-list-of-struct-write-aux
                     value-struct-read-aux-of-value-struct-write-aux
                     ,arr-length-alt-def
                     not-errorp-when-member-value-listp
                     ,type-of-value-when-arr-typep))
          (define ,writer ((index integerp)
                           (val ,elem-typep)
                           (struct ,struct-tag-p))
            :guard (,index-okp index)
            :returns new-struct
            (b* ((array (value-struct-read (ident ,(ident->name name))
                                           (,struct-tag-fix struct)))
                 (new-array (,arr-write array index val)))
              (value-struct-write (ident ,(ident->name name))
                                  new-array
                                  (,struct-tag-fix struct)))
            :guard-hints (("Goal" :in-theory (enable ,index-okp
                                                     ,arr-length
                                                     ,arr-index-okp
                                                     ,struct-tag-p
                                                     value-struct-read)))
            :hooks (:fix)
            ///
            (defruledl return-lemma
              (implies (,struct-tag-p struct)
                       (,struct-tag-p (,writer index val struct)))
              :enable (,writer
                       writer-lemma)
              :prep-lemmas
              ((defrule lemma
                 (implies (,struct-tag-p struct)
                          (equal (,arr-length (value-struct-read ',name struct))
                                 ,size))
                 :enable (,struct-tag-p value-struct-read)
                 :rule-classes :forward-chaining)))
            (more-returns
             (new-struct ,struct-tag-p
                         :hints
                         (("Goal"
                           :use (:instance return-lemma
                                 (struct (,struct-tag-fix struct))))))))))
       ((mv more-events
            more-readers
            more-writers
            more-checkers
            more-reader-return-thms
            more-writer-return-thms)
        (defstruct-gen-array-member-ops-aux *integer-nonbool-nonchar-types*
          struct-tag struct-tag-p name elem-typep index-okp reader writer))
       (event `(encapsulate () ,@events ,@more-events)))
    (mv event
        (cons index-okp more-checkers)
        (cons reader more-readers)
        (cons writer more-writers)
        (cons reader-return-thm more-reader-return-thms)
        (cons writer-return-thm more-writer-return-thms)))

  :prepwork
  ((define defstruct-gen-array-member-ops-aux ((index-types type-listp)
                                               (struct-tag symbolp)
                                               (struct-tag-p symbolp)
                                               (name identp)
                                               (elem-typep symbolp)
                                               (index-okp symbolp)
                                               (reader symbolp)
                                               (writer symbolp))
     :guard (type-integer-listp index-types)
     :returns (mv (more-events pseudo-event-form-listp)
                  (more-readers symbol-listp)
                  (more-writers symbol-listp)
                  (more-checkers symbol-listp)
                  (more-reader-return-thms symbol-listp)
                  (more-writer-return-thms symbol-listp))
     :parents nil
     (b* (((when (endp index-types)) (mv nil nil nil nil nil nil))
          (index-type (car index-types))
          (index-fixtype (integer-type-to-fixtype index-type))
          (index-typep (pack index-fixtype 'p))
          (index-getter (pack index-fixtype '->get))
          (index-okp-for-index (packn-pos (list struct-tag
                                                '-
                                                (ident->name name)
                                                '-
                                                index-fixtype
                                                '-index-okp)
                                          struct-tag))
          (reader-for-index (packn-pos (list reader
                                             '-
                                             index-fixtype)
                                       struct-tag))
          (writer-for-index (packn-pos (list writer
                                             '-
                                             index-fixtype)
                                       struct-tag))
          (reader-return-thm (packn-pos (list elem-typep
                                              '-of-
                                              reader-for-index)
                                        reader-for-index))
          (writer-return-thm (packn-pos (list struct-tag-p
                                              '-of-
                                              writer-for-index)
                                        writer-for-index))
          (events
           `((define ,index-okp-for-index ((index ,index-typep))
               :returns (yes/no booleanp)
               (,index-okp (,index-getter index))
               :hooks (:fix))
             (define ,reader-for-index ((index ,index-typep)
                                        (struct ,struct-tag-p))
               :guard (,index-okp-for-index index)
               :returns (val ,elem-typep)
               (,reader (,index-getter index) struct)
               :guard-hints (("Goal" :in-theory (enable ,index-okp-for-index)))
               :hooks (:fix))
             (define ,writer-for-index ((index ,index-typep)
                                        (val ,elem-typep)
                                        (struct ,struct-tag-p))
               :guard (,index-okp-for-index index)
               :returns (new-struct ,struct-tag-p)
               (,writer (,index-getter index) val struct)
               :guard-hints (("Goal" :in-theory (enable ,index-okp-for-index)))
               :hooks (:fix))))
          ((mv more-events
               more-readers
               more-writers
               more-checkers
               more-reader-return-thms
               more-writer-return-thms)
           (defstruct-gen-array-member-ops-aux (cdr index-types)
             struct-tag struct-tag-p name elem-typep index-okp reader writer)))
       (mv (append events more-events)
           (cons reader-for-index more-readers)
           (cons writer-for-index more-writers)
           (cons index-okp-for-index more-checkers)
           (cons reader-return-thm more-reader-return-thms)
           (cons writer-return-thm more-writer-return-thms))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defstruct-gen-member-ops ((struct-tag symbolp)
                                  (struct-tag-p symbolp)
                                  (struct-tag-fix symbolp)
                                  (member member-typep))
  :returns (mv (event pseudo-event-formp)
               (info defstruct-member-infop))
  :short "Generate the operations for a member of
          the structures defined by the @(tsee defstruct)."
  :long
  (xdoc::topstring
   (xdoc::p
    "For now we only generate them for integer members,
     but we will extend this to integer array members."))
  (b* ((name (member-type->name member))
       (type (member-type->type member))
       ((when (type-integerp type))
        (b* (((mv event
                  reader
                  writer
                  reader-return-thm
                  writer-return-thm)
              (defstruct-gen-integer-member-ops
                struct-tag struct-tag-p struct-tag-fix name type))
             (info (make-defstruct-member-info
                    :memtype member
                    :readers (list reader)
                    :writers (list writer)
                    :checkers nil
                    :reader-return-thms (list reader-return-thm)
                    :writer-return-thms (list writer-return-thm))))
          (mv event info)))
       ((unless (type-case type :array))
        (raise "Internal error: member type ~x0." type)
        (mv '(_) (make-defstruct-member-info :memtype member)))
       (elem-type (type-array->of type))
       ((unless (type-integerp elem-type))
        (raise "Internal error: member type ~x0." type)
        (mv '(_) (make-defstruct-member-info :memtype member)))
       (size (type-array->size type))
       ((unless (posp size))
        (raise "Internal error: member type ~x0." type)
        (mv '(_) (make-defstruct-member-info :memtype member)))
       ((mv event
            checkers
            readers
            writers
            reader-return-thms
            writer-return-thms)
        (defstruct-gen-array-member-ops
          struct-tag struct-tag-p struct-tag-fix name elem-type size))
       (info (make-defstruct-member-info
              :memtype member
              :readers readers
              :writers writers
              :checkers checkers
              :reader-return-thms reader-return-thms
              :writer-return-thms writer-return-thms)))
    (mv event info)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defstruct-gen-all-member-ops ((struct-tag symbolp)
                                      (struct-tag-p symbolp)
                                      (struct-tag-fix symbolp)
                                      (members member-type-listp))
  :returns (mv (events pseudo-event-form-listp)
               (infos defstruct-member-info-listp))
  :short "Generate the operations for all the members of
          the structures defined by the @(tsee defstruct)."
  (b* (((when (endp members)) (mv nil nil))
       ((mv event info) (defstruct-gen-member-ops
                          struct-tag struct-tag-p struct-tag-fix
                          (car members)))
       ((mv events infos) (defstruct-gen-all-member-ops
                            struct-tag struct-tag-p struct-tag-fix
                            (cdr members))))
    (mv (cons event events)
        (cons info infos))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defstruct-gen-everything ((tag symbolp)
                                  (tag-ident identp)
                                  (members member-type-listp)
                                  (call pseudo-event-formp))
  :returns (event pseudo-event-formp)
  :short "Generate all the events."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are the recognizer, fixer, fixtype, member operations,
     and the table event."))
  (b* ((struct-tag (packn-pos (list 'struct- tag) tag))
       (struct-tag-p (packn-pos (list struct-tag '-p) tag))
       (struct-tag-fix (packn-pos (list struct-tag '-fix) tag))
       (struct-tag-equiv (packn-pos (list struct-tag '-equiv) tag))
       ((mv recognizer-event
            not-errorp-when-struct-tag-p
            valuep-when-struct-tag-p
            value-kind-when-struct-tag-p
            type-of-value-when-struct-tag-p)
        (defstruct-gen-recognizer struct-tag-p tag members))
       ((mv fixer-event
            fixer-recognizer-thm)
        (defstruct-gen-fixer struct-tag-fix struct-tag-p tag members))
       (fixtype-event (defstruct-gen-fixtype
                        struct-tag struct-tag-p
                        struct-tag-fix struct-tag-equiv))
       ((mv member-op-events member-infos)
        (defstruct-gen-all-member-ops
          struct-tag struct-tag-p struct-tag-fix members))
       (info (make-defstruct-info
              :tag tag-ident
              :members member-infos
              :recognizer struct-tag-p
              :fixer struct-tag-fix
              :fixer-recognizer-thm fixer-recognizer-thm
              :not-error-thm not-errorp-when-struct-tag-p
              :valuep-thm valuep-when-struct-tag-p
              :value-kind-thm value-kind-when-struct-tag-p
              :type-of-value-thm type-of-value-when-struct-tag-p
              :call call))
       (table-event (defstruct-table-record-event (symbol-name tag) info)))
    `(progn
       ,recognizer-event
       ,fixer-event
       ,fixtype-event
       ,@member-op-events
       ,table-event)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defstruct-fn ((args true-listp)
                      (call pseudo-event-formp)
                      (ctx ctxp)
                      state)
  :returns (mv erp (event pseudo-event-formp) state)
  :short "Process the inputs and generate the events."
  (b* (((mv erp (list tag tag-ident members redundant) state)
        (defstruct-process-inputs args call ctx state))
       ((when erp) (mv erp '(_) state))
       ((when redundant) (acl2::value '(value-triple :redundant)))
       (event (defstruct-gen-everything tag tag-ident members call)))
    (acl2::value event)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro+ defstruct (&whole call &rest args)
  :short "Define a shallowly embedded C structure."
  :long
  (xdoc::topstring
   (xdoc::p
    "See @(see shallow-structures)."))
  `(make-event (defstruct-fn ',args ',call 'defstruct state)))
