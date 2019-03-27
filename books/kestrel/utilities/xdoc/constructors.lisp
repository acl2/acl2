; XDOC Utilities -- Constructors
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

; Only the following book should be non-locally included here,
; to minimize footprint and dependencies of this XDOC constructor library.
(include-book "xdoc/top" :dir :system)

; The books locally included here should be minimized, for the above reason.
; The flag book is used to prove the return type theorems of
; XDOC::TREE-TO-STRING and mutually recursive companions.
(local (include-book "tools/flag" :dir :system))

; Always verify guards, even if no :GUARD ... is provided.
(set-verify-guards-eagerness 2)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc xdoc::constructors
  :parents (xdoc-utilities)
  :short "Utilities to costruct
          well-formed <see topic='@(url xdoc)'>XDOC</see> strings."
  :long
  "<p>
   XDOC strings use <see topic='@(url xdoc::markup)'>XML tags</see>,
   which must be properly matched and nested.
   They also use
   <see topic='@(url xdoc::preprocessor)'>preprocessor directives</see>,
   which can be regarded as ``tag''-like constructs
   that must also be properly matched and nested.
   </p>
   <p>
   Starting with @(tsee stringp) values as the basic building blocks,
   the XDOC constructors provided here build trees that correspond to
   the combined structure of XML tags and preprocessor directives;
   these trees are recognized by the predicate @(tsee xdoc::treep).
   These trees also accommodate attributes of XML tags,
   whose values are subtrees, recursively.
   The function @(tsee xdoc::topstring) turns these trees into strings,
   by recursively turning subtrees into strings,
   joining those strings,
   and adding XML tags and preprocessor directives at the roots of the trees.
   </p>
   <p>
   With these XDOC constructors, one can write
   </p>
   @({
     (xdoc::topstring
       (xdoc::p \"A paragraph.\")
       (xdoc::ul
         (xdoc::li \"One.\")
         (xdoc::li \"Two.\")
         (xdoc::li \"Three.\"))
       (xdoc::p \"Another paragraph.\"))
   })
   <p>
   instead of
   </p>
   @({
     \"<p>A paragraph.</p>
      <ul>
        <li>One.</li>
        <li>Two.</li>
        <li>Three.</li>
      </ul>
      <p>Another paragraph.</p>\"
   })
   <p>
   The main advantage is that the XML tags (and preprocessor directives)
   will be always properly matched and nested by construction.
   Furthermore, using XDOC constructors
   is probably more readable,
   facilitates the modular and hierarchical construction of XDOC strings
   (in particular, see the
   <see topic='@(url xdoc::composite-constructors)'
   >composite XDOC constructors</see>),
   and allows the insertion of comments within the XDOC constructor forms
   (e.g. lines of semicolons to visually separate sections).
   </p>
   <p>
   The strings at the leaves of a tree
   may well contain XML tags or preprocessor directives.
   For relatively short XML-tagged text or preprocessor directives,
   it may be better to use tags and directives within a string
   rather than the corresponding XDOC constructors,
   e.g. @('(xdoc::p \"This is in <i>italics</i>.\")')
   rather than @('(xdoc::p \"This is in \" (xdoc::i \"italics\") \".\")').
   In other words, it is not necessary to use XDOC constructors for everything,
   but only where they are convenient.
   </p>
   <p>
   The books included by these XDOC constructor utilities should be minimized,
   to keep these utilities lightweight and more widely usable.
   </p>")

(xdoc::order-subtopics xdoc::constructors nil t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc xdoc::constructor-preliminaries
  :parents (xdoc::constructors)
  :short "Some preliminary utilities used by the XDOC constructors."
  :long
  "<p>
   These are independent from the XDOC constructors,
   but we introduce them here
   to keep the XDOC constructor utilities self-contained.
   </p>")

(xdoc::order-subtopics xdoc::constructor-preliminaries nil t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection xdoc::*newline*
  :parents (xdoc::constructor-preliminaries)
  :short "The string consisting of exactly the newline character."
  :long "@(def xdoc::*newline*)"

  (defconst xdoc::*newline*
    (coerce (list #\Newline) 'string))

  (assert-event (stringp xdoc::*newline*)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection xdoc::string-downcase$
  :parents (xdoc::constructor-preliminaries)
  :short "A variant of @(tsee string-downcase) applicable to any string."
  :long
  "<p>
   The built-in @(tsee string-downcase) has a guard requiring
   all the characters in the string to be
   <see topic='@(url standard-char-p)'>standard</see>.
   This function ``totalizes'' @(tsee string-downcase) to all strings
   by checking whether all the characters in the string are standard,
   and by throwing a hard error if any of them is not.
   </p>
   <p>
   This facilitates guard verification of code involving this function.
   The hard error seems appropriate for the envisioned usage of this function
   within the XDOC constructors,
   meant to be called to produce XDOC strings during book certification.
   </p>"

  (defund xdoc::string-downcase$ (string)
    (declare (xargs :guard (stringp string)))
    (if (standard-char-listp (coerce string 'list))
        (string-downcase string)
      (prog2$ (er hard? 'xdoc::string-downcase$
                  "Attempt to downcase non-standard string ~x0." string)
              "")))

  (defthm xdoc::stringp-of-string-downcase$
    (stringp (xdoc::string-downcase$ string))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection xdoc::string-escape
  :parents (xdoc::constructor-preliminaries)
  :short "Escape certain characters in a string, using backslashes."
  :long
  "<p>
   We escape each single quote and backquote character
   that occurs in the string.
   </p>
   <p>
   This is used in @(tsee xdoc::generate-primitive-constructor-for-dir/&&),
   since some of the macros generated by that macro have names
   that include the characters escaped by this function.
   These characters would cause XDOC errors if not escaped.
   </p>"

  (defund xdoc::chars-escape (chars)
    (declare (xargs :guard (character-listp chars)))
    (cond ((endp chars) nil)
          (t (if (member (car chars) '(#\' #\`))
                 (list* #\\ #\' (xdoc::chars-escape (cdr chars)))
               (cons (car chars) (xdoc::chars-escape (cdr chars)))))))

  (defthm xdoc::character-listp-of-chars-escape
    (implies (character-listp chars)
             (character-listp (xdoc::chars-escape chars)))
    :hints (("Goal" :in-theory (enable xdoc::chars-escape))))

  (defund xdoc::string-escape (string)
    (declare (xargs :guard (stringp string)))
    (let* ((chars (coerce string 'list))
           (chars (xdoc::chars-escape chars))
           (string (coerce chars 'string)))
      string))

  (defthm xdoc::stringp-of-string-escape
    (stringp (xdoc::string-escape string))
    :hints (("Goal" :in-theory (enable xdoc::string-escape)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection xdoc::partition-macro-args
  :parents (xdoc::constructor-preliminaries)
  :short "Partition the arguments of a macro into a list and an alist."
  :long
  "<p>
   The XDOC constructors are macros.
   Some of them take a varying number of ``regular'' arguments
   and a varying number of keyword arguments,
   but the keywords are not predefined
   and the two kinds of arguments may be intermixed.
   </p>
   <p>
   This function partitions these intermixed arguments into
   a list of regular arguments and an alist of keyword arguments.
   Each keyword encountered in the input list
   is regarded as starting a keyword argument
   (unless it follows one already);
   if a keyword is not followed by a value,
   it is an error.
   This function does not check for duplicate keywords.
   The output list and alists are in the same order as in the input.
   </p>"

  (defund xdoc::partition-macro-args (args ctx)
    (declare (xargs :guard (true-listp args)))
    (cond ((endp args) (mv nil nil))
          ((keywordp (car args))
           (if (consp (cdr args))
               (mv-let (rest-list rest-alist)
                 (xdoc::partition-macro-args (cddr args) ctx)
                 (mv rest-list (acons (car args) (cadr args) rest-alist)))
             (prog2$ (er hard? ctx "Missing value for keyword ~x0." (car args))
                     (mv nil nil))))
          (t (mv-let (rest-list rest-alist)
               (xdoc::partition-macro-args (cdr args) ctx)
               (mv (cons (car args) rest-list) rest-alist)))))

  (defthm xdoc::true-listp-of-mv-nth-0-partition-macro-args
    (true-listp (mv-nth 0 (xdoc::partition-macro-args args ctx)))
    :hints (("Goal" :in-theory (enable xdoc::partition-macro-args))))

  (defthm xdoc::true-listp-of-mv-nth-1-partition-macro-args
    (alistp (mv-nth 1 (xdoc::partition-macro-args args ctx)))
    :hints (("Goal" :in-theory (enable xdoc::partition-macro-args)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection xdoc::keyword-macro-args-to-terms
  :parents (xdoc::constructor-preliminaries)
  :short "Turn the keyword arguments of a macro into terms."
  :long
  "<p>
   This complements @(tsee xdoc::partition-macro-args),
   which extracts a list of regular arguments
   and an alist of keyword arguments.
   This alist has keys that are keyword
   but values that, in general, are terms that need to be evaluated
   to obtain the actual values of the keyword arguments;
   the terms are the ones supplied by the caller of the macro.
   This function turns that alist into
   a list of terms that, when put inside a @(tsee list),
   construct the alist with evaluated values:
   each term, when evaluated, returns a @(tsee cons) pair.
   </p>"

  (defund xdoc::keyword-macro-args-to-terms (alist)
    (declare (xargs :guard (alistp alist)))
    (cond ((endp alist) nil)
          (t (cons `(cons ,(caar alist)
                          ,(cdar alist))
                   (xdoc::keyword-macro-args-to-terms (cdr alist))))))

  (defthm xdoc::true-listp-of-keyword-macro-args-to-terms
    (true-listp (xdoc::keyword-macro-args-to-terms alist))
    :hints (("Goal" :in-theory (enable xdoc::keyword-macro-args-to-terms)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc xdoc::trees
  :parents (xdoc::constructors)
  :short "XDOC trees.")

(xdoc::order-subtopics xdoc::trees nil t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection xdoc::treep
  :parents (xdoc::trees)
  :short "Recognize XDOC trees."
  :long
  "<p>
   These are the trees produced by the XDOC constructors.
   </p>
   <p>
   These trees have strings at the leaves.
   A non-leaf node consists of one of the following:
   </p>
   <ul>
     <li>
     A single keyword.
     This represents either
     (i) a preprocessor directive
     or (ii) a concatenation of subtrees
     without a surrounding XML tag or preprocessor directive.
     Examples of (i) are @(':@def') and @(':@{}').
     The keyword @(':&&') is used for (ii).
     The latter is useful to treat sequences of trees as single trees.
     </li>
     <li>
     A @(tsee cons) pair
     whose @(tsee car) is a keyword and
     whose @(tsee cdr) is an alist from keywords to subtrees.
     This represents an XML tag, identified by the keyword at the @(tsee car),
     with the attributes represented by the alist at the @(tsee cdr).
     Examples are @('(:p)') and @('(:img (:src ...))').
     The alist may often be @('nil').
     The values of the attributes are recursively represented as subtrees,
     but there may often be a single string subtree per attribute.
     </li>
   </ul>
   <p>
   In some sense,
   the semantics of XDOC trees is defined by their conversion to flat strings.
   See @(tsee xdoc::tree-to-string).
   </p>"

  ;; functions:

  (mutual-recursion

   (defund xdoc::treep (x)
     (or (stringp x)
         (and (true-listp x)
              (consp x)
              (or (keywordp (car x))
                  (xdoc::tree-tagp (car x)))
              (xdoc::tree-listp (cdr x)))))

   (defund xdoc::tree-listp (x)
     (cond ((atom x) (eq x nil))
           (t (and (xdoc::treep (car x))
                   (xdoc::tree-listp (cdr x))))))

   (defund xdoc::tree-tagp (x)
     (and (consp x)
          (keywordp (car x))
          (xdoc::keyword-tree-alistp (cdr x))))

   (defund xdoc::keyword-tree-alistp (x)
     (cond ((atom x) (eq x nil))
           (t (and (consp (car x))
                   (keywordp (car (car x)))
                   (xdoc::treep (cdr (car x)))
                   (xdoc::keyword-tree-alistp (cdr x)))))))

  ;; theorems:

  (defthm xdoc::treep-when-stringp
    (implies (stringp x)
             (xdoc::treep x))
    :hints (("Goal" :in-theory (enable xdoc::treep))))

  (defthm xdoc::tree-listp-when-string-listp
    (implies (string-listp x)
             (xdoc::tree-listp x))
    :hints (("Goal" :in-theory (enable xdoc::tree-listp))))

  (defthm xdoc::true-listp-when-tree-listp
    (implies (xdoc::tree-listp x)
             (true-listp x))
    :rule-classes :forward-chaining
    :hints (("Goal" :in-theory (enable xdoc::tree-listp))))

  (defthm xdoc::treep-of-cons
    (equal (xdoc::treep (cons x y))
           (and (or (keywordp x)
                    (xdoc::tree-tagp x))
                (xdoc::tree-listp y)))
    :hints (("Goal" :in-theory (enable xdoc::treep))))

  (defthm xdoc::tree-listp-of-cons
    (equal (xdoc::tree-listp (cons x y))
           (and (xdoc::treep x)
                (xdoc::tree-listp y)))
    :hints (("Goal" :in-theory (enable xdoc::tree-listp))))

  (defthm xdoc::tagp-of-cons
    (equal (xdoc::tree-tagp (cons x y))
           (and (keywordp x)
                (xdoc::keyword-tree-alistp y)))
    :hints (("Goal" :in-theory (enable xdoc::tree-tagp))))

  (defthm xdoc::keyword-tree-alistp-of-cons
    (equal (xdoc::keyword-tree-alistp (cons x y))
           (and (consp x)
                (keywordp (car x))
                (xdoc::treep (cdr x))
                (xdoc::keyword-tree-alistp y)))
    :hints (("Goal" :in-theory (enable xdoc::keyword-tree-alistp)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection xdoc::tree-to-string
  :parents (xdoc::trees)
  :short "Turn a XDOC tree into the string it represents."
  :long
  "<p>
   An XDOC tree is turned into a string as follows.
   A leaf tree is already a string and is left unchanged.
   For a non-leaf tree, the subtrees are recursively turned into strings
   and concatenated;
   then the resulting string is surrounded by text
   determined by the root of the non-leaf tree.
   If the root represents a tree concatenation,
   no surrounding text is actually added.
   If the root represents a preprocessor directive,
   the surrounding text @('\"@(...)\"') creates the directive.
   If the root represents an XML tag,
   surrounding text @('\"<tag ... attribute=\\\"value\\\" ...>...</tag>\"')
   creates the XML tag;
   the values of the tag's attributes (if present)
   are obtained by recursively turning the subtrees in the alist into strings.
   </p>
   <p>
   As noted <see topic='@(url str::concatenation)'>here</see>,
   string concatenation is slow in ACL2 in general.
   The current implementation of this function
   uses straighforward string concatenation,
   but this could be optimized in the future,
   if concatenating strings turns out to be too slow
   in the actual usage of these XDOC constructors.
   </p>
   <p>
   Note that the @(tsee symbol-name) of a keyword tag
   consists of uppercase letters.
   We use @(tsee xdoc::string-downcase$)
   to produce lowercase tags and directives.
   We expect that this function will never throw an error
   with the tags and directives supported.
   </p>"

  ;; functions:

  (mutual-recursion

   (defund xdoc::tree-to-string (tree)
     (declare (xargs :guard (xdoc::treep tree)
                     :verify-guards nil)) ; done below
     (cond ((atom tree) tree)
           (t (let ((subtrees-string (xdoc::tree-list-to-string (cdr tree))))
                (mv-let (left-string right-string)
                  (xdoc::keyword-or-tree-tag-to-strings (car tree))
                  (concatenate 'string
                               left-string subtrees-string right-string))))))

   (defund xdoc::tree-list-to-string (trees)
     (declare (xargs :guard (xdoc::tree-listp trees)))
     (cond ((endp trees) "")
           (t (concatenate 'string
                           (xdoc::tree-to-string (car trees))
                           (xdoc::tree-list-to-string (cdr trees))))))

   (defund xdoc::keyword-or-tree-tag-to-strings (keyword/tag)
     (declare (xargs :guard (or (keywordp keyword/tag)
                                (xdoc::tree-tagp keyword/tag))))
     (cond ((eq keyword/tag :&&) (mv "" ""))
           ((member-eq keyword/tag '(:@\'\' :@{} :@\`\` :@$$ :@[]))
            (let* ((left-char (char (symbol-name keyword/tag) 1))
                   (right-char (char (symbol-name keyword/tag) 2))
                   (left-chars (list #\@ #\( left-char))
                   (right-chars (list right-char #\)))
                   (left-string (coerce left-chars 'string))
                   (right-string (coerce right-chars 'string)))
              (mv left-string right-string)))
           ((atom keyword/tag)
            (let ((keyword-chars (coerce (symbol-name keyword/tag) 'list)))
              (if (and (consp keyword-chars)
                       (eql (car keyword-chars) #\@))
                  (let* ((keyword-string (coerce (cdr keyword-chars) 'string))
                         (keyword-string (xdoc::string-downcase$
                                          keyword-string))
                         (left-string (concatenate 'string
                                                   "@(" keyword-string " "))
                         (right-string ")"))
                    (mv left-string right-string))
                (prog2$ (er hard?
                            'xdoc::tree-to-string
                            "Cannot process XDOC tree with root ~x0."
                            keyword/tag)
                        (mv "" "")))))
           (t (let* ((keyword (car keyword/tag))
                     (keyword-chars (coerce (symbol-name keyword) 'list))
                     (keyword-string (coerce keyword-chars 'string))
                     (keyword-string (xdoc::string-downcase$ keyword-string))
                     (attributes (cdr keyword/tag))
                     (attributes-string (xdoc::keyword-tree-alist-to-string
                                         attributes))
                     (left-string (concatenate 'string
                                               "<"
                                               keyword-string
                                               attributes-string
                                               ">"))
                     (right-string (concatenate 'string
                                                "</"
                                                keyword-string
                                                ">")))
                (mv left-string right-string)))))

   (defund xdoc::keyword-tree-alist-to-string (attributes)
     (declare (xargs :guard (xdoc::keyword-tree-alistp attributes)))
     (cond ((endp attributes) "")
           (t (let* ((attribute (car attributes))
                     (keyword (car attribute))
                     (tree (cdr attribute))
                     (keyword-chars (coerce (symbol-name keyword) 'list))
                     (keyword-string (coerce keyword-chars 'string))
                     (keyword-string (xdoc::string-downcase$ keyword-string))
                     (tree-string (xdoc::tree-to-string tree))
                     (attribute-string (concatenate 'string
                                                    " "
                                                    keyword-string
                                                    "=\""
                                                    tree-string
                                                    "\""))
                     (rest-attributes (cdr attributes))
                     (rest-attribute-string (xdoc::keyword-tree-alist-to-string
                                             rest-attributes)))
                (concatenate 'string
                             attribute-string
                             rest-attribute-string))))))

  ;; theorems:

  (local (make-flag flag-xdoc-tree-to-string xdoc::tree-to-string))

  (local
   (defthm-flag-xdoc-tree-to-string
     (defthm xdoc::theorem-for-tree-to-string
       (implies (xdoc::treep tree)
                (stringp (xdoc::tree-to-string tree)))
       :flag xdoc::tree-to-string)
     (defthm xdoc::theorem-for-tree-list-to-string
       (implies (xdoc::tree-listp trees)
                (stringp (xdoc::tree-list-to-string trees)))
       :flag xdoc::tree-list-to-string)
     (defthm xdoc::theorem-for-keyword-or-tree-tag-to-strings
       (implies (or (keywordp keyword/tag)
                    (xdoc::tree-tagp keyword/tag))
                (and (stringp (mv-nth 0 (xdoc::keyword-or-tree-tag-to-strings
                                         keyword/tag)))
                     (stringp (mv-nth 1 (xdoc::keyword-or-tree-tag-to-strings
                                         keyword/tag)))))
       :flag xdoc::keyword-or-tree-tag-to-strings)
     (defthm xdoc::theorem-for-keyword-tree-alist-to-string
       (implies (xdoc::keyword-tree-alistp attributes)
                (stringp (xdoc::keyword-tree-alist-to-string attributes)))
       :flag xdoc::keyword-tree-alist-to-string)
     :hints (("Goal" :in-theory (enable xdoc::tree-to-string
                                        xdoc::tree-list-to-string
                                        xdoc::keyword-or-tree-tag-to-strings
                                        xdoc::keyword-tree-alist-to-string
                                        xdoc::treep)))))

  (defthm xdoc::stringp-of-tree-to-string
    (implies (xdoc::treep tree)
             (stringp (xdoc::tree-to-string tree))))

  (defthm xdoc::stringp-of-tree-list-to-string
    (implies (xdoc::tree-listp trees)
             (stringp (xdoc::tree-list-to-string trees))))

  (defthm xdoc::stringp-of-mv-nth-0-keyword-or-tree-tag-to-strings
    (implies (or (keywordp keyword/tag)
                 (xdoc::tree-tagp keyword/tag))
             (stringp (mv-nth 0 (xdoc::keyword-or-tree-tag-to-strings
                                 keyword/tag))))
    :hints (("Goal" :in-theory (disable mv-nth))))

  (defthm xdoc::stringp-of-mv-nth-1-keyword-or-tree-tag-to-strings
    (implies (or (keywordp keyword/tag)
                 (xdoc::tree-tagp keyword/tag))
             (stringp (mv-nth 1 (xdoc::keyword-or-tree-tag-to-strings
                                 keyword/tag))))
    :hints (("Goal" :in-theory (disable mv-nth))))

  (defthm xdoc::stringp-of-keyword-tree-alist-to-string
    (implies (xdoc::keyword-tree-alistp attributes)
             (stringp (xdoc::keyword-tree-alist-to-string attributes))))

  ;; guard verification:

  (local
   (defthm xdoc::tree-to-string-verify-guards-lemma
     (implies (character-listp x)
              (character-listp (cdr x)))))

  (verify-guards xdoc::tree-to-string
    :hints (("Goal" :in-theory (e/d (xdoc::tree-tagp xdoc::keyword-tree-alistp)
                                    (mv-nth))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection xdoc::make-tree-tag
  :parents (xdoc::trees)
  :short "Construct a non-leaf XDOC tree with an XML tag at the root."
  :long
  "<p>
   This is for internal use of the XDOC constructor library.
   Users of this library should use
   constructors for specific tags, e.g. @(tsee xdoc::p).
   </p>
   <p>
   See also @(tsee xdoc::make-tree-dir/&&).
   </p>"

  (defund xdoc::make-tree-tag (tag attributes trees)
    (declare (xargs :guard (and (keywordp tag)
                                (xdoc::keyword-tree-alistp attributes)
                                (xdoc::tree-listp trees))))
    (cons (cons tag attributes) trees))

  (defthm xdoc::treep-of-make-tree-tag
    (equal (xdoc::treep (xdoc::make-tree-tag tag attributes trees))
           (and (keywordp tag)
                (xdoc::keyword-tree-alistp attributes)
                (xdoc::tree-listp trees)))
    :hints (("Goal" :in-theory (enable xdoc::make-tree-tag)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection xdoc::make-tree-dir/&&
  :parents (xdoc::trees)
  :short "Construct a non-leaf XDOC tree
          with a preprocessor directive or a tree concatenation at the root."
  :long
  "<p>
   This is for internal use of the XDOC constructor library.
   Users of this library should use
   the constructor @(tsee xdoc::&&) for concatenation
   or constructors for specific directives, e.g. @(tsee xdoc::@def).
   </p>
   <p>
   See also @(tsee xdoc::make-tree-tag).
   </p>"

  (defund xdoc::make-tree-dir/&& (dir/&& trees)
    (declare (xargs :guard (and (keywordp dir/&&)
                                (xdoc::tree-listp trees))))
    (cons dir/&& trees))

  (defthm xdoc::treep-of-make-tree-dir/&&
    (implies (keywordp dir/&&)
             (equal (xdoc::treep (xdoc::make-tree-dir/&& dir/&& trees))
                    (xdoc::tree-listp trees)))
    :hints (("Goal" :in-theory (enable xdoc::make-tree-dir/&&)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc xdoc::primitive-constructors
  :parents (xdoc::constructors)
  :short "Primitive XDOC constructors."
  :long
  "<p>
   These correspond to
   individual XML tags,
   individual preprocessor directives,
   and tree concatenation.
   In contrast, the
   <see topic='@(url xdoc::composite-constructors)'
   >composite XDOC constructors</see>
   correspond to multiple tags, directives, and concatenations.
   </p>
   <p>
   Since the primitive constructors have a very uniform structure,
   we introduce them via two event-generating macros,
   one for XML tags
   and one for preprocessor directives and tree concatenation.
   </p>")

(xdoc::order-subtopics xdoc::primitive-constructors nil t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection xdoc::generate-primitive-constructor-for-tag
  :parents (xdoc::primitive-constructors)
  :short "Generate a primitive constructor for an XML tag."
  :long
  "<p>
   The arguments are a keyword for the tag (e.g. @(':p') for paragraphs)
   and a documentation string that describes the primitive constructor.
   This documentation string is used as the @(':short') string
   of the XDOC topic generated for the primitive constructor itself.
   </p>
   <p>
   The generated XDOC constructor consists of a macro that calls a function
   (also generated),
   as often done with macros.
   We also generate a theorem about the return type of the constructor.
   </p>
   <p>
   The generated macro accepts regular and keyword arguments in any order:
   the former are subtrees for the content between the XML tags;
   the latter are attributes of the XML tag.
   The macro uses @(tsee xdoc::partition-macro-args) to divide them.
   </p>
   <p>
   See also @(tsee xdoc::generate-primitive-constructor-for-dir/&&).
   </p>
   @(def xdoc::generate-primitive-constructor-for-tag)"

  (defund xdoc::generate-primitive-constructor-for-tag-fn (tag doc)
    (declare (xargs :guard (and (keywordp tag) (stringp doc))))
    (let* ((macro-name (add-suffix-to-fn 'xdoc::|| (symbol-name tag)))
           (fn-name (add-suffix-to-fn macro-name "-FN"))
           (thm-name (packn (list 'xdoc::stringp-of- macro-name))))
      `(defsection ,macro-name
         :parents (xdoc::primitive-constructors)
         :short ,doc
         :long ,(concatenate 'string
                             "@(def xdoc::"
                             (xdoc::string-downcase$ (symbol-name macro-name))
                             ").")
         (defund ,fn-name (attributes trees)
           (declare (xargs :guard (and (xdoc::keyword-tree-alistp attributes)
                                       (xdoc::tree-listp trees))))
           (xdoc::make-tree-tag ,tag attributes trees))
         (defthm ,thm-name
           (equal (xdoc::treep (,fn-name attributes trees))
                  (and (xdoc::keyword-tree-alistp attributes)
                       (xdoc::tree-listp trees)))
           :hints (("Goal" :in-theory (enable ,fn-name))))
         (defmacro ,macro-name (&rest args)
           (mv-let (trees attributes)
             (xdoc::partition-macro-args args ',macro-name)
             (let ((attributes (xdoc::keyword-macro-args-to-terms attributes)))
               (list ',fn-name
                     (cons 'list attributes)
                     (cons 'list trees))))))))

  (defmacro xdoc::generate-primitive-constructor-for-tag (tag doc)
    `(make-event (xdoc::generate-primitive-constructor-for-tag-fn ,tag ,doc))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection xdoc::generate-primitive-constructor-for-dir/&&
  :parents (xdoc::primitive-constructors)
  :short "Generate a primitive constructor for
          a preprocessor directive or tree concatenation."
  :long
  "<p>
   The arguments are
   a keyword for the directive (e.g. @(':@def') for definitions)
   or for tree concatenation (i.e. @(':&&')),
   and a documentation string that describes the primitive constructor.
   This documentation string is used as the @(':short') string
   of the XDOC topic generated for the primitive constructor itself.
   </p>
   <p>
   The generated XDOC constructor consists of a macro that calls a function
   (also generated),
   as often done with macros.
   We also generate a theorem about the return type of the constructor.
   </p>
   <p>
   See also @(tsee xdoc::generate-primitive-constructor-for-tag).
   </p>
   @(def xdoc::generate-primitive-constructor-for-dir/&&)"

  (defund xdoc::generate-primitive-constructor-for-dir/&&-fn (dir/&& doc)
    (declare (xargs :guard (and (keywordp dir/&&) (stringp doc))))
    (let* ((macro-name (add-suffix-to-fn 'xdoc::|| (symbol-name dir/&&)))
           (fn-name (add-suffix-to-fn macro-name "-FN"))
           (thm-name (packn (list 'xdoc::stringp-of- macro-name))))
      `(defsection ,macro-name
         :parents (xdoc::primitive-constructors)
         :short ,doc
         :long ,(concatenate 'string
                             "@(def xdoc::"
                             (xdoc::string-escape
                              (xdoc::string-downcase$
                               (symbol-name macro-name)))
                             ").")
         (defund ,fn-name (trees)
           (declare (xargs :guard (xdoc::tree-listp trees)))
           (xdoc::make-tree-dir/&& ,dir/&& trees))
         (defthm ,thm-name
           (equal (xdoc::treep (,fn-name trees))
                  (xdoc::tree-listp trees))
           :hints (("Goal" :in-theory (enable ,fn-name))))
         (defmacro ,macro-name (&rest trees)
           (list ',fn-name (cons 'list trees))))))

  (defmacro xdoc::generate-primitive-constructor-for-dir/&& (dir/&& doc)
    `(make-event
      (xdoc::generate-primitive-constructor-for-dir/&&-fn ,dir/&& ,doc))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; primitive XDOC constructors for XML tags:

(xdoc::generate-primitive-constructor-for-tag :h1
  "Construct an XDOC tree for an HTML level-1 heading @('<h1>...</h1>').")

(xdoc::generate-primitive-constructor-for-tag :h2
  "Construct an XDOC tree for an HTML level-2 heading @('<h2>...</h2>').")

(xdoc::generate-primitive-constructor-for-tag :h3
  "Construct an XDOC tree for an HTML level-3 heading @('<h3>...</h3>').")

(xdoc::generate-primitive-constructor-for-tag :h4
  "Construct an XDOC tree for an HTML level-4 heading @('<h4>...</h4>').")

(xdoc::generate-primitive-constructor-for-tag :h5
  "Construct an XDOC tree for an HTML level-5 heading @('<h5>...</h5>').")

(xdoc::generate-primitive-constructor-for-tag :p
  "Construct an XDOC tree for an HTML paragraph @('<p>...</p>').")

(xdoc::generate-primitive-constructor-for-tag :blockquote
  "Construct an XDOC tree for
   an HTML quoted block @('<blockquote>...</blockquote>').")

(xdoc::generate-primitive-constructor-for-tag :li
  "Construct an XDOC tree for an HTML list item @('<li>...</li>').")

(xdoc::generate-primitive-constructor-for-tag :ul
  "Construct an XDOC tree for an HTML unordered list @('<ul>...</ul>').")

(xdoc::generate-primitive-constructor-for-tag :ol
  "Construct an XDOC tree for an HTML unordered list @('<ol>...</ol>').")

(xdoc::generate-primitive-constructor-for-tag :dt
  "Construct an XDOC tree for an HTML term @('<dt>...</dt>').")

(xdoc::generate-primitive-constructor-for-tag :dd
  "Construct an XDOC tree for an HTML description @('<dd>...</dd>').")

(xdoc::generate-primitive-constructor-for-tag :dl
  "Construct an XDOC tree for an HTML description list @('<dl>...</dl>').")

(xdoc::generate-primitive-constructor-for-tag :th
  "Construct an XDOC tree for an HTML table header cell @('<th>...</th>').")

(xdoc::generate-primitive-constructor-for-tag :td
  "Construct an XDOC tree for an HTML table cell @('<td>...</td>').")

(xdoc::generate-primitive-constructor-for-tag :tr
  "Construct an XDOC tree for an HTML table row @('<tr>...</tr>').")

(xdoc::generate-primitive-constructor-for-tag :table_
  ;; :TABLE would cause a conflict with the built-in TABLE
  "Construct an XDOC tree for an HTML table @('<table>...</table>').")

(xdoc::generate-primitive-constructor-for-tag :box
  "Construct an XDOC tree for an XDOC box @('<box>...</box>').")

(xdoc::generate-primitive-constructor-for-tag :br
  "Construct an XDOC tree for an HTML line break @('<br>...</br>').")

(xdoc::generate-primitive-constructor-for-tag :img
  "Construct an XDOC tree for an HTML image @('<img>...</img>').")

(xdoc::generate-primitive-constructor-for-tag :b
  "Construct an XDOC tree for HTML bold text @('<b>...</b>').")

(xdoc::generate-primitive-constructor-for-tag :i
  "Construct an XDOC tree for HTML italic text @('<i>...</i>').")

(xdoc::generate-primitive-constructor-for-tag :u_
  ;; :U would cause a conflict with the built-in U
  "Construct an XDOC tree for HTML underlined text @('<u>...</u>').")

(xdoc::generate-primitive-constructor-for-tag :color
  "Construct an XDOC tree for HTML colored text @('<color>...</color>').")

(xdoc::generate-primitive-constructor-for-tag :sf
  "Construct an XDOC tree for HTML sans-serif text @('<sf>...</sf>').")

(xdoc::generate-primitive-constructor-for-tag :tt
  "Construct an XDOC tree for XDOC inline code @('<tt>...</tt>')
   (which is not rendered using the homonymous HTML tags;
   see @(see xdoc::markup)).")

(xdoc::generate-primitive-constructor-for-tag :code
  "Construct an XDOC tree for XDOC code block @('<code>...</code>')
   (which is not rendered using the homonymous HTML tags;
   see @(see xdoc::markup)).")

(xdoc::generate-primitive-constructor-for-tag :a
  "Construct an XDOC tree for an HTML hyperlink @('<a>...</a>').")

(xdoc::generate-primitive-constructor-for-tag :see_
  ;; :SEE would cause a conflict with XDOC::SEE in [books]/xdoc/names.lisp
  "Construct an XDOC tree for an XDOC hyperlink @('<see>...</see>').")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; primitive XDOC constructors for preprocessor directives and for concatenation:

(xdoc::generate-primitive-constructor-for-dir/&& :&&
  "Construct an XDOC tree for a concatenation.")

(xdoc::generate-primitive-constructor-for-dir/&& :@\'\'
  "Construct an XDOC tree for a inline code directive @('@(\'...\')').")

(xdoc::generate-primitive-constructor-for-dir/&& :@{}
  "Construct an XDOC tree for a code block directive @('@({...})').")

(xdoc::generate-primitive-constructor-for-dir/&& :@\`\`
  "Construct an XDOC tree for an evaluation directive @('@(\`...\`)').")

(xdoc::generate-primitive-constructor-for-dir/&& :@$$
  "Construct an XDOC tree for a short KaTeK directive @('@($...$)').")

(xdoc::generate-primitive-constructor-for-dir/&& :@[]
  "Construct an XDOC tree for a long KaTeK directive @('@([...])').")

(xdoc::generate-primitive-constructor-for-dir/&& :@def
  "Construct an XDOC tree for a definition directive @('@(def ...)').")

(xdoc::generate-primitive-constructor-for-dir/&& :@gdef
  "Construct an XDOC tree
   for a generated definition directive @('@(gdef ...)').")

(xdoc::generate-primitive-constructor-for-dir/&& :@formals
  "Construct an XDOC tree for a formals directive @('@(formals ...)').")

(xdoc::generate-primitive-constructor-for-dir/&& :@body
  "Construct an XDOC tree for a body directive @('@(body ...)').")

(xdoc::generate-primitive-constructor-for-dir/&& :@measure
  "Construct an XDOC tree for a measure directive @('@(measure ...)').")

(xdoc::generate-primitive-constructor-for-dir/&& :@call
  "Construct an XDOC tree for a call directive @('@(call ...)').")

(xdoc::generate-primitive-constructor-for-dir/&& :@srclink
  "Construct an XDOC tree for a source link directive @('@(srclink ...)').")

(xdoc::generate-primitive-constructor-for-dir/&& :@see
  "Construct an XDOC tree for a topic link directive @('@(see ...)').")

(xdoc::generate-primitive-constructor-for-dir/&& :@csee
  "Construct an XDOC tree
   for a capitalized topic link directive @('@(csee ...)').")

(xdoc::generate-primitive-constructor-for-dir/&& :@tsee
  "Construct an XDOC tree
   for a typewriter topic link directive @('@(csee ...)').")

(xdoc::generate-primitive-constructor-for-dir/&& :@see?
  "Construct an XDOC tree
   for a conditional topic link directive @('@(see? ...)').")

(xdoc::generate-primitive-constructor-for-dir/&& :@url
  "Construct an XDOC tree
   for a mangled topic link directive @('@(url ...)').")

(xdoc::generate-primitive-constructor-for-dir/&& :@sym
  "Construct an XDOC tree
   for a printed topic link directive @('@(sym ...)').")

(xdoc::generate-primitive-constructor-for-dir/&& :@csym
  "Construct an XDOC tree
   for a capitalized printed topic link directive @('@(csym ...)').")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc xdoc::composite-constructors
  :parents (xdoc::constructors)
  :short "Composite XDOC constructors."
  :long
  "<p>
   These correspond to multiple
   XML tags, preprocessor directives, and concatenations.
   In contrast,
   the <see topic='@(url xdoc::primitive-constructors)'>primitive
   constructors</see> correspond to single
   XML tags, preprocessor directives, and concatenations.
   </p>")

(xdoc::order-subtopics xdoc::composite-constructors nil t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc xdoc::generic-composite-constructors
  :parents (xdoc::composite-constructors)
  :short "Generic composite XDOC constructors."
  :long
  "<p>
   These are composite XDOC constructors
   that should be generally useful.
   Other composite XDOC constructors are more specific.
   </p>")

(xdoc::order-subtopics xdoc::generic-composite-constructors nil t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection xdoc::topstring
  :parents (xdoc::generic-composite-constructors)
  :short "Construct an XDOC string from a sequence of XDOC trees."
  :long
  "<p>
   A @(':long') documentation string often consists of
   a series of one or more XDOC trees
   for paragraphs, (un)ordered lists, code blocks, etc.
   This function can be used to wrap them into a top-level ``pseudo-tag''.
   </p>
   @(def xdoc::topstring)"

  (defmacro xdoc::topstring (&rest trees)
    `(xdoc::tree-to-string (xdoc::&& ,@trees))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection xdoc::topstring-p
  :parents (xdoc::generic-composite-constructors)
  :short "Construct an XDOC string with a single paragraph."
  :long
  "<p>
   Sometimes a @(':long') documentation string consists of a single paragraph.
   This macro wraps the arguments (often just one string)
   into a paragraph tree and then calls @(tsee xdoc::topstring).
   </p>
   @(def xdoc::topstring-p)"

  (defmacro xdoc::topstring-p (&rest trees)
    `(xdoc::topstring (xdoc::p ,@trees))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection xdoc::topstring-@def
  :parents (xdoc::generic-composite-constructors)
  :short "Construct an XDOC string with a single definition directive."
  :long
  "<p>
   Sometimes a @(':long') documentation string
   consists of a single definition preprocessor directive.
   This macro wraps the arguments (often just one string)
   into a definition directive tree and then calls @(tsee xdoc::topstring).
   </p>
   @(def xdoc::topstring-@def)"

  (defmacro xdoc::topstring-@def (&rest trees)
    `(xdoc::topstring (xdoc::@def ,@trees))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection xdoc::desc
  :parents (xdoc::generic-composite-constructors)
  :short "Construct an XDOC tree for a description."
  :long
  "<p>
   This consists of
   a paragraph that identifies the thing(s) being described
   followed by a quoted block of a sequence of trees that describe the thing(s).
   </p>
   <p>
   The first argument is either a string for a single thing being described
   or a list of strings for a multiple things being described.
   In the latter case, the strings are separated by line breaks
   in the generated paragraph.
   </p>
   <p>
   An alternative to generating a paragrah followed by a quoted block,
   is to generate an HTML description list @('<dl>...</dl>')
   with the thing(s) that are being described as term(s) @('<dt>...</dt>')
   and with the description trees inside @('<dd>...</dd>').
   However, the terms in a description list are rendered in bold,
   so it seems preferable to use a paragraph and a quoted block.
   </p>
   @(def xdoc::desc)"

  (defund xdoc::desc-things-to-string (things)
    (declare (xargs :guard (string-listp things)))
    (cond ((endp things) "")
          ((endp (cdr things)) (car things))
          (t (concatenate 'string
                          (car things)
                          "<br/>"
                          (xdoc::desc-things-to-string (cdr things))))))

  (defthm xdoc::stringp-of-desc-things-to-string
    (implies (string-listp things)
             (stringp (xdoc::desc-things-to-string things)))
    :hints (("Goal" :in-theory (enable xdoc::desc-things-to-string))))

  (defund xdoc::desc-fn (thing/things description)
    (declare (xargs :guard (and (or (stringp thing/things)
                                    (string-listp thing/things))
                                (xdoc::tree-listp description))
                    :guard-hints (("Goal" :in-theory (enable
                                                      xdoc::blockquote-fn
                                                      xdoc::p-fn)))))
    (let* ((things (if (stringp thing/things)
                       (list thing/things)
                     thing/things))
           (things-string (xdoc::desc-things-to-string things))
           (things-tree (xdoc::p things-string))
           (description-tree (xdoc::blockquote-fn nil description)))
      (xdoc::&& things-tree description-tree)))

  (defmacro xdoc::desc (thing/things &rest description)
    `(xdoc::desc-fn ,thing/things (list ,@description))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection xdoc::codeblock
  :parents (xdoc::generic-composite-constructors)
  :short "Construct an XDOC tree for a code block @('@({...})')
          from a sequence of strings."
  :long
  "<p>
   The arguments must evaluate to strings that are the lines of the code block,
   starting with spaces appropriate for the desired indentation
   and with no ending new line characters.
   New line characters are automatically added at the end of each line.
   A new line character is also automatically added before all the lines,
   to ensure the proper formatting in the final XDOC string.
   </p>
   <p>
   Since the XDOC tree is constructed from a sequence of subtrees,
   the aforementioned newlines are not
   directly concatenated with the input strings.
   Instead, each input string is turned into two strings.
   </p>
   <p>
   This XDOC constructor provides a possibly more convenient way
   to enter the lines that form the code block,
   compared to the bare @(tsee xdoc::@{}) XDOC constructor.
   </p>
   @(def xdoc::codeblock)"

  (defund xdoc::codeblock-terminate-lines (lines)
    (declare (xargs :guard (string-listp lines)))
    (cond ((endp lines) nil)
          (t (list* (car lines)
                    xdoc::*newline*
                    (xdoc::codeblock-terminate-lines (cdr lines))))))

  (defthm xdoc::string-listp-of-codeblock-terminate-lines
    (implies (string-listp lines)
             (string-listp (xdoc::codeblock-terminate-lines lines)))
    :hints (("Goal" :in-theory (enable xdoc::codeblock-terminate-lines))))

  (defund xdoc::codeblock-fn (lines)
    (declare (xargs :guard (string-listp lines)))
    (xdoc::@{}-fn (cons xdoc::*newline*
                        (xdoc::codeblock-terminate-lines lines))))

  (defmacro xdoc::codeblock (&rest lines)
    `(xdoc::codeblock-fn (list ,@lines))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection xdoc::seeurl
  :parents (xdoc::generic-composite-constructors)
  :short "Construct an XDOC tree for a string of the form
          @('<see topic=\"@(url ...)\">...</see>')."
  :long
  "<p>
   This is a fairly common pattern,
   with several opportunities for mistyping it.
   This XDOC constructor takes two strings as arguments,
   one for the topic and one for the hyperlinked text.
   </p>
   @(def xdoc::seeurl)"

  (defmacro xdoc::seeurl (topic text)
    `(xdoc::see_ :topic (xdoc::@url ,topic) ,text)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Obsolete functions and macros; remove when no longer referenced.

(defmacro xdoc::def (&rest args)
  `(xdoc::topstring (xdoc::@def ,@args)))

(defmacro xdoc::@code (&rest args)
  `(xdoc::codeblock ,@args))

(defun xdoc::@code-fn (lines)
  (declare (xargs :guard (string-listp lines)))
  (xdoc::codeblock-fn lines))

(defmacro xdoc::toppstring (&rest args)
  `(xdoc::topstring-p ,@args))
