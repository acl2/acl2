; XDOC Documentation System for ACL2
;
; Copyright (C) 2021 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "XDOC")

; Only the following book should be non-locally included here,
; to minimize footprint and dependencies.
(include-book "top")

; The books locally included here should be minimized, for the above reason.
; The flag book is used to prove the return type theorems of
; TREE-TO-STRING and mutually recursive companions.
(local (include-book "tools/flag" :dir :system))

; Always verify guards, even if no :GUARD ... is provided.
(set-verify-guards-eagerness 2)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc constructors
  :parents (xdoc)
  :short "Utilities to costruct
          well-formed <see topic='@(url xdoc)'>XDOC</see> strings."
  :long
  "<p>XDOC strings use <see topic='@(url markup)'>XML tags</see>,
      which must be properly matched and nested.
      They also use
      <see topic='@(url preprocessor)'>preprocessor directives</see>,
      which can be regarded as ``tag''-like constructs
      that must also be properly matched and nested.</p>
   <p>Starting with @(tsee stringp) values as the basic building blocks,
      the XDOC constructors provided here build trees that correspond to
      the combined structure of XML tags and preprocessor directives;
      these trees are recognized by the predicate @(tsee treep).
      These trees also accommodate attributes of XML tags,
      whose values are subtrees, recursively.
      The function @(tsee topstring) turns these trees into strings,
      by recursively turning subtrees into strings,
      joining those strings,
      and adding XML tags and preprocessor directives
      at the roots of the trees.</p>
   <p>With these XDOC constructors, one can write</p>
   @({
   (xdoc::topstring
      (xdoc::p \"A paragraph.\")
      (xdoc::ul
        (xdoc::li \"One.\")
        (xdoc::li \"Two.\")
        (xdoc::li \"Three.\"))
      (xdoc::p \"Another paragraph.\")
      (xdoc::p \"See \"
               (xdoc::a :href \"https://www.wikipedia.org\" \"Wikipedia\")
               \".\"))
   })
   <p>instead of</p>
   @({
     \"<p>A paragraph.</p>
      <ul>
        <li>One.</li>
        <li>Two.</li>
        <li>Three.</li>
      </ul>
      <p>Another paragraph.</p>
      <p>See <a href=\"https://www.wikipedia.org\">Wikipedia</a>.</p>\"
   })
   <p>The main advantage is that the XML tags (and preprocessor directives)
      will be always properly matched and nested by construction.
      Furthermore, using XDOC constructors
      is probably more readable,
      facilitates the modular and hierarchical construction of XDOC strings
      (in particular, see the
      <see topic='@(url composite-constructors)'
      >composite XDOC constructors</see>),
      and allows the insertion of comments within the XDOC constructor forms
      (e.g. lines of semicolons to visually separate sections).</p>
   <p>The strings at the leaves of a tree
      may well contain XML tags or preprocessor directives.
      For relatively short XML-tagged text or preprocessor directives,
      it may be better to use tags and directives within a string
      rather than the corresponding XDOC constructors,
      e.g.</p>
   @({(xdoc::p \"This is in <i>italics</i>.\")})
   <p>rather than</p>
   <code>(xdoc::p \"This is in \" (xdoc::i \"italics\") \".\")</code>
   <p>In other words,
      it is not necessary to use XDOC constructors for everything,
      but only where they are convenient.</p>
   <p>The books included by these XDOC constructor utilities
      should be minimized,
      to keep these utilities lightweight and more widely usable.</p>")

(order-subtopics constructors nil t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc constructor-preliminaries
  :parents (constructors)
  :short "Some preliminary utilities used by the XDOC constructors."
  :long
  "<p>These are independent from the XDOC constructors,
      but we introduce them here
      to keep the XDOC constructor utilities self-contained.</p>")

(order-subtopics constructor-preliminaries nil t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection *newline*
  :parents (constructor-preliminaries)
  :short "The string consisting of exactly the newline character."
  :long "@(def *newline*)"

  (defconst *newline*
    (coerce (list #\Newline) 'string))

  (assert-event (stringp *newline*)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection string-downcase$
  :parents (constructor-preliminaries)
  :short "A variant of @(tsee acl2::string-downcase) applicable to any string."
  :long
  "<p>The built-in @(tsee acl2::string-downcase) has a guard requiring
      all the characters in the string to be
      <see topic='@(url standard-char-p)'>standard</see>.
      This function ``totalizes'' @(tsee acl2::string-downcase) to all strings
      by checking whether all the characters in the string are standard,
      and by throwing a hard error if any of them is not.</p>
   <p>This facilitates guard verification of code involving this function.
      The hard error seems appropriate for the envisioned usage of this function
      within the XDOC constructors,
      meant to be called to produce XDOC strings during book certification.</p>"

  (defund string-downcase$ (string)
    (declare (xargs :guard (stringp string)))
    (if (standard-char-listp (coerce string 'list))
        (acl2::string-downcase string)
      (prog2$ (er hard? 'string-downcase$
                  "Attempt to downcase non-standard string ~x0." string)
              "")))

  (defthm stringp-of-string-downcase$
    (stringp (string-downcase$ string))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection string-escape
  :parents (constructor-preliminaries)
  :short "Escape certain characters in a string, using backslashes."
  :long
  "<p>We escape each single quote and backquote character
      that occurs in the string.</p>
   <p>This is used in @(tsee generate-primitive-constructor-for-dir/&&),
      since some of the macros generated by that macro have names
      that include the characters escaped by this function.
      These characters would cause XDOC errors if not escaped.</p>"

  (defund chars-escape (chars)
    (declare (xargs :guard (character-listp chars)))
    (cond ((endp chars) nil)
          (t (if (member (car chars) '(#\' #\`))
                 (list* #\\ #\' (chars-escape (cdr chars)))
               (cons (car chars) (chars-escape (cdr chars)))))))

  (defthm character-listp-of-chars-escape
    (implies (character-listp chars)
             (character-listp (chars-escape chars)))
    :hints (("Goal" :in-theory (enable chars-escape))))

  (defund string-escape (string)
    (declare (xargs :guard (stringp string)))
    (let* ((chars (coerce string 'list))
           (chars (chars-escape chars))
           (string (coerce chars 'string)))
      string))

  (defthm stringp-of-string-escape
    (stringp (string-escape string))
    :hints (("Goal" :in-theory (enable string-escape)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection partition-macro-args
  :parents (constructor-preliminaries)
  :short "Partition the arguments of a macro into a list and an alist."
  :long
  "<p>The XDOC constructors are macros.
      Some of them take a varying number of ``regular'' arguments
      and a varying number of keyword arguments,
      but the keywords are not predefined
      and the two kinds of arguments may be intermixed.</p>
   <p>This function partitions these intermixed arguments into
      a list of regular arguments and an alist of keyword arguments.
      Each keyword encountered in the input list
      is regarded as starting a keyword argument
      (unless it follows one already);
      if a keyword is not followed by a value,
      it is an error.
      This function does not check for duplicate keywords.
      The output list and alists are in the same order as in the input.</p>"

  (defund partition-macro-args (args ctx)
    (declare (xargs :guard (true-listp args)))
    (cond ((endp args) (mv nil nil))
          ((keywordp (car args))
           (if (consp (cdr args))
               (mv-let (rest-list rest-alist)
                 (partition-macro-args (cddr args) ctx)
                 (mv rest-list (acons (car args) (cadr args) rest-alist)))
             (prog2$ (er hard? ctx "Missing value for keyword ~x0." (car args))
                     (mv nil nil))))
          (t (mv-let (rest-list rest-alist)
               (partition-macro-args (cdr args) ctx)
               (mv (cons (car args) rest-list) rest-alist)))))

  (defthm true-listp-of-mv-nth-0-partition-macro-args
    (true-listp (mv-nth 0 (partition-macro-args args ctx)))
    :hints (("Goal" :in-theory (enable partition-macro-args))))

  (defthm alistp-of-mv-nth-1-partition-macro-args
    (alistp (mv-nth 1 (partition-macro-args args ctx)))
    :hints (("Goal" :in-theory (enable partition-macro-args)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection keyword-macro-args-to-terms
  :parents (constructor-preliminaries)
  :short "Turn the keyword arguments of a macro into terms."
  :long
  "<p>This complements @(tsee partition-macro-args),
      which extracts a list of regular arguments
      and an alist of keyword arguments.
      This alist has keys that are keywords
      but values that, in general, are terms that need to be evaluated
      to obtain the actual values of the keyword arguments;
      the terms are the ones supplied by the caller of the macro.
      This function turns that alist into
      a list of terms that, when put inside a @(tsee list),
      construct the alist with evaluated values:
      each term, when evaluated, returns a @(tsee cons) pair.</p>"

  (defund keyword-macro-args-to-terms (alist)
    (declare (xargs :guard (alistp alist)))
    (cond ((endp alist) nil)
          (t (cons `(cons ,(caar alist)
                          ,(cdar alist))
                   (keyword-macro-args-to-terms (cdr alist))))))

  (defthm true-listp-of-keyword-macro-args-to-terms
    (true-listp (keyword-macro-args-to-terms alist))
    :hints (("Goal" :in-theory (enable keyword-macro-args-to-terms)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc trees
  :parents (constructors)
  :short "XDOC trees.")

(order-subtopics trees nil t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection treep
  :parents (trees)
  :short "Recognize XDOC trees."
  :long
  "<p>These are the trees produced by the XDOC constructors.</p>
   <p>These trees have strings at the leaves.
      A non-leaf node consists of one of the following:</p>
   <ul>
     <li>A single keyword.
         This represents either
         (i) a preprocessor directive
         or (ii) a concatenation of subtrees
         without a surrounding XML tag or preprocessor directive.
         Examples of (i) are @(':@def') and @(':@{}').
         The keyword @(':&&') is used for (ii).
         The latter is useful to treat sequences of trees as single trees.</li>
     <li>A @(tsee cons) pair
         whose @(tsee car) is a keyword and
         whose @(tsee cdr) is an alist from keywords to subtrees.
         This represents an XML tag,
         identified by the keyword at the @(tsee car),
         with the attributes represented by the alist at the @(tsee cdr).
         Examples are @('(:p)') and @('(:img (:src ...))').
         The alist may often be @('nil').
         The values of the attributes are recursively represented as subtrees,
         but there may often be a single string subtree per attribute.</li>
   </ul>
   <p>In some sense,
      the semantics of XDOC trees is defined by their conversion to flat strings.
      See @(tsee tree-to-string).</p>"

  ;; functions:

  (mutual-recursion

   (defund treep (x)
     (or (stringp x)
         (and (true-listp x)
              (consp x)
              (or (keywordp (car x))
                  (tree-tagp (car x)))
              (tree-listp (cdr x)))))

   (defund tree-listp (x)
     (cond ((atom x) (eq x nil))
           (t (and (treep (car x))
                   (tree-listp (cdr x))))))

   (defund tree-tagp (x)
     (and (consp x)
          (keywordp (car x))
          (keyword-tree-alistp (cdr x))))

   (defund keyword-tree-alistp (x)
     (cond ((atom x) (eq x nil))
           (t (and (consp (car x))
                   (keywordp (car (car x)))
                   (treep (cdr (car x)))
                   (keyword-tree-alistp (cdr x)))))))

  ;; theorems:

  (defthm treep-when-stringp
    (implies (stringp x)
             (treep x))
    :hints (("Goal" :in-theory (enable treep))))

  (defthm tree-listp-when-string-listp
    (implies (string-listp x)
             (tree-listp x))
    :hints (("Goal" :in-theory (enable tree-listp))))

  (defthm true-listp-when-tree-listp
    (implies (tree-listp x)
             (true-listp x))
    :rule-classes :forward-chaining
    :hints (("Goal" :in-theory (enable tree-listp))))

  (defthm treep-of-cons
    (equal (treep (cons x y))
           (and (or (keywordp x)
                    (tree-tagp x))
                (tree-listp y)))
    :hints (("Goal" :in-theory (enable treep))))

  (defthm tree-listp-of-cons
    (equal (tree-listp (cons x y))
           (and (treep x)
                (tree-listp y)))
    :hints (("Goal" :in-theory (enable tree-listp))))

  (defthm tagp-of-cons
    (equal (tree-tagp (cons x y))
           (and (keywordp x)
                (keyword-tree-alistp y)))
    :hints (("Goal" :in-theory (enable tree-tagp))))

  (defthm keyword-tree-alistp-of-cons
    (equal (keyword-tree-alistp (cons x y))
           (and (consp x)
                (keywordp (car x))
                (treep (cdr x))
                (keyword-tree-alistp y)))
    :hints (("Goal" :in-theory (enable keyword-tree-alistp)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection tree-to-string
  :parents (trees)
  :short "Turn a XDOC tree into the string it represents."
  :long
  "<p>An XDOC tree is turned into a string as follows.
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
      are obtained by recursively turning
      the subtrees in the alist into strings.</p>
   <p>As noted <see topic='@(url str::concatenation)'>here</see>,
      string concatenation is slow in ACL2 in general.
      The current implementation of this function
      uses straighforward string concatenation,
      but this could be optimized in the future,
      if concatenating strings turns out to be too slow
      in the actual usage of these XDOC constructors.</p>
   <p>Note that the @(tsee symbol-name) of a keyword tag
      consists of uppercase letters.
      We use @(tsee string-downcase$)
      to produce lowercase tags and directives.
      We expect that this function will never throw an error
      with the tags and directives supported.</p>"

  ;; functions:

  (mutual-recursion

   (defund tree-to-string (tree)
     (declare (xargs :guard (treep tree)
                     :verify-guards nil)) ; done below
     (cond ((atom tree) (if (mbt (stringp tree)) tree ""))
           (t (let ((subtrees-string (tree-list-to-string (cdr tree))))
                (mv-let (left-string right-string)
                  (keyword-or-tree-tag-to-strings (car tree))
                  (concatenate 'string
                               left-string subtrees-string right-string))))))

   (defund tree-list-to-string (trees)
     (declare (xargs :guard (tree-listp trees)))
     (cond ((endp trees) "")
           (t (concatenate 'string
                           (tree-to-string (car trees))
                           (tree-list-to-string (cdr trees))))))

   (defund keyword-or-tree-tag-to-strings (keyword/tag)
     (declare (xargs :guard (or (keywordp keyword/tag)
                                (tree-tagp keyword/tag))))
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
                         (keyword-string (string-downcase$
                                          keyword-string))
                         (left-string (concatenate 'string
                                                   "@(" keyword-string " "))
                         (right-string ")"))
                    (mv left-string right-string))
                (prog2$ (er hard?
                            'tree-to-string
                            "Cannot process XDOC tree with root ~x0."
                            keyword/tag)
                        (mv "" "")))))
           (t (let* ((keyword (car keyword/tag))
                     (keyword-chars (coerce (symbol-name keyword) 'list))
                     (keyword-string (coerce keyword-chars 'string))
                     (keyword-string (string-downcase$ keyword-string))
                     (attributes (cdr keyword/tag))
                     (attributes-string (keyword-tree-alist-to-string
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

   (defund keyword-tree-alist-to-string (attributes)
     (declare (xargs :guard (keyword-tree-alistp attributes)))
     (cond ((endp attributes) "")
           (t (let* ((attribute (car attributes))
                     (keyword (car attribute))
                     (tree (cdr attribute))
                     (keyword-chars (coerce (symbol-name keyword) 'list))
                     (keyword-string (coerce keyword-chars 'string))
                     (keyword-string (string-downcase$ keyword-string))
                     (tree-string (tree-to-string tree))
                     (attribute-string (concatenate 'string
                                                    " "
                                                    keyword-string
                                                    "=\""
                                                    tree-string
                                                    "\""))
                     (rest-attributes (cdr attributes))
                     (rest-attribute-string (keyword-tree-alist-to-string
                                             rest-attributes)))
                (concatenate 'string
                             attribute-string
                             rest-attribute-string))))))

  ;; theorems:

  (local (acl2::make-flag flag-xdoc-tree-to-string tree-to-string))

  (local
   (defthm-flag-xdoc-tree-to-string
     (defthm theorem-for-tree-to-string
       (stringp (tree-to-string tree))
       :flag tree-to-string)
     (defthm theorem-for-tree-list-to-string
       (stringp (tree-list-to-string trees))
       :flag tree-list-to-string)
     (defthm theorem-for-keyword-or-tree-tag-to-strings
       (and (stringp (mv-nth 0 (keyword-or-tree-tag-to-strings
                                keyword/tag)))
            (stringp (mv-nth 1 (keyword-or-tree-tag-to-strings
                                keyword/tag))))
       :flag keyword-or-tree-tag-to-strings)
     (defthm theorem-for-keyword-tree-alist-to-string
       (stringp (keyword-tree-alist-to-string attributes))
       :flag keyword-tree-alist-to-string)
     :hints (("Goal" :in-theory (enable tree-to-string
                                        tree-list-to-string
                                        keyword-or-tree-tag-to-strings
                                        keyword-tree-alist-to-string
                                        treep)))))

  (defthm stringp-of-tree-to-string
    (stringp (tree-to-string tree)))

  (defthm stringp-of-tree-list-to-string
    (stringp (tree-list-to-string trees)))

  (defthm stringp-of-mv-nth-0-keyword-or-tree-tag-to-strings
    (implies (or (keywordp keyword/tag)
                 (tree-tagp keyword/tag))
             (stringp (mv-nth 0 (keyword-or-tree-tag-to-strings
                                 keyword/tag))))
    :hints (("Goal" :in-theory (disable mv-nth))))

  (defthm stringp-of-mv-nth-1-keyword-or-tree-tag-to-strings
    (stringp (mv-nth 1 (keyword-or-tree-tag-to-strings
                        keyword/tag)))
    :hints (("Goal" :in-theory (disable mv-nth))))

  (defthm stringp-of-keyword-tree-alist-to-string
    (stringp (keyword-tree-alist-to-string attributes)))

  ;; guard verification:

  (local
   (defthm tree-to-string-verify-guards-lemma
     (implies (character-listp x)
              (character-listp (cdr x)))))

  (verify-guards tree-to-string
    :hints (("Goal" :in-theory (e/d (tree-tagp keyword-tree-alistp treep)
                                    (mv-nth))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection make-tree-tag
  :parents (trees)
  :short "Construct a non-leaf XDOC tree with an XML tag at the root."
  :long
  "<p>This is for internal use of the XDOC constructor library.
      Users of this library should use
      constructors for specific tags, e.g. @(tsee p).</p>
   <p>See also @(tsee make-tree-dir/&&).</p>"

  (defund make-tree-tag (tag attributes trees)
    (declare (xargs :guard (and (keywordp tag)
                                (keyword-tree-alistp attributes)
                                (tree-listp trees))))
    (cons (cons tag attributes) trees))

  (defthm treep-of-make-tree-tag
    (equal (treep (make-tree-tag tag attributes trees))
           (and (keywordp tag)
                (keyword-tree-alistp attributes)
                (tree-listp trees)))
    :hints (("Goal" :in-theory (enable make-tree-tag)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection make-tree-dir/&&
  :parents (trees)
  :short "Construct a non-leaf XDOC tree
          with a preprocessor directive or a tree concatenation at the root."
  :long
  "<p>This is for internal use of the XDOC constructor library.
      Users of this library should use
      the constructor @(tsee &&) for concatenation
      or constructors for specific directives, e.g. @(tsee @def).</p>
   <p>See also @(tsee make-tree-tag).</p>"

  (defund make-tree-dir/&& (dir/&& trees)
    (declare (xargs :guard (and (keywordp dir/&&)
                                (tree-listp trees))))
    (cons dir/&& trees))

  (defthm treep-of-make-tree-dir/&&
    (implies (keywordp dir/&&)
             (equal (treep (make-tree-dir/&& dir/&& trees))
                    (tree-listp trees)))
    :hints (("Goal" :in-theory (enable make-tree-dir/&&)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc primitive-constructors
  :parents (constructors)
  :short "Primitive XDOC constructors."
  :long
  "<p>These correspond to
      individual XML tags,
      individual preprocessor directives,
      and tree concatenation.
      In contrast, the
      <see topic='@(url composite-constructors)'>composite
      XDOC constructors</see>
      correspond to multiple tags, directives, and concatenations,
      or provide a more concise notation for common attributes.</p>
   <p>These primitive constructors are
      macros with a variable number of arguments.
      Each argument must be a tree or a keyword,
      such that each keyword is immediately followed by a tree.
      Each keyword-tree pair forms an attribute of an XML tag,
      with the keyword naming the attribute
      and the immediately following tree providing the value of the attribute.
      Keyword-tree pairs can be used only in constructors for XML tags,
      not in constructors for preprocessor directives or tree concatenation.
      Keyword-tree pairs may occur anywhere in the argument list.
      See the <see topic='@(url constructors)'>top-level topic</see>
      for example calls of primitive constructors.</p>
   <p>Since these primitive constructors have a very uniform structure,
      we introduce them via two event-generating macros,
      one for XML tags
      and one for preprocessor directives and tree concatenation.</p>")

(order-subtopics primitive-constructors nil t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection generate-primitive-constructor-for-tag
  :parents (primitive-constructors)
  :short "Generate a primitive constructor for an XML tag."
  :long
  "<p>The arguments are a keyword for the tag (e.g. @(':p') for paragraphs)
      and a documentation string that describes the primitive constructor.
      This documentation string is used as the @(':short') string
      of the XDOC topic generated for the primitive constructor itself.</p>
   <p>The generated XDOC constructor consists of a macro that calls a function
      (also generated),
      as often done with macros.
      We also generate a theorem about the return type of the constructor.</p>
   <p>The generated macro accepts regular and keyword arguments in any order:
      the former are subtrees for the content between the XML tags;
      the latter are attributes of the XML tag.
      The macro uses @(tsee partition-macro-args) to divide them.</p>
   <p>The name of the macro includes an added underscore at the end
      if the tag is @(':table'), @(':u'), or @(':see').
      That is, the generated macro names for these tags are
      @('table_'), @('u_'), and @('see_').
      The reason is that
      @('table') would conflict with the built-in @(tsee table),
      @('u') would conflict with the built-in @(tsee u),
      and @('see') would conflict with an existing function called @('see')
      in @('[books]/xdoc/names.lisp').</p>
   <p>See also @(tsee generate-primitive-constructor-for-dir/&&).</p>
   @(def generate-primitive-constructor-for-tag)"

  (defund generate-primitive-constructor-for-tag-fn (tag doc)
    (declare (xargs :guard (and (keywordp tag) (stringp doc))))
    (let* ((macro-name (case tag
                         (:table 'table_)
                         (:u 'u_)
                         (:see 'see_)
                         (t (intern$ (symbol-name tag) "XDOC"))))
           (fn-name (acl2::add-suffix-to-fn macro-name "-FN"))
           (thm-name (acl2::packn (list 'stringp-of- macro-name)))
           (long (concatenate
                  'string
                  "<p>See the <see topic='@(url primitive-constructors)'
                   >primitive constructors topic</see>
                   for information about the kind of arguments
                   that must be passed to this constructor.</p>"
                  "@(def "
                  (string-downcase$ (symbol-name macro-name))
                  ")")))
      `(defsection ,macro-name
         :parents (primitive-constructors)
         :short ,doc
         :long ,long
         (defund ,fn-name (attributes trees)
           (declare (xargs :guard (and (keyword-tree-alistp attributes)
                                       (tree-listp trees))))
           (make-tree-tag ,tag attributes trees))
         (defthm ,thm-name
           (equal (treep (,fn-name attributes trees))
                  (and (keyword-tree-alistp attributes)
                       (tree-listp trees)))
           :hints (("Goal" :in-theory (enable ,fn-name))))
         (defmacro ,macro-name (&rest args)
           (mv-let (trees attributes)
             (partition-macro-args args ',macro-name)
             (let ((attributes (keyword-macro-args-to-terms attributes)))
               (list ',fn-name
                     (cons 'list attributes)
                     (cons 'list trees))))))))

  (defmacro generate-primitive-constructor-for-tag (tag doc)
    `(make-event (generate-primitive-constructor-for-tag-fn ,tag ,doc))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection generate-primitive-constructor-for-dir/&&
  :parents (primitive-constructors)
  :short "Generate a primitive constructor for
          a preprocessor directive or tree concatenation."
  :long
  "<p>The arguments are
      a keyword for the directive (e.g. @(':@def') for definitions)
      or for tree concatenation (i.e. @(':&&')),
      and a documentation string that describes the primitive constructor.
      This documentation string is used as the @(':short') string
      of the XDOC topic generated for the primitive constructor itself.</p>
   <p>The generated XDOC constructor consists of a macro that calls a function
      (also generated),
      as often done with macros.
      We also generate a theorem about the return type of the constructor.</p>
   <p>See also @(tsee generate-primitive-constructor-for-tag).</p>
   @(def generate-primitive-constructor-for-dir/&&)"

  (defund generate-primitive-constructor-for-dir/&&-fn (dir/&& doc)
    (declare (xargs :guard (and (keywordp dir/&&) (stringp doc))))
    (let* ((macro-name (acl2::add-suffix-to-fn '|| (symbol-name dir/&&)))
           (fn-name (acl2::add-suffix-to-fn macro-name "-FN"))
           (thm-name (acl2::packn (list 'stringp-of- macro-name))))
      `(defsection ,macro-name
         :parents (primitive-constructors)
         :short ,doc
         :long ,(concatenate 'string
                             "@(def "
                             (string-escape
                              (string-downcase$
                               (symbol-name macro-name)))
                             ")")
         (defund ,fn-name (trees)
           (declare (xargs :guard (tree-listp trees)))
           (make-tree-dir/&& ,dir/&& trees))
         (defthm ,thm-name
           (equal (treep (,fn-name trees))
                  (tree-listp trees))
           :hints (("Goal" :in-theory (enable ,fn-name))))
         (defmacro ,macro-name (&rest trees)
           (list ',fn-name (cons 'list trees))))))

  (defmacro generate-primitive-constructor-for-dir/&& (dir/&& doc)
    `(make-event
      (generate-primitive-constructor-for-dir/&&-fn ,dir/&& ,doc))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; primitive XDOC constructors for XML tags:

(generate-primitive-constructor-for-tag :h1
  "Construct an XDOC tree for an HTML level-1 heading @('<h1>...</h1>').")

(generate-primitive-constructor-for-tag :h2
  "Construct an XDOC tree for an HTML level-2 heading @('<h2>...</h2>').")

(generate-primitive-constructor-for-tag :h3
  "Construct an XDOC tree for an HTML level-3 heading @('<h3>...</h3>').")

(generate-primitive-constructor-for-tag :h4
  "Construct an XDOC tree for an HTML level-4 heading @('<h4>...</h4>').")

(generate-primitive-constructor-for-tag :h5
  "Construct an XDOC tree for an HTML level-5 heading @('<h5>...</h5>').")

(generate-primitive-constructor-for-tag :p
  "Construct an XDOC tree for an HTML paragraph @('<p>...</p>').")

(generate-primitive-constructor-for-tag :blockquote
  "Construct an XDOC tree for
   an HTML quoted block @('<blockquote>...</blockquote>').")

(generate-primitive-constructor-for-tag :li
  "Construct an XDOC tree for an HTML list item @('<li>...</li>').")

(generate-primitive-constructor-for-tag :ul
  "Construct an XDOC tree for an HTML unordered (bulleted) list @('<ul>...</ul>').")

(generate-primitive-constructor-for-tag :ol
  "Construct an XDOC tree for an HTML ordered (numbered) list @('<ol>...</ol>').")

(generate-primitive-constructor-for-tag :dt
  "Construct an XDOC tree for an HTML term @('<dt>...</dt>').")

(generate-primitive-constructor-for-tag :dd
  "Construct an XDOC tree for an HTML description @('<dd>...</dd>').")

(generate-primitive-constructor-for-tag :dl
  "Construct an XDOC tree for an HTML description list @('<dl>...</dl>').")

(generate-primitive-constructor-for-tag :th
  "Construct an XDOC tree for an HTML table header cell @('<th>...</th>').")

(generate-primitive-constructor-for-tag :td
  "Construct an XDOC tree for an HTML table cell @('<td>...</td>').")

(generate-primitive-constructor-for-tag :tr
  "Construct an XDOC tree for an HTML table row @('<tr>...</tr>').")

(generate-primitive-constructor-for-tag :table
  ;; generates TABLE_ macro (see GENERATE-PRIMITIVE-CONSTRUCTOR-FOR-TAG)
  "Construct an XDOC tree for an HTML table @('<table>...</table>').")

(generate-primitive-constructor-for-tag :box
  "Construct an XDOC tree for an XDOC box @('<box>...</box>').")

(generate-primitive-constructor-for-tag :br
  "Construct an XDOC tree for an HTML line break @('<br>...</br>').")

(generate-primitive-constructor-for-tag :img
  "Construct an XDOC tree for an HTML image @('<img>...</img>').")

(generate-primitive-constructor-for-tag :b
  "Construct an XDOC tree for HTML bold text @('<b>...</b>').")

(generate-primitive-constructor-for-tag :i
  "Construct an XDOC tree for HTML italic text @('<i>...</i>').")

(generate-primitive-constructor-for-tag :u
  ;; generates U_ macro (see GENERATE-PRIMITIVE-CONSTRUCTOR-FOR-TAG)
  "Construct an XDOC tree for HTML underlined text @('<u>...</u>').")

(generate-primitive-constructor-for-tag :color
  "Construct an XDOC tree for HTML colored text @('<color>...</color>').")

(generate-primitive-constructor-for-tag :sf
  "Construct an XDOC tree for HTML sans-serif text @('<sf>...</sf>').")

(generate-primitive-constructor-for-tag :tt
  "Construct an XDOC tree for XDOC inline code @('<tt>...</tt>')
   (which is not rendered using the homonymous HTML tags;
   see @(see markup)).")

(generate-primitive-constructor-for-tag :code
  "Construct an XDOC tree for XDOC code block @('<code>...</code>')
   (which is not rendered using the homonymous HTML tags;
   see @(see markup)).")

(generate-primitive-constructor-for-tag :a
  "Construct an XDOC tree for an HTML hyperlink @('<a>...</a>').")

(generate-primitive-constructor-for-tag :see
  ;; generates SEE_ macro (see GENERATE-PRIMITIVE-CONSTRUCTOR-FOR-TAG)
  "Construct an XDOC tree for an XDOC hyperlink @('<see>...</see>').")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; primitive XDOC constructors for preprocessor directives and for concatenation:

(generate-primitive-constructor-for-dir/&& :&&
  "Construct an XDOC tree for a concatenation.")

(generate-primitive-constructor-for-dir/&& :@\'\'
  "Construct an XDOC tree
   for a inline code directive <tt>@</tt><tt>(\'...\')</tt>.")

(generate-primitive-constructor-for-dir/&& :@{}
  "Construct an XDOC tree
   for a code block directive <tt>@</tt><tt>({...})</tt>.")

(generate-primitive-constructor-for-dir/&& :@\`\`
  "Construct an XDOC tree
   for an evaluation directive <tt>@</tt><tt>(\`...\`)</tt>.")

(generate-primitive-constructor-for-dir/&& :@$$
  "Construct an XDOC tree
   for a short KaTeK directive <tt>@</tt><tt>($...$)</tt>.")

(generate-primitive-constructor-for-dir/&& :@[]
  "Construct an XDOC tree
   for a long KaTeK directive <tt>@</tt><tt>([...])</tt>.")

(generate-primitive-constructor-for-dir/&& :@def
  "Construct an XDOC tree
   for a definition directive <tt>@</tt><tt>(def ...)</tt>.")

(generate-primitive-constructor-for-dir/&& :@gdef
  "Construct an XDOC tree
   for a generated definition directive <tt>@</tt><tt>(gdef ...)</tt>.")

(generate-primitive-constructor-for-dir/&& :@formals
  "Construct an XDOC tree
   for a formals directive <tt>@</tt><tt>(formals ...)</tt>.")

(generate-primitive-constructor-for-dir/&& :@body
  "Construct an XDOC tree
   for a body directive <tt>@</tt><tt>(body ...)</tt>.")

(generate-primitive-constructor-for-dir/&& :@measure
  "Construct an XDOC tree
   for a measure directive <tt>@</tt><tt>(measure ...)</tt>.")

(generate-primitive-constructor-for-dir/&& :@call
  "Construct an XDOC tree
   for a call directive <tt>@</tt><tt>(call ...)</tt>.")

(generate-primitive-constructor-for-dir/&& :@srclink
  "Construct an XDOC tree
   for a source link directive <tt>@</tt><tt>(srclink ...)</tt>.")

(generate-primitive-constructor-for-dir/&& :@see
  "Construct an XDOC tree
   for a topic link directive <tt>@</tt><tt>(see ...)</tt>.")

(generate-primitive-constructor-for-dir/&& :@csee
  "Construct an XDOC tree
   for a capitalized topic link directive <tt>@</tt><tt>(csee ...)</tt>.")

(generate-primitive-constructor-for-dir/&& :@tsee
  "Construct an XDOC tree
   for a typewriter topic link directive <tt>@</tt><tt>(tsee ...)</tt>.")

(generate-primitive-constructor-for-dir/&& :@see?
  "Construct an XDOC tree
   for a conditional topic link directive <tt>@</tt><tt>(see? ...)</tt>.")

(generate-primitive-constructor-for-dir/&& :@url
  "Construct an XDOC tree
   for a mangled topic link directive <tt>@</tt><tt>(url ...)</tt>.")

(generate-primitive-constructor-for-dir/&& :@sym
  "Construct an XDOC tree
   for a printed topic link directive <tt>@</tt><tt>(sym ...)</tt>.")

(generate-primitive-constructor-for-dir/&& :@csym
  "Construct an XDOC tree
   for a capitalized printed topic link directive
   <tt>@</tt><tt>(csym ...)</tt>.")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc composite-constructors
  :parents (constructors)
  :short "Composite XDOC constructors."
  :long
  (xdoc::tree-to-string
   (xdoc::p
    "These correspond to multiple
     XML tags, preprocessor directives, and concatenations,
     or provide a more concise notation for common attributes.
     In contrast,
     the <see topic='@(url primitive-constructors)'>primitive
     constructors</see> correspond to single
     XML tags, preprocessor directives, and concatenations.")))

(order-subtopics composite-constructors nil t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc generic-composite-constructors
  :parents (composite-constructors)
  :short "Generic composite XDOC constructors."
  :long
  (xdoc::tree-to-string
   (xdoc::p
    "These are composite XDOC constructors
     that should be generally useful.
     Other composite XDOC constructors are more specific.")))

(order-subtopics generic-composite-constructors nil t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection topstring
  :parents (generic-composite-constructors)
  :short "Construct an XDOC string from a sequence of XDOC trees."
  :long
  (xdoc::tree-to-string
   (xdoc::&&
    (xdoc::p
     "This can be used to construct XDOC strings at the ``top level'',
      e.g. @(':short') and @(':long') documentation string.")
    (xdoc::@def "topstring")))

  (defmacro topstring (&rest trees)
    `(tree-to-string (&& ,@trees))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection topstring-p
  :parents (generic-composite-constructors)
  :short "Construct an XDOC string with a single paragraph."
  :long
  (xdoc::topstring
   (xdoc::p
    "This combines @(tsee topstring) with @(tsee p).")
   (xdoc::@def "topstring-p"))

  (defmacro topstring-p (&rest trees)
    `(topstring (p ,@trees))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection topstring-@def
  :parents (generic-composite-constructors)
  :short "Construct an XDOC string with a single definition directive."
  :long
  (xdoc::topstring
   (xdoc::p
    "This combines @(tsee topstring) with @(tsee @def).")
   (xdoc::@def "topstring-@def"))

  (defmacro topstring-@def (&rest trees)
    `(topstring (@def ,@trees))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection desc
  :parents (generic-composite-constructors)
  :short "Construct an XDOC tree for a description."
  :long
  (xdoc::topstring
   (xdoc::p
    "This consists of
     a paragraph that identifies the thing(s) being described
     followed by a quoted block of a sequence of trees
     that describe the thing(s).")
   (xdoc::p
    "The first argument is either a string for a single thing being described
     or a list of strings for a multiple things being described.
     In the latter case, the strings are separated by line breaks
     in the generated paragraph.")
   (xdoc::p
    "An alternative to generating a paragrah followed by a quoted block,
     is to generate an HTML description list @('<dl>...</dl>')
     with the thing(s) that are being described as term(s) @('<dt>...</dt>')
     and with the description trees inside @('<dd>...</dd>').
     However, the terms in a description list are rendered in bold,
     so it seems preferable to use a paragraph and a quoted block.")
   (xdoc::@def "desc"))

  (defund desc-things-to-string (things)
    (declare (xargs :guard (string-listp things)))
    (cond ((endp things) "")
          ((endp (cdr things)) (car things))
          (t (concatenate 'string
                          (car things)
                          "<br/>"
                          (desc-things-to-string (cdr things))))))

  (defthm stringp-of-desc-things-to-string
    (implies (string-listp things)
             (stringp (desc-things-to-string things)))
    :hints (("Goal" :in-theory (enable desc-things-to-string))))

  (defund desc-fn (thing/things description)
    (declare (xargs :guard (and (or (stringp thing/things)
                                    (string-listp thing/things))
                                (tree-listp description))
                    :guard-hints (("Goal" :in-theory (enable
                                                      blockquote-fn
                                                      p-fn)))))
    (let* ((things (if (stringp thing/things)
                       (list thing/things)
                     thing/things))
           (things-string (desc-things-to-string things))
           (things-tree (p things-string))
           (description-tree (blockquote-fn nil description)))
      (&& things-tree description-tree)))

  (defmacro desc (thing/things &rest description)
    `(desc-fn ,thing/things (list ,@description))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection codeblock
  :parents (generic-composite-constructors)
  :short "Construct an XDOC tree for a code block @('@({...})')
          from a sequence of strings."
  :long
  (xdoc::topstring
   (xdoc::p
    "The arguments must evaluate to strings
     that are the lines of the code block,
     starting with spaces appropriate for the desired indentation
     and with no ending new line characters.
     New line characters are automatically added at the end of each line.
     A new line character is also automatically added before all the lines,
     to ensure the proper formatting in the final XDOC string.")
   (xdoc::p
    "Since the XDOC tree is constructed from a sequence of subtrees,
     the aforementioned newlines are not
     directly concatenated with the input strings.
     Instead, each input string is turned into two strings.")
   (xdoc::p
    "This XDOC constructor provides a possibly more convenient way
     to enter the lines that form the code block,
     compared to the bare @(tsee @{}) XDOC constructor.")
   (xdoc::@def "codeblock"))

  (defund codeblock-terminate-lines (lines)
    (declare (xargs :guard (string-listp lines)))
    (cond ((endp lines) nil)
          (t (list* (car lines)
                    *newline*
                    (codeblock-terminate-lines (cdr lines))))))

  (defthm string-listp-of-codeblock-terminate-lines
    (implies (string-listp lines)
             (string-listp (codeblock-terminate-lines lines)))
    :hints (("Goal" :in-theory (enable codeblock-terminate-lines))))

  (defund codeblock-fn (lines)
    (declare (xargs :guard (string-listp lines)))
    (@{}-fn (cons *newline*
                        (codeblock-terminate-lines lines))))

  (defmacro codeblock (&rest lines)
    `(codeblock-fn (list ,@lines))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection ahref
  :parents (generic-composite-constructors)
  :short "Construct an XDOC tree for a string of the form
          @('<a href=\"...\">...</a>')."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is a fairly common pattern.
     This XDOC constructor obviates the need to type @(':href'),
     compared to the primitive constructor @(tsee a):
     the first argument is always the URL,
     and the remaining arguments form the text.")
   (xdoc::@def "ahref"))

  (defmacro ahref (href &rest text)
    `(a :href ,href ,@text)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection seetopic
  :parents (generic-composite-constructors)
  :short "Construct an XDOC tree for a string of the form
          @('<see topic=\"@(url ...)\">...</see>')."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is a fairly common pattern,
     with several opportunities for mistyping it.
     This XDOC constructor takes two strings as arguments,
     one for the topic and one for the hyperlinked text.")
   (xdoc::@def "seetopic"))

  (defmacro seetopic (topic text)
    `(see_ :topic (@url ,topic) ,text)))
