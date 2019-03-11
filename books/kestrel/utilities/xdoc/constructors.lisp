; XDOC Utilities -- Constructors
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "xdoc/top" :dir :system)

(include-book "tools/flag" :dir :system)

(set-verify-guards-eagerness 2)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc xdoc::constructors
  :parents (xdoc-utilities)
  :short "Utilities to costruct
          well-formed <see topic='@(url xdoc)'>XDOC</see> strings."
  :long
  "<p>
   XDOC strings use HTML tags, which must be properly matched and nested.
   There are also constraints about nesting well-tagged HTML text,
   e.g. an (un)ordered list must contain a sequence of list items.
   The XDOC constructors provided here help build HTML strings
   with properly matched and nested tags
   that satisfy certain constraints.
   </p>
   <p>
   Starting with @(tsee stringp) values as the basic building blocks,
   these XDOC constructors build trees that correspond to the HTML structure;
   these trees are recognized by the predicate @(tsee xdoc::treep).
   The function @(tsee xdoc::topstring) turns trees into strings,
   by recursively turning subtrees into strings,
   joining those strings,
   and surrounding them with the HTML tags at the roots of the trees.
   </p>
   <p>
   The string at the leaves of a tree could contain HTML tags.
   Thus, the XDOC constructors provided here can be used also
   with XDOC strings built without the constructors.
   </p>
   <p>
   The following XDOC constructors are provided:
   </p>
   <ul>
     <li>@('(xdoc::h1 string)') for level-1 headings</li>
     <li>@('(xdoc::h2 string)') for level-2 headings</li>
     <li>@('(xdoc::h3 string)') for level-3 headings</li>
     <li>@('(xdoc::h4 string)') for level-4 headings</li>
     <li>@('(xdoc::h5 string)') for level-5 headings</li>
     <li>@('(xdoc::p string)') for paragraphs</li>
     <li>@('(xdoc::blockquote tree ... tree)') for quoted blocks</li>
     <li>@('(xdoc::li tree ... tree)') for (un)ordered list items</li>
     <li>@('(xdoc::ul li-tree ... li-tree)') for unordered lists</li>
     <li>@('(xdoc::ol li-tree ... li-tree)') for ordered lists</li>
     <li>@('(xdoc::dt string)') for description list terms</li>
     <li>@('(xdoc::dd tree ... tree)') for description list descriptions</li>
     <li>@('(xdoc::dl dt/dd-tree ... dt/dd-tree)') for description lists</li>
     <li>@('(xdoc::&& tree ... tree)') to join trees into a tree
         that will not be surrounded by any tag when turned into a string</li>
     <li>@('(xdoc::@{} string)') for XDOC code blocks</li>
     <li>@('(xdoc::@code line ... line)') for XDOC code blocks
         whose string is constructed by
         terminating the given lines with newline characters
         and by joining the terminated lines together</li>
     <li>@('(xdoc::desc string-or-list-of-strings tree ... tree)')
         for singleton description lists where
         the string(s) become(s) the term(s)
         and the trees become the description</li>
     <li>@('(xdoc::topstring tree ... tree)') to turn trees into a string,
         at the top level</li>
     <li>@('(xdoc::toppstring string)') for a single top-level paragraph</li>
   </ul>
   <p>
   More constructors may be added as needed.
   </p>
   <p>
   Example usage:
   </p>
   @({
     (xdoc::topstring
       (xdoc::p \"A paragraph.\")
       (xdoc::ul
         (xdoc::li \"One.\")
         (xdoc::li \"Two.\")
         (xdoc::li \"Three.\"))
       (xdoc::p \"Another paragraph.\"))
   })")

(local (set-default-parents xdoc::constructors))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection xdoc::treep
  :short "Recognize XDOC trees."
  :long
  "<p>
   These are the trees produced by our XDOC constructors.
   </p>
   <p>
   These trees have strings at the leaves.
   A non-leaf node consists of
   a keyword that corresponds to an HTML tag (e.g. @(':p') for @('<p>')),
   and zero or more subtrees.
   The keyword tag may also be @(':@{}'),
   which corresponds to the XDOC macro @('@({...})');
   this is not an HTML tag,
   but essentially behaves like one as far as the XDOC structure is concerned.
   The keyword tag may also be @(':&&'),
   which indicates that the strings from the subtrees should be joined
   without being surrounded by any tag;
   this is useful to treat lists of subtrees (e.g. lists of paragraphs)
   as single trees.
   See @(tsee xdoc::topstring) for details on how the tags are treated.
   </p>"

  (mutual-recursion

   (defun xdoc::treep (x)
     (or (stringp x)
         (and (true-listp x)
              (consp x)
              (keywordp (car x))
              (xdoc::tree-listp (cdr x)))))

   (defun xdoc::tree-listp (x)
     (cond ((atom x) (eq x nil))
           (t (and (xdoc::treep (car x))
                   (xdoc::tree-listp (cdr x)))))))

  (defthm xdoc::treep-when-stringp
    (implies (stringp x)
             (xdoc::treep x)))

  (defthm xdoc::treep-of-cons
    (equal (xdoc::treep (cons x y))
           (and (keywordp x)
                (xdoc::tree-listp y))))

  (defthm xdoc::tree-listp-when-string-listp
    (implies (string-listp x)
             (xdoc::tree-listp x)))

  (defthm xdoc::tree-listp-of-cons
    (equal (xdoc::tree-listp (cons x y))
           (and (xdoc::treep x)
                (xdoc::tree-listp y))))

  (in-theory (disable xdoc::treep xdoc::tree-listp)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection xdoc::li-treep
  :short "Recognize XDOC trees for HTML list items
          in an HTML unordered or ordered list."

  (defun xdoc::li-treep (x)
    (and (xdoc::treep x)
         (consp x)
         (eq (car x) :li)))

  (defun xdoc::li-tree-listp (x)
    (cond ((atom x) (eq x nil))
          (t (and (xdoc::li-treep (car x))
                  (xdoc::li-tree-listp (cdr x))))))

  (defthm xdoc::treep-when-li-treep
    (implies (xdoc::li-treep x)
             (xdoc::treep x)))

  (defthm xdoc::tree-listp-when-li-tree-listp
    (implies (xdoc::li-tree-listp x)
             (xdoc::tree-listp x)))

  (defthm xdoc::li-treep-of-cons
    (equal (xdoc::li-treep (cons x y))
           (and (eq x :li)
                (xdoc::tree-listp y))))

  (defthm xdoc::li-tree-listp-of-cons
    (equal (xdoc::li-tree-listp (cons x y))
           (and (xdoc::li-treep x)
                (xdoc::li-tree-listp y))))

  (in-theory (disable xdoc::li-treep xdoc::li-tree-listp)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection xdoc::dt/dd-treep
  :short "Recognize XDOC trees for HTML terms or descriptions
          in an HTML description list."

  (defun xdoc::dt/dd-treep (x)
    (and (xdoc::treep x)
         (consp x)
         (or (eq (car x) :dt)
             (eq (car x) :dd))))

  (defun xdoc::dt/dd-tree-listp (x)
    (cond ((atom x) (eq x nil))
          (t (and (xdoc::dt/dd-treep (car x))
                  (xdoc::dt/dd-tree-listp (cdr x))))))

  (defthm xdoc::treep-when-dt/dd-treep
    (implies (xdoc::dt/dd-treep x)
             (xdoc::treep x)))

  (defthm xdoc::tree-listp-when-dt/dd-tree-listp
    (implies (xdoc::dt/dd-tree-listp x)
             (xdoc::tree-listp x)))

  (defthm xdoc::dt/dd-treep-of-cons
    (equal (xdoc::dt/dd-treep (cons x y))
           (and (or (eq x :dt)
                    (eq x :dd))
                (xdoc::tree-listp y))))

  (defthm xdoc::dt/dd-tree-listp-of-cons
    (equal (xdoc::dt/dd-tree-listp (cons x y))
           (and (xdoc::dt/dd-treep x)
                (xdoc::dt/dd-tree-listp y))))

  (in-theory (disable xdoc::dt/dd-treep xdoc::dt/dd-tree-listp)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection xdoc::make-tree
  :short "Construct a non-leaf XDOC tree with the given tag and subtrees."
  :long
  "<p>
   This is more an internal function than an API function
   of this library of XDOC constructors.
   Using this function instead of @(tsee cons) ensures that
   the arguments have the right types (via the guard)
   and the result is an XDOC tree (proved as a theorem).
   It also provides a bit of abstraction over
   the representation of XDOC trees.
   </p>"

  (defun xdoc::make-tree (tag trees)
    (declare (xargs :guard (and (keywordp tag) (xdoc::tree-listp trees))))
    (cons tag trees))

  (defthm xdoc::treep-of-make-tree
    (equal (xdoc::treep (xdoc::make-tree tag trees))
           (and (keywordp tag)
                (xdoc::tree-listp trees))))

  (defthm xdoc::li-treep-of-make-tree
    (equal (xdoc::li-treep (xdoc::make-tree tag trees))
           (and (eq tag :li)
                (xdoc::tree-listp trees))))

  (defthm xdoc::dt/dd-treep-of-make-tree
    (equal (xdoc::dt/dd-treep (xdoc::make-tree tag trees))
           (and (or (eq tag :dt)
                    (eq tag :dd))
                (xdoc::tree-listp trees))))

  (in-theory (disable xdoc::make-tree)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection xdoc::*newline*
  :short "The string consisting of exactly the newline character."
  (defconst xdoc::*newline*
    (coerce (list #\Newline) 'string)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection xdoc::h1
  :short "Construct an XDOC tree for
          an HTML level-1 heading @('\<h1\>...\</h1\>')
          from a string."
  :long "@(def xdoc::h1)"

  (defund xdoc::h1-fn (string)
    (declare (xargs :guard (stringp string)))
    (xdoc::make-tree :h1 (list string)))

  (defmacro xdoc::h1 (string)
    `(xdoc::h1-fn ,string)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection xdoc::h2
  :short "Construct an XDOC tree for
          an HTML level-2 heading @('\<h2\>...\</h2\>')
          from a string."
  :long "@(def xdoc::h2)"

  (defund xdoc::h2-fn (string)
    (declare (xargs :guard (stringp string)))
    (xdoc::make-tree :h2 (list string)))

  (defmacro xdoc::h2 (string)
    `(xdoc::h2-fn ,string)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection xdoc::h3
  :short "Construct an XDOC tree for
          an HTML level-3 heading @('\<h3\>...\</h3\>')
          from a string."
  :long "@(def xdoc::h3)"

  (defund xdoc::h3-fn (string)
    (declare (xargs :guard (stringp string)))
    (xdoc::make-tree :h3 (list string)))

  (defmacro xdoc::h3 (string)
    `(xdoc::h3-fn ,string)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection xdoc::h4
  :short "Construct an XDOC tree for
          an HTML level-4 heading @('\<h4\>...\</h4\>')
          from a string."
  :long "@(def xdoc::h4)"

  (defund xdoc::h4-fn (string)
    (declare (xargs :guard (stringp string)))
    (xdoc::make-tree :h4 (list string)))

  (defmacro xdoc::h4 (string)
    `(xdoc::h4-fn ,string)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection xdoc::h5
  :short "Construct an XDOC tree for
          an HTML level-5 heading @('\<h5\>...\</h5\>')
          from a string."
  :long "@(def xdoc::h5)"

  (defund xdoc::h5-fn (string)
    (declare (xargs :guard (stringp string)))
    (xdoc::make-tree :h5 (list string)))

  (defmacro xdoc::h5 (string)
    `(xdoc::h5-fn ,string)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection xdoc::p
  :short "Construct an XDOC tree for
          an HTML paragraph @('\<p\>...\</p\>')
          from a string."
  :long "@(def xdoc::p)"

  (defund xdoc::p-fn (string)
    (declare (xargs :guard (stringp string)))
    (xdoc::make-tree :p (list string)))

  (defmacro xdoc::p (string)
    `(xdoc::p-fn ,string)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection xdoc::blockquote
  :short "Construct an XDOC tree for
          an HTML quoted block @('\<blockquote\>...\</blockquote\>')
          from a sequence of XDOC trees subtrees."
  :long "@(def xdoc::blockquote)"
  (defmacro xdoc::blockquote (&rest trees)
    `(xdoc::make-tree :blockquote (list ,@trees))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection xdoc::li
  :short "Construct an XDOC tree for
          an HTML list item @('\<li\>...\</li\>')
          from a sequence of XDOC subtrees."
  :long "@(def xdoc::li)"
  (defmacro xdoc::li (&rest trees)
    `(xdoc::make-tree :li (list ,@trees))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection xdoc::ul
  :short "Construct an XDOC tree for
          an HTML unordered list @('\<ul\>...\</ul\>')
          from a sequence of XDOC subtrees for HTML list items."
  :long "@(def xdoc::ul)"

  (defund xdoc::ul-fn (trees)
    (declare (xargs :guard (xdoc::li-tree-listp trees)))
    (xdoc::make-tree :ul trees))

  (defmacro xdoc::ul (&rest trees)
    `(xdoc::ul-fn (list ,@trees))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection xdoc::ol
  :short "Construct an XDOC tree for
          an HTML ordered list @('\<ol\>...\</ol\>')
          from a sequence of XDOC subtrees for HTML list items."
  :long "@(def xdoc::ol)"

  (defund xdoc::ol-fn (trees)
    (declare (xargs :guard (xdoc::li-tree-listp trees)))
    (xdoc::make-tree :ol trees))

  (defmacro xdoc::ol (&rest trees)
    `(xdoc::ol-fn (list ,@trees))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection xdoc::dt
  :short "Construct an XDOC tree for
          an HTML term @('\<dt\>...\</dt\>')
          from a string."
  :long "@(def xdoc::dt)"

  (defund xdoc::dt-fn (string)
    (declare (xargs :guard (stringp string)))
    (xdoc::make-tree :dt (list string)))

  (defmacro xdoc::dt (string)
    `(xdoc::dt-fn ,string)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection xdoc::dd
  :short "Construct an XDOC tree for
          an HTML description @('\<dd\>...\</dd\>')
          from a sequence of XDOC subtrees."
  :long "@(def xdoc::dd)"
  (defmacro xdoc::dd (&rest trees)
    `(xdoc::make-tree :dd (list ,@trees))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection xdoc::dl
  :short "Construct an XDOC tree for
          an HTML description list @('\<dl\>...\</dl\>')
          from a sequence of XDOC tree for HTML terms and descriptions."
  :long "@(def xdoc::dl)"

  (defund xdoc::dl-fn (trees)
    (declare (xargs :guard (xdoc::dt/dd-tree-listp trees)))
    (xdoc::make-tree :dl trees))

  (defmacro xdoc::dl (&rest trees)
    `(xdoc::dl-fn (list ,@trees))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection xdoc::&&
  :short "Construct an XDOC tree for
          a sequence of subtrees to treat as a single tree."
  :long "@(def xdoc::&&)"
  (defmacro xdoc::&& (&rest trees)
    `(xdoc::make-tree :&& (list ,@trees))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection xdoc::@{}
  :short "Construct an XDOC tree for
          a preformatted code block @('@({...})')
          from a string."
  :long
  "<p>
   See @(tsee xdoc::@code) for a higher-level XDOC constructor
   for preformatted code blocks.
   </p>
   @(def xdoc::@{})"

  (defund xdoc::@{}-fn (string)
    (declare (xargs :guard (stringp string)))
    (xdoc::make-tree :@{} (list string)))

  (defmacro xdoc::@{} (string)
    `(xdoc::@{}-fn ,string)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection xdoc::@code
  :short "Construct an XDOC tree for
          a preformatted code block @('@({...})')
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
   @(def xdoc::@code)"

  (defun xdoc::@code-terminate-lines (lines)
    (declare (xargs :guard (string-listp lines)))
    (cond ((endp lines) nil)
          (t (list* (car lines)
                    xdoc::*newline*
                    (xdoc::@code-terminate-lines (cdr lines))))))

  (defthm xdoc::string-listp-of-@code-terminate-lines
    (implies (string-listp lines)
             (string-listp (xdoc::@code-terminate-lines lines))))

  (in-theory (disable xdoc::@code-terminate-lines))

  (defund xdoc::@code-fn (lines)
    (declare (xargs :guard (string-listp lines)))
    (xdoc::make-tree :@{} (cons xdoc::*newline*
                                (xdoc::@code-terminate-lines lines))))

  (defmacro xdoc::@code (&rest lines)
    `(xdoc::@code-fn (list ,@lines))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection xdoc::desc
  :short "Construct an XDOC tree for a description."
  :long
  "<p>
   This is an HTML description list
   with a (sequence of) term(s) and a description.
   It is a higher-level XDOC constructor,
   which combines lower-level ones into one
   that may be more convenient to use.
   </p>
   <p>
   The first argument is either a string for a single term
   or a list of strings for a sequence of terms.
   </p>
   @(def xdoc::desc)"

  (defun xdoc::desc-make-dt-trees (strings)
    (declare (xargs :guard (string-listp strings)))
    (cond ((endp strings) nil)
          (t (cons (xdoc::make-tree :dt (list (car strings)))
                   (xdoc::desc-make-dt-trees (cdr strings))))))

  (defthm xdoc::dt/dd-tree-listp-of-desc-make-dt-trees
    (implies (string-listp strings)
             (xdoc::dt/dd-tree-listp (xdoc::desc-make-dt-trees strings))))

  (defund xdoc::desc-fn (dt-part dd-part)
    (declare (xargs :guard (and (or (stringp dt-part)
                                    (string-listp dt-part))
                                (xdoc::tree-listp dd-part))))
    (let* ((dt-part (if (stringp dt-part) (list dt-part) dt-part))
           (dt-trees (xdoc::desc-make-dt-trees dt-part))
           (dd-tree (xdoc::make-tree :dd dd-part)))
      (xdoc::make-tree :dl (append dt-trees (list dd-tree)))))

  (defmacro xdoc::desc (dt-part &rest dd-part)
    `(xdoc::desc-fn ,dt-part (list ,@dd-part))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection xdoc::topstring
  :short "Turn a list of XDOC trees into the string they represent."
  :long
  "<p>
   An XDOC string has typically the form
   @({
     <p>a paragraph</p>
     <p>another paragraph</p>
     <ul>
       <li>an item</li>
       <li>another item</li>
     </ul>
     <p>and so on</p>
   })
   i.e. it is a sequence of HTML paragraphs, lists, etc.
   There is no top-level tag
   (unlike, say, the @('<html>') tag of HTML pages).
   </p>
   <p>
   This function can be thought of as a top-level tag for XDOC strings,
   i.e. something like
   @({
     <top>
       <p>a paragraph</p>
       <p>another paragraph</p>
       <ul>
         <li>an item</li>
         <li>another item</li>
       </ul>
       <p>and so on</p>
     </top>
   })
   However, this function does not construct an XDOC tree,
   but rather the flat string that the sequence of XDOC trees represent.
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
   An XDOC tree is turned into a string as follows.
   A leaf tree is already a string and is left unchanged.
   For a non-leaf tree, the subtrees are recursively turned into strings
   and concatenated;
   then the resulting string is surrounded by an opening and closing tag
   (with a newline just after each of the opening and closing tags)
   derived directly from the keyword at the root of the tree.
   There are two special cases:
   (i) if the keyword at the root of the tree is @(':@{}'),
   then @('@({') is used as opening ``tag''
   and @('})') is used as closing ``tag'';
   (ii) if the keyword at the root of the tree is @(':&&'),
   then no opening or closing tags are added.
   </p>
   <p>
   The @(tsee symbol-name) of a keyword tag consists of uppercase letters.
   In order to turn those into lowercase letters,
   all the characters must satisfy @(tsee standard-char-p).
   This is always the case for the tags we use,
   but since the definition of XDOC trees allows arbitrary keywords,
   we introduce a conversion function from tags to strings
   that returns the empty string if any characters in the tag name
   are non-standard.
   </p>
   <p>
   At the top-level, the list of XDOC trees
   is treated as if they were subtrees
   (i.e. recursively turned into strings and concatenated,
   separated by newline characters),
   but without adding any tag around the whole thing.
   </p>
   @(def xdoc::topstring)"

  (defund xdoc::tag-to-string (tag)
    (declare (xargs :guard (keywordp tag)))
    (let* ((tag-string (symbol-name tag))
           (tag-chars (coerce tag-string 'list)))
      (if (standard-char-listp tag-chars)
          (string-downcase tag-string)
        "")))

  (mutual-recursion

   (defun xdoc::topstring-fn (tree)
     (declare (xargs ::guard (xdoc::treep tree)
                     :verify-guards nil)) ; done below
     (cond ((atom tree) tree)
           (t (let* ((substring (xdoc::topstring-fn-list (cdr tree)))
                     (tag (car tree))
                     (open (case tag
                             (:&& "")
                             (:@{} (concatenate 'string
                                                "@({"
                                                xdoc::*newline*))
                             (t (concatenate 'string
                                             "<"
                                             (xdoc::tag-to-string tag)
                                             ">"
                                             xdoc::*newline*))))
                     (close (case tag
                              (:&& "")
                              (:@{} (concatenate 'string
                                                 "})"
                                                 xdoc::*newline*))
                              (t (concatenate 'string
                                              "</"
                                              (xdoc::tag-to-string tag)
                                              ">"
                                              xdoc::*newline*)))))
                (concatenate 'string open substring close)))))

   (defun xdoc::topstring-fn-list (trees)
     (declare (xargs :guard (xdoc::tree-listp trees)))
     (cond ((endp trees) "")
           (t (concatenate 'string
                           (xdoc::topstring-fn (car trees))
                           (xdoc::topstring-fn-list (cdr trees)))))))

  (make-flag flag-xdoc-top-fn xdoc::topstring-fn)

  (defthm-flag-xdoc-top-fn
    (defthm xdoc::theorem-for-top-fn
      (implies (xdoc::treep tree)
               (stringp (xdoc::topstring-fn tree)))
      :flag xdoc::topstring-fn)
    (defthm xdoc::theorem-for-top-fn-list
      (implies (xdoc::tree-listp trees)
               (stringp (xdoc::topstring-fn-list trees)))
      :flag xdoc::topstring-fn-list)
    :hints (("Goal" :in-theory (enable xdoc::treep))))

  (verify-guards xdoc::topstring-fn
    :hints (("Goal" :in-theory (enable xdoc::tree-listp))))

  (in-theory (disable xdoc::topstring-fn xdoc::topstring-fn-list))

  (defmacro xdoc::topstring (&rest trees)
    `(xdoc::topstring-fn-list (list ,@trees))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection xdoc::toppstring
  :short "Construct a top-level XDOC paragraph from a string."
  :long
  "<p>
   This abbreviates @(tsee xdoc::topstring) applied to a single @(tsee xdoc::p).
   It is useful for more compact writing of
   XDOC strings that consist of single paragraphs.
   In this case, one could just write
   @('\"<p>...</p>\"') instead of @('(xdoc::toppstring \"...\")'),
   but the latter may be more error-prone
   in the sense that closing tag may be forgotten.
   </p>
   @(def xdoc::toppstring)"
  (defmacro xdoc::toppstring (string)
    `(xdoc::topstring (xdoc::p ,string))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The following functions and macros are temporary.
; They are here for compatibility with some books
; that use the old XDOC constructors.
; When all the books are changed to use the new XDOC constructors above,
; the following functions and macros will be removed.

(defmacro xdoc::textp (x)
  `(xdoc::treep ,x))

(defmacro xdoc::app (&rest args)
  `(xdoc::&& ,@args))

(defmacro xdoc::p* (&rest args)
  `(xdoc::p ,@args))

(defmacro xdoc::li* (&rest args)
  `(xdoc::li ,@args))

(defmacro xdoc::topapp (&rest args)
  `(xdoc::topstring ,@args))

(defmacro xdoc::topp (&rest args)
  `(xdoc::toppstring ,@args))

(defmacro xdoc::code (&rest args)
  `(xdoc::@code ,@args))

(defund xdoc::img (src)
  (declare (xargs :guard (stringp src)))
  (concatenate 'string "<img src=\"" src "\"/>"))

(defund xdoc::def (name)
  (declare (xargs :guard (stringp name)))
  (concatenate 'string "@(def " name ")"))
