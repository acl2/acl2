; XDOC Constructors
;
; Copyright (C) 2018 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "std/util/define" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc xdoc::xdoc-constructors
  :parents (kestrel-utilities)
  :short "Utilities to costruct
          well-tagged <see topic='@(url xdoc)'>XDOC</see> strings."
  :long
  "<p>
   XDOC strings use XML tags, which must be properly matched and nested.
   The XDOC constructors provided here help build XML strings
   with properly matched and nested tags.
   </p>
   <p>
   As noted <see topic='@(url str::concatenation)'>here</see>,
   string concatenation is slow in ACL2 in general.
   These XDOC constructors currently use string concatenation,
   but they are written in a way that
   they can be easily made more efficient in the future,
   if concatenating strings turns out to be too slow
   in the actual use of these XDOC constructors.
   </p>
   <p>
   Specifically, a recognizer @(tsee xdoc::textp) is provided
   that is currently a synonym of @(tsee stringp)
   but could be changed to be something else in the future.
   The ``bottom'' XDOC constructors (e.g. @(tsee xdoc::p))
   map strings to @('xdoc::textp') values.
   The ``intermediate'' XDOC constructors (e.g. @(tsee xdoc::app))
   map @('xdoc::textp') values to @('xdoc::textp') values.
   The ``top'' XDOC constructor (i.e. @(tsee xdoc::topapp))
   maps @('xdoc::textp') values to strings.
   If these XDOC constructors are used properly,
   without bypassing the (non-enforced) @('xdoc::textp') abstraction,
   (e.g. by using @(tsee concatenate) directly)
   then changing the internal representation of @('xdoc::textp')
   and the definition of the XDOC constructors accordingly
   should require no change in calling code.
   In particular, a @(':long') should be always followed by
   a call to @(tsee xdoc::topapp).
   </p>")

(define xdoc::textp (x)
  :parents (xdoc::xdoc-constructors)
  :short "Recognize XDOC text."
  :long
  "<p>
   See the discussion <see topic='@(url xdoc::xdoc-constructors)'>here</see>
   about the current vs. possible future implementation.
   </p>"
  (stringp x))

(define xdoc::text ((string stringp))
  :returns (text xdoc::textp
                 :hyp :guard
                 :hints (("Goal" :in-theory (enable xdoc::textp))))
  :parents (xdoc::xdoc-constructors)
  :short "Turn a string into XDOC text."
  :long
  "<p>
   This is currently the identity function
   because @(tsee xdoc::textp) is currently a synonym of @(tsee stringp),
   but if the definition of @(tsee xdoc::textp) changes at some point,
   this function will be changed accordingly.
   See the discussion <see topic='@(url xdoc::xdoc-constructors)'>here</see>
   about the current vs. possible future implementation.
   </p>"
  string)

(defsection xdoc::app
  :parents (xdoc::xdoc-constructors)
  :short "Concatenate zero or more pieces of XDOC text,
          at an intermediate level."
  :long
  "<p>
   The arguments are evaluated and must return @(tsee xdoc::textp) values;
   the result is a @(tsee xdoc::textp) value.
   </p>
   <p>
   This must not be used at the top level, i.e. just after @(':long').
   It must be used only to concatenate text at an intermediate level.
   See also @(tsee xdoc::topapp).
   </p>
   @(def xdoc::app)"
  (defmacro xdoc::app (&rest pieces)
    `(concatenate 'string ,@pieces)))

(defsection xdoc::topapp
  :parents (xdoc::xdoc-constructors)
  :short "Concatenate zero or more pieces of XDOC text, at the top level."
  :long
  "<p>
   The arguments are evaluated and must return @(tsee xdoc::textp) values;
   the result is a string.
   </p>
   <p>
   This must be used only at the top level, i.e. just after @(':long').
   It must not be used when
   See also @(tsee xdoc::app).
   </p>
   @(def xdoc::topapp)"
  (defmacro xdoc::topapp (&rest pieces)
    `(concatenate 'string ,@pieces)))

(define xdoc::tag ((tag-name stringp) (text xdoc::textp))
  :returns (text1 xdoc::textp :hints (("Goal" :in-theory (enable xdoc::textp))))
  :parents (xdoc::xdoc-constructors)
  :short "Surround the given text with a tag with the given name."
  :long
  "<p>
   Two new line characters are added at the end,
   producing a blank line to improve readability
   when the resulting text is concatenated with other text.
   </p>"
  (b* ((open-angle (coerce (list #\<) 'string))
       (close-angle (coerce (list #\>) 'string))
       (slash (coerce (list #\/) 'string))
       (open-tag (concatenate 'string open-angle tag-name close-angle))
       (close-tag (concatenate 'string open-angle slash tag-name close-angle))
       (newline (coerce (list #\Newline) 'string)))
    (concatenate 'string open-tag text close-tag newline newline))
  :guard-hints (("Goal" :in-theory (enable xdoc::textp))))

(define xdoc::h1 ((string stringp))
  :returns (text xdoc::textp)
  :parents (xdoc::xdoc-constructors)
  :short "Build an XML level-1 heading @('\<h1\>...\</h1\>')."
  :long
  "<p>
   The argument is a string, and not a @(tsee xdoc::textp) value,
   because a heading is expected to be ``atomic''.
   </p>"
  (xdoc::tag "h1" (xdoc::text string)))

(define xdoc::h2 ((string stringp))
  :returns (text xdoc::textp)
  :parents (xdoc::xdoc-constructors)
  :short "Build an XML level-2 heading @('\<h2\>...\</h2\>')."
  :long
  "<p>
   The argument is a string, and not a @(tsee xdoc::textp) value,
   because a heading is expected to be ``atomic''.
   </p>"
  (xdoc::tag "h2" (xdoc::text string)))

(define xdoc::h3 ((string stringp))
  :returns (text xdoc::textp)
  :parents (xdoc::xdoc-constructors)
  :short "Build an XML level-3 heading @('\<h3\>...\</h3\>')."
  :long
  "<p>
   The argument is a string, and not a @(tsee xdoc::textp) value,
   because a heading is expected to be ``atomic''.
   </p>"
  (xdoc::tag "h3" (xdoc::text string)))

(define xdoc::h4 ((string stringp))
  :returns (text xdoc::textp)
  :parents (xdoc::xdoc-constructors)
  :short "Build an XML level-4 heading @('\<h4\>...\</h4\>')."
  :long
  "<p>
   The argument is a string, and not a @(tsee xdoc::textp) value,
   because a heading is expected to be ``atomic''.
   </p>"
  (xdoc::tag "h4" (xdoc::text string)))

(define xdoc::h5 ((string stringp))
  :returns (text xdoc::textp)
  :parents (xdoc::xdoc-constructors)
  :short "Build an XML level-5 heading @('\<h5\>...\</h5\>')."
  :long
  "<p>
   The argument is a string, and not a @(tsee xdoc::textp) value,
   because a heading is expected to be ``atomic''.
   </p>"
  (xdoc::tag "h5" (xdoc::text string)))

(define xdoc::p ((string stringp))
  :returns (text xdoc::textp)
  :parents (xdoc::xdoc-constructors)
  :short "Build an XML paragraph @('\<p\>...\</p\>') from a string."
  :long
  "<p>
   The paragraph just contains the string, i.e. it is ``atomic''.
   </p>
   <p>
   Use @(tsee xdoc::p*) to build non-``atomic'' paragraphs.
   </p>"
  (xdoc::tag "p" (xdoc::text string)))

(defsection xdoc::p*
  :parents (xdoc::xdoc-constructors)
  :short "Build an XML paragraph @('\<p\>...\</p\>') from
          zero or more pieces of XDOC text."
  :long
  "<p>
   The arguments are evaluated and must return @(tsee xdoc::textp) values,
   which are concatenated into a resulting @(tsee xdoc::textp) value.
   </p>
   <p>
   Use @(tsee xdoc::p) to build ``atomic'' paragraphs.
   </p>
   @(def xdoc::p*)"
  (defmacro xdoc::p* (&rest pieces)
    `(xdoc::tag "p" (concatenate 'string ,@pieces))))

(define xdoc::li ((string stringp))
  :returns (text xdoc::textp)
  :parents (xdoc::xdoc-constructors)
  :short "Build an XML list item @('\<li\>...\</li\>') from a string."
  :long
  "<p>
   The list item just contains the string, i.e. it is ``atomic''
   </p>
   <p>
   See @(tsee xdoc::li*) to build non-``atomic'' list items.
   </p>"
  (xdoc::tag "li" (xdoc::text string)))

(defsection xdoc::li*
  :parents (xdoc::xdoc-constructors)
  :short "Build an XML list item @('\<li\>...\</li\>') from
          zero or more pieces of XDOC text."
  :long
  "<p>
   The arguments are evaluated and must return @(tsee xdoc::textp) values,
   which are concatenated into a resulting @(tsee xdoc::textp) value.
   </p>
   <p>
   Use @(tsee xdoc::li) to build ``atomic'' list items.
   </p>
   @(def xdoc::li*)"
  (defmacro xdoc::li* (&rest pieces)
    `(xdoc::tag "li" (concatenate 'string ,@pieces))))

(defsection xdoc::ul
  :parents (xdoc::xdoc-constructors)
  :short "Build an XML unordered list @('\<ul\>...\</ul\>')."
  :long
  "<p>
   The arguments are evaluated and must return @(tsee xdoc::textp) values,
   which are concatenated into a resulting @(tsee xdoc::textp) value.
   The arguments are expected to be
   calls to @(tsee xdoc::li) or @(tsee xdoc::li*).
   </p>
   @(def xdoc::ul)"
  (defmacro xdoc::ul (&rest items)
    `(xdoc::tag "ul" (concatenate 'string ,@items))))

(defsection xdoc::ol
  :parents (xdoc::xdoc-constructors)
  :short "Build an XML ordered list @('\<ol\>...\</ol\>')."
  :long
  "<p>
   The arguments are evaluated and must return @(tsee xdoc::textp) values,
   which are concatenated into a resulting @(tsee xdoc::textp) value.
   The arguments are expected to be
   calls to @(tsee xdoc::li) or @(tsee xdoc::li*).
   </p>
   @(def xdoc::ol)"
  (defmacro xdoc::ol (&rest items)
    `(xdoc::tag "ol" (concatenate 'string ,@items))))

(defsection xdoc::blockquote
  :parents (xdoc::xdoc-constructors)
  :short "Build an XML quoted block @('\<blockquote\>...\</blockquote\>')."
  :long
  "<p>
   The arguments are evaluated and must return @(tsee xdoc::textp) values,
   which are concatenated into a @(tsee xdoc::textp) value
   that is tagged and returned.
   </p>
   @(def xdoc::blockquote)"
  (defmacro xdoc::blockquote (&rest items)
    `(xdoc::tag "blockquote" (concatenate 'string ,@items))))

(defsection xdoc::code
  :parents (xdoc::xdoc-constructors)
  :short "Build an XML preformatted code block @('@({...})')."
  :long
  "<p>
   The arguments must be strings that are the lines of the code block,
   starting with suitable spaces and with no ending new line characters.
   New line characters are automatically added at the end of each line.
   A new line character is also automatically added after the opening @('@({'),
   to ensure the proper formatting;
   a blank line is added after the closing @('})'),
   to improve readability
   when the resulting string is combined with others in sequence.
   </p>
   @(def xdoc::code)"

  (define xdoc::terminate-lines
    ((unterminated-lines string-listp)
     (reversed-current-terminated-lines string-listp))
    :returns (final-terminated-lines string-listp :hyp :guard)
    (cond ((endp unterminated-lines) (reverse
                                      reversed-current-terminated-lines))
          (t (b* ((unterminated-line (car unterminated-lines))
                  (terminated-line (concatenate 'string
                                                unterminated-line
                                                (coerce '(#\Newline) 'string))))
               (xdoc::terminate-lines
                (cdr unterminated-lines)
                (cons terminated-line reversed-current-terminated-lines)))))
    :prepwork
    ((local
      (defthm returns-lemma ; to prove the :RETURNS theorem above
        (implies (and (string-listp x)
                      (string-listp y))
                 (string-listp (revappend x y)))))))

  (defmacro xdoc::code (&rest lines)
    (declare (xargs :guard (string-listp lines)))
    (let ((newline (coerce (list #\Newline) 'string))
          (lines (xdoc::terminate-lines lines nil)))
      `(concatenate 'string "@({" ,newline ,@lines "})" ,newline ,newline))))

(defsection xdoc::desc
  :parents (xdoc::xdoc-constructors)
  :short "Build a description."
  :long
  "<p>
   The description consists of
   an XML paragraph that identifies the thing being described,
   followed by a sequence of XML paragraphs, lists, and other structures
   that describe the thing and that are in an XML quoted block.
   This macro takes as arguments:
   a string that identifies the thing,
   which is not evaluated and is surrounded with XML paragraph tags;
   and a variable number of XML structures that describe the thing,
   which are evaluated, concatenated, and surrounded with XML quoted block tags.
   </p>
   <p>
   For example, the thing could be the input to an event macro.
   The text that identifies the input could be a short line,
   namely the name of the input (perhaps with an indication of a default value).
   </p>"
  (defmacro xdoc::desc (desc-id &rest desc-items)
    (declare (xargs :guard (stringp desc-id)))
    `(concatenate 'string
                  (xdoc::p ,desc-id)
                  (xdoc::blockquote ,@desc-items))))

(define xdoc::img ((src stringp))
  :returns (text xdoc::textp :hints (("Goal" :in-theory (enable xdoc::textp))))
  :parents (xdoc::xdoc-constructors)
  :short "Build an XML image reference @('<img src=\"...\">')."
  :long
  "<p>
   The argument is the value for the @('src') attribute.
   </p>"
  (concatenate 'string "<img src=\"" src "\"/>"))

(define xdoc::def ((name stringp))
  :returns (text xdoc::textp :hints (("Goal" :in-theory (enable xdoc::textp))))
  :parents (xdoc::xdoc-constructors)
  :short "Build an XDOC definition directive."
  :long
  "<p>
   This is a @('@(def ...)') directive.
   The name is supplied as an argument.
   </p>"
  (concatenate 'string "@(def " name))
