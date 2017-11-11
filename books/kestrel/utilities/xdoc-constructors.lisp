; XDOC Constructors
;
; Copyright (C) 2017 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "xdoc/top" :dir :system)
(include-book "std/util/define" :dir :system)
(include-book "std/strings/cat" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc xdoc::xdoc-constructors
  :parents (kestrel-utilities)
  :short "Utilities to costruct
          well-tagged <see topic='@(url xdoc)'>XDOC</see> strings."
  :long
  "<p>
   XDOC strings use XML tags, which must be properly matched and nested.
   The XDOC constructors provided here are functions
   that surround their argument strings with various XML tags,
   ensuring proper matching and nesting.
   At the top level, @(tsee str::cat) can be used
   to put tagged text blocks into a sequence (e.g. in a @(':long')).
   </p>")

(define xdoc::tag ((tag-name stringp) (text stringp))
  :returns (tagged-text stringp)
  :parents (xdoc::xdoc-constructors)
  :short "Surround the given text with a tag with the given name."
  :long
  "<p>
   Two new line characters are added at the end,
   producing a blank line to improve readability
   when the resulting string is combined with others in sequence.
   </p>"
  (b* ((open-angle (coerce (list #\<) 'string))
       (close-angle (coerce (list #\>) 'string))
       (slash (coerce (list #\/) 'string))
       (open-tag (str::cat open-angle tag-name close-angle))
       (close-tag (str::cat open-angle slash tag-name close-angle))
       (newline (coerce (list #\Newline) 'string)))
    (str::cat open-tag text close-tag newline newline)))

(define xdoc::h1 ((text stringp))
  :returns (tagged-text stringp)
  :parents (xdoc::xdoc-constructors)
  :short "Build an XML level-1 heading @('\<h1\>...\</h1\>')."
  (xdoc::tag "h1" text))

(define xdoc::h2 ((text stringp))
  :returns (tagged-text stringp)
  :parents (xdoc::xdoc-constructors)
  :short "Build an XML level-2 heading @('\<h2\>...\</h2\>')."
  (xdoc::tag "h2" text))

(define xdoc::h3 ((text stringp))
  :returns (tagged-text stringp)
  :parents (xdoc::xdoc-constructors)
  :short "Build an XML level-3 heading @('\<h3\>...\</h3\>')."
  (xdoc::tag "h3" text))

(define xdoc::h4 ((text stringp))
  :returns (tagged-text stringp)
  :parents (xdoc::xdoc-constructors)
  :short "Build an XML level-4 heading @('\<h4\>...\</h4\>')."
  (xdoc::tag "h4" text))

(define xdoc::h5 ((text stringp))
  :returns (tagged-text stringp)
  :parents (xdoc::xdoc-constructors)
  :short "Build an XML level-5 heading @('\<h5\>...\</h5\>')."
  (xdoc::tag "h5" text))

(define xdoc::p ((text stringp))
  :returns (tagged-text stringp)
  :parents (xdoc::xdoc-constructors)
  :short "Build an XML paragraph @('\<p\>...\</p\>')."
  (xdoc::tag "p" text))

(define xdoc::li ((text stringp))
  :returns (tagged-text stringp)
  :parents (xdoc::xdoc-constructors)
  :short "Build an XML list item @('\<li\>...\</li\>')."
  (xdoc::tag "li" text))

(defsection xdoc::ul
  :parents (xdoc::xdoc-constructors)
  :short "Build an XML unordered list @('\<ul\>...\</ul\>')."
  :long "@(def xdoc::ul)"
  (defmacro xdoc::ul (&rest items)
    `(xdoc::tag "ul" (str::cat ,@items))))

(defsection xdoc::ol
  :parents (xdoc::xdoc-constructors)
  :short "Build an XML ordered list @('\<ol\>...\</ol\>')."
  :long "@(def xdoc::ol)"
  (defmacro xdoc::ol (&rest items)
    `(xdoc::tag "ol" (str::cat ,@items))))

(defsection xdoc::blockquote
  :parents (xdoc::xdoc-constructors)
  :short "Build an XML quoted block @('\<blockquote\>...\</blockquote\>')."
  :long "@(def xdoc::blockquote)"
  (defmacro xdoc::blockquote (&rest items)
    `(xdoc::tag "blockquote" (str::cat ,@items))))

(defsection xdoc::code
  :parents (xdoc::xdoc-constructors)
  :short "Build an XML preformatted code block @('@({...})')."
  :long
  "<p>
   The arguments must be the lines of the code block,
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
    (cond ((endp unterminated-lines) (rev reversed-current-terminated-lines))
          (t (b* ((unterminated-line (car unterminated-lines))
                  (terminated-line (str::cat unterminated-line
                                             (coerce '(#\Newline) 'string))))
               (xdoc::terminate-lines
                (cdr unterminated-lines)
                (cons terminated-line reversed-current-terminated-lines))))))

  (defmacro xdoc::code (&rest lines)
    (let ((newline (coerce (list #\Newline) 'string))
          (lines (xdoc::terminate-lines lines nil)))
      `(str::cat "@({" ,newline ,@lines "})" ,newline ,newline))))

(defsection xdoc::desc
  :parents (xdoc::xdoc-constructors)
  :short "Build a description."
  :long
  "<p>
   The description consists of
   an XML paragraph that identifies the thing being described
   and a sequence of XML paragraphs, lists, and similar structures
   that describe the thing and that are in a quoted block.
   This macro takes as arguments:
   text that identifies the thing,
   which the macro surrounds with XML paragraph tags;
   and a variable number of XML structures that describe the thing,
   which the macro surrounds with XML quoted block tags.
   </p>
   <p>
   The thing could be, for example, the input to a macro.
   The text that identifies the input could be a short line,
   namely the name of the input (perhaps with an indication of a default value).
   </p>"
  (defmacro xdoc::desc (desc-id &rest desc-items)
    `(str::cat (xdoc::p ,desc-id)
               (xdoc::blockquote ,@desc-items))))
