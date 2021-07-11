; Computational Object Inference
; Copyright (C) 2005-2014 Kookamara LLC
;
; Contact:
;
;   Kookamara LLC
;   11410 Windermere Meadows
;   Austin, TX 78759, USA
;   http://www.kookamara.com/
;
; License: (An MIT/X11-style license)
;
;   Permission is hereby granted, free of charge, to any person obtaining a
;   copy of this software and associated documentation files (the "Software"),
;   to deal in the Software without restriction, including without limitation
;   the rights to use, copy, modify, merge, publish, distribute, sublicense,
;   and/or sell copies of the Software, and to permit persons to whom the
;   Software is furnished to do so, subject to the following conditions:
;
;   The above copyright notice and this permission notice shall be included in
;   all copies or substantial portions of the Software.
;
;   THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
;   IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
;   FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
;   AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
;   LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
;   FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
;   DEALINGS IN THE SOFTWARE.

(in-package "ACL2")

(include-book "xdoc/top" :dir :system)

;;====================================================================
;;
;; The def::doc wrapper around defdoc.  We really need to understand
;; better how package names work with documentation.  It would also
;; be good to know how to generate .html files from documentation.
;;
;;====================================================================

;;; Legacy documentation has been superseded Nov. 2014 by the use of
;;; auto-generated defxdoc forms in the respective files.
; (defmacro def::doc (name &key (section 'nil) (one-liner '"") (notes '"") (details 'nil))
;   (let ((section (or (and section (if (symbolp section) (symbol-name section) section)) (symbol-name name)))
;         (details (or details (symbol-name name))))
;     (let ((doc `(concatenate 'string
;
; ":Doc-Section " ,section "
; "
; ,one-liner
; "~/"
; ,notes
; "~/"
; ,details
; "
; "
;
; )))
;       `(make-event
;         `(DEFDOC ,',name ,,doc)))))


;;====================================================================
;;
;; Here are some functions for constructing fancy documentation.
;; Perhaps we shouldn just put documentation support into a separate
;; "doc" package.
;;
;;====================================================================

(defmacro docstring (&rest args)
  `(concatenate 'string ,@args))

(defun href (x)
  (concatenate 'string "~il[" x "]"))

(defun docref (x)
  (concatenate 'string "~l[" x "]"))

(defun \n () "~nl[]")

(defun verbatim (x)
  (concatenate 'string "~bv[]" x "~ev[]"))

(defun quoted (x)
  (concatenate 'string "~bq[]" x "~eq[]"))

;;====================================================================
;;
;; Here is an example of using "document" to document itself,
;; including the use of some fancy features.  Use :doc def::doc
;; to see how ACL2 renders the following documentation.
;;
;; We should probably document the fancy documentation strings, too.
;;
;;====================================================================


;;; The following legacy doc string was replaced Nov. 2014 by the
;;; auto-generated defxdoc form just below.
; (def::doc def::doc
;
;   :section def::doc
;
;   :one-liner "A simple macro for easing the documentation process"
;
;   :details (docstring
; "
;
;   The def::doc macro eases the process of constructing documentation
; strings for ACL2 symbols. "(docref"doc")".  Macro keywords are used to
; identify content for each of the primary documentation elements:
;
; "(verbatim"
; :section     Either a symbol or string identifying the section
; :one-liner   A simple one-line overview of the symbol
; :notes       Notes related to this symbol
; :details     Documentation details about the symbol
; ")
; (\n) ;; Note how this newline appears in the output of :doc ..
; "
;   The string arguments used by the macro can be computed, allowing the
; user to use functions as abbreviations for common and unwieldly
; documentation constructs.
; "
; ))

(defxdoc def::doc
  :parents (acl2::miscellaneous)
  :short "A simple macro for easing the documentation process"
  :long "<p>The def::doc macro eases the process of constructing documentation
 strings for ACL2 symbols. See @(see doc).  Macro keywords are used to identify
 content for each of the primary documentation elements:</p>

 @({
  :section     Either a symbol or string identifying the section
  :one-liner   A simple one-line overview of the symbol
  :notes       Notes related to this symbol
  :details     Documentation details about the symbol
 })

 <p><br></br>

   The string arguments used by the macro can be computed, allowing the user to
 use functions as abbreviations for common and unwieldly documentation
 constructs.</p>")
