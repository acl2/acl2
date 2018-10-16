; Copyright (C) 2018 Centaur Technology
;
; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/
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
;
; Original author: Sol Swords <sswords@centtech.com>




; Note about Emacs internals having to do with this file.  When emacs
; does syntax highlighting, skipping over s-expressions, etc, it is
; using a lightweight form of parsing that is implemented using syntax
; tables.  Syntax tables map characters to syntax types, which are
; categories like whitespace, string quote, open parenthesis, word
; constituents, etc.  This isn't quite adequate for everything,
; because some important syntactic elements consist of more than one
; character.  This is true of fancy-strings, since the opening
; delimiter is #{""" and closing delimiter is """}.

; To work around this, emacs allows specific occurrences of characters
; to be assigned their own syntax tables that differ from the general
; syntax table used for the rest of the buffer.  Specifically, if the
; variable parse-sexp-lookup-properties is set to t, then a text
; property called syntax-table is used instead of the buffer-global
; syntax table, when that property is set, on a per-character basis.
; A function syntax-propertize-function (when nonnil) is responsible
; for setting up this property on characters throughout a given range.
; Whenever a change is made in a buffer, syntax-propertize-function is
; called on a range including the changed location and extending some
; distance after.  Syntax-propertize-function is supposed to set the
; properties when necessary on the characters in that range.

; To do this correctly, we can interface with emacs's parser using the
; syntax-ppss function.  This returns the parse state at a position,
; which tells us whether we're inside a string or comment, nesting
; level of parens, etc.  The catch is that we shouldn't call it on any
; position until we've set up all our text properties up to that point
; -- syntax-ppss uses information from the properties we're setting
; up, so we need to do things in a monotonic order from the beginning
; to end of the buffer.

; So the way these functions work: we set the point to the start of
; the range we're given and check whether or not we're already inside
; a generic string (syntax-ppss tells us this).  If so, we're going to
; assume it's a fancystring (because the generic string syntax type
; isn't used for regular string quotes).  Whenever we're inside a
; fancystring we'll search for the end delimiter and mark it as a
; generic string quote to end the fancystring.  Whenever we're not
; inside a fancystring we'll search for the next fancystring opening
; delimiter that isn't already part of a string or comment and mark it
; as a generic string quote to start the fancystring.


; Change body to (cons 'message args) and resubmit the following
; functions to debug
(defmacro fancystring-debug (&rest args) nil)

; From emacs manual 35.4 Syntax Properties, if the 'syntax-table
; property of a character is a cons (syntax-code . matching-char),
; this directly specifies a syntax class for the character.  So here
; we set the 'syntax-table property of the close brace to (15 . nil),
; where 15 specifies "generic string delimiter" (from 35.7, Syntax
; Table Internals).
(defun set-generic-string-delimiter (pos)
  (put-text-property pos (+ 1 pos) 'syntax-table '(15)))

(defun fancystring-syntax-propertize-when-inside-generic-string (end quotestart)
; Call this function when we're inside a generic string.  Assume it is a
; fancystring.  Search forward for the end of the fancystring and mark it as
; such.  We don't need to worry about other strings or comments because
; everything inside is just more fancystring.

; BOZO The string start position is at quotestart (from (nth 8
; syntax)).  In principle it could be something other than the start
; of a fancystring -- e.g. if we had some additional syntax for
; strings that was set up through some other method.  But usage of the
; generic string syntax type seems to be limited to use with
; syntax-propertize-function, which is us, so we feel safe in assuming
; it is just the start of a fancystring.

; BOZO I tried just searching til the end of the region here, but I
; get "unbalanced parentheses" problems within large fancystrings.
; Whereas if I just cheat and search all the way to the ending
; delimiter and mark it even if it's past end, it seems to work out
; fine.  I think this is OK because everything until the end of the
; fancystring is just fancystring -- we don't need emacs to parse the
; intervening stuff beforehand to know how to set the property
; correctly.
  (when (search-forward "\"\"\"}" nil t)
    (let ((after-close-brace (point)))
      (fancystring-debug "Found close fancyquote at %d" after-close-brace quotestart)
      (set-generic-string-delimiter (- after-close-brace 1))
      (when (< (point) end)
	(fancystring-syntax-propertize-when-not-inside-generic-string end)))))

(defun fancystring-syntax-propertize-when-not-inside-generic-string (end)
; Call this function when we're not already inside a generic string.  Search
; forward for an open fancystring delimiter.  Check that it is not in a comment
; or string, and if not, mark it as the open delimiter.  Otherwise recur to
; find the next one.
  (when (search-forward "#{\"\"\"" end t)
    (let* ((after-open-quote (point))
	   (sharpsign (- after-open-quote 5))
	   (openbrace (+ sharpsign 1))
; check syntax on the # character
	   (syntax (syntax-ppss sharpsign)))
      (cond ((or (nth 3 syntax)  ; indicates in a string
		 (nth 4 syntax)) ; indicates in a comment
	     (when (eq (nth 3 syntax) t)
; Somehow we went from not being in a generic string to being in a generic
; string without passing a fancystring open delimiter.  Unexpected.
	       (error "Assertion failed in ~
                       fancystring-syntax-propertize-when-not-inside-generic-string"))
	     (fancystring-debug "Skipping open fancyquote at %d because it is in a %s"
                                sharpsign (if (nth 3 syntax) "string" "comment"))
	     (goto-char (+ after-open-quote 1))
	     (fancystring-syntax-propertize-when-not-inside-generic-string end))
	    (t
; Not in a string or comment. Set this up as an open delimiter.
	     (fancystring-debug "Found open fancyquote at %d" after-open-quote)
	     (set-generic-string-delimiter openbrace)
; Now we should be inside a generic string, so recur by calling that function.
	     (fancystring-syntax-propertize-when-inside-generic-string end openbrace))))))


(defun fancystring-syntax-propertize-function (start end)
  (fancystring-debug "Running fancystring-syntax-propertize-function start %d end %d" start end)
  (save-excursion
    (goto-char start)
    (let* ((syntax (syntax-ppss)))
      (if (eq (nth 3 syntax) t)
; We're already inside a generic string -- look for the end of a fancystring
	  (fancystring-syntax-propertize-when-inside-generic-string end (nth 8 syntax))
; Not inside a generic string -- look for the beginning of a fancystring
	(fancystring-syntax-propertize-when-not-inside-generic-string end)))))
	    
      
      
(add-hook 'lisp-mode-hook
          '(lambda ()
             (setq parse-sexp-lookup-properties t)
             (setq syntax-propertize-function 'fancystring-syntax-propertize-function)))
