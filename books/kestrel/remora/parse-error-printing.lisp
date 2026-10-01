; Remora Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Stephen Westfold

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "REMORA")

(include-book "kestrel/utilities/strings/strings-codes" :dir :system)
(include-book "unicode/utf8-encode" :dir :system)
(include-book "std/basic/controlled-configuration" :dir :system)
(include-book "std/basic/defs" :dir :system)
(include-book "centaur/fty/baselists" :dir :system)
(include-book "std/typed-lists/nat-listp" :dir :system)
(include-book "std/util/define" :dir :system)
(include-book "xdoc/defxdoc-plus" :dir :system)

(include-book "portcullis")

(acl2::controlled-configuration :no-function nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ parse-error-printing
  :parents (parsing-and-printing)
  :short "Readable display of parse errors."
  :long
  (xdoc::topstring
   (xdoc::p
    "Parse errors, e.g. those returned by @(tsee parse-from-file), carry
     the remaining input as a list of code points, which prints as a long
     list of numbers.  @(tsee print-parse-error) prints an error with the
     remaining input shown as (a prefix of) the text itself.")
   (xdoc::p
    "These functions are kept in a small book so that they can be
     included without the @('oslib') dependencies of
     @(see parse-directory-utilities)."))
  :order-subtopics t
  :default-parent t)


(define sanitize-codepoints-for-display ((cps nat-listp))
  :returns (ucps ustring?)
  :hooks nil
  :short "Replace any non-scalar code point with U+FFFD."
  (cond ((endp cps) nil)
        ((acl2::uchar? (car cps))
         (cons (car cps) (sanitize-codepoints-for-display (cdr cps))))
        (t (cons #xFFFD (sanitize-codepoints-for-display (cdr cps))))))

(define codepoints-to-display-string ((cps nat-listp) (max natp))
  :returns (s stringp)
  :hooks nil
  :short "UTF-8 encode at most @('max') code points into an ACL2 string,
          appending @('...') if the input was truncated."
  (b* ((truncatedp (< (lnfix max) (len cps)))
       (cps (if truncatedp (take (lnfix max) cps) cps))
       (bytes (ustring=>utf8 (sanitize-codepoints-for-display
                              (acl2::nat-list-fix cps))))
       ((unless (unsigned-byte-listp 8 bytes)) "")
       (s (nats=>string bytes)))
    (if truncatedp
        (concatenate 'string s "...")
      s)))

(define readable-parse-error (x &key ((max natp) '100))
  :hooks nil
  :short "Make a parse error more readable."
  :long
  (xdoc::topstring
   (xdoc::p
    "Walks @('x') (typically a @(tsee reserr) from
     @(tsee parse-from-file)) and replaces every subterm of the form
     @('(:remaining-input . <code-points>)') with
     @('(:remaining-input <string>)'), where @('<string>') shows at most
     @('max') characters of the remaining input."))
  (cond ((not (consp x)) x)
        ((and (eq (car x) :remaining-input)
              (nat-listp (cdr x)))
         (list :remaining-input
               (codepoints-to-display-string (cdr x) max)))
        (t (cons (readable-parse-error (car x) :max max)
                 (readable-parse-error (cdr x) :max max)))))

(define print-parse-error (x &key ((max natp) '100))
  :returns (nil-val null)
  :hooks nil
  :short "Print a parse error readably to the comment window,
          via @(tsee readable-parse-error)."
  (cw "~x0~%" (readable-parse-error x :max max)))

