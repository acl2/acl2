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

(include-book "characters")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ format-strings
  :parents (abstract-syntax)
  :short "Leo format strings."
  :long
  (xdoc::topstring
   (xdoc::p
    "A format string in Leo is a sequence of characters
     where occurrences of @('{}') are treated as containers.")
   (xdoc::p
    "In abstract syntax, we model a format string as
     a sequence of characters and containers.
     That is, we treat containers as separate entities,
     which are intermixed with regular characters in a format string.
     We also require the non-container characters to
     not include any subsequence @('{}'),
     because that must be represented as a container."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum char/container
  :short "Fixtype of Leo characters and containers."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are the elements of format strings.
     See @(see format-strings)."))
  (:char ((get char)))
  (:container ())
  :pred char/container-p)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deflist char/container-list
  :short "Fixtype of lists of Leo characters and containers."
  :elt-type char/container
  :true-listp t
  :elementp-of-nil nil
  :pred char/container-listp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define char/container-list-no-open/close-brace-p ((ccs char/container-listp))
  :returns (yes/no booleanp)
  :short "Check that a list of characters and containers does not include
          a non-container open brace immediately followed by
          a non-container close brace."
  :long
  (xdoc::topstring
   (xdoc::p
    "The Unicode open and close brace characters are the ASCII ones."))
  (b* (((when (endp ccs)) t)
       (cc (car ccs))
       ((when (char/container-case cc :container))
        (char/container-list-no-open/close-brace-p (cdr ccs)))
       (ch (char/container-char->get cc))
       ((when (not (eql ch (char-code #\{))))
        (char/container-list-no-open/close-brace-p (cdr ccs))))
    (or (endp (cdr ccs))
        (and (not (char/container-equiv (cadr ccs)
                                        (char/container-char (char-code #\}))))
             (char/container-list-no-open/close-brace-p (cdr ccs)))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod format-string
  :short "Fixtype of Leo format strings."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is a sequence of characters and containers;
     see @(see format-strings).
     We wrap it into a one-field product type for greater abstraction."))
  ((elements char/container-list
             :reqfix (if (char/container-list-no-open/close-brace-p elements)
                         elements
                       nil)))
  :require (char/container-list-no-open/close-brace-p elements)
  :tag :format-string
  :pred format-stringp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define format-string-containers ((fstring format-stringp))
  :returns (n natp)
  :short "Number of containers in a format string."
  (format-string-containers-aux (format-string->elements fstring))
  :hooks (:fix)

  :prepwork
  ((define format-string-containers-aux ((elements char/container-listp))
     :returns (n natp)
     (b* (((when (endp elements)) 0)
          (element (car elements))
          (n1 (char/container-case element
                                   :char 0
                                   :container 1))
          (n2 (format-string-containers-aux (cdr elements))))
       (+ n1 n2))
     :hooks (:fix))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Parse a char-list that is the first argument of a console.log
;; into a format-string.

;; Use for an error.  Same as *error-format-string* but I don't
;; want the redundant definitions between here and json2ast.lisp
(defconst *empty-format-string*
  (make-format-string :elements nil))

;; "{{" parses to an open brace character.
;; "}}" parses to a close brace character.
;; "{}" parses to a container.
;; Any other occurrence of '{' or '}' is an error.
;;
;; The states are :BASE and :OPEN{ and :CLOSE}
;;
;; When an open brace is encountered currently (in :BASE state)
;; the state is set to :OPEN{ and the next character must be
;; either another open brace (resulting in a single open brace char)
;; or a close brace (resulting in a container).
;;
;; When a close brace is encountered (in :BASE state)
;; the state is set to :CLOSE} and the next character must be
;; another close brace (resulting in a single close brace char).

(define parse-format-chars ((chars char-listp) (parse-state symbolp))
  :returns (mv (erp booleanp) (chars/containers char/container-listp))
  (b* (((when (endp chars))
        (case parse-state
          (:base (mv nil nil))
          ;; if chars ends with open or close brace, that is considered an error
          (:open{ (mv t nil))
          (:close} (mv t nil))
          ;; should never happen
          (t (mv t (er hard? 'top-level "parse-state should be :base or :open{ or :close}")))))
       (first-char (first chars))
       (code (char->codepoint first-char))
       (rest-chars (rest chars)))
    (case parse-state
      (:base
       (if (= code 123) ; '{'
           (parse-format-chars rest-chars :open{)
         (if (= code 125) ; '}'
             (parse-format-chars rest-chars :close})
           (b* (((mv rest-erp rest-parsed) (parse-format-chars rest-chars :base))
                ((when rest-erp)
                 (mv t nil)))
             (mv nil
                 (cons (make-char/container-char :get first-char) rest-parsed))))))
      (:open{
       (if (= code 123) ; a second '{'
           (b* (((mv rest-erp rest-parsed) (parse-format-chars rest-chars :base))
                ((when rest-erp)
                 (mv t nil)))
             (mv nil
                 (cons (make-char/container-char :get first-char)
                       rest-parsed)))
         (if (= code 125) ; a close '}'
             (b* (((mv rest-erp rest-parsed) (parse-format-chars rest-chars :base))
                  ((when rest-erp)
                   (mv t nil)))
               (mv nil
                   (cons (make-char/container-container)
                         rest-parsed)))
           ;; Anything after '{' other than '{' or '}' is considered an error.
           (mv t nil))))
      (:close}
       (if (= code 125) ; a second '}'
           (b* (((mv rest-erp rest-parsed) (parse-format-chars rest-chars :base))
                ((when rest-erp)
                 (mv t nil)))
             (mv nil
                 (cons (make-char/container-char :get first-char)
                       rest-parsed)))
         ;; Anything after '}' other than '}' is considered an error.
         (mv t nil)))
      ;; any other parse-state is a hard error
      (t (mv t (er hard? 'top-level "parse-state should be :base or :open{ or :close}"))))))

(define char-list-to-format-string ((chars char-listp))
  :returns (mv (erp booleanp) (fstring format-stringp))
  :short "Parse the given chars into a format-string."
  (b* (((mv erp chars/containers) (parse-format-chars chars :base))
       ((when erp)
        (mv t *empty-format-string*)))
    (mv nil
        (make-format-string :elements chars/containers))))
