; PFCS (Prime Field Constraint System) Library
;
; Copyright (C) 2022-2024 Provable Inc. (https://www.provable.com)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Eric McCarthy (bendyarm on GitHub)
;

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "PFCS")

(include-book "kestrel/abnf/parsing-tools/defdefparse" :dir :system)

;; Note, the contents here should eventually be combined with the
;; ABNF community books in the ABNF package.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define make-repeat-range-0* ()
  :returns (result abnf::repeat-rangep)
  (abnf::make-repeat-range
   :min 0
   :max (acl2::nati-infinity)))

(define make-repeat-range-1*1 ()
  :returns (result abnf::repeat-rangep)
  (abnf::make-repeat-range
   :min 1
   :max (acl2::nati-finite 1)))

(define make-repeat-range-1* ()
  :returns (result abnf::repeat-rangep)
  (abnf::make-repeat-range
   :min 1
   :max (acl2::nati-infinity)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define make-repetition-0*-rule ((rulename stringp))
  :returns (result abnf::repetitionp)
  :short "Makes ABNF AST for a repetition of zero or more @('rulename')."
  (abnf::make-repetition
          :element (abnf::element-rulename
                    (abnf::rulename rulename))
          :range (make-repeat-range-0*)))

(define make-repetition-1*-rule ((rulename stringp))
  :returns (result abnf::repetitionp)
  :short "Makes ABNF AST for a repetition of one or more @('rulename')."
  (abnf::make-repetition
          :element (abnf::element-rulename
                    (abnf::rulename rulename))
          :range (make-repeat-range-1*)))

(define make-repetition-unit-rule ((rulename stringp))
  :returns (result abnf::repetitionp)
  :short "Makes ABNF AST for a repetition of exactly one @('rulename')."
  (abnf::make-repetition
          :element (abnf::element-rulename
                    (abnf::rulename rulename))
          :range (make-repeat-range-1*1)))

(define make-repetition-unit-case-sensitive-string ((string stringp))
  :returns (result abnf::repetitionp)
  :short "Makes ABNF AST for a repetition of exactly one instance of the given case-sensitive string terminal.)."
  (abnf::make-repetition
          :element (abnf::element-char-val
                    (abnf::char-val-sensitive string))
          :range (make-repeat-range-1*1)))

(define make-repetition-unit-case-insensitive-string ((string stringp))
  :returns (result abnf::repetitionp)
  :short "Makes ABNF AST for a repetition of exactly one instance of the given
  case-insensitive string terminal.)."
  (abnf::make-repetition
          :element (abnf::element-char-val
                    (abnf::char-val-insensitive nil string))
          :range (make-repeat-range-1*1)))
