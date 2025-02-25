; PFCS (Prime Field Constraint System) Library
;
; Copyright (C) 2022-2025 Provable Inc. (https://www.provable.com)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ABNF")

(include-book "projects/abnf/parsing-tools/defdefparse" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ constructor-utilities
  :parents (abnf)
  :short "Some utilities to construct ABNF abstract syntax."
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define make-repeat-range-0* ()
  :returns (result repeat-rangep)
  (make-repeat-range
   :min 0
   :max (acl2::nati-infinity)))

(define make-repeat-range-1*1 ()
  :returns (result repeat-rangep)
  (make-repeat-range
   :min 1
   :max (acl2::nati-finite 1)))

(define make-repeat-range-1* ()
  :returns (result repeat-rangep)
  (make-repeat-range
   :min 1
   :max (acl2::nati-infinity)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define make-repetition-0*-rule ((rulename acl2::stringp))
  :returns (result repetitionp)
  :short "Makes ABNF AST for a repetition of zero or more @('rulename')."
  (make-repetition
   :element (element-rulename
             (rulename rulename))
   :range (make-repeat-range-0*)))

(define make-repetition-1*-rule ((rulename acl2::stringp))
  :returns (result repetitionp)
  :short "Makes ABNF AST for a repetition of one or more @('rulename')."
  (make-repetition
   :element (element-rulename
             (rulename rulename))
   :range (make-repeat-range-1*)))

(define make-repetition-unit-rule ((rulename acl2::stringp))
  :returns (result repetitionp)
  :short "Makes ABNF AST for a repetition of exactly one @('rulename')."
  (make-repetition
   :element (element-rulename
             (rulename rulename))
   :range (make-repeat-range-1*1)))

(define make-repetition-unit-case-sensitive-string ((string acl2::stringp))
  :returns (result repetitionp)
  :short "Makes ABNF AST for a repetition of
          exactly one instance of the given case-sensitive string terminal.)."
  (make-repetition
   :element (element-char-val
             (char-val-sensitive string))
   :range (make-repeat-range-1*1)))

(define make-repetition-unit-case-insensitive-string ((string acl2::stringp))
  :returns (result repetitionp)
  :short "Makes ABNF AST for a repetition of
          exactly one instance of the given case-insensitive string terminal.)."
  (make-repetition
   :element (element-char-val
             (char-val-insensitive nil string))
   :range (make-repeat-range-1*1)))
