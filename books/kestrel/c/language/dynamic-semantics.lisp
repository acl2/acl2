; C Library
;
; Copyright (C) 2022 Kestrel Institute (http://www.kestrel.edu)
; Copyright (C) 2022 Kestrel Technology LLC (http://kestreltechnology.com)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C")

(include-book "operations")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ dynamic-semantics
  :parents (language)
  :short "A dynamic semantics of C."
  :long
  (xdoc::topstring
   (xdoc::p
    "We are in the process of reformulating and moving code from
     @('../atc/execution.lisp') to this file.")
   (xdoc::p
    "We distinguish between pure (i.e. side-effect-free) expressions
     and expressions that may have side effects.
     We allow the latter to appear only in certain parts of statements,
     and we put restrictions to ensure a predictable order of evaluation.
     Pure expressions may be evaluated in any order;
     we evaluate them left to right.")
   (xdoc::p
    "We formalize a big-step operational interpretive semantics.
     To ensure the termination of the ACL2 mutually recursive functions
     that formalize the execution of statements, function calls, etc.,
     these ACL2 functions take a limit on the depth of the recursive calls,
     which ends the recursion with an error when it reaches 0,
     which is decremented at each recursive call,
     and which is used as termination measure.
     Thus, a proof of total correctness
     (i.e. the code terminates and produces correct results)
     involves showing the existence of sufficiently large limit values,
     while a proof of partial correctness
     (i.e. the code produces correct results if it terminates)
     is relativized to the limit value not running out.
     The limit is an artifact of the formalization;
     it has no explicit counterpart in the execution state of the C code."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exec-iconst ((ic iconstp))
  :returns (result value-resultp)
  :short "Execute an integer constant."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is according to [C:6.4.4.1/5]:
     based on the suffixes and the base,
     we find the first type that suffices to represent the value,
     in the lists indicated in the table,
     and we return the value of the found type.
     If the value is too large, we return an error.")
   (xdoc::p
    "This is the dynamic counterpart of @(tsee check-iconst)."))
  (b* (((iconst ic) ic)
       (error (error (list :iconst-out-of-range (iconst-fix ic)))))
    (if ic.unsignedp
        (iconst-length-case
         ic.length
         :none (cond ((uint-integerp ic.value) (value-uint ic.value))
                     ((ulong-integerp ic.value) (value-ulong ic.value))
                     ((ullong-integerp ic.value) (value-ullong ic.value))
                     (t error))
         :long (cond ((ulong-integerp ic.value) (value-ulong ic.value))
                     ((ullong-integerp ic.value) (value-ullong ic.value))
                     (t error))
         :llong (cond ((ullong-integerp ic.value) (value-ullong ic.value))
                      (t error)))
      (iconst-length-case
       ic.length
       :none (if (iconst-base-case ic.base :dec)
                 (cond ((sint-integerp ic.value) (value-sint ic.value))
                       ((slong-integerp ic.value) (value-slong ic.value))
                       ((sllong-integerp ic.value) (value-sllong ic.value))
                       (t error))
               (cond ((sint-integerp ic.value) (value-sint ic.value))
                     ((uint-integerp ic.value) (value-uint ic.value))
                     ((slong-integerp ic.value) (value-slong ic.value))
                     ((ulong-integerp ic.value) (value-ulong ic.value))
                     ((sllong-integerp ic.value) (value-sllong ic.value))
                     ((ullong-integerp ic.value) (value-ullong ic.value))
                     (t error)))
       :long (if (iconst-base-case ic.base :dec)
                 (cond ((slong-integerp ic.value) (value-slong ic.value))
                       ((sllong-integerp ic.value) (value-sllong ic.value))
                       (t error))
               (cond ((slong-integerp ic.value) (value-slong ic.value))
                     ((ulong-integerp ic.value) (value-ulong ic.value))
                     ((sllong-integerp ic.value) (value-sllong ic.value))
                     ((ullong-integerp ic.value) (value-ullong ic.value))
                     (t error)))
       :llong (if (iconst-base-case ic.base :dec)
                  (cond ((sllong-integerp ic.value) (value-sllong ic.value))
                        (t error))
                (cond ((sllong-integerp ic.value) (value-sllong ic.value))
                      ((ullong-integerp ic.value) (value-ullong ic.value))
                      (t error))))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exec-const ((c constp))
  :returns (result value-resultp)
  :short "Execute a constant."
  :long
  (xdoc::topstring
   (xdoc::p
    "We only support the execution of integer constants for now."))
  (const-case c
              :int (exec-iconst c.get)
              :float (error :exec-const-float)
              :enum (error :exec-const-enum)
              :char (error :exec-const-char))
  :hooks (:fix))
