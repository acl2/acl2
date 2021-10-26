; Syntheto Library
;
; Copyright (C) 2021 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "SYNTHETO")

(include-book "functions")

; temporary, to avoid conflicts with NLD:
;; (include-book "kestrel/soft/defunvar" :dir :system)
;; (include-book "kestrel/soft/defun-sk2" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; This is (a start towards) shallowly embedded Syntheto function specifications,
; i.e. event macros corresponding to those Syntheto constructs,
; which will generate and submit the appropriate ACL2 events
; that correspond to the Syntheto function specifications.
; Please feel free to improve this file,
; and to add your name to the file header.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

#|

Shallowly embedded input/output function specification.
This must take a single function header as parameter
and an expression that expresses a relation
between the inputs and outputs of that function.

An input/output specification of the form

  specification s (function f (x:T) returns (y:U)) {
    relation[x,y]
  }

is translated to

  (soft::defunvar f (*) => *)

  (soft::defun-sk2 s ()
    (forall (x)
            (implies (T x)
                     (b* ((y (f x)))
                       (and (U y)
                            relation[x,y])))))

where the generalization to multiple inputs and outputs should be obvious.

That is, we generate a function variable f for the header
and we generate a quantifier 2nd-order function s to constrain f.

Currently soft::defunvar does not support multiple outputs,
so we limit f to return a single output.
However, multiple inputs are easily supported.

Note how the type information is includes in the definition of s.
The constraint is
relativized to the input that satisfies its type,
and strengthened to require the output to satisfy its type.

An alternative approach to handle types may be to
independently extend soft::defunvar to support constrained function variables
(in the spirit of ACL2's non-trivial encapsulates,
and in fact implemented as that),
generate a function variable f constrained to
(i) fix its input to T and (ii) unconditionally return U, and
thus avoid the (T x) and (U y) terms in the soft::defun-sk2.
Note that this requires the refinement of the specification
to take function variable constraints into account.

|#

(defun generate-input-type-conditions (inputs)
  (if (endp inputs)
      ()
    (b* ((input (first inputs))
         (input-namestring (first input))
         (input-name (intern-syndef input-namestring))
         (input-type (second input))
         (input-pred (type-name-to-pred
                      (s-type-to-fty-name-symbol input-type))))
      (cons `(,input-pred ,input-name)
            (generate-input-type-conditions (rest inputs))))))

(define s-spec-in-out-fn (spec-namestring
                          fun-namestring
                          inputs
                          outputs
                          relation)
  :returns (event "A @(tsee acl2::maybe-pseudo-event-formp).")
  :verify-guards nil
  (b* ((spec-name (intern-syndef spec-namestring))
       (fun-name (intern-syndef fun-namestring))
       ((unless (= (len outputs) 1)) ; needs soft::defunvar extension
        (raise "Multiple outputs ~x0 not supported." outputs))
       (input-type-conditions (generate-input-type-conditions inputs))
       (input-names (strip-cadrs input-type-conditions))
       (output (car outputs))
       (output-namestring (first output))
       (output-name (intern-syndef output-namestring))
       (output-type (second output))
       (output-pred (type-name-to-pred
                     (s-type-to-fty-name-symbol output-type)))
       (type-defs (defining-forms-for-unnamed-types-in-s-exp (list inputs outputs relation)))
       (defunvar-event
         ;; `(soft::defunvar ,fun-name ,(repeat (len inputs) '*) => *))
         `(defstub ,fun-name ,(repeat (len inputs) '*) => *))
       (relation-term (translate-term relation))
       (matrix `(implies (and ,@input-type-conditions)
                         (b* ((,output-name (,fun-name ,@input-names)))
                           (and (,output-pred ,output-name)
                                ,relation-term))))
       (body `(forall ,input-names ,matrix))
       (defun-sk2-event
         ;; `(soft::defun-sk2 ,spec-name () ,body))
         `(defun-sk ,spec-name () ,body))
       (event `(with-output :off :all :on error :gag-mode t
                 (progn ,@type-defs
                        ,defunvar-event
                        ,defun-sk2-event))))
    event))

(defmacro s-spec-in-out (spec-namestring ; string
                         &key
                         fun-namestring ; string
                         inputs ; result of d-->s-typed-vars
                         outputs ; result of d-->s-typed-vars
                         relation) ; result of d-->s-expr
  `(make-event (s-spec-in-out-fn ',spec-namestring
                                 ',fun-namestring
                                 ',inputs
                                 ',outputs
                                 ',relation)))
