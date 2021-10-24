; Syntheto Library
;
; Copyright (C) 2021 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "SYNTHETO")

(include-book "../translation")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; ASTs for the top-level constructs in the Syntheto file ams-spec-v0.synth.
; This is version 0 of the specification of the
; Aircraft Maintenance Scheduling (AMS) example.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defconst *struct-acid*
  (toplevel-type
   (make-type-definition
    :name (identifier "acid")
    :body (type-definer-product
           (make-type-product
            :fields (list
                     (make-field
                      :name (identifier "id")
                      :type (type-integer)))
            :invariant nil)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defconst *variant-actype*
  (toplevel-type
   (make-type-definition
    :name (identifier "actype")
    :body (type-definer-sum
           (make-type-sum
            :alternatives (list
                           (make-alternative
                            :name (identifier "a")
                            :product (make-type-product
                                      :fields nil
                                      :invariant nil))
                           (make-alternative
                            :name (identifier "b")
                            :product (make-type-product
                                      :fields nil
                                      :invariant nil))
                           (make-alternative
                            :name (identifier "c")
                            :product (make-type-product
                                      :fields nil
                                      :invariant nil))))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defconst *struct-aircraft*
  (toplevel-type
   (make-type-definition
    :name (identifier "aircraft")
    :body (type-definer-product
           (make-type-product
            :fields (list
                     (make-field
                      :name (identifier "id")
                      :type (type-defined (identifier "acid")))
                     (make-field
                      :name (identifier "type")
                      :type (type-defined (identifier "actype"))))
            :invariant nil)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; TODO: figure out the exact nature and polymorphis of builtins
;       such as empty, head, tail, some and none below

(defconst *function-find-aircraft*
  (toplevel-function
   (make-function-definition
    :header
    (make-function-header
     :name (identifier "find_aircraft")
     :inputs (list (make-typed-variable
                    :name (identifier "id")
                    :type (type-defined (identifier "acid")))
                   (make-typed-variable
                    :name (identifier "roster")
                    :type (type-set (type-defined (identifier "aircraft")))))
     :outputs (list (make-typed-variable
                     :name (identifier "aircraft")
                     :type (type-option (type-defined (identifier "aircraft"))))))
    :precondition
    nil
    :postcondition
    nil
    :definer
    (make-function-definer-regular
     :body
     (make-expression-if
      :test
      (make-expression-call :function (identifier "empty")
                            :arguments (list (make-expression-variable
                                              :name (identifier "roster"))))
      :then
      (make-expression-call :function (identifier "none")
                            :arguments nil)
      :else
      (make-expression-bind
       :variables (list (make-typed-variable
                         :name (identifier "ac")
                         :type (type-defined (identifier "aircraft"))))
       :value (make-expression-call
               :function (identifier "head")
               :arguments (list (make-expression-variable
                                 :name (identifier "roster"))))
       :body (make-expression-if
              :test
              (make-expression-binary
               :operator (binary-op-eq)
               :left-operand (make-expression-product-field
                              :type (identifier "aircraft")
                              :target (make-expression-variable
                                       :name (identifier "ac"))
                              :field (identifier "id"))
               :right-operand (make-expression-variable
                               :name (identifier "id")))
              :then
              (make-expression-call
               :function (identifier "some")
               :arguments (list (make-expression-variable
                                 :name (identifier "ac"))))
              :else
              (make-expression-call
               :function (identifier "find_aircraft")
               :arguments (list
                           (make-expression-variable
                            :name (identifier "id"))
                           (make-expression-call
                            :function (identifier "tail")
                            :arguments (list
                                        (make-expression-variable
                                         :name (identifier "roster")))))))))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; (defconst *function-acroster-is-wf*
;;   (toplevel-function
;;    (make-function-definition
;;     :header
;;     (make-function-header
;;      :name (identifier "acroster_is-wf")
;;      :inputs (list (make-typed-variable
;;                     :name (identifier "roster")
;;                     :type (type-set (type-defined (identifier "aircraft")))))
;;      :outputs (list (make-typed-variable
;;                      :name (identifier "yes_no")
;;                      :type (type-boolean))))
;;     :precondition nil
;;     :postcondition nil
;;     :definer
;;     (make-function-definer-regular
;;      :body
;;      (make-expression-binary
;;       :operator
;;       (binary-op-or)
;;       :left-operand
;;       (make-expression-call
;;        :function
;;        (identifier "is_empty")
;;        :arguments
;;        (list (make-expression-variable :name (identifier "roster"))))
;;       :right-operand
;;       (make-expression-binary
;;        :operator
;;        (binary-op-and)
;;        :left-operand
;;        (make-expression-sum-test
;;         :target
;;         (make-expression-call
;;          :function
;;          (identifier "find_aircraft")
;;          :arguments
;;          (list
;;           (make-expression-product-field
;;            :type (identifier "aircraft")
;;            :target
;;            (make-expression-call
;;             :function
;;             (identifier "head")
;;             :arguments
;;             (list (make-expression-variable :name (identifier "roster"))))
;;            :field
;;            (identifier "id"))
;;           (make-expression-call
;;            :function
;;            (identifier "tail")
;;            :arguments
;;            (list (make-expression-variable :name (identifier "roster"))))))
;;         :alternative
;;         (identifier "some"))
;;        :right-operand
;;        (make-expression-call
;;         :function
;;         (identifier "acroster_is_wf")
;;         :arguments
;;         (list (make-expression-call
;;                :function
;;                (identifier "tail")
;;                :arguments
;;                (list (make-expression-variable
;;                       :name (identifier "roster"))))))))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defconst *struct-mission*
  (toplevel-type
   (make-type-definition
    :name (identifier "mission")
    :body (type-definer-product
           (make-type-product
            :fields (list
                     (make-field
                      :name (identifier "required")
                      :type (type-defined (identifier "actype"))))
            :invariant nil)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; TODO:

;; function is_solution (solution: seq<acid>,
;;                       missions: seq<mission>,
;;                       roster: set<aircraft>)
;; assumes acroster_is_wf(roster)
;; returns (yes_no: boolean) {
;;     if (is_empty(missions)) {
;;         return true;
;;     } else {
;;         when (is_empty(solution)) { return false; }
;;         let ac: opt<aircraft> = find_aircraft(head(solution), roster);
;;         return ac.some? &&
;;                (ac.some == head(missions).required) &&
;;                is_solution(tail(solution), tail(missions), roster);
;;     }
;; }

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; TODO:

;; function is_solvable (missions: seq<mission>, roster: set<aircraft>)
;; assumes acroster_is_wf(roster)
;; returns (yes_no: boolean) {
;;     exists (solution:seq<acid>) is_solution(solution, missions, roster)
;; }

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defconst *variant-result*
  (toplevel-type
   (make-type-definition
    :name (identifier "result")
    :body (type-definer-sum
           (make-type-sum
            :alternatives
            (list
             (make-alternative
              :name (identifier "solution")
              :product (make-type-product
                        :fields (list
                                 (make-field
                                  :name (identifier "get")
                                  :type (type-sequence
                                         (type-defined (identifier "acid")))))
                        :invariant nil))
             (make-alternative
              :name (identifier "nosolution")
              :product (make-type-product
                        :fields nil
                        :invariant nil))))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; TODO:

;; function in_out (missions: seq<mission>, roster:set<aircraft>, result:result)
;; returns (yes_no boolean) {
;;     acroster_is_wf(roster) ==>
;;     (if (is_solvable (missions, roster)) {
;;          result.solution? &&
;;          is_solution(result.some, missions, roster);
;;      } else {
;;          result.nosolution?
;;      })
;; }

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; TODO:

;; specification spec_schedule
;; (function schedule (missions: seq<mission>, roster: set<aircraft>)
;;  returns (result: result)) {
;;      forall (missions: seq<mission>, roster: set<aircraft>)
;;          in_out(missions, roster, schedule(missions, roster))
;; }

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; TODO: static checking fails if we add *function-find-aircraft*,
;       due to the polymorphic built functions mentioned above

(defconst *events*
  (list *struct-acid*
        *variant-actype*
        *struct-aircraft*))

(assert-event (equal (mv-list 2 (check-toplevel-list *events* (make-context)))
                     (list nil nil))) ; no error, no obligations

(translate-to-acl2 *events*)
