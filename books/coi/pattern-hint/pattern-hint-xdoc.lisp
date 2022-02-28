;;  
;; Copyright (C) 2021, Collins Aerospace
;; All rights reserved.
;; 
;; This software may be modified and distributed under the terms
;; of the 3-clause BSD license.  See the LICENSE file for details.
;;
;; ===================================================================
;;
;; This book provides a pattern-matching driven computed hint facility
;;
;; See :doc pattern::hint
;;
;; (pattern::hint
;;   (< x y)
;;   :use ((:instance 
;; 
;;
;; The following pattern matching primitives can be nested:
;;
;; (:match (foo a b))
;; 
;; pattern::hint
;; pattern::hint*
;;
;; def::pattern-hint
;; def::pattern-hint-list
;; def::pattern-function
;;
;; ===================================================================

(in-package "ACL2")

;; (:and
;;  p1
;;  p2
;;  )

;; (:or
;;  p1
;;  p2
;;  )

#|

;; A notional grammar for pattern-hint expressions.
;;
;; symbol-alist : nil | ((symbol symbol) . symbol-alist)
;; term-alist   : nil | ((symbol term) . term-alist)
;; term-list    : nil | (term . term-list)
;; expr-list    : nil | (expr . expr-list)
;; expr: (:and   . expr-list)                     | ;; Compute the intersection of all of the bindings computed for expr-list
;;       (:or    . expr-list)                     | ;; Compute the union of all of the bindings computed for expr-list
;;       (:first . expr-list)                     | ;; Return the first binding found for expr-list
;;       (:pass)                                  | ;; Continue
;;       (:if expr expr exp)                      | ;; Match the first expression.  If successful, continue with the second.  If not, match the third.
;;       (:implies expr expr)                     | ;; Match the first expression.  If successful, continue with the second.
;;       (:call (symbol . term-list) symbol-list) | ;; Call the specified pattern function, bind each symbol in symbol-list to the values returned.
;;       (:not expr)                              | ;; If expr does not generate a binding, continue
;;       (:commutes expr symbol-alist)            | ;; Treat the pairs of symbols in symbol-alist as "commuting" and compute a binding that reflects commuted terms.
;;       (:replicate expr symbol-alist)           | ;; Compute a cartesian-product binding for each pair of symbols in symbol-alist.
;;       ;; 
;;       (:syntaxp term)                          | ;; Instantiate and evaluate term.  If not nil, continue
;;       (:equal . term-list)                     | ;; If all instantiated terms are equal, continue
;;       (:bind-free term symbol-list)            | ;; Instantiate and evaluate term.  Bind each symbol in symbol-list to the values returned.
;;       (:check  term)                           | ;; Call the simplifier to establish an instance of term.  If successful, continue
;;
;;       (:bind . term-alist)                     | ;; Bind each symbol to its associated term instance (may overwrite bindings)
;;       (:literally . symbol-list)               | ;; Bind each symbol in the list to itself as a term
;;       (:keep . symbol-list)                    | ;; Keep only the symbols bound in symbol-list
;;       (:match term expr)                       | ;; pattern match term against expr
;;       (:either term)                           | ;; Match either true or negated versions of term in the clause
;;       (:term   term)                           | ;; Match subterms appearing in the clause against term
;;       term                                       ;; Match term against terms appearing in the clause
;;

(def::pattern-function acl2::lte-match ()
  (:or (< a b)
       (not (< b a)))
  :returns (a b))

(defthm nonsense-example
  (< x y)
  :hints ((pattern::hint
           (:and
            (not (consp x))
            (:or (integerp x)
                 (stringp x))
            (:first (acl2-numberp y)
                    (integerp y))
            (:either (integerp a))
            (:term (+ p q))
            (:match a (append x y))
            (:literally w x)
            (:commutes (equal x y) (y x))
            (:replicate (equal x y) (a x) (b y))
            (:call (lte-match) (c d))
            (:syntaxp (not (cw "Found Match ~x0 ~x1" a b)))
            (:bind-free (expand-term a) (x y))
            (:not (foo y)) 
            (:if (:equal x y) (:bind (n x) (p y))
                 (:implies (< a b) (integerp z)))
            (:check (< a b))
            (:keep x y)
            )
           :use       (silly-rule
                       (:instance silly-rule
                                  (x x)
                                  (y y)))
           :expand    ((beta x))
           :cases     ((gamma x y))
           :restrict  ((dangerous-rule ((v1 a)
                                        (v2 b))))
           :in-theory (e/d (joe) (fred))
           :do-not   '(preprocess)
           :limit    nil   
           :repeat   nil   
           :slow     nil   
           :stable   t     
           :name     frank
          )))

:limit    [nil]   ;; When numeric, limit the total number of times the hint can fire
:repeat   [nil]   ;; When true, allow duplicate hint instances in successive subgoals.
:slow     [nil]   ;; When numeric, limits the number of hint instances per application.
                  ;; When true, limits the number of instances to 1
:stable   [t]     ;; Apply hints only when stable under simplification.
:name     frank ;; The name reported when the hint fires.
|#

