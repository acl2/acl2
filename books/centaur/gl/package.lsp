; GL - A Symbolic Simulation Framework for ACL2
; Copyright (C) 2008-2013 Centaur Technology
;
; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/
;
; This program is free software; you can redistribute it and/or modify it under
; the terms of the GNU General Public License as published by the Free Software
; Foundation; either version 2 of the License, or (at your option) any later
; version.  This program is distributed in the hope that it will be useful but
; WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
; FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
; more details.  You should have received a copy of the GNU General Public
; License along with this program; if not, write to the Free Software
; Foundation, Inc., 51 Franklin Street, Suite 500, Boston, MA 02110-1335, USA.
;
; Original author: Sol Swords <sswords@centtech.com>

(in-package "ACL2")

(defpkg "GL"
 (set-difference-eq
  (union-eq
   *acl2-exports*
   *common-lisp-symbols-from-main-lisp-package*
   '(pkg-witness bad-atom<= b* quit exit
     hons-acons hons-get hut het hqual hons-equal
     hons-assoc-equal make-fal
     definline definlined
     defxdoc defsection define

     qv bfr-and bfr-not bfr-and
     bfr-p bfr-or bfr-xor bfr-iff bfr-ite bfr-eval bfr-eval-list
     q-implies add-bfr-fn add-bfr-pat add-bfr-fn-pat max-depth
     equal-by-bfr-evals-hint-heavy
     equal-of-booleans-rewrite bfr-ite-fn q-implies-fn bfr-or
     bfr-eval-when-non-consp-values
     |(bfr-ite non-nil y z)|
     bfr-eval-when-not-consp
     bfr-eval-of-non-consp-cheap

     bfr-eval-cp-default-hint
     bfr-eval-list-when-not-consp
     bfr-p-of-bfr-and
     bfr-p-of-bfr-not
     bfr-p-of-bfr-ite
     bfr-p-of-bfr-xor
     bfr-p-of-bfr-iff
     bfr-p-of-bfr-or
     bfr-p-of-q-implies
     lnfix lifix lbfix

     mv-nth-cons-meta

     def-ruleset def-ruleset! add-to-ruleset add-to-ruleset! e/d* enable*
     disable* e/d** ruleset-theory

     allow-arith5-help
     with-arith5-help
     arith5-enable-ruleset
     arith5-disable-ruleset

     prove-guard-invariants

     add-untranslate-pattern
     def-pattern-match-constructor
     defn getprop body
     formals stobjs-out theorem recursivep current-acl2-world
     unnormalized-body def-bodies
     make-n-vars
     binary-logand binary-logior name wrld
     minimal-arithmetic-theory
     minimal-theory
     pattern-match
     alphorder lexorder
     mfc-clause
     natp-compound-recognizer
     zp-open
     add-def-complex
     inverse-of-+
     translate1
     value

     default-+-2
     default-<-1
     default-+-1
     default-<-2
     default-*-1 default-*-2
     default-unary-/

     parse-clause-id
     is-prefix subgoal-of

     bfr-eval-of-bfr-and
     bfr-eval-of-bfr-or
     bfr-eval-of-bfr-not

     a b c d e f g h i j k l m n o p q r s t u v w x y z

     fold-constants-in-plus
     simplify-products-gather-exponents-equal
     simplify-products-gather-exponents-<
     lhs rhs
     rational-implies1
     rational-implies2
     default-plus-1
     default-plus-2
     acl2-numberp-x
     INTEGERP-MINUS-X NUMERATOR-ZERO NUMERATOR-POSITIVE
     NUMERATOR-NEGATIVE DEFAULT-LESS-THAN-1
     DEFAULT-LESS-THAN-2 SIMPLIFY-SUMS-EQUAL
     PREFER-POSITIVE-ADDENDS-EQUAL
     DEFAULT-TIMES-1 NOT-INTEGERP-1A
     PREFER-POSITIVE-ADDENDS-<
     SIMPLIFY-SUMS-< META-INTEGERP-CORRECT
     REDUCE-INTEGERP-+ ASH-TO-FLOOR
     RATIONALP-X REDUCE-ADDITIVE-CONSTANT-<
     REDUCE-MULTIPLICATIVE-CONSTANT-<
     |(logand y x)|
     |(< (logand x y) 0)| NOT-INTEGERP-4A
     NOT-INTEGERP-4B FLOOR-ZERO
     CANCEL-FLOOR-+ INTEGERP-/-EXPT-2
     FLOOR-NEGATIVE FLOOR-POSITIVE
     NOT-INTEGERP-3B INTEGERP-/-EXPT-1
     NOT-INTEGERP-3A FLOOR-NONPOSITIVE
     NOT-INTEGERP-2A FLOOR-NONNEGATIVE
     NOT-INTEGERP-2B NOT-INTEGERP-1B
     FLOOR-X-Y-=-1 NOT-INTEGERP-4B
     DEFAULT-TIMES-2 FLOOR-=-X/Y
     EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT
     EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT
     EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT
     EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT
     BOOLEAN-LISTP MOD-ZERO MOD-NEGATIVE


     conjoin-clauses conjoin disjoin disjoin-lst
     pseudo-term-list-listp

     two-nats-measure

     flag-present flag-fn-name flag-alist flag-defthm-macro flag-equivs-name
     use-by-hint use-by-computed-hint

     def-gl-clause-processor gl-hint
     def-gl-thm def-gl-param-thm
     def-g-thm def-g-param-thm make-g-world
     mk-g-number mk-g-boolean mk-g-ite mk-g-concrete
     gobjectp glc glr gl-fnsym gl-interp
     gl-interp-raw gl-interp
     gl-aside gl-ignore nonnil-symbol-listp env

     xor
     gl-bdd-mode gl-aig-mode gl-mbe

     logcons logcar logcdr loghead logtail logapp
     b-ior b-and b-xor b-not bfix bitp boolfix

     numlist
     defsection

     ;; some imports for better xdoc integration
     hardware-verification
     proof-automation
     boolean-reasoning
     satlink
     ubdds
     aig
     acl2::hons-and-memoization
     xdoc
     set-max-mem
     the-method
     aignet


     ))
  '(nat-listp ; included 12/4/2012 by Matt K., for addition to *acl2-exports*
    )))

(defpkg "GL-SYM" nil)
(defpkg "GL-THM" nil)
(defpkg "GL-FACT" nil)
(defpkg "GL-FLAG" nil)

;; (defmacro gl::include-book (&rest args)
;;   `(acl2::include-book ,@args :ttags :all))
