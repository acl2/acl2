; Copyright (C) 2020, ForrestHunt, Inc.
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; For examples see use-io-pairs-tests.lisp.

; Possible future enhancements:

; - Track the I/O pairs in a table, and develop variants add-io-pair(s) of
;   use-io-pair(s) that add to the existing I/O pairs.  Then we will probably
;   need to unmemoize first (probably automatically, with add-io-pair(s)).
;   There could also be clear-io-pairs.

; - Relax the restriction that the function takes and returns a single value.

(in-package "ACL2")

(include-book "xdoc/top" :dir :system)

(defxdoc use-io-pair
  :parents (events)
  :short "Execute a function using a verified input-output pair"
  :long "<p>WARNING: This utility may undergo significant changes until the end
 of January 2021.</p>

 @({
 Example:
 (use-io-pair
  'rtl::primep #.primes::*bn-254-group-prime* t
  :test 'eql
  :hints '((\"Goal\"
            :in-theory
            (enable primes::primep-of-bn-254-group-prime-constant))))

 General Form:
 (use-io-pair fn input output &key hints debug test)
 })

 <p>where all arguments are evaluated.  The value of @('fn') must be a unary
 function symbol whose argument is an ordinary value (not @(see state) or a
 user-defined @(tsee stobj)); also, @('fn') must return a single value.  (It
 would likely be straightforward to remove the restriction to a single input
 and output.)</p>

 <p>@('use-io-pair') is merely a convenient way to invoke the utility @(see
 use-io-pairs) when there is a single input/output pair, essentially as
 follows; see @(see use-io-pairs) for further documentation.</p>

 @({
 (use-io-pairs fn (acons input output nil)
               :hints hints
               :debug debug
               :test test)))
 })")

(defxdoc use-io-pairs
  :parents (events)
  :short "Execute a function using verified input-output pairs"
  :long "<p>WARNING: This utility may undergo significant changes until the end
 of January 2021.</p>

 <p>Note: For examples, look in the @(see community-books) at the book,,
 @('kestrel/utilities/use-io-pairs-tests.lisp').</p>

 @({
 Example:
 (use-io-pair
  'rtl::primep #.primes::*bn-254-group-prime* t
  :test 'eql
  :hints '((\"Goal\"
            :in-theory
            (enable primes::primep-of-bn-254-group-prime-constant))))

 General Form:
 (use-io-pair fn input output &key hints debug test)
 })

 <p>where all arguments are evaluated to produce the following.</p>

 <ul>

 <li>@('fn'): A unary function symbol whose argument is an ordinary value (not
 @(see state) or a user-defined @(tsee stobj)), which also returns a single
 value</li>

 <li>@('input') and @('output'): @('(f input)') must evaluate to
 @('output')</li>

 <li>@('hints') (optional, default @('nil')): when non-@('nil'), used as the
 @(':hints') argument to a theorem that proves @('(f input)') equals
 @('output')</li>

 <li>@('debug') (optional, default @('nil')): when non-@('nil'), causes @(tsee
 cw) to print a message to the terminal when an I/O pair is being used during
 evaluation, that is, when the output is obtained by lookup on the input rather
 than by computing with the body of @('fn')</li>

 <li>@('test') (optional, default @(''equal')): called to test equality of an
 input to @('fn') to one of the specified I/O pairs, so that the result is
 looked up rather than computed</li>

 </ul>

 <p>A more general utility, which allows the substitution of one function for
 another during execution, is available with the @(':invoke') argument of
 @(tsee memoize).</p>")

(defmacro use-io-pair (fn input output &key hints debug test)
  `(use-io-pairs ,fn (acons ,input ,output nil)
                 :hints ,hints
                 :debug ,debug
                 ,@(and test `(:test ,test))))

(defun io-pairs-dcls (fn wrld)

; Much of this code is based on that of ACL2 source function
; guard-raw.

  (declare (xargs :mode :program))
  (cons '(declare (xargs :verify-guards t))
        (let* ((ev (get-event fn wrld))
               (def ; strip off leading defun
                (case (car ev)
                  (defun (cdr ev))
                  (mutual-recursion (assoc-eq fn (strip-cdrs (cdr ev))))
                  (verify-termination-boot-strap
; For some functions, like apply$, we wind up in this case.
                   (cdr (cltl-def-from-name fn wrld)))
                  (otherwise ; surprising case; just declare the guard
                   `(declare (xargs :guard ,(guard fn nil wrld)))))))
          (butlast (cddr def) 1))))

(defun use-io-pairs-helper (fn pairs hints debug test state)

; We know that fn is a function symbol in (w state).

  (declare (xargs :stobjs state :mode :program))
  (let* ((suffix1 (check-sum-obj (list 'defthm fn pairs)))
         (thm-name (add-suffix fn (coerce (explode-atom suffix1 10) 'string)))
         (wrld (w state))
         (formals (formals fn wrld))
         (formal (assert$ (and (consp formals)
                               (null (cdr formals)))
                          (car formals)))
         (suffix2 (check-sum-obj (list 'defun fn pairs)))
         (new-fn (and (symbolp fn) ; else irrelevant
                      (add-suffix fn (coerce (explode-atom suffix2 10)
                                             'string)))))
    (mv `(defun ,new-fn ,formals
           ,@(io-pairs-dcls fn wrld)
           (let ((pair (assoc ,formal ',pairs :test ',test)))
             (if pair
                 ,(if debug
                      `(prog2$
                        (cw "; DEBUG: Found io-pair for input ~x0.~|"
                            ,formal)
                        (cdr pair))
                    '(cdr pair))
               (,fn ,@formals))))
        `(defthm ,thm-name
           (equal (,fn ,@formals)
                  (,new-fn ,@formals))
           ,@(and hints `(:hints ,hints))
           :rule-classes nil))))

(defmacro unmemoize? (fn)
  `(make-event (if (memoizedp ,fn)
                   '(unmemoize ,fn)
                 '(value-triple nil))))

(defmacro use-io-pairs (fn pairs &key hints debug test)
  (declare (xargs :guard ; same as for assoc
                  (or (null test)
                      (equal test ''eq)
                      (equal test ''eql)
                      (equal test ''equal))))
  `(make-event
    (let ((fn ,fn)
          (pairs ,pairs)
          (hints ,hints)
          (debug ,debug)
          (test ,(or test ''equal))
          (wrld (w state)))
      (cond
       ((and (symbolp fn)
             (equal (stobjs-in fn wrld) '(nil))
             (equal (stobjs-out fn wrld) '(nil)))
        (mv-let (def thm)
          (use-io-pairs-helper fn pairs hints debug test state)
          (list 'progn
                def
                thm
                (list 'unmemoize? (kwote fn))
                (list 'memoize (kwote fn) :invoke (kwote (cadr def))))))
       (t (er hard 'use-io-pairs
              "The first argument of use-io-pairs must be a function symbol ~
               with a single non-stobj input and output.  That argument, ~x0, ~
               is thus illegal."
              fn))))))
