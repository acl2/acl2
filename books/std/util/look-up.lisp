; Standard Utilities Library
; Copyright (C) 2008-2014 Centaur Technology
;
; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/
;
; License: (An MIT/X11-style license)
;
;   Permission is hereby granted, free of charge, to any person obtaining a
;   copy of this software and associated documentation files (the "Software"),
;   to deal in the Software without restriction, including without limitation
;   the rights to use, copy, modify, merge, publish, distribute, sublicense,
;   and/or sell copies of the Software, and to permit persons to whom the
;   Software is furnished to do so, subject to the following conditions:
;
;   The above copyright notice and this permission notice shall be included in
;   all copies or substantial portions of the Software.
;
;   THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
;   IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
;   FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
;   AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
;   LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
;   FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
;   DEALINGS IN THE SOFTWARE.
;
; Original author: Jared Davis <jared@centtech.com>

(in-package "STD")
(include-book "support")

(defsection var-is-stobj-p
  :parents (support)
  :short "@(call var-is-stobj-p) checks whether @('var') is currently the name
of a @(see acl2::stobj)."

  (defund var-is-stobj-p (var world)
    (declare (xargs :guard (and (symbolp var)
                                (plist-worldp world))))
    (consp (getprop var 'acl2::stobj nil 'acl2::current-acl2-world world))))

(defsection look-up-formals
  :parents (support)
  :short "@(call look-up-formals) looks up the names of the arguments of the
function @('fn'), or causes a hard error if @('fn') isn't a function."

  (defund look-up-formals (fn world)
    (declare (xargs :guard (and (symbolp fn)
                                (plist-worldp world))))
    (b* ((__function__ 'look-up-formals)
         (look (getprop fn 'acl2::formals :bad 'acl2::current-acl2-world world))
         ((when (eq look :bad))
          (raise "Can't look up the formals for ~x0!" fn))
         ((unless (symbol-listp look))
          (raise "Expected a symbol-listp, but found ~x0!" look)))
      look))

  (local (in-theory (enable look-up-formals)))

  (defthm symbol-listp-of-look-up-formals
    (symbol-listp (look-up-formals fn world))))

(defsection look-up-guard
  :parents (support)
  :short "@(call look-up-guard) looks up the guard of the function @('fn'), or
causes a hard error if @('fn') isn't a function."

  (defund look-up-guard (fn world)
    (declare (xargs :guard (and (symbolp fn)
                                (plist-worldp world))))
    (b* ((?tmp
          ;; Silly... make sure the function exists, causing an error
          ;; otherwise.
          (look-up-formals fn world)))
      (getprop fn 'acl2::guard t 'acl2::current-acl2-world world))))

(defsection look-up-return-vals
  :parents (support)
  :short "@(call look-up-return-vals) returns the @('stobjs-out') property for
@('fn').  This is a list that may contain @('nil')s and @(see acl2::stobj) names,
with the same length as the number of return vals for @('fn')."

  (defund look-up-return-vals (fn world)
    (declare (xargs :guard (and (symbolp fn)
                                (plist-worldp world))))
    (b* ((__function__ 'look-up-return-vals)
         (stobjs-out
          (getprop fn 'acl2::stobjs-out :bad 'acl2::current-acl2-world world))
         ((when (eq stobjs-out :bad))
          (raise "Can't look up stobjs-out for ~x0!" fn)
          '(NIL))
         ((unless (and (consp stobjs-out)
                       (symbol-listp stobjs-out)))
          (raise "Expected stobjs-out to be a non-empty symbol-list, but ~
                  found ~x0."
                 stobjs-out)
          '(NIL)))
      stobjs-out))

  (local (in-theory (enable look-up-return-vals)))

  (defthm symbol-listp-of-look-up-return-vals
    (symbol-listp (look-up-return-vals fn world))))


(defsection look-up-wrapper-args
  :parents (support)
  :short "@(call look-up-wrapper-args) is like @(see look-up-formals), except
that @('wrapper') can be either a function or a macro, and in the macro case
the arguments we return may include lambda-list keywords; see @(see
macro-args)."

  (defund look-up-wrapper-args (wrapper world)
    (declare (xargs :guard (and (symbolp wrapper)
                                (plist-worldp world))))
    (b* ((__function__ 'look-up-wrapper-args)
         (look (getprop wrapper 'acl2::formals :bad
                        'acl2::current-acl2-world world))
         ((unless (eq look :bad))
          look)
         (look (getprop wrapper 'acl2::macro-args :bad
                        'acl2::current-acl2-world world))
         ((unless (eq look :bad))
          look))
      (raise "Failed to find formals or macro-args for ~x0!" wrapper))))



(defsection logic-mode-p
  :parents (support)
  :short "@(call logic-mode-p) looks up the function @('fn') and returns
@('t') if @('fn') is in logic mode, or @('nil') otherwise.  It causes a
hard error if @('fn') isn't a function."

  (defund logic-mode-p (fn world)
    (declare (xargs :guard (and (symbolp fn)
                                (plist-worldp world))))
    (b* ((__function__ 'logic-mode-p)
         (look (getprop fn 'acl2::formals :bad 'acl2::current-acl2-world world))
         ((when (eq look :bad))
          (raise "Can't look up the formals for ~x0!" fn))
         (symbol-class (getprop fn 'acl2::symbol-class nil 'acl2::current-acl2-world world))
         ((unless (member symbol-class '(:common-lisp-compliant
                                         :ideal
                                         :program)))
          (raise "Unexpected symbol-class for ~x0: ~x1." fn symbol-class)))
      (not (eq symbol-class :program))))

  (local (in-theory (enable logic-mode-p)))

  (defthm booleanp-of-look-up-formals
    (or (equal (logic-mode-p fn world) t)
        (equal (logic-mode-p fn world) nil))
    :rule-classes :type-prescription))
