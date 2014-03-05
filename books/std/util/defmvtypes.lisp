; Standard Utilities Library
; Copyright (C) 2008-2014 Centaur Technology
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
; Original author: Jared Davis <jared@centtech.com>

(in-package "STD")
(include-book "deflist")
(include-book "std/strings/defs-program" :dir :system)
(defxdoc defmvtypes
  :parents (std/util)
  :short "Introduce type-prescription rules for a function that returns
multiple values."

  :long "<p>Defmvtypes is just a shorthand that allows you to quickly introduce
type-prescription rules for a function that returns multiple values.</p>

<p>General form:</p>

@({
 (defmvtypes fn return-types
    &key hyp)
})

<p>For example,</p>

@({
 (defmvtypes foo
   (true-listp nil booleanp (and (consp x) (true-listp x))))
})

<p>introduces three type-prescription rules:</p>
<ol>
 <li>@('(true-listp (mv-nth 0 (foo ...))')</li>
 <li>@('(booleanp (mv-nth 2 (foo ...))')</li>
 <li>@('(and (consp (mv-nth 3 (foo ...)))
             (true-listp (mv-nth 3 (foo ...))))')</li>
</ol>

<h3>Usage and Arguments</h3>

<p>Each of the @('return-types') should either be a plain symbol like
@('true-listp'), or a term whose only free variable is @('pkg::x'), where
@('pkg') is the package of @('fn').</p>

<p>The theorems introduced will be unconditional unless a @(':hyp') argument is
provided.  For instance,</p>

@({
 (defmvtypes foo
   (nil nil true-listp)
   :hyp (bar a b c))
})

<p>Would result in:</p>

@({
 (implies (bar a b c)
          (true-listp (mv-nth 2 (foo ...))))
})")

(defun defmvtypes-element-to-thm (spec ; the type specifier (symbol/term)
                                  hyp fn args
                                  place ; the return-value number
                                  )
  ;; Returns ((defthm ...)) or NIL
  (declare (xargs :mode :program))
  (if (not spec)
      nil
    (let* ((thmname (intern-in-package-of-symbol
                     (str::cat (symbol-name fn) "-MVTYPES-"
                               (coerce (explode-atom place 10) 'string))
                     fn))
           (x       (intern-in-package-of-symbol "X" fn))
           (rval    `(mv-nth ,place (,fn . ,args)))
           (concl   (cond
                     ((symbolp spec)
                      (list spec rval))
                     ((atom spec)
                      (er hard? 'defmvtypes-element-to-thm
                          "Bad return-value type specifier for defmvtypes: ~x0." spec))
                     (t
                      (let ((new (subst rval x spec)))
                        (if (equal new spec)
                            (er hard? 'defmvtypes-element-to-thm
                                "Bad return-value type specifier: does not mention ~x0: ~x1."
                                x spec)
                          new))))))
      `((defthm ,thmname
          ,(if hyp
               `(implies ,hyp ,concl)
             concl)
          :rule-classes :type-prescription
          :hints((and stable-under-simplificationp
                      '(:in-theory (enable (:executable-counterpart force))))))))))

(defun defmvtypes-elements-to-thms (specs hyp fn args place)
  (declare (xargs :mode :program))
  (if (atom specs)
      nil
    (append (defmvtypes-element-to-thm (car specs) hyp fn args place)
            (defmvtypes-elements-to-thms (cdr specs) hyp fn args (+ 1 place)))))

(defun defmvtypes-fn (specs fn hyp world)
  (declare (xargs :mode :program))
  (let ((args (getprop fn 'acl2::formals :bad 'acl2::current-acl2-world world)))
    (if (eq args :bad)
        (er hard? 'defmvtypes-fn "Failed to find formals for ~x0.~%" fn)
      `(encapsulate
         ()
         (local (in-theory (e/d (,fn)
                                ((:executable-counterpart force)))))
         ,@(defmvtypes-elements-to-thms specs hyp fn args 0)))))

(defmacro defmvtypes (fn specs &key hyp)
  `(make-event (defmvtypes-fn ',specs ',fn ',hyp (w state))))

;; Basic tests
(local
 (encapsulate
   ()
   (defund foo (x y)
     (mv (cons x y)
         0
         1
         (if x t nil)
         (cons x nil)))

   (defmvtypes foo
     (consp (equal x 0) posp booleanp (and (consp x) (true-listp x))))

   (defun bar (a b)
     (mv a b))

   (defmvtypes bar
     (consp integerp)
     :hyp (and (consp a)
               (integerp b)))))

