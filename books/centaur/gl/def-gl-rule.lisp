; Standard Utilities Library
; Copyright (C) 2014, Oracle and/or its affiliates. All rights reserved.
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
; Original author: David L. Rager <david.rager@oracle.com>

(in-package "GL")
(include-book "std/util/define" :dir :system)
(include-book "std/util/defrule" :dir :system)

(defxdoc def-gl-rule
  :parents (def-gl-thm)
  :short "A slightly enhanced version of @(see def-gl-thm)"
  :long "<p>@('def-gl-rule') is a drop-in replacement for @('def-gl-thm') that
adds:</p>

<ul>

<li>Integration with @(see xdoc).  You can give @(':parents'), @(':short'), and
@(':long') documentation right at the top level of the @('defrule').</li>

</ul>

<h3>Support for @('Local')</h3>

<p>Another option is to provide a non-@('nil') value to the keyword argument
@(':local').  This results in surrounding the rule with a @(see
acl2::local).</p>


<h3>@('Disabledp')</h3>

<p>Another option is to provide a non-@('nil') value to the keyword argument
@(':disabledp') (note the 'p' at the end).  This results in disabling the new
rule after its proof finishes.</p>

<p>Some examples:</p>

@({
  (def-gl-rule baz        -->  (local
      ...                        (encapsulate ()
      :local t)                    (defthm baz ...)))
})

@({
  (def-gl-rule baz        -->  (defthm baz ...)
      ...                      (in-theory (disable baz))
      :disabledp t)
})")

(local (xdoc::set-default-parents def-gl-rule))

(define find-and-remove-key (key lst)
  :short "Remove keyword <tt>key</tt> and associated value from list <tt>lst</tt>"
  (cond ((atom lst)
         (mv nil lst))
        ((and (equal (car lst) key)
              (atom (cdr lst)))
         (mv (er hard? __function__
                 "Car of lst matches key, when there is no associated value in
                  the lst.  Car is: ~x0.  Lst is: ~x1"
                 (car lst)
                 lst)
             nil))
        ((equal (car lst) key)
         (mv (cadr lst) (cddr lst)))
        (t
         (mv-let (val recur-lst)
           (find-and-remove-key key (cdr lst))
           (mv val (cons (car lst) recur-lst))))))

(defmacro def-gl-rule (name &rest rst)
  (b* (((mv short rst)     (find-and-remove-key :short rst))
       ((mv long rst)      (find-and-remove-key :long rst))
       ((mv parents rst)   (find-and-remove-key :parents rst))
       ((mv disabledp rst) (find-and-remove-key :disabledp rst))
       ((mv local rst)     (find-and-remove-key :local rst))
       (event
        `(defsection ,name
           :short ,short
           :long ,long
           :parents ,parents
           (def-gl-thm ,name ,@rst)
           ,@(if disabledp
                 `((in-theory (disable ,name)))
               nil))))
    (if local
        `(local ,event)
      event)))

(defmacro def-gl-ruled (name &rest rst)
  `(def-gl-rule ,name :disabledp t ,@rst))

(defmacro def-gl-rulel (name &rest rst)
  `(def-gl-rule ,name :local t ,@rst))

(defmacro def-gl-ruledl (name &rest rst)
  `(def-gl-rule ,name :local t :disabledp t ,@rst))
