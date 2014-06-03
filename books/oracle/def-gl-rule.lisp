; Standard Utilities Library
; Copyright (C) 2014, Oracle and/or its affiliates. All rights reserved.
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
; Original author: David L. Rager <david.rager@oracle.com>

(in-package "ACL2")

(include-book "std/util/define" :dir :system)

(defxdoc def-gl-rule
  :parents (std/util)
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

(define find-and-remove-key (key lst)
  :short "Remove keyword <tt>key</tt> and associated value from list
          <tt>lst</tt>"
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
  (b* (((mv short rst)
        (find-and-remove-key :short rst))
       ((mv long rst)
        (find-and-remove-key :long rst))
       ((mv parents rst)
        (find-and-remove-key :parents rst))
       ((mv disabledp rst)
        (find-and-remove-key :disabledp rst))
       ((mv local rst)
        (find-and-remove-key :local rst))
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
