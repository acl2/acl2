; GL - A Symbolic Simulation Framework for ACL2
; Copyright (C) 2018 Centaur Technology
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
; Original author: Sol Swords <sswords@centtech.com>

(in-package "FGL")

(include-book "def-gl-rewrite")
(include-book "glcp-config")

;; This set of rules deals with a common problem in specs where something that
;; returns a non-Boolean value is typically used in a Boolean context -- think
;; (member-equal x lst).  In FGL, (member-equal x lst) is generally something
;; that needs to be represented using if-then-elses, which are problematic.  So
;; we produce an alternate representation here.  We first introduce a function
;; maybe-value that separately represents the Boolean equivalent and the full
;; data of an object.  -- its definition is just (and true (or val t)).  So it
;; is nonnil iff true is nonnil, but its full value is val if true and val are
;; both nonnil.

;; We use maybe-value to expose the Boolean equivalent of member-equal,
;; memberp-equal, while hiding away the real value in an equivalent call of
;; hide-member-equal, which we won't allow to expand or prove any rules about.


;; This function is just IF, but we'll turn off its definition.
(defun fgl-hidden-if (test then else)
  (if test then else))

(disable-definition fgl-hidden-if)

;; This function represents a value that is likely to be just treated as
;; Boolean, but may not actually be T when it is non-NIL.  The TRUE input
;; determines its truth value and VAL determines its actual form when non-NIL.
;; We use this function when we think we won't need the actual value of val,
;; just its truth value.
(defun maybe-value (true val)
  (and true
       (or val t)))

(disable-definition maybe-value)

;; Under IFF, maybe-value is just its truth value.
(def-gl-rewrite maybe-value-under-iff
  (iff (maybe-value true val)
       true))


;; To merge a maybe-value with some other object, merge with the test under an
;; IFF context and then merge the value using fgl-hidden-if.
(def-gl-branch-merge maybe-value-merge
  (equal (if test (maybe-value true val) else)
         (maybe-value (if test true (and else t)) (fgl-hidden-if test val else))))

;; We probably shouldn't need to compare maybe-value with equal, but this might
;; succeed if we end up needing to.
(def-gl-rewrite equal-of-maybe-value
  (equal (equal (maybe-value true val) x)
         (if true
             (if val
                 (equal x val)
               (equal x t))
           (not x))))
 
         
;; We'll represent member-equal using maybe-value.  Memberp-equal gives its
;; truth value:
(defun memberp-equal (x lst)
  (if (atom lst)
      nil
    (or (equal x (car lst))
        (memberp-equal x (cdr lst)))))

(def-gl-rewrite memberp-equal-of-cons
  (equal (memberp-equal x (cons a b))
         (or (equal x a) (memberp-equal x b))))

(def-gl-rewrite memberp-equal-of-nil
  (equal (memberp-equal x nil) nil))

;; We introduce a version of member-equal about which we won't prove any rules,
;; so as to hide it away in the value of the maybe-value:
(defun hide-member-equal (x lst)
  (member-equal x lst))

;; Turn off both member-equal and hide-member-equal...
(disable-definition member-equal)

(disable-definition hide-member-equal)

(defthm memberp-equal-iff-member-equal
  (iff (memberp-equal x lst) (member-equal x lst)))

;; Now when we see member-equal, we'll hide its full value away using
;; hide-member-equal and expose its Boolean value (memberp-equal) through
;; maybe-value.
(def-gl-rewrite member-equal-to-maybe-value
  (equal (member-equal x lst)
         (maybe-value (memberp-equal x lst) (hide-member-equal x lst))))

;; This makes our strategy work for (consp (member-equal x lst)) calls, though
;; this is kind of a roundabout way to get it.
(def-gl-rewrite consp-of-member-equal-result
  (implies (equal true (memberp-equal x lst))
           (equal (consp (maybe-value true (hide-member-equal x lst)))
                  true)))
