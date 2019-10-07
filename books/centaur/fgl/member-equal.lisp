; FGL - A Symbolic Simulation Framework for ACL2
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

(include-book "def-fgl-rewrite")
(include-book "config")
(include-book "syntax-bind")
(include-book "centaur/misc/starlogic" :dir :system)
(local (in-theory (enable if!)))

;; This set of rules deals with a common problem in specs where something that
;; returns a non-Boolean value is typically used in a Boolean context -- think
;; (member-equal x lst).  In FGL, (member-equal x lst) is generally something
;; that needs to be represented using if-then-elses, which are problematic.  So
;; we produce an alternate representation here.  We first introduce a function
;; maybe-list that separately represents the Boolean saying whether it's a cons
;; or nil, and the actual object -- its definition is just (and consp (if
;; (consp val) val '(t))).  So it is consp iff consp is nonnil, and a cons
;; otherwise.

;; We use maybe-list to expose the Boolean equivalent of member-equal,
;; memberp-equal, while hiding away the real value in an equivalent call of
;; hide-member-equal, which we won't allow to expand or prove any rules about.

;; Using maybe-list instead of maybe-true allows us to also support use of the
;; idiom (consp (member ...)).  There are some complications regarding if
;; branch merging with using maybe-list instead of maybe-true, so in some cases
;; we revert to using maybe-true.


;; ;; This function is just IF, but we'll turn off its definition.
;; (defun fgl-hidden-if (test then else)
;;   (if test then else))

;; (disable-definition fgl-hidden-if)

;; This function represents a value that is likely to be just treated as
;; Boolean but is actually either a cons or NIL.  The CONSP input determines
;; whether it is consp or nil, and VAL determines its actual form when non-NIL.
;; We use this function when we think we won't need the actual value of val,
;; just whether it is consp or nil.
(defun maybe-list (consp val)
  (and consp
       (if (consp val)
           val
         '(t))))

(disable-definition maybe-list)

;; Under IFF, maybe-list is just its truth value.
(def-fgl-rewrite maybe-list-under-iff
  (iff (maybe-list true val)
       true))

;; Also under CONSP.
(def-fgl-rewrite consp-of-maybe-list
  (equal (consp (maybe-list true val))
         (and true t)))

(defun maybe-consp (x)
  (or (consp x) (not x)))

(disable-definition maybe-consp)

(def-fgl-rewrite maybe-consp-of-cons
  (maybe-consp (cons x y)))

(def-fgl-rewrite maybe-consp-of-maybe-list
  (maybe-consp (maybe-list consp val)))


(defun maybe-true (truep val)
  (and truep
       (or val t)))

(disable-definition maybe-true)

(def-fgl-rewrite maybe-true-under-iff
  (iff (maybe-true truep val)
       truep))

;; This supports cases like
;; (or ... (member k x) (member k y))
;; where the ... may or may not also be member checks.
;; When they are member checks, we support keeping the aggregate in maybe-list
;; form so that we can support both simple Boolean checks and consp checks of
;; the OR.  When they are not member checks, we revert to maybe-true form,
;; which will still support Boolean checks but not consp checks.
(def-fgl-branch-merge maybe-list-merge
  (equal (if test (maybe-list true val) else)
         (b* ((maybe-consp (maybe-consp else))
              (maybe-consp-true (syntax-bind maybe-consp-true (eq maybe-consp t))))
           (if (and* maybe-consp-true maybe-consp)
               (maybe-list (if test true (consp else)) (if! test val else))
             (maybe-true (if test true (and else t))
                         (if! test (if! (consp val) val '(t)) else))))))

(def-fgl-branch-merge maybe-true-merge
  (equal (if test (maybe-true true val) else)
         (maybe-true (if test true (and else t))
                     (if! test val else))))

;; We probably shouldn't need to compare maybe-list with equal, but this might
;; succeed if we end up needing to.
(def-fgl-rewrite equal-of-maybe-list
  (equal (equal (maybe-list true val) x)
         (if true
             (if (consp val)
                 (equal x val)
               (equal x '(t)))
           (not x))))

(def-fgl-rewrite equal-of-maybe-true
  (equal (equal (maybe-true true val) x)
         (if true
             (if val
                 (equal x val)
               (equal x t))
           (not x))))
 
         
;; We'll represent member-equal using maybe-list.  Memberp-equal gives its
;; truth value:
(defun memberp-equal (x lst)
  (if (atom lst)
      nil
    (or (equal x (car lst))
        (memberp-equal x (cdr lst)))))

(def-fgl-rewrite memberp-equal-of-cons
  (equal (memberp-equal x (cons a b))
         (or (equal x a) (memberp-equal x b))))

(def-fgl-rewrite memberp-equal-of-nil
  (equal (memberp-equal x nil) nil))

;; We introduce a version of member-equal about which we won't prove any rules,
;; so as to hide it away in the value of the maybe-list:
(defun hide-member-equal (x lst)
  (member-equal x lst))

;; Turn off both member-equal and hide-member-equal...
(disable-definition member-equal)

(disable-definition hide-member-equal)

(defthm memberp-equal-iff-member-equal
  (iff (memberp-equal x lst) (member-equal x lst)))

(def-fgl-rewrite maybe-consp-of-hide-member-equal
  (maybe-consp (hide-member-equal x lst)))

;; Now when we see member-equal, we'll hide its full value away using
;; hide-member-equal and expose its Boolean value (memberp-equal) through
;; maybe-list.
(def-fgl-rewrite member-equal-to-maybe-list
  (equal (member-equal x lst)
         (maybe-list (memberp-equal x lst) (hide-member-equal x lst))))


