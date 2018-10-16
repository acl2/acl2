; GL - A Symbolic Simulation Framework for ACL2
; Copyright (C) 2008-2013 Centaur Technology
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

(in-package "GL")
(include-book "defagg")
(include-book "tools/pattern-match" :dir :system)
(include-book "misc/untranslate-patterns" :dir :system)
(include-book "centaur/misc/numlist" :dir :system)

(defagg g-concrete (obj))
(defagg g-boolean (bool))
(defagg g-integer (bits))
(defagg g-ite (test then else))
(defagg g-apply (fn args) :notinline t)
(defagg g-var (name))

; Note: g-number used to be defined here.  It is no longer a core symbolic
; object type, so we don't define it here anymore, but we still support it as a
; shape spec construct so it is defined in shape-spec-defs.lisp.

(defsection g-int
  :parents (shape-specs)
  :short "Create a g-binding for an integer."
  :long "<p>This is a low-level way to create a custom shape specifier for a
signed integer.  You might generally prefer higher-level tools like @(see
auto-bindings).</p>"

  (defun g-int (start by n)
    (declare (xargs :guard (and (acl2-numberp start)
                                (acl2-numberp by)
                                (natp n))))
    (g-integer (numlist start by n))))

(defconst *g-keywords*
  '(:g-boolean :g-integer :g-concrete :g-ite :g-apply :g-var))



(defun g-keyword-symbolp (x)

;; Performance considerations: We'll be calling this function a lot on various
;; atoms.  We check symbolp first so that we skip the more expensive member
;; check on non-symbols.  Oddly, it doesn't seem to help to also check keywordp
;; -- it seems that's more expensive than member.  Also, in CCL benchmarks, in
;; general (member-eq x lst) is faster than (member x lst), but for some reason
;; (and (symbolp x) (member x lst)) is faster than
;; (and (symbolp x) (member-eq x lst)).

;; [Jared]: I put in an MBE equivalence here that seems to speed this up by about
;; 3x on some arguments.  It is slighly slower on conses but I don't think we care
;; too much about that.  I don't use member, so this now returns a boolean, which is
;; probably nice.  Here is some performance testing data.

;;   v1 -- symbolp, but member (no boolean fixing) instead of eq checks
;;   v2 -- symbolp, mbe with explicit eq checks

#||
 (in-package "GL")
 (let ((x (cons 1 1)))

  ;; v1 4.689 sec    v2 5.022 sec ;
   (time (loop for i fixnum from 1 to 1000000000 do (g-keyword-symbolp x)))

  ;; v1 24.760 sec   v2 9.201 sec ;
   (setq x 'foo)
   (time (loop for i fixnum from 1 to 1000000000 do (g-keyword-symbolp x)))

  ;; v1 4.682 sec    v2 5.018 sec ;
   (setq x 17)
   (time (loop for i fixnum from 1 to 1000000000 do (g-keyword-symbolp x)))

  ;; v1 15.388 sec   v2 5.367 sec ;
   (setq x :g-boolean)
   (time (loop for i fixnum from 1 to 1000000000 do (g-keyword-symbolp x)))

  ;; v1 17.395 sec   v2 6.375 sec ;
   (setq x :g-number)
   (time (loop for i fixnum from 1 to 1000000000 do (g-keyword-symbolp x)))

  ;; v1 18.732 sec   v2 7.277 sec ;
   (setq x :g-concrete)
   (time (loop for i fixnum from 1 to 1000000000 do (g-keyword-symbolp x)))

  ;; v1 24.086 sec   v2 9.199 sec ;
   (setq x :g-var)
   (time (loop for i fixnum from 1 to 1000000000 do (g-keyword-symbolp x))))
||#

  (declare (xargs :guard t))
  (and (symbolp x)
       (mbe :logic (if (member x *g-keywords*)
                       t
                     nil)
            :exec
            (or (eq x :g-boolean)
                (eq x :g-integer)
                (eq x :g-concrete)
                (eq x :g-ite)
                (eq x :g-apply)
                (eq x :g-var)))))

(in-theory (disable g-keyword-symbolp))



(defthmd g-keyword-symbolp-def
  (equal (g-keyword-symbolp x)
         (if (member-equal x *g-keywords*)
             t
           nil))
  :hints(("Goal" :in-theory (enable g-keyword-symbolp))))

(defthm not-g-keyword-symbol-when-not-symbol
  (implies (not (symbolp x))
           (not (g-keyword-symbolp x)))
  :hints(("Goal" :in-theory (enable g-keyword-symbolp)))
  :rule-classes ((:rewrite :backchain-limit-lst 0)
                 :type-prescription))

(defun gl-cons (x y)
  (declare (xargs :guard t))
  (cons (if (g-keyword-symbolp x)
            (g-concrete x)
          x)
        y))
