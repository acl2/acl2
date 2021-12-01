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

(include-book "aabf")
(include-book "std/strings/defs-program" :dir :system)

;; AABF-NEST is a macro that makes it easier to construct logic in an AABF
;; manager.  It takes something like this:
;;    (aabf-nest (aabf-bitnot (list (aabf-and (or a b c) d) e)) man)
;; and turns it into:
;; (b* (((mv or0 man) (aabf-or b c man))
;;      ((mv or1 man) (aabf-or a or0 man))
;;      ((mv aabf-and2 man) (aabf-and or1 e man)))
;;      ((mv aabf-bitnot man) (aabf-bitnot (list aabf-and2) man)))
;;   (mv aabf-bitnot man))
;; That is, it makes it so that you can elide the MAN parameter and return
;; value from each function call and nest them as if they were returning just
;; the logical result, not the manager stobj.

;; MANRET and DEF-MANRET-BINDER are macros that support AABF-NEST and allow it
;; support functions extensibly.  The MANRET binder works more or less as follows:
;;    (b* (((manret ans man) (foo a b c))) ...)
;; expands to
;;    (b* (((manret-foo ans man) (foo a b c))) ...)
;; The way this expands depends on how the MANRET binder for FOO is defined.
;; If it was defined using
;;  (def-manret-binder foo) or (def-manret-binder foo :returns-man t :takes-man t),
;; then it expands to:
;;    (b* (((mv foo man) (foo a b c man))) ...)
;; If it was defined using (def-manret-binder foo :returns-man nil):
;;    (b* ((foo          (foo a b c man))) ...)
;; If it was defined using (def-manret-binder foo :takes-man nil):
;;    (b* ((foo          (foo a b c))) ...).

;; This helps AABF-NEST extend to support new functions: when it encounters a
;; function call (foo a b c) for which it doesn't have built-in support, it
;; uses MANRET to produce its expansion.


(acl2::def-b*-binder manret
  :decls ((declare (xargs :guard
                          #!acl2 (and (consp forms)
                                      (consp (car forms))
                                      (symbolp (caar forms))
                                      (not (cdr forms))))))
  :body
  (b* ((fnname (caar acl2::forms))
       (macroname (intern$ (concatenate 'string "PATBIND-MANRET-" (symbol-name fnname)) "FGL")))
    (list macroname args acl2::forms acl2::rest-expr)))


(defmacro def-manret-binder (fn &key (returns-man 't) (takes-man 't))
  (b* (((unless (symbolp fn)) (er hard? 'def-manret-binder "Fn must be a symbol"))
       (returns-man (and returns-man takes-man)))
    `(acl2::def-b*-binder ,(intern$ (concatenate 'string "MANRET-" (symbol-name fn)) "FGL")
       :body
       (b* ((varname (car args))
            ,@(and (or returns-man takes-man) '((man (cadr args)))))
         `(b* ((,,(if returns-man
                      '`(mv ,varname ,man)
                     'varname)
                ,,(if takes-man
                      '`(,@(car acl2::forms) ,man)
                    '(car acl2::forms))))
            ,acl2::rest-expr)))))


(def-manret-binder aabf-true :takes-man nil)
(def-manret-binder aabf-false :takes-man nil)
(def-manret-binder aabf-not :returns-man nil)
(def-manret-binder aabf-and)
(def-manret-binder aabf-or)
(def-manret-binder aabf-xor)
(def-manret-binder aabf-iff)
(def-manret-binder aabf-ite)


(mutual-recursion
 (defun aabf-nest-fn (x varnum man acc)
   (declare (Xargs :mode :program))
   (b* (((when (atom x)) (mv x varnum acc))
        (fn (car x))
        ((when (eq fn 'quote)) (mv x varnum acc))
        ((when (eq fn 'not))
         (b* (((mv expr varnum acc) (aabf-nest-fn (second x) varnum man acc)))
           (mv `(aabf-not ,expr ,man) varnum acc)))
        ((when (member fn '(and or xor iff)))
         (aabf-binary-nestlist-fn (car x) (cdr x) varnum man acc))
        ((when (eq fn 'ite))
         (b* (((mv test varnum acc) (aabf-nest-fn (second x) varnum man acc))
              ((mv then varnum acc) (aabf-nest-fn (third x) varnum man acc))
              ((mv else varnum acc) (aabf-nest-fn (fourth x) varnum man acc))
              (var (intern$ (str::cat "ITE" (str::nat-to-dec-string varnum)) "FGL"))
              (acc (cons `((mv ,var ,man) (aabf-ite ,test ,then ,else ,man)) acc)))
           (mv var (1+ varnum) acc)))
        ((unless (symbolp fn))
         (er hard? 'aabf-nest-fn "Bad function symbol: ~x0~%" (car x))
         (mv nil varnum acc))
        ((when (or (assoc-eq fn acl2::*primitive-formals-and-guards*)
                   (member fn '(list list*))))
         (b* (((mv args varnum acc) (aabf-nestlist-fn (cdr x) varnum man acc)))
           (mv (cons fn args) varnum acc)))
        ((mv args varnum acc) (aabf-nestlist-fn (cdr x) varnum man acc))
        (var (intern$ (str::cat (symbol-name fn) (str::nat-to-dec-string varnum)) "FGL"))
        (acc (cons `((manret ,var ,man) (,fn . ,args)) acc)))
     (mv var (1+ varnum) acc)))

 (defun aabf-nestlist-fn (x varnum man acc)
   (b* (((when (atom x))
         (mv nil varnum acc))
        ((mv first varnum acc) (aabf-nest-fn (car x) varnum man acc))
        ((mv rest varnum acc) (aabf-nestlist-fn (cdr x) varnum man acc)))
     (mv (cons first rest) varnum acc)))

 (defun aabf-binary-nestlist-fn (op x varnum man acc)
   (declare (Xargs :mode :program))
   (b* (((when (atom x))
         (mv (case op
               ((and iff) '(aabf-true))
               (t   '(aabf-false)))
             varnum acc))
        ((when (atom (cdr x)))
         (aabf-nest-fn (car x) varnum man acc))
        ((mv first varnum acc) (aabf-nest-fn (car x) varnum man acc))
        ((mv rest varnum acc) (aabf-binary-nestlist-fn op (cdr x) varnum man acc))
        (var (intern$ (str::cat (symbol-name op) (str::nat-to-dec-string varnum)) "FGL"))
        (acc (cons `((mv ,var ,man)
                     (,(case op
                         (and 'aabf-and)
                         (or 'aabf-or)
                         (xor 'aabf-xor)
                         (iff 'aabf-iff))
                      ,first ,rest ,man))
                   acc)))
     (mv var (1+ varnum) acc))))

(defmacro aabf-nest (nest man)
  (b* (((mv res ?varnum acc) (aabf-nest-fn nest 0 man nil)))
    `(b* ,(reverse acc)
       (mv ,res ,man))))
