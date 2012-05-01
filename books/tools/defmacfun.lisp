; Copyright (C) 2011 Centaur Technology
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

;; A common idiom is to define a function that can be run by a macro with, say,
;; an extensive list of keyword arguments.  If later I want to add more
;; arguments to the function and macro, this is annoying because I have to
;; change the argument list in three places -- the function, the macro argument
;; list, and the call of the function in the macro body.  The macro DEFMACFUN
;; defines the macro and function in one step, so you only have to change the
;; arglist in one place.  Basically, the user gives the argument
;; list for the macro and the declarations and body for the function.

;; In addition to the ACL2 lambda-list constructs &key, &optional, etc., we
;; also support the &auto construct, which always passes the value of a
;; particular term to the function.  This is useful for passing stobjs, for
;; example:
;; (defmacfun my-w (&auto state) (w state))
;; expands to
;; (defmacro my-w () (my-w-fn state))
;; (defun my-w-fn (state) (w state)).

(program)

(defconst *macfun-&words*
  '(&whole &optional &rest &body &key &allow-other-keys &auto))

(defun macfun-find-next-&word-index (formals)
  (if (atom formals)
      nil
    (if (member-eq (car formals) *macfun-&words*)
        0
      (let ((idx (macfun-find-next-&word-index (cdr formals))))
        (and idx (1+ idx))))))

(defun macfun-split-formals-at-next-&word (formals)
  (let ((idx (macfun-find-next-&word-index formals)))
    (if idx
        (mv (take idx formals)
            (nthcdr idx formals))
      (mv formals nil))))

(defun macfun-formals-to-macro-formals (formals)
  ;; Just strips out the &auto args.
  (let* ((mem (member-eq '&auto formals)))
    (if mem
        (let* ((len (len formals))
               (lenrest (len mem))
               (prefix (take (- len lenrest) formals))
               (suffix-idx (macfun-find-next-&word-index (cdr mem)))
               (suffix (and suffix-idx
                            (nthcdr suffix-idx (cdr mem)))))
          (append prefix suffix))
      formals)))

(defun macfun-key/opt/autos-to-function-formals (formals)
  (if (atom formals)
      nil
    (let ((rest (macfun-key/opt/autos-to-function-formals (cdr formals))))
      (case (len (car formals))
        (0 (cons (car formals) rest))
        (1 ;; not sure if this is legal, but fairly obvious
         (cons (caar formals) rest))
        (2 ;; just variable and default
         (cons (caar formals) rest))
        (3 ;; variable, default, and provided-p
         (list* (caar formals) (caddar formals) rest))
        (otherwise ;; skip and let defmacro hassle them
         rest)))))

;; Returns the function formals for the first few, and the unprocessed prefix.
(defun macfun-formals-to-function-formals1 (formals)
  (case (car formals)
    ((&whole &rest &body)
     (if (consp (cdr formals))
         (mv (list (cadr formals)) (cddr formals))
       (mv nil nil)))
    ((&optional &key &auto)
     (mv-let (key/opt/autos formals)
       (macfun-split-formals-at-next-&word (cdr formals))
       (mv (macfun-key/opt/autos-to-function-formals key/opt/autos)
           formals)))
    (&allow-other-keys
     ;; Should end here, unless maybe there are &auto args,
     ;; but we'll let defmacro make the call
     (mv nil (cdr formals)))
    (otherwise
     (mv-let (reqs rest)
       (macfun-split-formals-at-next-&word formals)
       (mv reqs rest)))))

(defun macfun-formals-to-function-formals (formals)
  (if (atom formals)
      nil
    ;; We can be pretty flexible here because defmacro will catch our
    ;; mistakes...
    ;; We may have some required vars at the beginning (or after
    ;; &whole, for example), so include those...
    (mv-let (fn-formals rest)
      (macfun-formals-to-function-formals1 formals)
      (append fn-formals
              (macfun-formals-to-function-formals rest)))))



(defun macfun-autos-to-function-actuals (autos)
  (if (atom autos)
      nil
    (cons (list 'quote (case (len (car autos))
                         (0 (car autos))
                         (1 ;; dumb case
                          (caar autos))
                         (2 ;; (varname term)
                          (cadar autos))
                         (otherwise (er hard? 'defmacfun
                                        "An &auto binding should either be just a variable
or a form (variable term), which ~x0 isn't.~%" (car autos)))))
          (macfun-autos-to-function-actuals (cdr autos)))))


(defun macfun-formals-to-function-actuals1 (formals)
  (case (car formals)
    ((&whole &rest &body)
     (if (consp (cdr formals))
         (mv (list (list 'list ''quote (cadr formals))) (cddr formals))
       (mv nil nil)))
    (&auto
     (mv-let (autos formals)
       (macfun-split-formals-at-next-&word (cdr formals))
       (mv (macfun-autos-to-function-actuals autos)
           formals)))
    ((&optional &key)
     (mv-let (key/opts formals)
       (macfun-split-formals-at-next-&word (cdr formals))
       (mv (macfun-key/opt/autos-to-function-formals key/opts)
           formals)))
    (&allow-other-keys
     ;; Should end here, unless maybe there are &auto args,
     ;; but we'll let defmacro make the call
     (mv nil (cdr formals)))
    (otherwise
     (mv-let (reqs rest)
       (macfun-split-formals-at-next-&word formals)
       (mv reqs rest)))))



(defun macfun-formals-to-function-actuals (formals)
  (if (atom formals)
      nil
    ;; This is almost all the same as macfun-formals-to-function-formals, but
    ;; autos are different.
    (mv-let (actuals rest)
      (macfun-formals-to-function-actuals1 formals)
      (append actuals
              (macfun-formals-to-function-actuals rest)))))


(defun macfun-get-nonstrings (x)
  (if (atom x)
      nil
    (if (stringp (car x))
        (macfun-get-nonstrings (cdr x))
      (cons (car x)
            (macfun-get-nonstrings (cdr x))))))


(defun macfun-get-strings (x)
  (if (atom x)
      nil
    (if (stringp (car x))
        (cons (car x)
              (macfun-get-strings (cdr x)))
      (macfun-get-strings (cdr x)))))

(defun defmacfun-fn (name formals doc-decl-body)
  (let* ((bodylst (last doc-decl-body))
         (doc-decl (butlast doc-decl-body 1))
         (docs (macfun-get-strings doc-decl))
         (decls (macfun-get-nonstrings doc-decl))
         (fnname (intern-in-package-of-symbol
                  (concatenate 'string (symbol-name name) "-FN")
                  name))
         (fn-formals (macfun-formals-to-function-formals formals))
         (fn-actuals (macfun-formals-to-function-actuals formals))
         (mac-formals (macfun-formals-to-macro-formals formals)))
    `(progn
       ;; define the macro first to check for syntax errors
       (defmacro ,name ,mac-formals
         ,@docs
         (list ',fnname . ,fn-actuals))

       (defun ,fnname ,fn-formals
         ,@decls . ,bodylst))))

(defmacro defmacfun (name formals &rest doc-decl-body)
  (defmacfun-fn name formals doc-decl-body))
