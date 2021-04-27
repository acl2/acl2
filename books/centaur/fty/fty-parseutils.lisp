; FTY type support library
; Copyright (C) 2014 Centaur Technology
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

(in-package "FTY")
(include-book "database")
(include-book "fixtype")
(include-book "std/util/define" :dir :system)
(program)


; Basic Parsing Helpers -------------------------------------------------------

(defmacro getarg-nonnil! (key default kwd-alist)
  "Same as getarg, but use the default value unless we find a non-nil value."
  `(let* ((getarg-look (assoc ,key ,kwd-alist)))
     (or (and getarg-look
              (cdr getarg-look))
         ,default)))

(defmacro getarg! (key default kwd-alist)
  "Same as getarg, but a macro so that the default value is only constructed if
   needed."
  `(let* ((getarg-look (assoc ,key ,kwd-alist)))
     (if getarg-look
         (cdr getarg-look)
       ,default)))

(defconst *inline-keywords* '(:kind :fix :acc :xtor))
(defconst *inline-defaults* '(:kind :fix :acc))

(define get-deftypes-inline-opt (default kwd-alist)
  (b* ((inline (getarg :inline default kwd-alist))
       (inline (if (eq inline :all) *inline-keywords* inline))
       ((unless (subsetp inline *inline-keywords*))
        (raise ":inline must be a subset of ~x0, but is ~x1"
               *inline-keywords* inline)))
    inline))

;; [Jared] BOZO can probably simplify the interface to get rid of no-count and
;; just use :count nil.

(define flextype-get-count-fn (name kwd-alist)
  ;; :count nil means the same as no-count
  (b* ((count-look (assoc :count kwd-alist))
       (no-count   (getarg :no-count nil kwd-alist))
       ((when (and (cdr count-look) no-count))
        (raise "Confused: a count function name was provided with :no-count t"))
       ((when count-look)
        (cdr count-look)))
    (and (not (getarg :no-count nil kwd-alist))
         (intern-in-package-of-symbol (cat (symbol-name name) "-COUNT")
                                      name))))

(define find-symbols-named-x (tree)
  ;; This might not be quite right in the case of "unhygenic" macros, but is
  ;; mainly intended as a way to prevent the user from getting horrible error
  ;; messages anyway, so it's unlikely to be any kind of problem.
  (if (atom tree)
      (and (symbolp tree)
           (equal (symbol-name tree) "X")
           (list tree))
    (union-eq (find-symbols-named-x (car tree))
              (find-symbols-named-x (cdr tree)))))


; Type Lookup -----------------------------------------------------------------
;
; Looking up the correspondence between predicates, fixing functions, and
; equivalence relations is tricky since we support the introduction of mutually
; recursive types: we have to look not only at the existing fixtypes table, but
; also at the new types we are introducing.

(defconst *known-flextype-generators*
  '(defflexsum
     defprod
     deftagsum
     defoption
     deftranssum
     deflist
     defalist
     defmap
     defset))

(define flextype-form->fixtype (user-level-form)
  "Create the new fixtype binding for a new type we're going to introduce."
  (b* (((unless (and (consp user-level-form)
                     (member (first user-level-form) *known-flextype-generators*)))
        (raise "Not a valid top-level deftypes form: ~x0.~%
                Expected ~v1.~%"
               (if (consp user-level-form)
                   (list (first user-level-form) '[...])
                 user-level-form)
               *known-flextype-generators*))
       ((unless (and (consp (cdr user-level-form))
                     (symbolp (second user-level-form))))
        (raise "Not a valid top-level fixtype definition: ~x0~%"
               (list (first user-level-form) (second user-level-form) '[...])))
       ((list* & name args) user-level-form)
       (fix (or (cadr (member :fix args))
                (intern-in-package-of-symbol (cat (symbol-name name) "-FIX") name)))
       (pred (or (cadr (member :pred args))
                 (intern-in-package-of-symbol (cat (symbol-name name) "-P") name)))
       (equiv (or (cadr (member :equiv args))
                  (intern-in-package-of-symbol (cat (symbol-name name) "-EQUIV") name))))
    (cons name
          (make-fixtype :name name
                        :pred pred
                        :fix fix
                        :equiv equiv
                        :executablep t
                        :equiv-means-fixes-equal equiv))))

(define flextype-forms->fixtypes (user-level-forms)
  "Create the new fixtype bindings for all of the new types we're going to introduce."
  (if (atom user-level-forms)
      nil
    (cons (flextype-form->fixtype (car user-level-forms))
          (flextype-forms->fixtypes (cdr user-level-forms)))))

(define get-pred/fix/equiv
  ((type         "Type we want to look up.")
   (our-fixtypes "Fixtypes for the new types we're currently defining.")
   (fixtypes     "Existing fixtypes that have already been defined previously."))
  :returns (mv (pred  "Name of the recognizer predicate for type.")
               (fix   "Name of the fixing function for type.")
               (equiv "Name of the equivalence relation for type.")
               (rec-p "True if this type is part of the mutual recursion."))
  (b* (((unless type)
        ;; Special convenience so that NIL can be used for untyped fields.
        (mv nil nil 'equal nil))
       (fixtype1 (find-fixtype type our-fixtypes))
       (fixtype  (or fixtype1
                     (find-fixtype type fixtypes)))
       ((unless fixtype)
        (raise "Type ~x0 doesn't have an associated fixing function.  Please ~
                provide that association using ~x1.~%" type 'deffixtype)
        (mv nil nil 'equal nil)))
    (mv (fixtype->pred fixtype)
        (fixtype->fix fixtype)
        (fixtype->equiv fixtype)
        ;; It's recursive if it's being newly defined.
        (and fixtype1 t))))



(define check-flexlist-already-defined (pred kwd-alist our-fixtypes ctx state)
  ;; Special function for inferring already-definedp
  (b* (((when (< 1 (len our-fixtypes)))
        ;; Defining more than one fixtype.  We don't currently support this for
        ;; already-defined lists/alists, so assume we're not already-defined.
        (mv nil (getarg :true-listp nil kwd-alist)))
       (existing-formals (fgetprop pred 'acl2::formals t (w state)))
       (already-defined (not (eq existing-formals t)))
       (- (and already-defined
               (cw "NOTE: Using existing definition of ~x0.~%" pred)))
       (- (or (not already-defined)
              (eql (len existing-formals) 1)
              (er hard? ctx
                  "~x0 is already defined in an incompatible manner: it ~
                   should take exactly 1 input, but its formals are ~x1"
                  pred existing-formals)))
       (true-listp (if (not already-defined)
                       (getarg :true-listp nil kwd-alist)
                     (b* (((mv err res) (acl2::magic-ev-fncall
                                         pred '(t) state t nil))
                          ((when err)
                           (er hard? ctx
                               "Couldn't run ~x0 to figure out if it required true-listp: ~@1"
                               pred res))
                          (option (assoc :true-listp kwd-alist))
                          ((unless (or (atom option) (eq (cdr option) (not res))))
                           (er hard? ctx
                               "The existing definition of ~x0 ~s1 its input ~
                                to be a true-list, but the :true-listp option ~
                                given was ~x2."
                               pred (if res "does not require" "requires")
                               (cdr option))))
                       (not res)))))
    (mv already-defined true-listp)))

(define check-flexlist-fix-already-defined (fix kwd-alist our-fixtypes ctx state)
  (declare (ignorable kwd-alist))
  ;; Special function for inferring already-definedp
  (b* (((when (< 1 (len our-fixtypes)))
        ;; Defining more than one fixtype.  We don't currently support this for
        ;; already-defined lists/alists, so assume we're not already-defined.
        nil)
       (fix$inline (acl2::add-suffix fix acl2::*inline-suffix*))
       (existing-formals (fgetprop fix$inline 'acl2::formals t (w state)))
       (already-defined (not (eq existing-formals t)))
       (- (and already-defined
               (cw "NOTE: Using existing definition of ~x0.~%" fix)))
       (- (or (not already-defined)
              (eql (len existing-formals) 1)
              (er hard? ctx
                  "~x0 is already defined in an incompatible manner: it ~
                   should take exactly 1 input, but its formals are ~x1"
                  fix existing-formals)))
       ;; It isn't convenient to do a check like this for the fixing function,
       ;; because usually its guard requires that the input be already
       ;; well-formed.  We could use with-guard-checking-error-triple but then
       ;; we'd have to return state.  For now, if the fix has the wrong
       ;; definition, we'll most likely just fail on one of the theorems.
       ;; (true-listp (if (not already-defined)
       ;;                 (getarg :true-listp nil kwd-alist)
       ;;               (b* (((mv err res) (acl2::magic-ev-fncall
       ;;                                   fix '(t) state t nil))
       ;;                    ((when err)
       ;;                     (er hard? ctx
       ;;                         "Couldn't run ~x0 to figure out if it required true-listp: ~@1"
       ;;                         pred res))
       ;;                    (option (assoc :true-listp kwd-alist))
       ;;                    ((unless (or (atom option) (eq (cdr option) (not res))))
       ;;                     (er hard? ctx
       ;;                         "The existing definition of ~x0 ~s1 its input ~
       ;;                          to be a true-list, but the :true-listp option ~
       ;;                          given was ~x2."
       ;;                         pred (if res "does not require" "requires")
       ;;                         (cdr option))))
       ;;                 (not res))))
       )
    already-defined))

(defun extra-binder-names->acc-alist (names type-name)
  (if (atom names)
      nil
    (cons (if (consp (car names))
              (car names)
            (cons (car names)
                  (intern-in-package-of-symbol
                   (cat (symbol-name type-name) "->" (symbol-name (car names)))
                   type-name)))
          (extra-binder-names->acc-alist (cdr names) type-name))))
