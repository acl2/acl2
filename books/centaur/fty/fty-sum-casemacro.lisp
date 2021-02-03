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

(include-book "std/util/support" :dir :system)

(program)

;; Two formats for case macro specs:

;; When you have a kind function producing a symbol giving the kind:
;; kind-casemacro-spec = (macro-name kind-function-name kind-case-spec *)
;; kind-case-spec = (kind-name ctor-name) | (kind-name (subkind-name +) ctor-name)

;; This last form of case spec supports cases where the object could be more
;; than one distinct kind.  When this sort of thing is present, then the
;; possible case keywords are different from the possible kinds of objects;
;; we'll say the former are "case kinds" and the latter are "prod kinds".  The
;; case kinds are just the strip-cars of the case-specs.  The prod kinds are
;; given by kind-casemacro-prod-kinds.

(defun kind-casemacro-casespec-p (spec)
  (and (consp spec)
       (symbolp (car spec))
       (consp (cdr spec))
       (if (atom (cadr spec))
           (and (symbolp (cadr spec))
                (not (cddr spec)))
         (and (consp (cadr spec))
              (symbol-listp (cadr spec))
              (consp (cddr spec))
              (symbolp (caddr spec))
              (not (cdddr spec))))))

(defun kind-casemacro-casespecs-p (specs)
  (if (atom specs)
      (eq specs nil)
    (and (kind-casemacro-casespec-p (car specs))
         (kind-casemacro-casespecs-p (cdr specs)))))

(defun kind-casemacro-spec-p (spec)
  (and (consp spec)
       (symbolp (car spec)) ;; macro-name
       (consp (cdr spec))
       (symbolp (cadr spec)) ;; kind name
       (kind-casemacro-casespecs-p (cddr spec))))
       


(defun kind-casemacro-cases (var cases kwd-alist)
  (declare (xargs :guard (kind-casemacro-casespecs-p cases)))
  (b* (((when (atom kwd-alist)) nil)
       ((when (eq (caar kwd-alist) :otherwise))
        `((otherwise ,(cdar kwd-alist))))
       (kind (caar kwd-alist))
       (case-spec (cdr (assoc kind cases)))
       (subkindsp (consp (car case-spec)))
       (ctor (if subkindsp (cadr case-spec) (car case-spec))))
    (cons `(,(cond ((atom (cdr kwd-alist)) 'otherwise)
                   (subkindsp (car case-spec))
                   (t kind))
            (b* (((,ctor ,var :quietp t)))
              ,(cdar kwd-alist)))
          (kind-casemacro-cases var cases (cdr kwd-alist)))))

(defun kind-casemacro-prod-kinds (cases)
  (declare (xargs :guard (kind-casemacro-casespecs-p cases)))
  (if (atom cases)
      nil
    (if (consp (cadar cases))
        (append (cadar cases) (kind-casemacro-prod-kinds (cdr cases)))
      (cons (caar cases) (kind-casemacro-prod-kinds (cdr cases))))))

(defun kind-casemacro-check-prod-kinds-covered (cases keys seen)
  (declare (xargs :guard (kind-casemacro-casespecs-p cases)))
  (b* (((when (atom keys))
        ;; Check whether we covered all the prod-kinds.
        (let ((diff (set-difference-eq (kind-casemacro-prod-kinds cases) seen)))
          (and diff
               (er hard? 'kind-casemacro-fn "No case covers product kinds ~x0~%"
                   (remove-duplicates-eq diff)))))
       (kind (car keys))
       ((when (eq kind :otherwise))
        ;; Check whether there are any remaining cases.
        (let ((diff (set-difference-eq (kind-casemacro-prod-kinds cases) seen)))
          (and (not diff)
               (er hard? 'kind-casemacro-fn "Redundant :otherwise entry.~%"))))
       (case-spec (cdr (assoc kind cases)))
       (prods (if (consp (car case-spec)) (car case-spec) (list kind)))
       ((when (subsetp prods seen))
        (er hard? 'kind-casemacro-fn "Redundant case: ~x0~%" kind)))
    (kind-casemacro-check-prod-kinds-covered cases (cdr keys)
                                             (append prods seen))))

(defun kind-casemacro-fn (var-or-expr rest-args case-spec)
  (b* (((unless (kind-casemacro-spec-p case-spec))
        (er hard? 'kind-casemacro-fn "Bad case-spec: ~x0~%" case-spec))
       ((list* macro-name kind-fn case-specs) case-spec)
       (case-kinds (remove-duplicates-eq (strip-cars case-specs)))
       (prod-kinds (remove-duplicates-eq (kind-casemacro-prod-kinds case-specs)))
       ((when (and (eql (len rest-args) 1)
                   (or (atom (car rest-args))
                       (eq (caar rest-args) 'quote))))
        (cond ((and (atom (car rest-args))
                    (member-eq (car rest-args) prod-kinds))
               ;; Special case: (foo-case expr :kind) becomes (eq (foo-kind expr) :kind)
               `(eq (,kind-fn ,var-or-expr) ,(car rest-args)))
              ((and (atom (car rest-args))
                    (member-eq (car rest-args) case-kinds))
               ;; It's a case-kind and not a prod-kind.  That means it has a list of subkinds in its entry.
               `(member-eq (,kind-fn ,var-or-expr) ',(cadr (assoc (car rest-args) case-specs))))
              ((and (eq (caar rest-args) 'quote)
                    (true-listp (cadr rest-args))
                    (subsetp (cadr rest-args) prod-kinds))
               ;; Special case: (foo-case expr '(:kind1 :kind2))
               ;; becomes (member-eq (foo-kind expr) '(:kind1 :kind2))
               `(member-eq (,kind-fn ,var-or-expr) ,(car rest-args)))
              (t (cond ((equal case-kinds prod-kinds)
                        (er hard? macro-name "Bad argument: ~x0~% Must be one of ~x1 or a quoted subset.~%" 
                            (car rest-args) case-kinds))
                       (t (er hard? macro-name "Bad argument: ~x0~% Must be one of ~x1 or a quoted subset of ~x2.~%"
                              (car rest-args)
                              (union-eq prod-kinds case-kinds)
                              prod-kinds))))))
       ((when (consp var-or-expr))
        (er hard? macro-name "Expected a variable, rather than: ~x0" var-or-expr))
       (var var-or-expr)

       (allowed-keywordlist-keys (append case-kinds '(:otherwise)))
       (allowed-parenthesized-keys (append case-kinds '(acl2::otherwise :otherwise acl2::&)))
                     
       ((mv kwd-alist rest)
        (extract-keywords macro-name
                          allowed-keywordlist-keys
                          rest-args nil))

       ((when (and rest kwd-alist))
        ;; Note: if we ever want to allow keyword options that aren't themselves cases,
        ;; change this error condition.
        ;; For now, only allow one kind of syntax --
        ;; either :foo bar :baz fuz
        ;; or    (:foo bar) (:baz fuz)
        ;; but not :foo bar (:baz fuz).
        (er hard? macro-name "Inconsistent syntax: ~x0" rest-args))

       ((unless (or kwd-alist
                    (and (alistp rest)
                         (true-list-listp rest)
                         ;; weaken this?
                         (subsetp (strip-cars rest) allowed-parenthesized-keys))))
        (er hard? macro-name "Malformed cases: ~x0~%" rest))
       
       (kwd-alist (reverse kwd-alist))

       (keys (if kwd-alist
                 (strip-cars kwd-alist)
               (sublis '((acl2::otherwise . :otherwise)
                         (acl2::&         . :otherwise))
                       (strip-cars rest))))
       (vals (if kwd-alist
                 (strip-cdrs kwd-alist)
               (pairlis$ (make-list (len rest) :initial-element 'progn$)
                         (strip-cdrs rest))))
       ((unless (<= (len (member :otherwise keys)) 1))
        ;; otherwise must be last or not exist
        (er hard? macro-name "Otherwise case must be last"))
       (- (kind-casemacro-check-prod-kinds-covered case-specs keys nil))

       (kind-kwd-alist (or kwd-alist (pairlis$ keys vals)))
                   
       (body
        (let ((var.kind (intern-in-package-of-symbol
                         (concatenate 'string (symbol-name var) ".KIND")
                         (if (equal (symbol-package-name var) "COMMON-LISP")
                             'acl2::acl2
                           var))))
          `(let* ((,var.kind (,kind-fn ,var)))
             (case ,var.kind
               . ,(kind-casemacro-cases var case-specs kind-kwd-alist))))))
    body))



;; When you just have various condition expressions determing which kind:
;; cond-casemacro-spec = (macro-name cond-var cond-case-spec *)
;; cond-case-spec = (kind-name cond-expr ctor-name)


(defun cond-casemacro-casespec-p (spec)
  (and (consp spec)
       (symbolp (car spec))
       (consp (cdr spec))
       ;; cadr spec is some expression...
       (consp (cddr spec))
       (symbolp (caddr spec))
       (not (cdddr spec))))

(defun cond-casemacro-casespecs-p (specs)
  (if (atom specs)
      (eq specs nil)
    (and (cond-casemacro-casespec-p (car specs))
         (cond-casemacro-casespecs-p (cdr specs)))))

(defun cond-casemacro-spec-p (spec)
  (and (consp spec)
       (symbolp (car spec)) ;; macro-name
       (consp (cdr spec))
       (symbolp (cadr spec)) ;; cond-var
       (cond-casemacro-casespecs-p (cddr spec))))


(defun cond-casemacro-cases (var cond-var cases kwd-alist)
  (declare (xargs :guard (cond-casemacro-casespecs-p cases)))
  (b* (((when (atom cases)) nil)
       ((list kwd cond-expr ctor) (car cases))
       (entry (cdr (assoc kwd kwd-alist)))
       (test (if (and (atom (cdr cases))
                      (eq cond-expr t))
                 t
               `(let ((,cond-var ,var)) ,cond-expr))))
    (cons `(,test (b* (((,ctor ,var :quietp t))) ,entry))
          (cond-casemacro-cases var cond-var (cdr cases) kwd-alist))))
  ;;       `((otherwise (b* (((,entry))))
  ;;   (cons `(,cond-expr 
  ;; (b* (((when (atom kwd-alist)) nil)
  ;;      ((when (eq (caar kwd-alist) :otherwise))
  ;;       `((otherwise ,(cdar kwd-alist))))
  ;;      (kind (caar kwd-alist))
  ;;      (case-spec (cdr (assoc kind cases)))
  ;;      ((list cond-expr ctor) case-spec))
  ;;   (cons `(,(cond ((atom (cdr kwd-alist)) t)
  ;;                  (t `(let ((,cond-var ,var)) ,cond-expr)))
  ;;           (b* (((,ctor ,var :quietp t)))
  ;;             ,(cdar kwd-alist)))
  ;;         (cond-casemacro-cases var cond-var cases (cdr kwd-alist)))))

(defun cond-casemacro-list-conditions (kwds kinds)
  (if (atom kinds)
      nil
    `(,(car kinds) ,(if (member (car kinds) kwds) t nil)
      . ,(cond-casemacro-list-conditions kwds (cdr kinds)))))

  ;; (b* (((when (atom cases))
  ;;       nil)
  ;; (b* (((when (atom kwds)) nil)
  ;;      (kind (car kwds))
  ;;      (case-spec (cdr (assoc kind cases)))
  ;;      (cond-expr (car case-spec)))
  ;;   (cons cond-expr
  ;;         (cond-casemacro-list-conditions (cdr kwds) cases))))


(defun cond-casemacro-fn (var-or-expr rest-args case-spec)
  (b* (((unless (cond-casemacro-spec-p case-spec))
        (er hard? 'cond-casemacro-fn "Bad case-spec: ~x0~%" case-spec))
       ((list* macro-name cond-var case-specs) case-spec)
       (case-kinds (remove-duplicates-eq (strip-cars case-specs)))
       ((when (and (eql (len rest-args) 1)
                   (or (atom (car rest-args))
                       (eq (caar rest-args) 'quote))))
        (b* (((mv var binding)
              (if (symbolp var-or-expr)
                  (mv var-or-expr nil)
                (mv cond-var `((,cond-var ,var-or-expr)))))
             (caselist (if (atom (car rest-args))
                           (list (car rest-args))
                         (cadr (car rest-args))))
             ((unless (subsetp-eq caselist case-kinds))
              (er hard? macro-name "Bad argument: ~x0~% Must be one of ~x1 or a quoted subset.~%" 
                  (car rest-args) case-kinds))
             (new-args (cond-casemacro-list-conditions caselist
                                                       case-kinds))
             (body (cond-casemacro-fn var new-args case-spec)))
          (if binding
              `(b* ,binding ,body)
            body)))
        ;; (cond ((and (atom (car rest-args))
        ;;             (member-eq (car rest-args) case-kinds))
        ;;        ;; Special case: (foo-case expr :kind) becomes (let ((cond-var expr)) cond)
        ;;        `(let ((,cond-var ,var-or-expr))
        ;;           ,(cadr (assoc (car rest-args) case-specs))))
        ;;       ((and (eq (car rest-args) 'quote)
        ;;             (true-listp (cadr rest-args))
        ;;             (subsetp (cadr rest-args) case-kinds))
        ;;        ;; Special case: (foo-case expr '(:kind1 :kind2))
        ;;        ;; becomes (member-eq (foo-kind expr) '(:kind1 :kind2))
        ;;        `(let ((,cond-var ,var-or-expr))
        ;;           (or . ,(cond-casemacro-list-conditions (cadr rest-args) case-kinds))))
        ;;       (t (er hard? macro-name "Bad argument: ~x0~% Must be one of ~x1 or a quoted subset.~%" 
        ;;              (car rest-args) case-kinds))))
       ((when (consp var-or-expr))
        (er hard? macro-name "Expected a variable, rather than: ~x0" var-or-expr))
       (var var-or-expr)

       (allowed-keywordlist-keys (append case-kinds '(:otherwise)))
       (allowed-parenthesized-keys (append case-kinds '(acl2::otherwise :otherwise acl2::&)))
                     
       ((mv kwd-alist rest)
        (extract-keywords macro-name
                          allowed-keywordlist-keys
                          rest-args nil))

       ((when (and rest kwd-alist))
        ;; Note: if we ever want to allow keyword options that aren't themselves cases,
        ;; change this error condition.
        ;; For now, only allow one kind of syntax --
        ;; either :foo bar :baz fuz
        ;; or    (:foo bar) (:baz fuz)
        ;; but not :foo bar (:baz fuz).
        (er hard? macro-name "Inconsistent syntax: ~x0" rest-args))

       ((unless (or kwd-alist
                    (and (alistp rest)
                         (true-list-listp rest)
                         ;; weaken this?
                         (subsetp (strip-cars rest) allowed-parenthesized-keys))))
        (er hard? macro-name "Malformed cases: ~x0~%" rest))
       
       (kwd-alist (reverse kwd-alist))

       (keys (if kwd-alist
                 (strip-cars kwd-alist)
               (sublis '((acl2::otherwise . :otherwise)
                         (acl2::&         . :otherwise))
                       (strip-cars rest))))
       (vals (if kwd-alist
                 (strip-cdrs kwd-alist)
               (pairlis$ (make-list (len rest) :initial-element 'progn$)
                         (strip-cdrs rest))))
       ((unless (<= (len (member :otherwise keys)) 1))
        ;; otherwise must be last or not exist
        (er hard? macro-name "Otherwise case must be last"))

       (kind-kwd-alist (or kwd-alist (pairlis$ keys vals)))
                   
       (body `(cond . ,(cond-casemacro-cases var cond-var case-specs kind-kwd-alist))))
    body))
