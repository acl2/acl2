; FGL - A Symbolic Simulation Framework for ACL2
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

(in-package "FGL")
;; (include-book "shape-spec-defs")
(include-book "centaur/fty/deftypes" :dir :system)
(include-book "centaur/fty/basetypes" :dir :system)

(include-book "centaur/fty/bitstruct" :dir :system)

(fty::defbitstruct fgl-function-mode
  :parents (fgl)
  :short "Limitations on what the FGL interpreter will do to resolve a call of a given function."
  ((split-ifs booleanp
    "If true, when the function is applied to arguments represented as @('g-ite')
     objects, the FGL interpreter will first split into cases for all combinations
     of @('g-ite') branches.  Generally this should be set for functions that resolve
     via rewrite rules and false for functions that resolve via definition
     expansion.")
   (dont-concrete-exec booleanp
    "If true, skip attempting to concretely execute the function in the case when
     all the arguments are explicit.")
   (dont-expand-def booleanp
    "If true, skip expanding the function's definition after attempting ~
     rewrites and primitive execution.")
   (dont-rewrite booleanp
    "If true, skip applying rewrite rules to calls of the function.")
   (dont-rewrite-under-if-test booleanp
    "If true, skip applying rewrite rules to calls of the function when trying
     to resolve an IF test to a Boolean formula.")
   (dont-primitive-exec booleanp
    "If true, skip applying primitives to calls of the function.")))

(fty::defmap fgl-function-mode-alist :key-type symbolp :val-type fgl-function-mode :true-listp t)

(define fgl-function-mode-lookup ((fn symbolp)
                                 (alist fgl-function-mode-alist-p))
  :returns (mode fgl-function-mode-p)
  (or (cdr (hons-get fn (make-fast-alist (fgl-function-mode-alist-fix alist)))) 0))

(defconst *fgl-config-fields*
  '((trace-rewrites booleanp :default 'nil)
    (reclimit posp :rule-classes (:rewrite :type-prescription) :default '1000000)
    (make-ites booleanp :default 'nil)
    (rewrite-rule-table :default (table-alist 'fgl-rewrite-rules (w state)))
    (branch-merge-rules :default (cdr (hons-assoc-equal 'fgl::fgl-branch-merge-rules (table-alist 'fgl-branch-merge-rules (w state)))))
    (function-modes fgl-function-mode-alist :default (table-alist 'fgl-fn-modes (w state)))
    (prof-enabledp booleanp :default 't)
    (sat-config)
    (skip-toplevel-sat-check booleanp :default 'nil)
    
    ))

(local
 (defun fgl-config-process-field (field)
   (cond ((atom field) field)
         ((eq (car field) ':default)
          (if (quotep (cadr field))
              (cons :default (cons (unquote (cadr field)) (cddr field)))
            (cons :default (cons nil (cddr field)))))
         (t (cons (car field)
                  (fgl-config-process-field (cdr field)))))))

(local
 (defun fgl-config-process-fields (fields)
   (if (atom fields)
       nil
     (cons (fgl-config-process-field (car fields))
           (fgl-config-process-fields (cdr fields))))))

(make-event
 `(defprod fgl-config
    ,(fgl-config-process-fields *fgl-config-fields*)
    :layout :tree))


(define fgl-config-setting ((table-key symbolp)
                             (state-key symbolp)
                             default
                             table
                             (args keyword-value-listp)
                             state)
  (b* ((look (assoc-keyword table-key args))
       ((when look) (cadr look))
       ((when (boundp-global state-key state))
        (f-get-global state-key state))
       (look (hons-assoc-equal table-key table))
       ((when look) (cdr look)))
    default))

(local
 (defun default-fgl-config-settings (fields state)
   (declare (xargs :stobjs state :mode :program))
   (b* (((when (atom fields)) nil)
        ((cons fieldname fieldargs) (car fields))
        (type (if (keywordp (car fieldargs))
                  nil
                (car fieldargs)))
        (fixtype (and type
                      (fty::find-fixtype type (fty::get-fixtypes-alist (w state)))))
        (fix (and type (fty::fixtype->fix fixtype)))
        (key (intern-in-package-of-symbol (symbol-name fieldname) :keyword))
        (state-key (intern-in-package-of-symbol (concatenate 'string "FGL-" (symbol-name fieldname)) :keyword))
        (default (cadr (member ':default fieldargs)))
        (setting-term `(fgl-config-setting ,key ,state-key ,default configtab args state))
        (setting-term-fix (if fix `(ec-call (,fix ,setting-term)) setting-term)))
     (cons key
           (cons setting-term-fix
                (default-fgl-config-settings (cdr fields) state))))))

(make-event
 `(define default-fgl-config-fn ((args keyword-value-listp) state)
    (b* ((configtab (table-alist 'fgl-config-table (w state))))
      (make-fgl-config
       . ,(default-fgl-config-settings *fgl-config-fields* state)))))

(defun default-fgl-config-filter-args (args)
  (declare (xargs :mode :program))
  (if (atom args)
      nil
    (if (acl2::assoc-symbol-name-equal (car args) *fgl-config-fields*)
        (list* (car args) (cadr args)
               (default-fgl-config-filter-args (cddr args)))
      (default-fgl-config-filter-args (cddr args)))))
  

(defmacro default-fgl-config (&rest args)
  `(default-fgl-config-fn (list . ,(default-fgl-config-filter-args args)) state))

(table fgl-config-table)
